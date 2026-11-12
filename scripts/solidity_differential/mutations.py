"""Compile actual importer/Denote mutants in isolated source/cache snapshots."""
import json
from pathlib import Path
import shutil
import subprocess
import sys

from .engine import ROOT, WORKSPACE, MUTANT_BUILD_TIMEOUT, HarnessError, command, write_json

# Exact shared lowering anchor; every mutation must still compile and diverge at runtime.
CONDITIONAL_LOWERING = """private partial def lowerConditional (j : Json) : M Val := do
  let cond ← atom (← lowerExpr (← mField j "condition"))
  let yes ← lowerExpr (← mField j "trueExpression")
  let no ← lowerExpr (← mField j "falseExpression")
  let dest ← fresh
  let thenB := yes.pre.push (.assignVar dest yes.expr)
  let elseB := no.pre.push (.assignVar dest no.expr)
  let ite := Stmt.ite cond.expr thenB.toList elseB.toList
  pure { pre := cond.pre.push (.letVar dest (.literal 0)) |>.push ite, expr := .localVar dest }
"""

POSTINCREMENT_STORAGE = '  let stmts := pre.push (.letVar oldVar (.storage name)) ++ combined.pre |>.push (.letVar newVar combined.expr) |>.push (.setStorage name (.localVar newVar))\n  return { pre := stmts, expr := if isPrefix then .localVar newVar else .localVar oldVar }\n'
POSTINCREMENT_LOCAL = '        unless isSupportedIncDecTy ty do\n          failAt target s!"unsupported scalar local increment/decrement type {ty}"\n        let oldVar ← fresh\n        let combined ← combineCompound compoundOp ty (.localVar oldVar) (.literal 1) j\n        let stmts := #[Stmt.letVar oldVar (.localVar binding)] ++ combined.pre |>.push (.assignVar binding combined.expr)\n        return { pre := stmts, expr := if isPrefix then .localVar binding else .localVar oldVar }\n'

# Narrow parameters must preserve the incoming assembly word at helper binding.
HELPER_SCALAR_BINDING = """    | .scalar value =>
        let converted ← convert pty argTy value argNode
        if (bodyCompoundAssignedIds body).contains pid"""

MUTANTS = {
    'helper-scalar-address-word': ('Compiler/SolidityImport/Import.lean', HELPER_SCALAR_BINDING,
        HELPER_SCALAR_BINDING.replace('        if (bodyCompoundAssignedIds',
            '        let converted := if paramType pty == some .address then\n'
            '          { converted with expr := .bitAnd converted.expr (.literal (2^128-1)) }\n'
            '          else converted\n        if (bodyCompoundAssignedIds')),
    'helper-scalar-enum-word': ('Compiler/SolidityImport/Import.lean', HELPER_SCALAR_BINDING,
        HELPER_SCALAR_BINDING.replace('        if (bodyCompoundAssignedIds',
            '        let converted := if pty.startsWith "enum " then\n'
            '          { converted with expr := .add converted.expr (.literal 1) }\n'
            '          else converted\n        if (bodyCompoundAssignedIds')),
    # Add the incorrect check at the first helper boundary. Nested event argument
    # helpers must stay total so this mutant reaches execution instead of rejection.
    'helper-scalar-enum-check': ('Compiler/SolidityImport/Import.lean', HELPER_SCALAR_BINDING,
        HELPER_SCALAR_BINDING.replace('        if (bodyCompoundAssignedIds',
            '        let converted ← if pty.startsWith "enum " && caller.stack.length == 2 then\n'
            '          LegacyMemory.checkedEnum argNode pty converted else pure converted\n'
            '        if (bodyCompoundAssignedIds')),
    'postincrement-new-value': ('Compiler/SolidityImport/Import.lean', POSTINCREMENT_STORAGE,
        POSTINCREMENT_STORAGE.replace('else .localVar oldVar', 'else .localVar newVar')),
    'postincrement-double-write': ('Compiler/SolidityImport/Import.lean', POSTINCREMENT_STORAGE,
        POSTINCREMENT_STORAGE.replace('.setStorage name (.localVar newVar)',
            '.setStorage name (.add (.localVar newVar) (.literal 1))')),
    'postincrement-missing-write': ('Compiler/SolidityImport/Import.lean', POSTINCREMENT_STORAGE,
        POSTINCREMENT_STORAGE.replace(' |>.push (.setStorage name (.localVar newVar))', '')),
    'postincrement-local-new-value': ('Compiler/SolidityImport/Import.lean', POSTINCREMENT_LOCAL,
        POSTINCREMENT_LOCAL.replace('else .localVar oldVar', 'else .localVar binding')),

    'conditional-invert': ('Compiler/SolidityImport/Import.lean', CONDITIONAL_LOWERING,
        CONDITIONAL_LOWERING.replace('Stmt.ite cond.expr thenB.toList elseB.toList',
            'Stmt.ite (.logicalNot cond.expr) thenB.toList elseB.toList')),
    'conditional-eager-true': ('Compiler/SolidityImport/Import.lean', CONDITIONAL_LOWERING,
        CONDITIONAL_LOWERING.replace('let thenB := yes.pre.push (.assignVar dest yes.expr)',
            'let thenB := #[Stmt.assignVar dest yes.expr]').replace('pre := cond.pre.push',
            'pre := (cond.pre ++ yes.pre).push')),
    'conditional-eager-false': ('Compiler/SolidityImport/Import.lean', CONDITIONAL_LOWERING,
        CONDITIONAL_LOWERING.replace('let elseB := no.pre.push (.assignVar dest no.expr)',
            'let elseB := #[Stmt.assignVar dest no.expr]').replace('pre := cond.pre.push',
            'pre := (cond.pre ++ no.pre).push')),
    'conditional-repeat-condition': ('Compiler/SolidityImport/Import.lean', CONDITIONAL_LOWERING,
        CONDITIONAL_LOWERING.replace('  let yes ← lowerExpr',
            '  let repeated ← atom (← lowerExpr (← mField j "condition"))\n  let yes ← lowerExpr').replace(
            'pre := cond.pre.push', 'pre := (cond.pre ++ repeated.pre).push')),

    'helper-copy-source': ('Compiler/SolidityImport/LegacyMemory.lean',
        'let copy ← copyCalldata data source length',
        'let copy ← copyCalldata data (.add source (.literal 1)) length'),
    'helper-copy-header': ('Compiler/SolidityImport/LegacyMemory.lean',
        '.mstore (.localVar pointer) length] ++ copy ++',
        '.mstore (.localVar pointer) (.add length (.literal 1))] ++ copy ++'),
    'helper-copy-rounding': ('Compiler/SolidityImport/LegacyMemory.lean',
        '.mstore (.literal 64) (.add data rounded)',
        '.mstore (.literal 64) (.add data length)'),
    'helper-copy-reuse': ('Compiler/SolidityImport/LegacyMemory.lean',
        '.mstore (.literal 64) (.add data rounded)',
        '.mstore (.literal 64) (.localVar pointer)'),
    'helper-copy-padding': ('Compiler/SolidityImport/LegacyMemory.lean',
        '#[.mstore (.add data length) (.literal 0)]', '#[]'),
    'helper-forward-offset': ('Compiler/SolidityImport/Import.lean',
        'let forwarded := { descriptor with param := pname }',
        'let forwarded := { descriptor with param := pname, dataBinding := descriptor.headerBinding }'),
    'legacy-bool-code': ('Verity/Core/Model/LegacyBoolCalls.lean', '.if_ (.call "iszero" [.call "extcodesize" [target]])', '.if_ (.lit 0)'),
    'legacy-bool-truth': ('Verity/Core/Model/LegacyBoolCalls.lean', '.assign result (.call "iszero" [.call "iszero" [.call "mload" [ptr]]])', '.assign result (.call "eq" [.call "mload" [ptr], .lit 1])'),
    'legacy-bool-short': ('Verity/Core/Model/LegacyBoolCalls.lean', '.if_ (.call "lt" [.call "returndatasize" [], .lit 32])', '.if_ (.call "lt" [.call "returndatasize" [], .lit 1])'),
    'legacy-bool-failure': ('Verity/Core/Model/LegacyBoolCalls.lean', '.exprStmt (.call "revert" [.lit 0, .call "returndatasize" []])', '.exprStmt (.call "revert" [.lit 0, .lit 0])'),
    'legacy-bool-selector': ('Verity/Core/Model/LegacyBoolCalls.lean', '.lit (selector * 2^224)', '.lit ((selector + 1) * 2^224)'),
    'legacy-bool-static': ('Verity/Core/Model/LegacyBoolCalls.lean', '.call "staticcall" [\n       .call "gas" [], target, ptr,', '.call "call" [\n       .call "gas" [], target, .lit 0, ptr,'),
    'legacy-bool-pointer': ('Verity/Core/Model/LegacyBoolCalls.lean', '.assign result (.call "iszero" [.call "iszero" [.call "mload" [ptr]]])', '.exprStmt (.call "mstore" [.lit 64, .call "add" [ptr, .lit 32]]),\n     .assign result (.call "iszero" [.call "iszero" [.call "mload" [ptr]]])'),
    'legacy-store-slot': ('Compiler/SolidityImport/Import.lean', '.setStorageArrayElement rawStorageFieldName slotVal.expr valVal.expr', '.setStorageArrayElement rawStorageFieldName (.add slotVal.expr (.literal 1)) valVal.expr'),
    'void-call-offset': ('Verity/Core/Model/LegacyVoidCalls.lean', 'store head (.call "sub" [tail, add ptr 4])', 'store head (.call "sub" [tail, ptr])'),
    'void-call-code': ('Verity/Core/Model/LegacyVoidCalls.lean', '.if_ (.call "iszero" [.call "extcodesize" [target]])', '.if_ (.lit 0)'),
    'void-call-failure': ('Verity/Core/Model/LegacyVoidCalls.lean', '.exprStmt (.call "revert" [.lit 0, .call "returndatasize" []])', '.exprStmt (.call "revert" [.lit 0, .lit 0])'),
    'void-call-pre': ('Verity/Core/Model/LegacyVoidCalls.lean', 'return [.block body]', 'return if layout.any (· != .word) then [] else [.block body]'),
    'void-call-post': ('Verity/Core/Model/LegacyVoidCalls.lean', 'return [.block body]', 'return if layout.all (· == .word) then [] else [.block body]'),
    'void-call-return-decoder': ('Verity/Core/Model/LegacyVoidCalls.lean', 'return [.block body]', 'return [.block (body ++ [.if_ (.call "lt" [.call "returndatasize" [], .lit 32]) [.exprStmt (.call "revert" [.lit 0, .lit 0])]])]'),
    'void-call-length-reload': ('Verity/Core/Model/LegacyVoidCalls.lean', 'body := body ++ [.assign (name ("size" ++ toString index)) length]', 'body := body'),
    'void-call-stored-address': ('Compiler/SolidityImport/Legacy.lean', 'LegacyMemory.cleanScalar .address value.expr', '.bitAnd value.expr (.literal (2^159-1))'),
    'void-call-head-order': ('Verity/Core/Model/LegacyVoidCalls.lean', '  let mut operand := 1\n  -- Legacy ABI-v1 fills every scalar head before any dynamic offset or payload.\n  for (kind, index) in layout.zipIdx do\n    if kind == .word then\n      body := body ++ [store (add ptr (4 + 32 * index)) (values.getD operand (.lit 0))]\n    operand := operand + (if kind == .calldataBytes then 2 else 1)\n  operand := 1\n  for (kind, index) in layout.zipIdx do\n    let head := add ptr (4 + 32 * index)\n    let data := values.getD operand (.lit 0)\n    if kind != .word then\n', '  let mut operand := 1\n  -- Legacy ABI-v1 fills every scalar head before any dynamic offset or payload.\n  for (kind, index) in layout.zipIdx do\n    if kind == .word && index != 5 then\n      body := body ++ [store (add ptr (4 + 32 * index)) (values.getD operand (.lit 0))]\n    operand := operand + (if kind == .calldataBytes then 2 else 1)\n  operand := 1\n  for (kind, index) in layout.zipIdx do\n    let head := add ptr (4 + 32 * index)\n    let data := values.getD operand (.lit 0)\n    if kind == .word && index == 5 then\n      body := body ++ [store head data]\n    if kind != .word then\n'),
    'post-log-emitter': ('Verity/Core/Model/EventLogs.lean',
        'rawLog := some entry',
        'rawLog := some { entry with emitter := world.thisAddress }'),
    'post-log-payload': ('Verity/Core/Model/EventLogs.lean',
        'rawLog := some entry',
        'rawLog := some { entry with data := entry.data.drop 1 }'),
    'post-log-order': ('Verity/Core/Model/RawCalls.lean',
        'CallWorld.commitCalleeWorld before observed.world else before',
        'CallWorld.commitCalleeWorld before { observed.world with events := before.events ++ '
        '(observed.world.events.drop before.events.length).reverse } else before'),
    'post-log-parent-prefix': ('Verity/Core/Model/RawCalls.lean',
        'CallWorld.commitCalleeWorld before observed.world else before',
        'CallWorld.commitCalleeWorld before observed.world else { before with events := [] }'),
    'post-log-caller': ('Compiler/CompilationModel/Compile.lean',
        'Stmt.emit eventName args => do\n'
        '      compileEmit fields events dynamicSource eventName args internalFunctions',
        'Stmt.emit _ _ => do\n      return []'),
    'post-log-outer-rollback': ('Compiler/CompilationModel/Compile.lean',
        'YulStmt.exprStmt (YulExpr.call "revert" [\n          YulExpr.lit 0,\n'
        '          YulExpr.ident "__returndata_size"',
        'YulStmt.exprStmt (YulExpr.call "return" [\n          YulExpr.lit 0,\n'
        '          YulExpr.ident "__returndata_size"'),
    'payable-credit': ('Compiler/SolidityImport/ValueTransactions.lean',
        'balance := Uint256.ofNat (recipient.balance.val + amount)',
        'balance := Uint256.ofNat recipient.balance.val'),
    'payable-debit': ('Compiler/SolidityImport/ValueTransactions.lean',
        'balance := Uint256.ofNat (source.balance.val - amount)',
        'balance := Uint256.ofNat source.balance.val'),
    'payable-rollback': ('Compiler/SolidityImport/ValueTransactions.lean',
        'if result.success then result.world else prepared.rollbackWorld',
        'if result.success then result.world else prepared.callWorld'),
    'payable-nonce': ('Compiler/SolidityImport/ValueTransactions.lean',
        'let rollbackWorld := world.writeAccount sender { source with nonce }',
        'let rollbackWorld := world'),
    'payable-guard': ('Compiler/SolidityImport/ValueTransactions.lean',
        'fn.isPayable || value == 0', 'true'),
    'payable-metadata': ('Compiler/SolidityImport/Import.lean',
        'isPayable := optStr fn "stateMutability" == some "payable", body := body.toList,',
        'isPayable := false, body := body.toList,'),
    'raw-call-input-offset': ('Verity/Core/Model/Denote.lean',
        'UInt8.ofNat (state.world.physicalByte (pointer + i)).val }',
        'UInt8.ofNat (state.world.physicalByte (pointer + i + 1)).val }'),
    'raw-call-value': ('Verity/Core/Model/Denote.lean',
        'value := if delegated then state.world.msgValue.val else values[2]!',
        'value := if delegated then state.world.msgValue.val else 0'),
    'raw-call-rollback': ('Verity/Core/Model/RawCalls.lean',
        'world := if observed.success then', 'world := if true then'),
    'raw-call-delegate-opcode': ('Verity/Core/Model/ECM.lean',
        '(.call (if delegated then "delegatecall" else "call")',
        '(.call (if delegated then "staticcall" else "call")'),
    'raw-call-enum-comparison': ('Compiler/SolidityImport/Import.lean',
        'left ← LegacyMemory.checkedEnum leftNode common left', 'pure ()'),
    'import-legacy-calldata-source': ('Compiler/SolidityImport/LegacyMemory.lean',
        'copyCalldata destination source count)',
        'copyCalldata destination (.add source (.literal 1)) count)'),
    'import-legacy-calldata-length': ('Compiler/SolidityImport/LegacyMemory.lean',
        'else cb.lengthBinding)', 'else cb.dataBinding)'),
    'import-legacy-calldata-hash': ('Compiler/SolidityImport/LegacyMemory.lean',
        '| "keccak256", #[a, b] => return .keccak256 a b',
        '| "keccak256", #[a, b] => return .keccak256 a (.add b (.literal 1))'),
    'import-legacy-calldata-enum-entry': ('Compiler/SolidityImport/Import.lean',
        'let limit := if !strictAbi then none else match env.enumBounds.find? p.id with',
        'let limit := if !strictAbi && !env.enumBounds.contains p.id then none else match env.enumBounds.find? p.id with'),
    'import-legacy-calldata-enum-invalid': ('Compiler/SolidityImport/Import.lean',
        'Stmt.ecm Compiler.ECM.SolidityInvalid.module [] else .panicCode (.literal 0x21)',
        'Stmt.revertEmpty else .panicCode (.literal 0x21)'),
    'import-legacy-static-header': ('Compiler/SolidityImport/LegacyAbi.lean',
        '.mstore header (.literal size)', '.mstore header (.literal (size + 1))'),
    'import-legacy-static-stride': ('Compiler/SolidityImport/LegacyAbi.lean',
        '.literal (32 * index)', '.literal (31 * index)'),
    'import-legacy-static-rounding': ('Compiler/SolidityImport/LegacyAbi.lean',
        '.letVar headerName (.mload (.literal 64))',
        '.letVar headerName (.bitAnd (.add (.mload (.literal 64)) (.literal 31)) (.bitNot (.literal 31)))'),
    'import-legacy-static-chainid': ('Compiler/SolidityImport/Import.lean',
        '| "chainid", #[] => pure { pre, expr := .chainid }',
        '| "chainid", #[] => pure { pre, expr := .literal 0 }'),
    'import-legacy-packed-rounding': ('Compiler/SolidityImport/LegacyPacked.lean',
        '.mstore (.literal 64) (.add data (.literal size))',
        '.mstore (.literal 64) (.add data (.literal ((size + 31) / 32 * 32)))'),
    'import-legacy-packed-header': ('Compiler/SolidityImport/LegacyPacked.lean',
        '.mstore header (.literal size)', '.mstore header (.literal (size + 1))'),
    'import-legacy-packed-alignment': ('Compiler/SolidityImport/LegacyPacked.lean',
        'let shift := 8 * (32 - width)', 'let shift := 8 * (31 - width)'),

    'import-legacy-pointer-encode-order': ('Verity/Core/Model/LegacySignatureCalls.lean',
        '    .let_ (p ++ "ptr") (.call "mload" [.lit 64]),\n    store ptr (.lit (selector * 2^224)), store (add ptr 4) hash,\n    store (add ptr 36) (.lit 64),\n    .let_ (p ++ "size") (.call "mload" [.call "sub" [data, .lit 32]]),',
        '    .let_ (p ++ "ptr") (.call "mload" [.lit 64]),\n    .let_ (p ++ "size") (.call "mload" [.call "sub" [data, .lit 32]]),\n    store ptr (.lit (selector * 2^224)), store (add ptr 4) hash,\n    store (add ptr 36) (.lit 64),'),
    'import-legacy-pointer-zero-slot': ('Compiler/SolidityImport/Import.lean',
        'pointer := .literal 128, size := .literal 0', 'pointer := .literal 96, size := .literal 0'),
    'import-legacy-pointer-length': ('Compiler/SolidityImport/LegacyBytePointers.lean',
        '{ buffer with size := .mload (.sub buffer.pointer (.literal 32)) }',
        '{ buffer with size := .literal 0 }'),
    'ecm-legacy-code-existence': ('Verity/Core/Model/LegacySignatureCalls.lean',
        '.if_ (.call "iszero" [.call "extcodesize" [target]])', '.if_ (.lit 0)'),
    'ecm-legacy-recovery-stale': ('Verity/Core/Model/LegacySignatureCalls.lean',
        'store ptr (.lit 0),', ''),
    'ecm-legacy-validator-selector': ('Verity/Core/Model/LegacySignatureCalls.lean',
        'store ptr (.lit (selector * 2^224))', 'store ptr (.lit ((selector + 1) * 2^224))'),
    'import-legacy-loop-final-counter': ('Compiler/SolidityImport/Import.lean', '#[.assignVar binding (.localVar limit)]', '#[.assignVar binding (.literal 0)]'),
    'import-legacy-division-operands': ('Compiler/SolidityImport/Import.lean', 'return { pre := a.pre ++ b.pre, expr := .div a.expr b.expr }', 'return { pre := a.pre ++ b.pre, expr := .div b.expr a.expr }'),
    'import-legacy-guard-stability': ('Compiler/SolidityImport/LegacyControlFlow.lean', 'if writes.contains id then s else s.insert id', 'if writes.contains id && false then s else s.insert id'),
    'import-legacy-bytes-header': ('Compiler/SolidityImport/LegacyBytePointers.lean', 'expr := .sub buffer.pointer (.literal 32)', 'expr := buffer.pointer'),
    'import-legacy-bytes-padding': ('Compiler/SolidityImport/AbiLowering.lean', '  , .mstore (.add data length) (.literal 0) ]', '  ]'),
    'import-legacy-bytes-byte-lane': ('Compiler/SolidityImport/Import.lean', '| "byte", #[a, b] => pure { pre, expr := .byte a b }', '| "byte", #[a, b] => pure { pre, expr := .byte (.add a (.literal 1)) b }'),
    'import-fixed-bytes-literal-alignment': ('Compiler/SolidityImport/Import.lean', '  return { pre := #[], expr := .literal (word * 16 ^ (64 - hex.length)) }', '  return { pre := #[], expr := .literal word }'),
    'import-fixed-bytes-truncation': ('Compiler/SolidityImport/Import.lean', '      return { v with expr := .bitAnd v.expr (.literal ((2 ^ (8 * width) - 1) * 2 ^ shift)) }', '      return v'),
    'denote-memory-revert-empty': ('Verity/Core/Model/Denote.lean', '  return .revertWithData ((List.range size).map fun i =>\n    UInt8.ofNat (state.world.byteMemory.readByte (offset + i)).val)', '  let _ := (offset, size)\n  return .revertWithData []'),
    'ecm-memory-revert-size': ('Verity/Core/Model/ECM.lean', '  | [offset, size] => pure [.exprStmt (.call "revert" [offset, size])]', '  | [offset, size] => pure [.exprStmt (.call "revert" [offset, .call "add" [size, .lit 1]])]'),

    "import-legacy-root-checked": ("Compiler/SolidityImport/Import.lean", 'legacyWrapping := legacy, unchecked := legacy', 'legacyWrapping := legacy, unchecked := false'),
    "import-legacy-helper-checked": ("Compiler/SolidityImport/Import.lean", 'legacyWrapping := legacy, unchecked := legacy', 'legacyWrapping := false, unchecked := legacy'),
    "import-require-condition": ("Compiler/SolidityImport/Import.lean", 'return condition.pre.push (.require condition.expr value)', 'return condition.pre.push (.require (.literal 1) value)'),
    "denote-require-selector": ("Verity/Core/Model/Denote.lean", '[0x08, 0xc3, 0x79, 0xa0]', '[0x08, 0xc3, 0x79, 0xa1]'),
    "import-custom-require-condition": ("Compiler/SolidityImport/Import.lean", '(.requireError condition.expr name values)', '(.requireError (.literal 1) name values)'),
    "denote-custom-require-selector": ("Verity/Core/Model/Denote.lean", '(wordBytes hash).take 4', '((wordBytes hash).drop 1).take 4'),
    "denote-custom-require-argument": ("Verity/Core/Model/Denote.lean", 'return selector ++ values.flatMap wordBytes', 'return selector ++ values.flatMap (fun value => wordBytes (value + 1))'),
    "denote-panic-selector": ("Verity/Core/Model/Denote.lean", '[0x4e, 0x48, 0x7b, 0x71]', '[0x4e, 0x48, 0x7b, 0x70]'),
    "denote-panic-endian": ("Verity/Core/Model/Denote.lean", 'value / 2^(8*(31-i))', 'value / 2^(8*i)'),
    "import-comparison": ("Compiler/SolidityImport/Import.lean", '| "<" =>\n      if isSigned then cmp .slt left right else cmp .lt left right', '| "<" =>\n      if isSigned then cmp .slt left right else cmp .gt left right'),
    "import-field-slot": ("Compiler/SolidityImport/Import.lean", '    | none => .mappingStruct key1 members\'.toList\n  let field : Field := { name, ty, slot := some slot }', '    | none => .mappingStruct key1 members\'.toList\n  let field : Field := { name, ty, slot := some (slot + 1) }'),
    "denote-packed-mask": ("Verity/Core/Model/Denote.lean", '(2 ^ packed.width) - 1', '(2 ^ packed.width) - 2'),
    "denote-storage-read": ("Verity/Core/Model/Denote.lean", '    world.readSlot (wordNormalize slot)\n', '    world.readSlot (wordNormalize (slot + 1))\n'),
}


def snapshot(destination):
    destination.mkdir(parents=True, exist_ok=False)
    paths = command(["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=ROOT).split("\0")
    for name in paths:
        if not name or not (ROOT / name).is_file():
            continue
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, target)
    cache = destination / ".lake"
    cache.mkdir(exist_ok=True)
    (cache / "packages").symlink_to(WORKSPACE / ".lake/packages", target_is_directory=True)
    # Private copy-on-write cache: no hardlinks/symlinks to mutable parent oleans.
    # CI attaches its persistent build cache through a symlink. Copy the target
    # directory, not that link, or mutants overwrite the parent's compiled code.
    build = (WORKSPACE / ".lake/build").resolve(strict=True)
    if sys.platform == "darwin":
        command(["/bin/cp", "-cRL", build, cache / "build"], timeout=300)
    else:
        command(["cp", "-aL", "--reflink=auto", build, cache / "build"], timeout=300)
    (cache / "solidity-import").mkdir()
    for compiler_name in ("solc-0.7.6", "solc-0.8.34", "solc-0.8.26", "solc-0.8.10"):
        compiler_src = WORKSPACE / ".lake/solidity-import" / compiler_name
        if compiler_src.exists():
            shutil.copy2(compiler_src, cache / "solidity-import" / compiler_name)


def release(destination):
    """Drop the private build copy once a mutant is scored; sources, logs and reports stay.

    Without reflinks (ext4) every snapshot is a full copy of `.lake/build`, so
    campaigns otherwise leak ~1.4 GiB per mutant.
    """
    shutil.rmtree(destination / ".lake/build", ignore_errors=True)


def mutation_campaign(output, selected=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    from .check_environment_mutations import MUTANTS as CONTEXT_MUTANTS
    from .check_environment_mutations import mutation_campaign as context_campaign
    from .check_storage_mutations import MUTANTS as STORAGE_MUTANTS
    from .check_storage_mutations import mutation_campaign as storage_campaign
    from .check_abi_mutations import MUTANTS as ABI_MUTANTS
    from .check_abi_mutations import mutation_campaign as abi_campaign
    from .check_struct_abi_mutations import MUTANTS as STRUCT_ABI_MUTANTS
    from .check_struct_abi_mutations import mutation_campaign as struct_abi_campaign
    from .check_abi_length_for_mutations import MUTANTS as ARRAY_FOR_MUTANTS
    from .check_abi_length_for_mutations import mutation_campaign as array_for_campaign
    from .check_scalar_array_abi_mutations import MUTANTS as SCALAR_ARRAY_MUTANTS
    from .check_scalar_array_abi_mutations import mutation_campaign as scalar_array_campaign
    from .check_nested_dynamic_struct_abi_mutations import MUTANTS as NESTED_STRUCT_ABI_MUTANTS
    from .check_nested_dynamic_struct_abi_mutations import mutation_campaign as nested_struct_abi_campaign
    from .check_multiple_dynamic_abi_mutations import MUTANTS as MULTIPLE_ABI_MUTANTS
    from .check_multiple_dynamic_abi_mutations import mutation_campaign as multiple_abi_campaign
    for name in selected or [*MUTANTS, *CONTEXT_MUTANTS, *STORAGE_MUTANTS, *ABI_MUTANTS, *STRUCT_ABI_MUTANTS, *SCALAR_ARRAY_MUTANTS, *ARRAY_FOR_MUTANTS, *NESTED_STRUCT_ABI_MUTANTS, *MULTIPLE_ABI_MUTANTS]:
        if name in MULTIPLE_ABI_MUTANTS:
            result = multiple_abi_campaign(output, [name])
            reports.extend(result['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        if name in NESTED_STRUCT_ABI_MUTANTS:
            result = nested_struct_abi_campaign(output, [name])
            reports.extend(result['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        if name in ARRAY_FOR_MUTANTS:
            result = array_for_campaign(output, [name])
            reports.extend(result['mutants'])
            write_json(output / 'mutation-results.json', reports)
            continue
        if name in SCALAR_ARRAY_MUTANTS:
            result = scalar_array_campaign(output, [name])
            reports.extend(result['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        if name in STRUCT_ABI_MUTANTS:
            result = struct_abi_campaign(output, [name])
            reports.extend(result['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        if name in ABI_MUTANTS:
            result = abi_campaign(output, [name])
            reports.extend(result['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        if name in STORAGE_MUTANTS:
            storage = storage_campaign(output, [name])
            reports.extend(storage['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        if name in CONTEXT_MUTANTS:
            context = context_campaign(output, [name])
            reports.extend(context['mutants'])
            write_json(output / "mutation-results.json", reports)
            continue
        relative, before, after = MUTANTS[name]
        directory = output / name
        if directory.exists():
            raise HarnessError("mutation output already exists; choose a fresh output: " + str(directory))
        snapshot(directory)
        try:
            source = directory / relative
            text = source.read_text()
            if text.count(before) != 1:
                raise HarnessError("mutation anchor drifted: " + name)
            config = "differential-require.json" if "require" in name else "differential.json"
            if name == "import-legacy-root-checked":
                config = "differential-legacy-arithmetic.json"
            elif name == "import-legacy-helper-checked":
                config = "differential-legacy-helper.json"
            if name in ("import-fixed-bytes-literal-alignment", "import-fixed-bytes-truncation",
                        "denote-memory-revert-empty", "ecm-memory-revert-size"):
                config = "differential-fixed-bytes-legacy-zero.json"
            if "custom-require" in name:
                config = "differential-require-custom.json"
            argv = [sys.executable, str(directory / "scripts/solidity_import_differential.py"),
                    "--config", str(directory / "Contracts/SolidityImportSmoke" / config),
                    "--output", str(directory / ".lake/campaign"), "--cases", "8"]
            if name.startswith("import-legacy-bytes-"):
                argv = [sys.executable, "-c",
                        "import sys; sys.path.insert(0, 'scripts'); "
                        "from solidity_differential.check_legacy_bytes import main; sys.exit(main())",
                        "--context", "zero", "--output", str(directory / ".lake/campaign"),
                        "--cases", "8", "--jobs", "1"]
            if name in ("import-legacy-loop-final-counter", "import-legacy-division-operands",
                        "import-legacy-guard-stability"):
                function = "counted" if name == "import-legacy-loop-final-counter" else "arithmetic"
                argv = [sys.executable, "-c",
                        "import sys; sys.path.insert(0, 'scripts'); "
                        "from solidity_differential.check_legacy_control_flow import main; sys.exit(main())",
                        "--context", "zero", "--function", function, "--guard-probe",
                        "--output", str(directory / ".lake/campaign"), "--cases", "0", "--jobs", "1"]
            if name in ("ecm-legacy-recovery-stale", "ecm-legacy-validator-selector",
                        "ecm-legacy-code-existence"):
                argv = [sys.executable, "-c",
                        "import sys; sys.path.insert(0, 'scripts'); "
                        "from solidity_differential.check_legacy_signature_calls import main; sys.exit(main())",
                        "--output", str(directory / ".lake/campaign"), "--random-cases", "0"]
            if name.startswith("import-legacy-pointer-"):
                argv = [sys.executable, "-c",
                        "import sys; sys.path.insert(0, 'scripts'); "
                        "from solidity_differential.check_legacy_byte_pointers import main; sys.exit(main())",
                        "--output", str(directory / ".lake/campaign"), "--random-cases", "0"]
            if name.startswith("import-legacy-packed-"):
                argv = [sys.executable, "-c",
                        "import sys; sys.path.insert(0, 'scripts'); "
                        "from solidity_differential.check_legacy_packed_hash import main; sys.exit(main())",
                        "--output", str(directory / ".lake/campaign"), "--random-cases", "0"]
            if name.startswith("import-legacy-static-"):
                argv = [sys.executable, "-c",
                        "import sys; sys.path.insert(0, 'scripts'); "
                        "from solidity_differential.check_legacy_static_abi import main; sys.exit(main())",
                        "--output", str(directory / ".lake/campaign")]
            if name.startswith("import-legacy-calldata-"):
                argv = [sys.executable, "-c",
                        "import sys; sys.path.insert(0, 'scripts'); "
                        "from solidity_differential.check_legacy_calldata_hash import main; sys.exit(main())",
                        "--output", str(directory / ".lake/campaign")]
            if name.startswith("helper-scalar-"):
                argv = [sys.executable, "-m", "solidity_differential.check_legacy_helper_assembly_scalars",
                        "--output", str(directory / ".lake/campaign")]
            if name.startswith("postincrement-"):
                argv = [sys.executable, "-m", "solidity_differential.check_legacy_postincrement_arguments",
                        "--output", str(directory / ".lake/campaign")]
            if name.startswith("conditional-"):
                kind = "effects" if name == "conditional-repeat-condition" else "scalar"
                argv = [sys.executable, "-m", "solidity_differential.check_legacy_scalar_conditionals",
                        "--kind", kind, "--output", str(directory / ".lake/campaign")]
            if name.startswith(("helper-copy-", "helper-forward-")):
                argv = [sys.executable, "-m", "solidity_differential.check_legacy_calldata_helpers",
                        "--output", str(directory / ".lake/campaign")]
            if name.startswith(("legacy-bool-", "legacy-store-")):
                argv = [sys.executable, "-m", "solidity_differential.check_legacy_static_installation",
                        "--output", str(directory / ".lake/campaign"), "--random-cases", "0"]
            if name.startswith("void-call-"):
                argv = [sys.executable, "-m", "solidity_differential.check_legacy_void_callbacks",
                        "--output", str(directory / ".lake/campaign")]
            if name.startswith("post-log-"):
                argv = [sys.executable, "-m", "solidity_differential.check_legacy_post_call_events",
                        "--output", str(directory / ".lake/campaign")]
            if name.startswith("payable-"):
                argv = [sys.executable, "-c",
                        "import sys; sys.path.insert(0, 'scripts'); "
                        "from solidity_differential.check_legacy_payable import main; sys.exit(main())",
                        "--output", str(directory / ".lake/campaign")]
            if name.startswith("raw-call-"):
                argv = [sys.executable, "-c",
                        "import sys; sys.path.insert(0, 'scripts'); "
                        "from solidity_differential.check_legacy_raw_calls import main; sys.exit(main())",
                        "--output", str(directory / ".lake/campaign")]
            # A pre-existing fixture divergence is not evidence that a mutation was
            # detected. Run the identical inputs in the private snapshot first.
            baseline_argv = [str(directory / ".lake/baseline") if arg == str(directory / ".lake/campaign")
                             else arg for arg in argv]
            baseline = subprocess.run(baseline_argv, cwd=directory, text=True,
                                      capture_output=True, timeout=MUTANT_BUILD_TIMEOUT)
            (directory / "baseline.log").write_text(baseline.stdout + baseline.stderr)
            baseline_file = directory / ".lake/baseline/results.json"
            baseline_report = json.loads(baseline_file.read_text()) if baseline_file.exists() else {}
            if (baseline.returncode != 0 or baseline_report.get("divergences") != [] or
                    baseline_report.get("cases", baseline_report.get("count", 0)) <= 0):
                raise HarnessError(
                    f"mutation positive control failed: {name} (exit {baseline.returncode}); "
                    f"inspect {directory / 'baseline.log'}\n"
                    + (baseline.stdout + baseline.stderr)[-4000:])
            source.write_text(text.replace(before, after))
            try:
                result = subprocess.run(argv, cwd=directory, text=True, capture_output=True, timeout=MUTANT_BUILD_TIMEOUT)
                (directory / "mutation.log").write_text(result.stdout + result.stderr)
                report_file = directory / ".lake/campaign/results.json"
                report = json.loads(report_file.read_text()) if report_file.exists() else {}
                if result.returncode == 1 and report.get("divergences"):
                    status = "detected"
                elif result.returncode == 0:
                    status = "survived"
                else:
                    status = "invalid"  # compilation/tool failure does not kill a mutant
            except subprocess.TimeoutExpired:
                status = "invalid"
        finally:
            release(directory)
        reports.append({"mutant": name, "status": status, "path": relative, "output": str(directory)})
        write_json(output / "mutation-results.json", reports)
        print(f"{name}: {status}", flush=True)
    return {"mutants": reports, "divergences": [r for r in reports if r["status"] != "detected"]}
