"""Exercise the public observed import command rather than constructing AST environments."""
import json


REJECTION_DRIVER = r'''
elab "expect_import_rejection " code:str " containing " expected:str : command => do
  let saved ← get
  let parsedCmd ← match Parser.runParserCategory (← getEnv) `command code.getString with
    | .ok parsed => pure parsed
    | .error message => throwError "test command parse failed: {message}"
  let diagnostic ← try
    elabCommand parsedCmd
    pure ""
  catch error => pure (← error.toMessageData.toString)
  let messages ← (← get).messages.toList.mapM (fun m => m.data.toString)
  let after ← getEnv
  let leaked := ["rejected.observed", "rejected.report", "rejected.sourceDigest",
    "rejected.scope", "rejected.model", "rejected.covered"].any
      (fun name => after.contains name.toName)
  set saved
  if leaked then throwError "failed import left declarations behind"
  unless (diagnostic ++ String.intercalate "\n" messages).contains expected.getString do
    throwError "missing import rejection {expected.getString}: {diagnostic}; parser {parsedCmd.getKind}; messages {messages}"
'''


def write_driver(path, template, output, source, rows, optimized, storage, spec=None):
    spec = spec or {}
    (output / 'Source.sol').write_text(source)
    signatures = list(dict.fromkeys(row['signature'] for row in rows))
    contract = spec.get('contract', 'LegacyObservedStorage' if storage else 'LegacyObservedControl')
    profile = ('{ solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
               'viaIR := false, bytecodeHash := "none", optimizerRuns := ' + ('some 800' if optimized else 'none') + ' }')

    def command(alias, functions, *, observed=True):
        return (f'solidity_import {alias} from {json.dumps(str(output))} entry "Source.sol" '
                f'using {profile} ' + ('observed ' if observed else '') + f'contract {contract}\n' +
                '\n'.join('  function ' + signature for signature in functions))

    negatives = ([('ambiguousRecord(uint256,uint128,uint256)',
                   'assignment expression in multi-argument call requires explicit evaluation-order support'),
                  ('recursive(uint256)', 'recursive observed helper call')] if storage else
                 [('unguarded(uint256)', 'division/modulo needs a nonzero literal'),
                  ('staleGuard(uint256)', 'division/modulo needs a nonzero literal'),
                  ('unnamedResult()', 'observed control returns must be named')])
    negatives = spec.get('negatives', negatives)
    rejected = [signature.split('(')[0] for signature, _ in negatives]
    guards = []
    for signature, message in negatives:
        guards.append((command('rejected', [signature]), message))
    guards += [(command('rejected', [signatures[0], 'missing()']), 'no function'),
               (command('rejected', [signatures[0], signatures[0]]), 'is imported twice'),
               (command('rejected', [signatures[0]]).replace('viaIR := false',
                    'viaIR := false, sourceGas := true'), 'without source-gas instrumentation'),
               (command('rejected', [signatures[0]], observed=False),
                spec.get('bounded_rejection',
                    'a while loop condition must test v != 0 or v > 0' if storage else
                    'Solidity 0.7.6 while loops require an unsigned local compared with zero'))]
    guarded = '\n'.join('expect_import_rejection ' + json.dumps(code) + ' containing ' +
                        json.dumps(message) for code, message in guards)
    root = 'root' if storage else 'root.control'
    path.write_text('import Compiler.SolidityImport.ObservedCommand\nimport Compiler.SolidityImport.ObservedExecution\n' + template +
        '\n' + REJECTION_DRIVER + '\n' + guarded + '\n' + command('tested', signatures) +
        '\n' + command('repeated', signatures) + r'''
run_elab do
  if (← getEnv).contains `tested.model || (← getEnv).contains `tested.covered then
    throwError "observed import falsely exports bounded-model coverage"

#eval do
  let .ok input := Json.parse (← IO.FS.readFile INPUT) | throw (IO.userError "invalid input")
  let .ok rows := input.getObjValAs? (Array Json) "cases" | throw (IO.userError "missing cases")
  let .ok mutation := input.getObjValAs? String "mutation" | throw (IO.userError "missing mutation")
  unless tested.sourceDigest == repeated.sourceDigest && tested.sourceDigest.length == 64 do
    throw (IO.userError "unstable or missing source digest")
  unless tested.report.roots == ROOTS && tested.report.functions.all (!·.denoteCovered) do
    throw (IO.userError "incorrect root inventory or coverage claim")
  let mut observed : Array Json := #[]
  let mut compiled : Array Json := #[]
  for fn in tested.observed.functions do
    let .ok selected := ObservedExecution.findRoot tested.observed fn.name
      | throw (IO.userError "downstream root selection failed")
    let root := { selected with control := { selected.control with
      body := perturb mutation selected.control.body } }
    let .ok code := ControlCodegen.scalarFrame root.control.params root.control.body root.fields
      | throw (IO.userError "imported code generation failed")
    compiled := compiled.push (Json.mkObj [("name", toJson fn.name), ("body", toJson code)])
    for row in rows do
      if (row.getObjValAs? String "function").toOption == some fn.name then
        match evaluate EVALUATE_ROOT row with
        | .ok result => observed := observed.push result
        | .error message => throw (IO.userError message)
  IO.FS.writeFile OUTPUT (Json.mkObj [("observations", toJson observed),
    ("compiled", toJson compiled), ("rejected", toJson (REJECTED : List String)),
    ("report", toJson tested.report.toText), ("settings", toJson tested.report.settingsJson),
    ("sourceDigest", toJson tested.sourceDigest),
    ("included", toJson (tested.report.includedFunctions.map (fun (f : ImportedFunction) => f.name))),
    ("excluded", toJson (tested.report.excludedFunctions.map (fun (f : ImportedFunction) => f.name)))]).pretty
'''.replace('INPUT', json.dumps(str(output/'input.json')))
        .replace('OUTPUT', json.dumps(str(output/'model.json')))
        .replace('ROOTS', '[' + ', '.join(json.dumps(s.split('(')[0]) for s in signatures) + ']')
        .replace('REJECTED', '[' + ', '.join(map(json.dumps, rejected)) + ']')
        .replace('EVALUATE_ROOT', root))


def validate_metadata(model, optimized, storage, roots, spec=None):
    settings = json.loads(model['settings'])
    if (settings['evmVersion'] != 'istanbul' or 'viaIR' in settings
            or settings['optimizer'] != dict(enabled=optimized, runs=800 if optimized else 200)
            or settings['metadata'] != dict(bytecodeHash='none')):
        raise ValueError('ordinary importer changed the selected source profile')
    included = set(roots)
    excluded = {'unguarded', 'staleGuard', 'viewOnly', 'unnamedResult'}
    if storage:
        included |= {'walkHelper', 'captureHelper', 'recordHelper', 'mappingHelper',
                     'voidHelper', 'forward'}
        excluded = {'ambiguousRecord', 'recursive', 'recursionHelper'}
    if spec:
        included = set(roots) | set(spec['helpers'])
        excluded = set(spec['excluded'])
    if set(model['included']) != included or set(model['excluded']) != excluded:
        raise ValueError('ordinary importer closure reporting differs')
