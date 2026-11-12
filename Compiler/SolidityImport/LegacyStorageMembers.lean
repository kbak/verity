import Compiler.SolidityImport.ExprHelpers

/-! Declaration-bound scalar access to a top-level legacy storage struct.
Only the non-value receiver is exempted from the legacy struct-type rejection.
Whole structs, aliases, nested paths and unsupported scalar types remain excluded. -/
namespace Compiler.CompilationModel.SolidityImport
open Lean

/-- Recognize a direct scalar member of an actual storage declaration by AST IDs.
The shared lowering still validates its solc storage layout and member projection. -/
def legacyScalarStorageMember (node : Json) (env : Env) : Bool :=
  (do
    guard (optStr node "nodeType" == some "MemberAccess")
    let base ← field? node "expression"
    guard (optStr base "nodeType" == some "Identifier")
    let rootId ← (field? base "referencedDeclaration").bind (·.getNat?.toOption)
    let root ← env.stateVars.find? rootId
    guard ((field? root "stateVariable").bind (·.getBool?.toOption) == some true)
    let rootTy ← (field? root "typeDescriptions").bind (optStr · "typeString")
    let baseTy ← (field? base "typeDescriptions").bind (optStr · "typeString")
    guard (rootTy.startsWith "struct " && baseTy == rootTy ++ " storage ref")
    let typeName ← field? root "typeName"
    guard (optStr typeName "nodeType" == some "UserDefinedTypeName")
    let structId ← (field? typeName "referencedDeclaration").bind (·.getNat?.toOption)
    let declaration ← env.structs.find? structId
    guard (optStr declaration "nodeType" == some "StructDefinition")
    let members ← (field? declaration "members").bind (·.getArr?.toOption)
    let memberId ← (field? node "referencedDeclaration").bind (·.getNat?.toOption)
    let member ← members.find? fun m =>
      (field? m "id").bind (·.getNat?.toOption) == some memberId
    guard (optStr member "nodeType" == some "VariableDeclaration")
    guard (optStr member "name" == optStr node "memberName")
    let ty ← (field? member "typeDescriptions").bind (optStr · "typeString")
    guard ((field? node "typeDescriptions").bind (optStr · "typeString") == some ty)
    return ty == "bool" || ty == "address" || ty == "address payable" || ty == "bytes32" ||
      (ty.startsWith "uint" && (bitsOf ty).any fun n => 0 < n && n ≤ 256 && n % 8 == 0)
    : Option Bool).getD false

end Compiler.CompilationModel.SolidityImport
