import Compiler.CompilationModel

/-! Executable local-binding frame checks shared by the importer and its proofs. -/
namespace Compiler.CompilationModel.SolidityImport

mutual
/-- A prefix can only continue or revert, and cannot assign a protected name. -/
 def prefixStmt (keys : List String) : Stmt → Bool
  | .letVar name _ | .assignVar name _ => !keys.contains name
  | .ite _ yes no => prefixList keys yes && prefixList keys no
  | .panic _ => true
  | _ => false
 def prefixList (keys : List String) : List Stmt → Bool
  | [] => true
  | s :: ss => prefixStmt keys s && prefixList keys ss
end

/-- Admit a local read only across a world-preserving prefix that cannot rebind it. -/
def localAssignmentSibling (pre : List Stmt) : Expr → Bool
  | .localVar name => prefixList [name] pre
  | _ => false

end Compiler.CompilationModel.SolidityImport
