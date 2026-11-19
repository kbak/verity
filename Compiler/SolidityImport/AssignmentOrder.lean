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

/-- A comparison can read a word literal or a binding protected on every continuing path. -/
def protectedComparisonWord (pre : List Stmt) : Expr → Bool
  | .literal _ => prefixList [] pre
  | .localVar name | .param name => prefixList [name] pre
  | _ => false

/-- The lowered comparison has two total scalar reads, both independent of the assignment. -/
def protectedComparison (pre : List Stmt) : Expr → Bool
  | .eq a b | .lt a b | .le a b | .gt a b | .ge a b | .slt a b | .sgt a b =>
    protectedComparisonWord pre a && protectedComparisonWord pre b
  | _ => false

/-- Non-strict signed comparisons and inequality can negate a lowered comparison. -/
def protectedComparisonSibling (pre : List Stmt) (expr : Expr) : Bool :=
  match expr with
  | .logicalNot inner => protectedComparison pre inner
  | _ => protectedComparison pre expr

end Compiler.CompilationModel.SolidityImport
