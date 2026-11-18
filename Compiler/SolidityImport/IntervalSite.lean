import Verity.Core.Model.Types

namespace Compiler.CompilationModel.SolidityImport.CertifiedInterval

/-- The captured frame and source-ordered statements for one iteration of a selected loop.
Declaration IDs refer to the checked solc AST. Scalar locals, flattened struct members and
fixed storage array bases retain their specialized frame bindings. -/
structure Site where
  sourceDigest : String
  root : String
  file : String
  sourceRange : String
  callStack : List Nat
  frameAllocation : Nat
  locals : List (Nat × Expr)
  structLocals : List (Nat × List (String × String × String))
  arrayBases : List (Nat × Expr × Nat × Nat)
  /-- Lexical words the iteration may read before assigning them. -/
  inputs : List String
  bits : Nat
  lowName : String
  highName : String
  midName : String
  doneName : String
  fields : List Field
  body : List Stmt

end Compiler.CompilationModel.SolidityImport.CertifiedInterval
