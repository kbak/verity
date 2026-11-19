import Compiler.SolidityImport.LegacyCallTuples

namespace Compiler.CompilationModel.SolidityImport.LegacyStaticCalls
open Lean

/-- Recognize a low-level STATICCALL tuple. -/
abbrev applies := LegacyCallTuples.isStaticCall

/-- Lower a legacy STATICCALL and retain the complete return buffer. -/
def lower (node : Json) (leaf : Json → M Val) (bytes : Json → M EncodedBytes) :
    M (Array Stmt) := do
  unless applies node do failAt node "expected a raw static call tuple"
  LegacyCallTuples.lower node leaf bytes

end Compiler.CompilationModel.SolidityImport.LegacyStaticCalls
