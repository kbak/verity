import Compiler.SolidityImport.ExprHelpers

/-! Select the original-bytecode variant only under the explicit source gas profile. -/
namespace Compiler.CompilationModel.SolidityImport.SourceGasCalls
open Lean

/-- Both profiles use the same closed ABI layout; metered calls require a source site. -/
def module (node : Json) (result : String) (kind : Compiler.ECM.LegacyStaticKind) :
    M Compiler.ECM.ExternalCallModule := do
  if (← get).sourceGas then
    let site ← mStr (← mField node "src")
    if site.isEmpty then failAt node "static call source gas site is missing"
    return Compiler.ECM.SourceStaticCall.module result kind site
  else
    return match kind with
      | .recover => Compiler.ECM.LegacySignatureCall.recoverModule result
      | .bytes4 selector => Compiler.ECM.LegacySignatureCall.bytes4Module result selector
      | .bool selector count => Compiler.ECM.LegacyBoolCall.module result selector count

end Compiler.CompilationModel.SolidityImport.SourceGasCalls
