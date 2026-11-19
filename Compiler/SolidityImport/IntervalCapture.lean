import Compiler.SolidityImport.IntervalSearch

open Lean Meta

namespace Compiler.CompilationModel.SolidityImport.IntervalCapture

/-- The lexical environments immediately before and after the actual emitted iteration. -/
structure Capture where
  node : Json
  before : Env
  after : Env
  doneName : String
  iteration : IntervalSearch.Iteration

private initialize selected : EnvExtension (Option (String × Nat × IO.Ref (Option Capture))) ←
  registerEnvExtension (pure none)

private initialize capturedId : InternalExceptionId ←
  registerInternalExceptionId `SolidityImport.intervalCaptured

/-- Stop only a matching, explicitly requested import. Ordinary bounded lowering continues
through this hook. The typed receiver is scoped to a single invocation using Lean's environment. -/
def atSite (node : Json) (lowerExpr : Json → M Val) (lowerBody : Json → M (Array Stmt)) :
    M Unit := do
  let some (file, offset, receiver) := selected.getState (← getEnv) | return
  let frame ← get
  let id ← mNat (← mField node "id")
  let src ← mStr (← mField node "src")
  unless frame.nodeFile.find? id == some file &&
      (src.splitOn ":").head?.bind String.toNat? == some offset do return
  -- Re-record callees even if an earlier statement in the root already visited them.
  modify fun e => { e with included := #[] }
  let doneName ← fresh
  let iteration ← IntervalSearch.lowerIteration node doneName lowerExpr lowerBody
  receiver.set (some { node, before := frame, after := ← get, doneName, iteration })
  throw (Exception.internal capturedId)

/-- Capture the first static lowering instance at this exact source offset. Importer
errors retain their original diagnostic. Later source statements are outside the slice. -/
def firstInstance (file : String) (offset : Nat) (visit : MetaM Unit) : MetaM Capture := do
  let receiver ← IO.mkRef (none : Option Capture)
  let env := selected.setState (← getEnv) (some (file, offset, receiver))
  try
    withEnv env visit
  catch err =>
    match err with
    | .internal id _ => unless id == capturedId do throw err
    | _ => throw err
  let some result ← receiver.get | throwError "selected interval source site was not reached"
  return result

end Compiler.CompilationModel.SolidityImport.IntervalCapture
