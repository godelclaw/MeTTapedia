import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ExecutionResponses
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Consumers

/-! # Operational production controls on authored language installations -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ExecutionControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Discovery.Execution

@[noinline] def lambda : IO Unit := do
  let .ok installed := Consumers.generate BindingPipeline.Controls.originalLambda
    | throw (IO.userError "Authored lambda was refused")
  let some index := (List.finRange installed.indexed.headers.length).head?
    | throw (IO.userError "Lambda generated no modal interface")
  let identity := Consumers.lambdaIdentity
  let application := Pattern.apply "App" [identity, identity]
  let initial := Batch.begin installed index [] [application, identity]
  if !initial.certificate.isEmpty || initial.settled then
    throw (IO.userError "Initial execution invented a receipt or completed coverage")
  let finished := initial.resume 2000
  if !finished.settled then throw (IO.userError "Lambda source agendas did not settle")
  let certificate := finished.certificate
  if certificate.length != 1 || !(certificate.all fun witness =>
      witness.source == application && witness.payload.target == identity) then
    throw (IO.userError "Produced lambda receipts do not identify the beta application and target")
  let split := (initial.resume 13).resume 1987
  if split.certificate != certificate then
    throw (IO.userError "Resuming source schedulers changed produced receipts")
  if (finished.resume 23).certificate != certificate then
    throw (IO.userError "Settled source receipt list changed")
  IO.println "Discovery execution: beta receipt produced; stuck source exhausted; exact pause/resume"

@[noinline] def duplicateOrigins : IO Unit := do
  let .ok installed := Consumers.generate Consumers.sharedLanguage
    | throw (IO.userError "Authored duplicate-origin language was refused")
  let some index := (List.finRange installed.indexed.headers.length).head?
    | throw (IO.userError "Shared language generated no modal interface")
  let initial := Batch.begin installed index [] [Consumers.sharedSource, Consumers.sharedSource]
  let finished := initial.resume 1000
  if !finished.settled then throw (IO.userError "Duplicate-origin source agendas did not settle")
  let certificate := finished.certificate
  if certificate.map (·.payload.index) != [0, 1, 0, 1] then
    throw (IO.userError "Source duplication or declaration origins were merged")
  if !(certificate.all fun witness => witness.payload.target == Consumers.sharedTarget) then
    throw (IO.userError "Duplicate-origin source emitted an incorrect target")
  if ((initial.resume 17).resume 983).certificate != certificate then
    throw (IO.userError "Pause/resume lost duplicate-origin order")
  IO.println "Discovery execution: equal targets retain both declarations and repeated source occurrences"

def main : IO Unit := do
  lambda
  duplicateOrigins

#eval main

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ExecutionControls
