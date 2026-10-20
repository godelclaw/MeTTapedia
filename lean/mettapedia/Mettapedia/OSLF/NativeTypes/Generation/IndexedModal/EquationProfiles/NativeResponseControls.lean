import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.NativeResponses
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.ControlsPreparation
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.QueryLaws

/-!
# Generated native questions through the root occurrence adapter

Independent rely domains and dependent result conditions are prepared before
execution. The original scoped payload constructs a general root occurrence.
The adapter rejects changed declaration ordinals, caller contexts, capture
evidence and dependent targets while retaining every original payload field.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.NativeResponseControls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Modal NativeReceiptRechecking
open FocusMeaning FiniteFocusChecking
open Discovery.ControlsPreparation Discovery.ControlsParameters

def checkQuestion {installed : Joined.Installed} {ambient : List String}
    (question : FocusQuery.Question installed ambient) (fuel : Nat) : IO Nat := do
  let session := Discovery.discover question fuel
  let some membership := session.membership?
    | throw (IO.userError "Native adapter fixture failed independent family membership")
  let mut checked := 0
  for input in (requests question.parameters).attach do
    let response := membership.family.respond input.val ((requests_exact question.parameters input.val).mp input.property)
    let original := read response.receipt.firing.answer
    let receipt := RootReceipts.pack (installed.indexed.schema question.index).declaration
      (NativeBindingEventAction.bound ambient) (NativeResponses.expected installed question.index) response.source original
    let _valid := NativeResponses.source_response_pack_valid question.parameters question.focus input.val
      response.source_response
    if RootReceipts.payload receipt != original then
      throw (IO.userError "Root occurrence adapter changed a source receipt field")
    if !NativeResponses.accepts question.parameters question.focus input.val receipt then
      throw (IO.userError "Generated contextual response failed its general occurrence observation")
    let ordinal := {receipt with job := {receipt.job with ordinal := (NativeResponses.plan installed).rules.length}}
    if NativeResponses.accepts question.parameters question.focus input.val ordinal then
      throw (IO.userError "Out-of-range execution ordinal was accepted as the native origin")
    let context := {receipt with job := {receipt.job with site :=
      {receipt.job.site with context := .lambda none .hole}}}
    if NativeResponses.accepts question.parameters question.focus input.val context then
      throw (IO.userError "Changed caller context with the same address was accepted")
    let captures := {receipt with captured := []}
    if !receipt.captured.isEmpty && NativeResponses.accepts question.parameters question.focus input.val captures then
      throw (IO.userError "Missing captured assignment was accepted")
    let completed := {receipt with completed := []}
    if !receipt.completed.isEmpty && NativeResponses.accepts question.parameters question.focus input.val completed then
      throw (IO.userError "Missing completed assignment was accepted")
    let forbidden := {question.parameters with target := fun _ _ _ => false}
    if NativeResponses.accepts forbidden question.focus input.val receipt then
      throw (IO.userError "The dependent target was ignored by the root occurrence adapter")
    checked := checked + 1
  if checked = 0 then throw (IO.userError "Native adapter fixture contained no requested inputs")
  pure checked

#eval do
  let lambda ← install BindingPipeline.Controls.originalLambda
  let identity ← expect (lambdaQuestion lambda)
  let binder ← expect (binderQuestion lambda)
  let letCase ← install BindingPipeline.Controls.originalLetCase
  let pair ← expect (caseQuestion letCase)
  let first ← checkQuestion identity 2000
  let second ← checkQuestion binder 2000
  let third ← checkQuestion pair 2000
  if first != 2 || second != 1 || third != 4 then
    throw (IO.userError "Native adapter lost independently declared rely inputs")
  IO.println "NativeRootOccurrenceAdapter: 7 requested responses; full payloads, ordinals, contexts and dependent targets checked"

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.NativeResponseControls
