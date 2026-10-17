import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.JoinedRuntime
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.OriginLaws

/-! # Vocabulary and parameter choices affect the actual joined generator -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.PolicyControls

open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

@[noinline] def run : IO Unit := do
  let language := Consumers.sharedLanguage
  let snapshot := BindingPipeline.Controls.snapshot language
  let fragment := BindingPipeline.Controls.fragment
  let logic := BindingPipeline.Controls.fullLogic
  let .ok enabled := Consumers.generate language | throw (IO.userError "Shared-index language refused")
  let .ok disabled := Joined.generate snapshot fragment
      {logic with observations := {logic.observations with core := {logic.observations.core with modal := false}}}
      (fun _ => .star, fun _ => .star) [] | throw (IO.userError "Modal-disabled language refused")
  if !disabled.indexed.headers.isEmpty then throw (IO.userError "Disabled modal formers remain enabled")
  if disabled.indexed.operational.modal.length != enabled.indexed.operational.modal.length then
    throw (IO.userError "Vocabulary restriction changed operational occurrences")
  let .ok restricted := Joined.generate snapshot fragment {logic with native := ⟨[]⟩}
      (fun _ => .star, fun _ => .star) [] | throw (IO.userError "Restricted vocabulary refused installation")
  for index in List.finRange restricted.indexed.headers.length do
    if restricted.checkShared (restricted.formationCertificate index)
        (JoinedRuntime.formationJudgment restricted index) != .vocabularyRefused then
      throw (IO.userError "Unsupported formation confused with a negative answer")
  let selectedFragment := {fragment with operational := {fragment.operational with ruleIndices := some [1]}}
  let .ok selected := Joined.generate snapshot selectedFragment logic (fun _ => .star, fun _ => .star) []
    | throw (IO.userError "Selected declaration refused")
  if selected.indexed.headers.isEmpty then throw (IO.userError "Selected rule lost all modal families")
  for index in List.finRange selected.indexed.headers.length do
    let origin := selected.sourceOrigin index
    if origin.authoredDeclaration != 1 || origin.selectedDeclaration != 0 then
      throw (IO.userError "Authored declaration confused with selected execution ordinal")
  let receipts := JoinedRuntime.payloads selected [] "Program" Consumers.sharedSource 500
  if receipts.map (·.index) != [0] then throw (IO.userError "Selected executor ignored its rule profile")
  for payload in receipts do
    let retained := (List.finRange selected.indexed.headers.length).any fun index =>
      match selected.checkSourceReceipt index [] Consumers.sharedSource payload with
      | none => false
      | some receipt => receipt.origin.authoredDeclaration == 1 && receipt.origin.selectedDeclaration == 0
    if !retained then throw (IO.userError "Source-indexed receipt did not retain both declaration coordinates")
  let .ok kinds := Joined.generate snapshot fragment logic (fun _ => .box, fun _ => .box) []
    | throw (IO.userError "Kind profile refused")
  if enabled.indexed.headers.length != kinds.indexed.headers.length then
    throw (IO.userError "Profile changed source occurrence origins")
  if !enabled.indexed.headers.any (fun header => !header.indices.isEmpty) then
    throw (IO.userError "Shared index omitted")
  if !enabled.indexed.headers.any (fun header => enabled.indexed.operational.modal[header.origin].focus !=
      enabled.indexed.operational.modal[header.origin].program) then
    throw (IO.userError "Heterogeneous focus omitted")
  for index in List.finRange enabled.indexed.headers.length do
    if (enabled.indexed.interfaces index).resultSort != .star then
      throw (IO.userError "Target classifier sort ignored")
    JoinedRuntime.checkOne enabled index
  for index in List.finRange kinds.indexed.headers.length do
    if (kinds.indexed.interfaces index).resultSort != .box then
      throw (IO.userError "Changed target classifier sort ignored")
    JoinedRuntime.checkOne kinds index
  IO.println "Policy controls: modal vocabulary, full slots, focus carrier and kind profile passed"

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.PolicyControls
