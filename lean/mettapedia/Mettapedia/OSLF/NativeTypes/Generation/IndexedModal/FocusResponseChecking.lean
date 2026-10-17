import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusMeaning

/-! # Executable evidence for a specified indexed modal response -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusMeaning

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Modal.NativeReceiptRechecking

variable {installed : Joined.Installed} {index : installed.Index} {ambient : List String}
variable (arguments : Arguments installed index ambient)
variable [targetDecidable : ∀ values assignment target, Decidable (arguments.target values assignment target)]

instance indexMatchesDecidable (payload : Payload) : Decidable (IndexMatches arguments payload) :=
  inferInstanceAs (Decidable (∀ _position, _ = _))

instance relyMatchesDecidable (values : RelyValues installed index ambient) (payload : Payload) :
    Decidable (RelyMatches values payload) :=
  inferInstanceAs (Decidable (∀ _position, _ = _))

def checkResponse (focus : Pattern) (values : RelyValues installed index ambient)
    (source : Pattern) (payload : Payload) : Option (Response arguments focus values) :=
  match installed.checkReceipt index ambient source payload with
  | none => none
  | some receipt =>
      if focused : receipt.frame.focus = focus then
        if indices : IndexMatches arguments (read receipt.firing.answer) then
          if relies : RelyMatches values (read receipt.firing.answer) then
            if target : arguments.target values receipt.firing.answer.completed receipt.firing.answer.target then
              some ⟨source, receipt, focused, indices, relies, target⟩
            else none
          else none
        else none
      else none

theorem checkResponse_read {focus source : Pattern} {values : RelyValues installed index ambient}
    {payload : Payload} {response : Response arguments focus values}
    (checked : checkResponse arguments focus values source payload = some response) :
    response.source = source ∧ read response.receipt.firing.answer = payload := by
  unfold checkResponse at checked
  split at checked
  · cases checked
  · rename_i receipt found
    split at checked
    · split at checked
      · split at checked
        · split at checked
          · cases Option.some.inj checked
            exact ⟨rfl, receipt.same.symm.trans (installed.checkReceipt_read found)⟩
          · cases checked
        · cases checked
      · cases checked
    · cases checked

theorem checkResponse_sound {focus source : Pattern} {values : RelyValues installed index ambient}
    {payload : Payload} {response : Response arguments focus values}
    (checked : checkResponse arguments focus values source payload = some response) :
    SourceResponse arguments focus values source payload := by
  obtain ⟨sameSource, samePayload⟩ := checkResponse_read arguments checked
  rw [← sameSource, ← samePayload]
  exact response.source_response

theorem checkResponse_complete {focus source : Pattern} {values : RelyValues installed index ambient}
    {payload : Payload} (valid : SourceResponse arguments focus values source payload) :
    ∃ response, checkResponse arguments focus values source payload = some response := by
  obtain ⟨firing, selected, focused, indices, relies, target⟩ := valid
  obtain ⟨receipt, checked, same⟩ := installed.checkReceipt_complete index ambient source payload firing selected
  have samePayload : read receipt.firing.answer = payload := receipt.same.symm.trans same
  have sameFocus := focus_unique receipt.frame same focused
  have indexMatch : IndexMatches arguments (read receipt.firing.answer) := samePayload ▸ indices
  have relyMatch : RelyMatches values (read receipt.firing.answer) := samePayload ▸ relies
  have targetMatch : arguments.target values receipt.firing.answer.completed receipt.firing.answer.target := by
    change arguments.target values (read receipt.firing.answer).completed (read receipt.firing.answer).target
    rw [samePayload]
    exact target
  refine ⟨⟨source, receipt, sameFocus, indexMatch, relyMatch, targetMatch⟩, ?_⟩
  simp only [checkResponse, checked, dif_pos sameFocus, dif_pos indexMatch,
    dif_pos relyMatch, dif_pos targetMatch]

theorem checkResponse_exact (focus : Pattern) (values : RelyValues installed index ambient)
    (source : Pattern) (payload : Payload) :
    (checkResponse arguments focus values source payload).isSome = true ↔
      SourceResponse arguments focus values source payload := by
  constructor
  · intro accepted
    cases checked : checkResponse arguments focus values source payload with
    | none => rw [checked] at accepted; cases accepted
    | some response => exact checkResponse_sound arguments checked
  · intro valid
    obtain ⟨response, checked⟩ := checkResponse_complete arguments valid
    rw [checked]
    rfl

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusMeaning
