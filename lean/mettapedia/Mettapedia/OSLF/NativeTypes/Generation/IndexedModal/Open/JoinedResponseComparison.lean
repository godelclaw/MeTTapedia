import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.BindingResponses
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusMeaningLaws

/-!
# Original event fibres and installed pointwise response membership

The indexed installation's independently specified source responses agree
with its original typed binding frames, retaining the exact source and
complete receipt payload. Pointwise native membership is consequently a
universal may assertion about those event fibres. Future-sensitive
classifiers additionally quantify over restrictions; this comparison does
not identify the two quantifiers.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.JoinedResponses

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Modal
open NativeReceiptRechecking
open FocusMeaning

variable {installed : Joined.Installed} {index : installed.Index} {ambient : List String}

def FrameResponse (arguments : Arguments installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient)
    (frame : SemanticReceipts.Frame installed.indexed installed.semantic index ambient) : Prop :=
  frame.focus = focus ∧ IndexMatches arguments (read frame.point.val.receipt) ∧
    RelyMatches values (read frame.point.val.receipt) ∧
    arguments.target values frame.point.val.receipt.completed frame.point.val.receipt.target

theorem frame_response_source {arguments : Arguments installed index ambient} {focus : Pattern}
    {values : RelyValues installed index ambient}
    {frame : SemanticReceipts.Frame installed.indexed installed.semantic index ambient}
    (response : FrameResponse arguments focus values frame) :
    SourceResponse arguments focus values
      (CurriedBindingLanguage.toPattern frame.point.val.source) (read frame.point.val.receipt) := by
  obtain ⟨focused, indices, relies, target⟩ := response
  refine ⟨frame.point.val.receipt.valid, frame.point.property, ?_, indices, relies, target⟩
  simpa only [NativeReceiptRechecking.read, focused] using frame.selected

/-- The original source term is preserved when a complete payload enters
the shared installed checker. -/
theorem checked_frame_source {source : Pattern} {payload : Payload}
    {receipt : installed.Receipt index ambient source}
    (checked : installed.checkReceipt index ambient source payload = some receipt) :
    CurriedBindingLanguage.toPattern receipt.frame.point.val.source = source := by
  unfold Joined.Installed.checkReceipt at checked
  split at checked
  · cases checked
  · rename_i firing firingChecked
    split at checked
    · cases checked
    · rename_i frame frameChecked
      cases Option.some.inj checked
      exact (installed.semantic.authored installed.indexed).checkReceiptFrame?_source
        installed.indexed.headers[index].origin firing.answer firing.selected frameChecked

theorem source_response_frame {arguments : Arguments installed index ambient} {focus source : Pattern}
    {values : RelyValues installed index ambient} {payload : Payload}
    (response : SourceResponse arguments focus values source payload) :
    ∃ frame : SemanticReceipts.Frame installed.indexed installed.semantic index ambient,
      FrameResponse arguments focus values frame ∧
      CurriedBindingLanguage.toPattern frame.point.val.source = source ∧
      read frame.point.val.receipt = payload := by
  obtain ⟨firing, selected, focused, indices, relies, target⟩ := response
  obtain ⟨receipt, checked, same⟩ := installed.checkReceipt_complete index ambient source payload firing selected
  refine ⟨receipt.frame, ?_, checked_frame_source checked, same⟩
  refine ⟨focus_unique receipt.frame same focused, ?_, ?_, ?_⟩
  · simpa only [same] using indices
  · simpa only [same] using relies
  · change arguments.target values (read receipt.frame.point.val.receipt).completed
      (read receipt.frame.point.val.receipt).target
    simpa only [same] using target

theorem frame_response_iff_source (arguments : Arguments installed index ambient) (focus source : Pattern)
    (values : RelyValues installed index ambient) (payload : Payload) :
    (∃ frame : SemanticReceipts.Frame installed.indexed installed.semantic index ambient,
      FrameResponse arguments focus values frame ∧
      CurriedBindingLanguage.toPattern frame.point.val.source = source ∧
      read frame.point.val.receipt = payload) ↔
      SourceResponse arguments focus values source payload := by
  constructor
  · rintro ⟨frame, response, sourced, same⟩
    simpa only [sourced, same] using frame_response_source response
  · exact source_response_frame

/-- The current universal family ranges over independently typed rely
values and original receipt frames, rather than a list of observed tests. -/
theorem inhabits_iff_frames (arguments : Arguments installed index ambient) (focus : Pattern) :
    Inhabits arguments focus ↔
      FocusAdmitted installed index ambient focus ∧
        ∀ values, Requested arguments values →
          ∃ frame : SemanticReceipts.Frame installed.indexed installed.semantic index ambient,
            FrameResponse arguments focus values frame := by
  rw [inhabits_iff_source]
  constructor
  · rintro ⟨admitted, all⟩
    refine ⟨admitted, fun values requested => ?_⟩
    obtain ⟨source, payload, response⟩ := all values requested
    obtain ⟨frame, held, _, _⟩ := source_response_frame response
    exact ⟨frame, held⟩
  · rintro ⟨admitted, all⟩
    refine ⟨admitted, fun values requested => ?_⟩
    obtain ⟨frame, held⟩ := all values requested
    exact ⟨CurriedBindingLanguage.toPattern frame.point.val.source,
      read frame.point.val.receipt, frame_response_source held⟩

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.JoinedResponses
