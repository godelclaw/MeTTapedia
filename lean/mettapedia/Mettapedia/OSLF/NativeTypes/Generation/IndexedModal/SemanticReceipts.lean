import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.ReceiptChecking
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeReceiptChecking

/-!
# Indexed interfaces with independently interpreted scoped receipt families

A checked semantic companion uses the existing authored receipt interpreter.
Its operational presentation is the identical installed presentation; the
older projected cube is retained only for that interpreter's existing code
alphabet. Source-indexed receipt readouts retain complete payloads and typed
ordered index values, and expose the actual binder-local focus.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SemanticReceipts

open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open Mettapedia.OSLF.NativeTypes.Modal
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open NativeReceiptRechecking
open NativeBindingEventAction (bound)

variable (installed : Pipeline.Installed)

structure Companion where
  vertex : CubeEnrichment.Vertex (NativeCubeProfile.signature installed.operational)
  decoded : NativeCubeProfile.vertex? installed.operational = some vertex
  freeEmpty : (BindingPipeline.plan installed.operational.generated).snapshot.free =
    Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
  operationalMeaning : NativeOperationalProfile.check installed.operational.Environment = true
  modalMeanings : ∀ index : Fin installed.operational.modal.length,
    NativeBindingModalAdmission.Admitted installed.operational.modal[index]
  sourceTrees : NativeBindingTreeAdmission.check (BindingPipeline.plan installed.operational.generated) = true

def admit? : Option (Companion installed) :=
  let operational := installed.operational
  if freeTypesEmpty : (BindingPipeline.plan operational.generated).snapshot.freeTypes = [] then
    have freeEmpty : (BindingPipeline.plan operational.generated).snapshot.free =
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty := by
      funext name
      change ((BindingPipeline.plan operational.generated).snapshot.freeTypes.find?
        (fun entry => entry.1 == name)).map Prod.snd = none
      rw [freeTypesEmpty]
      rfl
    if operationalMeaning : NativeOperationalProfile.check operational.Environment = true then
      let meanings : Option (∀ index : Fin operational.modal.length,
          NativeBindingModalAdmission.Admitted operational.modal[index]) :=
        NativeBindingModalAdmission.allFin?
          (fun index : Fin operational.modal.length =>
            NativeBindingModalAdmission.check? operational.modal[index])
      match meanings with
      | none => none
      | some modalMeanings =>
          if sourceTrees : NativeBindingTreeAdmission.check (BindingPipeline.plan operational.generated) = true then
            match decoded : NativeCubeProfile.vertex? operational with
            | none => none
            | some decodedVertex =>
                some ⟨decodedVertex, decoded, freeEmpty, operationalMeaning, modalMeanings, sourceTrees⟩
          else none
    else none
  else none

def Companion.authored (companion : Companion installed) : AuthoredPipeline.Installed :=
  ⟨installed.operational, companion.vertex, companion.decoded, companion.freeEmpty,
    companion.operationalMeaning, companion.modalMeanings, companion.sourceTrees⟩

variable (companion : Companion installed)

abbrev programSort (index : Fin installed.headers.length) :=
  (companion.authored installed).nativeProgramSort installed.headers[index].origin

abbrev Frame (index : Fin installed.headers.length) (ambient : List String) :=
  NativeBindingSchemaFocus.Frame (installed.schema index) ambient (programSort installed companion index)

def frame? (index : Fin installed.headers.length) {ambient : List String} {pattern : Pattern}
    (receipt : Pipeline.Installed.Receipt installed index (bound ambient)
      (.base (programSort installed companion index)) pattern) :
    Option (Frame installed companion index ambient) :=
  (companion.authored installed).checkReceiptFrame? installed.headers[index].origin receipt.answer receipt.selected

theorem frame_complete (index : Fin installed.headers.length) {ambient : List String} {pattern : Pattern}
    (receipt : Pipeline.Installed.Receipt installed index (bound ambient)
      (.base (programSort installed companion index)) pattern) :
    ∃ frame, frame? installed companion index receipt = some frame ∧ read frame.point.val.receipt = read receipt.answer :=
  (companion.authored installed).checkReceiptFrame?_complete installed.headers[index].origin receipt.answer receipt.selected

theorem frame_read (index : Fin installed.headers.length) {ambient : List String} {pattern : Pattern}
    (receipt : Pipeline.Installed.Receipt installed index (bound ambient)
      (.base (programSort installed companion index)) pattern)
    {frame : Frame installed companion index ambient}
    (checked : frame? installed companion index receipt = some frame) :
    read frame.point.val.receipt = read receipt.answer :=
  (companion.authored installed).checkReceiptFrame?_read installed.headers[index].origin receipt.answer receipt.selected checked

/-- The actual index capture has its authored dependencies, ambient scope,
result sort and canonical object metadata. -/
def indexValue? (index : Fin installed.headers.length) {ambient : List String}
    (frame : Frame installed companion index ambient) (position : Fin installed.headers[index].indices.length) :=
  NativeBindingSchemaCaptures.readSlot (installed.schema index) frame.point
    installed.headers[index].indices[position].slot

theorem indexValue_complete (index : Fin installed.headers.length) {ambient : List String}
    (frame : Frame installed companion index ambient) (position : Fin installed.headers[index].indices.length) :
    ∃ value, indexValue? installed companion index frame position = some value := by
  apply NativeBindingSchemaCaptures.readSlot_complete
  apply NativeBindingSchemaCaptures.matched_present
  exact installed.headers[index].indicesMatched _ (List.getElem_mem position.isLt)

theorem indexValue_read (index : Fin installed.headers.length) {ambient : List String}
    (frame : Frame installed companion index ambient) (position : Fin installed.headers[index].indices.length)
    {value : NativeBindingSchemaCaptures.SlotValue (installed.schema index)
      installed.headers[index].indices[position].slot ambient}
    (checked : indexValue? installed companion index frame position = some value) :
    ScopedRuleMatching.lookup frame.point.val.receipt.completed
      installed.headers[index].indices[position].slot.name = some value.val :=
  NativeBindingSchemaCaptures.readSlot_value _ _ _ checked

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SemanticReceipts
