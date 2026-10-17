import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingGeneratedSchemaTyping
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingTreeAdmission
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaSource
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingFrameChecking

/-!
# Every original typed firing is covered by its generated native schemas

For every ambient context and admitted authored tree profile, original scoped
matching and ordered premises construct the complete native schema frame.
The construction derives typing and positions from the language generator,
retains every original receipt, and compares named declarations through their
canonical alpha reading. Actual source inhabitants are canonical representatives.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingGeneratedFrameCoverage

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise GeneralExecutionAdmission
open RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage NativeBindingSchemaCaptures NativeBindingSchemaFocus

theorem frame_exists {plan : Plan} (index : NativeEventDeclarations.Index plan)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (labels : (plan.snapshot.language.terms.map (·.label)).Nodup)
    (treeChecked : NativeBindingTreeAdmission.check plan = true)
    {ambient : List String} {sort : String}
    (program : (NativeEventDeclarations.schema plan index).programCarrier = .base sort)
    (point : Selected (NativeEventDeclarations.schema plan index) ambient sort) :
    ∃ frame : Frame (NativeEventDeclarations.schema plan index) ambient sort,
      frame.point = point := by
  let schema := NativeEventDeclarations.schema plan index
  have shape := NativeBindingTreeAdmission.generated_schema_tree treeChecked index
  have reconstructed := NativeBindingSchemaSource.reconstructed schema point shape
  obtain ⟨rawSource, instantiated, erased⟩ := Option.map_eq_some_iff.mp reconstructed
  obtain ⟨site, licensed, position, focusBound, focusType⟩ :=
    NativeBindingGeneratedSchemaTyping.generated_licensed index
  have sourceTyped : HasType plan.snapshot.language plan.snapshot.free
      ([] ++ NativeBindingEventAction.bound ambient) rawSource.eraseBinderMetadata schema.programCarrier := by
    rw [erased, program, List.nil_append, freeEmpty]
    exact toPattern_typed point.val.source
  have sourceObject : isObjectPattern rawSource.eraseBinderMetadata = true := by
    rw [erased]
    exact toPattern_object point.val.source
  obtain ⟨rawFocus, selected, typed, object, depth⟩ :=
    NativeBindingTypedFocusCoverage.instantiated_focus licensed labels instantiated shape sourceTyped sourceObject
  refine ⟨{
    point := point
    focus := rawFocus.eraseBinderMetadata
    typed := ?_
    object := object
    canonical := Pattern.eraseBinderMetadata_hasCanonicalBinderMetadata rawFocus
    selected := ?_
    source := reconstructed
    focusDepth := ?_
  }, rfl⟩
  · rw [focusBound, focusType]
    exact typed
  · refine ⟨rawFocus, ?_, rfl⟩
    rw [position]
    exact selected
  · rw [position, focusBound]
    exact depth

theorem checker_covers_every_firing {plan : Plan} (index : NativeEventDeclarations.Index plan)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (labels : (plan.snapshot.language.terms.map (·.label)).Nodup)
    (treeChecked : NativeBindingTreeAdmission.check plan = true)
    {ambient : List String} {sort : String}
    (program : (NativeEventDeclarations.schema plan index).programCarrier = .base sort)
    (point : Selected (NativeEventDeclarations.schema plan index) ambient sort) :
    ∃ frame,
      NativeBindingFrameChecking.frame? (NativeEventDeclarations.schema plan index) point = some frame ∧
      frame.point = point := by
  obtain ⟨frame, pointSame⟩ := frame_exists index freeEmpty labels treeChecked program point
  obtain ⟨checked, accepted, same⟩ :=
    NativeBindingFrameChecking.frame?_complete (NativeEventDeclarations.schema plan index) frame
  rw [pointSame] at accepted
  exact ⟨checked, accepted, same ▸ pointSame⟩

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingGeneratedFrameCoverage
