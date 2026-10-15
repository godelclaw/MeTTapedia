import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingFocusChecking

/-!
# Actual operational receipt admission into an authored schema event

This finite checker computes the authored instantiated focus, verifies its
sorting and canonical object shape, and checks source reconstruction and
local binder depth. Accepted frames retain the input receipt unchanged.
Its domain is exactly independently formed frames over that receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingFrameChecking

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise GeneralExecutionAdmission
open RuleBinding ScopedRuleMatching
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage
open Mettapedia.GSLT.LanguageDef.WellSorted
open NativeBindingEventAction (bound)
open NativeBindingSchemaCaptures NativeBindingSchemaFocus

variable {plan : Plan} (schema : Rules.Schema plan)

def frame? {ambient : List String} {sort : String} (point : Selected schema ambient sort) :
    Option (Frame schema ambient sort) :=
  match NativeBindingFocusChecking.focusAt? Substitution.instantiateBVar
      schema.declaration.rule schema.declaration.binding.spec ambient.length .left
      point.val.receipt.completed [] 0 schema.declaration.rule.left schema.position with
  | none => none
  | some focus =>
      if sorted : checkHasType plan.snapshot.language plan.snapshot.free
          (schema.focusBound ++ bound ambient) focus.val.eraseBinderMetadata schema.focusCarrier = true then
        if object : isObjectPattern focus.val.eraseBinderMetadata = true then
          if canonical : focus.val.eraseBinderMetadata.hasCanonicalBinderMetadata = true then
            if sourced : (instantiateAt? schema.declaration.rule schema.declaration.binding.spec ambient.length
                .left [] 0 point.val.receipt.completed schema.declaration.rule.left).map Pattern.eraseBinderMetadata = some (toPattern point.val.source) then
              if depth : NativeFocusSubstitution.depthAt? schema.declaration.rule.left schema.position 0 =
                  some schema.focusBound.length then
                some ⟨point, focus.val.eraseBinderMetadata, checkHasType_sound sorted, object, canonical,
                  ⟨focus.val, focus.property, rfl⟩, sourced, depth⟩
              else none
            else none
          else none
        else none
      else none

theorem frame?_point {ambient : List String} {sort : String} (point : Selected schema ambient sort)
    {frame : Frame schema ambient sort} (checked : frame? schema point = some frame) :
    frame.point = point := by
  unfold frame? at checked
  split at checked
  · cases checked
  · split at checked
    · split at checked
      · split at checked
        · split at checked
          · split at checked
            · cases Option.some.inj checked
              rfl
            · cases checked
          · cases checked
        · cases checked
      · cases checked
    · cases checked

theorem frame?_complete {ambient : List String} {sort : String} (frame : Frame schema ambient sort) :
    ∃ checked, frame? schema frame.point = some checked ∧ checked = frame := by
  obtain ⟨rawFocus, selected, erased⟩ := frame.selected
  obtain ⟨focus, focused, sameRaw⟩ := NativeBindingFocusChecking.focusAt?_complete selected
  have same : focus.val.eraseBinderMetadata = frame.focus :=
    (congrArg Pattern.eraseBinderMetadata sameRaw).trans erased
  have typed := checkHasType_complete_of_object frame.typed frame.object
  unfold frame?
  rw [focused]
  have sameTyped : checkHasType plan.snapshot.language plan.snapshot.free
      (schema.focusBound ++ bound ambient) focus.val.eraseBinderMetadata schema.focusCarrier = true := by simpa only [same] using typed
  have sameObject : isObjectPattern focus.val.eraseBinderMetadata = true := by simpa only [same] using frame.object
  have sameCanonical : focus.val.eraseBinderMetadata.hasCanonicalBinderMetadata = true := by simpa only [same] using frame.canonical
  simp only [sameTyped, sameObject, sameCanonical, frame.source, frame.focusDepth, ↓reduceDIte]
  refine ⟨_, rfl, ?_⟩
  exact frame_ext schema rfl same

theorem frame?_exact {ambient : List String} {sort : String} (point : Selected schema ambient sort) :
    (∃ checked, frame? schema point = some checked) ↔
      ∃ frame : Frame schema ambient sort, frame.point = point := by
  constructor
  · rintro ⟨checked, found⟩
    exact ⟨checked, frame?_point schema point found⟩
  · rintro ⟨frame, same⟩
    obtain ⟨checked, found, _⟩ := frame?_complete schema frame
    rw [same] at found
    exact ⟨checked, found⟩

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingFrameChecking
