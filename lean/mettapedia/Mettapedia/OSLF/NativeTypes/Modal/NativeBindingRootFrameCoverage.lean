import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaSource
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingFrameChecking

/-!
# Every ordinary authored root firing has a native semantic frame

For computed root metadata, original scoped matching and ordered premise
evidence construct the frame for every ambient context and every firing.
No individual ground execution or assumed coverage field is used. Authored
binder labels remain in the declaration while source reading is alpha-aware.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingRootFrameCoverage

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage
open NativeBindingSchemaCaptures NativeBindingSchemaFocus NativeBindingMatchInstantiation

variable {plan : Plan} (schema : Rules.Schema plan)

noncomputable def rootFrame (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (root : schema.position = []) (rootBound : schema.focusBound = [])
    {ambient : List String} {sort : String} (rootCarrier : schema.focusCarrier = .base sort)
    (shape : treeSchema schema.declaration.rule.left = true) (point : Selected schema ambient sort) :
    Frame schema ambient sort where
  point := point
  focus := toPattern point.val.source
  typed := by
    rw [rootBound, List.nil_append, rootCarrier, freeEmpty]
    exact toPattern_typed point.val.source
  object := toPattern_object point.val.source
  canonical := toPattern_canonical point.val.source
  selected := by
    obtain ⟨rawSource, actual, erased⟩ := Option.map_eq_some_iff.mp
      (NativeBindingSchemaSource.reconstructed schema point shape)
    refine ⟨rawSource, ?_, erased⟩
    rw [root]
    exact .here actual
  source := NativeBindingSchemaSource.reconstructed schema point shape
  focusDepth := by rw [root, rootBound]; rfl

theorem rootFrame_point (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (root : schema.position = []) (rootBound : schema.focusBound = [])
    {ambient : List String} {sort : String} (rootCarrier : schema.focusCarrier = .base sort)
    (shape : treeSchema schema.declaration.rule.left = true) (point : Selected schema ambient sort) :
    (rootFrame schema freeEmpty root rootBound rootCarrier shape point).point = point := rfl

theorem checker_covers_root (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (root : schema.position = []) (rootBound : schema.focusBound = [])
    {ambient : List String} {sort : String} (rootCarrier : schema.focusCarrier = .base sort)
    (shape : treeSchema schema.declaration.rule.left = true) (point : Selected schema ambient sort) :
    ∃ frame, NativeBindingFrameChecking.frame? schema point = some frame ∧ frame.point = point := by
  obtain ⟨frame, checked, _⟩ := NativeBindingFrameChecking.frame?_complete schema
    (rootFrame schema freeEmpty root rootBound rootCarrier shape point)
  exact ⟨frame, checked, NativeBindingFrameChecking.frame?_point schema point checked⟩

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingRootFrameCoverage
