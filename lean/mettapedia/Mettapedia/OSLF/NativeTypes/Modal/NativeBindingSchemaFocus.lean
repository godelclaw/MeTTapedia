import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaCaptures
import Mettapedia.OSLF.NativeTypes.Modal.NativeFocusSubstitution
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingAlphaReadout

/-!
# Actual authored schema focus with complete operational evidence

The source and focus are linked by independent scoped instantiation of the
authored declaration. The original selected receipt supplies its matching,
premise history and specified target. Ambient substitution preserves that
link, the exact local binder prefix and every retained receipt origin.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaFocus

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise GeneralExecutionAdmission
open RuleBinding ScopedRuleMatching
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open NativeBindingEventAction (bound)

variable {plan : Plan} (schema : Rules.Schema plan)

structure Frame (ambient : List String) (sort : String) where
  point : NativeBindingSchemaCaptures.Selected schema ambient sort
  focus : Pattern
  typed : HasType plan.snapshot.language plan.snapshot.free
    (schema.focusBound ++ bound ambient) focus schema.focusCarrier
  object : isObjectPattern focus = true
  canonical : focus.hasCanonicalBinderMetadata = true
  selected : ∃ rawFocus, Instantiation.FocusInstance Substitution.instantiateBVar
    schema.declaration.rule schema.declaration.binding.spec ambient.length .left
    point.val.receipt.completed [] 0 schema.declaration.rule.left schema.position rawFocus ∧
      rawFocus.eraseBinderMetadata = focus
  source : (instantiateAt? schema.declaration.rule schema.declaration.binding.spec ambient.length
    .left [] 0 point.val.receipt.completed schema.declaration.rule.left).map Pattern.eraseBinderMetadata =
      some (toPattern point.val.source)
  focusDepth : NativeFocusSubstitution.depthAt? schema.declaration.rule.left schema.position 0 =
    some schema.focusBound.length

theorem fill_source {ambient : List String} {sort : String} (frame : Frame schema ambient sort) :
    ∃ rawFocus, rawFocus.eraseBinderMetadata = frame.focus ∧
      (Instantiation.fill? Substitution.instantiateBVar schema.declaration.rule
        schema.declaration.binding.spec ambient.length .left [] 0 frame.point.val.receipt.completed
        rawFocus schema.declaration.rule.left schema.position).map Pattern.eraseBinderMetadata =
          some (toPattern frame.point.val.source) := by
  obtain ⟨rawFocus, selected, erased⟩ := frame.selected
  exact ⟨rawFocus, erased,
    (congrArg (Option.map Pattern.eraseBinderMetadata) (Instantiation.fill_authored selected)).trans frame.source⟩

theorem rule_admitted {ambient : List String} {sort : String} (frame : Frame schema ambient sort) :
    admittedFor schema.declaration.rule schema.declaration.binding.spec = true := by
  have declared := GeneralPlanEnvironment.selected_rule plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  have specified := GeneralPlanEnvironment.selected_specification plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  rw [← frame.point.property] at declared specified
  cases frame.point.val.receipt.valid with
  | fire actualRule actualSpec admitted _ _ _ _ _ _ =>
      cases Option.some.inj (actualRule.symm.trans declared)
      cases Option.some.inj (actualSpec.symm.trans specified)
      exact admitted

theorem rule_scopes (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan)) :
    NativeOperationalProfile.ScopedRule schema.declaration.rule :=
  ready.scopes _ (List.mem_of_getElem? (GeneralPlanEnvironment.selected_rule plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)))

def action (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    {source target : List String} (substitution : Sub (signature plan.snapshot.language) source target)
    {sort : String} (frame : Frame schema source sort) : Frame schema target sort where
  point := NativeBindingSchemaCaptures.action schema freeEmpty ready substitution frame.point
  focus := ContextSubstitution.substitute
    (ContextSubstitution.lift schema.focusBound.length (NativeBindingRendering.assignment substitution)) frame.focus
  typed := by
    have before := frame.typed
    rw [freeEmpty] at before ⊢
    exact before.substituteBound
      ((NativeBindingRendering.typedAssignment substitution).liftContext schema.focusBound)
  object := GeneralPremise.contextSubstitute_objects frame.object
    (NativePremiseSubstitutionBase.objects_lift
      (fun index => (NativeBindingRendering.assignment_images substitution index).1) _)
  canonical := GeneralPremise.contextSubstitute_canonical frame.canonical
    (NativePremiseSubstitutionBase.canonical_lift
      (fun index => (NativeBindingRendering.assignment_images substitution index).2) _)
  selected := by
    have bounded : ContextSubstitution.WellScopedAssignment source.length target.length
        (NativeBindingRendering.assignment substitution) := by
      simpa only [NativeBindingRendering.typedAssignment,
        Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.length_map] using
        (NativeBindingRendering.typedAssignment substitution).wellScoped
    obtain ⟨rawFocus, rawSelected, erased⟩ := frame.selected
    have selected := NativeFocusSubstitution.focus_substitutes rawSelected frame.focusDepth
      (rule_admitted schema frame) (depthCoherent_left _) (rule_scopes schema ready).left
      (NativeBindingRendering.assignment substitution)
      bounded
    refine ⟨_, by simpa only [NativeBindingSchemaCaptures.action_completed] using selected, ?_⟩
    exact (NativeBindingAlphaReadout.erase_substitution _
      (NativePremiseSubstitutionBase.canonical_lift
        (fun index => (NativeBindingRendering.assignment_images substitution index).2) _) rawFocus).trans
      (congrArg (ContextSubstitution.substitute
        (ContextSubstitution.lift schema.focusBound.length (NativeBindingRendering.assignment substitution))) erased)
  source := by
    have bounded : ContextSubstitution.WellScopedAssignment source.length target.length
        (NativeBindingRendering.assignment substitution) := by
      simpa only [NativeBindingRendering.typedAssignment,
        Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.length_map] using
        (NativeBindingRendering.typedAssignment substitution).wellScoped
    obtain ⟨rawSource, rawSourced, erased⟩ := Option.map_eq_some_iff.mp frame.source
    have sourced := NativeRuleInstantiationSubstitution.instantiateAt_substitutes rawSourced
      (rule_admitted schema frame) (depthCoherent_left _) (rule_scopes schema ready).left
      (NativeBindingRendering.assignment substitution)
      bounded
    rw [ContextSubstitution.lift_zero] at sourced
    have actual : instantiateAt? schema.declaration.rule schema.declaration.binding.spec target.length
        .left [] 0 (NativeBindingSchemaCaptures.action schema freeEmpty ready substitution frame.point).val.receipt.completed
        schema.declaration.rule.left = some (ContextSubstitution.substitute
          (NativeBindingRendering.assignment substitution) rawSource) := by
      simpa only [NativeBindingSchemaCaptures.action_completed] using sourced
    rw [actual]
    apply congrArg some
    exact (NativeBindingAlphaReadout.erase_substitution _
      (fun index => (NativeBindingRendering.assignment_images substitution index).2) rawSource).trans
      ((congrArg (ContextSubstitution.substitute (NativeBindingRendering.assignment substitution)) erased).trans
        (NativeBindingRendering.print_substitution substitution frame.point.val.source).symm)
  focusDepth := frame.focusDepth

theorem action_focus (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    {source target : List String} (substitution : Sub (signature plan.snapshot.language) source target)
    {sort : String} (frame : Frame schema source sort) :
    (action schema freeEmpty ready substitution frame).focus = ContextSubstitution.substitute
      (ContextSubstitution.lift schema.focusBound.length (NativeBindingRendering.assignment substitution)) frame.focus := rfl

theorem frame_ext {ambient : List String} {sort : String} {left right : Frame schema ambient sort}
    (points : left.point = right.point) (focus : left.focus = right.focus) : left = right := by
  cases left
  cases right
  dsimp only at points focus
  cases points
  cases focus
  rfl

theorem action_identity (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    {ambient : List String} {sort : String} (frame : Frame schema ambient sort) :
    action schema freeEmpty ready (fun _ position => Term.var position) frame = frame := by
  apply frame_ext
  · exact NativeBindingSchemaCaptures.action_identity schema freeEmpty ready frame.point
  · simp only [action_focus, NativeBindingRendering.assignment_identity,
      ContextSubstitution.lift_identity, ContextSubstitution.substitute_id]

theorem action_composition (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    {source middle target : List String}
    (first : Sub (signature plan.snapshot.language) source middle)
    (second : Sub (signature plan.snapshot.language) middle target) {sort : String}
    (frame : Frame schema source sort) :
    action schema freeEmpty ready second (action schema freeEmpty ready first frame) =
      action schema freeEmpty ready (fun sort position => Binding.bind second (first sort position)) frame := by
  apply frame_ext
  · exact NativeBindingSchemaCaptures.action_composition schema freeEmpty ready first second frame.point
  · simp only [action_focus, ContextSubstitution.substitute_comp, ContextSubstitution.lift_comp,
      NativeBindingRendering.assignment_composition]

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaFocus
