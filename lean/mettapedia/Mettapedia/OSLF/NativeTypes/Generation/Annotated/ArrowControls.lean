import Mettapedia.OSLF.NativeTypes.Generation.Annotated.Schemas
import Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls

open Mettapedia.OSLF.Framework

/-!
# Generated annotated modalities at every arrow domain

The concrete finite catalogue is empty for this top-level abstraction.
Its actual raw generator template nevertheless has a checking annotation for
every source-arrow domain and ambient context. The original compiled rule
is recovered by lookup; no typed site list or carrier pool is supplied.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Modal.Annotations
open Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls

def fragment : LanguageFragment := ⟨none, permissions⟩
def chosen : Snapshot := selectedSnapshot snapshot fragment

theorem chosen_snapshot : chosen = snapshot := by
  unfold chosen selectedSnapshot fragment
  rw [unrestricted_signature]

def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun _ => .star)

def generated : Generated := generate snapshot fragment Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment vertex

theorem generated_plan : generated.plan = runtimePlan := by
  change compile chosen permissions = runtimePlan
  rw [chosen_snapshot]
  exact actual_plan

theorem actual_raw_sites : generated.rawSites = Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language := by
  change selectedSites chosen.language permissions = _
  rw [chosen_snapshot]
  change selectedSites language permissions = _
  simp [selectedSites, permissions, selected]

theorem root_template : generated.rawSites[0]? =
    some ({context := .hole, focus := source, declaration := 0, rule := rule} : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site) := by
  rw [actual_raw_sites]
  cbv

def annotation (domain : TypeExpr) (bound : List TypeExpr) : SourceAnnotation :=
  {bound := bound, programCarrier := .arrow domain carrier,
    focusBound := bound, focusCarrier := .arrow domain carrier,
    descent := .here (.lambda (.application 1 (.cons (.application 0 .nil) .nil)))}

theorem annotation_check (domain : TypeExpr) (bound : List TypeExpr) :
    generated.checkSourceAnnotation
      {context := .hole, focus := source, declaration := 0, rule := rule}
      (annotation domain bound) = true := by
  change checkDescent chosen.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree rule) source .hole bound
    (.arrow domain carrier) bound (.arrow domain carrier) _ = true
  rw [chosen_snapshot]
  change checkDescent language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree rule) source .hole bound
    (.arrow domain carrier) bound (.arrow domain carrier) _ = true
  simp [checkDescent, check, checkArguments, annotation, language, source, wrap, done,
    doneGrammar, wrapGrammar, carrier, usesBareCollection?, parameterType?, MatchesParameterRepresentation]

theorem every_arrow_source_generated (domain : TypeExpr) (bound : List TypeExpr) :
    (generated.instantiateAnnotatedSource? 0 (annotation domain bound)).isOk = true := by
  unfold Generated.instantiateAnnotatedSource?
  split
  · rename_i missing
    rw [root_template] at missing
    contradiction
  · rename_i actual actualAt
    have same := Option.some.inj (actualAt.symm.trans root_template)
    subst actual
    have templateChecked : generated.checkRawTemplate
        {context := .hole, focus := source, declaration := 0, rule := rule} = true := by
      change (decide (chosen.language.rewrites[0]? = some rule) && selected permissions.ruleIndices 0 &&
        decide ((.hole : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext).fill source = rule.left)) = true
      rw [chosen_snapshot]
      change (decide (language.rewrites[0]? = some rule) && selected permissions.ruleIndices 0 &&
        decide ((.hole : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext).fill source = rule.left)) = true
      simp [language, permissions, rule, selected,
        Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill]
    simp only [templateChecked, annotation_check domain bound, ↓reduceDIte, Except.isOk, Except.toBool]

theorem every_arrow_schema_generated (domain : TypeExpr) (bound : List TypeExpr) :
    (generated.instantiateAnnotatedSchema? 0 (annotation domain bound)).isOk = true := by
  have sourceSuccess := every_arrow_source_generated domain bound
  unfold Generated.instantiateAnnotatedSchema?
  cases sourceAt : generated.instantiateAnnotatedSource? 0 (annotation domain bound) with
  | error issue => simp [sourceAt, Except.isOk, Except.toBool] at sourceSuccess
  | ok checkedSource =>
      have retained := instantiated_source_input_retained sourceAt
      have sameSource : checkedSource.site =
          ({context := .hole, focus := source, declaration := 0, rule := rule} : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site) := by
        have actualAt := checkedSource.present
        rw [retained.1, root_template] at actualAt
        exact Option.some.inj actualAt.symm
      have selectedRule : (declaration, 0) ∈ generated.plan.rules.zipIdx := by
        rw [generated_plan]
        simp [runtimePlan]
      obtain ⟨checked, engineAt, _⟩ := annotated_source_engine_complete checkedSource declaration 0 selectedRule
        (by rw [sameSource]; rfl) (by rw [sameSource]; rfl)
      simp [engineAt, Except.isOk, Except.toBool]

/-- The public result contains a non-base carrier for every chosen domain. -/
theorem every_arrow_schema_readout (domain : TypeExpr) (bound : List TypeExpr)
    (checked : AnnotatedSchema generated)
    (produced : generated.instantiateAnnotatedSchema? 0 (annotation domain bound) = .ok checked) :
    checked.schema.programCarrier = .arrow domain carrier ∧
    checked.schema.focusCarrier = .arrow domain carrier ∧
    checked.schema.bound = bound ∧ checked.schema.focusBound = bound := by
  have retained := instantiated_schema_input_retained produced
  change checked.source.annotation.programCarrier = _ ∧ checked.source.annotation.focusCarrier = _ ∧
    checked.source.annotation.bound = _ ∧ checked.source.annotation.focusBound = _
  rw [retained.2]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The source declaration omits binding metadata; the accepted operational
schema retains the inferred binding plan rather than replacing its origin. -/
theorem inferred_binding_preserved (domain : TypeExpr) (bound : List TypeExpr)
    (checked : AnnotatedSchema generated)
    (produced : generated.instantiateAnnotatedSchema? 0 (annotation domain bound) = .ok checked) :
    checked.schema.declaration.authored.bindings = none ∧
    checked.schema.declaration.rule.bindings = some checked.schema.declaration.binding.spec := by
  have retained := instantiated_schema_input_retained produced
  have actualAt := checked.source.present
  rw [retained.1, root_template] at actualAt
  have same := Option.some.inj actualAt.symm
  refine ⟨?_, rfl⟩
  rw [checked.original_authored, same]
  rfl

theorem malformed_annotation_rejected (domain : TypeExpr) (bound : List TypeExpr) :
    generated.checkSourceAnnotation
      {context := .hole, focus := source, declaration := 0, rule := rule}
      {annotation domain bound with descent := .here .fvar} = false := by
  simp [Generated.checkSourceAnnotation, annotation, checkDescent, check, source]

end Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls
