import Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls

open Mettapedia.OSLF.Framework

/-!
# Explicit substitutions in the generated annotated template family

The authored source contains an explicit substitution with an independently
chosen intermediate arrow carrier. Its selected bound-variable occurrence
is checked under both the substitution binder and the lambda binder. The
same generator retains every domain and ambient context without enumerating
types. Annotation acceptance remains distinct from operational admission.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.Annotated.SubstitutionControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Modal.Annotations

def source : Pattern := .subst (.lambda none (.bvar 1)) (.lambda none (.bvar 0))
def target : Pattern := .lambda none (.lambda none (.bvar 0))
def rule : RewriteRule where
  name := "explicit-substitution-source"
  typeContext := []
  premises := []
  left := source
  right := target

def language : LanguageDef :=
  {Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls.language with name := "annotated-explicit-substitution", rewrites := [rule]}
def snapshot : Snapshot := ⟨language, [], ⟨[], []⟩⟩
def permissions : Permissions := {sites := .all}
def fragment : LanguageFragment := ⟨none, permissions⟩
def chosen : Snapshot := selectedSnapshot snapshot fragment

theorem chosen_snapshot : chosen = snapshot := by
  unfold chosen selectedSnapshot fragment
  rw [unrestricted_signature]

def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun _ => .star)
def generated : Generated := generate snapshot fragment Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment vertex

def binding : Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference.BindingPlan :=
  ⟨Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference.inferredSpec rule, .inferredRootInputs⟩
def declaration : RulePlan := ⟨0, rule, binding⟩
def runtimePlan : Plan := ⟨snapshot, permissions, [declaration], [], []⟩

theorem actual_plan : generated.plan = runtimePlan := by
  change compile chosen permissions = runtimePlan
  rw [chosen_snapshot]
  cbv

theorem actual_raw_sites : generated.rawSites = Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language := by
  change selectedSites chosen.language permissions = _
  rw [chosen_snapshot]
  change selectedSites language permissions = _
  simp [selectedSites, permissions, selected]

def boundSite : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site :=
  {context := .substBody (.lambda none .hole) (.lambda none (.bvar 0)),
    focus := .bvar 1, declaration := 0, rule := rule}

theorem actual_bound_template : generated.rawSites[2]? = some boundSite := by
  rw [actual_raw_sites]
  cbv

def intermediate (leaf : TypeExpr) : TypeExpr := .arrow leaf leaf

def annotation (domain leaf : TypeExpr) (bound : List TypeExpr) : SourceAnnotation :=
  {bound := bound, programCarrier := .arrow domain (intermediate leaf),
    focusBound := domain :: intermediate leaf :: bound,
    focusCarrier := intermediate leaf,
    descent := .substBody (intermediate leaf) (.lambda .bvar) (.lambda (.here .bvar))}

theorem annotation_check (domain leaf : TypeExpr) (bound : List TypeExpr) :
    generated.checkSourceAnnotation boundSite (annotation domain leaf bound) = true := by
  change checkDescent chosen.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree rule) (.bvar 1)
    boundSite.context bound (.arrow domain (intermediate leaf))
    (domain :: intermediate leaf :: bound) (intermediate leaf) _ = true
  rw [chosen_snapshot]
  simp [checkDescent, check, annotation, boundSite, intermediate]

theorem every_substitution_source_generated (domain leaf : TypeExpr) (bound : List TypeExpr) :
    (generated.instantiateAnnotatedSource? 2 (annotation domain leaf bound)).isOk = true := by
  unfold Generated.instantiateAnnotatedSource?
  split
  · rename_i missing
    rw [actual_bound_template] at missing
    contradiction
  · rename_i actual actualAt
    have same := Option.some.inj (actualAt.symm.trans actual_bound_template)
    subst actual
    have templateChecked : generated.checkRawTemplate boundSite = true := by
      change (decide (chosen.language.rewrites[0]? = some rule) && selected permissions.ruleIndices 0 &&
        decide (boundSite.context.fill boundSite.focus = rule.left)) = true
      rw [chosen_snapshot]
      change (decide (language.rewrites[0]? = some rule) && selected permissions.ruleIndices 0 &&
        decide (boundSite.context.fill boundSite.focus = rule.left)) = true
      simp [language, rule, permissions, selected, boundSite, source,
        Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill]
    simp only [templateChecked, annotation_check domain leaf bound, ↓reduceDIte, Except.isOk, Except.toBool]

theorem every_substitution_schema_generated (domain leaf : TypeExpr) (bound : List TypeExpr) :
    (generated.instantiateAnnotatedSchema? 2 (annotation domain leaf bound)).isOk = true := by
  have sourceSuccess := every_substitution_source_generated domain leaf bound
  unfold Generated.instantiateAnnotatedSchema?
  cases sourceAt : generated.instantiateAnnotatedSource? 2 (annotation domain leaf bound) with
  | error issue => simp [sourceAt, Except.isOk, Except.toBool] at sourceSuccess
  | ok checkedSource =>
      have retained := instantiated_source_input_retained sourceAt
      have sameSource : checkedSource.site = boundSite := by
        have actualAt := checkedSource.present
        rw [retained.1, actual_bound_template] at actualAt
        exact Option.some.inj actualAt.symm
      have selectedRule : (declaration, 0) ∈ generated.plan.rules.zipIdx := by
        rw [actual_plan]
        simp [runtimePlan]
      obtain ⟨checked, engineAt, _⟩ := annotated_source_engine_complete checkedSource declaration 0 selectedRule
        (by rw [sameSource]; rfl) (by rw [sameSource]; rfl)
      simp [engineAt, Except.isOk, Except.toBool]

/-- The actual generated result retains the complete two-binder context,
the intermediate substitution carrier and its independently chosen domain. -/
theorem every_substitution_schema_readout (domain leaf : TypeExpr) (bound : List TypeExpr)
    (checked : AnnotatedSchema generated)
    (produced : generated.instantiateAnnotatedSchema? 2 (annotation domain leaf bound) = .ok checked) :
    checked.schema.programCarrier = .arrow domain (intermediate leaf) ∧
    checked.schema.focusCarrier = intermediate leaf ∧
    checked.schema.bound = bound ∧
    checked.schema.focusBound = domain :: intermediate leaf :: bound := by
  have retained := instantiated_schema_input_retained produced
  change checked.source.annotation.programCarrier = _ ∧ checked.source.annotation.focusCarrier = _ ∧
    checked.source.annotation.bound = _ ∧ checked.source.annotation.focusBound = _
  rw [retained.2]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem malformed_replacement_rejected (domain leaf : TypeExpr) (bound : List TypeExpr) :
    generated.checkSourceAnnotation boundSite
      {annotation domain leaf bound with
        descent := .substBody (intermediate leaf) .fvar (.lambda (.here .bvar))} = false := by
  simp [Generated.checkSourceAnnotation, annotation, boundSite, checkDescent, check]

theorem ill_sorted_focus_rejected (domain leaf : TypeExpr) (bound : List TypeExpr) :
    generated.checkSourceAnnotation boundSite
      {annotation domain leaf bound with focusCarrier := .base "Term"} = false := by
  simp [Generated.checkSourceAnnotation, annotation, boundSite, checkDescent, check, intermediate]

theorem missing_substitution_binder_rejected (domain leaf : TypeExpr) (bound : List TypeExpr) :
    generated.checkSourceAnnotation boundSite
      {annotation domain leaf bound with focusBound := domain :: bound} = false := by
  simp [Generated.checkSourceAnnotation, annotation, boundSite, checkDescent, check]

end Mettapedia.OSLF.NativeTypes.Generation.Annotated.SubstitutionControls
