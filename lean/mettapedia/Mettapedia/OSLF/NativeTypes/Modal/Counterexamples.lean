import Mettapedia.OSLF.NativeTypes.Modal.Equations
import Mettapedia.OSLF.NativeTypes.Modal.Comparison
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceUniversalCompletion
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceModalReadouts

open Mettapedia.OSLF.Framework

/-!
# The existential and specified-contractum readings are different

The language has a nonempty equation Alpha = Beta, a base rewrite Beta to
Done, and a second rewrite Other to Alpha. The root-context modality generated
by the first declaration has no rely variables. Under the existential
comprehension in the hypercube paper, Other inhabits the continuation which
excludes Done's equation class. It neither takes a one-step reduction to Done
nor supplies a certificate of that continuation at Done.

Thus the existential comprehension does not validate the source rule's specified
RHS step and elimination rules. The specified-contractum former defined in
`Mettapedia.OSLF.NativeTypes.Modal.Rules` rejects this inhabitant and validates those rules.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.Counterexamples

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules

def carrier : TypeExpr := .base "Term"
def alpha : Pattern := .apply "Alpha" []
def beta : Pattern := .apply "Beta" []
def other : Pattern := .apply "Other" []
def done : Pattern := .apply "Done" []

def equation : Equation where
  name := "alpha-beta"
  typeContext := []
  premises := []
  left := alpha
  right := beta

def firstRule : RewriteRule where
  name := "beta-done"
  typeContext := []
  premises := []
  left := beta
  right := done

def secondRule : RewriteRule where
  name := "other-alpha"
  typeContext := []
  premises := []
  left := other
  right := alpha

def language : LanguageDef where
  name := "specified-rhs-separator"
  types := ["Term"]
  terms := [
    {label := "Alpha", category := "Term", params := [], syntaxPattern := []},
    {label := "Beta", category := "Term", params := [], syntaxPattern := []},
    {label := "Other", category := "Term", params := [], syntaxPattern := []},
    {label := "Done", category := "Term", params := [], syntaxPattern := []}]
  equations := [equation]
  rewrites := [firstRule, secondRule]

def snapshot : Snapshot := {language := language, freeTypes := [], provider := {signatures := [], rows := []}}
def permissions : Permissions := {sites := .rootOnly}

def binding : GeneralRuleBindingInference.BindingPlan :=
  ⟨{dependencies := []}, .inferredRootInputs⟩

def firstDeclaration : RulePlan := ⟨0, firstRule, binding⟩
def secondDeclaration : RulePlan := ⟨1, secondRule, binding⟩

def oriented (direction : ScopedEquationExecution.Orientation) : EquationPlan :=
  ⟨0, equation, direction, binding, true⟩

def runtimePlan : Plan :=
  ⟨snapshot, permissions, [firstDeclaration, secondDeclaration],
    [oriented .forward, oriented .reverse], []⟩

theorem actual_plan : compile snapshot permissions = runtimePlan := by cbv

theorem totality_checked :
    (GeneralExecutionTotalAdmission.compile snapshot permissions).complete = true := by
  apply GeneralExecutionTotalAdmission.compile_complete_of_generic
  · rw [actual_plan]
    rfl
  · rw [actual_plan]
    cbv

def request (source : Pattern) : GeneralOccurrenceFrontier.Request :=
  ⟨runtimePlan, [], carrier, source⟩

def executed (source : Pattern) : GeneralOccurrenceFrontier.State (request source) :=
  GeneralOccurrenceFrontier.run (request source) 80 (GeneralOccurrenceFrontier.start (request source))

/-- Exhaustive execution exists for every sorted object in this authored
language; completion is earned by the existing total-admission theorem. -/
theorem every_typed_object_has_complete_execution {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (typed : HasType language snapshot.free bound source expected)
    (object : isObjectPattern source = true) :
    ∃ result, GeneralOccurrenceFrontier.executeCertified? snapshot permissions bound expected source =
      some result ∧ GeneralOccurrenceFrontier.complete _ result = true ∧
      GeneralOccurrenceFrontier.checkCertificate _ result = true := by
  obtain ⟨result, executed⟩ := GeneralOccurrenceFrontier.executeCertified?_exists totality_checked typed object
  exact ⟨result, executed, GeneralOccurrenceFrontier.executeCertified?_complete executed⟩

private theorem literal_typed (source : Pattern)
    (present : source = alpha ∨ source = beta ∨ source = other ∨ source = done) :
    OpenPatternWellSorted language snapshot.free [] carrier source := by
  apply checkOpenPatternWellSorted_sound
  rcases present with rfl | rfl | rfl | rfl <;> cbv

theorem root_only_site {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed
      language free OperationalPermissions.rootOnly bound expected source site) :
    site = SiteData.here bound expected source := by
  cases licensed with
  | here => rfl
  | application _ _ _ _ _ _ _ permitted _ =>
      simp [OperationalPermissions.rootOnly] at permitted
  | lambda permitted _ => cases permitted
  | multiLambda permitted _ => cases permitted
  | directCollection permitted _ _ _ _ => cases permitted
  | authoredCollection _ _ permitted _ _ _ _ => cases permitted

theorem nullary_matching {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial captured : ScopedRuleMatching.Assignment} {label : String}
    {target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    (matched : GeneralScopedMatchMachine.TracedMatches rule spec ambient site path depth initial
      (.apply label []) target trace captured) : target = .apply label [] := by
  cases matched with
  | constructor arguments => cases arguments; rfl

theorem nullary_reduct (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (assignment : ScopedRuleMatching.Assignment) (label : String)
    (right : rule.right = .apply label []) :
    ScopedRuleMatching.reductWith? operation rule spec ambient assignment = some (.apply label []) := by
  simp only [ScopedRuleMatching.reductWith?, right, ScopedRuleMatching.instantiateWith?,
    ScopedRuleMatching.instantiateArgsWith?, Option.bind_eq_bind]
  rfl

private theorem oriented_forward : (oriented .forward).rule.left = alpha ∧
    (oriented .forward).rule.right = beta := by cbv
private theorem oriented_reverse : (oriented .reverse).rule.left = beta ∧
    (oriented .reverse).rule.right = alpha := by cbv

def Eqv : Pattern → Pattern → Prop := GeneralOccurrenceSemantics.Equation runtimePlan [] carrier

/-- Every contextual equation event in this root-only profile is one of the
actual two authored orientations. This is independent of frontier endpoints. -/
theorem equation_events_for (plan : Plan)
    (sites : plan.permissions.sites = .rootOnly)
    (equations : plan.equations = [oriented .forward, oriented .reverse])
    {source target : Pattern} (equated : GeneralOccurrenceSemantics.Equation plan [] carrier source target) :
    (source = alpha ∧ target = beta) ∨ (source = beta ∧ target = alpha) := by
  obtain ⟨receipt, complete, endpoint⟩ := equated
  have licensed := complete.job.2
  rw [sites] at licensed
  have root := root_only_site licensed
  have declared := List.fst_mem_of_mem_zipIdx complete.job.1
  have selected : receipt.job.equation = oriented .forward ∨ receipt.job.equation = oriented .reverse := by
    simpa only [equations, List.mem_cons, List.not_mem_nil, or_false] using declared
  have matched := complete.matched
  rw [root] at matched
  have reduct := complete.reduct
  have targetEq := complete.endpoint
  rw [root] at targetEq
  rcases selected with forward | backward
  · rw [forward, oriented_forward.1] at matched
    have sourceEq : source = alpha := by
      have erased : source.eraseBinderMetadata = alpha := nullary_matching matched
      have canonical := complete.sourceTyped.2.1
      rwa [Pattern.eraseBinderMetadata_eq_self_of_canonical canonical] at erased
    have actual := nullary_reduct Substitution.instantiateBVar
      receipt.job.equation.rule receipt.job.equation.binding.spec receipt.job.site.focusBound.length
      receipt.completed "Beta" (forward ▸ oriented_forward.2)
    have rawEq : receipt.rawReduct = beta := Option.some.inj (reduct.symm.trans actual)
    have final : target = beta := by
      rw [← endpoint, targetEq, rawEq]
      simp only [SiteData.here, DerivedContexts.OneHoleContext.fill, beta,
        Pattern.eraseBinderMetadata, List.map_nil]
    exact Or.inl ⟨sourceEq, final⟩
  · rw [backward, oriented_reverse.1] at matched
    have sourceEq : source = beta := by
      have erased : source.eraseBinderMetadata = beta := nullary_matching matched
      have canonical := complete.sourceTyped.2.1
      rwa [Pattern.eraseBinderMetadata_eq_self_of_canonical canonical] at erased
    have actual := nullary_reduct Substitution.instantiateBVar
      receipt.job.equation.rule receipt.job.equation.binding.spec receipt.job.site.focusBound.length
      receipt.completed "Alpha" (backward ▸ oriented_reverse.2)
    have rawEq : receipt.rawReduct = alpha := Option.some.inj (reduct.symm.trans actual)
    have final : target = alpha := by
      rw [← endpoint, targetEq, rawEq]
      simp only [SiteData.here, DerivedContexts.OneHoleContext.fill, alpha,
        Pattern.eraseBinderMetadata, List.map_nil]
    exact Or.inr ⟨sourceEq, final⟩

theorem equation_events {source target : Pattern} (equated : Eqv source target) :
    (source = alpha ∧ target = beta) ∨ (source = beta ∧ target = alpha) :=
  equation_events_for runtimePlan rfl rfl equated

private theorem equation_keeps (distinguished : Pattern)
    (excludesAlpha : distinguished ≠ alpha) (excludesBeta : distinguished ≠ beta)
    {source target : Pattern} (equivalent : Relation.EqvGen Eqv source target) :
    source = distinguished ↔ target = distinguished := by
  induction equivalent with
  | rel source target equated =>
      rcases equation_events equated with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [Ne.symm excludesAlpha, Ne.symm excludesBeta]
      · simp only [Ne.symm excludesAlpha, Ne.symm excludesBeta]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem alpha_not_done_class : ¬ Relation.EqvGen Eqv alpha done := by
  intro equivalent
  have preserved := equation_keeps done (by decide) (by decide) equivalent
  exact (by decide : alpha ≠ done) (preserved.mpr rfl)

/-- A checked actual local execution supplies the independent primitive. -/
def otherPrimitive : GeneralRuleJobs.Receipt where
  job := ⟨1, secondDeclaration, SiteData.here [] carrier other⟩
  matcherTrace := []
  captured := []
  completed := []
  premiseHistory := []
  localTarget := alpha
  target := alpha

private theorem otherPrimitive_valid : otherPrimitive.Valid runtimePlan [] carrier other := by
  apply GeneralRuleJobs.finish_sound (job := otherPrimitive.job)
    (trace := []) (captured := []) (completed := []) (history := [])
  · refine ⟨?_, .here rfl rfl ?_⟩
    · simp only [otherPrimitive, runtimePlan, List.zipIdx_cons, List.zipIdx_nil,
        List.mem_cons]
      exact Or.inr (Or.inl trivial)
    · apply checkHasType_sound
      cbv
  · exact .constructor .nil
  · exact .nil
  · cbv

theorem other_steps_alpha :
    (GeneralOccurrenceSemantics.gslt runtimePlan [] carrier).Step other alpha :=
  ⟨other, otherPrimitive, .refl _, otherPrimitive_valid, .refl _⟩

private theorem primitive_other_target {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid runtimePlan [] carrier other) : receipt.target = alpha := by
  have root := root_only_site valid.1.2
  have actualRule := receipt.job.selected_rule valid.1
  have firing := valid.2.1
  rw [root] at firing
  have declared := valid.1.1
  have selected : (receipt.job.declaration = firstDeclaration ∧ receipt.job.ordinal = 0) ∨
      (receipt.job.declaration = secondDeclaration ∧ receipt.job.ordinal = 1) := by
    simpa only [runtimePlan, List.zipIdx_cons, List.zipIdx_nil, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq, Nat.zero_add] using declared
  cases firing with
  | @fire _ _ _ _ _ rule spec _ _ _ _ selectedRule _ _ _ matched _ _ reduct _ =>
      have same : rule = receipt.job.declaration.rule := Option.some.inj (selectedRule.symm.trans actualRule)
      subst rule
      rcases selected with ⟨first, _⟩ | ⟨second, _⟩
      · rw [first] at matched
        have impossible : other = beta := nullary_matching matched
        exact False.elim ((by decide : other ≠ beta) impossible)
      · have right : receipt.job.declaration.rule.right = alpha := by rw [second]; rfl
        have actual := nullary_reduct (ScopedReflectiveExecution.binderOperation
          (GeneralPlanEnvironment.environment runtimePlan).reflection receipt.job.declaration.rule)
          receipt.job.declaration.rule spec 0 receipt.completed "Alpha" right
        have localSame : receipt.localTarget = alpha := Option.some.inj (reduct.symm.trans actual)
        rw [valid.2.2.2.1, root, localSame]
        rfl

theorem other_not_steps_done :
    ¬ (GeneralOccurrenceSemantics.gslt runtimePlan [] carrier).Step other done := by
  rintro ⟨representative, firing, before, fired, after⟩
  have representativeEq : representative = other :=
    (equation_keeps other (by decide) (by decide) before).mp rfl
  subst representative
  rw [primitive_other_target fired] at after
  exact alpha_not_done_class after

def schema : Schema runtimePlan where
  ordinal := 0
  declaration := firstDeclaration
  declared := List.mem_cons_self
  position := (Mettapedia.OSLF.Framework.RedexPosition.positions firstRule.left).head!
  bound := []
  programCarrier := carrier
  focusBound := []
  focusCarrier := carrier

theorem schema_position : schema.position = [] := by cbv

theorem schema_filled (assignment : ScopedRuleMatching.Assignment) (term : Pattern) :
    schema.fill? assignment term = some term := by
  unfold Schema.fill?
  rw [schema_position]
  simp only [Mettapedia.OSLF.NativeTypes.Modal.Instantiation.fill?]

theorem schema_rely_empty : schema.relyNames = [] := by cbv

theorem schema_matched_empty : schema.matchedNames = [] := by cbv

/-- A nonconstant continuation, invariant under the actual authored equations. -/
def continuation : Continuation :=
  fun _ target => PLift (¬ Relation.EqvGen Eqv target done)

theorem continuation_equation_invariant {first second : Pattern}
    (equivalent : Relation.EqvGen Eqv first second) :
    Nonempty (continuation [] first) ↔ Nonempty (continuation [] second) := by
  constructor
  · rintro ⟨⟨excludes⟩⟩
    exact ⟨⟨fun reached => excludes (.trans first second done equivalent reached)⟩⟩
  · rintro ⟨⟨excludes⟩⟩
    exact ⟨⟨fun reached => excludes (.trans second first done (.symm first second equivalent) reached)⟩⟩

/-- The paper's rely-possibly comprehension has an existential contractum. -/
def PaperModal (term : Pattern) : Prop :=
  HasType language snapshot.free [] term carrier ∧
    ∀ assignment : ScopedRuleMatching.Assignment,
      TypedRequest schema (fun _ _ => False) [] assignment →
      ∃ source target, schema.fill? assignment term = some source ∧
        (GeneralOccurrenceSemantics.gslt runtimePlan [] carrier).Step source target ∧
        Nonempty (continuation assignment target)

theorem other_inhabits_paper_modal : PaperModal other := by
  refine ⟨(literal_typed other (Or.inr (Or.inr (Or.inl rfl)))).1, ?_⟩
  intro assignment _
  exact ⟨other, alpha, schema_filled assignment other, other_steps_alpha, ⟨⟨alpha_not_done_class⟩⟩⟩

theorem specified_rhs : schema.rhs? [] = some done := by cbv

/-- The specified target implication fails for the existential modal meaning,
even with an equation-invariant continuation and a complete engine. -/
theorem literal_m_step_refuted :
    PaperModal other ∧ schema.fill? [] other = some other ∧ schema.rhs? [] = some done ∧
      ¬ (GeneralOccurrenceSemantics.gslt runtimePlan [] carrier).Step other done :=
  ⟨other_inhabits_paper_modal, schema_filled [] other, specified_rhs, other_not_steps_done⟩

theorem literal_m_elim_refuted : PaperModal other ∧ ¬ Nonempty (continuation [] done) := by
  refine ⟨other_inhabits_paper_modal, ?_⟩
  rintro ⟨⟨excludes⟩⟩
  exact excludes (.refl done)

/-- The exact specified-contractum correction excludes the separating term. -/
theorem corrected_modality_rejects_other :
    ¬ Inhabits schema (fun _ _ => False) continuation other := by
  rintro ⟨implementation⟩
  have submitted : TypedRequest schema (fun _ _ => False) implementation.anchor [] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro name member
      rw [schema_rely_empty] at member
      exact False.elim (List.not_mem_nil member)
    · exact ⟨fun _ _ impossible => False.elim (List.not_mem_nil impossible),
        fun _ _ impossible => False.elim (List.not_mem_nil impossible)⟩
    · intro name member
      rw [schema_matched_empty] at member
      exact False.elim (List.not_mem_nil member)
    · intro name member
      simp [schema, firstDeclaration, RulePlan.rule, firstRule,
        GeneralRuleBindingInference.BindingPlan.elaborate,
        Mettapedia.OSLF.Framework.RedexPosition.fvarNames,
        Mettapedia.OSLF.Framework.RedexPosition.fvarNamesList, beta, done] at member
  obtain ⟨source, target, filled, rhs, step⟩ := m_step implementation [] submitted
  have sourceSame : source = other := Option.some.inj (filled.symm.trans (schema_filled [] other))
  have targetSame : target = done := Option.some.inj (rhs.symm.trans specified_rhs)
  subst source
  subst target
  exact other_not_steps_done step

/-- The separator inhabits the very existential meaning used by the general
comparison theorem; no independently renamed modal predicate is required. -/
theorem other_inhabits_existential :
    Mettapedia.OSLF.NativeTypes.Modal.Comparison.ExistentialInhabits schema (fun _ _ => False) continuation other := by
  refine ⟨other_inhabits_paper_modal.1, [], ?_, ?_, other_inhabits_paper_modal.2⟩
  · exact ⟨fun _ _ impossible => False.elim (List.not_mem_nil impossible),
      fun _ _ impossible => False.elim (List.not_mem_nil impossible)⟩
  · intro name member
    rw [schema_matched_empty] at member
    exact False.elim (List.not_mem_nil member)

theorem existential_comparison_is_strict :
    Mettapedia.OSLF.NativeTypes.Modal.Comparison.ExistentialInhabits schema (fun _ _ => False) continuation other ∧
      ¬ Inhabits schema (fun _ _ => False) continuation other :=
  ⟨other_inhabits_existential, corrected_modality_rejects_other⟩

end Mettapedia.OSLF.NativeTypes.Modal.Counterexamples
