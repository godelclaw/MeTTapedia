import Mettapedia.GSLT.LanguageDef.MeTTaILMatchAutomataExecution
import Mettapedia.OSLF.MeTTaIL.ContextualStepFuel

/-!
# First-order closure of authored contextual execution

This module supplies syntax admission and closure laws for the canonical
contextual executor. It adds no evaluator or reduction relation. Relation
queries use the existing variable-only premise plans. Recursive congruence
and root scoped-step premises use the existing `premiseStepUsing` semantics:
instantiate the source, execute an authorized root step, match the target
relatively, and merge that match with the original bindings.

The admitted profile contains first-order patterns, absent rule-binding
annotations, syntactic freshness, and scoped-step premises with an empty local
telescope. Quantified premises and nonempty scoped telescopes remain outside
this profile. Equations are not directed reductions; an equation-free premise
is needed only when relating the resulting lists to the canonical GSLT step.

Recursive syntax closure is earned by induction on the actual contextual
depth. A matched child alone gives no execution permission. Ordered results
and duplicate premise witnesses remain the canonical executor's lists.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderContextualExecution

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open MeTTaILFirstOrderRuleCompilation

/-- Syntax profile for an authored recursive premise. The result type of an
empty-telescope scoped step is retained, rather than treated as a binder. -/
def premiseAdmitted : Premise → Bool
  | .freshness condition => isMatchCorrectAux condition.term
  | .relationQuery _ arguments => (compileArgumentNames? arguments).isSome
  | .congruence source target => isMatchCorrectAux source && isMatchCorrectAux target
  | .scopedStep step => step.binders.isEmpty &&
      (isMatchCorrectAux step.source && isMatchCorrectAux step.target)
  | .forAll _ _ _ => false

/-- Every executable row field is admitted; contextual authority comes from
the actual ordered premise list. Binding annotations require another profile. -/
def ruleAdmitted (rule : RewriteRule) : Bool :=
  rule.bindings.isNone && (isMatchCorrectAux rule.left &&
    (isMatchCorrectAux rule.right && rule.premises.all premiseAdmitted))

/-- Complete source admission retains each authored rewrite occurrence. -/
def languageAdmitted (language : LanguageDef) : Bool :=
  language.rewrites.all ruleAdmitted

theorem language_admitted_rule (language : LanguageDef)
    (admitted : languageAdmitted language = true) (rule : RewriteRule)
    (member : rule ∈ language.rewrites) : ruleAdmitted rule = true :=
  List.all_eq_true.mp admitted rule member

/-- Admission exposes exactly the retained row fields and metadata boundary. -/
theorem rule_admitted_iff (rule : RewriteRule) : ruleAdmitted rule = true ↔
    rule.bindings = none ∧ isMatchCorrectAux rule.left = true ∧
    isMatchCorrectAux rule.right = true ∧ rule.premises.all premiseAdmitted = true := by
  simp [ruleAdmitted]

/-- Every observed capture is first-order because it comes from an admitted
authored LHS and an actual first-order subterm, at its original occurrence. -/
theorem reference_bindings_firstOrder (language : LanguageDef)
    (admitted : languageAdmitted language = true) (subject : PatternPlan)
    (observed : MeTTaILSubtermMatchAutomata.BoundMatch)
    (member : observed ∈ MeTTaILSubtermMatchAutomata.reference
      (MeTTaILSubtermMatchAutomata.languagePatterns language) subject) :
    FirstOrderBindings observed.bindings := by
  obtain ⟨entry, _, rowMember⟩ := List.mem_flatMap.mp member
  obtain ⟨row, authored, observedMember⟩ := List.mem_flatMap.mp rowMember
  obtain ⟨bindings, matched, rfl⟩ := List.mem_map.mp observedMember
  have patternMember := List.fst_mem_of_mem_zipIdx authored
  obtain ⟨rule, ruleMember, sameLeft⟩ := List.mem_map.mp patternMember
  have fields := (rule_admitted_iff rule).mp
    (language_admitted_rule language admitted rule ruleMember)
  exact matchPattern_bindings_firstOrder row.1 entry.2.erase
    (sameLeft ▸ fields.2.1) (isMatchCorrect_erase entry.2) bindings matched

/-- The relation-only compiler is contained in this contextual profile. -/
theorem premiseAdmitted_erase (plan : PremisePlan) : premiseAdmitted plan.erase = true := by
  simp only [premiseAdmitted, PremisePlan.erase, compileArgumentNames?_map_fvar]
  rfl

theorem ruleAdmitted_erase (plan : RulePlan) : ruleAdmitted plan.erase = true := by
  simp only [ruleAdmitted, RulePlan.erase, Option.isNone_none, Bool.true_and,
    isMatchCorrect_erase]
  apply List.all_eq_true.mpr
  intro premise member
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
  exact premiseAdmitted_erase source

/-- An existing complete relation-only compilation earns source admission;
this does not assume correctness of a separate contextual compiler. -/
theorem RuleProgram.language_admitted (language : LanguageDef)
    (program : RuleProgram language.rewrites) : languageAdmitted language = true := by
  apply List.all_eq_true.mpr
  intro rule member
  rw [← program.erase_eq_source] at member
  obtain ⟨plan, _, rfl⟩ := List.mem_map.mp member
  exact ruleAdmitted_erase plan

/-- One canonical premise preserves admitted captures. The recursive closure
hypothesis is discharged below by induction on canonical contextual fuel. -/
theorem premiseStepUsing_bindings_firstOrder (relations : RelationEnv)
    (relationsFirstOrder : FirstOrderRelations relations) (language : LanguageDef)
    (recursiveStep : Pattern → List Pattern)
    (stepFirstOrder : ∀ source, isMatchCorrectAux source = true →
      ∀ target ∈ recursiveStep source, isMatchCorrectAux target = true)
    (seed : Bindings) (seedFirstOrder : FirstOrderBindings seed)
    (premise : Premise) (admitted : premiseAdmitted premise = true)
    (bindings : Bindings)
    (member : bindings ∈ premiseStepUsing (engineBasePremises relations)
      language recursiveStep seed premise) : FirstOrderBindings bindings := by
  cases premise with
  | freshness condition =>
      have unchanged : bindings = seed :=
        premiseStepWithEnv_freshness_mem (relEnv := relations) (lang := language)
          (bindings := seed) (bs := bindings) (fc := condition) member
      simpa only [unchanged] using seedFirstOrder
  | forAll _ _ _ => simp [premiseAdmitted] at admitted
  | relationQuery relation arguments =>
      cases accepted : compileArgumentNames? arguments with
      | none => simp [premiseAdmitted, accepted] at admitted
      | some names =>
          have erased := compileArgumentNames?_erase arguments names accepted
          let plan : PremisePlan := ⟨relation, names⟩
          have represented : plan.erase = .relationQuery relation arguments := by
            simp only [PremisePlan.erase, plan, erased]
          rw [← represented, ← PremisePlan.run_eq_premiseStepUsing] at member
          exact plan.run_bindings_firstOrder relations language relationsFirstOrder
            seed seedFirstOrder bindings member
  | congruence source target =>
      simp only [premiseAdmitted, Bool.and_eq_true] at admitted
      obtain ⟨candidate, candidateMember, mergedMember⟩ := List.mem_flatMap.mp member
      obtain ⟨relative, relativeMatched, merged⟩ := List.mem_filterMap.mp mergedMember
      have candidateFirstOrder := stepFirstOrder _
        (applyBindings_firstOrder seed seedFirstOrder source admitted.1)
        candidate candidateMember
      exact FirstOrderBindings.merge seedFirstOrder
        (matchPattern_bindings_firstOrder target candidate admitted.2
          candidateFirstOrder relative relativeMatched) merged
  | scopedStep step =>
      simp only [premiseAdmitted, Bool.and_eq_true] at admitted
      simp only [premiseStepUsing, admitted.1, ↓reduceIte] at member
      obtain ⟨candidate, candidateMember, mergedMember⟩ := List.mem_flatMap.mp member
      obtain ⟨relative, relativeMatched, merged⟩ := List.mem_filterMap.mp mergedMember
      have candidateFirstOrder := stepFirstOrder _
        (applyBindings_firstOrder seed seedFirstOrder step.source admitted.2.1)
        candidate candidateMember
      exact FirstOrderBindings.merge seedFirstOrder
        (matchPattern_bindings_firstOrder step.target candidate admitted.2.2
          candidateFirstOrder relative relativeMatched) merged

/-- The actual ordered premise fold preserves the compiler image across
every successful branch, including recursive relative-binding merges. -/
theorem premisesUsing_bindings_firstOrder (relations : RelationEnv)
    (relationsFirstOrder : FirstOrderRelations relations) (language : LanguageDef)
    (recursiveStep : Pattern → List Pattern)
    (stepFirstOrder : ∀ source, isMatchCorrectAux source = true →
      ∀ target ∈ recursiveStep source, isMatchCorrectAux target = true)
    (premises : List Premise) (admitted : premises.all premiseAdmitted = true)
    (seed : Bindings) (seedFirstOrder : FirstOrderBindings seed)
    (bindings : Bindings)
    (member : bindings ∈ premisesUsing (engineBasePremises relations)
      language recursiveStep premises seed) : FirstOrderBindings bindings := by
  induction premises generalizing seed with
  | nil =>
      simp only [premisesUsing, List.mem_singleton] at member
      simpa only [member] using seedFirstOrder
  | cons premise premises ih =>
      simp only [List.all_cons, Bool.and_eq_true] at admitted
      obtain ⟨next, nextMember, tailMember⟩ := List.mem_flatMap.mp member
      exact ih admitted.2 next
        (premiseStepUsing_bindings_firstOrder relations relationsFirstOrder
          language recursiveStep stepFirstOrder seed seedFirstOrder
          premise admitted.1 next nextMember) tailMember

/-- An admitted canonical rule maps admitted subjects to admitted reducts.
The RHS binder-depth law is derived from the actual admitted source syntax. -/
theorem applyRuleUsing_firstOrder (relations : RelationEnv)
    (relationsFirstOrder : FirstOrderRelations relations) (language : LanguageDef)
    (recursiveStep : Pattern → List Pattern)
    (stepFirstOrder : ∀ source, isMatchCorrectAux source = true →
      ∀ target ∈ recursiveStep source, isMatchCorrectAux target = true)
    (rule : RewriteRule) (admitted : ruleAdmitted rule = true)
    (subject : Pattern) (subjectFirstOrder : isMatchCorrectAux subject = true)
    (target : Pattern)
    (member : target ∈ Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing
      RuleInterpretation.syntactic (engineBasePremises relations)
      language recursiveStep rule subject) : isMatchCorrectAux target = true := by
  simp only [ruleAdmitted, Bool.and_eq_true] at admitted
  obtain ⟨initial, initialMatched, instantiated⟩ := List.mem_flatMap.mp member
  obtain ⟨final, finalMember, rfl⟩ := List.mem_map.mp instantiated
  have initialFirstOrder := matchPattern_bindings_firstOrder rule.left subject
    admitted.2.1 subjectFirstOrder initial initialMatched
  have finalFirstOrder := premisesUsing_bindings_firstOrder relations
    relationsFirstOrder language recursiveStep stepFirstOrder
    rule.premises admitted.2.2.2 initial initialFirstOrder final finalMember
  change isMatchCorrectAux (applyRuleBindings rule final) = true
  rw [applyRuleBindings, applyBindingsScoped_zero_of_binderFree _ _ _
    (binderFree_of_firstOrder rule.right admitted.2.2.1)]
  exact applyBindings_firstOrder final finalFirstOrder rule.right admitted.2.2.1

/-- Recursive support is earned at every depth from the complete admitted
source and the actual relation table's first-order payload closure. -/
theorem rewriteAt_firstOrder (relations : RelationEnv)
    (relationsFirstOrder : FirstOrderRelations relations) (language : LanguageDef)
    (admitted : languageAdmitted language = true) (fuel : Nat)
    (subject : Pattern) (subjectFirstOrder : isMatchCorrectAux subject = true)
    (target : Pattern)
    (member : target ∈ Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt
      RuleInterpretation.syntactic (engineBasePremises relations) language fuel subject) :
    isMatchCorrectAux target = true := by
  induction fuel generalizing subject target with
  | zero => simp [Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt] at member
  | succ fuel ih =>
      obtain ⟨rule, ruleMember, targetMember⟩ := List.mem_flatMap.mp member
      exact applyRuleUsing_firstOrder relations relationsFirstOrder language _
        (fun source sourceFirstOrder result resultMember =>
          ih source sourceFirstOrder result resultMember)
        rule (language_admitted_rule language admitted rule ruleMember)
        subject subjectFirstOrder target targetMember

/-- Both shared matching strategies retain the admitted compiler image
through their canonical authorized contextual dispatch. -/
theorem runAt_firstOrder (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (relations : RelationEnv) (relationsFirstOrder : FirstOrderRelations relations)
    (language : LanguageDef) (admitted : languageAdmitted language = true)
    (fuel : Nat) (subject : PatternPlan) (target : Pattern)
    (member : target ∈ MeTTaILMatchAutomataExecution.runAt strategy
      (engineBasePremises relations) language fuel subject) : isMatchCorrectAux target = true := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact] at member
  exact rewriteAt_firstOrder relations relationsFirstOrder language admitted
    fuel subject.erase (isMatchCorrect_erase subject) target member

/-- Every recursive reduct can re-enter the independently admitted subject
compiler. No assumption about an intermediate target's representation is used. -/
theorem runAt_target_compiles (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (relations : RelationEnv) (relationsFirstOrder : FirstOrderRelations relations)
    (language : LanguageDef) (admitted : languageAdmitted language = true)
    (fuel : Nat) (subject : PatternPlan) (target : Pattern)
    (member : target ∈ MeTTaILMatchAutomataExecution.runAt strategy
      (engineBasePremises relations) language fuel subject) :
    ∃ plan, compilePattern? target = some plan := by
  have firstOrder := runAt_firstOrder strategy relations relationsFirstOrder
    language admitted fuel subject target member
  cases accepted : compilePattern? target with
  | none =>
      have same := compilePattern?_isSome_eq_isMatchCorrectAux target
      simp only [accepted, Option.isSome_none, firstOrder] at same
      cases same
  | some plan => exact ⟨plan, rfl⟩

/-- The actual contextual executor cannot promote a child match when every
authored root row fails to match the supplied subject. -/
theorem rewriteAt_eq_nil_of_no_root_match (base : BasePremiseEvaluator)
    (language : LanguageDef) (fuel : Nat) (subject : Pattern)
    (noRoot : ∀ rule ∈ language.rewrites, matchPattern rule.left subject = []) :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt
      RuleInterpretation.syntactic base language fuel subject = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      apply List.flatMap_eq_nil_iff.mpr
      intro rule member
      simp only [Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing,
        RuleInterpretation.syntactic, noRoot rule member, List.flatMap_nil]

theorem runAt_eq_nil_of_no_root_match (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (base : BasePremiseEvaluator) (language : LanguageDef) (fuel : Nat)
    (subject : PatternPlan)
    (noRoot : ∀ rule ∈ language.rewrites, matchPattern rule.left subject.erase = []) :
    MeTTaILMatchAutomataExecution.runAt strategy base language fuel subject = [] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  exact rewriteAt_eq_nil_of_no_root_match base language fuel subject.erase noRoot

/-! ## Authorization and closure controls -/

namespace Controls

def start : Pattern := .apply "Start" []
def middle : Pattern := .apply "Middle" []
def final : Pattern := .apply "Final" []
def box (subject : Pattern) : Pattern := .apply "Box" [subject]

def firstRule : RewriteRule :=
  { name := "first", typeContext := [], premises := [], left := start, right := middle }

def secondRule : RewriteRule :=
  { name := "second", typeContext := [], premises := [], left := start, right := final }

def contextualRule : RewriteRule :=
  { name := "box-step", typeContext := []
    premises := [.congruence (.fvar "x") (.fvar "y")]
    left := box (.fvar "x"), right := box (.fvar "y") }

def language : LanguageDef :=
  { LanguageDef.empty "contextual-controls" with
    rewrites := [firstRule, secondRule, firstRule, contextualRule] }

def childOnlyLanguage : LanguageDef :=
  { language with rewrites := [firstRule, secondRule, firstRule] }

def subject : PatternPlan := .application "Box" [.application "Start" []]

def conflictingLanguage : LanguageDef :=
  { language with rewrites := [firstRule, secondRule, firstRule,
    { contextualRule with premises := [.congruence (.fvar "x") (.fvar "x")] }] }

def guardedLanguage : LanguageDef :=
  { language with rewrites := [firstRule, secondRule, firstRule,
    { contextualRule with premises := [.relationQuery "allow" [.fvar "x"],
      .congruence (.fvar "x") (.fvar "y")] }] }

def scopedLanguage : LanguageDef :=
  { language with rewrites := [firstRule, secondRule, firstRule,
    { contextualRule with premises := [.scopedStep
      (ScopedStepPremise.root (.base "Term") (.fvar "x") (.fvar "y"))] }] }

def guardedRelations : RelationEnv where
  tuples relation _ := if relation = "allow" then [[start], [start]] else []

/-- The complete contextual profile is earned from the authored fields. -/
theorem language_admitted : languageAdmitted language = true := by decide +kernel

theorem guarded_language_admitted : languageAdmitted guardedLanguage = true := by decide +kernel

theorem scoped_language_admitted : languageAdmitted scopedLanguage = true := by decide +kernel

theorem provider_firstOrder : FirstOrderRelations guardedRelations := by
  intro relation arguments _ values member
  by_cases selected : relation = "allow"
  · simp [guardedRelations, selected] at member
    subst values
    rfl
  · simp [guardedRelations, selected] at member

/-- Source row order and duplicate recursive witnesses remain observable at
the parent; both matchers feed the same canonical contextual execution. -/
theorem recursive_witnesses_ordered (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises RelationEnv.empty)
      language 2 subject = [box middle, box final, box middle] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

theorem exhausted_context_depth (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises RelationEnv.empty)
      language 1 subject = [] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

/-- Matching the nested Start is insufficient when no Box rule authorizes it. -/
theorem unauthorized_child (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises RelationEnv.empty)
      childOnlyLanguage 4 subject = [] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

/-- A recursive target match remains relative, then conflicts with the
original x=Start seed when the recursive candidate is Middle or Final. -/
theorem conflicting_relative_match (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises RelationEnv.empty)
      conflictingLanguage 2 subject = [] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

theorem missing_guard (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises RelationEnv.empty)
      guardedLanguage 2 subject = [] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

/-- Duplicate guard tuples and recursive rows both retain their witnesses. -/
theorem guarded_recursive_witnesses_ordered (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises guardedRelations)
      guardedLanguage 2 subject =
      [box middle, box final, box middle, box middle, box final, box middle] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

theorem root_scoped_step (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises RelationEnv.empty)
      scopedLanguage 2 subject = [box middle, box final, box middle] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

theorem nonempty_scoped_telescope_refused : premiseAdmitted (.scopedStep
    { binders := [.base "Term"], resultType := .base "Term"
      source := .fvar "x", target := .fvar "y" }) = false := rfl

theorem annotated_rule_refused : ruleAdmitted
    { contextualRule with bindings := some { dependencies := [] } } = false := rfl

theorem binder_endpoint_refused : premiseAdmitted
    (.congruence (.lambda (some "x") (.bvar 0)) (.fvar "y")) = false := rfl

def freshnessRule : RewriteRule :=
  { name := "fresh", typeContext := []
    premises := [.freshness { varName := "atom", term := .fvar "subject" }]
    left := .apply "Fresh" [.fvar "subject"], right := .apply "Accepted" [] }

def freshnessLanguage : LanguageDef :=
  { LanguageDef.empty "freshness-controls" with rewrites := [freshnessRule, freshnessRule] }

def resolvedFreshnessLanguage : LanguageDef :=
  { freshnessLanguage with rewrites := [{ freshnessRule with
    left := .apply "FreshName" [.fvar "atom", .fvar "subject"] }] }

theorem freshness_language_admitted : languageAdmitted freshnessLanguage = true := by
  decide +kernel

/-- Syntactic freshness retains duplicate authored rule occurrences. -/
theorem freshness_witnesses_ordered (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises RelationEnv.empty)
      freshnessLanguage 1 (.application "Fresh" [.application "Pair" [.metavariable "other", .metavariable "other"]]) =
      [.apply "Accepted" [], .apply "Accepted" []] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

theorem nonfresh_subject_refused (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises RelationEnv.empty)
      freshnessLanguage 1 (.application "Fresh" [.application "Pair" [.metavariable "other", .metavariable "atom"]]) = [] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

/-- The name itself is resolved from the captured literal free-variable value. -/
theorem resolved_freshness_name (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises RelationEnv.empty)
      resolvedFreshnessLanguage 1 (.application "FreshName" [.metavariable "actual", .metavariable "other"]) =
      [.apply "Accepted" []] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

theorem resolved_nonfresh_name_refused (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises RelationEnv.empty)
      resolvedFreshnessLanguage 1 (.application "FreshName" [.metavariable "actual", .metavariable "actual"]) = [] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

theorem nonname_freshness_binding_refused (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises RelationEnv.empty)
      resolvedFreshnessLanguage 1 (.application "FreshName" [.application "NotAName" [], .metavariable "other"]) = [] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

/-- A relation query can bind the name used by a later freshness guard. -/
def nameGuardLanguage (queryFirst : Bool) : LanguageDef :=
  { freshnessLanguage with rewrites := [{ freshnessRule with premises :=
      if queryFirst then
        [.relationQuery "name" [.fvar "atom"],
         .freshness { varName := "atom", term := .fvar "subject" }]
      else
        [.freshness { varName := "atom", term := .fvar "subject" },
         .relationQuery "name" [.fvar "atom"]] }] }

def nameGuardRelations : RelationEnv :=
  ⟨fun relation _ => if relation == "name" then [[.fvar "actual"], [.fvar "actual"]] else []⟩

/-- Query-first resolves atom to actual, which occurs in the captured subject. -/
theorem resolved_guard_order_refused (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises nameGuardRelations)
      (nameGuardLanguage true) 1 (.application "Fresh" [.metavariable "actual"]) = [] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

/-- Freshness-first checks the then-unbound literal name and retains both
later relation witnesses; the premise list cannot be reordered. -/
theorem literal_guard_order_preserved (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises nameGuardRelations)
      (nameGuardLanguage false) 1 (.application "Fresh" [.metavariable "actual"]) =
      [.apply "Accepted" [], .apply "Accepted" []] := by
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  decide +kernel

end Controls

#print axioms premiseStepUsing_bindings_firstOrder
#print axioms reference_bindings_firstOrder
#print axioms premisesUsing_bindings_firstOrder
#print axioms applyRuleUsing_firstOrder
#print axioms rewriteAt_firstOrder
#print axioms runAt_firstOrder
#print axioms runAt_target_compiles
#print axioms rewriteAt_eq_nil_of_no_root_match
#print axioms runAt_eq_nil_of_no_root_match
#print axioms Controls.recursive_witnesses_ordered
#print axioms Controls.exhausted_context_depth
#print axioms Controls.unauthorized_child
#print axioms Controls.conflicting_relative_match
#print axioms Controls.missing_guard
#print axioms Controls.guarded_recursive_witnesses_ordered
#print axioms Controls.root_scoped_step
#print axioms Controls.nonempty_scoped_telescope_refused
#print axioms Controls.annotated_rule_refused
#print axioms Controls.freshness_witnesses_ordered
#print axioms Controls.nonfresh_subject_refused
#print axioms Controls.resolved_freshness_name
#print axioms Controls.nonname_freshness_binding_refused
#print axioms Controls.resolved_guard_order_refused
#print axioms Controls.literal_guard_order_preserved
#print axioms Controls.binder_endpoint_refused

end Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderContextualExecution
