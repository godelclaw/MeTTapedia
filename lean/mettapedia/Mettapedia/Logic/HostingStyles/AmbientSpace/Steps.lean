import Mettapedia.Logic.HostingStyles.AmbientSpace.Atoms

/-!
# The steps of a member of the family on the atoms of λΠ terms

The member at a space steps by beta, by the congruences of application,
product and abstraction, by the release of a dropped quotation, and by the
root step, whose premise the evaluator answers from the space.

* `step_root`, `root_inv`: what a root step is, in every language that has
  the rewrite.  A root step takes a pattern to an answer of the space for it;
  the pattern need not be a run, and the answer is in no run.
* **The steps of the member at the space of a list of rules, from the atom of
  a term, are the atoms of the steps of the term** in the theory of those
  rules, at every position and at every depth (`ambient_step_iff`): beta is a
  rewrite of the presentation, a rule at the root is found by the evaluator
  in the space, and a position beneath the root is reached by the congruences
  that beta uses.  No rewrite hands the space down: the evaluator has it.
* Hence the transitions of the atom of a term (`termStep_atomTerm_iff`); one
  step of the term is one step of the member.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientSpace

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.LanguageDef.LFTyping (subst0)
open Mettapedia.GSLT.Dedukti (Theory RootStep inst patternVars usesOnly)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule lamBodyRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce

/-! ## The root step -/

/-- **The root step**, under the evaluator at a space: from a pattern to an
answer of the space for it, both read up to the static equivalence. -/
theorem step_root {lang : LanguageDef} (member : rootRule ∈ lang.rewrites)
    {space subject answer : Pattern}
    (found : answer ∈ matchResults (contract space) (contract subject)) :
    StepAt (ambientEvaluator space) lang 1 subject answer := by
  refine stepAt_of_rule (rule := rootRule) member (initial := [("subject", subject)])
    (final := [("answer", answer), ("subject", subject)]) ?_ ?_ ?_
  · simp [rootRule, matchPattern]
  · refine .cons (.relationQuery ?_) (.nil _)
    show _ ∈ (matchResults (contract space)
      (contract (applyBindings [("subject", subject)] (.fvar "subject")))).map
        fun result => ("answer", result) :: [("subject", subject)]
    have subjectValue : applyBindings [("subject", subject)] (.fvar "subject") = subject := by
      simp [applyBindings]
    rw [subjectValue]
    exact List.mem_map.mpr ⟨answer, found, rfl⟩
  · simp [applyRuleBindings, rootRule, applyBindings]

/-- What a root step is, under the evaluator at a space. -/
theorem root_inv {lang : LanguageDef} {space : Pattern} {fuel : Nat} {source : Pattern}
    {initial final : Bindings} (matched : initial ∈ matchPattern rootRule.left source)
    (premises : PremisesAt (ambientEvaluator space) lang fuel initial rootRule.premises final) :
    ∃ answer, answer ∈ matchResults (contract space) (contract source) ∧
      applyRuleBindings rootRule final = answer := by
  have bound : initial = [("subject", source)] :=
    mem_matchPattern_fvar.mp (show initial ∈ matchPattern (.fvar "subject") source from matched)
  subst bound
  have premises' : PremisesAt (ambientEvaluator space) lang fuel [("subject", source)]
      [rootPremise] final := premises
  cases premises' with
  | cons first rest =>
      cases rest
      cases first with
      | relationQuery answered =>
          have answers : final ∈ (matchResults (contract space)
              (contract (applyBindings [("subject", source)] (.fvar "subject")))).map
                fun result => ("answer", result) :: [("subject", source)] := answered
          have subjectValue : applyBindings [("subject", source)] (.fvar "subject") = source := by
            simp [applyBindings]
          rw [subjectValue] at answers
          obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
          exact ⟨answer, found, by simp [applyRuleBindings, rootRule, applyBindings]⟩

/-- **Negative**: under the evaluator that answers nothing there is no root
step. -/
theorem silent_no_root {lang : LanguageDef} {fuel : Nat} {initial final : Bindings} :
    ¬ PremisesAt silentEvaluator lang fuel initial rootRule.premises final := by
  intro premises
  have premises' : PremisesAt silentEvaluator lang fuel initial [rootPremise] final := premises
  cases premises' with
  | cons first rest =>
      cases first with
      | relationQuery answered => cases answered

/-! ## From the atom of a term: every step is the atom of a step -/

/-- **A step of the member at a space, from the atom of a term, is the atom
of a step of the term**, in every theory whose steps at the root include what
the space answers for the atoms of terms.  At every depth. -/
theorem ambient_stepAt_sound_of {space : Pattern} {theory : Theory}
    (answers : ∀ {depth : Nat} {term : LF.Term} {answer : Pattern},
      answer ∈ matchResults (contract space) (atomAt depth term) →
        ∃ next, answer = atomAt depth next ∧ Dedukti.Step theory term next) :
    ∀ (fuel : Nat) {depth : Nat} {source : LF.Term} {target : Pattern},
      StepAt (ambientEvaluator space) ambient fuel (atomAt depth source) target →
        ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next := by
  intro fuel
  induction fuel with
  | zero => intro depth source target step; cases step
  | succ fuel ih =>
      intro depth source target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [ambient_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, argument, shape, applied⟩ := beta_inv matched premises
        obtain ⟨function, argumentTerm, rfl, functionEq, rfl⟩ := atomAt_eq_app shape
        obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_lam functionEq.symm
        simp only [Pattern.lambda.injEq] at bodyEq
        obtain ⟨-, rfl⟩ := bodyEq
        exact ⟨subst0 argumentTerm bodyTerm, by rw [applied, instantiateBVar_atomAt],
          Dedukti.Step.root (.beta domainTerm bodyTerm argumentTerm)⟩
      · obtain ⟨function, argument, next, shape, inner, applied⟩ := appFunction_inv matched premises
        obtain ⟨first, second, rfl, rfl, rfl⟩ := atomAt_eq_app shape
        obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
        exact ⟨.app nextTerm second, by rw [applied]; rfl,
          innerStep.plug (.appFunction .hole second)⟩
      · obtain ⟨function, argument, next, shape, inner, applied⟩ := appArgument_inv matched premises
        obtain ⟨first, second, rfl, rfl, rfl⟩ := atomAt_eq_app shape
        obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
        exact ⟨.app first nextTerm, by rw [applied]; rfl,
          innerStep.plug (.appArgument first .hole)⟩
      · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ := piDomain_inv matched premises
        obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_pi shape
        simp only [Pattern.lambda.injEq] at bodyEq
        obtain ⟨-, rfl⟩ := bodyEq
        obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
        exact ⟨.pi nextTerm second, by rw [applied]; rfl,
          innerStep.plug (.piDomain .hole second)⟩
      · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ := piBody_inv matched premises
        obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_pi shape
        simp only [Pattern.lambda.injEq] at bodyEq
        obtain ⟨-, rfl⟩ := bodyEq
        obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
        exact ⟨.pi first nextTerm, by rw [applied]; rfl,
          innerStep.plug (.piBody first .hole)⟩
      · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ := lamDomain_inv matched premises
        obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_lam shape
        simp only [Pattern.lambda.injEq] at bodyEq
        obtain ⟨-, rfl⟩ := bodyEq
        obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
        exact ⟨.lam nextTerm second, by rw [applied]; rfl,
          innerStep.plug (.lamDomain .hole second)⟩
      · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ := lamBody_inv matched premises
        obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_lam shape
        simp only [Pattern.lambda.injEq] at bodyEq
        obtain ⟨-, rfl⟩ := bodyEq
        obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
        exact ⟨.lam first nextTerm, by rw [applied]; rfl,
          innerStep.plug (.lamBody first .hole)⟩
      · exact absurd matched (atomAt_not_matched (label := "prime-drop") (by decide))
      · obtain ⟨answer, found, applied⟩ := root_inv matched premises
        rw [contract_atomAt] at found
        obtain ⟨nextTerm, rfl, rootStep⟩ := answers found
        exact ⟨nextTerm, applied, rootStep⟩

/-- **A step of the member at the space of a list of rules, from the atom of
a term, is the atom of a step of the term**, in every theory that declares
those rules.  At every depth. -/
theorem ambient_stepAt_sound {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (declared : ∀ rule ∈ rules, theory.rule rule) (fuel : Nat) {depth : Nat}
    {source : LF.Term} {target : Pattern}
    (step : StepAt (ambientEvaluator (ruleSpace rules)) ambient fuel (atomAt depth source) target) :
    ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next :=
  ambient_stepAt_sound_of (fun found => by
    rw [contract_ruleSpace] at found
    obtain ⟨rule, inRules, assignment, rfl, rfl⟩ :=
      exists_instance_of_mem_matchResults firstOrder bound found
    exact ⟨_, rfl, Dedukti.Step.root (.rule assignment (declared rule inRules))⟩) fuel step

/-! ## Every step of the term is a step of the member -/

/-- A beta contraction at the root is a step of every member between the
atoms, at every depth. -/
theorem ambient_beta_stepAt {base : BasePremiseEvaluator} (depth : Nat)
    (domain body argument : LF.Term) :
    StepAt base ambient 1 (atomAt depth (.app (.lam domain body) argument))
      (atomAt depth (subst0 argument body)) := by
  have step := step_beta (base := base) (lang := ambient) (by simp [ambient_rewrites])
    (atomAt depth domain) (atomAt (depth + 1) body) (atomAt depth argument) none
  rw [instantiateBVar_atomAt] at step
  exact step

/-- **Every step of a term, in a theory whose rules are those of a list and
which has no definition, is a step of the member at the space of the list
between the atoms**, at every depth. -/
theorem ambient_stepAt_complete {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (listed : ∀ rule, theory.rule rule → rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {source next : LF.Term}
    (step : Dedukti.Step theory source next) :
    ∀ depth : Nat, ∃ fuel, StepAt (ambientEvaluator (ruleSpace rules)) ambient fuel
      (atomAt depth source) (atomAt depth next) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole =>
          intro depth
          cases root with
          | beta domain body argument => exact ⟨1, ambient_beta_stepAt depth domain body argument⟩
          | delta defined =>
              rw [undefined] at defined
              cases defined
          | @rule rule assignment member =>
              refine ⟨1, step_root (by simp [ambient_rewrites]) ?_⟩
              show _ ∈ matchResults (contract (ruleSpace rules))
                (contract (atomAt depth (inst assignment rule.lhs)))
              rw [contract_ruleSpace, contract_atomAt]
              exact atomAt_mem_matchResults firstOrder bound (listed rule member) depth assignment
      | appFunction rest argument ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appFunction (by simp [ambient_rewrites])
            (atomAt depth argument) inner⟩
      | appArgument function rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appArgument (by simp [ambient_rewrites])
            (atomAt depth function) inner⟩
      | piDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_piDomain (by simp [ambient_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | piBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_piBody (by simp [ambient_rewrites])
            (atomAt depth domain) none inner⟩
      | lamDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_lamDomain (by simp [ambient_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | lamBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_lamBody (by simp [ambient_rewrites])
            (atomAt depth domain) none inner⟩

/-- **The member at the space of a list of rules computes, on the atom of a
term, by beta and by those rules**: its steps from the atom are the atoms of
the steps of the term in a theory whose rules are those of the list and which
has no definition.  At every depth, and one step for one step. -/
theorem ambient_step_iff {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (ambientEvaluator (ruleSpace rules)) ambient (atomAt depth source) target ↔
      ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next := by
  constructor
  · rintro ⟨fuel, step⟩
    exact ambient_stepAt_sound firstOrder bound (fun rule member => (rulesIff rule).mpr member)
      fuel step
  · rintro ⟨next, rfl, step⟩
    exact ambient_stepAt_complete firstOrder bound (fun rule member => (rulesIff rule).mp member)
      undefined step depth

/-- **The transitions of the atom of a term**, in the member at the space of
a list of rules: the atoms of its steps. -/
theorem termStep_atomTerm_iff {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Contexts.Term ambient (atomInterface depth)} :
    TermStep (ambientEvaluator (ruleSpace rules)) ambient (atomTerm depth source) target ↔
      ∃ next, Dedukti.Step theory source next ∧ target = atomTerm depth next := by
  constructor
  · rintro ⟨redex, contractum, before, fired, after⟩
    obtain rfl := eq_atomTerm_of_related before
    obtain ⟨next, shape, step⟩ := (ambient_step_iff firstOrder bound rulesIff undefined).mp fired
    have same : contractum = atomTerm depth next := Subtype.ext shape
    rw [same] at after
    exact ⟨next, step, eq_atomTerm_of_related after⟩
  · rintro ⟨next, step, rfl⟩
    exact ⟨atomTerm depth source, atomTerm depth next, Relation.EqvGen.refl _,
      (ambient_step_iff firstOrder bound rulesIff undefined).mpr ⟨next, rfl, step⟩,
      Relation.EqvGen.refl _⟩

#print axioms step_root
#print axioms root_inv
#print axioms silent_no_root
#print axioms ambient_stepAt_sound_of
#print axioms ambient_stepAt_sound
#print axioms ambient_stepAt_complete
#print axioms ambient_step_iff
#print axioms termStep_atomTerm_iff

end Mettapedia.Logic.HostingStyles.AmbientSpace
