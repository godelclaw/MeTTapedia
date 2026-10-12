import Mettapedia.Logic.HostingStyles.AtomsReduce.Rules
import Mettapedia.Logic.HostingStyles.AtomsReduce.Matching

/-!
# The steps of the candidate on the atoms of λΠ terms

Two statements, each at every depth and each in both directions.

* **An atom by itself computes by beta**: the steps of the candidate from the
  atom of a term are the atoms of the beta steps of the term, at every
  position, under every evaluator of the premises (`plain_step_iff`).  No
  rewrite about a run or a dropping matches the atom of a term.
* **A run computes by beta and by the rules its space stores**: under the
  matching evaluator, the steps of the candidate from the run of the atom of
  a term, in the space of a list of rules without binder whose right sides
  are bound, are the runs of the atoms of the steps of the term in the theory
  of those rules, at every position (`run_step_iff`).  The rule at the root
  is found by the evaluator; the positions beneath are reached by the
  congruences beneath a run; beta is a rewrite of the candidate, and reaches
  the run through the congruence of its subject.

One step of the term is one step of the candidate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (subst0)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
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

variable {base : BasePremiseEvaluator}

/-! ## What matches the atom of a term, and what matches a run -/

/-- An application of a constructor that the atom of no term is headed by
matches no atom of a term. -/
theorem atomAt_not_matched {label : String}
    (outside : label ∉ ["prime-variable", "prime-symbol", "App", "Lam", "Pi"])
    {parameters : List Pattern} {depth : Nat} {term : LF.Term} {bindings : Bindings} :
    bindings ∉ matchPattern (.apply label parameters) (atomAt depth term) := by
  intro matched
  obtain ⟨arguments, shape, -⟩ := eq_apply_of_matched matched
  exact atomAt_ne_apply outside depth term arguments shape

/-- An application of another constructor matches no run. -/
theorem run_not_matched {label : String} (other : label ≠ "prime-run") {parameters : List Pattern}
    {space subject : Pattern} {bindings : Bindings} :
    bindings ∉ matchPattern (.apply label parameters) (runPattern space subject) := by
  intro matched
  obtain ⟨arguments, shape, -⟩ := eq_apply_of_matched matched
  simp only [runPattern, Pattern.apply.injEq] at shape
  exact other shape.1.symm

theorem runPattern_injective {space subject otherSpace otherSubject : Pattern}
    (same : runPattern space subject = runPattern otherSpace otherSubject) :
    space = otherSpace ∧ subject = otherSubject := by
  simpa [runPattern] using same

/-! ## An atom by itself -/

/-- **A step of the candidate from the atom of a term is the atom of a beta
step of the term**, at every depth and under every evaluator. -/
theorem plain_stepAt_sound (theory : Theory) :
    ∀ (fuel : Nat) {depth : Nat} {source : LF.Term} {target : Pattern},
      StepAt base atomsReduce fuel (atomAt depth source) target →
        ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next := by
  intro fuel
  induction fuel with
  | zero => intro depth source target step; cases step
  | succ fuel ih =>
      intro depth source target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [atomsReduce_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
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
      · exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))

/-- A beta contraction at the root is a step of the candidate between the
atoms, at every depth. -/
theorem plain_beta_stepAt (depth : Nat) (domain body argument : LF.Term) :
    StepAt base atomsReduce 1 (atomAt depth (.app (.lam domain body) argument))
      (atomAt depth (subst0 argument body)) := by
  have step := step_beta (base := base) (lang := atomsReduce) (by simp [atomsReduce_rewrites])
    (atomAt depth domain) (atomAt (depth + 1) body) (atomAt depth argument) none
  rw [instantiateBVar_atomAt] at step
  exact step

/-- **Every beta step of a term is a step of the candidate between the
atoms**, at every depth and under every evaluator. -/
theorem plain_stepAt_complete {source next : LF.Term}
    (step : Dedukti.Step Theory.empty source next) :
    ∀ depth : Nat, ∃ fuel, StepAt base atomsReduce fuel (atomAt depth source)
      (atomAt depth next) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole =>
          intro depth
          cases root with
          | beta domain body argument => exact ⟨1, plain_beta_stepAt depth domain body argument⟩
          | delta defined => cases defined
          | rule assignment member => exact member.elim
      | appFunction rest argument ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appFunction (by simp [atomsReduce_rewrites])
            (atomAt depth argument) inner⟩
      | appArgument function rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appArgument (by simp [atomsReduce_rewrites])
            (atomAt depth function) inner⟩
      | piDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_piDomain (by simp [atomsReduce_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | piBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_piBody (by simp [atomsReduce_rewrites])
            (atomAt depth domain) none inner⟩
      | lamDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_lamDomain (by simp [atomsReduce_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | lamBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_lamBody (by simp [atomsReduce_rewrites])
            (atomAt depth domain) none inner⟩

/-- **An atom by itself computes by beta**: the steps of the candidate from
the atom of a term are the atoms of its beta steps, at every depth and under
every evaluator. -/
theorem plain_step_iff {depth : Nat} {source : LF.Term} {target : Pattern} :
    Step base atomsReduce (atomAt depth source) target ↔
      ∃ next, target = atomAt depth next ∧ Dedukti.Step Theory.empty source next := by
  constructor
  · rintro ⟨fuel, step⟩
    exact plain_stepAt_sound Theory.empty fuel step
  · rintro ⟨next, rfl, step⟩
    exact plain_stepAt_complete step depth

/-! ## A run in the space of a list of rules -/

/-- **A step of the candidate from the run of the atom of a term is the run
of the atom of a step of the term**, in every theory whose steps at the root
include what the space answers for the atoms of terms.  At every depth, and
for every space: the six congruences beneath a run and the congruence of its
subject do not read the space. -/
theorem run_stepAt_sound_of {space : Pattern} {theory : Theory}
    (answers : ∀ {depth : Nat} {term : LF.Term} {answer : Pattern},
      answer ∈ matchResults (contract space) (atomAt depth term) →
        ∃ next, answer = atomAt depth next ∧ Dedukti.Step theory term next) :
    ∀ (fuel : Nat) {depth : Nat} {source : LF.Term} {target : Pattern},
      StepAt matchingEvaluator atomsReduce fuel (runPattern space (atomAt depth source)) target →
        ∃ next, target = runPattern space (atomAt depth next) ∧
          Dedukti.Step theory source next := by
  intro fuel
  induction fuel with
  | zero => intro depth source target step; cases step
  | succ fuel ih =>
      intro depth source target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [atomsReduce_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "Pi") (by decide))
      · exact absurd matched (run_not_matched (label := "Pi") (by decide))
      · exact absurd matched (run_not_matched (label := "Lam") (by decide))
      · exact absurd matched (run_not_matched (label := "Lam") (by decide))
      · exact absurd matched (run_not_matched (label := "prime-drop") (by decide))
      · obtain ⟨otherSpace, subject, next, shape, inner, applied⟩ := runSubject_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨nextTerm, rfl, innerStep⟩ := plain_stepAt_sound theory fuel inner
        exact ⟨nextTerm, applied, innerStep⟩
      · obtain ⟨otherSpace, subject, answer, shape, found, applied⟩ := runRoot_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        rw [contract_atomAt] at found
        obtain ⟨nextTerm, rfl, rootStep⟩ := answers found
        exact ⟨nextTerm, applied, rootStep⟩
      · obtain ⟨otherSpace, function, argument, next, shape, inner, applied⟩ :=
          runAppFunction_inv matched premises
        obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
        obtain ⟨first, second, rfl, rfl, rfl⟩ := atomAt_eq_app subjectEq
        obtain ⟨nextTerm, nextEq, innerStep⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective nextEq
        exact ⟨.app nextTerm second, applied, innerStep.plug (.appFunction .hole second)⟩
      · obtain ⟨otherSpace, function, argument, next, shape, inner, applied⟩ :=
          runAppArgument_inv matched premises
        obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
        obtain ⟨first, second, rfl, rfl, rfl⟩ := atomAt_eq_app subjectEq
        obtain ⟨nextTerm, nextEq, innerStep⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective nextEq
        exact ⟨.app first nextTerm, applied, innerStep.plug (.appArgument first .hole)⟩
      · obtain ⟨otherSpace, domain, binder, body, next, shape, inner, applied⟩ :=
          runPiDomain_inv matched premises
        obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
        obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_pi subjectEq
        simp only [Pattern.lambda.injEq] at bodyEq
        obtain ⟨-, rfl⟩ := bodyEq
        obtain ⟨nextTerm, nextEq, innerStep⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective nextEq
        exact ⟨.pi nextTerm second, applied, innerStep.plug (.piDomain .hole second)⟩
      · obtain ⟨otherSpace, domain, binder, body, next, shape, inner, applied⟩ :=
          runPiBody_inv matched premises
        obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
        obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_pi subjectEq
        simp only [Pattern.lambda.injEq] at bodyEq
        obtain ⟨-, rfl⟩ := bodyEq
        obtain ⟨nextTerm, nextEq, innerStep⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective nextEq
        exact ⟨.pi first nextTerm, applied, innerStep.plug (.piBody first .hole)⟩
      · obtain ⟨otherSpace, domain, binder, body, next, shape, inner, applied⟩ :=
          runLamDomain_inv matched premises
        obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
        obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_lam subjectEq
        simp only [Pattern.lambda.injEq] at bodyEq
        obtain ⟨-, rfl⟩ := bodyEq
        obtain ⟨nextTerm, nextEq, innerStep⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective nextEq
        exact ⟨.lam nextTerm second, applied, innerStep.plug (.lamDomain .hole second)⟩
      · obtain ⟨otherSpace, domain, binder, body, next, shape, inner, applied⟩ :=
          runLamBody_inv matched premises
        obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
        obtain ⟨first, second, rfl, rfl, bodyEq⟩ := atomAt_eq_lam subjectEq
        simp only [Pattern.lambda.injEq] at bodyEq
        obtain ⟨-, rfl⟩ := bodyEq
        obtain ⟨nextTerm, nextEq, innerStep⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective nextEq
        exact ⟨.lam first nextTerm, applied, innerStep.plug (.lamBody first .hole)⟩

/-- **A step of the candidate from the run of the atom of a term, in the
space of a list of rules, is the run of the atom of a step of the term**, in
every theory that declares those rules.  At every depth. -/
theorem run_stepAt_sound {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (declared : ∀ rule ∈ rules, theory.rule rule) (fuel : Nat) {depth : Nat}
    {source : LF.Term} {target : Pattern}
    (step : StepAt matchingEvaluator atomsReduce fuel
      (runPattern (ruleSpace rules) (atomAt depth source)) target) :
    ∃ next, target = runPattern (ruleSpace rules) (atomAt depth next) ∧
      Dedukti.Step theory source next :=
  run_stepAt_sound_of (fun found => by
    rw [contract_ruleSpace] at found
    obtain ⟨rule, inRules, assignment, rfl, rfl⟩ :=
      exists_instance_of_mem_matchResults firstOrder bound found
    exact ⟨_, rfl, Dedukti.Step.root (.rule assignment (declared rule inRules))⟩) fuel step

/-- **Every step of a term, in a theory whose rules are those of a list and
which has no definition, is a step of the candidate between the runs of the
atoms in the space of the list**, at every depth. -/
theorem run_stepAt_complete {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (listed : ∀ rule, theory.rule rule → rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {source next : LF.Term}
    (step : Dedukti.Step theory source next) :
    ∀ depth : Nat, ∃ fuel, StepAt matchingEvaluator atomsReduce fuel
      (runPattern (ruleSpace rules) (atomAt depth source))
      (runPattern (ruleSpace rules) (atomAt depth next)) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole =>
          intro depth
          cases root with
          | beta domain body argument =>
              exact ⟨2, step_runSubject (by simp [atomsReduce_rewrites]) _
                (plain_beta_stepAt depth domain body argument)⟩
          | delta defined =>
              rw [undefined] at defined
              cases defined
          | @rule rule assignment member =>
              refine ⟨1, step_runRoot (by simp [atomsReduce_rewrites]) ?_⟩
              show _ ∈ matchResults (contract (ruleSpace rules))
                (contract (atomAt depth (inst assignment rule.lhs)))
              rw [contract_ruleSpace, contract_atomAt]
              exact atomAt_mem_matchResults firstOrder bound (listed rule member) depth assignment
      | appFunction rest argument ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_runAppFunction (by simp [atomsReduce_rewrites])
            (atomAt depth argument) inner⟩
      | appArgument function rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_runAppArgument (by simp [atomsReduce_rewrites])
            (atomAt depth function) inner⟩
      | piDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_runPiDomain (by simp [atomsReduce_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | piBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_runPiBody (by simp [atomsReduce_rewrites])
            (atomAt depth domain) none inner⟩
      | lamDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_runLamDomain (by simp [atomsReduce_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | lamBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_runLamBody (by simp [atomsReduce_rewrites])
            (atomAt depth domain) none inner⟩

/-- **A run computes by beta and by the rules its space stores**: under the
matching evaluator, the steps of the candidate from the run of the atom of a
term in the space of a list of rules are the runs of the atoms of the steps
of the term, in a theory whose rules are those of the list and which has no
definition.  At every depth, and one step for one step. -/
theorem run_step_iff {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step matchingEvaluator atomsReduce (runPattern (ruleSpace rules) (atomAt depth source)) target ↔
      ∃ next, target = runPattern (ruleSpace rules) (atomAt depth next) ∧
        Dedukti.Step theory source next := by
  constructor
  · rintro ⟨fuel, step⟩
    exact run_stepAt_sound firstOrder bound (fun rule member => (rulesIff rule).mpr member) fuel step
  · rintro ⟨next, rfl, step⟩
    exact run_stepAt_complete firstOrder bound (fun rule member => (rulesIff rule).mp member)
      undefined step depth

#print axioms plain_stepAt_sound
#print axioms plain_stepAt_complete
#print axioms plain_step_iff
#print axioms run_stepAt_sound_of
#print axioms run_stepAt_sound
#print axioms run_stepAt_complete
#print axioms run_step_iff

end Mettapedia.Logic.HostingStyles.AtomsReduce
