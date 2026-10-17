import Mettapedia.Logic.HostingStyles.AmbientRegions.HeadedRoots
import Mettapedia.Logic.HostingStyles.LocatedAtoms.TwoSpaces

/-!
# With headed root steps: contained at every ambient space, under the unchanged evaluator

In `headedContained` no root step has a variable as left side.  Under the
evaluator of a region **without a guard**, which is weak
(`regionEvaluator_weak`):

* **No space and no name has a transition, at every stage**
  (`headed_space_static`, `headed_name_static`), under every evaluator: every
  rewrite is headed by a constructor of atoms (`headedContained_headedIn_atom`).
  A bound variable has no transition either (`headed_boundVariable_normal`).
* **Containment at every ambient space** (`headed_run_step_ambient_irrelevant`,
  `headed_run_termStep_ambient_irrelevant`): for every two ambient spaces the
  transitions of `run(space, atom)` are the same.  No hypothesis on the
  ambient spaces: no root step matches a run.
* **The run of the atom of a term computes by the rules of its space**
  (`headed_runAtom_step_iff`, `headed_runAtom_termStep_iff`), at every ambient
  space and for every list of first-order rules with bound right sides.
* **Nothing is lost for tables without a variable as a left side**
  (`headed_atom_step_iff`, `headed_hostOf_tabularAt`,
  `headed_hostOf_scopedTabularAt`).
* **What is lost** (`headed_variableRule_not_preserved`): a rule whose left
  side is a variable does not fire on a variable that a binder binds, because
  no left side matches a bound variable; in the contained presentation it
  fires (`contained_variableRule_preserved`).
* The ambient space that rewrites inside a run of the contained presentation
  without a guard does not here (`headed_ambient_stays_outside`).
* **Negative** (`headed_runRoot_unheaded`): the root step of a run keeps a
  variable as its subject, so the run of a bound variable steps where the
  bound variable does not.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.LanguageDef.LFTyping (subst0)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable rewritingTheory inst substitute inst_eq_substitute patternVars usesOnly
    withChoice chooseLeft chooseRight normal_of_normalTest)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule lamBodyRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings
open Mettapedia.Logic.HostingStyles.LocatedAtoms (takeAll takeAll_admitted)

variable {admits : Pattern → Bool}

/-! ## Only an atom has a transition, at every stage -/

/-- **Every rewrite of the presentation is headed by a constructor of
atoms.** -/
theorem headedContained_headedIn_atom : rewritesHeadedIn headedContained ["Atom"] = true := by
  decide

/-- **Negative**: the contained presentation has a rewrite with no head. -/
theorem contained_not_headedIn_atom : rewritesHeadedIn containedRun ["Atom"] = false := by
  decide

/-- **A term that has a transition is an atom**, under every evaluator. -/
theorem headed_atom_of_termStep {base : BasePremiseEvaluator} {interface : Contexts.Interface}
    {source target : Contexts.Term headedContained interface}
    (step : TermStep base headedContained source target) : interface.type = .base "Atom" := by
  obtain ⟨sort, listed, type⟩ := termStep_ofSorts headedContained_headedIn_atom step
  rw [List.mem_singleton.mp listed] at type
  exact type

/-- **No space has a transition**, at every stage and under every
evaluator. -/
theorem headed_space_static {base : BasePremiseEvaluator} {stage : List TypeExpr}
    (term next : Contexts.Term headedContained ⟨.base "Space", stage⟩) :
    ¬ TermStep base headedContained term next :=
  fun step => absurd (TypeExpr.base.inj (headed_atom_of_termStep step)) (by decide)

/-- **No name has a transition**, at every stage and under every
evaluator. -/
theorem headed_name_static {base : BasePremiseEvaluator} {stage : List TypeExpr}
    (term next : Contexts.Term headedContained ⟨.base "CandidateName", stage⟩) :
    ¬ TermStep base headedContained term next :=
  fun step => absurd (TypeExpr.base.inj (headed_atom_of_termStep step)) (by decide)

/-- Every left side of the presentation is an application. -/
theorem headedContained_left_apply : ∀ rule ∈ headedContained.rewrites,
    ∃ label parameters, rule.left = .apply label parameters := by
  intro rule member
  rw [headedContained_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl⟩

/-- **A bound variable has no step**, under every evaluator: no left side
matches it. -/
theorem headed_boundVariable_normal {base : BasePremiseEvaluator} (index : Nat) (target : Pattern) :
    ¬ Step base headedContained (.bvar index) target := by
  rintro ⟨fuel, step⟩
  cases fuel with
  | zero => cases step
  | succ fuel =>
      obtain ⟨rule, member, initial, final, matched, -, -⟩ := exists_rule_of_stepAt step
      obtain ⟨label, parameters, left⟩ := headedContained_left_apply rule member
      rw [left] at matched
      exact bvar_not_matched matched

/-! ## Containment at every ambient space -/

/-- **A step of a run at one ambient space is a step of that run at every
ambient space**: no derivation from a run asks the ambient space. -/
theorem headed_run_stepAt_ambient_irrelevant (first second : Pattern) :
    ∀ (fuel : Nat) {space subject target : Pattern},
      StepAt (regionEvaluator admits first) headedContained fuel (runPattern space subject)
          target →
        Step (regionEvaluator admits second) headedContained (runPattern space subject) target := by
  intro fuel
  induction fuel with
  | zero => intro space subject target step; cases step
  | succ fuel ih =>
      intro space subject target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rcases mem_headedContained_rewrites.mp member with plain | root | run
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
        rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "Pi") (by decide))
        · exact absurd matched (run_not_matched (label := "Pi") (by decide))
        · exact absurd matched (run_not_matched (label := "Lam") (by decide))
        · exact absurd matched (run_not_matched (label := "Lam") (by decide))
        · exact absurd matched (run_not_matched (label := "prime-drop") (by decide))
      · exact absurd matched (headedRoots_not_matched_run root)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at run
        rcases run with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨otherSpace, inner, answer, shape, found, applied⟩ :=
            regionRunRoot_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          rw [applied]
          exact ⟨1, step_regionRunRoot (by simp [headedContained_rewrites]) found⟩
        · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
            runAppFunction_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runAppFunction (by simp [headedContained_rewrites]) argument
            lifted⟩
        · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
            runAppArgument_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runAppArgument (by simp [headedContained_rewrites]) function
            lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runPiDomain_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runPiDomain (by simp [headedContained_rewrites]) body binder
            lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runPiBody_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runPiBody (by simp [headedContained_rewrites]) domain binder
            lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runLamDomain_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runLamDomain (by simp [headedContained_rewrites]) body binder
            lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
            runLamBody_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          rw [applied]
          obtain ⟨count, lifted⟩ := ih inner
          exact ⟨count + 1, step_runLamBody (by simp [headedContained_rewrites]) domain binder
            lifted⟩
        · obtain ⟨otherSpace, domain, binder, body, argument, shape, applied⟩ :=
            runBeta_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          rw [applied]
          exact ⟨1, step_runBeta (by simp [headedContained_rewrites]) _ domain body argument
            binder⟩
        · obtain ⟨otherSpace, atom, shape, applied⟩ := runRelease_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          rw [applied]
          exact ⟨1, step_runRelease (by simp [headedContained_rewrites]) _ atom⟩
        · obtain ⟨outer, inner, innerSubject, next, shape, innerStep, applied⟩ :=
            runBeneathRun_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
          rw [applied]
          obtain ⟨count, lifted⟩ := ih innerStep
          exact ⟨count + 1, step_runBeneathRun (by simp [headedContained_rewrites]) _ lifted⟩

/-- **Containment, on patterns: for every two ambient spaces a run has the
same steps.** -/
theorem headed_run_step_ambient_irrelevant (first second : Pattern)
    {space subject target : Pattern} :
    Step (regionEvaluator admits first) headedContained (runPattern space subject) target ↔
      Step (regionEvaluator admits second) headedContained (runPattern space subject) target := by
  constructor
  · rintro ⟨fuel, step⟩
    exact headed_run_stepAt_ambient_irrelevant first second fuel step
  · rintro ⟨fuel, step⟩
    exact headed_run_stepAt_ambient_irrelevant second first fuel step

/-- **Containment, on terms: for every two ambient spaces the transitions of
`run(space, atom)` are the same.** -/
theorem headed_run_termStep_ambient_irrelevant (first second : Pattern) {stage : List TypeExpr}
    (space : Contexts.Term headedContained ⟨.base "Space", stage⟩)
    (atom target : Contexts.Term headedContained ⟨.base "Atom", stage⟩) :
    TermStep (regionEvaluator admits first) headedContained
        (runTermIn headedContained_declaresRun space atom) target ↔
      TermStep (regionEvaluator admits second) headedContained
        (runTermIn headedContained_declaresRun space atom) target := by
  have move : ∀ one other : Pattern,
      TermStep (regionEvaluator admits one) headedContained
          (runTermIn headedContained_declaresRun space atom) target →
        TermStep (regionEvaluator admits other) headedContained
          (runTermIn headedContained_declaresRun space atom) target := by
    rintro one other ⟨redex, contractum, before, fired, after⟩
    obtain ⟨otherSpace, otherAtom, rfl, -, -⟩ :=
      eq_runTermIn_of_related headedContained_quoteDropOnly headedContained_quoteDropSorted
        headedContained_declaresRun before
    obtain ⟨fuel, bounded⟩ := fired
    exact ⟨_, contractum,
      termSetoid_base_irrelevant_in headedContained_quoteDropOnly headedContained_quoteDropSorted
        before,
      headed_run_stepAt_ambient_irrelevant one other fuel bounded,
      termSetoid_base_irrelevant_in headedContained_quoteDropOnly headedContained_quoteDropSorted
        after⟩
  exact ⟨move first second, move second first⟩

/-! ## The run of the atom of a term -/

/-- A step from the run of the atom of a term is the run of the atom of a
step of the term, in every theory whose steps at the root include what the
space of the run answers for the atoms of terms.  At every ambient space. -/
theorem headed_runAtom_stepAt_sound {space ambientSpace : Pattern} {theory : Theory}
    (answers : ∀ {depth : Nat} {term : LF.Term} {answer : Pattern},
      answer ∈ admittedAnswers admits space (atomAt depth term) →
        ∃ next, answer = atomAt depth next ∧ Dedukti.Step theory term next) :
    ∀ (fuel : Nat) {depth : Nat} {source : LF.Term} {target : Pattern},
      StepAt (regionEvaluator admits ambientSpace) headedContained fuel
          (runPattern space (atomAt depth source)) target →
        ∃ next, target = runPattern space (atomAt depth next) ∧
          Dedukti.Step theory source next := by
  intro fuel
  induction fuel with
  | zero => intro depth source target step; cases step
  | succ fuel ih =>
      intro depth source target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rcases mem_headedContained_rewrites.mp member with plain | root | run
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
        rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "App") (by decide))
        · exact absurd matched (run_not_matched (label := "Pi") (by decide))
        · exact absurd matched (run_not_matched (label := "Pi") (by decide))
        · exact absurd matched (run_not_matched (label := "Lam") (by decide))
        · exact absurd matched (run_not_matched (label := "Lam") (by decide))
        · exact absurd matched (run_not_matched (label := "prime-drop") (by decide))
      · exact absurd matched (headedRoots_not_matched_run root)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at run
        rcases run with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨otherSpace, subject, answer, shape, found, applied⟩ :=
            regionRunRoot_inv matched premises
          obtain ⟨rfl, rfl⟩ := runPattern_injective shape
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
        · obtain ⟨otherSpace, domain, binder, body, argument, shape, applied⟩ :=
            runBeta_inv matched premises
          obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
          obtain ⟨function, argumentTerm, rfl, functionEq, rfl⟩ := atomAt_eq_app subjectEq
          obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_lam functionEq.symm
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          exact ⟨subst0 argumentTerm bodyTerm, by rw [applied, instantiateBVar_atomAt],
            Dedukti.Step.root (.beta domainTerm bodyTerm argumentTerm)⟩
        · obtain ⟨otherSpace, atom, shape, applied⟩ := runRelease_inv matched premises
          obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
          exact absurd subjectEq (atomAt_ne_apply (label := "prime-drop") (by decide) depth source _)
        · obtain ⟨outer, inner, innerSubject, next, shape, innerStep, applied⟩ :=
            runBeneathRun_inv matched premises
          obtain ⟨rfl, subjectEq⟩ := runPattern_injective shape
          exact absurd subjectEq (atomAt_ne_apply (label := "prime-run") (by decide) depth source _)

/-- Every step of a term by the rules of a list is a step of the run of its
atom in the space of the list, at every ambient space. -/
theorem headed_runAtom_stepAt_complete (admitsAtoms : AdmitsAtoms admits)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (listed : ∀ rule, theory.rule rule → rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) (ambientSpace : Pattern) {source next : LF.Term}
    (step : Dedukti.Step theory source next) :
    ∀ depth : Nat, ∃ fuel, StepAt (regionEvaluator admits ambientSpace) headedContained fuel
      (runPattern (ruleSpace rules) (atomAt depth source))
      (runPattern (ruleSpace rules) (atomAt depth next)) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole =>
          intro depth
          cases root with
          | beta domain body argument =>
              have fired := step_runBeta (base := regionEvaluator admits ambientSpace)
                (lang := headedContained) (by simp [headedContained_rewrites]) (ruleSpace rules)
                (atomAt depth domain) (atomAt (depth + 1) body) (atomAt depth argument) none
              rw [instantiateBVar_atomAt] at fired
              exact ⟨1, fired⟩
          | delta defined =>
              rw [undefined] at defined
              cases defined
          | @rule rule assignment member =>
              refine ⟨1, step_regionRunRoot (by simp [headedContained_rewrites]) ?_⟩
              refine mem_admittedAnswers.mpr ⟨?_, ?_⟩
              · rw [contract_atomAt]
                exact admitsAtoms _ _
              · rw [contract_ruleSpace, contract_atomAt]
                exact atomAt_mem_matchResults firstOrder bound (listed rule member) depth assignment
      | appFunction rest argument ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_runAppFunction (by simp [headedContained_rewrites])
            (atomAt depth argument) inner⟩
      | appArgument function rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_runAppArgument (by simp [headedContained_rewrites])
            (atomAt depth function) inner⟩
      | piDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_runPiDomain (by simp [headedContained_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | piBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_runPiBody (by simp [headedContained_rewrites])
            (atomAt depth domain) none inner⟩
      | lamDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_runLamDomain (by simp [headedContained_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | lamBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_runLamBody (by simp [headedContained_rewrites])
            (atomAt depth domain) none inner⟩

/-- **The run of the atom of a term computes by the rules of its space, at
every ambient space**: its steps are the runs of the atoms of the steps of
the term by those rules.  For every list of first-order rules with bound
right sides and for every ambient space. -/
theorem headed_runAtom_step_iff (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits ambientSpace) headedContained
        (runPattern (ruleSpace rules) (atomAt depth source)) target ↔
      ∃ next, target = runPattern (ruleSpace rules) (atomAt depth next) ∧
        Dedukti.Step theory source next := by
  constructor
  · rintro ⟨fuel, step⟩
    refine headed_runAtom_stepAt_sound (fun found => ?_) fuel step
    have inSpace := (mem_admittedAnswers.mp found).2
    rw [contract_ruleSpace, contract_atomAt] at inSpace
    obtain ⟨rule, inRules, assignment, rfl, rfl⟩ :=
      exists_instance_of_mem_matchResults firstOrder bound inSpace
    exact ⟨_, rfl, Dedukti.Step.root (.rule assignment ((rulesIff rule).mpr inRules))⟩
  · rintro ⟨next, rfl, step⟩
    exact headed_runAtom_stepAt_complete admitsAtoms firstOrder bound
      (fun rule member => (rulesIff rule).mp member) undefined ambientSpace step depth

/-- **On terms.**  At every ambient space, the transitions of the run of the
atom of a term in the space of a list of rules are the runs of the atoms of
its steps by those rules. -/
theorem headed_runAtom_termStep_iff (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Contexts.Term headedContained (atomInterface depth)} :
    TermStep (regionEvaluator admits ambientSpace) headedContained
        (runAtomIn (presentation := headedPresentation) headedContained_declaresRun
          headedContained_carriesAtoms rules depth source) target ↔
      ∃ next, Dedukti.Step theory source next ∧
        target = runAtomIn (presentation := headedPresentation) headedContained_declaresRun
          headedContained_carriesAtoms rules depth next :=
  termStep_runAtomIn_iff (presentation := headedPresentation) headedContained_declaresRun
    headedContained_carriesAtoms headedContained_quoteDropOnly headedContained_quoteDropSorted
    headedContained_namesOnlyDropped
    (headed_runAtom_step_iff admitsAtoms ambientSpace firstOrder bound rulesIff undefined)

/-! ## Atoms outside a run: tables without a variable as a left side -/

/-- A step from the atom of a term is the atom of a step of the term, in
every theory whose steps at the root include what the ambient space answers
for the atoms of terms. -/
theorem headed_atom_stepAt_sound {ambientSpace : Pattern} {theory : Theory}
    (answers : ∀ {depth : Nat} {term : LF.Term} {answer : Pattern},
      answer ∈ admittedAnswers admits ambientSpace (atomAt depth term) →
        ∃ next, answer = atomAt depth next ∧ Dedukti.Step theory term next) :
    ∀ (fuel : Nat) {depth : Nat} {source : LF.Term} {target : Pattern},
      StepAt (regionEvaluator admits ambientSpace) headedContained fuel (atomAt depth source)
          target →
        ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next := by
  intro fuel
  induction fuel with
  | zero => intro depth source target step; cases step
  | succ fuel ih =>
      intro depth source target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rcases mem_headedContained_rewrites.mp member with plain | root | run
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
        rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨domain, binder, body, argument, shape, applied⟩ := beta_inv matched premises
          obtain ⟨function, argumentTerm, rfl, functionEq, rfl⟩ := atomAt_eq_app shape
          obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_lam functionEq.symm
          simp only [Pattern.lambda.injEq] at bodyEq
          obtain ⟨-, rfl⟩ := bodyEq
          exact ⟨subst0 argumentTerm bodyTerm, by rw [applied, instantiateBVar_atomAt],
            Dedukti.Step.root (.beta domainTerm bodyTerm argumentTerm)⟩
        · obtain ⟨function, argument, next, shape, inner, applied⟩ :=
            appFunction_inv matched premises
          obtain ⟨first, second, rfl, rfl, rfl⟩ := atomAt_eq_app shape
          obtain ⟨nextTerm, rfl, innerStep⟩ := ih inner
          exact ⟨.app nextTerm second, by rw [applied]; rfl,
            innerStep.plug (.appFunction .hole second)⟩
        · obtain ⟨function, argument, next, shape, inner, applied⟩ :=
            appArgument_inv matched premises
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
        · obtain ⟨domain, binder, body, next, shape, inner, applied⟩ :=
            lamDomain_inv matched premises
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
      · obtain ⟨name, label, parameters, rfl, exact, -⟩ := headedRoots_shape rule root
        obtain ⟨answer, found, applied⟩ := headedRoot_inv exact matched premises
        obtain ⟨nextTerm, rfl, rootStep⟩ := answers found
        exact ⟨nextTerm, applied, rootStep⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at run
        rcases run with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact absurd matched (atomAt_not_matched (label := "prime-run") (by decide))

/-- **The atom of a term that is no bound variable has a root step to each
answer of the ambient space**, in every language with the eight root steps:
the root step of its head. -/
theorem step_headedRoot_atomAt {lang : LanguageDef} {ambientSpace : Pattern}
    (roots : ∀ rule ∈ headedRoots, rule ∈ lang.rewrites) {depth : Nat} {term : LF.Term}
    (notBound : ∀ index : Nat, atomAt depth term ≠ .bvar index) {answer : Pattern}
    (found : answer ∈ admittedAnswers admits ambientSpace (atomAt depth term)) :
    StepAt (regionEvaluator admits ambientSpace) lang 1 (atomAt depth term) answer := by
  cases term with
  | var index =>
      by_cases below : index < depth
      · exact absurd (atomAt_var_of_lt below) (notBound index)
      · rw [atomAt_var_of_le (Nat.le_of_not_lt below)] at found ⊢
        exact step_headedRoot (name := "RootVariable") (left := .apply "prime-variable" [.fvar "I"])
          (roots _ (by simp [headedRoots])) (initial := [("I", numeral (index - depth))])
          (by simp [variableAtom, matchPattern, matchArgs, mergeBindings])
          (by simp [variableAtom, applyBindings]) found
  | srt sort =>
      rw [atomAt_srt] at found ⊢
      exact step_headedRoot (name := "RootSymbol") (left := .apply "prime-symbol" [.fvar "I"])
        (roots _ (by simp [headedRoots])) (initial := [("I", numeral (sortCode sort))])
        (by simp [symbolAtom, matchPattern, matchArgs, mergeBindings])
        (by simp [symbolAtom, applyBindings]) found
  | con name =>
      exact step_headedRoot (name := "RootSymbol") (left := .apply "prime-symbol" [.fvar "I"])
        (roots _ (by simp [headedRoots])) (initial := [("I", numeral (nameCode name + 2))])
        (by simp [atomAt, symbolAtom, matchPattern, matchArgs, mergeBindings])
        (by simp [atomAt, symbolAtom, applyBindings]) found
  | app function argument =>
      exact step_headedRoot (name := "RootApp") (left := .apply "App" [.fvar "F", .fvar "X"])
        (roots _ (by simp [headedRoots]))
        (initial := [("X", atomAt depth argument), ("F", atomAt depth function)])
        (by simp [atomAt, matchPattern, matchArgs, mergeBindings])
        (by simp [atomAt, applyBindings]) found
  | lam domain body =>
      exact step_headedRoot (name := "RootLam") (left := .apply "Lam" [.fvar "A", .fvar "M"])
        (roots _ (by simp [headedRoots]))
        (initial := [("M", .lambda none (atomAt (depth + 1) body)), ("A", atomAt depth domain)])
        (by simp [atomAt, matchPattern, matchArgs, mergeBindings])
        (by simp [atomAt, applyBindings]) found
  | pi domain body =>
      exact step_headedRoot (name := "RootPi") (left := .apply "Pi" [.fvar "A", .fvar "M"])
        (roots _ (by simp [headedRoots]))
        (initial := [("M", .lambda none (atomAt (depth + 1) body)), ("A", atomAt depth domain)])
        (by simp [atomAt, matchPattern, matchArgs, mergeBindings])
        (by simp [atomAt, applyBindings]) found

/-- An instance of a side without binder that is no variable is no bound
variable. -/
theorem atomAt_inst_ne_bvar {side : LF.Term} (free : Dedukti.binderFree side = true)
    (headed : ∀ index : Nat, side ≠ .var index) (assignment : Nat → LF.Term) (depth index : Nat) :
    atomAt depth (inst assignment side) ≠ .bvar index := by
  rw [inst_eq_substitute assignment free]
  cases side with
  | var other => exact absurd rfl (headed other)
  | srt sort =>
      show atomAt depth (.srt sort) ≠ _
      rw [atomAt_srt]
      simp [symbolAtom]
  | con name =>
      show atomAt depth (.con name) ≠ _
      simp [atomAt, symbolAtom]
  | app function argument =>
      show atomAt depth (.app (substitute assignment function) (substitute assignment argument)) ≠ _
      simp [atomAt]
  | lam domain body => simp [Dedukti.binderFree] at free
  | pi domain body => simp [Dedukti.binderFree] at free

/-- Every step of a term, by the rules of a list none of whose left sides is
a variable, is a step between the atoms. -/
theorem headed_atom_stepAt_complete (admitsAtoms : AdmitsAtoms admits)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index)
    {theory : Theory} (listed : ∀ rule, theory.rule rule → rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {source next : LF.Term}
    (step : Dedukti.Step theory source next) :
    ∀ depth : Nat, ∃ fuel, StepAt (regionEvaluator admits (ruleSpace rules)) headedContained fuel
      (atomAt depth source) (atomAt depth next) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole =>
          intro depth
          cases root with
          | beta domain body argument =>
              have fired := step_beta (base := regionEvaluator admits (ruleSpace rules))
                (lang := headedContained) (by simp [headedContained_rewrites])
                (atomAt depth domain) (atomAt (depth + 1) body) (atomAt depth argument) none
              rw [instantiateBVar_atomAt] at fired
              exact ⟨1, fired⟩
          | delta defined =>
              rw [undefined] at defined
              cases defined
          | @rule rule assignment member =>
              refine ⟨1, step_headedRoot_atomAt
                (fun other inRoots => mem_headedContained_rewrites.mpr (.inr (.inl inRoots)))
                (atomAt_inst_ne_bvar (firstOrder rule (listed rule member)).1
                  (headed rule (listed rule member)) assignment depth) ?_⟩
              refine mem_admittedAnswers.mpr ⟨?_, ?_⟩
              · rw [contract_atomAt]
                exact admitsAtoms _ _
              · rw [contract_ruleSpace, contract_atomAt]
                exact atomAt_mem_matchResults firstOrder bound (listed rule member) depth assignment
      | appFunction rest argument ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appFunction (by simp [headedContained_rewrites])
            (atomAt depth argument) inner⟩
      | appArgument function rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_appArgument (by simp [headedContained_rewrites])
            (atomAt depth function) inner⟩
      | piDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_piDomain (by simp [headedContained_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | piBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_piBody (by simp [headedContained_rewrites])
            (atomAt depth domain) none inner⟩
      | lamDomain rest body ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih depth
          exact ⟨fuel + 1, step_lamDomain (by simp [headedContained_rewrites])
            (atomAt (depth + 1) body) none inner⟩
      | lamBody domain rest ih =>
          intro depth
          obtain ⟨fuel, inner⟩ := ih (depth + 1)
          exact ⟨fuel + 1, step_lamBody (by simp [headedContained_rewrites])
            (atomAt depth domain) none inner⟩

/-- **Outside a run the presentation computes, on the atom of a term, by beta
and by the rules that the ambient space stores**, for a list of rules none of
whose left sides is a variable. -/
theorem headed_atom_step_iff (admitsAtoms : AdmitsAtoms admits)
    {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits (ruleSpace rules)) headedContained (atomAt depth source) target ↔
      ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next := by
  constructor
  · rintro ⟨fuel, step⟩
    refine headed_atom_stepAt_sound (fun found => ?_) fuel step
    have inSpace := (mem_admittedAnswers.mp found).2
    rw [contract_ruleSpace, contract_atomAt] at inSpace
    obtain ⟨rule, inRules, assignment, rfl, rfl⟩ :=
      exists_instance_of_mem_matchResults firstOrder bound inSpace
    exact ⟨_, rfl, Dedukti.Step.root (.rule assignment ((rulesIff rule).mpr inRules))⟩
  · rintro ⟨next, rfl, step⟩
    exact headed_atom_stepAt_complete admitsAtoms firstOrder bound headed
      (fun rule member => (rulesIff rule).mp member) undefined step depth

variable {declared : Contexts.Interface → Prop}

/-- **On terms: at the space of a table of first-order rules with bound right
sides none of whose left sides is a variable, the presentation is a host of
the theories given by that table.** -/
theorem headed_hostOf_tabularAt (admitsAtoms : AdmitsAtoms admits) {table : RuleTable}
    (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index) :
    HostOf (headedTheory admits (tableSpace table).1)
      (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
      .terms .hosting := by
  rintro reading ⟨source, ⟨theory, tabular, rfl⟩, interface, rfl⟩
  exact ⟨termsMapIn theory _ headedContained_carriesAtoms,
    termsMapIn_hosting headedContained_carriesAtoms headedContained_quoteDropOnly
      headedContained_quoteDropSorted headedContained_namesOnlyDropped
      (headed_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
        (fun rule member => headed rule (Finset.mem_toList.mp member))
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)⟩

/-- **With contexts: a reading of the presentation, at the space of such a
table, in which the holes of atoms are free is a host, with all contexts, of
the theories given by the table** on the terms with free variables below a
width, for every width. -/
theorem headed_hostOf_scopedTabularAt (admitsAtoms : AdmitsAtoms admits) {table : RuleTable}
    (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index) (free : AtomsFree declared) :
    HostOf ((headedTheory admits (tableSpace table).1).regionReading declared)
      (fun source => ∃ (theory : Theory) (width : Nat),
        theory.Tabular table ∧ source = scopedRewriting width theory)
      .contexts .hosting := by
  rintro reading ⟨theory, width, tabular, rfl⟩
  exact ⟨scopedMapIn theory _ headedContained_carriesAtoms free width,
    scopedMapIn_hosting headedContained_carriesAtoms headedContained_quoteDropOnly
      headedContained_quoteDropSorted headedContained_namesOnlyDropped
      (headed_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
        (fun rule member => headed rule (Finset.mem_toList.mp member))
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)
      (fun sourceStep _ within => wellScoped_of_listStep admitted.listed.1 admitted.listed.2
        (fun rule member => ((tabular.rules rule).trans Finset.mem_toList.symm).mp member)
        tabular.undefined sourceStep within)
      free width⟩

/-! ## What is lost, and what the unchanged evaluator now gives -/

/-- `x ⟶ u` sends the variable to the constant, in the theory of the rule. -/
theorem takeAll_step : Dedukti.Step (Theory.ofTable {takeAll}) (.var 0) (.con "u") := by
  have root := Dedukti.RootStep.rule (theory := Theory.ofTable {takeAll}) (rule := takeAll)
    (fun _ => .var 0) (Finset.mem_singleton_self _)
  simpa [takeAll, Dedukti.inst, Dedukti.instantiate, Dedukti.lift_zero] using Dedukti.Step.root root

/-- **What is lost: a rule whose left side is a variable does not fire on a
variable that a binder binds.**  The theory of the rule `x ⟶ u` contracts the
variable; its atom beneath one binder is a bound variable, and has no step at
any ambient space. -/
theorem headed_variableRule_not_preserved :
    Dedukti.Step (Theory.ofTable {takeAll}) (.var 0) (.con "u") ∧
      ∀ (base : BasePremiseEvaluator) (target : Pattern),
        ¬ Step base headedContained (atomAt 1 (.var 0)) target :=
  ⟨takeAll_step, fun _ target => headed_boundVariable_normal 0 target⟩

/-- **In the contained presentation that step is there**: its root step has
a variable as left side. -/
theorem contained_variableRule_preserved (admitsAtoms : AdmitsAtoms admits) :
    Step (regionEvaluator admits (ruleSpace [takeAll])) containedRun (atomAt 1 (.var 0))
      (atomAt 1 (.con "u")) :=
  (contained_atom_step_iff admitsAtoms takeAll_admitted.1 takeAll_admitted.2
    (theory := Theory.ofTable {takeAll})
    (fun rule => by
      show rule ∈ ({takeAll} : Finset Dedukti.RewriteRule) ↔ rule ∈ [takeAll]
      simp)
    (fun _ => rfl)).mpr ⟨_, rfl, takeAll_step⟩

/-- **Negative: the root step of a run still has a variable as its subject.**
In the space of the rule `x ⟶ u` the run of a bound variable steps, at every
ambient space, and the bound variable by itself has no step: the steps of a
run are the runs of the steps of its subject at its space only for subjects
that a headed root step matches.  The eight root steps replace the ambient
root step, and not the root step of a run. -/
theorem headed_runRoot_unheaded (ambientSpace : Pattern) :
    Step (regionEvaluator anySubject ambientSpace) headedContained
        (runPattern (ruleSpace [takeAll]) (atomAt 1 (.var 0)))
        (runPattern (ruleSpace [takeAll]) (atomAt 1 (.con "u"))) ∧
      atomAt 1 (.var 0) = .bvar 0 ∧
        ∀ (base : BasePremiseEvaluator) (target : Pattern),
          ¬ Step base headedContained (atomAt 1 (.var 0)) target :=
  ⟨(headed_runAtom_step_iff anySubject_admitsAtoms ambientSpace takeAll_admitted.1
      takeAll_admitted.2 (theory := Theory.ofTable {takeAll})
      (fun rule => by
        show rule ∈ ({takeAll} : Finset Dedukti.RewriteRule) ↔ rule ∈ [takeAll]
        simp)
      (fun _ => rfl)).mpr ⟨_, rfl, takeAll_step⟩,
    rfl, fun _ target => headed_boundVariable_normal 0 target⟩

/-- **The ambient space that rewrites inside a run of the contained
presentation without a guard does not here**: at that ambient space, and
without a guard, the run in the empty space of the application of the sort of
types to itself has no step. -/
theorem headed_ambient_stays_outside (target : Pattern) :
    ¬ Step (regionEvaluator anySubject runEquationSpace.1) headedContained
      (runPattern (ruleSpace []) (atomAt 0 (.app (.srt .type) (.srt .type)))) target := by
  intro step
  obtain ⟨next, -, sourceStep⟩ := (headed_runAtom_step_iff anySubject_admitsAtoms
    runEquationSpace.1 (rules := []) noRules_admitted.1 noRules_admitted.2 (theory := Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-- **Positive**: the run of `choose heads tails` in the space of the two
rules of choice steps, at every ambient space and without a guard. -/
theorem headed_runCoin_steps (ambientSpace : Pattern) :
    Step (regionEvaluator anySubject ambientSpace) headedContained
      (runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 coin))
      (runPattern (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 (.con "heads"))) :=
  (headed_runAtom_step_iff anySubject_admitsAtoms ambientSpace choiceRules_admitted.1
    choiceRules_admitted.2 withChoice_rules (fun _ => rfl)).mpr
    ⟨_, rfl, Dedukti.step_choose_left Theory.empty _ _⟩

/-- **A weak evaluator, containment between ambient spaces and static spaces
together, under the unchanged evaluator.**  Without a guard the evaluator
answers the queries of the eight root steps and the premise of the root step
of a run by one function that answers by stored rules; for every two ambient
spaces a run has the same steps; and no space and no name has a transition,
at every stage. -/
theorem headed_weak_contained_static :
    (∀ (ambientSpace : Pattern) (lang : LanguageDef) (bindings : Bindings) (subject : Pattern),
        regionEvaluator anySubject ambientSpace lang bindings
            (.relationQuery "AmbientStep" [subject, .fvar "answer"]) =
          (admittedAnswers anySubject ambientSpace (applyBindings bindings subject)).map
            fun result => ("answer", result) :: bindings) ∧
      (∀ ambientSpace : Pattern, AuthoredEvaluators.AnswersRunBy
        (regionEvaluator anySubject ambientSpace) (admittedAnswers anySubject)) ∧
      AuthoredEvaluators.AnswersByStoredRules (admittedAnswers anySubject) ∧
      (∀ (first second space subject target : Pattern),
        Step (regionEvaluator anySubject first) headedContained (runPattern space subject)
            target ↔
          Step (regionEvaluator anySubject second) headedContained (runPattern space subject)
            target) ∧
      (∀ (ambientSpace : Pattern) (stage : List TypeExpr)
          (term next : Contexts.Term headedContained ⟨.base "Space", stage⟩),
        ¬ TermStep (regionEvaluator anySubject ambientSpace) headedContained term next) ∧
      ∀ (ambientSpace : Pattern) (stage : List TypeExpr)
        (term next : Contexts.Term headedContained ⟨.base "CandidateName", stage⟩),
        ¬ TermStep (regionEvaluator anySubject ambientSpace) headedContained term next :=
  ⟨regionEvaluator_ambientQuery anySubject, regionEvaluator_answersRunBy anySubject,
    admittedAnswers_any_answersByStoredRules,
    fun first second _ _ _ => headed_run_step_ambient_irrelevant first second,
    fun _ _ term next => headed_space_static term next,
    fun _ _ term next => headed_name_static term next⟩

#print axioms headedContained_headedIn_atom
#print axioms headed_space_static
#print axioms headed_name_static
#print axioms headed_boundVariable_normal
#print axioms headed_run_stepAt_ambient_irrelevant
#print axioms headed_run_step_ambient_irrelevant
#print axioms headed_run_termStep_ambient_irrelevant
#print axioms headed_runAtom_step_iff
#print axioms headed_runAtom_termStep_iff
#print axioms headed_atom_stepAt_sound
#print axioms step_headedRoot_atomAt
#print axioms headed_atom_step_iff
#print axioms headed_hostOf_tabularAt
#print axioms headed_hostOf_scopedTabularAt
#print axioms headed_variableRule_not_preserved
#print axioms contained_variableRule_preserved
#print axioms headed_runRoot_unheaded
#print axioms headed_ambient_stays_outside
#print axioms headed_runCoin_steps
#print axioms headed_weak_contained_static
#print axioms contained_not_headedIn_atom
#print axioms headed_atom_of_termStep
#print axioms headedContained_left_apply
#print axioms headed_runAtom_stepAt_sound
#print axioms headed_runAtom_stepAt_complete
#print axioms atomAt_inst_ne_bvar
#print axioms headed_atom_stepAt_complete
#print axioms takeAll_step

end Mettapedia.Logic.HostingStyles.AmbientRegions
