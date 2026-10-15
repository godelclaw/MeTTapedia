import Mettapedia.Logic.HostingStyles.AmbientRegions.RunTerms
import Mettapedia.Logic.HostingStyles.AmbientSpace.RootSubject

/-!
# Containment: in the contained presentation a run steps by its own space

The steps of `run(space, atom)` in the contained presentation are compared at
two ambient spaces, and with the steps of `atom` in the member at `space`.

## What the ambient root step can do to a run

The left side of the ambient root step is a variable, and a run is an atom:
the ambient space is asked for a run as for every other pattern.  So
containment is a statement about ambient spaces that **answer nothing for a
run** (`RunSilent`):

* under a guard that admits no run, every space (`runSilent_of_refuses`,
  `runSilent_notRun`, `runSilent_atomNotRun`);
* under every guard, the empty space and the space of a list of rules none of
  whose left sides is a variable (`runSilent_emptySpace`,
  `runSilent_ruleSpace`);
* **not** the space of the rule `x ⟶ x` without a guard
  (`identity_not_runSilent`).

## Containment

* **The steps of a run do not consult such an ambient space**
  (`contained_run_step_ambient_irrelevant`): at two ambient spaces that answer
  nothing for a run, `run(space, atom)` has the same steps.
* **They are the runs of the steps of the atom in the member at the space of
  the run** (`contained_run_step_iff`): the run constructor puts the member at
  `space` inside every other member.  The direction from the member to the
  run holds at every ambient space (`contained_run_of_step`).
* On terms: `contained_run_termStep_ambient_irrelevant`,
  `contained_run_termStep_iff`.

## Without a guard the contained presentation is not contained

* At the space of the rule `x ⟶ x` a run has a transition that it does not
  have at the empty space (`anySubject_run_depends_on_ambient`).
* An ambient space that stores an equation between two runs rewrites strictly
  inside a run (`anySubject_ambient_reaches_inside`): the step is the run of
  no step of the subject at the space of the run.

So the plain matching evaluator gives containment between the ambient spaces
that answer nothing for a run, and not beyond them; the guard `notRun` gives
it at every ambient space.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory patternVars usesOnly normal_of_normalTest)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule lamBodyRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

variable {admits : Pattern → Bool}

/-! ## Spaces that answer nothing for a run -/

/-- **A space answers nothing for a run**, under a guard: whatever the space
and the subject of the run are. -/
def RunSilent (admits : Pattern → Bool) (space : Pattern) : Prop :=
  ∀ runSpace subject : Pattern, admittedAnswers admits space (runPattern runSpace subject) = []

/-- **Positive**: under a guard that admits no run, every space. -/
theorem runSilent_of_refuses
    (refuses : ∀ space subject : Pattern, admits (runPattern space subject) = false)
    (space : Pattern) : RunSilent admits space := by
  intro runSpace subject
  exact admittedAnswers_of_not_admitted (by rw [contract_runPattern']; exact refuses _ _) space

/-- Under the guard that admits what is no run, every space. -/
theorem runSilent_notRun (space : Pattern) : RunSilent notRun space :=
  runSilent_of_refuses notRun_run space

/-- Under the guard that admits an atom that is no run, every space. -/
theorem runSilent_atomNotRun (space : Pattern) : RunSilent atomNotRun space :=
  runSilent_of_refuses atomNotRun_run space

/-- **Positive**: the empty space, under every guard. -/
theorem runSilent_emptySpace (admits : Pattern → Bool) : RunSilent admits emptySpace := by
  intro runSpace subject
  unfold admittedAnswers
  split_ifs
  · rw [show contract emptySpace = emptySpace by decide]
    exact matchResults_emptySpace _
  · rfl

/-- **Positive**: the space of a list of first-order rules none of whose left
sides is a variable, under every guard. -/
theorem runSilent_ruleSpace (admits : Pattern → Bool) {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index) :
    RunSilent admits (ruleSpace rules) := by
  intro runSpace subject
  unfold admittedAnswers
  split_ifs
  · rw [contract_ruleSpace, contract_runPattern']
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro answer found
    obtain ⟨rule, member, bindings, matched, -⟩ := (mem_matchResults_ruleSpace firstOrder).mp found
    cases left : rule.lhs with
    | var index => exact headed rule member index left
    | srt sort =>
        rw [left, ruleSide_srt] at matched
        exact apply_not_matched (label := "prime-symbol") (other := "prime-run") (by decide) matched
    | con name =>
        rw [left, ruleSide_con] at matched
        exact apply_not_matched (label := "prime-symbol") (other := "prime-run") (by decide) matched
    | app function argument =>
        rw [left, ruleSide_app] at matched
        exact apply_not_matched (label := "App") (other := "prime-run") (by decide) matched
    | lam domain body =>
        have free := (firstOrder rule member).1
        rw [left] at free
        simp [Dedukti.binderFree] at free
    | pi domain body =>
        have free := (firstOrder rule member).1
        rw [left] at free
        simp [Dedukti.binderFree] at free
  · rfl

/-- **Negative**: without a guard the space of the rule `x ⟶ x` answers for
a run. -/
theorem identity_not_runSilent : ¬ RunSilent anySubject (ruleSpace [identityRule]) := by
  intro silent
  have none := silent emptySpace unitAtom
  have found := identity_answers (contract (runPattern emptySpace unitAtom))
  rw [admittedAnswers_any, contract_ruleSpace] at none
  rw [none] at found
  cases found

/-- A space is read up to the static equivalence. -/
theorem RunSilent.congr {first second : Pattern} (same : contract first = contract second)
    (silent : RunSilent admits first) : RunSilent admits second := by
  intro runSpace subject
  rw [← admittedAnswers_congr admits same rfl]
  exact silent runSpace subject

/-! ## The steps of a run do not consult the ambient space -/

/-- **A step of a run at an ambient space that answers nothing for a run is a
step of that run at every ambient space.** -/
theorem contained_run_stepAt_of_silent {first : Pattern} (silent : RunSilent admits first)
    (second : Pattern) :
    ∀ (fuel : Nat) {space subject target : Pattern},
      StepAt (regionEvaluator admits first) containedRun fuel (runPattern space subject) target →
        Step (regionEvaluator admits second) containedRun (runPattern space subject) target := by
  intro fuel
  induction fuel with
  | zero => intro space subject target step; cases step
  | succ fuel ih =>
      intro space subject target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [contained_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "Pi") (by decide))
      · exact absurd matched (run_not_matched (label := "Pi") (by decide))
      · exact absurd matched (run_not_matched (label := "Lam") (by decide))
      · exact absurd matched (run_not_matched (label := "Lam") (by decide))
      · exact absurd matched (run_not_matched (label := "prime-drop") (by decide))
      · obtain ⟨answer, found, -⟩ := ambientRoot_inv matched premises
        rw [silent space subject] at found
        cases found
      · obtain ⟨otherSpace, inner, answer, shape, found, applied⟩ :=
          regionRunRoot_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        rw [applied]
        exact ⟨1, step_regionRunRoot (by simp [contained_rewrites]) found⟩
      · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
          runAppFunction_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runAppFunction (by simp [contained_rewrites]) argument lifted⟩
      · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
          runAppArgument_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runAppArgument (by simp [contained_rewrites]) function lifted⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runPiDomain_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runPiDomain (by simp [contained_rewrites]) body binder lifted⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runPiBody_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runPiBody (by simp [contained_rewrites]) domain binder lifted⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runLamDomain_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runLamDomain (by simp [contained_rewrites]) body binder lifted⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runLamBody_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runLamBody (by simp [contained_rewrites]) domain binder lifted⟩
      · obtain ⟨otherSpace, domain, binder, body, argument, shape, applied⟩ :=
          runBeta_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        rw [applied]
        exact ⟨1, step_runBeta (by simp [contained_rewrites]) _ domain body argument binder⟩
      · obtain ⟨otherSpace, atom, shape, applied⟩ := runRelease_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        rw [applied]
        exact ⟨1, step_runRelease (by simp [contained_rewrites]) _ atom⟩
      · obtain ⟨outer, inner, innerSubject, next, shape, innerStep, applied⟩ :=
          runBeneathRun_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        rw [applied]
        obtain ⟨count, lifted⟩ := ih innerStep
        exact ⟨count + 1, step_runBeneathRun (by simp [contained_rewrites]) _ lifted⟩

/-- **For two ambient spaces that answer nothing for a run, a run has the
same steps.** -/
theorem contained_run_step_ambient_irrelevant {first second : Pattern}
    (silentFirst : RunSilent admits first) (silentSecond : RunSilent admits second)
    {space subject target : Pattern} :
    Step (regionEvaluator admits first) containedRun (runPattern space subject) target ↔
      Step (regionEvaluator admits second) containedRun (runPattern space subject) target := by
  constructor
  · rintro ⟨fuel, step⟩
    exact contained_run_stepAt_of_silent silentFirst second fuel step
  · rintro ⟨fuel, step⟩
    exact contained_run_stepAt_of_silent silentSecond first fuel step

/-! ## A step of a run is the run of a step of its subject at its space -/

/-- **A step of a run, at an ambient space that answers nothing for a run, is
the run of a step of its subject in the member at the space of the run.** -/
theorem contained_run_stepAt_inv {ambientSpace : Pattern} (silent : RunSilent admits ambientSpace) :
    ∀ (fuel : Nat) {space subject target : Pattern},
      StepAt (regionEvaluator admits ambientSpace) containedRun fuel (runPattern space subject)
          target →
        ∃ next, target = runPattern space next ∧
          Step (regionEvaluator admits space) containedRun subject next := by
  intro fuel
  induction fuel with
  | zero => intro space subject target step; cases step
  | succ fuel ih =>
      intro space subject target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [contained_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "Pi") (by decide))
      · exact absurd matched (run_not_matched (label := "Pi") (by decide))
      · exact absurd matched (run_not_matched (label := "Lam") (by decide))
      · exact absurd matched (run_not_matched (label := "Lam") (by decide))
      · exact absurd matched (run_not_matched (label := "prime-drop") (by decide))
      · obtain ⟨answer, found, -⟩ := ambientRoot_inv matched premises
        rw [silent space subject] at found
        cases found
      · obtain ⟨otherSpace, inner, answer, shape, found, applied⟩ :=
          regionRunRoot_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        exact ⟨answer, applied, ⟨1, step_ambientRoot (by simp [contained_rewrites]) found⟩⟩
      · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
          runAppFunction_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨reached, same, ⟨count, lifted⟩⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        exact ⟨_, applied, ⟨count + 1, step_appFunction (by simp [contained_rewrites]) argument
          lifted⟩⟩
      · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
          runAppArgument_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨reached, same, ⟨count, lifted⟩⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        exact ⟨_, applied, ⟨count + 1, step_appArgument (by simp [contained_rewrites]) function
          lifted⟩⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runPiDomain_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨reached, same, ⟨count, lifted⟩⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        exact ⟨_, applied, ⟨count + 1, step_piDomain (by simp [contained_rewrites]) body binder
          lifted⟩⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runPiBody_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨reached, same, ⟨count, lifted⟩⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        exact ⟨_, applied, ⟨count + 1, step_piBody (by simp [contained_rewrites]) domain binder
          lifted⟩⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runLamDomain_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨reached, same, ⟨count, lifted⟩⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        exact ⟨_, applied, ⟨count + 1, step_lamDomain (by simp [contained_rewrites]) body binder
          lifted⟩⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runLamBody_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨reached, same, ⟨count, lifted⟩⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        exact ⟨_, applied, ⟨count + 1, step_lamBody (by simp [contained_rewrites]) domain binder
          lifted⟩⟩
      · obtain ⟨otherSpace, domain, binder, body, argument, shape, applied⟩ :=
          runBeta_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        exact ⟨_, applied, ⟨1, step_beta (by simp [contained_rewrites]) domain body argument
          binder⟩⟩
      · obtain ⟨otherSpace, atom, shape, applied⟩ := runRelease_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        exact ⟨_, applied, ⟨1, step_release (by simp [contained_rewrites]) atom⟩⟩
      · obtain ⟨outer, inner, innerSubject, next, shape, innerStep, applied⟩ :=
          runBeneathRun_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        exact ⟨_, applied, contained_run_stepAt_of_silent silent _ fuel innerStep⟩

/-- A step of a run beneath a run in a space that answers nothing for a run,
at every ambient space. -/
theorem contained_run_of_run_stepAt {space : Pattern} (silent : RunSilent admits space)
    (ambientSpace : Pattern) {fuel : Nat} {inner innerSubject target : Pattern}
    (step : StepAt (regionEvaluator admits space) containedRun fuel
      (runPattern inner innerSubject) target) :
    Step (regionEvaluator admits ambientSpace) containedRun
      (runPattern space (runPattern inner innerSubject)) (runPattern space target) := by
  obtain ⟨next, rfl, -⟩ := contained_run_stepAt_inv silent fuel step
  obtain ⟨count, lifted⟩ := contained_run_stepAt_of_silent silent ambientSpace fuel step
  exact ⟨count + 1, step_runBeneathRun (by simp [contained_rewrites]) space lifted⟩

/-- **A step of a pattern in the member at a space is a step of its run in
that space, at every ambient space**, when the pattern has no run or the
space answers nothing for a run. -/
theorem contained_run_of_stepAt {space : Pattern} (ambientSpace : Pattern) :
    ∀ (fuel : Nat) {subject next : Pattern},
      tokens runLabel subject = 0 ∨ RunSilent admits space →
        StepAt (regionEvaluator admits space) containedRun fuel subject next →
          Step (regionEvaluator admits ambientSpace) containedRun (runPattern space subject)
            (runPattern space next) := by
  intro fuel
  induction fuel with
  | zero => intro subject next _ step; cases step
  | succ fuel ih =>
      intro subject next side step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [contained_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
        rw [applied]
        exact ⟨1, step_runBeta (by simp [contained_rewrites]) space domain body argument binder⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appFunction_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih
          (side.imp (fun clean => (tokens_apply_eq_zero_iff.mp clean).2 function (by simp)) id) inner
        exact ⟨count + 1, step_runAppFunction (by simp [contained_rewrites]) argument lifted⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appArgument_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih
          (side.imp (fun clean => (tokens_apply_eq_zero_iff.mp clean).2 argument (by simp)) id) inner
        exact ⟨count + 1, step_runAppArgument (by simp [contained_rewrites]) function lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piDomain_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih
          (side.imp (fun clean => (tokens_apply_eq_zero_iff.mp clean).2 domain (by simp)) id) inner
        exact ⟨count + 1, step_runPiDomain (by simp [contained_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piBody_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih
          (side.imp (fun clean => by
            have abstraction := (tokens_apply_eq_zero_iff.mp clean).2 (.lambda binder body) (by simp)
            rwa [tokens] at abstraction) id) inner
        exact ⟨count + 1, step_runPiBody (by simp [contained_rewrites]) domain binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamDomain_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih
          (side.imp (fun clean => (tokens_apply_eq_zero_iff.mp clean).2 domain (by simp)) id) inner
        exact ⟨count + 1, step_runLamDomain (by simp [contained_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamBody_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih
          (side.imp (fun clean => by
            have abstraction := (tokens_apply_eq_zero_iff.mp clean).2 (.lambda binder body) (by simp)
            rwa [tokens] at abstraction) id) inner
        exact ⟨count + 1, step_runLamBody (by simp [contained_rewrites]) domain binder lifted⟩
      · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
        rw [applied]
        exact ⟨1, step_runRelease (by simp [contained_rewrites]) space atom⟩
      · obtain ⟨answer, found, applied⟩ := ambientRoot_inv matched premises
        rw [applied]
        exact ⟨1, step_regionRunRoot (by simp [contained_rewrites]) found⟩
      · obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact contained_run_of_run_stepAt (side.resolve_left (run_not_runFree _ _)) ambientSpace
          step
      · obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact contained_run_of_run_stepAt (side.resolve_left (run_not_runFree _ _)) ambientSpace
          step
      · obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact contained_run_of_run_stepAt (side.resolve_left (run_not_runFree _ _)) ambientSpace
          step
      · obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact contained_run_of_run_stepAt (side.resolve_left (run_not_runFree _ _)) ambientSpace
          step
      · obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact contained_run_of_run_stepAt (side.resolve_left (run_not_runFree _ _)) ambientSpace
          step
      · obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact contained_run_of_run_stepAt (side.resolve_left (run_not_runFree _ _)) ambientSpace
          step
      · obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact contained_run_of_run_stepAt (side.resolve_left (run_not_runFree _ _)) ambientSpace
          step
      · obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact contained_run_of_run_stepAt (side.resolve_left (run_not_runFree _ _)) ambientSpace
          step
      · obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact contained_run_of_run_stepAt (side.resolve_left (run_not_runFree _ _)) ambientSpace
          step
      · obtain ⟨inner, innerSubject, rfl⟩ := eq_run_of_matched matched
        exact contained_run_of_run_stepAt (side.resolve_left (run_not_runFree _ _)) ambientSpace
          step

/-- The same for steps. -/
theorem contained_run_of_step {space : Pattern} (ambientSpace : Pattern) {subject next : Pattern}
    (side : tokens runLabel subject = 0 ∨ RunSilent admits space)
    (step : Step (regionEvaluator admits space) containedRun subject next) :
    Step (regionEvaluator admits ambientSpace) containedRun (runPattern space subject)
      (runPattern space next) := by
  obtain ⟨fuel, bounded⟩ := step
  exact contained_run_of_stepAt ambientSpace fuel side bounded

/-- **The steps of a run are the runs of the steps of its subject in the
member at the space of the run**, at every ambient space that answers nothing
for a run.  The run constructor puts the member at its space inside every
other member. -/
theorem contained_run_step_iff {ambientSpace space subject target : Pattern}
    (silent : RunSilent admits ambientSpace)
    (side : tokens runLabel subject = 0 ∨ RunSilent admits space) :
    Step (regionEvaluator admits ambientSpace) containedRun (runPattern space subject) target ↔
      ∃ next, target = runPattern space next ∧
        Step (regionEvaluator admits space) containedRun subject next := by
  constructor
  · rintro ⟨fuel, step⟩
    exact contained_run_stepAt_inv silent fuel step
  · rintro ⟨next, rfl, step⟩
    exact contained_run_of_step ambientSpace side step

/-- **Under a guard that admits no run**: at every ambient space, for every
space and every subject. -/
theorem contained_run_step_iff_of_refuses
    (refuses : ∀ space subject : Pattern, admits (runPattern space subject) = false)
    {ambientSpace space subject target : Pattern} :
    Step (regionEvaluator admits ambientSpace) containedRun (runPattern space subject) target ↔
      ∃ next, target = runPattern space next ∧
        Step (regionEvaluator admits space) containedRun subject next :=
  contained_run_step_iff (runSilent_of_refuses refuses ambientSpace)
    (.inr (runSilent_of_refuses refuses space))

/-- **A run of a pattern without a run steps as the member of the ambient
family at its space**, without a guard, at every ambient space that answers
nothing for a run. -/
theorem contained_run_step_iff_member {ambientSpace space subject target : Pattern}
    (silent : RunSilent anySubject ambientSpace) (clean : tokens runLabel subject = 0) :
    Step (regionEvaluator anySubject ambientSpace) containedRun (runPattern space subject) target ↔
      ∃ next, target = runPattern space next ∧
        Step (ambientEvaluator space) ambient subject next := by
  rw [contained_run_step_iff silent (.inl clean)]
  constructor
  · rintro ⟨next, shape, step⟩
    exact ⟨next, shape, (runFree_step_iff_member clean).1.mp step⟩
  · rintro ⟨next, shape, step⟩
    exact ⟨next, shape, (runFree_step_iff_member clean).1.mpr step⟩

/-! ## On terms -/

/-- **On terms: for two ambient spaces that answer nothing for a run, the
transitions of `run(space, atom)` are the same.** -/
theorem contained_run_termStep_ambient_irrelevant {first second : Pattern}
    (silentFirst : RunSilent admits first) (silentSecond : RunSilent admits second)
    {stage : List TypeExpr} (space : Contexts.Term containedRun ⟨.base "Space", stage⟩)
    (atom target : Contexts.Term containedRun ⟨.base "Atom", stage⟩) :
    TermStep (regionEvaluator admits first) containedRun
        (runTermIn contained_declaresRun space atom) target ↔
      TermStep (regionEvaluator admits second) containedRun
        (runTermIn contained_declaresRun space atom) target := by
  have move : ∀ {one other : Pattern}, RunSilent admits one →
      TermStep (regionEvaluator admits one) containedRun
          (runTermIn contained_declaresRun space atom) target →
        TermStep (regionEvaluator admits other) containedRun
          (runTermIn contained_declaresRun space atom) target := by
    rintro one other silent ⟨redex, contractum, before, fired, after⟩
    obtain ⟨otherSpace, otherAtom, rfl, -, -⟩ :=
      eq_runTermIn_of_related contained_quoteDropOnly contained_quoteDropSorted
        contained_declaresRun before
    obtain ⟨fuel, bounded⟩ := fired
    exact ⟨_, contractum,
      termSetoid_base_irrelevant_in contained_quoteDropOnly contained_quoteDropSorted before,
      contained_run_stepAt_of_silent silent other fuel bounded,
      termSetoid_base_irrelevant_in contained_quoteDropOnly contained_quoteDropSorted after⟩
  exact ⟨move silentFirst, move silentSecond⟩

/-- **On terms: the transitions of `run(space, atom)` are the runs of the
transitions of `atom` in the member at `space`**, at every ambient space that
answers nothing for a run. -/
theorem contained_run_termStep_iff {ambientSpace : Pattern}
    (silent : RunSilent admits ambientSpace) {stage : List TypeExpr}
    (space : Contexts.Term containedRun ⟨.base "Space", stage⟩)
    (atom target : Contexts.Term containedRun ⟨.base "Atom", stage⟩)
    (side : tokens runLabel atom.1 = 0 ∨ RunSilent admits space.1) :
    TermStep (regionEvaluator admits ambientSpace) containedRun
        (runTermIn contained_declaresRun space atom) target ↔
      ∃ next : Contexts.Term containedRun ⟨.base "Atom", stage⟩,
        TermStep (regionEvaluator admits space.1) containedRun atom next ∧
          (termSetoid (regionEvaluator admits ambientSpace) containedRun ⟨.base "Atom", stage⟩).r
            target (runTermIn contained_declaresRun space next) := by
  constructor
  · rintro ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩
    obtain ⟨otherSpace, otherAtom, rfl, spaceSame, atomSame⟩ :=
      eq_runTermIn_of_related contained_quoteDropOnly contained_quoteDropSorted
        contained_declaresRun before
    obtain ⟨reached, shape, moved⟩ := contained_run_stepAt_inv silent fuel fired
    obtain ⟨reachedSpace, reachedAtom, rfl, reachedSpaceVal, rfl⟩ :=
      eq_runTermIn_of_val contained_declaresRun contractum shape
    rw [regionEvaluator_congr admits spaceSame] at moved
    refine ⟨reachedAtom, ⟨otherAtom, reachedAtom, ?_, moved, Relation.EqvGen.refl _⟩, ?_⟩
    · exact (contained_quoteDropOnly.termSetoid_iff contained_quoteDropSorted).mpr atomSame.symm
    · refine (termSetoid (regionEvaluator admits ambientSpace) containedRun _).iseqv.trans
        ((termSetoid (regionEvaluator admits ambientSpace) containedRun _).iseqv.symm after) ?_
      refine (runTermIn_related_iff contained_quoteDropOnly contained_quoteDropSorted
        contained_declaresRun).mpr ⟨?_, rfl⟩
      rw [reachedSpaceVal]
      exact spaceSame
  · rintro ⟨next, ⟨redex, contractum, before, fired, after⟩, related⟩
    have cleanRedex : tokens runLabel redex.1 = 0 ∨ RunSilent admits space.1 := by
      refine side.imp (fun clean => ?_) id
      have same := contained_quoteDropOnly.contract_eq before
      rw [← tokens_contract (counted := runLabel) (by decide) (by decide) redex.1, ← same,
        tokens_contract (by decide) (by decide)]
      exact clean
    refine ⟨runTermIn contained_declaresRun space redex,
      runTermIn contained_declaresRun space contractum, ?_,
      contained_run_of_step ambientSpace cleanRedex fired, ?_⟩
    · exact (runTermIn_related_iff contained_quoteDropOnly contained_quoteDropSorted
        contained_declaresRun).mpr ⟨rfl, contained_quoteDropOnly.contract_eq before⟩
    · refine (termSetoid (regionEvaluator admits ambientSpace) containedRun _).iseqv.trans ?_
        ((termSetoid (regionEvaluator admits ambientSpace) containedRun _).iseqv.symm related)
      exact (runTermIn_related_iff contained_quoteDropOnly contained_quoteDropSorted
        contained_declaresRun).mpr ⟨rfl, contained_quoteDropOnly.contract_eq after⟩

/-! ## Without a guard the contained presentation is not contained -/

/-- The atom of a term that is normal in the pure calculus has no step at the
empty space, in the contained presentation and under every guard. -/
theorem contained_normal_at_empty (admits : Pattern → Bool) (term : LF.Term)
    (normal : Dedukti.normalTest pureCover.rigid pureCover.rules term = true) (depth : Nat)
    (target : Pattern) :
    ¬ Step (regionEvaluator admits emptySpace) containedRun (atomAt depth term) target := by
  intro step
  obtain ⟨fuel, bounded⟩ := step_ambientEvaluator_of_guarded
    ((runFree_step_iff_contained (tokens_run_atomAt term depth)).mp step)
  obtain ⟨next, -, sourceStep⟩ := ambient_stepAt_sound (rules := []) noRules_admitted.1
    noRules_admitted.2 (theory := Theory.empty) (fun _ member => absurd member List.not_mem_nil)
    fuel bounded
  exact normal_of_normalTest pureCover _ normal _ sourceStep

/-- **Without a guard the transitions of a run depend on the ambient space.**
At the space of the rule `x ⟶ x` the run of the sort of types in the empty
space steps to itself; at the empty space it has no step. -/
theorem anySubject_run_depends_on_ambient :
    Step (regionEvaluator anySubject (ruleSpace [identityRule])) containedRun
        (runPattern emptySpace (atomAt 0 (.srt .type)))
        (runPattern emptySpace (atomAt 0 (.srt .type))) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator anySubject emptySpace) containedRun
          (runPattern emptySpace (atomAt 0 (.srt .type))) target := by
  constructor
  · refine ⟨1, step_ambientRoot (by simp [contained_rewrites]) ?_⟩
    refine mem_admittedAnswers.mpr ⟨rfl, ?_⟩
    rw [contract_ruleSpace, contract_runPattern', contract_atomAt,
      show contract emptySpace = emptySpace by decide]
    exact identity_answers _
  · intro target step
    obtain ⟨next, -, inner⟩ := (contained_run_step_iff (runSilent_emptySpace anySubject)
      (.inl (tokens_run_atomAt _ _))).mp step
    exact contained_normal_at_empty anySubject (.srt .type) (by decide) 0 next inner

/-- An equation between the run of the sort of types and the run of the sort
of kinds, both in the empty space. -/
def runEquation : Pattern :=
  .apply "=" [runPattern emptySpace (atomAt 0 (.srt .type)),
    runPattern emptySpace (atomAt 0 (.srt .kind))]

/-- The space that stores that equation: a space of the contained
presentation. -/
def runEquationSpace : ContainedSpace :=
  ⟨spaceOfAtoms [runEquation], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- That space answers the run of the sort of kinds for the run of the sort
of types. -/
theorem runEquationSpace_answers :
    runPattern emptySpace (atomAt 0 (.srt .kind)) ∈
      admittedAnswers anySubject runEquationSpace.1
        (runPattern emptySpace (atomAt 0 (.srt .type))) := by
  refine mem_admittedAnswers.mpr ⟨rfl, ?_⟩
  have spaceFixed : contract runEquationSpace.1 = spaceOfAtoms [runEquation] := by decide
  have subjectFixed : contract (runPattern emptySpace (atomAt 0 (.srt .type))) =
      runPattern emptySpace (atomAt 0 (.srt .type)) := by decide
  rw [spaceFixed, subjectFixed, mem_matchResults_spaceOfAtoms]
  refine ⟨runEquation, List.mem_singleton.mpr rfl, ?_⟩
  have leftRead : asRule (runPattern emptySpace (atomAt 0 (.srt .type))) =
      runPattern emptySpace (atomAt 0 (.srt .type)) := by decide
  have rightRead : asRule (runPattern emptySpace (atomAt 0 (.srt .kind))) =
      runPattern emptySpace (atomAt 0 (.srt .kind)) := by decide
  rw [runEquation, atomResults_equation _ (by rw [leftRead]; decide) (by rw [rightRead]; decide),
    leftRead, rightRead]
  simp [runPattern, emptySpace, atomAt, symbolAtom, numeral, unitAtom, matchPattern, matchArgs,
    mergeBindings, applyBindings]

/-- **Without a guard an ambient space rewrites strictly inside a run.**  At
the space that stores an equation between two runs, the run in the empty
space of the application of the sort of types to itself has a step in its
function; that application has no step at the empty space. -/
theorem anySubject_ambient_reaches_inside :
    Step (regionEvaluator anySubject runEquationSpace.1) containedRun
        (runPattern emptySpace (atomAt 0 (.app (.srt .type) (.srt .type))))
        (runPattern emptySpace (.apply "App" [atomAt 0 (.srt .kind), atomAt 0 (.srt .type)])) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator anySubject emptySpace) containedRun
          (atomAt 0 (.app (.srt .type) (.srt .type))) target :=
  ⟨⟨2, step_runAppFunction (by simp [contained_rewrites]) (atomAt 0 (.srt .type))
      (step_ambientRoot (by simp [contained_rewrites]) runEquationSpace_answers)⟩,
    contained_normal_at_empty anySubject _ (by decide) 0⟩

/-- **Under the guard that admits what is no run that step is gone**: the run
has no step at that ambient space. -/
theorem notRun_ambient_stays_outside (target : Pattern) :
    ¬ Step (regionEvaluator notRun runEquationSpace.1) containedRun
      (runPattern emptySpace (atomAt 0 (.app (.srt .type) (.srt .type)))) target := by
  intro step
  obtain ⟨next, -, inner⟩ := (contained_run_step_iff_of_refuses notRun_run).mp step
  exact contained_normal_at_empty notRun _ (by decide) 0 next inner

#print axioms runSilent_of_refuses
#print axioms runSilent_emptySpace
#print axioms runSilent_ruleSpace
#print axioms identity_not_runSilent
#print axioms contained_run_stepAt_of_silent
#print axioms contained_run_step_ambient_irrelevant
#print axioms contained_run_stepAt_inv
#print axioms contained_run_of_stepAt
#print axioms contained_run_step_iff
#print axioms contained_run_step_iff_of_refuses
#print axioms contained_run_step_iff_member
#print axioms contained_run_termStep_ambient_irrelevant
#print axioms contained_run_termStep_iff
#print axioms anySubject_run_depends_on_ambient
#print axioms runEquationSpace_answers
#print axioms anySubject_ambient_reaches_inside
#print axioms notRun_ambient_stays_outside
#print axioms runSilent_notRun
#print axioms runSilent_atomNotRun
#print axioms RunSilent.congr
#print axioms contained_run_of_run_stepAt
#print axioms contained_run_of_step
#print axioms contained_normal_at_empty

end Mettapedia.Logic.HostingStyles.AmbientRegions
