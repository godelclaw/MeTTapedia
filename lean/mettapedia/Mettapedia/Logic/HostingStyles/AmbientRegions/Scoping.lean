import Mettapedia.Logic.HostingStyles.AmbientRegions.RunsOfAtoms

/-!
# Scoping: in the scoped presentation a run steps by its own space and by the ambient space

* **Every step of the contained presentation is a step of the scoped one**
  (`stepAt_contained_scoped`, on terms `termStep_contained_scoped`).
* **The steps of a run are those by the rules of either space**
  (`scoped_run_step_iff`): at an ambient space that answers nothing for a run,
  `run(space, subject)` steps to the runs of the steps of `subject` in the
  scoped member at the ambient space, and to the runs of the steps of
  `subject` in the ambient presentation at `space`.  The second kind is by
  the rewrites of the ambient presentation, which has no rewrite about a run:
  the space of a run reaches through application, abstraction and product,
  and not into a run inside its subject.
* For a subject without a run the two kinds together are the steps at one
  space that answers what both answer (`AnswersBoth`,
  `scoped_run_step_iff_joined`); for the atom of a term in the space of a
  list of rules, at the ambient space of another list, they are the runs of
  the atoms of the steps of the term by the rules of both lists
  (`scoped_runAtom_step_iff`, `scoped_runAtom_termStep_iff`).
* **A larger ambient space keeps every step**, in both presentations
  (`scoped_addedAmbient_steps`, `contained_addedAmbient_steps`), and the
  converse fails for the scoped one (`scoped_addedAmbient_converse_fails`).
* **A step that only the scoped presentation has** (`scoped_alone_steps`): the
  run of `choose heads tails` in the empty space, at the ambient space of the
  two rules of choice.  So the scoped presentation is not contained
  (`scoped_run_depends_on_ambient`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory patternVars usesOnly withChoice chooseLeft chooseRight normal_of_normalTest)
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

/-! ## The steps of a run are those by the rules of either space -/

/-- **A step of a run in the scoped presentation, at an ambient space that
answers nothing for a run, is the run of a step of its subject**: a step of
the scoped member at the ambient space, or a step of the ambient presentation
at the space of the run. -/
theorem scoped_run_stepAt_inv {ambientSpace : Pattern} (silent : RunSilent admits ambientSpace) :
    ∀ (fuel : Nat) {space subject target : Pattern},
      StepAt (regionEvaluator admits ambientSpace) scopedRun fuel (runPattern space subject)
          target →
        ∃ next, target = runPattern space next ∧
          (Step (regionEvaluator admits ambientSpace) scopedRun subject next ∨
            Step (regionEvaluator admits space) ambient subject next) := by
  intro fuel
  induction fuel with
  | zero => intro space subject target step; cases step
  | succ fuel ih =>
      intro space subject target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [scoped_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
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
        exact ⟨answer, applied, .inr ⟨1, step_ambientRoot (by simp [ambient_rewrites]) found⟩⟩
      · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
          runAppFunction_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨reached, same, either⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        refine ⟨_, applied, either.imp ?_ ?_⟩
        · rintro ⟨count, lifted⟩
          exact ⟨count + 1, step_appFunction (by simp [scoped_rewrites]) argument lifted⟩
        · rintro ⟨count, lifted⟩
          exact ⟨count + 1, step_appFunction (by simp [ambient_rewrites]) argument lifted⟩
      · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
          runAppArgument_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨reached, same, either⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        refine ⟨_, applied, either.imp ?_ ?_⟩
        · rintro ⟨count, lifted⟩
          exact ⟨count + 1, step_appArgument (by simp [scoped_rewrites]) function lifted⟩
        · rintro ⟨count, lifted⟩
          exact ⟨count + 1, step_appArgument (by simp [ambient_rewrites]) function lifted⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runPiDomain_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨reached, same, either⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        refine ⟨_, applied, either.imp ?_ ?_⟩
        · rintro ⟨count, lifted⟩
          exact ⟨count + 1, step_piDomain (by simp [scoped_rewrites]) body binder lifted⟩
        · rintro ⟨count, lifted⟩
          exact ⟨count + 1, step_piDomain (by simp [ambient_rewrites]) body binder lifted⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runPiBody_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨reached, same, either⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        refine ⟨_, applied, either.imp ?_ ?_⟩
        · rintro ⟨count, lifted⟩
          exact ⟨count + 1, step_piBody (by simp [scoped_rewrites]) domain binder lifted⟩
        · rintro ⟨count, lifted⟩
          exact ⟨count + 1, step_piBody (by simp [ambient_rewrites]) domain binder lifted⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runLamDomain_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨reached, same, either⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        refine ⟨_, applied, either.imp ?_ ?_⟩
        · rintro ⟨count, lifted⟩
          exact ⟨count + 1, step_lamDomain (by simp [scoped_rewrites]) body binder lifted⟩
        · rintro ⟨count, lifted⟩
          exact ⟨count + 1, step_lamDomain (by simp [ambient_rewrites]) body binder lifted⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runLamBody_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨reached, same, either⟩ := ih inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        refine ⟨_, applied, either.imp ?_ ?_⟩
        · rintro ⟨count, lifted⟩
          exact ⟨count + 1, step_lamBody (by simp [scoped_rewrites]) domain binder lifted⟩
        · rintro ⟨count, lifted⟩
          exact ⟨count + 1, step_lamBody (by simp [ambient_rewrites]) domain binder lifted⟩
      · obtain ⟨otherSpace, inner, moved, shape, innerStep, applied⟩ :=
          runSubject_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        exact ⟨moved, applied, .inl ⟨fuel, innerStep⟩⟩

/-- **A step of the ambient presentation at the space of a run is a step of
the run in the scoped presentation**, at every ambient space: a rule at the
root is found by the root step of the run, a position beneath the root by a
congruence beneath the run, and beta and release by the congruence of its
subject. -/
theorem scoped_run_of_ambient_stepAt {space : Pattern} (ambientSpace : Pattern) :
    ∀ (fuel : Nat) {subject next : Pattern},
      StepAt (regionEvaluator admits space) ambient fuel subject next →
        Step (regionEvaluator admits ambientSpace) scopedRun (runPattern space subject)
          (runPattern space next) := by
  intro fuel
  induction fuel with
  | zero => intro subject next step; cases step
  | succ fuel ih =>
      intro subject next step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [ambient_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
        rw [applied]
        exact ⟨2, step_runSubject (by simp [scoped_rewrites]) space
          (step_beta (by simp [scoped_rewrites]) domain body argument binder)⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appFunction_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runAppFunction (by simp [scoped_rewrites]) argument lifted⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appArgument_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runAppArgument (by simp [scoped_rewrites]) function lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piDomain_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runPiDomain (by simp [scoped_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piBody_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runPiBody (by simp [scoped_rewrites]) domain binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamDomain_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runLamDomain (by simp [scoped_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamBody_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runLamBody (by simp [scoped_rewrites]) domain binder lifted⟩
      · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
        rw [applied]
        exact ⟨2, step_runSubject (by simp [scoped_rewrites]) space
          (step_release (by simp [scoped_rewrites]) atom)⟩
      · obtain ⟨answer, found, applied⟩ := ambientRoot_inv matched premises
        rw [applied]
        exact ⟨1, step_regionRunRoot (by simp [scoped_rewrites]) found⟩

/-- **A step of the subject of a run, in the scoped member at the ambient
space, is a step of the run**: the ambient space reaches in. -/
theorem scoped_run_of_step {ambientSpace : Pattern} (space : Pattern) {subject next : Pattern}
    (step : Step (regionEvaluator admits ambientSpace) scopedRun subject next) :
    Step (regionEvaluator admits ambientSpace) scopedRun (runPattern space subject)
      (runPattern space next) := by
  obtain ⟨fuel, bounded⟩ := step
  exact ⟨fuel + 1, step_runSubject (by simp [scoped_rewrites]) space bounded⟩

/-- **The steps of a run are those by the rules of either space.**  At an
ambient space that answers nothing for a run, `run(space, subject)` steps to
the runs of the steps of `subject` in the scoped member at the ambient space,
and to the runs of the steps of `subject` in the ambient presentation at
`space`. -/
theorem scoped_run_step_iff {ambientSpace space subject target : Pattern}
    (silent : RunSilent admits ambientSpace) :
    Step (regionEvaluator admits ambientSpace) scopedRun (runPattern space subject) target ↔
      ∃ next, target = runPattern space next ∧
        (Step (regionEvaluator admits ambientSpace) scopedRun subject next ∨
          Step (regionEvaluator admits space) ambient subject next) := by
  constructor
  · rintro ⟨fuel, step⟩
    exact scoped_run_stepAt_inv silent fuel step
  · rintro ⟨next, rfl, viaAmbient | ⟨fuel, viaRun⟩⟩
    · exact scoped_run_of_step space viaAmbient
    · exact scoped_run_of_ambient_stepAt ambientSpace fuel viaRun

/-! ## One space that answers what both answer -/

/-- **A space answers what two spaces answer**, under a guard: its answers
for a subject are the answers of the one and those of the other. -/
def AnswersBoth (admits : Pattern → Bool) (joined first second : Pattern) : Prop :=
  ∀ subject answer : Pattern, answer ∈ admittedAnswers admits joined subject ↔
    answer ∈ admittedAnswers admits first subject ∨ answer ∈ admittedAnswers admits second subject

/-- **Positive**: the space of two lists of rules, one after the other. -/
theorem ruleSpace_append_answersBoth (admits : Pattern → Bool)
    (first second : List Dedukti.RewriteRule) :
    AnswersBoth admits (ruleSpace (first ++ second)) (ruleSpace first) (ruleSpace second) := by
  intro subject answer
  have split : matchResults (ruleSpace (first ++ second)) (contract subject) =
      matchResults (ruleSpace first) (contract subject) ++
        matchResults (ruleSpace second) (contract subject) := by
    simp [matchResults, ruleSpace, storedAtoms_spaceOfAtoms, List.map_append, List.flatMap_append]
  simp only [mem_admittedAnswers, contract_ruleSpace, split, List.mem_append]
  tauto

/-- **Negative**: the empty space does not answer what the space of the rule
`x ⟶ x` answers. -/
theorem emptySpace_not_answersBoth :
    ¬ AnswersBoth anySubject emptySpace (ruleSpace [identityRule]) emptySpace := by
  intro both
  have found : unitAtom ∈ admittedAnswers anySubject (ruleSpace [identityRule]) unitAtom := by
    refine mem_admittedAnswers.mpr ⟨rfl, ?_⟩
    rw [contract_ruleSpace]
    exact identity_answers _
  have atEmpty := (both unitAtom unitAtom).mpr (.inl found)
  rw [admittedAnswers_any, show contract emptySpace = emptySpace by decide,
    matchResults_emptySpace] at atEmpty
  cases atEmpty

/-- A step of the ambient presentation at a space that answers what two
spaces answer is a step at one of the two. -/
theorem stepAt_either_of_joined {joined first second : Pattern}
    (both : AnswersBoth admits joined first second) :
    ∀ (fuel : Nat) {source target : Pattern},
      StepAt (regionEvaluator admits joined) ambient fuel source target →
        Step (regionEvaluator admits first) ambient source target ∨
          Step (regionEvaluator admits second) ambient source target := by
  intro fuel
  induction fuel with
  | zero => intro source target step; cases step
  | succ fuel ih =>
      intro source target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [ambient_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
        rw [applied]
        exact .inl ⟨1, step_beta (by simp [ambient_rewrites]) domain body argument binder⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appFunction_inv matched premises
        rw [applied]
        exact (ih inner).imp
          (fun ⟨count, lifted⟩ => ⟨count + 1, step_appFunction (by simp [ambient_rewrites])
            argument lifted⟩)
          (fun ⟨count, lifted⟩ => ⟨count + 1, step_appFunction (by simp [ambient_rewrites])
            argument lifted⟩)
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appArgument_inv matched premises
        rw [applied]
        exact (ih inner).imp
          (fun ⟨count, lifted⟩ => ⟨count + 1, step_appArgument (by simp [ambient_rewrites])
            function lifted⟩)
          (fun ⟨count, lifted⟩ => ⟨count + 1, step_appArgument (by simp [ambient_rewrites])
            function lifted⟩)
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piDomain_inv matched premises
        rw [applied]
        exact (ih inner).imp
          (fun ⟨count, lifted⟩ => ⟨count + 1, step_piDomain (by simp [ambient_rewrites])
            body binder lifted⟩)
          (fun ⟨count, lifted⟩ => ⟨count + 1, step_piDomain (by simp [ambient_rewrites])
            body binder lifted⟩)
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piBody_inv matched premises
        rw [applied]
        exact (ih inner).imp
          (fun ⟨count, lifted⟩ => ⟨count + 1, step_piBody (by simp [ambient_rewrites])
            domain binder lifted⟩)
          (fun ⟨count, lifted⟩ => ⟨count + 1, step_piBody (by simp [ambient_rewrites])
            domain binder lifted⟩)
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamDomain_inv matched premises
        rw [applied]
        exact (ih inner).imp
          (fun ⟨count, lifted⟩ => ⟨count + 1, step_lamDomain (by simp [ambient_rewrites])
            body binder lifted⟩)
          (fun ⟨count, lifted⟩ => ⟨count + 1, step_lamDomain (by simp [ambient_rewrites])
            body binder lifted⟩)
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamBody_inv matched premises
        rw [applied]
        exact (ih inner).imp
          (fun ⟨count, lifted⟩ => ⟨count + 1, step_lamBody (by simp [ambient_rewrites])
            domain binder lifted⟩)
          (fun ⟨count, lifted⟩ => ⟨count + 1, step_lamBody (by simp [ambient_rewrites])
            domain binder lifted⟩)
      · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
        rw [applied]
        exact .inl ⟨1, step_release (by simp [ambient_rewrites]) atom⟩
      · obtain ⟨answer, found, applied⟩ := ambientRoot_inv matched premises
        rw [applied]
        exact ((both _ _).mp found).imp
          (fun inFirst => ⟨1, step_ambientRoot (by simp [ambient_rewrites]) inFirst⟩)
          (fun inSecond => ⟨1, step_ambientRoot (by simp [ambient_rewrites]) inSecond⟩)

/-- **The steps of the ambient presentation at a space that answers what two
spaces answer are the steps at the one and the steps at the other.** -/
theorem step_joined_iff {joined first second : Pattern}
    (both : AnswersBoth admits joined first second) {source target : Pattern} :
    Step (regionEvaluator admits joined) ambient source target ↔
      Step (regionEvaluator admits first) ambient source target ∨
        Step (regionEvaluator admits second) ambient source target := by
  constructor
  · rintro ⟨fuel, step⟩
    exact stepAt_either_of_joined both fuel step
  · rintro (⟨fuel, step⟩ | ⟨fuel, step⟩)
    · exact ⟨fuel, stepAt_of_answers_subset
        (fun subject answer found => (both subject answer).mpr (.inl found)) step⟩
    · exact ⟨fuel, stepAt_of_answers_subset
        (fun subject answer found => (both subject answer).mpr (.inr found)) step⟩

/-- **For a subject without a run, the steps of its run are the runs of its
steps at one space that answers what the space of the run and the ambient
space answer**: a run in the scoped presentation is a local set of rules
beside the ambient ones. -/
theorem scoped_run_step_iff_joined {ambientSpace space joined subject target : Pattern}
    (silent : RunSilent admits ambientSpace) (both : AnswersBoth admits joined space ambientSpace)
    (clean : tokens runLabel subject = 0) :
    Step (regionEvaluator admits ambientSpace) scopedRun (runPattern space subject) target ↔
      ∃ next, target = runPattern space next ∧
        Step (regionEvaluator admits joined) ambient subject next := by
  rw [scoped_run_step_iff silent]
  constructor
  · rintro ⟨next, shape, viaAmbient | viaRun⟩
    · exact ⟨next, shape,
        (step_joined_iff both).mpr (.inr ((runFree_step_iff_scoped clean).mp viaAmbient))⟩
    · exact ⟨next, shape, (step_joined_iff both).mpr (.inl viaRun)⟩
  · rintro ⟨next, shape, step⟩
    rcases (step_joined_iff both).mp step with viaRun | viaAmbient
    · exact ⟨next, shape, .inr viaRun⟩
    · exact ⟨next, shape, .inl ((runFree_step_iff_scoped clean).mpr viaAmbient)⟩

/-! ## The run of the atom of a term: the rules of both lists -/

/-- **The steps of the run of the atom of a term in the space of a list of
rules, at the ambient space of another list, are the runs of the atoms of the
steps of the term by the rules of both lists.** -/
theorem scoped_runAtom_step_iff (admitsAtoms : AdmitsAtoms admits)
    {runRules ambientRules : List Dedukti.RewriteRule}
    (silent : RunSilent admits (ruleSpace ambientRules))
    (firstOrder : ∀ rule ∈ runRules ++ ambientRules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ runRules ++ ambientRules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ runRules ++ ambientRules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Pattern} :
    Step (regionEvaluator admits (ruleSpace ambientRules)) scopedRun
        (runPattern (ruleSpace runRules) (atomAt depth source)) target ↔
      ∃ next, target = runPattern (ruleSpace runRules) (atomAt depth next) ∧
        Dedukti.Step theory source next := by
  rw [scoped_run_step_iff_joined silent (ruleSpace_append_answersBoth admits runRules ambientRules)
    (tokens_run_atomAt source depth)]
  constructor
  · rintro ⟨reached, rfl, step⟩
    obtain ⟨next, rfl, sourceStep⟩ :=
      (guarded_atom_step_iff admitsAtoms firstOrder bound rulesIff undefined).mp step
    exact ⟨next, rfl, sourceStep⟩
  · rintro ⟨next, rfl, sourceStep⟩
    exact ⟨atomAt depth next, rfl,
      (guarded_atom_step_iff admitsAtoms firstOrder bound rulesIff undefined).mpr
        ⟨next, rfl, sourceStep⟩⟩

/-- **On terms.**  The transitions of the run of the atom of a term in the
space of a list of rules, at the ambient space of another list, are the runs
of the atoms of its steps by the rules of both lists. -/
theorem scoped_runAtom_termStep_iff (admitsAtoms : AdmitsAtoms admits)
    {runRules ambientRules : List Dedukti.RewriteRule}
    (silent : RunSilent admits (ruleSpace ambientRules))
    (firstOrder : ∀ rule ∈ runRules ++ ambientRules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ runRules ++ ambientRules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ runRules ++ ambientRules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {source : LF.Term}
    {target : Contexts.Term scopedRun (atomInterface depth)} :
    TermStep (regionEvaluator admits (ruleSpace ambientRules)) scopedRun
        (runAtomIn (presentation := scopedPresentation) scoped_declaresRun region_carriesAtoms.2
          runRules depth source) target ↔
      ∃ next, Dedukti.Step theory source next ∧
        target = runAtomIn (presentation := scopedPresentation) scoped_declaresRun
          region_carriesAtoms.2 runRules depth next :=
  termStep_runAtomIn_iff (presentation := scopedPresentation) scoped_declaresRun
    region_carriesAtoms.2 scoped_quoteDropOnly scoped_quoteDropSorted scoped_namesOnlyDropped
    (scoped_runAtom_step_iff admitsAtoms silent firstOrder bound rulesIff undefined)

/-! ## A step that only the scoped presentation has -/

/-- **The ambient space reaches into a run of the scoped presentation**: the
run of `choose heads tails` in the empty space steps to the run of `heads`,
at the ambient space of the two rules of choice. -/
theorem scoped_runCoin_steps (admitsAtoms : AdmitsAtoms admits) :
    Step (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) scopedRun
      (runPattern (ruleSpace []) (atomAt 0 coin))
      (runPattern (ruleSpace []) (atomAt 0 (.con "heads"))) :=
  (scoped_runAtom_step_iff admitsAtoms (runRules := []) (choiceSpace_runSilent admits)
    choiceRules_admitted.1 choiceRules_admitted.2 withChoice_rules (fun _ => rfl)).mpr
    ⟨_, rfl, Dedukti.step_choose_left Theory.empty _ _⟩

/-- **A step that only the scoped presentation has.**  At the ambient space
of the two rules of choice the run of `choose heads tails` in the empty space
has a step in the scoped presentation and none in the contained one. -/
theorem scoped_alone_steps (admitsAtoms : AdmitsAtoms admits) :
    Step (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) scopedRun
        (runPattern (ruleSpace []) (atomAt 0 coin))
        (runPattern (ruleSpace []) (atomAt 0 (.con "heads"))) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) containedRun
          (runPattern (ruleSpace []) (atomAt 0 coin)) target :=
  ⟨scoped_runCoin_steps admitsAtoms, contained_runCoin_normal admitsAtoms⟩

/-- The run of `choose heads tails` in the empty space has no step at the
empty ambient space, in the scoped presentation. -/
theorem scoped_runCoin_normal_at_empty (admitsAtoms : AdmitsAtoms admits) (target : Pattern) :
    ¬ Step (regionEvaluator admits (ruleSpace [])) scopedRun
      (runPattern (ruleSpace []) (atomAt 0 coin)) target := by
  intro step
  obtain ⟨next, -, sourceStep⟩ := (scoped_runAtom_step_iff admitsAtoms (runRules := [])
    (ambientRules := []) (runSilent_emptySpace admits) noRules_admitted.1 noRules_admitted.2
    (theory := Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-- **The scoped presentation is not contained**: the transitions of a run
depend on the ambient space.  The run of `choose heads tails` in the empty
space has a step at the ambient space of the two rules of choice, and no step
at the empty ambient space; both ambient spaces answer nothing for a run. -/
theorem scoped_run_depends_on_ambient (admitsAtoms : AdmitsAtoms admits) :
    RunSilent admits (ruleSpace [chooseLeft, chooseRight]) ∧ RunSilent admits (ruleSpace []) ∧
      Step (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) scopedRun
        (runPattern (ruleSpace []) (atomAt 0 coin))
        (runPattern (ruleSpace []) (atomAt 0 (.con "heads"))) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator admits (ruleSpace [])) scopedRun
          (runPattern (ruleSpace []) (atomAt 0 coin)) target :=
  ⟨choiceSpace_runSilent admits, runSilent_emptySpace admits, scoped_runCoin_steps admitsAtoms,
    scoped_runCoin_normal_at_empty admitsAtoms⟩

/-! ## A larger ambient space keeps every step -/

/-- **One more atom in the ambient space keeps every transition of the scoped
presentation**, between the same terms and at every interface. -/
theorem scoped_addedAmbient_steps (atom ambientSpace : Pattern) {interface : Contexts.Interface}
    {term next : Contexts.Term scopedRun interface}
    (step : TermStep (regionEvaluator admits ambientSpace) scopedRun term next) :
    TermStep (regionEvaluator admits (addAtom atom ambientSpace)) scopedRun term next := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := step
  exact ⟨redex, contractum,
    termSetoid_base_irrelevant_in scoped_quoteDropOnly scoped_quoteDropSorted before,
    ⟨fuel, stepAt_addAtom_ambient atom fired⟩,
    termSetoid_base_irrelevant_in scoped_quoteDropOnly scoped_quoteDropSorted after⟩

/-- **One more atom in the ambient space keeps every transition of the
contained presentation.** -/
theorem contained_addedAmbient_steps (atom ambientSpace : Pattern)
    {interface : Contexts.Interface} {term next : Contexts.Term containedRun interface}
    (step : TermStep (regionEvaluator admits ambientSpace) containedRun term next) :
    TermStep (regionEvaluator admits (addAtom atom ambientSpace)) containedRun term next := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := step
  exact ⟨redex, contractum,
    termSetoid_base_irrelevant_in contained_quoteDropOnly contained_quoteDropSorted before,
    ⟨fuel, stepAt_addAtom_ambient atom fired⟩,
    termSetoid_base_irrelevant_in contained_quoteDropOnly contained_quoteDropSorted after⟩

/-- **The converse fails for the scoped presentation, inside a run**: with
the first rule of choice added to the empty ambient space, the run of
`choose heads tails` in the empty space has a step that it does not have at
the empty ambient space. -/
theorem scoped_addedAmbient_converse_fails (admitsAtoms : AdmitsAtoms admits) :
    Step (regionEvaluator admits (addAtom (equationOf chooseLeft) emptySpace)) scopedRun
        (runPattern (ruleSpace []) (atomAt 0 coin))
        (runPattern (ruleSpace []) (atomAt 0 (.con "heads"))) ∧
      ∀ target : Pattern,
        ¬ Step (regionEvaluator admits emptySpace) scopedRun
          (runPattern (ruleSpace []) (atomAt 0 coin)) target := by
  refine ⟨?_, scoped_runCoin_normal_at_empty admitsAtoms⟩
  exact (scoped_runAtom_step_iff admitsAtoms (runRules := []) (ambientRules := [chooseLeft])
    (runSilent_ruleSpace admits chooseLeft_admitted.1 (by
      intro rule member index
      rw [List.mem_singleton.mp member]
      simp [chooseLeft, Dedukti.choose]))
    chooseLeft_admitted.1 chooseLeft_admitted.2 (theory := Theory.ofTable {chooseLeft})
    (fun rule => by
      show rule ∈ ({chooseLeft} : Finset Dedukti.RewriteRule) ↔ rule ∈ [chooseLeft]
      simp)
    (fun _ => rfl)).mpr ⟨_, rfl, chooseLeft_step⟩

/-- **In the contained presentation a larger ambient space adds no step to a
run**: at the first rule of choice added to the empty ambient space the run of
`choose heads tails` in the empty space still has no step. -/
theorem contained_addedAmbient_adds_nothing_to_run (admitsAtoms : AdmitsAtoms admits)
    (target : Pattern) :
    ¬ Step (regionEvaluator admits (addAtom (equationOf chooseLeft) emptySpace)) containedRun
      (runPattern (ruleSpace []) (atomAt 0 coin)) target := by
  intro step
  have silent : RunSilent admits (ruleSpace [chooseLeft]) :=
    runSilent_ruleSpace admits chooseLeft_admitted.1 (by
      intro rule member index
      rw [List.mem_singleton.mp member]
      simp [chooseLeft, Dedukti.choose])
  obtain ⟨next, -, sourceStep⟩ := (contained_runAtom_step_iff admitsAtoms silent (rules := [])
    noRules_admitted.1 noRules_admitted.2 (theory := Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp step
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-! ## On terms: the contained presentation in the scoped one -/

/-- A term of the contained presentation, as a term of the scoped one: the
two have the same constructors. -/
def scopedOf {interface : Contexts.Interface} (term : Contexts.Term containedRun interface) :
    Contexts.Term scopedRun interface :=
  ⟨term.1, wellSorted_of_terms_subset (small := containedRun) (large := scopedRun)
    (fun _ member => member) term.2⟩

@[simp] theorem scopedOf_val {interface : Contexts.Interface}
    (term : Contexts.Term containedRun interface) : (scopedOf term).1 = term.1 :=
  rfl

/-- **Every transition of the contained presentation is a transition of the
scoped one**, between the same terms, at every interface and under one
evaluator. -/
theorem termStep_contained_scoped {ambientSpace : Pattern} {interface : Contexts.Interface}
    {term next : Contexts.Term containedRun interface}
    (step : TermStep (regionEvaluator admits ambientSpace) containedRun term next) :
    TermStep (regionEvaluator admits ambientSpace) scopedRun (scopedOf term) (scopedOf next) := by
  obtain ⟨redex, contractum, before, fired, after⟩ := step
  refine ⟨scopedOf redex, scopedOf contractum, ?_, step_contained_scoped fired, ?_⟩
  · exact (scoped_quoteDropOnly.termSetoid_iff scoped_quoteDropSorted).mpr
      (contained_quoteDropOnly.contract_eq before)
  · exact (scoped_quoteDropOnly.termSetoid_iff scoped_quoteDropSorted).mpr
      (contained_quoteDropOnly.contract_eq after)

/-- **Negative**: not every transition of the scoped presentation is one of
the contained presentation.  As terms: the run of `choose heads tails` in the
empty space, at the ambient space of the two rules of choice. -/
theorem termStep_scoped_not_contained (admitsAtoms : AdmitsAtoms admits) :
    TermStep (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) scopedRun
        (runAtomIn (presentation := scopedPresentation) scoped_declaresRun region_carriesAtoms.2
          [] 0 coin)
        (runAtomIn (presentation := scopedPresentation) scoped_declaresRun region_carriesAtoms.2
          [] 0 (.con "heads")) ∧
      ∀ target : Contexts.Term containedRun (atomInterface 0),
        ¬ TermStep (regionEvaluator admits (ruleSpace [chooseLeft, chooseRight])) containedRun
          (runAtomIn (presentation := containedPresentation) contained_declaresRun
            region_carriesAtoms.1 [] 0 coin) target := by
  constructor
  · exact (scoped_runAtom_termStep_iff admitsAtoms (runRules := []) (choiceSpace_runSilent admits)
      choiceRules_admitted.1 choiceRules_admitted.2 withChoice_rules (fun _ => rfl)).mpr
      ⟨_, Dedukti.step_choose_left Theory.empty _ _, rfl⟩
  · intro target step
    obtain ⟨next, sourceStep, -⟩ := (contained_runAtom_termStep_iff admitsAtoms
      (choiceSpace_runSilent admits) (rules := []) noRules_admitted.1 noRules_admitted.2
      (theory := Theory.empty)
      (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
      (fun _ => rfl)).mp step
    exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

#print axioms scoped_run_stepAt_inv
#print axioms scoped_run_of_ambient_stepAt
#print axioms scoped_run_step_iff
#print axioms ruleSpace_append_answersBoth
#print axioms emptySpace_not_answersBoth
#print axioms step_joined_iff
#print axioms scoped_run_step_iff_joined
#print axioms scoped_runAtom_step_iff
#print axioms scoped_runAtom_termStep_iff
#print axioms scoped_alone_steps
#print axioms scoped_run_depends_on_ambient
#print axioms scoped_addedAmbient_steps
#print axioms contained_addedAmbient_steps
#print axioms scoped_addedAmbient_converse_fails
#print axioms contained_addedAmbient_adds_nothing_to_run
#print axioms termStep_contained_scoped
#print axioms termStep_scoped_not_contained
#print axioms scoped_run_of_step
#print axioms stepAt_either_of_joined
#print axioms scoped_runCoin_steps
#print axioms scoped_runCoin_normal_at_empty

end Mettapedia.Logic.HostingStyles.AmbientRegions
