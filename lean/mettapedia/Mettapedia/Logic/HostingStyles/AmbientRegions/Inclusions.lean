import Mettapedia.Logic.HostingStyles.AmbientRegions.Rules
import Mettapedia.Logic.HostingStyles.AmbientSpace.BesideRun
import Mettapedia.Logic.HostingStyles.AmbientSpace.ChangedSpace

/-!
# The three presentations beside each other, on patterns

The ambient presentation, the contained one and the scoped one are compared
under one evaluator of a region, on patterns.

* **Every step of the ambient presentation is a step of the contained one,
  and every step of the contained one is a step of the scoped one**
  (`stepAt_ambient_contained`, `stepAt_contained_scoped`).  The three rewrites
  that the contained presentation has alone are derived in the scoped one,
  each through the congruence of the subject of a run.
* **On a pattern without a run the three have the same steps**
  (`runFree_step_iff_contained`, `runFree_step_iff_scoped`): no rewrite about
  a run matches such a pattern or a part of it.
* Without a guard the steps of the ambient presentation are those of the
  member of the ambient family (`step_any_iff_ambientEvaluator`), so **a
  pattern without a run steps in both presentations as in the ambient
  member** (`runFree_step_iff_member`).
* A guard only removes steps (`stepAt_any_of_guarded`), and an ambient space
  that answers more only adds steps (`stepAt_of_answers_subset`,
  `stepAt_addAtom_ambient`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
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

variable {admits : Pattern → Bool} {ambientSpace : Pattern}

/-! ## The evaluator, under another guard and at another ambient space -/

/-- What the evaluator answers under a guard it answers without one. -/
theorem regionEvaluator_subset_any (admits : Pattern → Bool) (ambientSpace : Pattern)
    (lang other : LanguageDef) (bindings : Bindings) (premise : Premise) :
    ∀ result ∈ regionEvaluator admits ambientSpace lang bindings premise,
      result ∈ regionEvaluator anySubject ambientSpace other bindings premise := by
  unfold regionEvaluator
  split
  · intro result member
    obtain ⟨answer, found, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨answer, admittedAnswers_subset_any found, rfl⟩
  · intro result member
    obtain ⟨answer, found, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨answer, admittedAnswers_subset_any found, rfl⟩
  · intro result member
    cases member

/-- An evaluator at an ambient space that answers at least what another
answers gives at least its answers to every premise. -/
theorem regionEvaluator_mono {small large : Pattern}
    (included : ∀ subject answer : Pattern, answer ∈ admittedAnswers admits small subject →
      answer ∈ admittedAnswers admits large subject)
    (lang other : LanguageDef) (bindings : Bindings) (premise : Premise) :
    ∀ result ∈ regionEvaluator admits small lang bindings premise,
      result ∈ regionEvaluator admits large other bindings premise := by
  unfold regionEvaluator
  split
  · intro result member
    obtain ⟨answer, found, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨answer, included _ _ found, rfl⟩
  · intro result member
    exact member
  · intro result member
    cases member

/-- **A guard only removes steps**: a step under a guard is a step without
one, in every language. -/
theorem stepAt_any_of_guarded {lang : LanguageDef} {fuel : Nat} {source target : Pattern}
    (step : StepAt (regionEvaluator admits ambientSpace) lang fuel source target) :
    StepAt (regionEvaluator anySubject ambientSpace) lang fuel source target :=
  StepAt.transport (fun _ member => member)
    (fun _ _ premise _ bindings result answered =>
      regionEvaluator_subset_any admits ambientSpace lang lang bindings premise result answered) step

/-- **An ambient space that answers more only adds steps**, in every
language. -/
theorem stepAt_of_answers_subset {lang : LanguageDef} {small large : Pattern}
    (included : ∀ subject answer : Pattern, answer ∈ admittedAnswers admits small subject →
      answer ∈ admittedAnswers admits large subject)
    {fuel : Nat} {source target : Pattern}
    (step : StepAt (regionEvaluator admits small) lang fuel source target) :
    StepAt (regionEvaluator admits large) lang fuel source target :=
  StepAt.transport (fun _ member => member)
    (fun _ _ premise _ bindings result answered =>
      regionEvaluator_mono included lang lang bindings premise result answered) step

/-- The ambient space with one more atom answers what the space answers. -/
theorem admittedAnswers_subset_addAtom (atom space subject : Pattern) {answer : Pattern}
    (found : answer ∈ admittedAnswers admits space subject) :
    answer ∈ admittedAnswers admits (addAtom atom space) subject := by
  obtain ⟨admitted, inSpace⟩ := mem_admittedAnswers.mp found
  exact mem_admittedAnswers.mpr ⟨admitted, matchResults_subset_addAtom atom space _ inSpace⟩

/-- **One more atom in the ambient space keeps every step**, in every
language and under every guard. -/
theorem stepAt_addAtom_ambient {lang : LanguageDef} (atom : Pattern) {fuel : Nat}
    {source target : Pattern}
    (step : StepAt (regionEvaluator admits ambientSpace) lang fuel source target) :
    StepAt (regionEvaluator admits (addAtom atom ambientSpace)) lang fuel source target :=
  stepAt_of_answers_subset (fun subject _ found => admittedAnswers_subset_addAtom atom _ subject found)
    step

/-! ## The ambient presentation in the contained one, the contained one in the scoped one -/

/-- **Every step of the ambient presentation is a step of the contained
one**, under one evaluator. -/
theorem stepAt_ambient_contained {fuel : Nat} {source target : Pattern}
    (step : StepAt (regionEvaluator admits ambientSpace) ambient fuel source target) :
    StepAt (regionEvaluator admits ambientSpace) containedRun fuel source target :=
  StepAt.transport ambient_rewrites_subset.1 (fun _ _ _ _ _ _ answered => answered) step

/-- **Every step of the ambient presentation is a step of the scoped one**,
under one evaluator. -/
theorem stepAt_ambient_scoped {fuel : Nat} {source target : Pattern}
    (step : StepAt (regionEvaluator admits ambientSpace) ambient fuel source target) :
    StepAt (regionEvaluator admits ambientSpace) scopedRun fuel source target :=
  StepAt.transport ambient_rewrites_subset.2 (fun _ _ _ _ _ _ answered => answered) step

/-- **Every step of the contained presentation is a step of the scoped one**,
under one evaluator.  Beta, release and the step of a run, each beneath a
run, are found through the congruence of the subject of a run. -/
theorem stepAt_contained_scoped :
    ∀ (fuel : Nat) {source target : Pattern},
      StepAt (regionEvaluator admits ambientSpace) containedRun fuel source target →
        Step (regionEvaluator admits ambientSpace) scopedRun source target := by
  intro fuel
  induction fuel with
  | zero => intro source target step; cases step
  | succ fuel ih =>
      intro source target step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [contained_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
        rw [applied]
        exact ⟨1, step_beta (by simp [scoped_rewrites]) domain body argument binder⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appFunction_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_appFunction (by simp [scoped_rewrites]) argument lifted⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appArgument_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_appArgument (by simp [scoped_rewrites]) function lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piDomain_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_piDomain (by simp [scoped_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piBody_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_piBody (by simp [scoped_rewrites]) domain binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamDomain_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_lamDomain (by simp [scoped_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamBody_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_lamBody (by simp [scoped_rewrites]) domain binder lifted⟩
      · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
        rw [applied]
        exact ⟨1, step_release (by simp [scoped_rewrites]) atom⟩
      · obtain ⟨answer, found, applied⟩ := ambientRoot_inv matched premises
        rw [applied]
        exact ⟨1, step_ambientRoot (by simp [scoped_rewrites]) found⟩
      · obtain ⟨space, subject, answer, rfl, found, applied⟩ := regionRunRoot_inv matched premises
        rw [applied]
        exact ⟨1, step_regionRunRoot (by simp [scoped_rewrites]) found⟩
      · obtain ⟨space, function, argument, moved, rfl, inner, applied⟩ :=
          runAppFunction_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runAppFunction (by simp [scoped_rewrites]) argument lifted⟩
      · obtain ⟨space, function, argument, moved, rfl, inner, applied⟩ :=
          runAppArgument_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runAppArgument (by simp [scoped_rewrites]) function lifted⟩
      · obtain ⟨space, domain, binder, body, moved, rfl, inner, applied⟩ :=
          runPiDomain_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runPiDomain (by simp [scoped_rewrites]) body binder lifted⟩
      · obtain ⟨space, domain, binder, body, moved, rfl, inner, applied⟩ :=
          runPiBody_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runPiBody (by simp [scoped_rewrites]) domain binder lifted⟩
      · obtain ⟨space, domain, binder, body, moved, rfl, inner, applied⟩ :=
          runLamDomain_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runLamDomain (by simp [scoped_rewrites]) body binder lifted⟩
      · obtain ⟨space, domain, binder, body, moved, rfl, inner, applied⟩ :=
          runLamBody_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runLamBody (by simp [scoped_rewrites]) domain binder lifted⟩
      · obtain ⟨space, domain, binder, body, argument, rfl, applied⟩ := runBeta_inv matched premises
        rw [applied]
        exact ⟨2, step_runSubject (by simp [scoped_rewrites]) space
          (step_beta (by simp [scoped_rewrites]) domain body argument binder)⟩
      · obtain ⟨space, atom, rfl, applied⟩ := runRelease_inv matched premises
        rw [applied]
        exact ⟨2, step_runSubject (by simp [scoped_rewrites]) space
          (step_release (by simp [scoped_rewrites]) atom)⟩
      · obtain ⟨outer, space, subject, next, rfl, inner, applied⟩ :=
          runBeneathRun_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runSubject (by simp [scoped_rewrites]) outer lifted⟩

/-- The same for steps. -/
theorem step_contained_scoped {source target : Pattern}
    (step : Step (regionEvaluator admits ambientSpace) containedRun source target) :
    Step (regionEvaluator admits ambientSpace) scopedRun source target := by
  obtain ⟨fuel, bounded⟩ := step
  exact stepAt_contained_scoped fuel bounded

/-! ## On a pattern without a run the three have the same steps -/

/-- **A step of the scoped presentation from a pattern without a run is a
step of the ambient presentation**, under one evaluator. -/
theorem stepAt_scoped_ambient_of_runFree :
    ∀ (fuel : Nat) {source target : Pattern}, tokens runLabel source = 0 →
      StepAt (regionEvaluator admits ambientSpace) scopedRun fuel source target →
        Step (regionEvaluator admits ambientSpace) ambient source target := by
  intro fuel
  induction fuel with
  | zero => intro source target _ step; cases step
  | succ fuel ih =>
      intro source target clean step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [scoped_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
        rw [applied]
        exact ⟨1, step_beta (by simp [ambient_rewrites]) domain body argument binder⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appFunction_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨count, lifted⟩ := ih (parts function (by simp)) inner
        exact ⟨count + 1, step_appFunction (by simp [ambient_rewrites]) argument lifted⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appArgument_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨count, lifted⟩ := ih (parts argument (by simp)) inner
        exact ⟨count + 1, step_appArgument (by simp [ambient_rewrites]) function lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piDomain_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨count, lifted⟩ := ih (parts domain (by simp)) inner
        exact ⟨count + 1, step_piDomain (by simp [ambient_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piBody_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        have cleanBody : tokens runLabel body = 0 := by
          have abstraction := parts (.lambda binder body) (by simp)
          rwa [tokens] at abstraction
        obtain ⟨count, lifted⟩ := ih cleanBody inner
        exact ⟨count + 1, step_piBody (by simp [ambient_rewrites]) domain binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamDomain_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨count, lifted⟩ := ih (parts domain (by simp)) inner
        exact ⟨count + 1, step_lamDomain (by simp [ambient_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamBody_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        have cleanBody : tokens runLabel body = 0 := by
          have abstraction := parts (.lambda binder body) (by simp)
          rwa [tokens] at abstraction
        obtain ⟨count, lifted⟩ := ih cleanBody inner
        exact ⟨count + 1, step_lamBody (by simp [ambient_rewrites]) domain binder lifted⟩
      · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
        rw [applied]
        exact ⟨1, step_release (by simp [ambient_rewrites]) atom⟩
      · obtain ⟨answer, found, applied⟩ := ambientRoot_inv matched premises
        rw [applied]
        exact ⟨1, step_ambientRoot (by simp [ambient_rewrites]) found⟩
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)

/-- **On a pattern without a run the scoped presentation steps as the ambient
one**, under one evaluator. -/
theorem runFree_step_iff_scoped {source target : Pattern} (clean : tokens runLabel source = 0) :
    Step (regionEvaluator admits ambientSpace) scopedRun source target ↔
      Step (regionEvaluator admits ambientSpace) ambient source target := by
  constructor
  · rintro ⟨fuel, step⟩
    exact stepAt_scoped_ambient_of_runFree fuel clean step
  · rintro ⟨fuel, step⟩
    exact ⟨fuel, stepAt_ambient_scoped step⟩

/-- **On a pattern without a run the contained presentation steps as the
ambient one**, under one evaluator. -/
theorem runFree_step_iff_contained {source target : Pattern} (clean : tokens runLabel source = 0) :
    Step (regionEvaluator admits ambientSpace) containedRun source target ↔
      Step (regionEvaluator admits ambientSpace) ambient source target := by
  constructor
  · intro step
    exact (runFree_step_iff_scoped clean).mp (step_contained_scoped step)
  · rintro ⟨fuel, step⟩
    exact ⟨fuel, stepAt_ambient_contained step⟩

/-- **Negative**: a run is a pattern on which the two differ from the ambient
presentation.  The run of the unit atom is a run. -/
theorem run_not_runFree (space subject : Pattern) :
    tokens runLabel (runPattern space subject) ≠ 0 := by
  simp [runPattern, tokens, runLabel]

/-! ## Without a guard: the member of the ambient family -/

/-- **Without a guard the steps of the ambient presentation are those of the
member of the ambient family at the ambient space.** -/
theorem step_any_iff_ambientEvaluator {source target : Pattern} :
    Step (regionEvaluator anySubject ambientSpace) ambient source target ↔
      Step (ambientEvaluator ambientSpace) ambient source target := by
  constructor
  · rintro ⟨fuel, step⟩
    refine ⟨fuel, StepAt.transport (fun _ member => member) ?_ step⟩
    intro rule member premise inRule bindings result answered
    rcases ambient_premises premise
        (List.mem_append_left _ (List.mem_flatMap.mpr ⟨rule, member, inRule⟩)) with
      rfl | ⟨left, right, rfl⟩
    · exact answered
    · cases answered
  · rintro ⟨fuel, step⟩
    refine ⟨fuel, StepAt.transport (fun _ member => member) ?_ step⟩
    intro rule member premise inRule bindings result answered
    rcases ambient_premises premise
        (List.mem_append_left _ (List.mem_flatMap.mpr ⟨rule, member, inRule⟩)) with
      rfl | ⟨left, right, rfl⟩
    · exact answered
    · simp [ambientEvaluator] at answered

/-- A step of the ambient presentation under a guard is a step of the member
of the ambient family. -/
theorem step_ambientEvaluator_of_guarded {source target : Pattern}
    (step : Step (regionEvaluator admits ambientSpace) ambient source target) :
    Step (ambientEvaluator ambientSpace) ambient source target := by
  obtain ⟨fuel, bounded⟩ := step
  exact step_any_iff_ambientEvaluator.mp ⟨fuel, stepAt_any_of_guarded bounded⟩

/-- **A pattern without a run steps, in both presentations and without a
guard, as in the member of the ambient family at the ambient space.** -/
theorem runFree_step_iff_member {source target : Pattern} (clean : tokens runLabel source = 0) :
    (Step (regionEvaluator anySubject ambientSpace) containedRun source target ↔
        Step (ambientEvaluator ambientSpace) ambient source target) ∧
      (Step (regionEvaluator anySubject ambientSpace) scopedRun source target ↔
        Step (ambientEvaluator ambientSpace) ambient source target) :=
  ⟨(runFree_step_iff_contained clean).trans step_any_iff_ambientEvaluator,
    (runFree_step_iff_scoped clean).trans step_any_iff_ambientEvaluator⟩

#print axioms stepAt_any_of_guarded
#print axioms stepAt_of_answers_subset
#print axioms stepAt_addAtom_ambient
#print axioms stepAt_ambient_contained
#print axioms stepAt_ambient_scoped
#print axioms stepAt_contained_scoped
#print axioms stepAt_scoped_ambient_of_runFree
#print axioms runFree_step_iff_scoped
#print axioms runFree_step_iff_contained
#print axioms step_any_iff_ambientEvaluator
#print axioms runFree_step_iff_member
#print axioms regionEvaluator_subset_any
#print axioms regionEvaluator_mono
#print axioms admittedAnswers_subset_addAtom
#print axioms step_contained_scoped
#print axioms run_not_runFree
#print axioms step_ambientEvaluator_of_guarded

end Mettapedia.Logic.HostingStyles.AmbientRegions
