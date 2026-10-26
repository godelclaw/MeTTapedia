import Mettapedia.GSLT.Logic.TaskRelativeMemory
import Mettapedia.MachineLearning.ContinualLearning.OptimalContinualLearning

/-!
# Memory for future task intersections

A task restricts the surviving parameters by intersection. The observation is
whether any parameter survives. One representative of each surviving
membership class answers every finite continuation, not only the next task.
For finite parameter spaces and complement-closed task families, those
classes can be isolated by finite continuations, making coverage necessary.

The canonical state is the union of the surviving membership classes. Rich
families containing every singleton require the exact surviving set; they do
not require retaining task order or redundant history. The displayed source
Definition 8 and its counterexample remain in `OptimalContinualLearning`.

Reference: Knoblauch, Husain and Diethe, *Optimal Continual Learning has
Perfect Memory and is NP-hard* (2020), https://proceedings.mlr.press/v119/knoblauch20a.html.
-/

set_option autoImplicit false

namespace Mettapedia.MachineLearning.ContinualLearning.FutureTaskMemory

open OptimalContinualLearning
open Mettapedia.GSLT.TaskRelativeMemory

variable {Parameter : Type*} (family : Set (Set Parameter))

abbrev Task := {solution : Set Parameter // solution ∈ family}

def restrict (remaining : Set Parameter) (task : Task family) : Set Parameter := remaining ∩ task.val

def observe (_ : Unit) (remaining : Set Parameter) : Prop := remaining.Nonempty

def survives (remaining : Set Parameter) (tasks : List (Task family)) : Prop :=
  (tasks.foldl (restrict family) remaining).Nonempty

theorem mem_after (remaining : Set Parameter) (tasks : List (Task family)) (parameter : Parameter) :
    parameter ∈ tasks.foldl (restrict family) remaining ↔
      parameter ∈ remaining ∧ ∀ task ∈ tasks, parameter ∈ task.val := by
  induction tasks generalizing remaining with
  | nil => simp
  | cons task tasks ih => simp only [List.foldl_cons, ih, restrict, Set.mem_inter_iff,
      List.mem_cons, forall_eq_or_imp]; tauto

theorem survives_iff (remaining : Set Parameter) (tasks : List (Task family)) :
    survives family remaining tasks ↔
      ∃ parameter ∈ remaining, ∀ task ∈ tasks, parameter ∈ task.val := by
  simp only [survives, Set.Nonempty, mem_after]

/-- The membership classes represented by a set, without selecting representatives. -/
def saturation (remaining : Set Parameter) : Set Parameter :=
  {parameter | ∃ representative ∈ remaining, MembershipEquivalent family representative parameter}

theorem saturation_restrict (remaining : Set Parameter) (task : Task family) :
    saturation family (restrict family remaining task) = restrict family (saturation family remaining) task := by
  ext parameter
  constructor
  · rintro ⟨representative, ⟨present, meets⟩, equivalent⟩
    exact ⟨⟨representative, present, equivalent⟩,
      (equivalent task.val task.property).mp meets⟩
  · rintro ⟨⟨representative, present, equivalent⟩, meets⟩
    exact ⟨representative, ⟨present, (equivalent task.val task.property).mpr meets⟩, equivalent⟩

theorem saturation_nonempty (remaining : Set Parameter) :
    (saturation family remaining).Nonempty ↔ remaining.Nonempty := by
  constructor
  · rintro ⟨_, representative, present, _⟩
    exact ⟨representative, present⟩
  · rintro ⟨parameter, present⟩
    exact ⟨parameter, parameter, present, membershipEquivalent_refl family parameter⟩

/-- Saturated sets implement the same task updates and feasibility observations. -/
def saturationRealization :
    Realization (restrict (family := family)) observe (saturation family) where
  update := restrict family
  read _ remaining := remaining.Nonempty
  update_agrees remaining task := (saturation_restrict family remaining task).symm
  read_agrees _ remaining := propext (saturation_nonempty family remaining)

theorem representatives_answer_all_futures {remaining memory : Set Parameter}
    (subset : memory ⊆ remaining)
    (represents : RepresentsEveryRemainingClass family remaining memory)
    (tasks : List (Task family)) :
    survives family memory tasks ↔ survives family remaining tasks := by
  rw [survives_iff, survives_iff]
  constructor
  · rintro ⟨parameter, present, allTasks⟩
    exact ⟨parameter, subset present, allTasks⟩
  · rintro ⟨parameter, present, allTasks⟩
    obtain ⟨representative, stored, equivalent⟩ := represents parameter present
    exact ⟨representative, stored,
      fun task occurs => (equivalent task.val task.property).mp (allTasks task occurs)⟩

theorem separating_task (closed : ComplementClosed family) {first second : Parameter}
    (different : ¬ MembershipEquivalent family first second) :
    ∃ task : Task family, first ∈ task.val ∧ second ∉ task.val := by
  classical
  by_contra absent
  apply different
  intro solution allowed
  constructor
  · intro present
    by_contra missing
    exact absent ⟨⟨solution, allowed⟩, present, missing⟩
  · intro present
    by_contra missing
    exact absent ⟨⟨solutionᶜ, closed solution allowed⟩, missing, fun opposite => opposite present⟩

/-- Finiteness and complement closure give actual finite class-isolating words. -/
theorem class_isolation [Fintype Parameter] (closed : ComplementClosed family) (parameter : Parameter) :
    ∃ tasks : List (Task family), ∀ candidate,
      (∀ task ∈ tasks, candidate ∈ task.val) ↔ MembershipEquivalent family parameter candidate := by
  classical
  have eliminate (candidates : Finset Parameter) :
      ∃ tasks : List (Task family),
        (∀ task ∈ tasks, parameter ∈ task.val) ∧
          ∀ candidate ∈ candidates, (∀ task ∈ tasks, candidate ∈ task.val) →
            MembershipEquivalent family parameter candidate := by
    induction candidates using Finset.induction_on with
    | empty => exact ⟨[], by simp⟩
    | @insert candidate candidates fresh ih =>
      obtain ⟨tasks, contains, separates⟩ := ih
      by_cases equivalent : MembershipEquivalent family parameter candidate
      · refine ⟨tasks, contains, ?_⟩
        intro other occurs allTasks
        rcases Finset.mem_insert.mp occurs with rfl | old
        · exact equivalent
        · exact separates other old allTasks
      · obtain ⟨task, containsParameter, excludesCandidate⟩ := separating_task family closed equivalent
        refine ⟨task :: tasks, ?_, ?_⟩
        · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro containsParameter contains
        · intro other occurs allTasks
          rcases Finset.mem_insert.mp occurs with rfl | old
          · exact (excludesCandidate (allTasks task (by simp))).elim
          · exact separates other old (fun next nextOccurs => allTasks next (by simp [nextOccurs]))
  obtain ⟨tasks, contains, separates⟩ := eliminate Finset.univ
  refine ⟨tasks, fun candidate => ⟨fun allTasks => separates candidate (Finset.mem_univ _) allTasks, ?_⟩⟩
  intro equivalent task occurs
  exact (equivalent task.val task.property).mp (contains task occurs)

theorem all_futures_iff_class_coverage [Fintype Parameter] (closed : ComplementClosed family)
    {remaining memory : Set Parameter} (subset : memory ⊆ remaining) :
    (∀ tasks, survives family memory tasks ↔ survives family remaining tasks) ↔
      RepresentsEveryRemainingClass family remaining memory := by
  constructor
  · intro correct parameter present
    obtain ⟨tasks, isolates⟩ := class_isolation family closed parameter
    have possible : survives family remaining tasks := (survives_iff family remaining tasks).mpr
      ⟨parameter, present, (isolates parameter).mpr (membershipEquivalent_refl family parameter)⟩
    obtain ⟨representative, stored, allTasks⟩ :=
      (survives_iff family memory tasks).mp ((correct tasks).mpr possible)
    exact ⟨representative, stored, (isolates representative).mp allTasks⟩
  · intro represents tasks
    exact representatives_answer_all_futures family subset represents tasks

theorem saturation_eq_iff_all_futures [Fintype Parameter] (closed : ComplementClosed family)
    (first second : Set Parameter) :
    saturation family first = saturation family second ↔
      ∀ tasks, survives family first tasks ↔ survives family second tasks := by
  constructor
  · intro same tasks
    have realizes := (saturationRealization family).futureRealization.agrees (tasks, ())
    have firstAgrees := realizes first
    have secondAgrees := realizes second
    rw [same] at firstAgrees
    exact Iff.of_eq (firstAgrees.symm.trans secondAgrees)
  · intro same
    have transfer (left right : Set Parameter)
        (forward : ∀ tasks, survives family left tasks → survives family right tasks) :
        saturation family left ⊆ saturation family right := by
      rintro parameter ⟨representative, present, equivalent⟩
      obtain ⟨tasks, isolates⟩ := class_isolation family closed representative
      have possible := (survives_iff family left tasks).mpr
        ⟨representative, present, (isolates representative).mpr (membershipEquivalent_refl family _)⟩
      obtain ⟨other, stored, sameTasks⟩ := (survives_iff family right tasks).mp (forward tasks possible)
      have otherEquivalent := (isolates other).mp sameTasks
      exact ⟨other, stored,
        membershipEquivalent_trans (membershipEquivalent_symm otherEquivalent) equivalent⟩
    exact Set.Subset.antisymm (transfer first second (fun tasks => (same tasks).mp))
      (transfer second first (fun tasks => (same tasks).mpr))

/-- With all singleton tasks available, an exact subset memory loses no surviving parameter. -/
theorem perfect_memory_of_singletons (singletons : ∀ parameter, {parameter} ∈ family)
    {remaining memory : Set Parameter} (subset : memory ⊆ remaining)
    (correct : ∀ tasks, survives family memory tasks ↔ survives family remaining tasks) :
    memory = remaining := by
  apply Set.Subset.antisymm subset
  intro parameter present
  let task : Task family := ⟨{parameter}, singletons parameter⟩
  have possible : survives family remaining [task] := by
    exact ⟨parameter, present, rfl⟩
  obtain ⟨representative, stored, allTasks⟩ :=
    (survives_iff family memory [task]).mp ((correct [task]).mpr possible)
  have equal : representative = parameter := allTasks task (by simp)
  simpa only [equal] using stored

namespace Controls

/-- A coarse family permits forgetting one of two parameters indefinitely. -/
theorem harmless_forgetting (tasks : List (Task ({Set.univ} : Set (Set Bool)))) :
    survives _ ({false} : Set Bool) tasks ↔ survives _ Set.univ tasks := by
  apply representatives_answer_all_futures
  · exact Set.subset_univ _
  · intro parameter _
    refine ⟨false, by simp, ?_⟩
    intro solution allowed
    have only : solution = Set.univ := by simpa using allowed
    simp [only]

/-- Singleton tasks force exact surviving-set memory. -/
theorem rich_family_requires_exact {remaining memory : Set Bool} (subset : memory ⊆ remaining)
    (correct : ∀ tasks : List (Task (Set.univ : Set (Set Bool))),
      survives _ memory tasks ↔ survives _ remaining tasks) : memory = remaining :=
  perfect_memory_of_singletons _ (by simp) subset correct

/-- Without complement closure, existential future queries can miss a whole class. -/
theorem nonclosed_family_can_hide_missing_class :
    (∀ tasks : List (Task asymmetricFamily),
      survives _ ({true} : Set Bool) tasks ↔ survives _ Set.univ tasks) ∧
      ¬ RepresentsEveryRemainingClass asymmetricFamily (Set.univ : Set Bool) {true} := by
  have everyTask : ∀ task : Task asymmetricFamily, true ∈ task.val := by
    intro task
    have allowed := task.property
    simp only [asymmetricFamily, Set.mem_insert_iff, Set.mem_singleton_iff] at allowed
    rcases allowed with full | singleton
    · simp only [full, Set.mem_univ]
    · simp only [singleton, Set.mem_singleton_iff]
  constructor
  · intro tasks
    exact iff_of_true ((survives_iff _ _ _).mpr ⟨true, by simp, fun task _ => everyTask task⟩)
      ((survives_iff _ _ _).mpr ⟨true, Set.mem_univ _, fun task _ => everyTask task⟩)
  · intro represents
    obtain ⟨representative, stored, equivalent⟩ := represents false (Set.mem_univ _)
    have equal : representative = true := by simpa using stored
    have allowed : ({true} : Set Bool) ∈ asymmetricFamily := by simp [asymmetricFamily]
    have same := equivalent {true} allowed
    simp [equal] at same

end Controls

end Mettapedia.MachineLearning.ContinualLearning.FutureTaskMemory
