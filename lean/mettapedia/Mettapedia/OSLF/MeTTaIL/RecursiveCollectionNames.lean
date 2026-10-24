import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine
import Mettapedia.OSLF.MeTTaIL.CanonicalCompare
import Mettapedia.OSLF.MeTTaIL.ScopedCollectionCanonical

/-!
# Name-table support retained by recursive matching

Native canonical comparisons use a finite ordered table. Matching creates no
new target names: child tasks inspect subterms and collection allocations
remove or retain existing elements. This keeps the table obligation local to
the original input, rather than assuming it for a whole future run.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine

open Syntax CanonicalBags CanonicalCompare CollectionSelection

private theorem allocation_value_mem {α : Type} {idempotent : Bool} {count : Nat}
    {items : List α} {allocation : Allocation α}
    (allocated : allocation ∈ tracedAllocations idempotent count items)
    {value : α} (member : value ∈ allocation.values) : value ∈ items := by
  induction count generalizing items allocation with
  | zero =>
    have same : allocation = ⟨[], items, []⟩ := by simpa [tracedAllocations] using allocated
    subst allocation
    cases member
  | succ count ih =>
    simp only [tracedAllocations, List.mem_flatMap, List.mem_map] at allocated
    obtain ⟨choice, chosen, tail, allocated, rfl⟩ := allocated
    simp only [Allocation.prepend, List.mem_cons] at member
    obtain ⟨found, _, residual⟩ := choice_valid chosen
    rcases member with rfl | later
    · exact List.mem_of_getElem? found
    · have contained := ih allocated later
      rw [residual] at contained
      split at contained
      · exact contained
      · exact (List.eraseIdx_sublist _ _).subset contained

def taskTargets : Task → List Pattern
  | .tree _ _ _ target => [target]
  | .arguments _ _ _ _ targets => targets
  | .restCapture _ _ _ _ targets => targets
  | .bag _ _ _ _ _ _ targets => targets
  | .bagSelect _ _ _ _ _ _ _ targets _ => targets

def TaskCovered (table : List String) (task : Task) : Prop :=
  ∀ target ∈ taskTargets task, Covered table target

def WorkCovered (table : List String) (work : Work) : Prop :=
  ∀ task ∈ work.tasks, TaskCovered table task

def StateCovered (table : List String) (state : State) : Prop :=
  ∀ work ∈ state.agenda, WorkCovered table work

theorem start_covered (table : List String) (request : Request)
    (covered : Covered table request.target) : StateCovered table (start request) := by
  simpa [StateCovered, WorkCovered, TaskCovered, taskTargets, start] using covered

theorem allocationWork_covered {table : List String} {path : List Nat} {depth : Nat}
    {initial : ScopedRuleMatching.Assignment} {kind : CollType} {schemas : List Pattern}
    {rest : Option String} {items : List Pattern} {allocation : Allocation Pattern} {work : Work}
    (covered : ∀ item ∈ items, Covered table item)
    (allocated : allocation ∈ tracedAllocations (kind == .hashSet) schemas.length items)
    (made : allocationWork path depth initial kind schemas rest allocation = some work) :
    WorkCovered table work := by
  have values : ∀ value ∈ allocation.values, Covered table value :=
    fun value member => covered value (allocation_value_mem allocated member)
  have residual : ∀ value ∈ arrange kind allocation.residual, Covered table value := by
    intro value member
    exact covered value ((tracedAllocations_residual_sublist allocated).subset ((arrange_mem _).mp member))
  cases rest with
  | none =>
    simp only [allocationWork] at made
    split at made
    · cases made
      simpa [WorkCovered, TaskCovered, taskTargets] using values
    · cases made
  | some name =>
    simp only [allocationWork, Option.some.injEq] at made
    subst work
    simpa [WorkCovered, TaskCovered, taskTargets] using And.intro values residual

private theorem ordinary_expand_covered (request : Request) (initial : ScopedRuleMatching.Assignment)
    (table : List String) (task : Task) (covered : TaskCovered table task)
    {branch : GeneralScopedMatchMachine.Work}
    (member : branch ∈ GeneralScopedMatchMachine.expand request initial task) :
    WorkCovered table (inheritWork branch) := by
  cases task with
  | tree path depth schema target =>
    have source : Covered table target := covered target (by simp [taskTargets])
    cases schema <;> cases target <;>
      simp only [GeneralScopedMatchMachine.expand] at member
    all_goals try split_ifs at member
    all_goals simp_all [WorkCovered, inheritWork, TaskCovered, taskTargets, Covered, names, mem_namesList]
    all_goals aesop (add safe forward [List.mem_of_mem_take, List.mem_of_mem_drop])
  | arguments path depth index schemas targets =>
    cases schemas <;> cases targets <;>
      simp_all [GeneralScopedMatchMachine.expand, WorkCovered, inheritWork, TaskCovered, taskTargets]
  | restCapture path depth name kind targets =>
    obtain ⟨final, _, rfl⟩ := List.mem_map.mp member
    simp [WorkCovered, inheritWork]
  | bag path depth index schemas rest kind targets =>
    cases schemas <;> cases rest <;>
      simp only [GeneralScopedMatchMachine.expand] at member
    all_goals try split_ifs at member
    all_goals simp_all [WorkCovered, inheritWork, TaskCovered, taskTargets]
  | bagSelect path depth index schema schemas rest kind targets selected =>
    cases found : targets[selected]? with
    | none => simp [GeneralScopedMatchMachine.expand, found] at member
    | some target =>
      simp only [GeneralScopedMatchMachine.expand, found, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simp only [WorkCovered, inheritWork, TaskCovered, taskTargets, List.mem_cons,
          List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨covered target (List.mem_of_getElem? found),
          fun value member => covered value ((List.eraseIdx_sublist _ _).subset member)⟩
      · exact fun task member => by
          have same : task = .bagSelect path depth index schema schemas rest kind targets (selected + 1) :=
            by simpa only [inheritWork, List.mem_singleton] using member
          subst task
          exact covered

theorem expand_covered (request : Request) (initial : ScopedRuleMatching.Assignment)
    (table : List String) (task : Task) (covered : TaskCovered table task)
    {branch : Work} (member : branch ∈ expand request initial task) : WorkCovered table branch := by
  unfold expand at member
  split at member
  next path depth kind schemas rest actual targets actualRest =>
    have source := covered (.collection actual targets actualRest) (by simp [taskTargets])
    have targetCoverage : ∀ target ∈ targets, Covered table target :=
      covered_elements.mp (fun name named => source name (List.mem_append_left _ named))
    split at member
    · split at member
      · obtain ⟨original, generated, rfl⟩ := List.mem_map.mp member
        exact ordinary_expand_covered request initial table _ covered generated
      · obtain ⟨allocation, allocated, made⟩ := List.mem_filterMap.mp member
        exact allocationWork_covered
          (fun value within => targetCoverage value ((arrange_mem _).mp within)) allocated made
    · cases member
  next =>
    obtain ⟨original, generated, rfl⟩ := List.mem_map.mp member
    exact ordinary_expand_covered request initial table _ covered generated
  next =>
    obtain ⟨original, generated, rfl⟩ := List.mem_map.mp member
    exact ordinary_expand_covered request initial table _ covered generated
  next =>
    obtain ⟨original, generated, rfl⟩ := List.mem_map.mp member
    exact ordinary_expand_covered request initial table _ covered generated
  next => cases member
  next => cases member

theorem advance_covered (request : Request) (table : List String) {work branch : Work}
    (covered : WorkCovered table work) (member : branch ∈ advance request work) :
    WorkCovered table branch := by
  cases taskList : work.tasks with
  | nil => simp [advance, taskList] at member
  | cons first remaining =>
    simp only [advance, taskList] at member
    obtain ⟨expanded, generated, rfl⟩ := List.mem_map.mp member
    have next := expand_covered request work.assignment table first
      (covered first (by simp [taskList])) generated
    intro task member
    rcases List.mem_append.mp member with earlier | later
    · exact next task earlier
    · exact covered task (by simp [taskList, later])

theorem tick_covered (request : Request) (table : List String) {state : State}
    (covered : StateCovered table state) : StateCovered table (tick request state) := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using covered
  | cons work remaining =>
    have first := covered work (by simp [agenda])
    have later : ∀ other ∈ remaining, WorkCovered table other :=
      fun other member => covered other (by simp [agenda, member])
    cases taskList : work.tasks with
    | nil => simpa only [StateCovered, tick, agenda, taskList] using later
    | cons task tasks =>
      intro branch member
      change branch ∈ (tick request state).agenda at member
      simp only [tick, agenda, taskList, List.mem_append] at member
      exact member.elim (advance_covered request table first) (later branch)

theorem run_covered (request : Request) (table : List String) (work : Nat) {state : State}
    (covered : StateCovered table state) : StateCovered table (run request work state) := by
  induction work generalizing state with
  | zero => exact covered
  | succ work ih => exact ih (tick_covered request table covered)

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine
