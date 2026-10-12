import Mettapedia.Machines.ProducerSupport
import Mettapedia.Machines.PropagationSchedule

/-!
# Finite positive producer rounds

One generator copies its callees' current answer support into its own support.
A component runs these generators in a fixed order and repeats a complete
pass when any support changed. This is distinct from the existing rule-event
worklist. Its completion bound counts generator invocations, not native
instructions, answer transport, proof occurrences or index construction.

The laws cover finite ground positive copying dependencies. They neither
deduplicate an ordered proof stream nor establish the C scheduler's source,
ownership and suspension correspondence. The native controls supply a separate
comparison on this fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProducerRounds

open ConstraintPropagation

section Passes

variable {State Index : Type*} [PartialOrder State]

/-- A complete pass which changes nothing has stabilized every visited
inflationary operation, even if those operations do not commute. -/
theorem stable_pass_fixes_members (operations : Index → Propagator State)
    (schedule : List Index) (state : State)
    (stable : run operations schedule state = state) :
    ∀ index ∈ schedule, (operations index).apply state = state := by
  induction schedule generalizing state with
  | nil => simp
  | cons first rest ih =>
    have firstFixed : (operations first).apply state = state := by
      apply le_antisymm
      · exact (le_run operations rest _).trans_eq stable
      · exact (operations first).le_apply state
    have restFixed : run operations rest state = state := by
      simpa only [run, firstFixed] using stable
    intro index member
    rcases List.mem_cons.mp member with same | later
    · subst index
      exact firstFixed
    · exact ih state restFixed index later

theorem stable_pass_quiescent (operations : Index → Propagator State)
    (schedule : List Index) (covers : ∀ index, index ∈ schedule) (state : State)
    (stable : run operations schedule state = state) : Quiescent operations state :=
  fun index => stable_pass_fixes_members operations schedule state stable index (covers index)

end Passes

section Accounting

variable {State Index : Type*}

/-- Execute the generators and count their invocations together. -/
def runAccounted (operations : Index → State → State) : List Index → State → State × Nat
  | [], state => (state, 0)
  | index :: rest, state =>
      let later := runAccounted operations rest (operations index state)
      (later.1, later.2 + 1)

theorem runAccounted_state [PartialOrder State] (operations : Index → Propagator State)
    (schedule : List Index) (state : State) :
    (runAccounted (fun index => (operations index).apply) schedule state).1 =
      run operations schedule state := by
  induction schedule generalizing state with
  | nil => rfl
  | cons index rest ih => exact ih _

theorem runAccounted_invocations (operations : Index → State → State)
    (schedule : List Index) (state : State) :
    (runAccounted operations schedule state).2 = schedule.length := by
  induction schedule generalizing state with
  | nil => rfl
  | cons index rest ih => simp only [runAccounted, ih, List.length_cons]

end Accounting

section FinitePasses

variable {Fact Index : Type*} [DecidableEq Fact] [Fintype Fact]

/-- Stop on a stable complete pass, rather than interpreting exhausted fuel
as completion. The theorem below supplies enough fuel from the finite domain. -/
def iteratePasses (operations : Index → Propagator (Finset Fact)) (schedule : List Index) :
    Nat → Finset Fact → Finset Fact
  | 0, state => state
  | fuel + 1, state =>
      let next := run operations schedule state
      if next = state then state else iteratePasses operations schedule fuel next

def iterateAccounted (operations : Index → Propagator (Finset Fact))
    (schedule : List Index) : Nat → Finset Fact → Finset Fact × Nat
  | 0, state => (state, 0)
  | fuel + 1, state =>
      let pass := runAccounted (fun index => (operations index).apply) schedule state
      if pass.1 = state then (state, pass.2)
      else
        let later := iterateAccounted operations schedule fuel pass.1
        (later.1, pass.2 + later.2)

omit [Fintype Fact] in
theorem iterateAccounted_state (operations : Index → Propagator (Finset Fact))
    (schedule : List Index) (fuel : Nat) (state : Finset Fact) :
    (iterateAccounted operations schedule fuel state).1 =
      iteratePasses operations schedule fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [iterateAccounted, iteratePasses, runAccounted_state]
    split_ifs
    · rfl
    · exact ih _

omit [Fintype Fact] in
theorem iterateAccounted_bound (operations : Index → Propagator (Finset Fact))
    (schedule : List Index) (fuel : Nat) (state : Finset Fact) :
    (iterateAccounted operations schedule fuel state).2 ≤ fuel * schedule.length := by
  induction fuel generalizing state with
  | zero => simp only [iterateAccounted, Nat.zero_mul, le_refl]
  | succ fuel ih =>
    simp only [iterateAccounted]
    split_ifs
    · rw [runAccounted_invocations, Nat.succ_mul]
      omega
    · dsimp only
      rw [runAccounted_invocations, Nat.succ_mul]
      have remaining := ih
        (runAccounted (fun index => (operations index).apply) schedule state).1
      omega

omit [Fintype Fact] in
theorem subset_passes (operations : Index → Propagator (Finset Fact))
    (schedule : List Index) (fuel : Nat) (state : Finset Fact) :
    state ⊆ iteratePasses operations schedule fuel state := by
  induction fuel generalizing state with
  | zero => exact Finset.Subset.rfl
  | succ fuel ih =>
    simp only [iteratePasses]
    split_ifs
    · exact Finset.Subset.rfl
    · exact (le_run operations schedule state).trans (ih _)

omit [Fintype Fact] in
theorem passes_le_fixed (operations : Index → Propagator (Finset Fact))
    (schedule : List Index) (fuel : Nat) {state upper : Finset Fact}
    (bound : state ⊆ upper) (fixed : Quiescent operations upper) :
    iteratePasses operations schedule fuel state ⊆ upper := by
  induction fuel generalizing state with
  | zero => exact bound
  | succ fuel ih =>
    simp only [iteratePasses]
    split_ifs
    · exact bound
    · exact ih (run_le_fixed operations schedule bound fixed)

theorem passes_quiescent (operations : Index → Propagator (Finset Fact))
    (schedule : List Index) (covers : ∀ index, index ∈ schedule)
    (fuel : Nat) (state : Finset Fact)
    (enough : Fintype.card Fact - state.card + 1 ≤ fuel) :
    Quiescent operations (iteratePasses operations schedule fuel state) := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
    simp only [iteratePasses]
    split_ifs with stable
    · exact stable_pass_quiescent operations schedule covers state stable
    · have grows : state.card < (run operations schedule state).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨le_run operations schedule state, Ne.symm stable⟩)
      have finite := Finset.card_le_univ (run operations schedule state)
      apply ih
      omega

end FinitePasses

section Producers

variable {Key Item : Type*} [DecidableEq Key] [DecidableEq Item]
  [Fintype Key] [Fintype Item]

/-- The body reads a snapshot of all named callees, then appends their copied
answers. Every new answer belongs to the current source producer. -/
def copy (dependencies : Finset (Key × Key)) (source : Key)
    (state : Finset (Key × Item)) : Finset (Key × Item) :=
  state ∪ (state.filter fun answer => (source, answer.1) ∈ dependencies).image
    (fun answer => (source, answer.2))

def operation (dependencies : Finset (Key × Key)) (source : Key) :
    Propagator (Finset (Key × Item)) where
  apply := copy dependencies source
  le_apply := fun _ => Finset.subset_union_left
  monotone_apply := by
    intro state next extension
    apply Finset.union_subset_union extension
    apply Finset.image_subset_image
    exact Finset.filter_subset_filter _ extension

omit [Fintype Key] [Fintype Item] in
theorem quiescent_iff_model (dependencies : Finset (Key × Key))
    (state : Finset (Key × Item)) :
    Quiescent (operation dependencies) state ↔ Models (ProducerSupport.rules dependencies) state := by
  rw [ProducerSupport.models_iff_closed]
  constructor
  · intro fixed dependency member item present
    have emitted : (dependency.1, item) ∈ copy dependencies dependency.1 state := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr
        ⟨(dependency.2, item), Finset.mem_filter.mpr ⟨present, member⟩, rfl⟩
    have same := fixed dependency.1
    change copy dependencies dependency.1 state = state at same
    rw [same] at emitted
    exact emitted
  · intro closed source
    apply Finset.Subset.antisymm
    · intro answer member
      rcases Finset.mem_union.mp member with old | added
      · exact old
      · obtain ⟨callee, present, same⟩ := Finset.mem_image.mp added
        subst answer
        exact closed (source, callee.1) (Finset.mem_filter.mp present).2 callee.2
          (Finset.mem_filter.mp present).1
    · exact Finset.subset_union_left

def closure (dependencies : Finset (Key × Key)) (schedule : List Key)
    (seeds : Finset (Key × Item)) : Finset (Key × Item) :=
  iteratePasses (operation dependencies) schedule (Fintype.card (Key × Item) - seeds.card + 1) seeds

/-- Ordered component passes and the independent rule-event worklist compute
the same support. Their intermediate work and delivery order can differ. -/
theorem closure_eq_worklist (dependencies : Finset (Key × Key))
    (schedule : List Key) (covers : ∀ source, source ∈ schedule)
    (select : Selector (↥dependencies × Item)) (seeds : Finset (Key × Item)) :
    closure dependencies schedule seeds =
      solve (ProducerSupport.rules dependencies) select seeds := by
  obtain ⟨extension, model, least⟩ :=
    solve_least_model (ProducerSupport.rules dependencies) select seeds
  have fixed := (quiescent_iff_model dependencies _).mpr model
  have finished := passes_quiescent (operation dependencies) schedule covers
    (Fintype.card (Key × Item) - seeds.card + 1) seeds (le_refl _)
  apply Finset.Subset.antisymm
  · exact passes_le_fixed (operation dependencies) schedule _ extension fixed
  · exact least _ (subset_passes (operation dependencies) schedule _ seeds)
      ((quiescent_iff_model dependencies _).mp finished)

theorem closure_exact (dependencies : Finset (Key × Key))
    (schedule : List Key) (covers : ∀ source, source ∈ schedule)
    (select : Selector (↥dependencies × Item)) (seeds : Finset (Key × Item))
    (answer : Key × Item) :
    answer ∈ closure dependencies schedule seeds ↔
      ProducerSupport.Reachable dependencies seeds answer := by
  rw [closure_eq_worklist dependencies schedule covers select seeds]
  exact ProducerSupport.solve_exact dependencies select seeds answer

theorem closure_invocation_bound (dependencies : Finset (Key × Key))
    (schedule : List Key) (seeds : Finset (Key × Item)) :
    (iterateAccounted (operation dependencies) schedule
      (Fintype.card (Key × Item) - seeds.card + 1) seeds).2 ≤
      (Fintype.card (Key × Item) - seeds.card + 1) * schedule.length :=
  iterateAccounted_bound _ _ _ _

end Producers

section Controls

private def cycle : Finset (Fin 2 × Fin 1) := {(0, 0), (1, 0)}
private def dependencies : Finset (Fin 2 × Fin 2) := {(0, 1), (1, 0)}

theorem seeded_cycle_completes : closure dependencies [0, 1] {(0, 0)} = cycle := by
  decide

theorem empty_cycle_completes : closure dependencies [0, 1] ∅ = (∅ : Finset (Fin 2 × Fin 1)) := by
  decide

/-- A pass which omits a producer can appear stable before the component is
complete. Coverage is necessary, even on a finite positive cycle. -/
theorem incomplete_schedule_not_quiescent :
    ¬ Quiescent (operation dependencies)
      (closure dependencies [0] ({(0, 0)} : Finset (Fin 2 × Fin 1))) := by
  intro fixed
  have changes : (operation dependencies (1 : Fin 2)).apply
      (closure dependencies [0] ({(0, 0)} : Finset (Fin 2 × Fin 1))) ≠
      closure dependencies [0] ({(0, 0)} : Finset (Fin 2 × Fin 1)) := by decide
  exact changes (fixed 1)

/-- An invocation budget is not a completion certificate. -/
theorem exhausted_pass_not_quiescent :
    ¬ Quiescent (operation ({(2, 1), (1, 0)} : Finset (Fin 3 × Fin 3)))
      (iteratePasses (operation {(2, 1), (1, 0)}) [2, 1, 0] 1
        ({(0, 0)} : Finset (Fin 3 × Fin 1))) := by
  intro fixed
  have changes : (operation ({(2, 1), (1, 0)} : Finset (Fin 3 × Fin 3)) 2).apply
      (iteratePasses (operation {(2, 1), (1, 0)}) [2, 1, 0] 1
        ({(0, 0)} : Finset (Fin 3 × Fin 1))) ≠
      iteratePasses (operation {(2, 1), (1, 0)}) [2, 1, 0] 1
        ({(0, 0)} : Finset (Fin 3 × Fin 1)) := by decide
  exact changes (fixed 2)

end Controls

#print axioms passes_quiescent
#print axioms closure_eq_worklist
#print axioms closure_exact
#print axioms closure_invocation_bound

end Mettapedia.Machines.ProducerRounds
