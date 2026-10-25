import Mathlib.Data.List.Basic

/-!
# A frontier machine for additive structural folds

A normalized source arm has a nonnegative integer weight and an ordered list
of proper recursive children. Metadata is not part of the algebra. The
frontier machine accumulates weights directly instead of returning an
intermediate integer through every recursive activation.

The proof covers this normalized algebra. Native source decoding, declaration
and constructor admission, scoped pointers, interruption and C conformance
remain implementation obligations. Visits count the expanded call tree;
physical DAG sharing may admit a stronger algorithmic bound.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.AdditiveTreeFold

inductive Tree (Metadata : Type) where
  | node (metadata : Metadata) (weight : Nat) (children : List (Tree Metadata))

variable {Metadata : Type}

mutual
  def source : Tree Metadata → Nat
    | .node _ weight children => weight + forest children
  termination_by tree => sizeOf tree

  def forest : List (Tree Metadata) → Nat
    | [] => 0
    | tree :: rest => source tree + forest rest
  termination_by trees => sizeOf trees
end

mutual
  def nodes : Tree Metadata → Nat
    | .node _ _ children => 1 + forestNodes children
  termination_by tree => sizeOf tree

  def forestNodes : List (Tree Metadata) → Nat
    | [] => 0
    | tree :: rest => nodes tree + forestNodes rest
  termination_by trees => sizeOf trees
end

@[simp] theorem forest_append (left right : List (Tree Metadata)) :
    forest (left ++ right) = forest left + forest right := by
  induction left with
  | nil => simp [forest]
  | cons head tail ih => simp [forest, ih, Nat.add_assoc]

@[simp] theorem forestNodes_append (left right : List (Tree Metadata)) :
    forestNodes (left ++ right) = forestNodes left + forestNodes right := by
  induction left with
  | nil => simp [forestNodes]
  | cons head tail ih => simp [forestNodes, ih, Nat.add_assoc]

structure State (Metadata : Type) where
  accumulated : Nat
  pending : List (Tree Metadata)

def step (state : State Metadata) : State Metadata :=
  match state.pending with
  | [] => state
  | .node _ weight children :: rest =>
      ⟨state.accumulated + weight, children ++ rest⟩

def meaning (state : State Metadata) : Nat :=
  state.accumulated + forest state.pending

theorem step_preserves (state : State Metadata) : meaning (step state) = meaning state := by
  rcases state with ⟨accumulated, pending⟩
  cases pending with
  | nil => rfl
  | cons tree rest =>
      cases tree
      simp [step, meaning, forest, source, Nat.add_assoc]

def run : Nat → State Metadata → State Metadata
  | 0, state => state
  | steps + 1, state => run steps (step state)

/-- Pausing does not alter the frontier's chronological continuation. -/
theorem run_add (first second : Nat) (state : State Metadata) :
    run second (run first state) = run (first + second) state := by
  induction first generalizing state with
  | zero => simp only [run, Nat.zero_add]
  | succ first ih =>
      simpa only [run, Nat.succ_add] using ih (step state)

theorem run_preserves (steps : Nat) (state : State Metadata) :
    meaning (run steps state) = meaning state := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih => exact (ih (step state)).trans (step_preserves state)

theorem forestNodes_zero (pending : List (Tree Metadata))
    (zero : forestNodes pending = 0) : pending = [] := by
  cases pending with
  | nil => rfl
  | cons tree rest => cases tree; simp [forestNodes, nodes] at zero

theorem step_decreases (state : State Metadata) (nonempty : state.pending ≠ []) :
    forestNodes (step state).pending + 1 = forestNodes state.pending := by
  rcases state with ⟨accumulated, pending⟩
  cases pending with
  | nil => exact (nonempty rfl).elim
  | cons tree rest =>
      cases tree
      simp [step, forestNodes, nodes, Nat.add_comm, Nat.add_left_comm]

theorem run_completes (steps : Nat) (state : State Metadata)
    (enough : forestNodes state.pending ≤ steps) : (run steps state).pending = [] := by
  induction steps generalizing state with
  | zero => exact forestNodes_zero _ (Nat.eq_zero_of_le_zero enough)
  | succ steps ih =>
      by_cases empty : state.pending = []
      · have same : step state = state := by simp [step, empty]
        simpa only [run, same] using ih state (by simp [empty, forestNodes])
      · have decreases := step_decreases state empty
        exact ih (step state) (by omega)

theorem result_exact (state : State Metadata) :
    (run (forestNodes state.pending) state).accumulated = meaning state := by
  have result := run_preserves (forestNodes state.pending) state
  simpa [meaning, run_completes _ state (Nat.le_refl _), forest] using result

/-- Every prefix accumulator is bounded by the final source value. -/
theorem prefix_bounded (steps maximum : Nat) (state : State Metadata)
    (bounded : meaning state ≤ maximum) :
    (run steps state).accumulated ≤ maximum := by
  have preserved := run_preserves steps state
  have lowerBound : (run steps state).accumulated ≤ meaning (run steps state) :=
    Nat.le_add_right _ _
  omega

/-- Repeated child occurrences are summed separately, even when their
metadata and immutable physical representation can be shared. -/
theorem duplicate_child_counted_twice (metadata : Metadata) (weight : Nat)
    (child : Tree Metadata) :
    source (.node metadata weight [child, child]) = weight + source child + source child := by
  simp [source, forest, Nat.add_assoc]

namespace Controls

def sample : Tree String := .node "ignored" 1 [.node "left" 2 [], .node "right" 3 []]

theorem complete_sum : (run 3 (State.mk 0 [sample])).accumulated = 6 := by decide

theorem prefix_not_complete : (run 1 (State.mk 0 [sample])).accumulated ≠ 6 := by decide

theorem sharing_is_not_deduplication :
    source (.node "root" 1 [.node "shared" 2 [], .node "shared" 2 []]) = 5 := by
  simp [source, forest]

end Controls
end Mettapedia.Machines.AdditiveTreeFold
