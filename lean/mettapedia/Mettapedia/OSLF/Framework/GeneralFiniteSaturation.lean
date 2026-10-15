import Mettapedia.OSLF.Framework.ResumableEquationCoverage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Earned finite saturation of the actual resumable queue

The executable work allowance is calculated from a finite closed carrier and
its actual one-step equation batches. Each representative is scanned at most
once. A newly scanned representative pays for all of its discoveries; a
repeated queue entry consumes one pending slot. This proves termination without
assuming a globally complete frontier or supplying a hand-written bound.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneralFiniteSaturation

open ResumableEquationOccurrenceFrontier
open scoped BigOperators

universe u v w z
variable {Node : Type u} {EquationOrigin : Type v} {Occurrence : Type w} {Obligation : Type z}
variable [DecidableEq Node]

def unseen (carrier : Finset Node) (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) :
    Finset Node := carrier.filter (fun node => node ∉ snapshot.visited.map Entry.state)

def allowance (model : Model Node EquationOrigin Occurrence Obligation) (carrier : Finset Node)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) : Nat :=
  snapshot.pending.length + (unseen carrier snapshot).sum (fun node => (model.equations node).answers.length + 1)

def PendingWithin (carrier : Finset Node) (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) : Prop :=
  ∀ entry ∈ snapshot.pending, entry.state ∈ carrier

def NeighborClosed (model : Model Node EquationOrigin Occurrence Obligation) (carrier : Finset Node) : Prop :=
  ∀ node ∈ carrier, ∀ answer ∈ (model.equations node).answers, answer.2 ∈ carrier

def ResolvedOn (model : Model Node EquationOrigin Occurrence Obligation) (carrier : Finset Node) : Prop :=
  ∀ node ∈ carrier, (model.equations node).unresolved = [] ∧ (model.firings node).unresolved = []

theorem tick_pendingWithin (model : Model Node EquationOrigin Occurrence Obligation) (carrier : Finset Node)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) (closed : NeighborClosed model carrier)
    (pending : PendingWithin carrier snapshot) : PendingWithin carrier (tick model snapshot) := by
  cases queue : snapshot.pending with
  | nil => simpa only [tick, queue] using pending
  | cons entry rest =>
      have first := pending entry (by simp [queue])
      have tail : ∀ item ∈ rest, item.state ∈ carrier := by
        intro item member
        exact pending item (by simp [queue, member])
      by_cases seen : entry.state ∈ snapshot.visited.map Entry.state
      · simpa only [tick, queue, seen, ↓reduceIte, PendingWithin] using tail
      · intro item member
        simp only [tick, queue, seen, ↓reduceIte, List.mem_append, List.mem_filter] at member
        rcases member with later | ⟨discovered, _⟩
        · exact tail item later
        · obtain ⟨answer, present, equal⟩ := List.mem_map.mp discovered
          subst item
          exact closed entry.state first answer present

theorem tick_parked_nil (model : Model Node EquationOrigin Occurrence Obligation) (carrier : Finset Node)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) (resolved : ResolvedOn model carrier)
    (pending : PendingWithin carrier snapshot) (parked : snapshot.parked = []) :
    (tick model snapshot).parked = [] := by
  cases queue : snapshot.pending with
  | nil => simpa only [tick, queue] using parked
  | cons entry rest =>
      have batches := resolved entry.state (pending entry (by simp [queue]))
      by_cases seen : entry.state ∈ snapshot.visited.map Entry.state
      · simpa only [tick, queue, seen, ↓reduceIte] using parked
      · simp only [tick, queue, seen, ↓reduceIte, parked, batches.1, batches.2,
          obligations, List.map_nil, List.append_nil]

theorem unseen_append (carrier : Finset Node) (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (entry : Entry Node EquationOrigin) (rest : List (Entry Node EquationOrigin))
    (_fresh : entry.state ∉ snapshot.visited.map Entry.state) :
    unseen carrier {snapshot with pending := rest, visited := snapshot.visited ++ [entry]} =
      (unseen carrier snapshot).erase entry.state := by
  ext node
  simp only [unseen, Finset.mem_filter, List.map_append, List.map_singleton,
    List.mem_append, List.mem_singleton, Finset.mem_erase]
  tauto

theorem tick_allowance_lt (model : Model Node EquationOrigin Occurrence Obligation) (carrier : Finset Node)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (pending : PendingWithin carrier snapshot) (active : snapshot.pending ≠ []) :
    allowance model carrier (tick model snapshot) < allowance model carrier snapshot := by
  cases queue : snapshot.pending with
  | nil => exact (active queue).elim
  | cons entry rest =>
      by_cases seen : entry.state ∈ snapshot.visited.map Entry.state
      · simp only [allowance, tick, queue, seen, ↓reduceIte, unseen, List.length_cons]
        omega
      · have first := pending entry (by simp [queue])
        have member : entry.state ∈ unseen carrier snapshot := Finset.mem_filter.mpr ⟨first, seen⟩
        have sum := Finset.add_sum_erase (unseen carrier snapshot)
          (fun node => (model.equations node).answers.length + 1) member
        have erased : unseen carrier (tick model snapshot) = (unseen carrier snapshot).erase entry.state := by
          ext node
          simp only [unseen, tick, queue, seen, ↓reduceIte, Finset.mem_filter,
            List.map_append, List.map_singleton, List.mem_append, List.mem_singleton, Finset.mem_erase]
          tauto
        have bounded := List.length_filter_le
          (fun candidate : Entry Node EquationOrigin =>
            decide (candidate.state ∉ entry.state :: (snapshot.visited.map Entry.state ++ rest.map Entry.state)))
          (discoveries entry (model.equations entry.state).answers)
        have length : (discoveries entry (model.equations entry.state).answers).length =
            (model.equations entry.state).answers.length := by simp only [discoveries, List.length_map]
        unfold allowance
        rw [erased]
        simp only [tick, queue, seen, ↓reduceIte, List.length_append, List.length_cons]
        omega

theorem run_nil_pending (model : Model Node EquationOrigin Occurrence Obligation)
    (fuel : Nat) (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (empty : snapshot.pending = []) : run model fuel snapshot = snapshot := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run, tick, empty] using ih

theorem run_exhausts_pending (model : Model Node EquationOrigin Occurrence Obligation) (carrier : Finset Node)
    (fuel : Nat) (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (closed : NeighborClosed model carrier) (pending : PendingWithin carrier snapshot)
    (sufficient : allowance model carrier snapshot ≤ fuel) : (run model fuel snapshot).pending = [] := by
  induction fuel generalizing snapshot with
  | zero =>
      have length : snapshot.pending.length = 0 := by unfold allowance at sufficient; omega
      simpa only [run] using List.length_eq_zero_iff.mp length
  | succ fuel ih =>
      by_cases empty : snapshot.pending = []
      · simpa only [run_nil_pending model (fuel + 1) snapshot empty] using empty
      · have decrease := tick_allowance_lt model carrier snapshot pending empty
        exact ih (tick model snapshot) (tick_pendingWithin model carrier snapshot closed pending) (by omega)

theorem run_parked_nil (model : Model Node EquationOrigin Occurrence Obligation) (carrier : Finset Node)
    (fuel : Nat) (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (closed : NeighborClosed model carrier) (resolved : ResolvedOn model carrier)
    (pending : PendingWithin carrier snapshot) (parked : snapshot.parked = []) :
    (run model fuel snapshot).parked = [] := by
  induction fuel generalizing snapshot with
  | zero => exact parked
  | succ fuel ih =>
      exact ih (tick model snapshot) (tick_pendingWithin model carrier snapshot closed pending)
        (tick_parked_nil model carrier snapshot resolved pending parked)

/-- A derived executable allowance, not a presumed completeness field. -/
def sourceAllowance (model : Model Node EquationOrigin Occurrence Obligation) (carrier : Finset Node)
    (source : Node) : Nat := allowance model carrier (initial source)

theorem source_quiescent (model : Model Node EquationOrigin Occurrence Obligation) (carrier : Finset Node)
    (source : Node) (within : source ∈ carrier) (closed : NeighborClosed model carrier)
    (resolved : ResolvedOn model carrier) :
    quiescent (run model (sourceAllowance model carrier source) (initial source)) = true := by
  have pending : PendingWithin carrier (initial source : Snapshot Node EquationOrigin Occurrence Obligation) := by
    intro entry member
    simp only [initial, List.mem_singleton] at member
    subst entry
    exact within
  apply (quiescent_iff _).mpr
  exact ⟨run_exhausts_pending model carrier _ _ closed pending (Nat.le_refl _),
    run_parked_nil model carrier _ _ closed resolved pending rfl⟩

end Mettapedia.OSLF.Framework.GeneralFiniteSaturation
