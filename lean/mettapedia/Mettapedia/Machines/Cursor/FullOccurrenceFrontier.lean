import Mettapedia.Machines.Cursor.OccurrenceMerge
import Mathlib.Order.Interval.Finset.Nat

/-!
# Full occurrence frontiers as bounded sequences

A clean occurrence index places each source position in exactly one leaf.
For a frontier of distinct leaves, the sum of their lengths certifies full
coverage if the positions are distinct and lie below the captured ceiling.
The resulting ordered cursor needs only its next position and that ceiling.

The counter and branch merge both map to the existing least-occurrence
reference provider. Their laws preserve reply-dependent bounded clients,
including pauses and residual control. The cardinality certificate is not
valid for overlapping leaves or stale coordinates; both have failing controls.
These are transition and coverage laws, not a proof of the native index's
representation invariant, C memory safety, or compiled instruction counts.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.FullOccurrenceFrontier

open Mettapedia.TypeTheory.IndexedPolynomial
open OccurrenceMerge

def Within (ceiling : Nat) (streams : List (List Nat)) : Prop :=
  ∀ position ∈ streams.flatten, position < ceiling

theorem full_coverage (ceiling : Nat) (streams : List (List Nat))
    (within : Within ceiling streams) (unique : streams.flatten.Nodup)
    (count : remaining streams = ceiling) :
    rows streams = Finset.range ceiling := by
  apply Finset.eq_of_subset_of_card_le
  · intro position member
    rw [rows_eq_flatten] at member
    exact Finset.mem_range.mpr (within position (List.mem_toFinset.mp member))
  · rw [Finset.card_range, rows_eq_flatten, List.toFinset_card_of_nodup unique]
    simpa [remaining, List.length_flatten] using count.ge

structure State where
  next : Nat
  ceiling : Nat
  deriving DecidableEq

def residual (state : State) : Finset Nat :=
  Finset.Ico state.next state.ceiling

def counterProvider : Provider (Sequence.protocol Nat) where
  State _ _ := State
  step state _ :=
    if state.next < state.ceiling then
      ⟨some state.next, ⟨state.next + 1, state.ceiling⟩⟩
    else
      ⟨none, state⟩

theorem residual_min (state : State) (live : state.next < state.ceiling) :
    (residual state).min' (Finset.nonempty_Ico.mpr live) = state.next := by
  apply (Finset.min'_eq_iff _ _ _).mpr
  exact ⟨Finset.mem_Ico.mpr ⟨le_rfl, live⟩,
    fun _ member => (Finset.mem_Ico.mp member).1⟩

def referenceHom : Hom counterProvider OccurrenceMerge.referenceProvider where
  map := residual
  step state _ := by
    by_cases live : state.next < state.ceiling
    · have nonempty : (residual state).Nonempty := Finset.nonempty_Ico.mpr live
      simp only [counterProvider, OccurrenceMerge.referenceProvider, live,
        nonempty, if_true, dite_true]
      rw [residual_min state live]
      congr 1
      exact Nat.Ico_succ_left_eq_erase_Ico
    · have empty : ¬ (residual state).Nonempty := by
        simpa [residual, Finset.nonempty_Ico] using live
      simp [counterProvider, OccurrenceMerge.referenceProvider, live, empty]

theorem bounded_client_observation {Return : Unit → Unit → Type}
    (client : Client (P := Sequence.protocol Nat) (Return := Return))
    (counterCost : Charge counterProvider)
    (referenceCost : Charge OccurrenceMerge.referenceProvider)
    (fuel : Nat) (packet : Packet counterProvider client ()) :
    referenceHom.outcome client
      (advance counterProvider client counterCost fuel packet).2 =
      (advance OccurrenceMerge.referenceProvider client referenceCost fuel
        (referenceHom.packet client packet)).2 :=
  Hom.advance client referenceHom counterCost referenceCost fuel packet

/-- The two cursor representations start at the same reference residual when
the native caller supplies the clean, bounded, unique-occurrence certificate. -/
theorem certified_initial_residual (ceiling : Nat) (streams : List (List Nat))
    (within : Within ceiling streams) (unique : streams.flatten.Nodup)
    (count : remaining streams = ceiling) :
    residual ⟨0, ceiling⟩ = rows streams := by
  rw [full_coverage ceiling streams within unique count]
  simp [residual, Nat.Ico_zero_eq_range]

/-- One successful pull consumes one position; reaching the ceiling is stable. -/
theorem successful_step (next ceiling : Nat) (live : next < ceiling) :
    counterProvider.step (base := ()) (index := ()) ⟨next, ceiling⟩ () =
      ⟨some next, ⟨next + 1, ceiling⟩⟩ := by
  simp [counterProvider, live]

theorem completed_step (next ceiling : Nat) (done : ceiling ≤ next) :
    counterProvider.step (base := ()) (index := ()) ⟨next, ceiling⟩ () =
      ⟨none, ⟨next, ceiling⟩⟩ := by
  simp [counterProvider, Nat.not_lt.mpr done]

namespace Controls

theorem interleaved_leaves_cover :
    rows [[0, 2, 4], [1, 3]] = Finset.range 5 := by
  apply full_coverage
  · simp [Within]
  · decide
  · decide

/-- Length alone cannot distinguish a duplicate position from a missing one. -/
theorem overlapping_count_is_insufficient :
    remaining [[0, 1], [1]] = 3 ∧ Within 3 [[0, 1], [1]] ∧
      rows [[0, 1], [1]] ≠ Finset.range 3 := by
  constructor
  · decide
  constructor
  · simp [Within]
  · decide

/-- Distinct stale coordinates can have the right length and the wrong range. -/
theorem stale_count_is_insufficient :
    remaining [[0, 1], [3]] = 3 ∧ ([[0, 1], [3]] : List (List Nat)).flatten.Nodup ∧
      rows [[0, 1], [3]] ≠ Finset.range 3 := by decide

theorem captured_ceiling_excludes_append :
    (counterProvider.step (base := ()) (index := ()) ⟨3, 3⟩ ()).1 = none ∧
      (counterProvider.step (base := ()) (index := ()) ⟨3, 4⟩ ()).1 = some 3 := by
  constructor <;> rfl

end Controls
end Mettapedia.Machines.Cursor.FullOccurrenceFrontier
