import Mettapedia.Cybernetics.FeedbackDynamics
import Mettapedia.Cybernetics.ReflexiveValence

/-!
# Actual propagation trajectories and qualitative valence

The event predicates remain abstract, time-dependent interpretations.  A
propagation occurrence, however, is tied to a nonzero contribution in an
actual positive-network execution.  Environmental forcing and named
coordinates remain explicit.

A separating recurrent trajectory can have magnitudes that eventually fall
below every positive bound.  Thus existence of a self-sustaining qualitative
carrier is not a lower bound on its intensity.  Conversely, an environment
can keep producing positive activity even when there are no internal
propagation edges.  Neither control determines felt experience.

The reconstruction separates two aspects of the Garden of Minds ontology:
qualitative cascade structure and the dynamics of its continuation or
attenuation.  It does not identify pain with suffering or impose a single
signed value on their independently named coordinates.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.FeedbackDynamics

open Mettapedia.Cybernetics.ReflexiveValence

universe u

section General

variable {Coordinate : Type u} [Fintype Coordinate]

namespace Network

/-- Time and component distinguish occurrences.  A propagation edge records
a strictly positive internal contribution, independently of its experiential
classification. -/
def trajectory (network : Network Coordinate) (forcing : Nat → Coordinate → ℚ)
    (initial : Coordinate → ℚ)
    (separation formation reflection : Nat → Coordinate → Prop) :
    ReflexiveValence.System where
  Event := Nat × Coordinate
  propagates origin target := target.1 = origin.1 + 1 ∧
    0 < network.coefficient target.2 origin.2 ∧
    0 < network.run forcing initial origin.1 origin.2
  separates event := separation event.1 event.2
  forms event := formation event.1 event.2
  reflexiveRepresentation event := reflection event.1 event.2

/-- A witnessed internal contribution really makes its target coordinate
positive at the next time.  Nonnegative external input cannot cancel it. -/
theorem propagation_target_positive (network : Network Coordinate)
    {forcing : Nat → Coordinate → ℚ} {initial : Coordinate → ℚ}
    (environment : ∀ time coordinate, 0 ≤ forcing time coordinate)
    (current : ∀ coordinate, 0 ≤ initial coordinate)
    (separation formation reflection : Nat → Coordinate → Prop)
    {origin target : Nat × Coordinate}
    (edge : (network.trajectory forcing initial separation formation reflection).propagates
      origin target) :
    0 < network.run forcing initial target.1 target.2 := by
  rcases edge with ⟨nextTime, coefficientPositive, sourcePositive⟩
  rw [nextTime, run_succ, step]
  have nonnegative := network.run_nonnegative environment current origin.1
  have included : network.coefficient target.2 origin.2 *
      network.run forcing initial origin.1 origin.2 ≤
      ∑ source, network.coefficient target.2 source *
        network.run forcing initial origin.1 source :=
    Finset.single_le_sum
      (fun source _ => mul_nonneg (network.nonnegative target.2 source) (nonnegative source))
      (Finset.mem_univ origin.2)
  exact lt_of_lt_of_le (mul_pos coefficientPositive sourcePositive)
    (included.trans (le_add_of_nonneg_right (environment origin.1 target.2)))

/-- An edge-free network has no internal propagation path, even when its
environment continuously drives the coordinates. -/
theorem no_propagation_of_zero_coefficients (network : Network Coordinate)
    (zero : ∀ target source, network.coefficient target source = 0)
    (forcing : Nat → Coordinate → ℚ) (initial : Coordinate → ℚ)
    (separation formation reflection : Nat → Coordinate → Prop)
    {origin target : Nat × Coordinate} :
    ¬ Nonempty (PropagationPath
      (network.trajectory forcing initial separation formation reflection) origin target) := by
  rintro ⟨path⟩
  rcases path.containsEdge with ⟨first, second, _, coefficientPositive, _⟩
  rw [zero second.2 first.2] at coefficientPositive
  exact (lt_irrefl 0) coefficientPositive

end Network

end General

namespace Canary

def opposite : Coordinate → Coordinate
  | .signal => .recurrence
  | .recurrence => .signal

theorem opposite_ne (coordinate : Coordinate) : opposite coordinate ≠ coordinate := by
  cases coordinate <;> decide

/-- One explicitly chosen separating interpretation of the two-component
attenuating network.  Both classifications and reflexive location are stated. -/
def attenuatingTrajectory : ReflexiveValence.System :=
  (coupled (1 / 2) (by norm_num)).trajectory (fun _ => uniform 0) (uniform 1)
    (fun _ _ => True) (fun _ _ => False)
    (fun _ coordinate => coordinate = .recurrence)

theorem attenuating_positive (time : Nat) (coordinate : Coordinate) :
    0 < (coupled (1 / 2) (by norm_num)).run
      (fun _ => uniform 0) (uniform 1) time coordinate := by
  rw [coupled_half_attenuates]
  exact pow_pos (by norm_num) time

theorem attenuating_edge (time : Nat) (coordinate : Coordinate) :
    attenuatingTrajectory.propagates (time, coordinate) (time + 1, opposite coordinate) := by
  refine ⟨rfl, ?_, attenuating_positive time coordinate⟩
  change 0 < if opposite coordinate = coordinate then 0 else (1 / 2 : ℚ)
  rw [if_neg (opposite_ne coordinate)]
  norm_num

/-- The actual time-indexed activity has an endlessly continuing separation
carrier, although its magnitudes will tend below every positive envelope. -/
theorem attenuating_trajectory_sustained : Suffering attenuatingTrajectory := by
  refine ⟨{
    carrier := Set.univ
    inhabited := ⟨(0, Coordinate.signal), Set.mem_univ _⟩
    advances := ?_
    carries := ?_ }⟩
  · intro event _
    exact ⟨(event.1 + 1, opposite event.2), Set.mem_univ _,
      ⟨.edge (attenuating_edge event.1 event.2)⟩⟩
  · intro _ _
    trivial

theorem attenuating_trajectory_reflexive_pain :
    PainAt attenuatingTrajectory (1, Coordinate.recurrence) := by
  exact ⟨(0, Coordinate.signal), trivial,
    ⟨.edge (attenuating_edge 0 .signal)⟩, rfl, trivial⟩

theorem attenuating_below_any_positive_envelope {threshold : ℚ}
    (positive : 0 < threshold) :
    ∃ time, ∀ coordinate,
      (coupled (1 / 2) (by norm_num)).run (fun _ => uniform 0) (uniform 1)
        time coordinate < threshold := by
  apply (coupled (1 / 2) (by norm_num)).eventually_below
    (gain := 1 / 2) (bound := 1) (by norm_num) (by norm_num) (by norm_num)
  · intro coordinate
    cases coordinate <;> simp [coupled, Finset.univ, Fintype.elems]
  · intro _
    exact le_refl 1
  · exact positive

/-- Cascade existence does not imply a positive lower bound on magnitude.
This is a limitation of a purely qualitative criterion, not an assignment
of experienced suffering to this arithmetic system. -/
theorem sustained_structure_with_arbitrarily_small_magnitudes :
    Suffering attenuatingTrajectory ∧
      ∀ threshold : ℚ, 0 < threshold → ∃ time, ∀ coordinate,
        (coupled (1 / 2) (by norm_num)).run (fun _ => uniform 0) (uniform 1)
          time coordinate < threshold := by
  exact ⟨attenuating_trajectory_sustained,
    fun _ positive => attenuating_below_any_positive_envelope positive⟩

/-- Environmental maintenance is a different source of positive activity. -/
def externallyDrivenTrajectory : ReflexiveValence.System :=
  driven.trajectory (fun _ => uniform 1) (uniform 0)
    (fun _ _ => True) (fun _ _ => False) (fun _ _ => True)

theorem externally_driven_positive_without_internal_path (time : Nat)
    (coordinate : Coordinate) :
    driven.run (fun _ => uniform 1) (uniform 0) (time + 1) coordinate = 1 ∧
      ∀ origin target : externallyDrivenTrajectory.Event,
        ¬ Nonempty (PropagationPath externallyDrivenTrajectory origin target) := by
  refine ⟨external_forcing_persists time coordinate, ?_⟩
  intro origin target
  exact driven.no_propagation_of_zero_coefficients (by intros; rfl)
    _ _ _ _ _

end Canary

end Mettapedia.Cybernetics.FeedbackDynamics
