import Mettapedia.FluidDynamics.NavierStokes.ModeStateObservableClass
import Mettapedia.Cybernetics.ApproximateGeometricVisibility

/-!
# Finite observations and certified tail error

A prefix records the first `N` coefficients, without padding its representation
with zeros. Finite response sums reconstruct summable observations with a
uniform tail budget. Adding the zeroth coefficient requires a nonempty prefix.
The hard support detector instead has the sharp uniform error threshold `1/2`
at every finite depth. These are mathematical readouts, with no native numerical
implementation or execution authority attached.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteObservation

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.GeometricGoalCostControl
open Mettapedia.Cybernetics.ApproximateGeometricVisibility
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

/-- An empty prefix is valid; it observes no coordinates. -/
def prefixObserver (N : ℕ) : Observer ModeState (Fin N → ℝ) where
  observe x i := x.coeff i

/-- Finite evaluation uses just the supplied prefix. -/
def prefixSum (S : SummableCoordinateObservable) (N : ℕ) (view : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, S.response i (view i)

theorem prefixSum_observe (S : SummableCoordinateObservable) (N : ℕ) (x : ModeState) :
    prefixSum S N ((prefixObserver N).observe x) = S.partialSum N x := by
  exact Fin.sum_univ_eq_sum_range (fun n => S.response n (x.coeff n)) N

/-- The same finite evaluator serves signed, magnitude, and nonlinear observations. -/
def prefixReadout (S : SummableCoordinateObservable) (N : ℕ) :
    ApproximateValueReadout (ValueGeometry.ofPseudoMetric ℝ) S.value (prefixObserver N)
      (S.envelope.tailError N) where
  error_nonnegative := S.envelope.tailError_nonneg N
  run := prefixSum S N
  agrees x := by
    change |prefixSum S N ((prefixObserver N).observe x) - S.value x| ≤ _
    rw [prefixSum_observe]
    exact S.partial_error_le N x

/-- A nonempty prefix also reconstructs the statistic with the same error. -/
def statisticReadout (S : SummableCoordinateObservable) {N : ℕ} (positive : 0 < N) :
    ApproximateValueReadout (ValueGeometry.ofPseudoMetric ℝ) S.statistic (prefixObserver N)
      (S.envelope.tailError N) where
  error_nonnegative := S.envelope.tailError_nonneg N
  run view := view ⟨0, positive⟩ + prefixSum S N view
  agrees x := by
    change |x.coeff 0 + prefixSum S N ((prefixObserver N).observe x) -
      (x.coeff 0 + S.value x)| ≤ _
    rw [prefixSum_observe]
    simpa only [add_sub_add_left_eq_sub] using S.partial_error_le N x

/-- A vanishing envelope tail upgrades approximate reconstruction to exact factorization. -/
theorem zeroTail_visible (S : SummableCoordinateObservable) (N : ℕ)
    (zero : S.envelope.tailError N = 0) : ValueVisibleAt S.value (prefixObserver N) := by
  have readout : ApproximateValueReadout (ValueGeometry.ofPseudoMetric ℝ)
      S.value (prefixObserver N) 0 := zero ▸ prefixReadout S N
  exact readout.toExactOfZero (fun _ _ h => dist_eq_zero.mp h)

/-- A particular finite-support observation is reconstructed exactly, independently
of whether the envelope has a nonzero tail. -/
theorem value_eq_partial_of_tail_zero (S : SummableCoordinateObservable) (N : ℕ) (x : ModeState)
    (tail : ∀ n, N ≤ n → S.response n (x.coeff n) = 0) : S.value x = S.partialSum N x := by
  apply tsum_eq_sum
  intro n hn
  exact tail n (Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hn))

theorem zero_spike_same_prefix (N : ℕ) :
    (prefixObserver N).observe modeZero = (prefixObserver N).observe (tailSpikeMode N) := by
  funext i
  simp [prefixObserver, modeZero, tailSpikeMode, Nat.ne_of_lt i.isLt]

/-- Remote spikes force a half-unit error for every finite-prefix readout. The
constant midpoint attains the bound, so this obstruction is sharp. -/
theorem tailPresence_approximatelyVisible_iff (N : ℕ) (error : ℝ) :
    ApproximatelyVisibleAt (ValueGeometry.ofPseudoMetric ℝ) tailPresenceRadius
      (prefixObserver N) error ↔ (1 / 2 : ℝ) ≤ error := by
  constructor
  · rintro ⟨readout⟩
    have diameter := readout.fibre_distance_le_two_error
      (ValueGeometry.ofPseudoMetric_symmetric ℝ) modeZero (tailSpikeMode N)
      (zero_spike_same_prefix N)
    change dist (tailPresenceRadius modeZero) (tailPresenceRadius (tailSpikeMode N)) ≤ _ at diameter
    rw [tailPresenceRadius_modeZero, tailPresenceRadius_tailSpikeMode] at diameter
    norm_num [Real.dist_eq] at diameter
    linarith
  · intro bound
    refine ⟨⟨by linarith, fun _ => 1 / 2, ?_⟩⟩
    intro x
    change |(1 / 2 : ℝ) - tailPresenceRadius x| ≤ error
    unfold tailPresenceRadius
    split_ifs <;> norm_num <;> linarith

/-! ## Separating controls -/

/-- A signed linear observation whose finite sums decrease at its first term. -/
def negativeLinear : WeightedObservable where
  coeff n := -modeWeight n
  boundConst := 1
  boundConst_nonneg := zero_le_one
  coeff_bound n := by
    have nonneg : 0 ≤ modeWeight n := geometricModeWeights.weight_nonneg n
    simp only [abs_neg, abs_of_nonneg nonneg, one_mul, le_refl]

theorem signed_partial_not_monotone :
    ¬ Monotone (fun N => negativeLinear.toCoordinateObservable.partialSum N (tailSpikeMode 0)) := by
  intro monotone
  have h := monotone (show 0 ≤ 1 by omega)
  norm_num [SummableCoordinateObservable.partialSum, SummableCoordinateObservable.term,
    negativeLinear, WeightedObservable.toCoordinateObservable, modeWeight, tailSpikeMode,
    Finset.sum_range_succ] at h

/-- A nonzero response at zero still has valid partial-sum error bounds, but its
value on a zero-padded state need not be that partial sum. -/
def constantResponse : SummableCoordinateObservable where
  envelope := geometricModeWeights
  response n _ := modeWeight n
  continuous_response _ := continuous_const.continuousOn
  norm_response_le n _ _ := by
    change |modeWeight n| ≤ modeWeight n
    exact (abs_of_nonneg (geometricModeWeights.weight_nonneg n)).le

theorem zero_padding_ne_empty_sum :
    constantResponse.value (truncateModes 0 modeZero) ≠ constantResponse.partialSum 0 modeZero := by
  have total : constantResponse.value (truncateModes 0 modeZero) = 2 := by
    change (∑' n, modeWeight n) = 2
    have h := geometricModeWeights_tailError 0
    change (∑' n, modeWeight (n + 0)) = 2 * (1 / 2 : ℝ) ^ 0 at h
    simpa only [Nat.add_zero, pow_zero, mul_one] using h
  simp only [SummableCoordinateObservable.partialSum, Finset.range_zero, Finset.sum_empty]
  rw [total]
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.FiniteObservation
