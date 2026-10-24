import Mettapedia.FluidDynamics.NavierStokes.ModeStateChartFork
import Mathlib.Analysis.PSeries

/-!
# Sobolev-Style Chart Fork on the Shared Mode State

Polynomial amplification `((n+1)^m)` precedes the bounded soft-support scalar.
The inverse-square envelope controls the response uniformly in `m`, with tail
error at most `1/N` for positive prefix length. Detecting any nonzero amplified
mode instead gives exactly the original hard support detector.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateSobolevChartFork

/-- Concrete inverse-square envelope on mode index. -/
def inverseSquareModeWeights : SummableModeWeights where
  weight n := 1 / ((n + 1 : ℝ) ^ (2 : ℕ))
  summable_weight := by
    simpa using (_root_.summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num))
  weight_nonneg := by
    intro n
    positivity

/-- Inverse-square truncation has a reciprocal uniform tail budget. -/
theorem inverseSquareModeWeights_tailError_le {N : ℕ} (hN : 0 < N) :
    inverseSquareModeWeights.tailError N ≤ 1 / (N : ℝ) := by
  have positive : (0 : ℝ) < N := by exact_mod_cast hN
  have finite (K : ℕ) :
      (∑ k ∈ Finset.range K, 1 / ((k : ℝ) + N + 1) ^ 2) ≤
        1 / (N : ℝ) - 1 / ((K : ℝ) + N) := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      rw [show (K : ℝ) + 1 + N = K + N + 1 by ring]
      have pos : (0 : ℝ) < K + N := by positivity
      have step : 1 / ((K : ℝ) + N + 1) ^ 2 ≤
          1 / ((K : ℝ) + N) - 1 / ((K : ℝ) + N + 1) := by
        field_simp
        nlinarith
      linarith
  have summable : Summable (fun k => inverseSquareModeWeights.weight (k + N)) :=
    (summable_nat_add_iff N).2 inverseSquareModeWeights.summable_weight
  apply le_of_tendsto summable.hasSum.tendsto_sum_nat
  filter_upwards with K
  have bound := finite K
  have nonneg : 0 ≤ 1 / ((K : ℝ) + N) := by positivity
  simpa [inverseSquareModeWeights, Nat.cast_add] using
    (bound.trans (sub_le_self _ nonneg))

/-- Polynomial Sobolev-style amplification of the `n`-th mode. -/
def sobolevAmplification (m : ℕ) (x : ModeState) (n : ℕ) : ℝ :=
  ((n + 1 : ℝ) ^ m) * x.coeff n

/-- Soft Sobolev-weighted mode contribution. -/
def softSobolevTerm (m : ℕ) (x : ModeState) (n : ℕ) : ℝ :=
  softSupportScalar (sobolevAmplification m x n) * inverseSquareModeWeights.weight n

/-- Soft Sobolev chart radius. -/
def softSobolevRadius (m : ℕ) (x : ModeState) : ℝ :=
  ∑' n, softSobolevTerm m x n

/-- Zeroth visible mode plus the soft Sobolev radius. -/
def softSobolevStatistic (m : ℕ) (x : ModeState) : ℝ :=
  x.coeff 0 + softSobolevRadius m x

/-- Hard Sobolev chart radius: any nonzero amplified mode is counted as present. -/
def hardSobolevRadius (m : ℕ) (x : ModeState) : ℝ :=
  if ∃ n, sobolevAmplification m x n ≠ 0 then 1 else 0

theorem continuous_sobolevAmplification (m n : ℕ) :
    Continuous fun x : ModeState => sobolevAmplification m x n := by
  exact (continuous_const : Continuous fun _ : ModeState => ((n + 1 : ℝ) ^ m)).mul
      (continuous_coeffObservable n)

/-- The soft Sobolev family uses the same bounded scalar with polynomial amplification. -/
def softSobolevObservable (m : ℕ) : SummableCoordinateObservable :=
  softSupportObservable inverseSquareModeWeights (fun n => (n + 1 : ℝ) ^ m)

theorem continuous_softSobolevRadius (m : ℕ) : Continuous (softSobolevRadius m) :=
  (softSobolevObservable m).continuous_value

theorem hardSobolevRadius_eq_hardSupportRadius (m : ℕ) :
    hardSobolevRadius m = hardSupportRadius := by
  funext x
  have key (n : ℕ) : sobolevAmplification m x n ≠ 0 ↔ x.coeff n ≠ 0 := by
    exact mul_ne_zero_iff.trans (and_iff_right (by positivity))
  simp only [hardSobolevRadius, key, hardSupportRadius, tailPresenceRadius]

theorem not_continuousAt_hardSobolevRadius_modeZero (m : ℕ) :
    ¬ ContinuousAt (hardSobolevRadius m) modeZero := by
  rw [hardSobolevRadius_eq_hardSupportRadius m]
  exact not_continuousAt_hardSupportRadius_modeZero

theorem not_continuousAt_hardSobolev_cutoffPotential_modeZero (m : ℕ) :
    ¬ ContinuousAt
      (cutoffPotential (fun r => r) (hardSobolevRadius m) unitStatisticMode)
      modeZero := by
  rw [hardSobolevRadius_eq_hardSupportRadius m]
  exact not_continuousAt_hardSupport_cutoffPotential_modeZero

theorem not_continuousAt_hardSobolev_coleHopfPhi_modeZero (m : ℕ) :
    ¬ ContinuousAt
      (coleHopfPhi 1 (cutoffPotential (fun r => r) (hardSobolevRadius m) unitStatisticMode))
      modeZero := by
  rw [hardSobolevRadius_eq_hardSupportRadius m]
  exact not_continuousAt_hardSupport_coleHopfPhi_modeZero

end ModeStateSobolevChartFork

end NavierStokes
end FluidDynamics
end Mettapedia
