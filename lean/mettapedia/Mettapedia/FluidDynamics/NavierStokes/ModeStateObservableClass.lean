import Mettapedia.FluidDynamics.NavierStokes.ModeStateProductTopologyObstruction
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Summable Observable Class on the Shared Mode State

Coordinate responses may be signed and are continuous on `[-1,1]`. A summable
nonnegative envelope gives continuity, uniform finite-prefix error bounds, and
convergence. Zero padding represents a partial sum only when each response
vanishes at zero. Weighted magnitudes, squares, and linear observations are
instances; no computability or floating-point claim is made.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section ModeStateObservableClass

/-- Nonnegative summable mode weights define a good observable class on
`ModeState`. -/
structure SummableModeWeights where
  weight : ℕ → ℝ
  summable_weight : Summable weight
  weight_nonneg : ∀ n, 0 ≤ weight n

/-- A separable observation with a summable envelope. Responses may be signed
and need only be continuous on the admissible coefficient interval. -/
structure SummableCoordinateObservable where
  envelope : SummableModeWeights
  response : ℕ → ℝ → ℝ
  continuous_response : ∀ n, ContinuousOn (response n) (Set.Icc (-1) 1)
  norm_response_le : ∀ n t, |t| ≤ 1 → ‖response n t‖ ≤ envelope.weight n

namespace SummableModeWeights

/-- Uniform budget for the coordinates omitted by a length-`N` prefix. -/
def tailError (W : SummableModeWeights) (N : ℕ) : ℝ := ∑' k, W.weight (k + N)

theorem tailError_nonneg (W : SummableModeWeights) (N : ℕ) : 0 ≤ W.tailError N :=
  tsum_nonneg (fun k => W.weight_nonneg (k + N))

theorem tailError_eq_sub (W : SummableModeWeights) (N : ℕ) :
    W.tailError N = (∑' n, W.weight n) - ∑ n ∈ Finset.range N, W.weight n := by
  have h := Summable.sum_add_tsum_nat_add N W.summable_weight
  dsimp [tailError]
  linarith

theorem tendsto_tailError (W : SummableModeWeights) :
    Tendsto W.tailError Filter.atTop (nhds 0) := by
  change Tendsto (fun N => W.tailError N) Filter.atTop (nhds 0)
  simp_rw [tailError_eq_sub]
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∑' n, W.weight n)
    Filter.atTop (nhds (∑' n, W.weight n))).sub W.summable_weight.hasSum.tendsto_sum_nat

theorem tailError_antitone (W : SummableModeWeights) : Antitone W.tailError := by
  apply antitone_nat_of_succ_le
  intro N
  rw [W.tailError_eq_sub (N + 1), W.tailError_eq_sub N, Finset.sum_range_succ]
  linarith [W.weight_nonneg N]

end SummableModeWeights

/-- Weighted `n`-th mode contribution. -/
def weightedModeTerm (W : SummableModeWeights) (x : ModeState) (n : ℕ) : ℝ :=
  |x.coeff n| * W.weight n

/-- Weighted radius observable. -/
def weightedModeRadius (W : SummableModeWeights) (x : ModeState) : ℝ :=
  ∑' n, weightedModeTerm W x n

/-- Zeroth visible mode plus the weighted radius. -/
def weightedModeStatistic (W : SummableModeWeights) (x : ModeState) : ℝ :=
  x.coeff 0 + weightedModeRadius W x

theorem continuous_coeffObservable (n : ℕ) :
    Continuous fun x : ModeState => x.coeff n := by
  exact (continuous_apply n).comp continuous_induced_dom

namespace SummableCoordinateObservable

def term (S : SummableCoordinateObservable) (x : ModeState) (n : ℕ) : ℝ :=
  S.response n (x.coeff n)

def value (S : SummableCoordinateObservable) (x : ModeState) : ℝ := ∑' n, S.term x n

def partialSum (S : SummableCoordinateObservable) (N : ℕ) (x : ModeState) : ℝ :=
  ∑ n ∈ Finset.range N, S.term x n

def statistic (S : SummableCoordinateObservable) (x : ModeState) : ℝ := x.coeff 0 + S.value x

theorem norm_term_le (S : SummableCoordinateObservable) (x : ModeState) (n : ℕ) :
    ‖S.term x n‖ ≤ S.envelope.weight n := S.norm_response_le n _ (x.abs_le_one n)

theorem summable_term (S : SummableCoordinateObservable) (x : ModeState) :
    Summable (S.term x) := Summable.of_norm_bounded S.envelope.summable_weight (S.norm_term_le x)

theorem abs_value_le (S : SummableCoordinateObservable) (x : ModeState) :
    |S.value x| ≤ ∑' n, S.envelope.weight n := by
  simpa only [Real.norm_eq_abs, value] using (S.summable_term x).hasSum.norm_le_of_bounded
    S.envelope.summable_weight.hasSum (S.norm_term_le x)

theorem continuous_term (S : SummableCoordinateObservable) (n : ℕ) :
    Continuous (fun x => S.term x n) :=
  (S.continuous_response n).comp_continuous (continuous_coeffObservable n)
    (fun x => (abs_le.mp (x.abs_le_one n)))

theorem continuous_value (S : SummableCoordinateObservable) : Continuous S.value :=
  continuous_tsum S.continuous_term S.envelope.summable_weight (fun n x => S.norm_term_le x n)

theorem continuous_statistic (S : SummableCoordinateObservable) : Continuous S.statistic :=
  (continuous_coeffObservable 0).add S.continuous_value

/-- The supplied finite partial sum approximates the independently defined
infinite sum uniformly, including signed observations. -/
theorem partial_error_le (S : SummableCoordinateObservable) (N : ℕ) (x : ModeState) :
    |S.partialSum N x - S.value x| ≤ S.envelope.tailError N := by
  have split : S.partialSum N x + (∑' k, S.term x (k + N)) = S.value x :=
    Summable.sum_add_tsum_nat_add N (S.summable_term x)
  have difference : S.partialSum N x - S.value x = -(∑' k, S.term x (k + N)) := by linarith
  rw [difference, abs_neg]
  have terms : Summable (fun k => S.term x (k + N)) := (summable_nat_add_iff N).2 (S.summable_term x)
  have weights : Summable (fun k => S.envelope.weight (k + N)) :=
    (summable_nat_add_iff N).2 S.envelope.summable_weight
  simpa only [Real.norm_eq_abs, SummableModeWeights.tailError] using
    terms.hasSum.norm_le_of_bounded weights.hasSum (fun k => S.norm_term_le x (k + N))

theorem tendstoUniformly_partial (S : SummableCoordinateObservable) :
    TendstoUniformly S.partialSum S.value Filter.atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [S.envelope.tendsto_tailError.eventually (gt_mem_nhds hε)] with N hN x
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (S.partial_error_le N x) hN

/-- Zero padding equals discarding the tail only for responses vanishing at zero. -/
theorem value_truncate_eq_partial (S : SummableCoordinateObservable)
    (zero : ∀ n, S.response n 0 = 0) (N : ℕ) (x : ModeState) :
    S.value (truncateModes N x) = S.partialSum N x := by
  rw [value, tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [term, truncateModes, Finset.mem_range.mp hn]
  · intro n hn
    have outside : ¬ n < N := by simpa only [Finset.mem_range] using hn
    simp [term, truncateModes, zero, outside]

/-- A single supported coordinate is observed without any tail error. -/
theorem value_spike (S : SummableCoordinateObservable) (zero : ∀ n, S.response n 0 = 0)
    (N : ℕ) : S.value (tailSpikeMode N) = S.response N 1 := by
  rw [value, tsum_eq_single N]
  · simp [term, tailSpikeMode]
  · intro n hn
    simp [term, tailSpikeMode, hn, zero]

def approximationData (S : SummableCoordinateObservable) :
    CutoffApproximationData S.value S.statistic where
  approx := truncateModes
  radius_tendsto x := S.continuous_value.continuousAt.tendsto.comp (tendsto_truncateModes_modeState x)
  statistic_tendsto x := S.continuous_statistic.continuousAt.tendsto.comp (tendsto_truncateModes_modeState x)

end SummableCoordinateObservable

/-- Weighted magnitude as a coordinate observation. -/
def absModeObservable (W : SummableModeWeights) : SummableCoordinateObservable where
  envelope := W
  response n t := |t| * W.weight n
  continuous_response n := (continuous_abs.mul continuous_const).continuousOn
  norm_response_le n t ht := by
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (W.weight_nonneg n)]
    simpa using mul_le_mul_of_nonneg_right ht (W.weight_nonneg n)

/-- Weighted square as a coordinate observation. -/
def squareModeObservable (W : SummableModeWeights) : SummableCoordinateObservable where
  envelope := W
  response n t := t ^ 2 * W.weight n
  continuous_response n := ((continuous_id.pow 2).mul continuous_const).continuousOn
  norm_response_le n t ht := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (W.weight_nonneg n))]
    simpa using mul_le_mul_of_nonneg_right
      ((sq_le_one_iff_abs_le_one t).mpr ht) (W.weight_nonneg n)

/-- The original geometric weights as an instance of the good observable class. -/
def geometricModeWeights : SummableModeWeights where
  weight := modeWeight
  summable_weight := summable_modeWeight
  weight_nonneg := by
    intro n
    have hpow : 0 ≤ (2 : ℝ) ^ n := by positivity
    unfold modeWeight
    exact inv_nonneg.mpr hpow

theorem weightedModeTerm_geometric_eq_modeTerm (x : ModeState) (n : ℕ) :
    weightedModeTerm geometricModeWeights x n = modeTerm x n := by
  simp [weightedModeTerm, geometricModeWeights, modeTerm]

theorem weightedModeRadius_geometric_eq_modeRadius :
    weightedModeRadius geometricModeWeights = modeRadius := by
  funext x
  simp [weightedModeRadius, weightedModeTerm, geometricModeWeights, modeRadius, modeTerm]

theorem weightedModeStatistic_geometric_eq_modeStatistic :
    weightedModeStatistic geometricModeWeights = modeStatistic := by
  funext x
  simp [weightedModeStatistic, modeStatistic, weightedModeRadius_geometric_eq_modeRadius]

/-- Exact geometric tail budget, including the empty prefix. -/
theorem geometricModeWeights_tailError (N : ℕ) :
    geometricModeWeights.tailError N = 2 * (1 / 2 : ℝ) ^ N := by
  simp only [SummableModeWeights.tailError, geometricModeWeights, modeWeight,
    pow_add, mul_inv_rev]
  rw [tsum_mul_left]
  simp_rw [← inv_pow]
  rw [tsum_geometric_of_abs_lt_one (by norm_num : |(2 : ℝ)⁻¹| < 1)]
  norm_num [mul_comm]

/-- Coefficients of a bounded signed linear observation. -/
structure WeightedObservable where
  coeff : ℕ → ℝ
  boundConst : ℝ
  boundConst_nonneg : 0 ≤ boundConst
  coeff_bound : ∀ n, |coeff n| ≤ boundConst * modeWeight n

def observableTerm (L : WeightedObservable) (x : ModeState) (n : ℕ) : ℝ := L.coeff n * x.coeff n

def matchingObservable (L : WeightedObservable) (x : ModeState) : ℝ := ∑' n, observableTerm L x n

def observableEnvelope (L : WeightedObservable) (n : ℕ) : ℝ := L.boundConst * modeWeight n

def observableEnvelopeSum (L : WeightedObservable) : ℝ := ∑' n, observableEnvelope L n

/-- The linear formula, interpreted in the common coordinate-observation class. -/
def WeightedObservable.toCoordinateObservable (L : WeightedObservable) :
    SummableCoordinateObservable where
  envelope := ⟨observableEnvelope L, summable_modeWeight.mul_left L.boundConst,
    fun n => mul_nonneg L.boundConst_nonneg (geometricModeWeights.weight_nonneg n)⟩
  response n t := L.coeff n * t
  continuous_response n := (continuous_const.mul continuous_id).continuousOn
  norm_response_le n t ht := by
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) ht).trans (L.coeff_bound n)

theorem matchingObservable_abs_le (L : WeightedObservable) (x : ModeState) :
    |matchingObservable L x| ≤ observableEnvelopeSum L := L.toCoordinateObservable.abs_value_le x

theorem matchingObservable_truncate_eq_sum (L : WeightedObservable) (x : ModeState) (N : ℕ) :
    matchingObservable L (truncateModes N x) = ∑ n ∈ Finset.range N, observableTerm L x n :=
  L.toCoordinateObservable.value_truncate_eq_partial (by simp [WeightedObservable.toCoordinateObservable]) N x

theorem truncateModes_matchingObservable_tendsto (L : WeightedObservable) (x : ModeState) :
    Tendsto (fun N => matchingObservable L (truncateModes N x)) atTop (nhds (matchingObservable L x)) :=
  L.toCoordinateObservable.approximationData.radius_tendsto x

end ModeStateObservableClass

end NavierStokes
end FluidDynamics
end Mettapedia
