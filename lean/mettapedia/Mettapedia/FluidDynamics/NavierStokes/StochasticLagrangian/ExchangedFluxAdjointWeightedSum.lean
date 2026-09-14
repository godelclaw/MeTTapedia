import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxAdjointSquareSum

/-!
# Weighted square sums of the actual nonlinear adjoint

An order `m` test norm is controlled by order `m + 1` output coefficients
and absolute order `m + 1` curl moments. These are explicit regularity
requirements, not an initial-data or global dynamical budget. In particular,
the order-one estimate has the reciprocal weight needed by the heat
commutator pairing, but its right-hand side still requires control.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjointWeightedSum

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeGalerkinKineticEnergy PancakeCurlOutputTail PancakeIndexedFourierMoments
open PancakeHigherDerivativeMoments ExchangedFluxAdjointSeries ExchangedFluxAdjointSquareSum
open PeriodicTensorFourierFrame

local notation "H" => Mettapedia.Analysis.UnitTorusGradientProjection.TensorL2
  (Fin 3) (EuclideanSpace ℝ (Fin 3))

def weightedCurlNorm (m : ℕ) (u : FourierVelocity) (k : Wavevector) : ℝ :=
  (1 + ‖frequencyVec k‖) ^ m * ‖fourierCurl u k‖

def weightedOutputNorm (m : ℕ) (F : H) (n : Wavevector) : ℝ :=
  (1 + ‖frequencyVec n‖) ^ m * ‖outputCoefficient F n‖

theorem weightedCurlNorm_nonneg (m : ℕ) (u : FourierVelocity) (k : Wavevector) :
    0 ≤ weightedCurlNorm m u k := by unfold weightedCurlNorm; positivity

theorem weightedOutputNorm_nonneg (m : ℕ) (F : H) (n : Wavevector) :
    0 ≤ weightedOutputNorm m F n := by unfold weightedOutputNorm; positivity

theorem weightedCurlNorm_le_fourierMoment (m : ℕ) (u : FourierVelocity) (k : Wavevector) :
    weightedCurlNorm m u k ≤ (2 * Real.pi) * fourierMoment (m + 1) u k := by
  have hc := (norm_coefficient_sup_le_euclidean (fourierCurl u k)).trans (norm_fourierCurl_le u k)
  calc
    _ ≤ (1 + ‖frequencyVec k‖) ^ m *
        ((2 * Real.pi) * ‖frequencyVec k‖ * ‖coefficientVec (u k)‖) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ (1 + ‖frequencyVec k‖) ^ m *
        ((2 * Real.pi) * (1 + ‖frequencyVec k‖) * ‖coefficientVec (u k)‖) := by
      gcongr
      exact le_add_of_nonneg_left zero_le_one
    _ = _ := by simp only [fourierMoment, pow_succ]; ring

theorem summable_weightedCurlNorm (m : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (m + 1) u)) : Summable (weightedCurlNorm m u) :=
  (hu.mul_left _).of_nonneg_of_le (weightedCurlNorm_nonneg m u)
    (weightedCurlNorm_le_fourierMoment m u)

theorem tsum_weightedCurlNorm_le (m : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (m + 1) u)) :
    (∑' k, weightedCurlNorm m u k) ≤ (2 * Real.pi) * ∑' k, fourierMoment (m + 1) u k := by
  simpa only [tsum_mul_left] using (summable_weightedCurlNorm m u hu).tsum_le_tsum
    (weightedCurlNorm_le_fourierMoment m u) (hu.mul_left _)

theorem one_add_norm_le_pairShift (p : Wavevector × Wavevector) (q : Wavevector) :
    1 + ‖frequencyVec q‖ ≤ (1 + ‖frequencyVec (pairShift p q)‖) *
      (1 + ‖frequencyVec p.1‖) * (1 + ‖frequencyVec p.2‖) := by
  have he : q = pairShift p q - p.1 - p.2 := by simp [pairShift]; abel
  have hn : ‖frequencyVec q‖ ≤ ‖frequencyVec (pairShift p q)‖ +
      ‖frequencyVec p.1‖ + ‖frequencyVec p.2‖ := by
    calc
      _ = ‖frequencyVec (pairShift p q) - frequencyVec p.1 - frequencyVec p.2‖ := by
        conv_lhs => rw [he, frequencyVec_sub, frequencyVec_sub]
      _ ≤ ‖frequencyVec (pairShift p q) - frequencyVec p.1‖ + ‖frequencyVec p.2‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (norm_sub_le _ _) le_rfl
  have hn₀ := norm_nonneg (frequencyVec (pairShift p q))
  have hl₀ := norm_nonneg (frequencyVec p.1)
  have hm₀ := norm_nonneg (frequencyVec p.2)
  nlinarith [mul_nonneg hn₀ hl₀, mul_nonneg hn₀ hm₀, mul_nonneg hl₀ hm₀,
    mul_nonneg (mul_nonneg hn₀ hl₀) hm₀]

theorem norm_weighted_combinedTest_le (m : ℕ) (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) :
    ‖((1 + ‖frequencyVec q‖) ^ m : ℝ) • combinedTest u F p q‖ ≤
      ((54 * (2 * Real.pi)) * (weightedCurlNorm (m + 1) u p.1 *
        weightedCurlNorm (m + 1) u p.2)) * weightedOutputNorm (m + 1) F (pairShift p q) := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖frequencyVec q‖)
    (one_add_norm_le_pairShift p q) (m + 1)
  have hq : (1 + ‖frequencyVec q‖) ^ m * ‖frequencyVec q‖ ≤
      ((1 + ‖frequencyVec (pairShift p q)‖) * (1 + ‖frequencyVec p.1‖) *
        (1 + ‖frequencyVec p.2‖)) ^ (m + 1) := by
    apply le_trans _ hp
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)
  calc
    _ ≤ (1 + ‖frequencyVec q‖) ^ m *
        ((54 * (2 * Real.pi)) * ‖frequencyVec q‖ *
          (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖) :=
      mul_le_mul_of_nonneg_left (norm_combinedTest_le u F p q) (by positivity)
    _ = ((1 + ‖frequencyVec q‖) ^ m * ‖frequencyVec q‖) *
        ((54 * (2 * Real.pi)) * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) *
          ‖outputCoefficient F (pairShift p q)‖) := by ring
    _ ≤ (((1 + ‖frequencyVec (pairShift p q)‖) * (1 + ‖frequencyVec p.1‖) *
        (1 + ‖frequencyVec p.2‖)) ^ (m + 1)) *
        ((54 * (2 * Real.pi)) * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) *
          ‖outputCoefficient F (pairShift p q)‖) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by simp only [weightedCurlNorm, weightedOutputNorm, mul_pow]; ring

set_option maxHeartbeats 800000 in
theorem sum_weighted_coefficientTest_sq_le (m : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (m + 2) u)) (F : H)
    (hF : Summable (fun n ↦ weightedOutputNorm (m + 1) F n ^ 2)) (Q : Finset Wavevector) :
    (∑ q ∈ Q, ‖((1 + ‖frequencyVec q‖) ^ m : ℝ) • coefficientTest u F q‖ ^ 2) ≤
      ((54 * (2 * Real.pi)) * (∑' k, weightedCurlNorm (m + 1) u k) ^ 2) ^ 2 *
        ∑' n, weightedOutputNorm (m + 1) F n ^ 2 := by
  let w := fun p : Wavevector × Wavevector ↦ (54 * (2 * Real.pi)) *
    (weightedCurlNorm (m + 1) u p.1 * weightedCurlNorm (m + 1) u p.2)
  have hw : Summable (weightedCurlNorm (m + 1) u) := summable_weightedCurlNorm (m + 1) u hu
  have hp := hw.mul_of_nonneg hw (weightedCurlNorm_nonneg _ _) (weightedCurlNorm_nonneg _ _)
  have hsw : Summable w := hp.mul_left _
  have he : (∑' p, w p) = (54 * (2 * Real.pi)) * (∑' k, weightedCurlNorm (m + 1) u k) ^ 2 := by
    change (∑' p : Wavevector × Wavevector, (54 * (2 * Real.pi)) *
      (weightedCurlNorm (m + 1) u p.1 * weightedCurlNorm (m + 1) u p.2)) = _
    rw [tsum_mul_left, ← hw.tsum_mul_tsum hw hp, pow_two]
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ m + 2) hu
  have h := Mettapedia.Analysis.ShiftedSeriesSquareBound.sum_norm_tsum_sq_le Q
    (fun p q ↦ ((1 + ‖frequencyVec q‖) ^ m : ℝ) • combinedTest u F p q)
    w (weightedOutputNorm (m + 1) F) pairShift
    (fun p ↦ mul_nonneg (by positivity) (mul_nonneg
      (weightedCurlNorm_nonneg _ _ _) (weightedCurlNorm_nonneg _ _ _))) hsw hF
    (fun q ↦ (summable_combinedTest u hu1 F q).const_smul _)
    (norm_weighted_combinedTest_le m u F)
  simpa only [tsum_const_smul'', tsum_combinedTest u hu1 F, he] using h

theorem summable_weighted_coefficientTest_sq (m : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (m + 2) u)) (F : H)
    (hF : Summable (fun n ↦ weightedOutputNorm (m + 1) F n ^ 2)) :
    Summable (fun q ↦ ‖((1 + ‖frequencyVec q‖) ^ m : ℝ) • coefficientTest u F q‖ ^ 2) :=
  summable_of_sum_le (fun _ ↦ sq_nonneg _) (sum_weighted_coefficientTest_sq_le m u hu F hF)

theorem tsum_weighted_coefficientTest_sq_le (m : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (m + 2) u)) (F : H)
    (hF : Summable (fun n ↦ weightedOutputNorm (m + 1) F n ^ 2)) :
    (∑' q, ‖((1 + ‖frequencyVec q‖) ^ m : ℝ) • coefficientTest u F q‖ ^ 2) ≤
      ((54 * (2 * Real.pi)) * (∑' k, weightedCurlNorm (m + 1) u k) ^ 2) ^ 2 *
        ∑' n, weightedOutputNorm (m + 1) F n ^ 2 :=
  (summable_weighted_coefficientTest_sq m u hu F hF).tsum_le_of_sum_le
    (sum_weighted_coefficientTest_sq_le m u hu F hF)

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjointWeightedSum
