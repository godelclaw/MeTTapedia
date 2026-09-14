import Mettapedia.Analysis.ShiftedSeriesSquareBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxOutputAdjoint

/-!
# Square-sum control of the constructed nonlinear test

Both input slots are combined at their common output frequency. The
output frame and shifted-series inequality control the entire lattice.
The unweighted output energy gives a negative-order test estimate; a
positive-order estimate requires two additional Fourier weights.
None of these input Fourier norms is a global initial-data budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjointSquareSum

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PeriodicGradientFluxTriple ExchangedFluxModeDynamics ExchangedFluxModeEnvelope
open ExchangedFluxAdjoint ExchangedFluxAdjointGeometry ExchangedFluxAdjointSeries
open ExchangedFluxHeatRepresentation ExchangedFluxOutputAdjoint PeriodicTensorFourierFrame

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "H" => Mettapedia.Analysis.UnitTorusGradientProjection.TensorL2
  (Fin 3) (EuclideanSpace ℝ (Fin 3))

def pairShift (p : Wavevector × Wavevector) : Wavevector ≃ Wavevector := Equiv.addRight (p.1 + p.2)

def combinedTest (u : FourierVelocity) (F : H) (p : Wavevector × Wavevector) (q : Wavevector) : C3 :=
  -outerTest u F (q, p) - (2 : ℝ) • leftTest u F (p.1, (q, p.2))

theorem summable_combinedTest (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (F : H) (q : Wavevector) : Summable (fun p ↦ combinedTest u F p q) :=
  (summable_norm_outerTest u hu F q).of_norm.neg.sub
    ((summable_norm_leftTest u hu F q).of_norm.const_smul 2)

theorem tsum_combinedTest (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (F : H) (q : Wavevector) : (∑' p, combinedTest u F p q) = coefficientTest u F q := by
  simp only [combinedTest]
  rw [((summable_norm_outerTest u hu F q).of_norm.neg).tsum_sub
    ((summable_norm_leftTest u hu F q).of_norm.const_smul 2), tsum_neg, tsum_const_smul'']
  rfl

theorem norm_combinedTest_le (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) :
    ‖combinedTest u F p q‖ ≤ (54 * (2 * Real.pi)) * ‖frequencyVec q‖ *
      (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖ := by
  have he₁ : tripleFrequency (q, p) = pairShift p q := by simp [tripleFrequency, pairShift, add_assoc]
  have he₂ : tripleFrequency (p.1, (q, p.2)) = pairShift p q := by
    simp [tripleFrequency, pairShift, add_assoc, add_left_comm]
  have hd : ‖differenceCLM (p.1, (q, p.2))‖ ≤ 6 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (norm_differenceCLM_le _)
  have hc : ‖differenceCLM (q, p) (coefficientCross (fourierCurl u p.1) (fourierCurl u p.2))‖ ≤
      6 * (2 * ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) :=
    (norm_differenceCLM_le _ _).trans (mul_le_mul_of_nonneg_left (norm_coefficientCross_le _ _) (by norm_num))
  have ho : ‖outerTest u F (q, p)‖ ≤ (18 * (2 * Real.pi)) * ‖frequencyVec q‖ *
      (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖ := by
    apply (norm_outerTest_le_output u F (q, p)).trans
    rw [he₁]
    calc
      _ ≤ ((3 / 2 : ℝ) * ((2 * Real.pi) * ‖frequencyVec q‖) *
          (6 * (2 * ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖))) *
          ‖outputCoefficient F (pairShift p q)‖ := by
        gcongr
        · exact norm_curlCoefficientCLM_le q
      _ = _ := by ring
  have hl : ‖leftTest u F (p.1, (q, p.2))‖ ≤ (18 * (2 * Real.pi)) * ‖frequencyVec q‖ *
      (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖ := by
    apply (norm_leftTest_le_output u F (p.1, (q, p.2))).trans
    rw [he₂]
    calc
      _ ≤ (3 * (6 * ((2 * Real.pi) * ‖frequencyVec q‖)) *
          ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖ := by
        gcongr
        exact norm_curlCoefficientCLM_le q
      _ = _ := by ring
  have h : ‖combinedTest u F p q‖ ≤ ‖outerTest u F (q, p)‖ +
      2 * ‖leftTest u F (p.1, (q, p.2))‖ := by
    simpa only [combinedTest, norm_neg, norm_smul, Real.norm_ofNat] using
      norm_sub_le (-outerTest u F (q, p)) ((2 : ℝ) • leftTest u F (p.1, (q, p.2)))
  nlinarith

theorem norm_normalized_combinedTest_le (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) :
    ‖((1 + ‖frequencyVec q‖)⁻¹ : ℝ) • combinedTest u F p q‖ ≤
      ((54 * (2 * Real.pi)) * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖)) *
        ‖outputCoefficient F (pairShift p q)‖ := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left (norm_combinedTest_le u F p q)
    (by positivity : 0 ≤ (1 + ‖frequencyVec q‖)⁻¹)
  apply h.trans
  have hr : ‖frequencyVec q‖ / (1 + ‖frequencyVec q‖) ≤ 1 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  calc
    _ = (‖frequencyVec q‖ / (1 + ‖frequencyVec q‖)) *
        (((54 * (2 * Real.pi)) * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖)) *
          ‖outputCoefficient F (pairShift p q)‖) := by ring
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hr

set_option maxHeartbeats 800000 in
theorem sum_normalized_coefficientTest_sq_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (F : H) (Q : Finset Wavevector) :
    (∑ q ∈ Q, ‖((1 + ‖frequencyVec q‖)⁻¹ : ℝ) • coefficientTest u F q‖ ^ 2) ≤
      ((54 * (2 * Real.pi)) * (∑' k, ‖fourierCurl u k‖) ^ 2) ^ 2 * ‖F‖ ^ 2 := by
  let w := fun p : Wavevector × Wavevector ↦
    (54 * (2 * Real.pi)) * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖)
  have hw := summable_norm_curl u hu
  have hsw : Summable w := (hw.mul_of_nonneg hw (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)).mul_left _
  have he : (∑' p, w p) = (54 * (2 * Real.pi)) * (∑' k, ‖fourierCurl u k‖) ^ 2 := by
    rw [show w = fun p : Wavevector × Wavevector ↦
      (54 * (2 * Real.pi)) * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) from rfl,
      tsum_mul_left, ← hw.tsum_mul_tsum hw
        (hw.mul_of_nonneg hw (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _))]
    ring
  have h := Mettapedia.Analysis.ShiftedSeriesSquareBound.sum_norm_tsum_sq_le Q
    (fun p q ↦ ((1 + ‖frequencyVec q‖)⁻¹ : ℝ) • combinedTest u F p q)
    w (fun n ↦ ‖outputCoefficient F n‖) pairShift
    (fun _ ↦ by positivity) hsw (summable_norm_outputCoefficient_sq F)
    (fun q ↦ (summable_combinedTest u hu F q).const_smul _)
    (norm_normalized_combinedTest_le u F)
  simp only [tsum_const_smul'', tsum_combinedTest u hu F, he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (tsum_norm_outputCoefficient_sq_le F) (sq_nonneg _))

theorem summable_normalized_coefficientTest_sq (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (F : H) :
    Summable (fun q ↦ ‖((1 + ‖frequencyVec q‖)⁻¹ : ℝ) • coefficientTest u F q‖ ^ 2) :=
  summable_of_sum_le (fun _ ↦ sq_nonneg _) (sum_normalized_coefficientTest_sq_le u hu F)

theorem tsum_normalized_coefficientTest_sq_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (F : H) :
    (∑' q, ‖((1 + ‖frequencyVec q‖)⁻¹ : ℝ) • coefficientTest u F q‖ ^ 2) ≤
      ((54 * (2 * Real.pi)) * (∑' k, ‖fourierCurl u k‖) ^ 2) ^ 2 * ‖F‖ ^ 2 :=
  (summable_normalized_coefficientTest_sq u hu F).tsum_le_of_sum_le
    (sum_normalized_coefficientTest_sq_le u hu F)

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjointSquareSum
