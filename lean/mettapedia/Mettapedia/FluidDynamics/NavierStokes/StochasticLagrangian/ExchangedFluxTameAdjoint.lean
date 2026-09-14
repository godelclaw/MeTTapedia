import Mettapedia.Analysis.FiniteEnvelopeSquareBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxAdjointSectors

/-!
# Additive derivative accounting for the coefficient adjoint

The two derivatives required by the positive-order test norm are placed
on the output or on one input at a time. This avoids multiplying all
three high-order weights. The resulting norms are still regularity
costs, not dynamically controlled quantities.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxTameAdjoint

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy
open ExchangedFluxAdjointSquareSum ExchangedFluxAdjointWeightedSum ExchangedFluxAdjointSectors
open PeriodicTensorFourierFrame

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "H" => Mettapedia.Analysis.UnitTorusGradientProjection.TensorL2
  (Fin 3) (EuclideanSpace ℝ (Fin 3))

def inputWeight (K : ℝ) (u : FourierVelocity) (j : Fin 3) (p : Wavevector × Wavevector) : ℝ :=
  ![3 * K * (weightedCurlNorm 0 u p.1 * weightedCurlNorm 0 u p.2),
    3 * K * (weightedCurlNorm 2 u p.1 * weightedCurlNorm 0 u p.2),
    3 * K * (weightedCurlNorm 0 u p.1 * weightedCurlNorm 2 u p.2)] j

def outputEnvelope (F : H) (j : Fin 3) (n : Wavevector) : ℝ :=
  ![weightedOutputNorm 2 F n, weightedOutputNorm 0 F n, weightedOutputNorm 0 F n] j

def tameEnvelope (K : ℝ) (u : FourierVelocity) (F : H) : ℝ :=
  27 * K ^ 2 * ((∑' k, weightedCurlNorm 0 u k) ^ 4 * ∑' n, weightedOutputNorm 2 F n ^ 2 +
    2 * ((∑' k, weightedCurlNorm 2 u k) * (∑' k, weightedCurlNorm 0 u k)) ^ 2 * ‖F‖ ^ 2)

theorem inputWeight_nonneg {K : ℝ} (hK : 0 ≤ K) (u : FourierVelocity)
    (j : Fin 3) (p : Wavevector × Wavevector) : 0 ≤ inputWeight K u j p := by
  fin_cases j <;> dsimp [inputWeight]
  all_goals
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hK)
      (mul_nonneg (weightedCurlNorm_nonneg _ _ _) (weightedCurlNorm_nonneg _ _ _))

theorem outputEnvelope_nonneg (F : H) (j : Fin 3) (n : Wavevector) :
    0 ≤ outputEnvelope F j n := by
  fin_cases j <;> dsimp [outputEnvelope]
  all_goals exact weightedOutputNorm_nonneg _ _ _

theorem one_add_norm_sq_le_pairShift (p : Wavevector × Wavevector) (q : Wavevector) :
    (1 + ‖frequencyVec q‖) ^ 2 ≤ 3 * ((1 + ‖frequencyVec (pairShift p q)‖) ^ 2 +
      (1 + ‖frequencyVec p.1‖) ^ 2 + (1 + ‖frequencyVec p.2‖) ^ 2) := by
  have he : q = pairShift p q - p.1 - p.2 := by simp [pairShift]; abel
  have hn : ‖frequencyVec q‖ ≤ ‖frequencyVec (pairShift p q)‖ +
      ‖frequencyVec p.1‖ + ‖frequencyVec p.2‖ := by
    calc
      _ = ‖frequencyVec (pairShift p q) - frequencyVec p.1 - frequencyVec p.2‖ := by
        conv_lhs => rw [he, frequencyVec_sub, frequencyVec_sub]
      _ ≤ ‖frequencyVec (pairShift p q) - frequencyVec p.1‖ + ‖frequencyVec p.2‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (norm_sub_le _ _) le_rfl
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖frequencyVec q‖)
    (show 1 + ‖frequencyVec q‖ ≤ (1 + ‖frequencyVec (pairShift p q)‖) +
      (1 + ‖frequencyVec p.1‖) + (1 + ‖frequencyVec p.2‖) by linarith) 2
  nlinarith [sq_nonneg (‖frequencyVec (pairShift p q)‖ - ‖frequencyVec p.1‖),
    sq_nonneg (‖frequencyVec (pairShift p q)‖ - ‖frequencyVec p.2‖),
    sq_nonneg (‖frequencyVec p.1‖ - ‖frequencyVec p.2‖)]

theorem norm_weighted_term_le (u : FourierVelocity) (F : H)
    (p : Wavevector × Wavevector) (q : Wavevector) (v : C3) (K : ℝ) (hK : 0 ≤ K)
    (hv : ‖v‖ ≤ K * ‖frequencyVec q‖ * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) *
      ‖outputCoefficient F (pairShift p q)‖) :
    ‖((1 + ‖frequencyVec q‖) : ℝ) • v‖ ≤
      ∑ j : Fin 3, inputWeight K u j p * outputEnvelope F j (pairShift p q) := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hq : (1 + ‖frequencyVec q‖) * ‖frequencyVec q‖ ≤
      3 * ((1 + ‖frequencyVec (pairShift p q)‖) ^ 2 +
        (1 + ‖frequencyVec p.1‖) ^ 2 + (1 + ‖frequencyVec p.2‖) ^ 2) := by
    apply le_trans _ (one_add_norm_sq_le_pairShift p q)
    nlinarith [norm_nonneg (frequencyVec q)]
  calc
    _ ≤ (1 + ‖frequencyVec q‖) * (K * ‖frequencyVec q‖ *
        (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = ((1 + ‖frequencyVec q‖) * ‖frequencyVec q‖) *
        (K * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖) := by ring
    _ ≤ (3 * ((1 + ‖frequencyVec (pairShift p q)‖) ^ 2 +
        (1 + ‖frequencyVec p.1‖) ^ 2 + (1 + ‖frequencyVec p.2‖) ^ 2)) *
        (K * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖) :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by
      simp [Fin.sum_univ_three, inputWeight, outputEnvelope, weightedCurlNorm, weightedOutputNorm]
      ring

theorem summable_inputWeight (K : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) : Summable (inputWeight K u j) := by
  have h0 := summable_weightedCurlNorm 0 u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have h2 := summable_weightedCurlNorm 2 u hu
  fin_cases j
  · exact (h0.mul_of_nonneg h0 (weightedCurlNorm_nonneg _ _) (weightedCurlNorm_nonneg _ _)).mul_left _
  · exact (h2.mul_of_nonneg h0 (weightedCurlNorm_nonneg _ _) (weightedCurlNorm_nonneg _ _)).mul_left _
  · exact (h0.mul_of_nonneg h2 (weightedCurlNorm_nonneg _ _) (weightedCurlNorm_nonneg _ _)).mul_left _

theorem tsum_inputWeight (K : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (j : Fin 3) :
    (∑' p, inputWeight K u j p) =
      ![3 * K * (∑' k, weightedCurlNorm 0 u k) ^ 2,
        3 * K * ((∑' k, weightedCurlNorm 2 u k) * (∑' k, weightedCurlNorm 0 u k)),
        3 * K * ((∑' k, weightedCurlNorm 0 u k) * (∑' k, weightedCurlNorm 2 u k))] j := by
  have h0 := summable_weightedCurlNorm 0 u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have h2 := summable_weightedCurlNorm 2 u hu
  fin_cases j
  · change (∑' p : Wavevector × Wavevector, 3 * K *
        (weightedCurlNorm 0 u p.1 * weightedCurlNorm 0 u p.2)) =
      3 * K * (∑' k, weightedCurlNorm 0 u k) ^ 2
    rw [tsum_mul_left, ← h0.tsum_mul_tsum h0
      (h0.mul_of_nonneg h0 (weightedCurlNorm_nonneg _ _) (weightedCurlNorm_nonneg _ _)), pow_two]
  · change (∑' p : Wavevector × Wavevector, 3 * K *
        (weightedCurlNorm 2 u p.1 * weightedCurlNorm 0 u p.2)) =
      3 * K * ((∑' k, weightedCurlNorm 2 u k) * (∑' k, weightedCurlNorm 0 u k))
    rw [tsum_mul_left, ← h2.tsum_mul_tsum h0
      (h2.mul_of_nonneg h0 (weightedCurlNorm_nonneg _ _) (weightedCurlNorm_nonneg _ _))]
  · change (∑' p : Wavevector × Wavevector, 3 * K *
        (weightedCurlNorm 0 u p.1 * weightedCurlNorm 2 u p.2)) =
      3 * K * ((∑' k, weightedCurlNorm 0 u k) * (∑' k, weightedCurlNorm 2 u k))
    rw [tsum_mul_left, ← h0.tsum_mul_tsum h2
      (h0.mul_of_nonneg h2 (weightedCurlNorm_nonneg _ _) (weightedCurlNorm_nonneg _ _))]

theorem summable_outputEnvelope_sq (F : H)
    (hF : Summable (fun n ↦ weightedOutputNorm 2 F n ^ 2)) (j : Fin 3) :
    Summable (fun n ↦ outputEnvelope F j n ^ 2) := by
  fin_cases j
  · exact hF
  · change Summable (fun n ↦ weightedOutputNorm 0 F n ^ 2)
    simpa only [weightedOutputNorm, pow_zero, one_mul] using
      summable_norm_outputCoefficient_sq F
  · change Summable (fun n ↦ weightedOutputNorm 0 F n ^ 2)
    simpa only [weightedOutputNorm, pow_zero, one_mul] using
      summable_norm_outputCoefficient_sq F

theorem sum_envelope_le (K : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (F : H) :
    (3 : ℝ) * (∑ j : Fin 3, (∑' p, inputWeight K u j p) ^ 2 *
      ∑' n, outputEnvelope F j n ^ 2) ≤ tameEnvelope K u F := by
  have hb0 : (∑' n, weightedOutputNorm 0 F n ^ 2) ≤ ‖F‖ ^ 2 := by
    simpa only [weightedOutputNorm, pow_zero, one_mul] using tsum_norm_outputCoefficient_sq_le F
  simp only [Fin.sum_univ_three, tsum_inputWeight K u hu]
  change (3 : ℝ) *
    ((3 * K * (∑' k, weightedCurlNorm 0 u k) ^ 2) ^ 2 * ∑' n, weightedOutputNorm 2 F n ^ 2 +
      (3 * K * ((∑' k, weightedCurlNorm 2 u k) * (∑' k, weightedCurlNorm 0 u k))) ^ 2 *
        ∑' n, weightedOutputNorm 0 F n ^ 2 +
      (3 * K * ((∑' k, weightedCurlNorm 0 u k) * (∑' k, weightedCurlNorm 2 u k))) ^ 2 *
        ∑' n, weightedOutputNorm 0 F n ^ 2) ≤ _
  calc
    _ = 27 * K ^ 2 * ((∑' k, weightedCurlNorm 0 u k) ^ 4 * ∑' n, weightedOutputNorm 2 F n ^ 2 +
        2 * ((∑' k, weightedCurlNorm 2 u k) * (∑' k, weightedCurlNorm 0 u k)) ^ 2 *
          ∑' n, weightedOutputNorm 0 F n ^ 2) := by ring
    _ ≤ tameEnvelope K u F := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hb0 (by positivity))) (by positivity)

theorem sum_weighted_series_sq_le (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (F : H) (hF : Summable (fun n ↦ weightedOutputNorm 2 F n ^ 2))
    (f : Wavevector × Wavevector → Wavevector → C3) (K : ℝ) (hK : 0 ≤ K)
    (hsf : ∀ q, Summable (fun p ↦ f p q))
    (hf : ∀ p q, ‖f p q‖ ≤ K * ‖frequencyVec q‖ *
      (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖)
    (Q : Finset Wavevector) :
    (∑ q ∈ Q, ‖((1 + ‖frequencyVec q‖) : ℝ) • (∑' p, f p q)‖ ^ 2) ≤ tameEnvelope K u F := by
  have h := Mettapedia.Analysis.FiniteEnvelopeSquareBound.sum_norm_tsum_sq_le Q Finset.univ
    (fun p q ↦ ((1 + ‖frequencyVec q‖) : ℝ) • f p q) (inputWeight K u) (outputEnvelope F) pairShift
    (fun j _ p ↦ inputWeight_nonneg hK u j p) (fun j _ n ↦ outputEnvelope_nonneg F j n)
    (fun j _ ↦ summable_inputWeight K u hu j) (fun j _ ↦ summable_outputEnvelope_sq F hF j)
    (fun q ↦ (hsf q).const_smul _)
    (fun p q ↦ norm_weighted_term_le u F p q (f p q) K hK (hf p q))
  simp only [tsum_const_smul'', Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at h
  exact h.trans (sum_envelope_le K u hu F)

theorem summable_weighted_series_sq (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (F : H) (hF : Summable (fun n ↦ weightedOutputNorm 2 F n ^ 2))
    (f : Wavevector × Wavevector → Wavevector → C3) (K : ℝ) (hK : 0 ≤ K)
    (hsf : ∀ q, Summable (fun p ↦ f p q))
    (hf : ∀ p q, ‖f p q‖ ≤ K * ‖frequencyVec q‖ *
      (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖) :
    Summable (fun q ↦ ‖((1 + ‖frequencyVec q‖) : ℝ) • (∑' p, f p q)‖ ^ 2) :=
  summable_of_sum_le (fun _ ↦ sq_nonneg _) (sum_weighted_series_sq_le u hu F hF f K hK hsf hf)

theorem tsum_weighted_series_sq_le (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (F : H) (hF : Summable (fun n ↦ weightedOutputNorm 2 F n ^ 2))
    (f : Wavevector × Wavevector → Wavevector → C3) (K : ℝ) (hK : 0 ≤ K)
    (hsf : ∀ q, Summable (fun p ↦ f p q))
    (hf : ∀ p q, ‖f p q‖ ≤ K * ‖frequencyVec q‖ *
      (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖) :
    (∑' q, ‖((1 + ‖frequencyVec q‖) : ℝ) • (∑' p, f p q)‖ ^ 2) ≤ tameEnvelope K u F :=
  (summable_weighted_series_sq u hu F hF f K hK hsf hf).tsum_le_of_sum_le
    (sum_weighted_series_sq_le u hu F hF f K hK hsf hf)

theorem tameEnvelope_mul (K r : ℝ) (u : FourierVelocity) (F : H) :
    tameEnvelope (K * r) u F = r ^ 2 * tameEnvelope K u F := by unfold tameEnvelope; ring

theorem tsum_weighted_coefficientTest_sq_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (F : H)
    (hF : Summable (fun n ↦ weightedOutputNorm 2 F n ^ 2)) :
    (∑' q, ‖((1 + ‖frequencyVec q‖) : ℝ) • ExchangedFluxAdjointSeries.coefficientTest u F q‖ ^ 2) ≤
      tameEnvelope (54 * (2 * Real.pi)) u F := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  simpa only [tsum_combinedTest u hu1 F] using tsum_weighted_series_sq_le u hu F hF
    (combinedTest u F) _ (by positivity) (summable_combinedTest u hu1 F) (norm_combinedTest_le u F)

theorem tsum_weighted_selectedTest_sq_le {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (F : H)
    (hF : Summable (fun n ↦ weightedOutputNorm 2 F n ^ 2)) :
    (∑' q, ‖((1 + ‖frequencyVec q‖) : ℝ) • selectedTest δ η u F q‖ ^ 2) ≤
      sectorFactor δ η ^ 2 * tameEnvelope (54 * (2 * Real.pi)) u F := by
  have hr := sectorFactor_nonneg hδ hη
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have h := tsum_weighted_series_sq_le u hu F hF (selectedTerm δ η u F)
    (54 * (2 * Real.pi) * sectorFactor δ η) (by positivity)
    (summable_selectedTerm δ η u hu1 F) (norm_selectedTerm_le hδ hη u F)
  simpa only [selectedTest, tameEnvelope_mul] using h

theorem norm_remainderTerm_le {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (u : FourierVelocity) (F : H) (p : Wavevector × Wavevector) (q : Wavevector) :
    ‖remainderTerm δ η u F p q‖ ≤ (54 * (2 * Real.pi) * (1 + sectorFactor δ η)) *
      ‖frequencyVec q‖ * (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) *
        ‖outputCoefficient F (pairShift p q)‖ := by
  calc
    _ ≤ ‖combinedTest u F p q‖ + ‖selectedTerm δ η u F p q‖ := norm_sub_le _ _
    _ ≤ (54 * (2 * Real.pi)) * ‖frequencyVec q‖ *
          (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖ +
        (54 * (2 * Real.pi) * sectorFactor δ η) * ‖frequencyVec q‖ *
          (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2‖) * ‖outputCoefficient F (pairShift p q)‖ :=
      add_le_add (norm_combinedTest_le u F p q) (norm_selectedTerm_le hδ hη u F p q)
    _ = _ := by ring

theorem tsum_weighted_remainderTest_sq_le {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (F : H)
    (hF : Summable (fun n ↦ weightedOutputNorm 2 F n ^ 2)) :
    (∑' q, ‖((1 + ‖frequencyVec q‖) : ℝ) • remainderTest δ η u F q‖ ^ 2) ≤
      (1 + sectorFactor δ η) ^ 2 * tameEnvelope (54 * (2 * Real.pi)) u F := by
  have hr := sectorFactor_nonneg hδ hη
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have h := tsum_weighted_series_sq_le u hu F hF (remainderTerm δ η u F)
    (54 * (2 * Real.pi) * (1 + sectorFactor δ η)) (by positivity)
    (summable_remainderTerm δ η u hu1 F) (norm_remainderTerm_le hδ hη u F)
  simpa only [remainderTest, tameEnvelope_mul] using h

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxTameAdjoint
