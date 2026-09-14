import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxAdjointSeries

/-!
# Retained geometric cancellation in the coefficient adjoints

The outer variation retains the exact projected vorticity cross product.
The inner variation retains the norm of the Leray difference. Equal and
opposite inner frequencies annihilate both operators, before any summation.
These are algebraic and operator estimates, not a dynamical coherence bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjointGeometry

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy
open PancakeIndexedFourierMoments PancakePhysicalSixthDecay
open PancakeCurlOutputTail
open PeriodicGradientFluxTriple ExchangedFluxModeDynamics ExchangedFluxVariation
open ExchangedFluxModeEnvelope ExchangedFluxAdjoint ExchangedFluxAdjointSeries LerayStretchExchange

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "H" => Mettapedia.Analysis.UnitTorusGradientProjection.TensorL2
  (Fin 3) (EuclideanSpace ℝ (Fin 3))

theorem norm_mixedMode_le_projected_cross (u v w : FourierVelocity) (p : TripleIndex) :
    ‖mixedMode u v w p‖ ≤ (embeddingConstant / 2) * ‖fourierCurl u p.1‖ *
      ‖differenceCLM p (coefficientCross (fourierCurl v p.2.1) (fourierCurl w p.2.2))‖ := by
  have h : ‖mixedTensor u v w p‖ ≤ (1 / 2 : ℝ) * ‖fourierCurl u p.1‖ *
      ‖differenceCLM p (coefficientCross (fourierCurl v p.2.1) (fourierCurl w p.2.2))‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    simp only [mixedTensor, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (norm_le_pi_norm _ _) (norm_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (by ring)
  exact (norm_tensorModeCLM_le _ _).trans
    ((mul_le_mul_of_nonneg_left h embeddingConstant_nonneg).trans_eq (by ring))

theorem norm_outerSlot_le_projected_cross (u : FourierVelocity) (p : TripleIndex) :
    ‖outerSlot u p‖ ≤ (embeddingConstant / 2) * ‖curlCoefficientCLM p.1‖ *
      ‖differenceCLM p (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2))‖ := by
  have hE := embeddingConstant_nonneg
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun a ↦ ?_)
  let v : FourierVelocity := fun _ j ↦ a j
  rw [show outerSlot u p a = mixedMode v u u p from outerSlot_apply u v p]
  have hc : ‖fourierCurl v p.1‖ ≤ ‖curlCoefficientCLM p.1‖ * ‖a‖ :=
    (curlCoefficientCLM p.1).le_opNorm a
  exact (norm_mixedMode_le_projected_cross v u u p).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity))
      (norm_nonneg _)).trans_eq (by ring))

theorem norm_outerTest_le_projected_cross (u : FourierVelocity) (F : H) (p : TripleIndex) :
    ‖outerTest u F p‖ ≤ (embeddingConstant / 2) * ‖curlCoefficientCLM p.1‖ *
      ‖differenceCLM p (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2))‖ * ‖F‖ := by
  have h := ((outerSlot u p).adjoint).le_opNorm F
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans (mul_le_mul_of_nonneg_right (norm_outerSlot_le_projected_cross u p) (norm_nonneg _))

theorem norm_leftSlot_le_difference (u : FourierVelocity) (p : TripleIndex) :
    ‖leftSlot u p‖ ≤ embeddingConstant * ‖differenceCLM p‖ * ‖curlCoefficientCLM p.2.1‖ *
      ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2.2‖ := by
  have hE := embeddingConstant_nonneg
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun a ↦ ?_)
  let v : FourierVelocity := fun _ j ↦ a j
  rw [show leftSlot u p a = mixedMode u v u p from leftSlot_apply u v p]
  have hc : ‖fourierCurl v p.2.1‖ ≤ ‖curlCoefficientCLM p.2.1‖ * ‖a‖ :=
    (curlCoefficientCLM p.2.1).le_opNorm a
  have hd : ‖differenceCLM p (coefficientCross (fourierCurl v p.2.1) (fourierCurl u p.2.2))‖ ≤
      ‖differenceCLM p‖ * (2 * (‖curlCoefficientCLM p.2.1‖ * ‖a‖) * ‖fourierCurl u p.2.2‖) := by
    apply ((differenceCLM p).le_opNorm _).trans
    gcongr
    exact (norm_coefficientCross_le _ _).trans (by gcongr)
  exact (norm_mixedMode_le_projected_cross u v u p).trans
    ((mul_le_mul_of_nonneg_left hd (by positivity)).trans_eq (by ring))

theorem norm_leftTest_le_difference (u : FourierVelocity) (F : H) (p : TripleIndex) :
    ‖leftTest u F p‖ ≤ embeddingConstant * ‖differenceCLM p‖ * ‖curlCoefficientCLM p.2.1‖ *
      ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2.2‖ * ‖F‖ := by
  have h := ((leftSlot u p).adjoint).le_opNorm F
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans (mul_le_mul_of_nonneg_right (norm_leftSlot_le_difference u p) (norm_nonneg _))

/-- The Leray difference is small for nearly opposite nonzero inputs. -/
theorem norm_differenceCLM_le_output (p : TripleIndex)
    (hl : p.2.1 ≠ 0) (hm : p.2.2 ≠ 0) :
    ‖differenceCLM p‖ ≤ 12 * ‖frequencyVec (p.2.1 + p.2.2)‖ /
      max ‖frequencyVec p.2.1‖ ‖frequencyVec p.2.2‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun a ↦ ?_)
  have h : ‖differenceCLM p a‖ ≤
      (4 * ‖frequencyVec (p.2.1 + p.2.2)‖ /
        max ‖frequencyVec p.2.1‖ ‖frequencyVec p.2.2‖) * ‖coefficientVec a‖ :=
    (norm_coefficient_sup_le_euclidean (differenceCLM p a)).trans
    (by
      rw [differenceCLM_apply]
      exact norm_lerayMode_sub_le_output_max p.2.1 p.2.2 a hl hm)
  exact h.trans ((mul_le_mul_of_nonneg_left
    (norm_coefficientVec_le_three a ‖a‖ (norm_nonneg _) (norm_le_pi_norm a))
    (by positivity)).trans_eq (by ring))

theorem norm_curlCoefficientCLM_le (q : Wavevector) :
    ‖curlCoefficientCLM q‖ ≤ (2 * Real.pi) * ‖frequencyVec q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun a ↦ ?_)
  let v : FourierVelocity := fun _ j ↦ a j
  exact (norm_coefficient_sup_le_euclidean (fourierCurl v q)).trans (norm_fourierCurl_le v q)

/-- The inner curl derivative is transferred to the sum of the inner frequencies. -/
theorem norm_difference_mul_curl_le_pair_frequency (p : TripleIndex)
    (hl : p.2.1 ≠ 0) (hm : p.2.2 ≠ 0) :
    ‖differenceCLM p‖ * ‖curlCoefficientCLM p.2.1‖ ≤
      12 * (2 * Real.pi) * ‖frequencyVec (p.2.1 + p.2.2)‖ := by
  have hmax : 0 < max ‖frequencyVec p.2.1‖ ‖frequencyVec p.2.2‖ :=
    (norm_pos_iff.mpr (frequencyVec_ne_zero hl)).trans_le (le_max_left _ _)
  have hr : ‖frequencyVec p.2.1‖ / max ‖frequencyVec p.2.1‖ ‖frequencyVec p.2.2‖ ≤ 1 :=
    (div_le_iff₀ hmax).mpr (by simpa only [one_mul] using
      (le_max_left ‖frequencyVec p.2.1‖ ‖frequencyVec p.2.2‖))
  calc
    _ ≤ (12 * ‖frequencyVec (p.2.1 + p.2.2)‖ /
          max ‖frequencyVec p.2.1‖ ‖frequencyVec p.2.2‖) *
        ((2 * Real.pi) * ‖frequencyVec p.2.1‖) :=
      mul_le_mul (norm_differenceCLM_le_output p hl hm) (norm_curlCoefficientCLM_le p.2.1)
        (norm_nonneg _) (by positivity)
    _ = (12 * (2 * Real.pi) * ‖frequencyVec (p.2.1 + p.2.2)‖) *
        (‖frequencyVec p.2.1‖ / max ‖frequencyVec p.2.1‖ ‖frequencyVec p.2.2‖) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hr

theorem norm_leftTest_le_pair_frequency (u : FourierVelocity) (F : H) (p : TripleIndex)
    (hl : p.2.1 ≠ 0) (hm : p.2.2 ≠ 0) :
    ‖leftTest u F p‖ ≤ (12 * (2 * Real.pi) * embeddingConstant) *
      ‖frequencyVec (p.2.1 + p.2.2)‖ * ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2.2‖ * ‖F‖ := by
  have hE := embeddingConstant_nonneg
  apply (norm_leftTest_le_difference u F p).trans
  calc
    _ = (embeddingConstant * (‖differenceCLM p‖ * ‖curlCoefficientCLM p.2.1‖)) *
        ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2.2‖ * ‖F‖ := by ring
    _ ≤ (embeddingConstant * (12 * (2 * Real.pi) * ‖frequencyVec (p.2.1 + p.2.2)‖)) *
        ‖fourierCurl u p.1‖ * ‖fourierCurl u p.2.2‖ * ‖F‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (norm_difference_mul_curl_le_pair_frequency p hl hm) hE)
            (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem outerTest_eq_zero_of_cross_eq_zero (u : FourierVelocity) (F : H) (p : TripleIndex)
    (hc : coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2) = 0) :
    outerTest u F p = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa only [hc, map_zero, norm_zero, mul_zero, zero_mul] using
    norm_outerTest_le_projected_cross u F p) (norm_nonneg _)

theorem differenceCLM_eq_zero_of_opposite (p : TripleIndex) (hp : p.2.2 = -p.2.1) :
    differenceCLM p = 0 := by
  ext a i
  simp [differenceCLM_apply, hp, lerayMode_neg_frequency]

theorem tests_eq_zero_of_opposite (u : FourierVelocity) (F : H) (p : TripleIndex)
    (hp : p.2.2 = -p.2.1) : outerTest u F p = 0 ∧ leftTest u F p = 0 := by
  have hd := differenceCLM_eq_zero_of_opposite p hp
  constructor
  · apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [hd, zero_apply, norm_zero, mul_zero, zero_mul] using
      norm_outerTest_le_projected_cross u F p) (norm_nonneg _)
  · apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [hd, norm_zero, mul_zero, zero_mul] using
      norm_leftTest_le_difference u F p) (norm_nonneg _)

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjointGeometry
