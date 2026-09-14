import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxVariationSeries

/-!
# Constructed infinite coefficient test for the stretching variation

At each velocity frequency, two absolutely convergent double sums construct
the adjoint test. The inner-slot exchange is performed before aggregation.
The convergence bounds retain an explicit curl operator norm and do not
assert a positive-order square-summability budget for the resulting test.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjointSeries

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PeriodicGradientFluxTriple ExchangedFluxVariation ExchangedFluxModeEnvelope
open ExchangedFluxHeatRepresentation ExchangedFluxAdjoint ExchangedFluxVariationSeries

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "H" => Mettapedia.Analysis.UnitTorusGradientProjection.TensorL2
  (Fin 3) (EuclideanSpace ℝ (Fin 3))

theorem norm_outerSlot_le (u : FourierVelocity) (p : TripleIndex) :
    ‖outerSlot u p‖ ≤ (6 * embeddingConstant * ‖curlCoefficientCLM p.1‖) *
      (‖fourierCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖) := by
  have hE := embeddingConstant_nonneg
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun a ↦ ?_)
  let v : FourierVelocity := fun _ j ↦ a j
  have he : outerSlot u p a = mixedMode v u u p := outerSlot_apply u v p
  rw [he]
  have hc : ‖fourierCurl v p.1‖ ≤ ‖curlCoefficientCLM p.1‖ * ‖a‖ :=
    (curlCoefficientCLM p.1).le_opNorm a
  exact (norm_mixedMode_le v u u p).trans
    ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (by positivity))
      (by positivity : 0 ≤ 6 * embeddingConstant)).trans_eq (by ring))

theorem norm_leftSlot_le (u : FourierVelocity) (p : TripleIndex) :
    ‖leftSlot u p‖ ≤ (6 * embeddingConstant * ‖curlCoefficientCLM p.2.1‖) *
      (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2.2‖) := by
  have hE := embeddingConstant_nonneg
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun a ↦ ?_)
  let v : FourierVelocity := fun _ j ↦ a j
  have he : leftSlot u p a = mixedMode u v u p := leftSlot_apply u v p
  rw [he]
  have hc : ‖fourierCurl v p.2.1‖ ≤ ‖curlCoefficientCLM p.2.1‖ * ‖a‖ :=
    (curlCoefficientCLM p.2.1).le_opNorm a
  exact (norm_mixedMode_le u v u p).trans
    ((mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) (norm_nonneg _))
      (by positivity : 0 ≤ 6 * embeddingConstant)).trans_eq (by ring))

theorem norm_outerTest_le (u : FourierVelocity) (F : H) (p : TripleIndex) :
    ‖outerTest u F p‖ ≤ (6 * embeddingConstant * ‖curlCoefficientCLM p.1‖ * ‖F‖) *
      (‖fourierCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖) := by
  have h := ((outerSlot u p).adjoint).le_opNorm F
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans ((mul_le_mul_of_nonneg_right (norm_outerSlot_le u p) (norm_nonneg _)).trans_eq (by ring))

theorem norm_leftTest_le (u : FourierVelocity) (F : H) (p : TripleIndex) :
    ‖leftTest u F p‖ ≤ (6 * embeddingConstant * ‖curlCoefficientCLM p.2.1‖ * ‖F‖) *
      (‖fourierCurl u p.1‖ * ‖fourierCurl u p.2.2‖) := by
  have h := ((leftSlot u p).adjoint).le_opNorm F
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans ((mul_le_mul_of_nonneg_right (norm_leftSlot_le u p) (norm_nonneg _)).trans_eq (by ring))

theorem summable_norm_outerTest (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (F : H) (q : Wavevector) :
    Summable (fun p : Wavevector × Wavevector ↦ ‖outerTest u F (q, p)‖) := by
  have h := summable_norm_curl u hu
  exact ((h.mul_of_nonneg h (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)).mul_left
    (6 * embeddingConstant * ‖curlCoefficientCLM q‖ * ‖F‖)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun p ↦ norm_outerTest_le u F (q, p))

theorem summable_norm_leftTest (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (F : H) (q : Wavevector) :
    Summable (fun p : Wavevector × Wavevector ↦ ‖leftTest u F (p.1, (q, p.2))‖) := by
  have h := summable_norm_curl u hu
  exact ((h.mul_of_nonneg h (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)).mul_left
    (6 * embeddingConstant * ‖curlCoefficientCLM q‖ * ‖F‖)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun p ↦ norm_leftTest_le u F (p.1, (q, p.2)))

/-- The exact test multiplying the velocity rate at one frequency. -/
def coefficientTest (u : FourierVelocity) (F : H) (q : Wavevector) : C3 :=
  -(∑' p : Wavevector × Wavevector, outerTest u F (q, p)) -
    (2 : ℝ) • ∑' p : Wavevector × Wavevector, leftTest u F (p.1, (q, p.2))

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjointSeries
