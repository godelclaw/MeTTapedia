import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxAdjoint

/-!
# Absolutely convergent mixed variations and inner-slot exchange

The three-slot variation is summed on the full triple lattice. The two
inner slots have the same total contribution, by exchange before pairing.
The norms here justify rearrangement only; they are not a nonlinear budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxVariationSeries

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeZeroModeCurlBridge PancakeCurlOutputTail
open PeriodicGradientFluxTriple ExchangedFluxModeDynamics ExchangedFluxVariation
open ExchangedFluxModeEnvelope ExchangedFluxSeriesBudget ExchangedFluxHeatRepresentation
open LongitudinalExchangeFluxFourier LerayStretchExchange

theorem norm_mixedMode_le (u v w : FourierVelocity) (p : TripleIndex) :
    ‖mixedMode u v w p‖ ≤ 6 * embeddingConstant *
      (‖fourierCurl u p.1‖ * (‖fourierCurl v p.2.1‖ * ‖fourierCurl w p.2.2‖)) := by
  have h : ‖mixedTensor u v w p‖ ≤
      6 * (‖fourierCurl u p.1‖ * (‖fourierCurl v p.2.1‖ * ‖fourierCurl w p.2.2‖)) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    simp only [mixedTensor, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc
      _ ≤ (1 / 2 : ℝ) * (‖fourierCurl u p.1‖ *
          (6 * (2 * ‖fourierCurl v p.2.1‖ * ‖fourierCurl w p.2.2‖))) := by
        gcongr
        · exact norm_le_pi_norm _ _
        · exact (norm_differenceCLM_le p _).trans
            (mul_le_mul_of_nonneg_left (norm_coefficientCross_le _ _) (by norm_num))
      _ = _ := by ring
  exact (norm_tensorModeCLM_le _ _).trans
    ((mul_le_mul_of_nonneg_left h embeddingConstant_nonneg).trans_eq (by ring))

theorem summable_norm_mixedMode (u v w : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v))
    (hw : Summable (fourierMoment 1 w)) :
    Summable (fun p : TripleIndex ↦ ‖mixedMode u v w p‖) := by
  have ha := summable_norm_curl u hu
  have hb := summable_norm_curl v hv
  have hc := summable_norm_curl w hw
  exact ((ha.mul_of_nonneg (hb.mul_of_nonneg hc (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _))
    (fun _ ↦ norm_nonneg _) (fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))).mul_left
      (6 * embeddingConstant)).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_mixedMode_le u v w)

theorem summable_norm_variationMode (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) :
    Summable (fun p : TripleIndex ↦ ‖variationMode u v p‖) := by
  apply (((summable_norm_mixedMode v u u hv hu hu).add
    (summable_norm_mixedMode u v u hu hv hu)).add
      (summable_norm_mixedMode u u v hu hu hv)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro p
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

theorem mixedMode_innerExchange (u v w : FourierVelocity) (p : TripleIndex) :
    mixedMode u v w (innerExchange p) = mixedMode u w v p := by
  have he : mixedTensor u v w (innerExchange p) = mixedTensor u w v p := by
    funext j
    simp only [mixedTensor, innerExchange_apply, differenceCLM_apply]
    rw [show coefficientCross (fourierCurl v p.2.2) (fourierCurl w p.2.1) =
      -coefficientCross (fourierCurl w p.2.1) (fourierCurl v p.2.2) from (cross_anticomm _ _).symm]
    simp only [lerayMode_neg]
    congr 2
    abel
  rw [mixedMode, tripleFrequency_innerExchange, he]
  rfl

theorem tsum_mixedMode_innerExchange (u v w : FourierVelocity) :
    (∑' p : TripleIndex, mixedMode u v w p) = ∑' p : TripleIndex, mixedMode u w v p := by
  simpa only [mixedMode_innerExchange] using (innerExchange.tsum_eq (fun p ↦ mixedMode u v w p)).symm

theorem mixedMode_eq_zero_of_inner_zero (u v w : FourierVelocity) (p : TripleIndex)
    (hp : p.2.1 = 0) : mixedMode u v w p = 0 := by
  have hc : coefficientCross (fourierCurl v p.2.1) (fourierCurl w p.2.2) = 0 := by
    ext i
    fin_cases i <;> simp [hp, fourierCurl_zero, coefficientCross]
  have he : mixedTensor u v w p = 0 := by
    funext j
    simp [mixedTensor, hc]
  rw [mixedMode, he, map_zero]

theorem tsum_active_variationMode (u v : FourierVelocity) :
    (∑' p : ActiveTriple, variationMode u v p.val) = ∑' p : TripleIndex, variationMode u v p := by
  apply tsum_subtype_eq_of_support_subset
  intro p hp
  change p.2.1 ≠ 0
  intro hz
  apply hp
  simp only [variationMode, mixedMode_eq_zero_of_inner_zero _ _ _ p hz, add_zero]

set_option synthInstance.maxHeartbeats 80000 in
/-- Exactly two independent slot sums remain, with no loss of sign. -/
theorem fluxVariation_eq_outer_add_twice_inner (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) :
    fluxVariation u v = -(∑' p : TripleIndex, mixedMode v u u p) -
      (2 : ℝ) • (∑' p : TripleIndex, mixedMode u v u p) := by
  rw [fluxVariation, tsum_active_variationMode]
  simp only [variationMode]
  rw [((summable_norm_mixedMode v u u hv hu hu).of_norm.add
    (summable_norm_mixedMode u v u hu hv hu).of_norm).tsum_add
      (summable_norm_mixedMode u u v hu hu hv).of_norm,
    (summable_norm_mixedMode v u u hv hu hu).of_norm.tsum_add
      (summable_norm_mixedMode u v u hu hv hu).of_norm,
    tsum_mixedMode_innerExchange u u v]
  module

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxVariationSeries
