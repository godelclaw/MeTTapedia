import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicTensorFourierWeight
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxHeatTestEstimate

/-!
# Constructed weighted output control for the actual stretching flux

The weighted field is the convergent exchanged cubic Fourier series with
the output-frequency weight inserted. Its actual frame coefficients are
the weighted coefficients of the physical projected inviscid flux.
This discharges output square summability from velocity moments, reality,
and incompressibility. The bounds remain regularity-dependent.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxWeightedOutput

open Mettapedia.Analysis.UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeBlockReality PeriodicGradientFluxTriple
open LongitudinalExchangeFluxFourier LongitudinalGradientFlux ExchangedFluxModeDynamics
open ExchangedFluxModeEnvelope ExchangedFluxHeatRepresentation ExchangedFluxAdjointWeightedSum
open PeriodicTensorFourierFrame PeriodicTensorFourierWeight FourierHeatFlow ExchangedFluxHeatTestEstimate

local notation "H" => TensorL2 (Fin 3) (EuclideanSpace ℝ (Fin 3))

def outputWeight (s : ℕ) (n : Wavevector) : ℝ := (1 + ‖frequencyVec n‖) ^ s

theorem outputWeight_nonneg (s : ℕ) (n : Wavevector) : 0 ≤ outputWeight s n := by
  unfold outputWeight; positivity

theorem outputWeight_neg (s : ℕ) (n : Wavevector) : outputWeight s (-n) = outputWeight s n := by
  have h : frequencyVec (-n) = -frequencyVec n := by
    ext i
    simp [frequencyVec, coefficientVec, wavevectorCoefficient]
  simp only [outputWeight, h, norm_neg]

theorem outputWeight_triple_le (s : ℕ) (p : TripleIndex) :
    outputWeight s (tripleFrequency p) ≤
      outputWeight s p.1 * (outputWeight s p.2.1 * outputWeight s p.2.2) := by
  have hn : ‖frequencyVec (tripleFrequency p)‖ ≤
      ‖frequencyVec p.1‖ + (‖frequencyVec p.2.1‖ + ‖frequencyVec p.2.2‖) := by
    simp only [tripleFrequency, frequencyVec_add]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
  have ha := norm_nonneg (frequencyVec p.1)
  have hb := norm_nonneg (frequencyVec p.2.1)
  have hc := norm_nonneg (frequencyVec p.2.2)
  have h : 1 + ‖frequencyVec (tripleFrequency p)‖ ≤
      (1 + ‖frequencyVec p.1‖) * ((1 + ‖frequencyVec p.2.1‖) * (1 + ‖frequencyVec p.2.2‖)) := by
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc,
      mul_nonneg (mul_nonneg ha hb) hc]
  simpa only [outputWeight, mul_pow] using pow_le_pow_left₀ (by positivity) h s

theorem norm_weighted_mode_le (s : ℕ) (u : FourierVelocity) (p : TripleIndex) :
    ‖outputWeight s (tripleFrequency p) • mode u p‖ ≤
      cubicEnvelope (weightedCurlNorm s u) p := by
  rw [norm_smul, Real.norm_of_nonneg (outputWeight_nonneg s _)]
  calc
    _ ≤ (outputWeight s p.1 * (outputWeight s p.2.1 * outputWeight s p.2.2)) *
        (6 * embeddingConstant * (‖fourierCurl u p.1‖ *
          (‖fourierCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖))) :=
      mul_le_mul (outputWeight_triple_le s p) (norm_mode_le u p) (norm_nonneg _)
        (mul_nonneg (outputWeight_nonneg s _) (mul_nonneg (outputWeight_nonneg s _)
          (outputWeight_nonneg s _)))
    _ = _ := by unfold cubicEnvelope weightedCurlNorm outputWeight; ring

theorem summable_norm_weighted_mode (s : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (s + 1) u)) :
    Summable (fun p : TripleIndex ↦ ‖outputWeight s (tripleFrequency p) • mode u p‖) :=
  (summable_cubicEnvelope (weightedCurlNorm s u) (weightedCurlNorm_nonneg s u)
    (summable_weightedCurlNorm s u hu)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (norm_weighted_mode_le s u)

/-- An actual tensor L² field, not a prescribed regularity budget. -/
def weightedFlux (s : ℕ) (u : FourierVelocity) : H :=
  -∑' p : TripleIndex, outputWeight s (tripleFrequency p) • mode u p

theorem norm_weightedFlux_le (s : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (s + 1) u)) :
    ‖weightedFlux s u‖ ≤ 6 * embeddingConstant * (∑' k, weightedCurlNorm s u k) ^ 3 := by
  have hw := summable_weightedCurlNorm s u hu
  have hn := weightedCurlNorm_nonneg s u
  have hp := hw.mul_of_nonneg hw hn hn
  have ht := hw.mul_of_nonneg hp hn (fun p ↦ mul_nonneg (hn p.1) (hn p.2))
  have he : (∑' p : TripleIndex, cubicEnvelope (weightedCurlNorm s u) p) =
      6 * embeddingConstant * (∑' k, weightedCurlNorm s u k) ^ 3 := by
    unfold cubicEnvelope
    rw [tsum_mul_left, ← hw.tsum_mul_tsum hp ht, ← hw.tsum_mul_tsum hw hp]
    ring
  rw [weightedFlux, norm_neg]
  exact (norm_tsum_le_tsum_norm (summable_norm_weighted_mode s u hu)).trans
    (((summable_norm_weighted_mode s u hu).tsum_le_tsum (norm_weighted_mode_le s u)
      (summable_cubicEnvelope _ hn hw)).trans_eq he)

theorem projectedFlux_eq_neg_mode_series (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    projectedFlux 0 u = -∑' p : TripleIndex, mode u p := by
  simp_rw [mode_eq_exchangeMode u _ (hd _) (hd _)]
  exact projectedFlux_inviscid_eq_exchangeSeries u hu hr

theorem outputCoefficient_weightedFlux (s : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (s + 1) u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (n : Wavevector) :
    outputCoefficient (weightedFlux s u) n =
      outputWeight s n • outputCoefficient (projectedFlux 0 u) n := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ s + 1) hu
  rw [projectedFlux_eq_neg_mode_series u hu1 hd hr]
  simp only [weightedFlux, outputCoefficient, map_neg]
  rw [smul_neg]
  apply congrArg Neg.neg
  exact outputCoefficient_weighted_series tripleFrequency (tensorCoeff u) (outputWeight s)
    (outputWeight_neg s) (summable_norm_mode u hu1).of_norm
    (summable_norm_weighted_mode s u hu).of_norm n

theorem summable_weightedOutputNorm_sq (s : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (s + 1) u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    Summable (fun n ↦ weightedOutputNorm s (projectedFlux 0 u) n ^ 2) := by
  have h := summable_norm_outputCoefficient_sq (weightedFlux s u)
  simp_rw [outputCoefficient_weightedFlux s u hu hd hr, norm_smul,
    Real.norm_of_nonneg (outputWeight_nonneg s _)] at h
  exact h

theorem tsum_weightedOutputNorm_sq_le (s : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (s + 1) u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∑' n, weightedOutputNorm s (projectedFlux 0 u) n ^ 2) ≤ ‖weightedFlux s u‖ ^ 2 := by
  have h := tsum_norm_outputCoefficient_sq_le (weightedFlux s u)
  simp_rw [outputCoefficient_weightedFlux s u hu hd hr, norm_smul,
    Real.norm_of_nonneg (outputWeight_nonneg s _)] at h
  exact h

theorem summable_heatOutputNorm_sq {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    Summable (fun n ↦ heatOutputNorm ν σ u n ^ 2) :=
  summable_weightedOutputNorm_sq 2 (coefficients ν σ u)
    (summable_fourierMoment_coefficients hν hσ u 3 hu)
    (coefficients_transverse ν σ u hd) (coefficients_reality ν σ u hr)

theorem tsum_weightedOutputNorm_sq_le_curl_moment (s : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment (s + 1) u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    (∑' n, weightedOutputNorm s (projectedFlux 0 u) n ^ 2) ≤
      (6 * embeddingConstant * (∑' k, weightedCurlNorm s u k) ^ 3) ^ 2 :=
  (tsum_weightedOutputNorm_sq_le s u hu hd hr).trans
    (pow_le_pow_left₀ (norm_nonneg _) (norm_weightedFlux_le s u hu) 2)

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxWeightedOutput
