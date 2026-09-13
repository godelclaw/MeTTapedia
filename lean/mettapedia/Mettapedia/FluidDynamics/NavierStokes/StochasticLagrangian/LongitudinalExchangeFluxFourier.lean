import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LerayStretchExchange
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicGradientFluxPair

/-!
# Exchange-symmetric reconstruction of the actual inviscid flux

Exchange of the two inner inputs is a bijection of the infinite triple
index. Averaging the two ordered contributions therefore preserves the
physical flux. Curl recovery turns this average into a Leray-projector
difference acting on a vorticity cross product before any norm is taken.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LongitudinalExchangeFluxFourier

open Mettapedia.Analysis.UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PeriodicGradientFluxSymbol PeriodicGradientFluxPair PeriodicGradientFluxTriple
open LongitudinalInviscidFluxFourier LongitudinalGradientFlux LerayStretchExchange
open PancakePeriodicVorticityEquation PancakeHigherDerivativeMoments
open PancakeCurlOutputTail PancakeBlockReality

def innerExchange : TripleIndex ≃ TripleIndex :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)

theorem innerExchange_apply (p : TripleIndex) : innerExchange p = (p.1, (p.2.2, p.2.1)) := rfl

theorem tripleFrequency_innerExchange (p : TripleIndex) :
    tripleFrequency (innerExchange p) = tripleFrequency p := by
  change p.1 + (p.2.2 + p.2.1) = p.1 + (p.2.1 + p.2.2)
  rw [add_comm p.2.2 p.2.1]

def exchangeCoeff (u : FourierVelocity) (p : TripleIndex) (j : Fin 3) : VelocityCoefficient :=
  (1 / 2 : ℝ) • (combinedStretchCoeff u p j + combinedStretchCoeff u (innerExchange p) j)

def combinedMode (u : FourierVelocity) (p : TripleIndex) :=
  toTensorL2 (fun j ↦ realMode (tripleFrequency p) (combinedStretchCoeff u p j))

def exchangeMode (u : FourierVelocity) (p : TripleIndex) :=
  toTensorL2 (fun j ↦ realMode (tripleFrequency p) (exchangeCoeff u p j))

theorem exchangeMode_eq_average (u : FourierVelocity) (p : TripleIndex) :
    exchangeMode u p = (1 / 2 : ℝ) • (combinedMode u p + combinedMode u (innerExchange p)) := by
  simp only [exchangeMode, combinedMode, exchangeCoeff, tripleFrequency_innerExchange,
    realMode, map_smul, map_add]
  change (tensorEmbedding (d := Fin 3) (E := EuclideanSpace ℝ (Fin 3))) ((1 / 2 : ℝ) •
    ((fun j ↦ realModeCLM (tripleFrequency p) (combinedStretchCoeff u p j)) +
     (fun j ↦ realModeCLM (tripleFrequency p) (combinedStretchCoeff u (innerExchange p) j)))) = _
  rw [map_smul, map_add]
  rfl

theorem summable_combinedMode (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Summable (combinedMode u) := by
  have he (p : TripleIndex) : combinedMode u p =
      ∑ r : Fin 3, toTensorL2 (fun j ↦
        realMode (tripleFrequency p) (depletedStretchCoeff u r p j)) := by
    simp only [combinedMode, toTensorL2, ← map_sum]
    congr 1
    funext j
    change realModeCLM (tripleFrequency p) (combinedStretchCoeff u p j) =
      ∑ r, realModeCLM (tripleFrequency p) (depletedStretchCoeff u r p j)
    rw [← map_sum, sum_depletedStretchCoeff]
  change Summable (fun p ↦ combinedMode u p)
  simp_rw [he]
  exact summable_sum (fun r _ ↦ summable_depletedTripleModes u hu r)

theorem summable_exchangeMode (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Summable (exchangeMode u) := by
  change Summable (fun p ↦ exchangeMode u p)
  simp_rw [exchangeMode_eq_average]
  exact ((summable_combinedMode u hu).add
    (innerExchange.summable_iff.mpr (summable_combinedMode u hu))).const_smul _

theorem tsum_exchangeMode (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    ∑' p, exchangeMode u p = ∑' p, combinedMode u p := by
  have h := summable_combinedMode u hu
  have hs := innerExchange.summable_iff.mpr h
  simp_rw [exchangeMode_eq_average]
  have hscale := (h.add hs).tsum_const_smul (1 / 2 : ℝ)
  simp only [Function.comp_apply] at hscale
  have hadd := h.tsum_add hs
  simp only [Function.comp_apply] at hadd
  rw [hscale, hadd, innerExchange.tsum_eq]
  module

theorem projectedFlux_inviscid_eq_exchangeSeries (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ n, u (-n) = coefficientConjugate (u n)) :
    projectedFlux 0 u = -∑' p, exchangeMode u p := by
  rw [tsum_exchangeMode u hu, projectedFlux_inviscid_eq_combinedTripleSeries u hu hr]
  rfl

theorem exchangeCoeff_eq_leray_difference (u : FourierVelocity) (p : TripleIndex) (j : Fin 3)
    (hl : modeDot p.2.1 (u p.2.1) = 0) (hm : modeDot p.2.2 (u p.2.2) = 0) :
    exchangeCoeff u p j =
      (1 / 2 : ℝ) •
        (((tripleFrequency p j : ℂ) / modeSquare (tripleFrequency p) *
          modeDot (p.2.1 + p.2.2) (fourierCurl u p.1)) •
        (lerayMode p.2.1 (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2)) -
         lerayMode p.2.2 (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2)))) := by
  rw [← stretch_pair_add_exchange u p.2.1 p.2.2 hl hm]
  simp only [exchangeCoeff, combinedStretchCoeff, innerExchange_apply, tripleFrequency]
  rw [add_comm p.2.2 p.2.1]
  congr 1
  simp only [smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring

/-- Projection onto actual gradient modes is contractive on each rank-one tensor. -/
theorem sum_norm_projected_rankOne_le (n : Wavevector) (a b : VelocityCoefficient) :
    (∑ j, ‖coefficientVec (projectedCoeff n (fun i ↦ a i • b) j)‖ ^ 2) ≤
      ‖coefficientVec a‖ ^ 2 * ‖coefficientVec b‖ ^ 2 := by
  rw [sum_norm_projectedCoeff_sq, contraction_rankOne]
  change ‖modeDot n a • coefficientVec b‖ ^ 2 / ‖frequencyVec n‖ ^ 2 ≤ _
  rw [norm_smul, mul_pow]
  have hd : ‖modeDot n a‖ ≤ ‖frequencyVec n‖ * ‖coefficientVec a‖ := by
    rw [← inner_frequencyVec]
    exact norm_inner_le_norm _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hd 2
  rw [mul_pow] at hsq
  by_cases hn : ‖frequencyVec n‖ = 0
  · simp only [hn, zero_pow (by omega : 2 ≠ 0), div_zero]
    positivity
  · apply (div_le_iff₀ (sq_pos_of_ne_zero hn)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖coefficientVec b‖)]

theorem exchangeCoeff_eq_projected (u : FourierVelocity) (p : TripleIndex) (j : Fin 3)
    (hl : modeDot p.2.1 (u p.2.1) = 0) (hm : modeDot p.2.2 (u p.2.2) = 0) :
    exchangeCoeff u p j = (1 / 2 : ℝ) • projectedCoeff (tripleFrequency p)
      (fun i ↦ fourierCurl u p.1 i •
        (lerayMode p.2.1 (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2)) -
         lerayMode p.2.2 (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2)))) j := by
  rw [exchangeCoeff_eq_leray_difference u p j hl hm]
  change _ = (1 / 2 : ℝ) • projectedCoeff (p.1 + (p.2.1 + p.2.2)) _ j
  rw [projectedCoeff_rankOne_of_transverse _ _ _ _ (fourierCurl_transverse p.1 u)]
  rfl

theorem sum_exchangeCoeff_energy_le (u : FourierVelocity) (p : TripleIndex)
    (hl : modeDot p.2.1 (u p.2.1) = 0) (hm : modeDot p.2.2 (u p.2.2) = 0) :
    (∑ j, ‖coefficientVec (exchangeCoeff u p j)‖ ^ 2) ≤
      (1 / 4 : ℝ) * ‖coefficientVec (fourierCurl u p.1)‖ ^ 2 *
        ‖coefficientVec
          (lerayMode p.2.1 (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2)) -
           lerayMode p.2.2 (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2)))‖ ^ 2 := by
  let b := lerayMode p.2.1 (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2)) -
    lerayMode p.2.2 (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2))
  have he (j : Fin 3) : ‖coefficientVec (exchangeCoeff u p j)‖ ^ 2 =
      (1 / 4 : ℝ) * ‖coefficientVec
        (projectedCoeff (tripleFrequency p) (fun i ↦ fourierCurl u p.1 i • b) j)‖ ^ 2 := by
    rw [exchangeCoeff_eq_projected u p j hl hm]
    change ‖(1 / 2 : ℝ) • coefficientVec
      (projectedCoeff (tripleFrequency p) (fun i ↦ fourierCurl u p.1 i • b) j)‖ ^ 2 = _
    rw [norm_smul, mul_pow]
    norm_num
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left
    (sum_norm_projected_rankOne_le (tripleFrequency p) (fourierCurl u p.1) b)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans_eq (by ring)

/-- The inner low-output gain survives the projection onto the full triple output. -/
theorem sum_exchangeCoeff_energy_le_low_output (u : FourierVelocity) (p : TripleIndex)
    (hl0 : p.2.1 ≠ 0) (hm0 : p.2.2 ≠ 0)
    (hl : modeDot p.2.1 (u p.2.1) = 0) (hm : modeDot p.2.2 (u p.2.2) = 0) :
    (∑ j, ‖coefficientVec (exchangeCoeff u p j)‖ ^ 2) ≤
      4 * (‖frequencyVec (p.2.1 + p.2.2)‖ /
        max ‖frequencyVec p.2.1‖ ‖frequencyVec p.2.2‖) ^ 2 *
      ‖coefficientVec (fourierCurl u p.1)‖ ^ 2 *
      ‖coefficientVec (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2))‖ ^ 2 := by
  have h := norm_lerayMode_sub_le_output_max p.2.1 p.2.2
    (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2)) hl0 hm0
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  refine (sum_exchangeCoeff_energy_le u p hl hm).trans ?_
  calc
    _ ≤ (1 / 4 : ℝ) * ‖coefficientVec (fourierCurl u p.1)‖ ^ 2 *
        (4 * ‖frequencyVec (p.2.1 + p.2.2)‖ /
          max ‖frequencyVec p.2.1‖ ‖frequencyVec p.2.2‖ *
          ‖coefficientVec (coefficientCross (fourierCurl u p.2.1) (fourierCurl u p.2.2))‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- The exchanged triple sum enters the same joint cost as the physical viscous pairs. -/
theorem jointSeriesCost_eq_exchangeSeries (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ n, u (-n) = coefficientConjugate (u n)) :
    jointSeriesCost ν u =
      ‖-(∑' p, exchangeMode u p) +
        (2 * ν) • ∑ r : Fin 3, ∑' p : Wavevector × Wavevector,
          toTensorL2 (fun j ↦ realMode (p.1 + p.2)
            (LongitudinalViscousFluxFourier.depletedPairCoeff u r p j))‖ ^ 2 := by
  rw [← projectedFluxSquare_eq_jointSeriesCost ν u hu hr,
    LongitudinalViscousFluxFourier.projectedFluxSquare_eq_pairSeries ν u hu hr,
    projectedFlux_inviscid_eq_exchangeSeries u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) hr]

end Mettapedia.FluidDynamics.NavierStokes.LongitudinalExchangeFluxFourier
