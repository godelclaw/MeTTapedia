import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierStretchingInteractionDynamics

/-!
# Initial-endpoint time budget for the exchanged stretching coefficient

Viscous damping pays the time integral of the exact amplitude-alignment
factor, up to the explicitly signed nonlinear work. The source is not
discarded or assumed to have an initial-data-controlled integral. The
result is a per-triple coefficient budget, not a bound on the squared
norm of a sum of many triples with repeated output frequencies.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierStretchingInteractionBudget

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeLocalInfiniteVelocity PeriodicGradientFluxTriple LongitudinalInviscidFluxFourier
open LongitudinalExchangeFluxFourier FourierVorticityPairDynamics
open FourierStretchingInteractionDynamics

def lowOutputRatio (p : TripleIndex) : ℝ :=
  ‖frequencyVec (p.2.1 + p.2.2)‖ / max ‖frequencyVec p.2.1‖ ‖frequencyVec p.2.2‖

def coefficientCost (u : FourierVelocity) (p : TripleIndex) : ℝ :=
  ∑ j, ‖coefficientVec (exchangeCoeff u p j)‖ ^ 2

theorem coefficientCost_le_interactionEnergy (u : FourierVelocity) (p : TripleIndex)
    (hl0 : p.2.1 ≠ 0) (hm0 : p.2.2 ≠ 0)
    (hl : modeDot p.2.1 (u p.2.1) = 0) (hm : modeDot p.2.2 (u p.2.2) = 0) :
    coefficientCost u p ≤ 4 * lowOutputRatio p ^ 2 * interactionEnergy u p := by
  simpa only [coefficientCost, lowOutputRatio, interactionEnergy, modeEnergy, pairEnergy,
    pairCross, ← norm_coefficientVec_sq, mul_assoc] using
    sum_exchangeCoeff_energy_le_low_output u p hl0 hm0 hl hm

variable {ν T B : ℝ} {u₀ : FourierVelocity}

theorem continuous_coefficientCost (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (p : TripleIndex) : Continuous (fun t ↦ coefficientCost (s.coefficients t) p) := by
  have hu := s.continuous
  have hc := continuous_curl_component s.coefficients hu
  have he (j i : Fin 3) : Continuous (fun t ↦ exchangeCoeff (s.coefficients t) p j i) := by
    simp only [exchangeCoeff, combinedStretchCoeff, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul, modeDot]
    fun_prop
  simp only [coefficientCost, norm_coefficientVec_sq]
  exact continuous_finsetSum Finset.univ (fun j _ ↦ continuous_coefficientEnergy _ (he j))

/-- This identity includes the true initial data, not only interior time intervals. -/
theorem interaction_energy_identity (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (hB : 0 ≤ B) (p : TripleIndex) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    interactionEnergy (s.coefficients t) p +
      2 * interactionDamping ν p * (∫ τ in (0 : ℝ)..t, interactionEnergy (s.coefficients τ) p) =
    interactionEnergy u₀ p + ∫ τ in (0 : ℝ)..t, interactionWork (s.coefficients τ) p := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hE : ContinuousOn (fun τ ↦ interactionEnergy (s.coefficients τ) p) (Set.Icc (0 : ℝ) t) :=
    (continuous_interactionEnergy s.coefficients s.continuous p).continuousOn
  have hW := (continuousOn_interactionWork s hB p).mono hsub
  have hiE : IntervalIntegrable (fun τ ↦ interactionEnergy (s.coefficients τ) p) volume 0 t :=
    hE.intervalIntegrable_of_Icc ht.1
  have hiW : IntervalIntegrable (fun τ ↦ interactionWork (s.coefficients τ) p) volume 0 t :=
    hW.intervalIntegrable_of_Icc ht.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hE
    (fun τ hτ ↦ hasDerivAt_interactionEnergy s p τ ⟨hτ.1, hτ.2.trans_le ht.2⟩)
    (hiW.sub (hiE.const_mul (2 * interactionDamping ν p)))
  rw [intervalIntegral.integral_sub hiW (hiE.const_mul _),
    intervalIntegral.integral_const_mul, s.initial] at h
  linarith

theorem scaled_integral_coefficientCost_le (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (hν : 0 ≤ ν) (hB : 0 ≤ B) (p : TripleIndex)
    (hl0 : p.2.1 ≠ 0) (hm0 : p.2.2 ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    interactionDamping ν p * (∫ τ in (0 : ℝ)..t, coefficientCost (s.coefficients τ) p) ≤
      2 * lowOutputRatio p ^ 2 *
        (interactionEnergy u₀ p + ∫ τ in (0 : ℝ)..t, interactionWork (s.coefficients τ) p) := by
  have hiC : IntervalIntegrable (fun τ ↦ coefficientCost (s.coefficients τ) p) volume 0 t :=
    (continuous_coefficientCost s p).intervalIntegrable 0 t
  have hiE : IntervalIntegrable (fun τ ↦ interactionEnergy (s.coefficients τ) p) volume 0 t :=
    (continuous_interactionEnergy s.coefficients s.continuous p).intervalIntegrable 0 t
  have h := intervalIntegral.integral_mono_on ht.1 hiC (hiE.const_mul (4 * lowOutputRatio p ^ 2))
    (fun τ _ ↦ coefficientCost_le_interactionEnergy (s.coefficients τ) p hl0 hm0
      (s.transverse τ p.2.1) (s.transverse τ p.2.2))
  rw [intervalIntegral.integral_const_mul] at h
  have hγ : 0 ≤ interactionDamping ν p := by
    unfold interactionDamping pairDamping modeDamping
    positivity
  have he := interaction_energy_identity s hB p t ht
  have hp := mul_le_mul_of_nonneg_left h hγ
  have hn := mul_nonneg (sq_nonneg (lowOutputRatio p))
    (interactionEnergy_nonneg (s.coefficients t) p)
  nlinarith

theorem integral_coefficientCost_le (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (hν : 0 < ν) (hB : 0 ≤ B) (p : TripleIndex)
    (hl0 : p.2.1 ≠ 0) (hm0 : p.2.2 ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, coefficientCost (s.coefficients τ) p) ≤
      (2 * lowOutputRatio p ^ 2 / interactionDamping ν p) *
        (interactionEnergy u₀ p + ∫ τ in (0 : ℝ)..t, interactionWork (s.coefficients τ) p) := by
  have h := scaled_integral_coefficientCost_le s hν.le hB p hl0 hm0 t ht
  have hp := interactionDamping_pos hν p hl0
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hp).mpr
  nlinarith only [h]

end Mettapedia.FluidDynamics.NavierStokes.FourierStretchingInteractionBudget
