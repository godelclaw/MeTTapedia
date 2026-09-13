import Mettapedia.Analysis.ExponentialMoments
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorParameter

/-!
# All-heat-parameter commutator budget with one inverse output derivative

The squared commutator is integrated in physical time, then over the entire
positive auxiliary heat axis. Summing with weight `(1 + |q|)⁻²` gives a
finite initial-energy budget. This is an inhomogeneous negative-order
coefficient norm, not the stronger weighted stretching-work estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorScaleBudget

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicComplexStretch PancakeCurlOutputTail
open PancakeSobolevFiberEnvelope PancakeLocalInfiniteVelocity PancakeInfinitePressureCoefficients
open InfiniteConvectionEnergy FourierHeatFlow FourierVorticityPairDynamics
open FourierHeatCommutatorTime FourierHeatCommutatorParameter PancakeLatticeDecayEnvelope
open Mettapedia.Analysis.ExponentialMoments

def accumulatedCoefficient (ν : ℝ) (u : ℝ → FourierVelocity) (σ t : ℝ) (q : Wavevector) : ℝ :=
  ∫ τ in (0 : ℝ)..t, ‖coefficientVec (nonlinearCommutator ν σ (u τ) q)‖ ^ 2

theorem accumulatedCoefficient_nonneg (ν : ℝ) (u : ℝ → FourierVelocity) (σ t : ℝ)
    (ht : 0 ≤ t) (q : Wavevector) : 0 ≤ accumulatedCoefficient ν u σ t q :=
  intervalIntegral.integral_nonneg_of_forall ht (fun _ ↦ sq_nonneg _)

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)

include hg hsg hu

theorem accumulatedCoefficient_le_exponential {σ : ℝ} (hν : 0 < ν) (hσ : 0 ≤ σ)
    (q : Wavevector) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    accumulatedCoefficient ν s.coefficients σ t q ≤
      (((2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 * kineticEnergy u₀ ^ 2) / 2) *
        (σ * Real.exp (-(modeDamping ν q * σ))) :=
  (integral_norm_commutator_sq_le_initial s g hg hsg hu hν hσ q t ht).trans_eq
    (by unfold multiplier; ring)

theorem accumulatedCoefficient_zero (hν : 0 < ν) {σ : ℝ} (hσ : 0 ≤ σ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    accumulatedCoefficient ν s.coefficients σ t 0 = 0 := by
  apply le_antisymm _ (accumulatedCoefficient_nonneg _ _ _ _ ht.1 _)
  have h := accumulatedCoefficient_le_exponential s g hg hsg hu hν hσ 0 t ht
  have hz : frequencyVec (0 : Wavevector) = 0 := by
    ext i
    simp [frequencyVec, coefficientVec, PancakePeriodicComplexStretch.wavevectorCoefficient]
  simpa only [hz, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, zero_mul, zero_div] using h

theorem integrableOn_accumulatedCoefficient (hν : 0 < ν)
    (q : Wavevector) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntegrableOn (fun σ ↦ accumulatedCoefficient ν s.coefficients σ t q) (Set.Ioi 0) := by
  by_cases hq : q = 0
  · subst q
    exact (integrableOn_zero : IntegrableOn (fun _ : ℝ ↦ (0 : ℝ)) (Set.Ioi 0)).congr_fun
      (fun σ hσ ↦ (accumulatedCoefficient_zero s g hg hsg hu hν hσ.le t ht).symm)
      measurableSet_Ioi
  have hr : 0 < ‖frequencyVec q‖ := lt_of_lt_of_le zero_lt_one (one_le_norm_frequencyVec hq)
  have ha : 0 < modeDamping ν q := by unfold modeDamping; positivity
  have hc : AEStronglyMeasurable (fun σ ↦ accumulatedCoefficient ν s.coefficients σ t q)
      (volume.restrict (Set.Ioi 0)) :=
    ((continuousOn_integral_norm_commutator_sq s g hg hsg hu hν.le q t ht).mono
      Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  apply ((integrableOn_mul_exp_neg_mul ha).const_mul
    (((2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 * kineticEnergy u₀ ^ 2) / 2)).mono' hc
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  rw [Real.norm_eq_abs, abs_of_nonneg (accumulatedCoefficient_nonneg _ _ _ _ ht.1 _)]
  exact accumulatedCoefficient_le_exponential s g hg hsg hu hν hσ.le q t ht

theorem integral_accumulatedCoefficient_le_initial (hν : 0 < ν)
    (q : Wavevector) (hq : q ≠ 0) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ σ : ℝ in Set.Ioi 0, accumulatedCoefficient ν s.coefficients σ t q) ≤
      kineticEnergy u₀ ^ 2 / (2 * ν ^ 2 * (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2) := by
  have hr : 0 < ‖frequencyVec q‖ := lt_of_lt_of_le zero_lt_one (one_le_norm_frequencyVec hq)
  have ha : 0 < modeDamping ν q := by unfold modeDamping; positivity
  have h := integral_mono_ae (integrableOn_accumulatedCoefficient s g hg hsg hu hν q t ht)
    ((integrableOn_mul_exp_neg_mul ha).const_mul
      (((2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 * kineticEnergy u₀ ^ 2) / 2))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
      exact accumulatedCoefficient_le_exponential s g hg hsg hu hν hσ.le q t ht)
  rw [integral_const_mul, integral_mul_exp_neg_mul ha] at h
  apply h.trans_eq
  unfold modeDamping
  field_simp

/-- Each output is charged once; the comparison has summable fourth-power decay. -/
theorem weighted_integral_le_decay (hν : 0 < ν)
    (q : Wavevector) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (1 / (1 + ‖frequencyVec q‖) ^ 2) *
        (∫ σ : ℝ in Set.Ioi 0, accumulatedCoefficient ν s.coefficients σ t q) ≤
      (2 * kineticEnergy u₀ ^ 2 / (ν ^ 2 * (2 * Real.pi) ^ 2)) * latticeDecayWeight q := by
  by_cases hq : q = 0
  · subst q
    have hz : (∫ σ : ℝ in Set.Ioi 0, accumulatedCoefficient ν s.coefficients σ t 0) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
      exact accumulatedCoefficient_zero s g hg hsg hu hν hσ.le t ht
    rw [hz, mul_zero]
    exact mul_nonneg (by positivity) (latticeDecayWeight_pos 0).le
  have hr := one_le_norm_frequencyVec hq
  have hr0 : 0 < ‖frequencyVec q‖ := lt_of_lt_of_le zero_lt_one hr
  have h := mul_le_mul_of_nonneg_left
    (integral_accumulatedCoefficient_le_initial s g hg hsg hu hν q hq t ht)
    (by positivity : 0 ≤ 1 / (1 + ‖frequencyVec q‖) ^ 2)
  apply h.trans
  have hp : (1 + ‖frequencyVec q‖) ^ 2 ≤ 4 * ‖frequencyVec q‖ ^ 2 := by
    nlinarith [sq_nonneg (‖frequencyVec q‖ - 1)]
  have hc := mul_le_mul_of_nonneg_left hp (sq_nonneg (kineticEnergy u₀))
  unfold latticeDecayWeight
  field_simp
  nlinarith

theorem summable_weighted_integral (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Summable (fun q : Wavevector ↦ (1 / (1 + ‖frequencyVec q‖) ^ 2) *
      (∫ σ : ℝ in Set.Ioi 0, accumulatedCoefficient ν s.coefficients σ t q)) :=
  (summable_latticeDecayWeight.mul_left
    (2 * kineticEnergy u₀ ^ 2 / (ν ^ 2 * (2 * Real.pi) ^ 2))).of_nonneg_of_le
      (fun q ↦ mul_nonneg (by positivity) (integral_nonneg
        (fun σ ↦ accumulatedCoefficient_nonneg _ _ _ _ ht.1 q)))
      (fun q ↦ weighted_integral_le_decay s g hg hsg hu hν q t ht)

theorem tsum_weighted_integral_le_initial (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∑' q : Wavevector, (1 / (1 + ‖frequencyVec q‖) ^ 2) *
      (∫ σ : ℝ in Set.Ioi 0, accumulatedCoefficient ν s.coefficients σ t q)) ≤
        (2 * kineticEnergy u₀ ^ 2 / (ν ^ 2 * (2 * Real.pi) ^ 2)) * ∑' q, latticeDecayWeight q := by
  have h := Summable.tsum_le_tsum (fun q ↦ weighted_integral_le_decay s g hg hsg hu hν q t ht)
    (summable_weighted_integral s g hg hsg hu hν t ht)
    (summable_latticeDecayWeight.mul_left
      (2 * kineticEnergy u₀ ^ 2 / (ν ^ 2 * (2 * Real.pi) ^ 2)))
  simpa only [tsum_mul_left] using h

open scoped ComplexConjugate
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open PancakePeriodicVorticityEquation

omit hg hsg hu in
/-- The solution, convergence hypotheses, and all-scale budget come from physical data. -/
theorem exists_physical_local_scale_budget (ν : ℝ) (hν : 0 < ν)
    (f : UnitAddTorus (Fin 3) → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 8 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          (∀ q, IntegrableOn (fun σ ↦ accumulatedCoefficient ν s.coefficients σ t q) (Set.Ioi 0)) ∧
          Summable (fun q : Wavevector ↦ (1 / (1 + ‖frequencyVec q‖) ^ 2) *
            (∫ σ : ℝ in Set.Ioi 0, accumulatedCoefficient ν s.coefficients σ t q)) ∧
          (∑' q : Wavevector, (1 / (1 + ‖frequencyVec q‖) ^ 2) *
            (∫ σ : ℝ in Set.Ioi 0, accumulatedCoefficient ν s.coefficients σ t q)) ≤
              (2 * kineticEnergy (torusFourierVelocity f) ^ 2 / (ν ^ 2 * (2 * Real.pi) ^ 2)) *
                ∑' q, latticeDecayWeight q := by
  obtain ⟨T, hT, B, hB, s, g, hg, hsg, hu⟩ :=
    exists_physical_localMomentEnvelope 2 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, fun t ht ↦
    ⟨fun q ↦ integrableOn_accumulatedCoefficient s g hg hsg hu hν q t ht,
      summable_weighted_integral s g hg hsg hu hν t ht,
      tsum_weighted_integral_le_initial s g hg hsg hu hν t ht⟩⟩

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorScaleBudget
