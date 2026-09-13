import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorOutputBudget

/-!
# Heat-parameter continuity of the accumulated commutator energy

The nonlinear discrepancy is continuous in the auxiliary heat parameter.
A physical-time dominated-convergence argument gives continuity of its
accumulated coefficient energy, including zero heat parameter.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorParameter

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeCurlOutputTail PancakeGalerkinKineticEnergy
open PancakeSobolevFiberEnvelope PancakeInfiniteVelocityEnvelope PancakeLocalInfiniteVelocity
open InfiniteConvectionEnergy InfiniteFilteredEquation FourierHeatFlow
open FourierHeatCommutatorEnergy FourierHeatCommutatorTime FourierHeatCommutatorOutputBudget
open LocalKineticEnergy
open ExchangedFluxModeDynamics

theorem continuous_parameter_commutator {ν : ℝ} (hν : 0 ≤ ν)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (q : Wavevector) :
    Continuous (fun σ : Set.Ici (0 : ℝ) ↦ nonlinearCommutator ν σ u q) := by
  have hc (i : Fin 3) : Continuous (fun σ : Set.Ici (0 : ℝ) ↦
      subgridConvection (fun k ↦ (multiplier ν σ k : ℂ)) u q i) := by
    apply continuous_tsum (f := fun k (σ : Set.Ici (0 : ℝ)) ↦
      ((multiplier ν σ q : ℂ) - (multiplier ν σ k : ℂ) * (multiplier ν σ (q-k) : ℂ)) *
        outputFiber q u k i) ?_
      ((summable_pairEnvelope (fourierMoment 2 u) (fourierMoment_nonneg _ _) hu).prod_factor q) ?_
    · intro k
      unfold multiplier
      fun_prop
    · intro k σ
      rw [norm_mul]
      have hm : ‖(multiplier ν σ q : ℂ) - (multiplier ν σ k : ℂ) *
          (multiplier ν σ (q-k) : ℂ)‖ ≤ 1 := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        simpa only [add_sub_cancel] using abs_multiplier_defect_le_one hν σ.2 k (q-k)
      exact (mul_le_of_le_one_left (norm_nonneg _) hm).trans
        (norm_outputFiber_le_momentEnvelope u (fourierMoment 2 u)
          (fourierMoment_nonneg _ _) (fun _ ↦ le_rfl) q k i)
  have hl := (lerayLinear q).toContinuousLinearMap.continuous.comp
    (continuous_const.smul (continuous_pi hc) : Continuous (fun σ : Set.Ici (0 : ℝ) ↦
      (-unitTorusDerivativePhase) • subgridConvection (fun k ↦ (multiplier ν σ k : ℂ)) u q))
  apply hl.congr
  intro σ
  exact (congrFun (nonlinearCommutator_eq_subgridForce hν σ.2 u hu) q).symm

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)

include hg hsg hu

theorem continuousOn_integral_norm_commutator_sq (hν : 0 ≤ ν)
    (q : Wavevector) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ContinuousOn (fun σ ↦ ∫ τ in (0 : ℝ)..t,
      ‖coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q)‖ ^ 2) (Set.Ici 0) := by
  rw [continuousOn_iff_continuous_restrict]
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  apply intervalIntegral.continuous_of_dominated_interval
    (bound := fun _ ↦ ((2 * Real.pi) ^ 2 * kineticEnergy u₀ ^ 2) * ‖frequencyVec q‖ ^ 2)
  · intro σ
    have hi : IntervalIntegrable (fun τ ↦
        ‖coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q)‖ ^ 2) volume 0 t :=
      ((continuousOn_norm_commutator_sq s g hg hsg hu hν σ.2 q).mono
        hsub).intervalIntegrable_of_Icc ht.1
    simpa only [Set.uIoc_of_le ht.1] using hi.aestronglyMeasurable
  · intro σ
    filter_upwards with τ hτ
    have hτ' : τ ∈ Set.Icc (0 : ℝ) T := hsub ⟨(min_eq_left ht.1 ▸ hτ.1).le,
      max_eq_right ht.1 ▸ hτ.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := norm_nonlinearCommutator_sq_le_energy_sq hν σ.2 _
      (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτ')) q
    have he := pow_le_pow_left₀ (kineticEnergy_nonneg _)
      (energy_le_initial s hν g hg hsg hu τ hτ') 2
    apply hb.trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left he (sq_nonneg _))
      (mul_le_of_le_one_right (sq_nonneg _) (multiplier_le_one hν σ.2 q))
      (mul_nonneg (sq_nonneg _) (multiplier_pos ν σ q).le) (by positivity)
  · exact intervalIntegrable_const
  · filter_upwards with τ hτ
    have hτ' : τ ∈ Set.Icc (0 : ℝ) T := hsub ⟨(min_eq_left ht.1 ▸ hτ.1).le,
      max_eq_right ht.1 ▸ hτ.2⟩
    exact (((PiLp.continuous_toLp 2 _).comp (continuous_parameter_commutator hν _
      (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ hτ')) q)).norm.pow 2)

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorParameter
