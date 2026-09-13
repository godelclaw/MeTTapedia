import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorDecay

/-!
# Initial-energy payment for heat-commutator output coefficients

The actual unforced energy-square identity pays the energy-enstrophy
majorant. The result has no local-envelope size, final-time, or unresolved
input-count factor. Its explicit output-frequency cost remains and is
not a bound for the full nonlinear flux variation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorTime

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail PancakeGalerkinKineticEnergy
open PancakeSobolevFiberEnvelope PancakePeriodicVorticityEquation
open PancakeInfiniteVelocityEnvelope PancakeLocalInfiniteVelocity
open InfiniteConvectionEnergy InfiniteFilteredEquation FourierHeatFlow
open FourierHeatCommutatorEnergy LocalKineticEnergy ExchangedFluxModeDynamics
open FourierHeatCommutatorDecay

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)

include hg hsg hu

theorem continuous_heat_subgrid_component {σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (q : Wavevector) (i : Fin 3) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      subgridConvection (fun k ↦ (multiplier ν σ k : ℂ)) (s.coefficients t) q i) := by
  let mask : Wavevector → ℂ := fun k ↦
    (multiplier ν σ q : ℂ) - (multiplier ν σ k : ℂ) * (multiplier ν σ (q-k) : ℂ)
  have hm (k : Wavevector) : ‖mask k‖ ≤ 1 := by
    dsimp only [mask]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [add_sub_cancel] using abs_multiplier_defect_le_one hν hσ k (q-k)
  apply continuous_tsum (f := fun k (t : Set.Icc (0 : ℝ) T) ↦ mask k * outputFiber q (s.coefficients t) k i)
    ?_ ((summable_pairEnvelope g hg hsg).prod_factor q) ?_
  · intro k
    apply continuous_const.mul
    change Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      (∑ j : Fin 3, (q j : ℂ) * s.coefficients t k j) * s.coefficients t (q-k) i)
    exact (continuous_finsetSum _ (fun j _ ↦ continuous_const.mul
      ((s.continuous k j).comp continuous_subtype_val))).mul
        ((s.continuous (q-k) i).comp continuous_subtype_val)
  · intro k t
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hm k)).trans
      (norm_outputFiber_le_momentEnvelope _ g hg (hu t t.2) q k i)

theorem continuous_nonlinearCommutator {σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (q : Wavevector) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ nonlinearCommutator ν σ (s.coefficients t) q) := by
  have hc := continuous_pi (continuous_heat_subgrid_component s g hg hsg hu hν hσ q)
  have hl := (lerayLinear q).toContinuousLinearMap.continuous.comp
    (continuous_const.smul hc : Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      (-unitTorusDerivativePhase) •
        subgridConvection (fun k ↦ (multiplier ν σ k : ℂ)) (s.coefficients t) q))
  apply hl.congr
  intro t
  exact (congrFun (nonlinearCommutator_eq_subgridForce hν hσ (s.coefficients t)
    (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t t.2))) q).symm

theorem continuousOn_norm_commutator_sq {σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (q : Wavevector) :
    ContinuousOn (fun t ↦ ‖coefficientVec (nonlinearCommutator ν σ (s.coefficients t) q)‖ ^ 2)
      (Set.Icc (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_restrict]
  exact (((PiLp.continuous_toLp 2 _).comp
    (continuous_nonlinearCommutator s g hg hsg hu hν hσ q)).norm.pow 2)

/-- The coefficient cost is paid solely by initial kinetic energy. -/
theorem integral_norm_commutator_sq_le_initial {σ : ℝ} (hν : 0 < ν) (hσ : 0 ≤ σ)
    (q : Wavevector) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, ‖coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q)‖ ^ 2) ≤
      (σ / 2) * ((2 * Real.pi) * ‖frequencyVec q‖) ^ 2 * multiplier ν σ q * kineticEnergy u₀ ^ 2 := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hi : IntervalIntegrable (fun τ ↦
      ‖coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q)‖ ^ 2) volume 0 t :=
    ((continuousOn_norm_commutator_sq s g hg hsg hu hν.le hσ q).mono hsub).intervalIntegrable_of_Icc ht.1
  have h := integral_le_of_energy_enstrophy_majorant_ae s hν g hg hsg hu t ht
    (fun τ ↦ ‖coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q)‖ ^ 2)
    ((2 * ν * σ) * ((2 * Real.pi) * ‖frequencyVec q‖) ^ 2 * multiplier ν σ q)
    (mul_nonneg (by positivity) (multiplier_pos ν σ q).le) hi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact norm_nonlinearCommutator_sq_le_decay hν.le hσ _
        (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ))) (s.transverse τ) q)
  apply h.trans_eq
  field_simp
  ring

/-- A finite weighted output sum retains its exact frequency cost. -/
theorem integral_weighted_output_sum_le_initial {σ : ℝ} (hν : 0 < ν) (hσ : 0 ≤ σ)
    (P : Finset Wavevector) (w : Wavevector → ℝ) (hw : ∀ q ∈ P, 0 ≤ w q)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, ∑ q ∈ P,
      w q * ‖coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q)‖ ^ 2) ≤
      (σ / 2) * (2 * Real.pi) ^ 2 * kineticEnergy u₀ ^ 2 *
        ∑ q ∈ P, w q * ‖frequencyVec q‖ ^ 2 * multiplier ν σ q := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  rw [intervalIntegral.integral_finsetSum]
  · calc
      _ = ∑ q ∈ P, w q *
          (∫ τ in (0 : ℝ)..t, ‖coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q)‖ ^ 2) := by
        simp only [intervalIntegral.integral_const_mul]
      _ ≤ ∑ q ∈ P, w q * ((σ / 2) * ((2 * Real.pi) * ‖frequencyVec q‖) ^ 2 *
          multiplier ν σ q * kineticEnergy u₀ ^ 2) :=
        Finset.sum_le_sum (fun q hq ↦ mul_le_mul_of_nonneg_left
          (integral_norm_commutator_sq_le_initial s g hg hsg hu hν hσ q t ht) (hw q hq))
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
  · intro q hq
    exact (((continuousOn_norm_commutator_sq s g hg hsg hu hν.le hσ q).mono hsub).const_mul
      (w q)).intervalIntegrable_of_Icc ht.1

open scoped ComplexConjugate
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks

omit hg hsg hu in
/-- The local solution and convergence envelopes are constructed from physical data. -/
theorem exists_physical_local_commutator_budget (ν : ℝ) (hν : 0 < ν)
    (f : UnitAddTorus (Fin 3) → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 8 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ σ ≥ (0 : ℝ), ∀ q, ∀ t ∈ Set.Icc (0 : ℝ) T,
          (∫ τ in (0 : ℝ)..t, ‖coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q)‖ ^ 2) ≤
            (σ / 2) * ((2 * Real.pi) * ‖frequencyVec q‖) ^ 2 * multiplier ν σ q *
              kineticEnergy (torusFourierVelocity f) ^ 2 := by
  obtain ⟨T, hT, B, hB, s, g, hg, hsg, hu⟩ :=
    exists_physical_localMomentEnvelope 2 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, fun _ hσ ↦
    integral_norm_commutator_sq_le_initial s g hg hsg hu hν hσ⟩

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorTime
