import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorTime
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatLatticeEnergy

/-!
# Initial-energy budget for all heat-commutator outputs

The full square-summable coefficient energy, not merely finite output
truncations, is continuous in physical time and is paid by initial kinetic
energy at every positive auxiliary heat parameter. The exact Gaussian
lattice cost remains explicit. No integration down to zero heat parameter
or estimate of the vorticity-weighted flux variation is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorOutputBudget

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeGalerkinKineticEnergy PancakeSobolevFiberEnvelope
open PancakePeriodicVorticityEquation PancakeLocalInfiniteVelocity
open InfiniteConvectionEnergy FourierHeatFlow FourierHeatCommutatorDecay
open FourierHeatCommutatorTime FourierHeatLatticeEnergy LocalKineticEnergy

theorem norm_nonlinearCommutator_sq_le_energy_sq {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (q : Wavevector) :
    ‖coefficientVec (nonlinearCommutator ν σ u q)‖ ^ 2 ≤
      ((2 * Real.pi) ^ 2 * kineticEnergy u ^ 2) *
        (‖frequencyVec q‖ ^ 2 * multiplier ν σ q) := by
  have he : Summable (fun k ↦ ‖coefficientVec (u k)‖ ^ 2) := by
    simpa only [norm_coefficientVec_sq] using InfiniteKineticCancellation.summable_coefficientEnergy u
      (InfiniteKineticCancellation.summable_amplitude u (summable_firstMoment_of_second u hu))
  rw [nonlinearCommutator_eq_subgridForce hν hσ u hu]
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_heat_subgridForce_le_energy_decay hν hσ u he q) 2
  apply h.trans_eq
  simp only [mul_pow, multiplier_half_sq]
  ring

theorem summable_norm_commutator_sq {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    Summable (fun q ↦ ‖coefficientVec (nonlinearCommutator ν σ u q)‖ ^ 2) :=
  ((summable_frequency_sq_mul_multiplier hν hσ).mul_left
    ((2 * Real.pi) ^ 2 * kineticEnergy u ^ 2)).of_nonneg_of_le
      (fun _ ↦ sq_nonneg _) (norm_nonlinearCommutator_sq_le_energy_sq hν.le hσ.le u hu)

theorem commutatorEnergy_le_energy_enstrophy {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ k, modeDot k (u k) = 0) :
    kineticEnergy (nonlinearCommutator ν σ u) ≤
      ((2 * ν * σ) * (2 * Real.pi) ^ 2 * outputEnergyCost ν σ) *
        (kineticEnergy u * kineticEnergy (fourierCurl u)) := by
  have hs := (summable_frequency_sq_mul_multiplier hν hσ).mul_left
    ((2 * ν * σ) * (2 * Real.pi) ^ 2 * (kineticEnergy u * kineticEnergy (fourierCurl u)))
  have hb (q : Wavevector) : ‖coefficientVec (nonlinearCommutator ν σ u q)‖ ^ 2 ≤
      ((2 * ν * σ) * (2 * Real.pi) ^ 2 * (kineticEnergy u * kineticEnergy (fourierCurl u))) *
        (‖frequencyVec q‖ ^ 2 * multiplier ν σ q) :=
    (norm_nonlinearCommutator_sq_le_decay hν.le hσ.le u hu hd q).trans_eq (by ring)
  have h := Summable.tsum_le_tsum hb (summable_norm_commutator_sq hν hσ u hu) hs
  simp only [tsum_mul_left] at h
  exact h.trans_eq (by unfold outputEnergyCost; ring)

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)

include hg hsg hu

theorem continuousOn_commutatorEnergy {σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ) :
    ContinuousOn (fun t ↦ kineticEnergy (nonlinearCommutator ν σ (s.coefficients t)))
      (Set.Icc (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_tsum (fun q ↦ continuousOn_iff_continuous_restrict.mp
    (continuousOn_norm_commutator_sq s g hg hsg hu hν.le hσ.le q))
    ((summable_frequency_sq_mul_multiplier hν hσ).mul_left
      ((2 * Real.pi) ^ 2 * kineticEnergy u₀ ^ 2))
  intro q t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb := norm_nonlinearCommutator_sq_le_energy_sq hν.le hσ.le _
    (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t t.2)) q
  apply hb.trans
  have he := energy_le_initial s hν.le g hg hsg hu t t.2
  have he2 := pow_le_pow_left₀ (kineticEnergy_nonneg _) he 2
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he2 (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (multiplier_pos ν σ q).le)

/-- The entire infinite output energy is paid, at fixed positive heat parameter. -/
theorem integral_commutatorEnergy_le_initial {σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, kineticEnergy (nonlinearCommutator ν σ (s.coefficients τ))) ≤
      (σ / 2) * (2 * Real.pi) ^ 2 * outputEnergyCost ν σ * kineticEnergy u₀ ^ 2 := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hi : IntervalIntegrable (fun τ ↦ kineticEnergy (nonlinearCommutator ν σ (s.coefficients τ)))
      volume 0 t := ((continuousOn_commutatorEnergy s g hg hsg hu hν hσ).mono
        hsub).intervalIntegrable_of_Icc ht.1
  have h := integral_le_of_energy_enstrophy_majorant_ae s hν g hg hsg hu t ht
    (fun τ ↦ kineticEnergy (nonlinearCommutator ν σ (s.coefficients τ)))
    ((2 * ν * σ) * (2 * Real.pi) ^ 2 * outputEnergyCost ν σ)
    (mul_nonneg (by positivity) (outputEnergyCost_nonneg ν σ)) hi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact commutatorEnergy_le_energy_enstrophy hν hσ _
        (hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ))) (s.transverse τ))
  apply h.trans_eq
  field_simp
  ring

open scoped ComplexConjugate
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks

omit hg hsg hu in
theorem exists_physical_local_output_budget (ν : ℝ) (hν : 0 < ν)
    (f : UnitAddTorus (Fin 3) → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 8 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ σ > (0 : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) T,
          (∫ τ in (0 : ℝ)..t, kineticEnergy (nonlinearCommutator ν σ (s.coefficients τ))) ≤
            (σ / 2) * (2 * Real.pi) ^ 2 * outputEnergyCost ν σ *
              kineticEnergy (torusFourierVelocity f) ^ 2 := by
  obtain ⟨T, hT, B, hB, s, g, hg, hsg, hu⟩ :=
    exists_physical_localMomentEnvelope 2 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, fun _ hσ ↦
    integral_commutatorEnergy_le_initial s g hg hsg hu hν hσ⟩

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorOutputBudget
