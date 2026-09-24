import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCommonGalerkinWindow

/-!
# Time-integrated Sobolev dissipation on the common interval

The absorbed differential estimate pays the integrated third-order
viscous quantity with the initial second-order energy and the bounded
quadratic growth cost. Its integrability is derived from the constructed
finite coefficient equation, not assumed of an unknown trajectory.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevTimeBudget

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeLocalVelocityExistence PancakeLocalVelocityEnergy
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeSobolevAbsorption
open PancakeUniformLocalSobolev PancakeCommonGalerkinWindow
open PancakeArbitraryDataBlocks PancakeContinuousCoordinateJet

theorem integrated_dissipation_of_rate_le (E dE D : ℝ → ℝ) (mu A T : ℝ)
    (hT : 0 ≤ T)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt E (dE t) t)
    (hD : ContinuousOn D (Set.Icc (0 : ℝ) T))
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, dE t + mu * D t ≤ A) :
    E T + mu * (∫ t in (0 : ℝ)..T, D t) ≤ E 0 + A * T := by
  have hE : ContinuousOn E (Set.Icc (0 : ℝ) T) :=
    fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  have hphi : ContinuousOn (fun t ↦ mu * D t - A) (Set.Icc (0 : ℝ) T) :=
    (hD.const_mul mu).sub continuousOn_const
  have hi := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hT hE.neg
    (fun t ht ↦ (hd t ⟨ht.1.le, ht.2.le⟩).neg.hasDerivWithinAt)
    hphi.integrableOn_Icc (fun t ht ↦ by
      have h := hr t ⟨ht.1.le, ht.2.le⟩
      linarith)
  have hDi : IntervalIntegrable D MeasureTheory.volume 0 T :=
    hD.intervalIntegrable_of_Icc hT
  rw [intervalIntegral.integral_sub (hDi.const_mul mu) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hi
  simp only [sub_zero, smul_eq_mul] at hi
  linarith

theorem continuousOn_sobolevDissipation {M : Finset Wavevector} {nu T : ℝ}
    {u₀ : FourierVelocity} (s : LocalVelocitySolution M nu u₀ T) :
    ContinuousOn (fun t ↦ sobolevDissipation M (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  simp_rw [sobolevDissipation_eq]
  apply continuousOn_finsetSum
  intro q hq
  apply ContinuousOn.const_mul
  apply continuousOn_finsetSum
  intro i hi
  exact Complex.continuous_normSq.comp_continuousOn (continuousOn_coefficients s q i)

/-- A bounded second-order energy pays the exact integrated viscous term. -/
theorem localSolution_integrated_sobolev {M : Finset Wavevector} {nu T : ℝ}
    {u₀ : FourierVelocity} (s : LocalVelocitySolution M nu u₀ T) (hnu : 0 < nu)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (B : ℝ)
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) T, sobolevEnergy M (s.coefficients t) ≤ B)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    sobolevEnergy M (s.coefficients t) +
      nu * (2 * Real.pi)^2 * (∫ tau in (0 : ℝ)..t, sobolevDissipation M (s.coefficients tau)) ≤
      sobolevEnergy M u₀ + growthConstant nu * B^2 * t := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun tau hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have h := integrated_dissipation_of_rate_le
    (fun tau ↦ sobolevEnergy M (s.coefficients tau))
    (fun tau ↦ energyRate M (s.coefficients tau) (PancakeGalerkinKineticEnergy.velocityRHS M (s.coefficients tau) nu))
    (fun tau ↦ sobolevDissipation M (s.coefficients tau))
    (nu * (2 * Real.pi)^2) (growthConstant nu * B^2) t ht.1
    (fun tau hτ ↦ localSolution_sobolev_derivative s tau (hsub hτ))
    ((continuousOn_sobolevDissipation s).mono hsub) (fun tau hτ ↦ ?_)
  · simpa only [initial_sobolevEnergy s] using h
  · apply (absorbed_energyRate_le M (s.coefficients tau) nu hnu hk (s.transverse tau)).trans
    apply mul_le_mul_of_nonneg_left _ (growthConstant_nonneg nu hnu)
    have hn := energy_nonneg M (amplitude (s.coefficients tau))
    have hb := hB tau (hsub hτ)
    change 0 ≤ sobolevEnergy M (s.coefficients tau) at hn
    nlinarith

local notation "T3" => UnitAddTorus (Fin 3)

/-- The common constructed family has both a uniform pointwise
second-order bound and a uniform integrated viscous budget. -/
theorem exists_common_physical_solution_with_budget (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 6 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ k, modeDot k (torusFourierVelocity f k) = 0) :
    ∃ tau > (0 : ℝ), ∃ B ≥ (0 : ℝ), ∃ H ≥ (0 : ℝ), ∀ M : Finset Wavevector,
      (∀ k, -k ∈ M ↔ k ∈ M) → (∀ k ∈ M, frequencyVec k ≠ 0) →
      ∃ s : LocalVelocitySolution M nu (torusFourierVelocity f) tau,
        ∀ t ∈ Set.Icc (0 : ℝ) tau,
          sobolevEnergy M (s.coefficients t) ≤ B ∧
          nu * (2 * Real.pi)^2 *
            (∫ r in (0 : ℝ)..t, sobolevDissipation M (s.coefficients r)) ≤ H := by
  obtain ⟨tau, htau, B, hB, hs⟩ := exists_common_physical_solution nu hnu f hf hr hd
  let H := B + growthConstant nu * B^2 * tau
  have hC := growthConstant_nonneg nu hnu
  refine ⟨tau, htau, B, hB, H, by dsimp [H]; positivity, fun M hsym hk ↦ ?_⟩
  obtain ⟨s, hb⟩ := hs M hsym hk
  refine ⟨s, fun t ht ↦ ⟨hb t ht, ?_⟩⟩
  have hi := localSolution_integrated_sobolev s hnu hk B hb t ht
  have h0 := hb 0 ⟨le_rfl, htau.le⟩
  rw [initial_sobolevEnergy s] at h0
  have hn := energy_nonneg M (amplitude (s.coefficients t))
  change 0 ≤ sobolevEnergy M (s.coefficients t) at hn
  have hc := mul_le_mul_of_nonneg_left ht.2
    (mul_nonneg hC (sq_nonneg B))
  dsimp [H]
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevTimeBudget
