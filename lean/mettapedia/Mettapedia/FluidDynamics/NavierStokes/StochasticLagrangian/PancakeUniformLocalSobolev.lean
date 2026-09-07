import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeQuadraticGrowthWindow

/-!
# Cutoff-independent local a priori control of the constructed evolution

Every existing local retained solution obeys the same second-order energy
bound until the explicit window closes. This is an a priori estimate;
extending each solution to the whole window is a separate continuation step.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeUniformLocalSobolev

open scoped BigOperators
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator
open PancakeLocalVelocityExistence PancakeSobolevWeights PancakeSobolevVelocityRate
open PancakeSobolevAbsorption PancakeQuadraticGrowthWindow PancakeCurlOutputTail

theorem initial_sobolevEnergy {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}
    (s : LocalVelocitySolution M nu u₀ T) :
    sobolevEnergy M (s.coefficients 0) = sobolevEnergy M u₀ := by
  rw [sobolevEnergy_eq, sobolevEnergy_eq]
  apply Finset.sum_congr rfl
  intro q hq
  rw [s.initial q hq]

theorem localSolution_sobolev_bound {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}
    (s : LocalVelocitySolution M nu u₀ T) (hnu : 0 < nu)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (B : ℝ) (hB : 0 ≤ B)
    (h0 : sobolevEnergy M u₀ ≤ B)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hw : t ≤ timeWindow (growthConstant nu) B) :
    sobolevEnergy M (s.coefficients t) ≤ 2 * (B+1) := by
  apply quadratic_growth_bound
    (fun tau ↦ sobolevEnergy M (s.coefficients tau))
    (fun tau ↦ energyRate M (s.coefficients tau) (PancakeGalerkinKineticEnergy.velocityRHS M
      (s.coefficients tau) nu)) (growthConstant nu) B T t
    (growthConstant_nonneg nu hnu) hB
  · exact fun tau _ ↦ energy_nonneg M (amplitude (s.coefficients tau))
  · exact localSolution_sobolev_derivative s
  · exact fun tau _ ↦ localSolution_sobolev_growth s hnu hk tau
  · rw [initial_sobolevEnergy s]
    exact h0
  · exact ht
  · exact hw

theorem sobolevEnergy_le_envelopeMass_sq (M : Finset Wavevector) (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ k, fourierMoment 2 u k ≤ g k) :
    sobolevEnergy M u ≤ (∑' k, g k)^2 := by
  have hG : 0 ≤ ∑' k, g k := tsum_nonneg hg
  have hpoint (k : Wavevector) : fourierMoment 2 u k ≤ ∑' j, g j :=
    (hu k).trans (hSum.le_tsum k (fun j _ ↦ hg j))
  change (∑ k ∈ M, (weight k * amplitude u k)^2) ≤ _
  have he (k : Wavevector) : weight k * amplitude u k = fourierMoment 2 u k := rfl
  simp_rw [he]
  calc
    _ ≤ ∑ k ∈ M, (∑' j, g j) * g k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [pow_two]
      exact mul_le_mul (hpoint k) (hu k) (fourierMoment_nonneg 2 u k) hG
    _ = (∑' j, g j) * ∑ k ∈ M, g k := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (hSum.sum_le_tsum M (fun k _ ↦ hg k)) hG

/-- One nonnegative summable initial Fourier envelope fixes the same
positive window and energy bound for every cutoff. The solution is bounded
on the intersection of that window with its already constructed lifespan. -/
theorem exists_uniform_initialEnvelope_window (nu : ℝ) (hnu : 0 < nu)
    (u₀ : FourierVelocity) (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) (hu : ∀ k, fourierMoment 2 u₀ k ≤ g k) :
    ∃ tau > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∀ (M : Finset Wavevector) (T : ℝ) (s : LocalVelocitySolution M nu u₀ T),
        (∀ k ∈ M, frequencyVec k ≠ 0) → ∀ t ∈ Set.Icc (0 : ℝ) T, t ≤ tau →
          sobolevEnergy M (s.coefficients t) ≤ B := by
  let B₀ := (∑' k, g k)^2
  refine ⟨timeWindow (growthConstant nu) B₀,
    timeWindow_pos _ _ (growthConstant_nonneg nu hnu) (sq_nonneg _),
    2 * (B₀+1), by positivity, ?_⟩
  intro M T s hk t ht hw
  exact localSolution_sobolev_bound s hnu hk B₀ (sq_nonneg _)
    (sobolevEnergy_le_envelopeMass_sq M u₀ g hg hSum hu) t ht hw

end Mettapedia.FluidDynamics.NavierStokes.PancakeUniformLocalSobolev
