import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSobolevVelocityRate

/-!
# Viscous absorption and the actual second-order energy derivative

The physical convection rate is absorbed with one half of the viscous
dissipation. The remaining scalar growth constant depends only on viscosity
and the fixed three-dimensional lattice sum.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevAbsorption

open scoped BigOperators
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy
open PancakeSignedTransportEnergy PancakeLocalVelocityExistence
open PancakeSobolevWeights PancakeSobolevVelocityRate

theorem quadratic_absorption (a d C mu : ℝ) (hd : 0 ≤ d) (hmu : 0 < mu) :
    C * a * Real.sqrt d ≤ mu * d + (C^2 / (4 * mu)) * a^2 := by
  have h := sq_nonneg (2 * mu * Real.sqrt d - C * a)
  simp only [sub_sq, mul_pow, Real.sq_sqrt hd] at h
  calc
    _ ≤ (4 * mu^2 * d + C^2 * a^2) / (4 * mu) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith)
    _ = _ := by field_simp

def growthConstant (nu : ℝ) : ℝ := 16 * latticeMass / nu

theorem growthConstant_nonneg (nu : ℝ) (hnu : 0 < nu) : 0 ≤ growthConstant nu :=
  div_nonneg (mul_nonneg (by norm_num) latticeMass_nonneg) hnu.le

theorem absorbed_energyRate_le (M : Finset Wavevector) (u : FourierVelocity) (nu : ℝ)
    (hnu : 0 < nu) (hk : ∀ k ∈ M, frequencyVec k ≠ 0)
    (hd : ∀ k ∈ M, modeDot k (u k) = 0) :
    energyRate M u (velocityRHS M u nu) +
      nu * (2 * Real.pi)^2 * sobolevDissipation M u ≤
      growthConstant nu * (sobolevEnergy M u)^2 := by
  have h := energyRate_le M u nu hk hd
  have hy := quadratic_absorption (sobolevEnergy M u) (sobolevDissipation M u)
    (8 * (2 * Real.pi) * Real.sqrt latticeMass) (nu * (2 * Real.pi)^2)
    (dissipation_nonneg M (amplitude u)) (by positivity)
  have hc : (8 * (2 * Real.pi) * Real.sqrt latticeMass)^2 /
      (4 * (nu * (2 * Real.pi)^2)) = growthConstant nu := by
    simp only [mul_pow, Real.sq_sqrt latticeMass_nonneg]
    unfold growthConstant
    field_simp
    ring
  rw [hc] at hy
  linarith

theorem hasDerivAt_sobolevEnergy (M : Finset Wavevector) (u : ℝ → FourierVelocity)
    (du : FourierVelocity) (t : ℝ)
    (hd : ∀ q ∈ M, ∀ i, HasDerivAt (fun tau ↦ u tau q i) (du q i) t) :
    HasDerivAt (fun tau ↦ sobolevEnergy M (u tau)) (energyRate M (u t) du) t := by
  have h := hasDerivAt_weightedEnergy M (fun _ ↦ weight) (fun _ ↦ 0) u du t
    (fun q _ ↦ hasDerivAt_const t (weight q)) hd
  have he : (fun tau ↦ ∑ q ∈ M, weight q ^ 2 * coefficientEnergy (u tau q)) =
      fun tau ↦ sobolevEnergy M (u tau) := by
    funext tau
    exact (sobolevEnergy_eq M (u tau)).symm
  simpa only [he, energyRate, mul_zero, zero_mul, Finset.sum_const_zero, zero_add] using h

theorem localSolution_sobolev_derivative {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}
    (s : LocalVelocitySolution M nu u₀ T) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivAt (fun tau ↦ sobolevEnergy M (s.coefficients tau))
      (energyRate M (s.coefficients t) (velocityRHS M (s.coefficients t) nu)) t :=
  hasDerivAt_sobolevEnergy M s.coefficients _ t (s.equation t ht)

theorem localSolution_sobolev_growth {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}
    (s : LocalVelocitySolution M nu u₀ T) (hnu : 0 < nu)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (t : ℝ) :
    energyRate M (s.coefficients t) (velocityRHS M (s.coefficients t) nu) ≤
      growthConstant nu * (sobolevEnergy M (s.coefficients t))^2 := by
  have h := absorbed_energyRate_le M (s.coefficients t) nu hnu hk (s.transverse t)
  have hn : 0 ≤ nu * (2 * Real.pi)^2 * sobolevDissipation M (s.coefficients t) :=
    mul_nonneg (by positivity) (dissipation_nonneg M (amplitude (s.coefficients t)))
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevAbsorption
