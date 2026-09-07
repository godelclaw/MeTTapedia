import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherSobolevVelocityRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeQuadraticGrowthWindow

/-!
# Cutoff-independent local control at every fixed Sobolev order

Viscosity absorbs one derivative from convection. The resulting growth
constant depends on the fixed order, viscosity and the lattice mass only.
The explicit local time bound is applied to the actual coefficient ODE.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeHigherSobolevWindow

open scoped BigOperators
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy
open PancakeSignedTransportEnergy PancakeLocalVelocityExistence PancakeSobolevVelocityRate
open PancakeSobolevWeights PancakeHigherSobolevWeights PancakeHigherSobolevVelocityRate
open PancakeSobolevAbsorption PancakeQuadraticGrowthWindow

def orderGrowthConstant (m : ℕ) (nu : ℝ) : ℝ :=
  4 * ((2 : ℝ)^m)^2 * latticeMass / nu

theorem orderGrowthConstant_nonneg (m : ℕ) (nu : ℝ) (hnu : 0 < nu) :
    0 ≤ orderGrowthConstant m nu := by
  unfold orderGrowthConstant
  positivity [latticeMass_nonneg]

theorem absorbed_orderVelocityRate_le (m : ℕ) (hm : 2 ≤ m)
    (M : Finset Wavevector) (u : FourierVelocity) (nu : ℝ)
    (hnu : 0 < nu) (hk : ∀ k ∈ M, frequencyVec k ≠ 0)
    (hd : ∀ k ∈ M, modeDot k (u k) = 0) :
    orderVelocityRate m M u (velocityRHS M u nu) +
      nu * (2 * Real.pi)^2 * velocityDissipation m M u ≤
      orderGrowthConstant m nu * (velocityEnergy m M u)^2 := by
  have h := orderVelocityRate_le m hm M u nu hk hd
  have hy := quadratic_absorption (velocityEnergy m M u) (velocityDissipation m M u)
    (4 * (2 : ℝ)^m * (2 * Real.pi) * Real.sqrt latticeMass) (nu * (2 * Real.pi)^2)
    (orderDissipation_nonneg m M (amplitude u)) (by positivity)
  have hc : (4 * (2 : ℝ)^m * (2 * Real.pi) * Real.sqrt latticeMass)^2 /
      (4 * (nu * (2 * Real.pi)^2)) = orderGrowthConstant m nu := by
    simp only [mul_pow, Real.sq_sqrt latticeMass_nonneg]
    unfold orderGrowthConstant
    field_simp
  rw [hc] at hy
  linarith

theorem hasDerivAt_velocityEnergy (m : ℕ) (M : Finset Wavevector)
    (u : ℝ → FourierVelocity) (du : FourierVelocity) (t : ℝ)
    (hd : ∀ q ∈ M, ∀ i, HasDerivAt (fun tau ↦ u tau q i) (du q i) t) :
    HasDerivAt (fun tau ↦ velocityEnergy m M (u tau)) (orderVelocityRate m M (u t) du) t := by
  have h := hasDerivAt_weightedEnergy M (fun _ ↦ orderWeight m) (fun _ ↦ 0) u du t
    (fun q _ ↦ hasDerivAt_const t (orderWeight m q)) hd
  have he : (fun tau ↦ ∑ q ∈ M, orderWeight m q ^ 2 * coefficientEnergy (u tau q)) =
      fun tau ↦ velocityEnergy m M (u tau) := by
    funext tau
    exact (velocityEnergy_eq m M (u tau)).symm
  simpa only [he, orderVelocityRate, mul_zero, zero_mul, Finset.sum_const_zero, zero_add] using h

theorem localSolution_order_derivative (m : ℕ)
    {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}
    (s : LocalVelocitySolution M nu u₀ T) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivAt (fun tau ↦ velocityEnergy m M (s.coefficients tau))
      (orderVelocityRate m M (s.coefficients t) (velocityRHS M (s.coefficients t) nu)) t :=
  hasDerivAt_velocityEnergy m M s.coefficients _ t (s.equation t ht)

theorem localSolution_order_growth (m : ℕ) (hm : 2 ≤ m)
    {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}
    (s : LocalVelocitySolution M nu u₀ T) (hnu : 0 < nu)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (t : ℝ) :
    orderVelocityRate m M (s.coefficients t) (velocityRHS M (s.coefficients t) nu) ≤
      orderGrowthConstant m nu * (velocityEnergy m M (s.coefficients t))^2 := by
  have h := absorbed_orderVelocityRate_le m hm M (s.coefficients t) nu hnu hk (s.transverse t)
  have hn : 0 ≤ nu * (2 * Real.pi)^2 * velocityDissipation m M (s.coefficients t) :=
    mul_nonneg (by positivity) (orderDissipation_nonneg m M (amplitude (s.coefficients t)))
  linarith

theorem initial_velocityEnergy (m : ℕ)
    {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}
    (s : LocalVelocitySolution M nu u₀ T) :
    velocityEnergy m M (s.coefficients 0) = velocityEnergy m M u₀ := by
  rw [velocityEnergy_eq, velocityEnergy_eq]
  apply Finset.sum_congr rfl
  intro q hq
  rw [s.initial q hq]

theorem localSolution_order_bound (m : ℕ) (hm : 2 ≤ m)
    {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}
    (s : LocalVelocitySolution M nu u₀ T) (hnu : 0 < nu)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (B : ℝ) (hB : 0 ≤ B)
    (h0 : velocityEnergy m M u₀ ≤ B)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hw : t ≤ timeWindow (orderGrowthConstant m nu) B) :
    velocityEnergy m M (s.coefficients t) ≤ 2 * (B+1) := by
  apply quadratic_growth_bound
    (fun tau ↦ velocityEnergy m M (s.coefficients tau))
    (fun tau ↦ orderVelocityRate m M (s.coefficients tau) (velocityRHS M (s.coefficients tau) nu))
    (orderGrowthConstant m nu) B T t (orderGrowthConstant_nonneg m nu hnu) hB
  · exact fun tau _ ↦ orderEnergy_nonneg m M (amplitude (s.coefficients tau))
  · exact localSolution_order_derivative m s
  · exact fun tau _ ↦ localSolution_order_growth m hm s hnu hk tau
  · rw [initial_velocityEnergy m s]
    exact h0
  · exact ht
  · exact hw

end Mettapedia.FluidDynamics.NavierStokes.PancakeHigherSobolevWindow
