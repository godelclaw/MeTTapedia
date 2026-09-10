import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfinitePressureCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFilteredStrainDynamics

/-!
# Static filters of the actual infinite velocity equation

A bounded Fourier multiplier does not commute with convection. Its error is
the absolutely convergent, all-input fiber with weight
`chi q - chi k * chi (q - k)`. In particular, restricting the output does not
remove interactions between two unresolved inputs.

The evolution below is derived from `LocalInfiniteVelocitySolution.equation`.
It is not the closed Galerkin evolution of the filtered velocity. Both the
physical-pressure form and the Leray-projected subgrid force are recorded.
The multiplier is static; moving filters require an additional time term.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.InfiniteFilteredEquation

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeSobolevFiberEnvelope
open PancakeCoefficientLimitEquation PancakeInfinitePressureCoefficients
open PancakeFilteredStrainDynamics PancakePeriodicVorticityEquation
open PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity
open PancakeConvectionFiberIdentity PancakeFrequencyProjectorCommutator

/-- The unresolved convection includes every input frequency, not just the
frequencies retained by the multiplier. -/
def subgridConvection (chi : Wavevector → ℂ) (u : FourierVelocity)
    (q : Wavevector) : VelocityCoefficient :=
  fun i ↦ ∑' k, (chi q - chi k * chi (q-k)) * outputFiber q u k i

theorem outputFiber_filtered (chi : Wavevector → ℂ) (u : FourierVelocity)
    (q k : Wavevector) (i : Fin 3) :
    outputFiber q (filteredVelocity chi u) k i =
      (chi k * chi (q-k)) * outputFiber q u k i := by
  simp only [outputFiber, filteredVelocity, modeDot_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem summable_outputFiber_filtered (chi : Wavevector → ℂ) (u : FourierVelocity)
    (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C) (q : Wavevector) (i : Fin 3)
    (hu : Summable (fun k ↦ outputFiber q u k i)) :
    Summable (fun k ↦ outputFiber q (filteredVelocity chi u) k i) := by
  have hC : 0 ≤ C := (norm_nonneg (chi 0)).trans (hchi 0)
  apply (hu.norm.mul_left (C * C)).of_norm_bounded
  intro k
  rw [outputFiber_filtered, norm_mul, norm_mul]
  gcongr <;> exact hchi _

theorem summable_subgridConvection (chi : Wavevector → ℂ) (u : FourierVelocity)
    (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C) (q : Wavevector) (i : Fin 3)
    (hu : Summable (fun k ↦ outputFiber q u k i)) :
    Summable (fun k ↦ (chi q - chi k * chi (q-k)) * outputFiber q u k i) := by
  have hC : 0 ≤ C := (norm_nonneg (chi 0)).trans (hchi 0)
  apply (hu.norm.mul_left (C + C * C)).of_norm_bounded
  intro k
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  gcongr <;> exact hchi _

/-- Exact nonlinear filtering, with convergence proved before splitting the
infinite sum. No cancellation of unresolved inputs is assumed. -/
theorem filtered_infiniteConvection (chi : Wavevector → ℂ) (u : FourierVelocity)
    (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C) (q : Wavevector)
    (hu : ∀ i, Summable (fun k ↦ outputFiber q u k i)) :
    chi q • infiniteConvection u q =
      infiniteConvection (filteredVelocity chi u) q + subgridConvection chi u q := by
  ext i
  have hf := summable_outputFiber_filtered chi u C hchi q i (hu i)
  have hs := summable_subgridConvection chi u C hchi q i (hu i)
  simp only [infiniteConvection, subgridConvection, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [← tsum_mul_left, ← hf.tsum_add hs]
  apply tsum_congr
  intro k
  rw [outputFiber_filtered]
  ring

theorem viscousCoeff_filtered (chi : Wavevector → ℂ) (u : FourierVelocity)
    (nu : ℝ) (q : Wavevector) :
    chi q • unitTorusViscousVorticityCoeff nu u q =
      unitTorusViscousVorticityCoeff nu (filteredVelocity chi u) q := by
  ext i
  simp [unitTorusViscousVorticityCoeff, filteredVelocity]
  ring

/-- The pressure is the pressure of the full velocity, filtered only on its
output. Replacing it by the pressure of the resolved velocity loses a term. -/
theorem filtered_infiniteVelocityRHS_pressure
    (chi : Wavevector → ℂ) (u : FourierVelocity) (C : ℝ)
    (hchi : ∀ k, ‖chi k‖ ≤ C) (nu : ℝ) (q : Wavevector)
    (hu : ∀ i, Summable (fun k ↦ outputFiber q u k i)) :
    chi q • infiniteVelocityRHS nu u q =
      (-unitTorusDerivativePhase) • infiniteConvection (filteredVelocity chi u) q -
        chi q • infinitePressureGradientCoeff u q +
        unitTorusViscousVorticityCoeff nu (filteredVelocity chi u) q +
        (-unitTorusDerivativePhase) • subgridConvection chi u q := by
  rw [infiniteVelocityRHS_pressure_decomposition, smul_add, smul_sub,
    smul_comm (chi q), filtered_infiniteConvection chi u C hchi q hu, smul_add,
    viscousCoeff_filtered]
  abel

/-- The unresolved force includes its pressure correction through Leray
projection. This form compares with the nonlinear RHS of the resolved field. -/
def subgridForce (chi : Wavevector → ℂ) (u : FourierVelocity)
    (q : Wavevector) : VelocityCoefficient :=
  lerayMode q ((-unitTorusDerivativePhase) • subgridConvection chi u q)

theorem filtered_infiniteVelocityRHS
    (chi : Wavevector → ℂ) (u : FourierVelocity) (C : ℝ)
    (hchi : ∀ k, ‖chi k‖ ≤ C) (nu : ℝ) (q : Wavevector)
    (hu : ∀ i, Summable (fun k ↦ outputFiber q u k i)) :
    chi q • infiniteVelocityRHS nu u q =
      infiniteVelocityRHS nu (filteredVelocity chi u) q + subgridForce chi u q := by
  have hl (v w : VelocityCoefficient) : lerayMode q (v + w) =
      lerayMode q v + lerayMode q w := by
    ext i
    simp [lerayMode, modeDot, Finset.sum_add_distrib, mul_add, add_div]
    split_ifs
    · rfl
    · ring
  rw [infiniteVelocityRHS, smul_add, ← lerayMode_smul, smul_comm (chi q),
    filtered_infiniteConvection chi u C hchi q hu, smul_add, hl, viscousCoeff_filtered]
  change _ = (_ + _) + lerayMode q ((-unitTorusDerivativePhase) • subgridConvection chi u q)
  abel

/-- Finite support identifies the infinite convection with the existing
finite algebra, without asserting a closed finite-dimensional evolution. -/
theorem infiniteVelocityRHS_eq_finite (modes : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ k, k ∉ modes → u k = 0)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) (nu : ℝ) (q : Wavevector) :
    infiniteVelocityRHS nu u q = velocityRHS modes u nu q := by
  have hc : infiniteConvection u q = convectionConvolution modes u q := by
    ext i
    exact tsum_outputFiber_eq_convectionConvolution modes u hs hu q i
  rw [infiniteVelocityRHS, hc, velocityRHS, finiteTransport_fourierCurl_eq modes u hk hu q]

/-- A sharp low-frequency filter. The set may be any finite output set;
reality of the reconstructed field additionally requires symmetry. -/
def sharpFilter (modes : Finset Wavevector) (q : Wavevector) : ℂ :=
  if q ∈ modes then 1 else 0

theorem norm_sharpFilter_le_one (modes : Finset Wavevector) (q : Wavevector) :
    ‖sharpFilter modes q‖ ≤ 1 := by
  unfold sharpFilter
  split_ifs <;> simp

/-- At a retained output, the exact stress contains every pair with at
least one unresolved leg, including both-high pairs. -/
theorem subgridConvection_sharp_of_mem (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) (hq : q ∈ modes) :
    subgridConvection (sharpFilter modes) u q =
      fun i ↦ ∑' k, if k ∉ modes ∨ q-k ∉ modes then outputFiber q u k i else 0 := by
  ext i
  apply tsum_congr
  intro k
  by_cases hk : k ∈ modes <;> by_cases hl : q-k ∈ modes <;>
    simp [sharpFilter, hq, hk, hl]

/-- Even when the resolved velocity vanishes, unresolved interactions need
not vanish. The filtered full RHS is precisely the subgrid force. -/
theorem filtered_infiniteVelocityRHS_of_filtered_eq_zero
    (chi : Wavevector → ℂ) (u : FourierVelocity) (C : ℝ)
    (hchi : ∀ k, ‖chi k‖ ≤ C) (nu : ℝ) (q : Wavevector)
    (hu : ∀ i, Summable (fun k ↦ outputFiber q u k i))
    (hz : filteredVelocity chi u = 0) :
    chi q • infiniteVelocityRHS nu u q = subgridForce chi u q := by
  rw [filtered_infiniteVelocityRHS chi u C hchi nu q hu, hz]
  have hc : infiniteConvection 0 q = 0 := by
    ext i
    simp [infiniteConvection, outputFiber, modeDot]
  have hr : infiniteVelocityRHS nu 0 q = 0 := by
    ext i
    simp [infiniteVelocityRHS, hc, unitTorusViscousVorticityCoeff, lerayMode, modeDot]
    split_ifs <;> rfl
  rw [hr, zero_add]

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-- The filtered coefficient equation of the already constructed local
infinite solution, including the all-input nonlinear stress. -/
theorem hasDerivAt_filtered_coefficients (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (q : Wavevector) (i : Fin 3) :
    HasDerivAt (fun τ ↦ filteredVelocity chi (s.coefficients τ) q i)
      ((infiniteVelocityRHS nu (filteredVelocity chi (s.coefficients t)) q +
        subgridForce chi (s.coefficients t) q) i) t := by
  apply ((s.equation t ht q i).const_mul (chi q)).congr_deriv
  exact congrFun (filtered_infiniteVelocityRHS chi (s.coefficients t) C hchi nu q
    (s.summable_convection t ⟨ht.1.le, ht.2.le⟩ q)) i

/-- The finite algebra is reusable for a finitely filtered actual solution,
but its coefficient ODE has the explicit all-input forcing term. -/
theorem hasDerivAt_filtered_coefficients_finite
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (modes : Finset Wavevector) (hs : ∀ k, k ∉ modes → chi k = 0)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (q : Wavevector) (i : Fin 3) :
    HasDerivAt (fun τ ↦ filteredVelocity chi (s.coefficients τ) q i)
      ((velocityRHS modes (filteredVelocity chi (s.coefficients t)) nu q +
        subgridForce chi (s.coefficients t) q) i) t := by
  have h := hasDerivAt_filtered_coefficients s chi C hchi t ht q i
  rw [infiniteVelocityRHS_eq_finite modes _
    (fun k hkm ↦ by simp [filteredVelocity, hs k hkm]) hk
    (fun k _ ↦ filteredVelocity_transverse chi _ k (s.transverse t k))] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.InfiniteFilteredEquation
