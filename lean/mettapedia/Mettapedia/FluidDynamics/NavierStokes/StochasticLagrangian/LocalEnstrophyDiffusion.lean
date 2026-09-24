import Mettapedia.Analysis.OperatorQuadraticForm
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialVorticityJets
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalFrozenVorticity

/-!
# Local enstrophy density and its actual parabolic balance

The material derivative follows the frozen instantaneous velocity and the
Laplacian is a sum of ordinary second coordinate derivatives. This local
identity supplies full-gradient dissipation; it does not bound stretching.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalEnstrophyDiffusion

open scoped ContDiff RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeLocalInfiniteVelocity PancakeHaarTransportRate
open PancakeFourierTranslationCurve
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalSpatialVorticityJets
open LocalAlignmentForcing LocalFrozenVorticity

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def energy (u : FourierVelocity) (x : T3) : ℝ := ‖fullVorticity u x‖ ^ 2

def frozenEnergy (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) (h : ℝ) : ℝ :=
  ‖frozenVorticity u t x h‖ ^ 2

def materialRate (u : FourierVelocity) (nu : ℝ) (x : T3) : ℝ :=
  2 * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x) +
    nu • fullVorticityLaplacian u x⟫

def gradientSquare (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2

def energySecond (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  deriv (deriv (fun h : ℝ ↦ energy u (x + coordinateShift j h))) 0

def energyLaplacian (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, energySecond u j x

theorem contDiff_energy_shift (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) : ContDiff ℝ 2 (fun h : ℝ ↦ energy u (x + coordinateShift j h)) :=
  (contDiff_fullVorticity_shift u hu j x).norm_sq ℝ

theorem energySecond_eq (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) :
    energySecond u j x = 2 * ⟪fullVorticity u x, fullCurlSecond u j x⟫ +
      2 * ‖fullCurlGradient u j x‖ ^ 2 := by
  have h := Mettapedia.Analysis.OperatorQuadraticForm.deriv_deriv_value
    (P := fun _ : ℝ ↦ (1 : R3 →L[ℝ] R3)) contDiffAt_const
    ((contDiff_fullVorticity_shift u hu j x).contDiffAt (x := 0))
    (Filter.Eventually.of_forall (fun _ _ _ ↦ rfl))
  rw [deriv_deriv_fullVorticity_shift u hu, deriv_fullVorticity_shift u hu] at h
  simpa only [Mettapedia.Analysis.OperatorQuadraticForm.value, one_apply_eq_self,
    real_inner_self_eq_norm_sq, deriv_const', deriv_const, zero_apply, inner_zero_right, mul_zero,
    add_zero, energySecond, energy, coordinateShift_zero] using h

theorem energyLaplacian_eq (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (x : T3) :
    energyLaplacian u x = 2 * ⟪fullVorticity u x, fullVorticityLaplacian u x⟫ +
      2 * gradientSquare u x := by
  simp only [energyLaplacian, energySecond_eq u hu, gradientSquare,
    ← sum_fullCurlSecond u hu, inner_sum, Finset.mul_sum, Finset.sum_add_distrib]

theorem materialRate_sub_diffusion_add_gradient_eq (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 3 u)) (x : T3) :
    materialRate u nu x - nu * energyLaplacian u x + 2 * nu * gradientSquare u x =
      2 * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫ := by
  rw [energyLaplacian_eq u hu x]
  simp only [materialRate, inner_add_right, real_inner_smul_right]
  ring

theorem hasDerivAt_frozenEnergy {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3) :
    HasDerivAt (fun h ↦ frozenEnergy s.coefficients t x h)
      (materialRate (s.coefficients t) nu x) 0 := by
  simpa only [frozenEnergy, materialRate, frozenVorticity_zero] using
    (hasDerivAt_frozenVorticity s g hg hSum hu a b hab hI t ht x).norm_sq

end Mettapedia.FluidDynamics.NavierStokes.LocalEnstrophyDiffusion
