import Mettapedia.Analysis.SecondDerivative
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalEnstrophyDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootWeightedIncrement

/-!
# The actual eighth-moment vorticity density

The fourth power of enstrophy density has an exact parabolic balance.
Both the full weighted gradient and the additional radial gradient are
retained. The stretching source is signed and no bound on it is asserted.
All expressions are polynomial in vorticity components, including at zero.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment

open scoped RealInnerProductSpace ContDiff
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeLocalInfiniteVelocity PancakeHaarTransportRate
open PancakeFourierTranslationCurve LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalAlignmentForcing LocalFrozenVorticity LocalJointDiffusionBudget
open GaussianRootWeightedIncrement (weightedPalinstrophyDensity)

local notation "T3" => UnitAddTorus (Fin 3)

def energy (u : FourierVelocity) (x : T3) : ℝ := (‖fullVorticity u x‖ ^ 2) ^ 4

theorem energy_eq_norm_pow (u : FourierVelocity) (x : T3) :
    energy u x = ‖fullVorticity u x‖ ^ 8 := by simp only [energy, ← pow_mul]

def frozenEnergy (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) (h : ℝ) : ℝ :=
  (‖frozenVorticity u t x h‖ ^ 2) ^ 4

def materialRate (u : FourierVelocity) (nu : ℝ) (x : T3) : ℝ :=
  8 * ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x,
    fullStrainOperator u x (fullVorticity u x) + nu • fullVorticityLaplacian u x⟫

/-- This equals `|omega|^6 |grad |omega||^2` away from zeros, without
requiring a direction field or a division by `|omega|` at zeros. -/
def radialGradientDensity (u : FourierVelocity) (x : T3) : ℝ :=
  ‖fullVorticity u x‖ ^ 4 * ∑ j : Fin 3, ⟪fullVorticity u x, fullCurlGradient u j x⟫ ^ 2

def stretchingDensity (u : FourierVelocity) (x : T3) : ℝ :=
  ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫

def energySecond (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  deriv (deriv (fun h : ℝ ↦ energy u (x + coordinateShift j h))) 0

def energyLaplacian (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, energySecond u j x

theorem energySecond_eq (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (j : Fin 3) (x : T3) :
    energySecond u j x =
      8 * ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x, fullCurlSecond u j x⟫ +
      8 * ‖fullVorticity u x‖ ^ 6 * ‖fullCurlGradient u j x‖ ^ 2 +
      48 * ‖fullVorticity u x‖ ^ 4 * ⟪fullVorticity u x, fullCurlGradient u j x⟫ ^ 2 := by
  have h := Mettapedia.Analysis.deriv_deriv_fun_pow_add_two
    ((LocalEnstrophyDiffusion.contDiff_energy_shift u hu j x).contDiffAt (x := 0)) 2
  have hd := (hasDerivAt_fullVorticity_shift u hu j x 0).norm_sq
  have hder : deriv (fun h : ℝ ↦ LocalEnstrophyDiffusion.energy u (x + coordinateShift j h)) 0 =
      2 * ⟪fullVorticity u x, fullCurlGradient u j x⟫ := by
    simpa only [LocalEnstrophyDiffusion.energy, coordinateShift_zero, add_zero] using hd.deriv
  have hsecond := LocalEnstrophyDiffusion.energySecond_eq u hu j x
  change deriv (deriv (fun h : ℝ ↦ LocalEnstrophyDiffusion.energy u (x + coordinateShift j h))) 0 = _ at hsecond
  rw [hder, hsecond] at h
  simp only [Nat.cast_ofNat, LocalEnstrophyDiffusion.energy, coordinateShift_zero, add_zero] at h
  change energySecond u j x = _ at h
  exact h.trans (by ring)

theorem energyLaplacian_eq (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (x : T3) :
    energyLaplacian u x =
      8 * ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x, fullVorticityLaplacian u x⟫ +
        8 * weightedPalinstrophyDensity u x + 48 * radialGradientDensity u x := by
  simp only [energyLaplacian, energySecond_eq u hu, weightedPalinstrophyDensity,
    radialGradientDensity, ← sum_fullCurlSecond u hu, inner_sum,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- Exact local balance for the full vorticity, not a frequency truncation. -/
theorem materialRate_sub_diffusion_add_dissipation_eq (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 3 u)) (x : T3) :
    materialRate u nu x / 8 - nu / 8 * energyLaplacian u x +
      nu * weightedPalinstrophyDensity u x + 6 * nu * radialGradientDensity u x =
        stretchingDensity u x := by
  rw [energyLaplacian_eq u hu x]
  simp only [materialRate, stretchingDensity, inner_add_right, real_inner_smul_right]
  ring

theorem radialGradientDensity_nonneg (u : FourierVelocity) (x : T3) :
    0 ≤ radialGradientDensity u x := by unfold radialGradientDensity; positivity

theorem hasDerivAt_frozenEnergy {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3) :
    HasDerivAt (fun h ↦ frozenEnergy s.coefficients t x h)
      (materialRate (s.coefficients t) nu x) 0 := by
  have h := ((hasDerivAt_frozenVorticity s g hg hSum hu a b hab hI t ht x).norm_sq).fun_pow 4
  apply h.congr_deriv
  simp only [materialRate, frozenVorticity_zero, Nat.cast_ofNat]
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment
