import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialTopEigenvalue
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialVorticityJets
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRegularizedMaterialRate

/-!
# Actual spatial diffusion of the spectral defect

On the simple-top branch, the Laplacian of the regularized defect has an
exact product rule. Its spectral-curvature term is nonnegative. The mixed
gradient term remains explicit; positive constant regularization pays it
with a strain-gradient cost. No uniform bound on that cost is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDefectDiffusion

open scoped ContDiff RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open PancakeFourierStrainGradient
open PancakeHaarTransportRate PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakePhysicalLaplacian
open PancakePhysicalDiffusionLimit PancakeRegularizedDiffusion PancakeRegularizedMaterialRate
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution
open LocalSpatialSpectralRelation LocalSpatialTopEigenvalue LocalSpatialVorticityJets
open LocalLowDiffusionBudget LocalJointDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The same field energy used by the collision-safe weak alignment budget. -/
abbrev energy := LocalAlignmentTransport.alignmentEnergy

def gapFirst (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) : R3 →L[ℝ] R3 :=
  gapDerivative (spatialStrain modes (filteredVelocity chi u) x)
    (strainGradient modes (filteredVelocity chi u) x j)

def gradientSquare (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  ∑ j : Fin 3, ⟪fullCurlGradient u j x,
    regularizedGap (spatialStrain modes (filteredVelocity chi u) x) delta (fullCurlGradient u j x)⟫

def gradientCross (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  ∑ j : Fin 3, ⟪fullCurlGradient u j x, gapFirst chi modes u j x (fullVorticity u x)⟫

def energySecond (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (j : Fin 3) (x : T3) : ℝ :=
  deriv (deriv (fun h : ℝ ↦ energy chi modes u delta (x + coordinateShift j h))) 0

def energyLaplacian (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  ∑ j : Fin 3, energySecond chi modes u delta j x

theorem energy_zero (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    energy chi modes u 0 x =
      topSpectralDefect (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x) := by
  simp only [energy, LocalAlignmentTransport.alignmentEnergy, regularizedEnergy_eq, zero_mul, add_zero]

theorem gradientSquare_coercive (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) :
    delta * ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2 ≤ gradientSquare chi modes u delta x := by
  simpa only [gradientSquare, Finset.mul_sum] using
    Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _ ↦ regularizedGap_coercive (spatialStrain modes (filteredVelocity chi u) x)
        delta (fullCurlGradient u j x))

theorem contDiffAt_gapCurve (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (j : Fin 3) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    ContDiffAt ℝ 2 (fun h ↦ regularizedGap (strainCurve chi modes u j x h) delta) 0 :=
  (((contDiffAt_eigenvalueCurve chi modes u j x (by norm_num) hg).add contDiffAt_const).smul
    contDiffAt_const).sub (contDiff_strainCurve chi modes u j x).contDiffAt

theorem deriv_gapCurve (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (j : Fin 3) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    deriv (fun h ↦ regularizedGap (strainCurve chi modes u j x h) delta) 0 =
      gapFirst chi modes u j x := by
  have h := hasDerivAt_regularizedGap (strainCurve chi modes u j x) _ delta 0
    (hasDerivAt_strainCurve chi modes u j x 0)
    ((contDiffAt_eigenvalueCurve (n := 2) chi modes u j x (by norm_num) hg).differentiableAt (by norm_num))
  simpa only [strainCurve_zero, coordinateShift_zero, add_zero, gapFirst] using h.deriv

theorem deriv_deriv_gapCurve (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (j : Fin 3) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    deriv (deriv (fun h ↦ regularizedGap (strainCurve chi modes u j x h) delta)) 0 =
      eigenvalueSecond chi modes u j x • (1 : R3 →L[ℝ] R3) -
        strainSecond modes (filteredVelocity chi u) j x := by
  have h := Mettapedia.Analysis.deriv_deriv_smul_const_sub
    ((contDiffAt_eigenvalueCurve chi modes u j x (by norm_num) hg).add (contDiffAt_const (c := delta)))
    (contDiff_strainCurve chi modes u j x).contDiffAt (1 : R3 →L[ℝ] R3)
  change _ = deriv (deriv (fun h ↦ topEigenvalue (strainCurve chi modes u j x h))) 0 •
    (1 : R3 →L[ℝ] R3) - strainSecond modes (filteredVelocity chi u) j x
  simpa only [regularizedGap, eigenvalueCurve, deriv_add_const',
    deriv_deriv_strainCurve] using h

theorem energySecond_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (hu : Summable (fourierMoment 3 u)) (j : Fin 3) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let A := regularizedGap (spatialStrain modes (filteredVelocity chi u) x) delta
    energySecond chi modes u delta j x =
      2 * ⟪A (fullVorticity u x), fullCurlSecond u j x⟫ +
        2 * ⟪fullCurlGradient u j x, A (fullCurlGradient u j x)⟫ +
        4 * ⟪fullCurlGradient u j x, gapFirst chi modes u j x (fullVorticity u x)⟫ +
        eigenvalueSecond chi modes u j x * ‖fullVorticity u x‖ ^ 2 -
        ⟪fullVorticity u x, strainSecond modes (filteredVelocity chi u) j x (fullVorticity u x)⟫ := by
  have h := Mettapedia.Analysis.OperatorQuadraticForm.deriv_deriv_value
    (contDiffAt_gapCurve chi modes u delta j x hg)
    ((contDiff_fullVorticity_shift u hu j x).contDiffAt (x := 0))
    (Filter.Eventually.of_forall (fun h a b ↦ (regularizedGap_symmetric
      (strainCurve chi modes u j x h) delta a b).symm))
  rw [deriv_deriv_gapCurve chi modes u delta j x hg, deriv_deriv_fullVorticity_shift u hu,
    deriv_gapCurve chi modes u delta j x hg, deriv_fullVorticity_shift u hu] at h
  simp only [Mettapedia.Analysis.OperatorQuadraticForm.value, strainCurve_zero,
    coordinateShift_zero, add_zero, sub_apply, smul_apply, one_apply_eq_self, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  change energySecond chi modes u delta j x = _ at h
  dsimp only
  linarith only [h]

theorem energyLaplacian_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (hu : Summable (fourierMoment 3 u)) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    energyLaplacian chi modes u delta x =
      linearRate S delta (fullVorticity u x) (strainLaplacian modes (filteredVelocity chi u) x)
        (fullVorticityLaplacian u x) + curvature chi modes u x * ‖fullVorticity u x‖ ^ 2 +
        2 * gradientSquare chi modes u delta x + 4 * gradientCross chi modes u x := by
  simp only [energyLaplacian, energySecond_eq chi modes u delta hu _ x hg,
    linearRate, remainderAnisotropy, curvature, eigenvalueLaplacian, gradientSquare,
    gradientCross, strainLaplacian, ← sum_fullCurlSecond u hu, sum_apply, inner_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDefectDiffusion
