import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TopEigenvalueSmoothness
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialSpectralRelation

/-!
# Actual top-eigenvalue spatial derivatives and curvature

The derivatives are taken along coordinate shifts of finite filtered strain.
On the positive-top-gap branch, the spectral curvature is nonnegative. No
lower-gap assumption or eigenvector differentiation is used.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpatialTopEigenvalue

open scoped ContDiff RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakePhysicalLaplacian PancakePhysicalDiffusionLimit
open LocalSpatialSpectralRelation
open PancakeStrainSpectralFrame

local notation "T3" => UnitAddTorus (Fin 3)

def eigenvalueCurve (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) (h : ℝ) : ℝ :=
  topEigenvalue (strainCurve chi modes u j x h)

def eigenvalueFirst (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ := deriv (eigenvalueCurve chi modes u j x) 0

def eigenvalueSecond (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ := deriv (deriv (eigenvalueCurve chi modes u j x)) 0

def eigenvalueLaplacian (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ := ∑ j : Fin 3, eigenvalueSecond chi modes u j x

def curvature (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  let e := topVector (spatialStrain modes (filteredVelocity chi u) x)
  eigenvalueLaplacian chi modes u x - ⟪e, strainLaplacian modes (filteredVelocity chi u) x e⟫

theorem contDiffAt_eigenvalueCurve {n : ℕ∞ω} (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) (hn : n ≠ 0)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    ContDiffAt ℝ n (eigenvalueCurve chi modes u j x) 0 :=
  TopEigenvalueSmoothness.contDiffAt_topEigenvalue _ 0
    (contDiff_strainCurve chi modes u j x).contDiffAt hn (by simpa only [strainCurve_zero] using hg)

theorem rayleigh_strainSecond_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let e := topVector (spatialStrain modes (filteredVelocity chi u) x)
    ⟪e, strainSecond modes (filteredVelocity chi u) j x e⟫ ≤ eigenvalueSecond chi modes u j x := by
  have h := TopEigenvalueSmoothness.rayleigh_second_derivative_le (strainCurve chi modes u j x) 0
    (contDiff_strainCurve chi modes u j x).contDiffAt (by simpa only [strainCurve_zero] using hg)
    (topVector (strainCurve chi modes u j x 0)) (topVector_norm _)
    ((orderedEigenframe (strainCurve chi modes u j x 0).1 (strainCurve chi modes u j x 0).2).apply_eigenbasis 0)
  change ⟪topVector (spatialStrain modes (filteredVelocity chi u) x),
    strainSecond modes (filteredVelocity chi u) j x
      (topVector (spatialStrain modes (filteredVelocity chi u) x))⟫ ≤
    deriv (deriv (fun h ↦ topEigenvalue (strainCurve chi modes u j x h))) 0
  simpa only [strainCurve_zero, deriv_deriv_strainCurve] using h

theorem curvature_nonneg (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi u) x)) :
    0 ≤ curvature chi modes u x := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun j _ ↦ rayleigh_strainSecond_le chi modes u j x hg)
  apply sub_nonneg.mpr
  simpa only [strainLaplacian, sum_apply, inner_sum, eigenvalueLaplacian] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalSpatialTopEigenvalue
