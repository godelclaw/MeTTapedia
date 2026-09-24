import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.BottomProjectorSmoothness
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpacetimeSpectralDifferentiability

/-!
# Actual spatial derivatives of the bottom strain projector

Finite filtered strain is spatially smooth. On the positive-bottom-gap
region its bottom projector, coordinate derivatives, and Laplacian are
smooth even when the top two eigenvalues coincide. No derivative or
integrability bound uniform in the gap or filter scale is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpatialBottomProjector

open scoped ContDiff Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFourierMaterialPaths
open PancakeFilteredStrainDynamics PancakeFourierPressureStrain PancakeSpatialStrainEvolution
open PancakeSpectralProjectorRegularity PancakeSpectralClusterDichotomy.SymmetricStrain
open PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpacetimeSpectralDifferentiability
open PancakeMeasurableMaterialRate

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "Op" => R3 →L[ℝ] R3
local notation "T3" => UnitAddTorus (Fin 3)

theorem torusPoint_add_single (r : X3) (j : Fin 3) (h : ℝ) :
    torusPoint (r + h • Pi.single j 1) =
      torusPoint r + PancakeFourierTranslationCurve.coordinateShift j h := by
  ext i
  simp [torusPoint, PancakeFourierTranslationCurve.coordinateShift,
    PancakeFourierStrainGradient.coordinateLine, Pi.single_apply, eq_comm]

theorem contDiff_spatialStrain {n : ℕ∞ω} (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) :
    ContDiff ℝ n (fun r : X3 ↦ (spatialStrain modes (filteredVelocity chi u) (torusPoint r)).1) := by
  apply realMatrixOperatorCLM.contDiff.comp
  refine contDiff_pi.mpr (fun a ↦ contDiff_pi.mpr (fun b ↦ ?_))
  simp only [matrixReconstruction_apply]
  apply ContDiff.sum
  intro q _
  have hphase : ContDiff ℝ n (fun r : X3 ↦ UnitAddTorus.mFourier q (torusPoint r)) := by
    simp only [mFourier_torusPoint, realModeDot]
    have hr : ContDiff ℝ n (fun r : X3 ↦ ∑ i, (q i : ℝ) * r i) := by fun_prop
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hr)).cexp
  simp only [strainCoeff, gradientCoeff, filteredVelocity,
    Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

def projector (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (r : X3) : Op :=
  bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi u) (torusPoint r))

def coordinateDerivative (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (r : X3) : Op :=
  fderiv ℝ (projector chi modes u) r (Pi.single j 1)

def laplacian (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (r : X3) : Op :=
  ∑ j : Fin 3, fderiv ℝ (coordinateDerivative chi modes u j) r (Pi.single j 1)

theorem contDiffAt_projector (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (r : X3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) (torusPoint r))) :
    ContDiffAt ℝ ∞ (projector chi modes u) r :=
  BottomProjectorSmoothness.contDiffAt_bottomEigenlineProjector _ r
    (contDiff_spatialStrain chi modes u).contDiffAt (by simp) hg

theorem contDiffAt_coordinateDerivative (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (r : X3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) (torusPoint r))) (j : Fin 3) :
    ContDiffAt ℝ ∞ (coordinateDerivative chi modes u j) r :=
  ((contDiffAt_projector chi modes u r hg).fderiv_right (by simp)).clm_apply contDiffAt_const

theorem contDiffAt_laplacian (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (r : X3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) (torusPoint r))) :
    ContDiffAt ℝ ∞ (laplacian chi modes u) r := by
  apply ContDiffAt.sum
  intro j _
  exact ((contDiffAt_coordinateDerivative chi modes u r hg j).fderiv_right (by simp)).clm_apply
    contDiffAt_const

theorem hasDerivAt_projector_line (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (r : X3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) (torusPoint r))) (j : Fin 3) :
    HasDerivAt (fun h : ℝ ↦ projector chi modes u (r + h • Pi.single j 1))
      (coordinateDerivative chi modes u j r) 0 := by
  have hP := ((contDiffAt_projector chi modes u r hg).differentiableAt (by simp)).hasFDerivAt
  have hline := ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j (1 : ℝ))).const_add r
  have hP' : HasFDerivAt (projector chi modes u) (fderiv ℝ (projector chi modes u) r)
      (r + (0 : ℝ) • Pi.single j 1) := by simpa only [zero_smul, add_zero] using hP
  convert! hP'.comp_hasDerivAt 0 hline using 1
  simp only [coordinateDerivative, one_smul]

theorem contDiffAt_projector_shift (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) (j : Fin 3) :
    ContDiffAt ℝ ∞ (fun h : ℝ ↦ bottomEigenlineProjector
      (spatialStrain modes (filteredVelocity chi u)
        (x + PancakeFourierTranslationCurve.coordinateShift j h))) 0 := by
  obtain ⟨r, rfl⟩ := torusPoint_surjective x
  have hP : ContDiffAt ℝ ∞ (projector chi modes u) (r + (0 : ℝ) • Pi.single j 1) := by
    simpa only [zero_smul, add_zero] using contDiffAt_projector chi modes u r hg
  have hline : ContDiffAt ℝ ∞ (fun h : ℝ ↦ r + h • Pi.single j 1) 0 := by fun_prop
  simpa only [Function.comp_def, projector, torusPoint_add_single] using hP.comp 0 hline

end Mettapedia.FluidDynamics.NavierStokes.LocalSpatialBottomProjector
