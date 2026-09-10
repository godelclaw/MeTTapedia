import Mettapedia.Analysis.SpectralRelationDerivatives
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalBottomEnergyDiffusion

/-!
# Spatial derivatives of the actual bottom spectral relation

All derivatives are taken along coordinate shifts of the reconstructed
filtered strain. The bottom gap suffices: top-eigenvalue collisions do
not enter. The mixed term in the twice differentiated equation is kept
with its sign for the material-minus-diffusion cancellation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpatialSpectralRelation

open scoped Topology ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFourierTranslationCurve
open PancakeHaarTransportRate PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy.SymmetricStrain
open PancakeFourierStrainGradient PancakeMappedFourierDiffusion PancakePhysicalDiffusionLimit
open PancakePhysicalLaplacian LocalBottomEnergyDiffusion BottomProjectorMotion
open LocalSpatialBottomProjector PancakeMeasurableMaterialRate

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def strainCurve (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) (h : ℝ) : SymmetricStrain :=
  spatialStrain modes (filteredVelocity chi u) (x + coordinateShift j h)

theorem strainCurve_zero (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) :
    strainCurve chi modes u j x 0 = spatialStrain modes (filteredVelocity chi u) x := by
  simp only [strainCurve, coordinateShift_zero, add_zero]

theorem contDiff_strainCurve {n : ℕ∞ω} (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) :
    ContDiff ℝ n (fun h ↦ (strainCurve chi modes u j x h).1) := by
  obtain ⟨r, rfl⟩ := torusPoint_surjective x
  have hline : ContDiff ℝ n (fun h : ℝ ↦ r + h • Pi.single j 1) := by fun_prop
  simpa only [Function.comp_def, torusPoint_add_single, strainCurve] using
    (contDiff_spatialStrain (n := n) chi modes u).comp hline

theorem hasDerivAt_strainCurve (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun τ ↦ (strainCurve chi modes u j x τ).1)
      (strainGradient modes (filteredVelocity chi u) (x + coordinateShift j h) j) h := by
  have hd := hasDerivAt_mappedField_shift realMatrixOperatorCLM modes
    (PancakeFourierPressureStrain.strainCoeff (filteredVelocity chi u)) j h x
  simpa only [mappedField_strain, mappedField_strainGradient, strainCurve] using hd

theorem deriv_strainCurve (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) :
    deriv (fun h ↦ (strainCurve chi modes u j x h).1) =
      fun h ↦ strainGradient modes (filteredVelocity chi u) (x + coordinateShift j h) j := by
  funext h
  exact (hasDerivAt_strainCurve chi modes u j x h).deriv

theorem deriv_deriv_strainCurve (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) :
    deriv (deriv (fun h ↦ (strainCurve chi modes u j x h).1)) 0 =
      strainSecond modes (filteredVelocity chi u) j x := by
  rw [deriv_strainCurve]
  simpa only [coordinateShift_zero, add_zero] using
    (hasDerivAt_strainGradient_shift modes (filteredVelocity chi u) j 0 x).deriv

def bottomEigenvalueCurve (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) (h : ℝ) : ℝ :=
  thirdEigenvalue (strainCurve chi modes u j x h)

def bottomEigenvalueFirst (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  deriv (bottomEigenvalueCurve chi modes u j x) 0

def bottomEigenvalueSecond (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) : ℝ :=
  deriv (deriv (bottomEigenvalueCurve chi modes u j x)) 0

def bottomEigenvalueLaplacian (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ := ∑ j : Fin 3, bottomEigenvalueSecond chi modes u j x

def mixedGradient (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : Op :=
  ∑ j : Fin 3, (strainGradient modes (filteredVelocity chi u) x j * projectorFirst chi modes u j x -
    bottomEigenvalueFirst chi modes u j x • projectorFirst chi modes u j x)

theorem contDiffAt_bottomEigenvalueCurve {n : ℕ∞ω} (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hn : n ≠ 0) (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    ContDiffAt ℝ n (bottomEigenvalueCurve chi modes u j x) 0 :=
  BottomProjectorSmoothness.contDiffAt_thirdEigenvalue _ 0
    (contDiff_strainCurve chi modes u j x).contDiffAt hn (by simpa only [strainCurve_zero] using hg)

theorem second_spectral_relation (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    let P := bottomEigenlineProjector S
    strainSecond modes (filteredVelocity chi u) j x * P + S.1 * projectorSecond chi modes u j x +
        (2 : ℝ) • (strainGradient modes (filteredVelocity chi u) x j * projectorFirst chi modes u j x) =
      bottomEigenvalueSecond chi modes u j x • P + thirdEigenvalue S • projectorSecond chi modes u j x +
        (2 * bottomEigenvalueFirst chi modes u j x) • projectorFirst chi modes u j x := by
  have hP : ContDiffAt ℝ 2 (projectorCurve chi modes u j x) 0 :=
    (contDiffAt_projector_shift chi modes u x hg j).of_le (by decide)
  have h := Mettapedia.Analysis.SpectralRelationDerivatives.second_derivative_relation
    (contDiff_strainCurve (n := 2) chi modes u j x).contDiffAt hP
    (contDiffAt_bottomEigenvalueCurve chi modes u j x (by norm_num) hg)
    (fun h ↦ strain_mul_bottomProjector (strainCurve chi modes u j x h))
  rw [deriv_deriv_strainCurve, deriv_strainCurve] at h
  simpa only [strainCurve_zero, projectorCurve, bottomEigenvalueCurve, strainCurve,
    coordinateShift_zero, add_zero, projectorFirst, projectorSecond,
    bottomEigenvalueFirst, bottomEigenvalueSecond] using h

theorem laplacian_spectral_relation (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi u) x)) :
    let S := spatialStrain modes (filteredVelocity chi u) x
    let P := bottomEigenlineProjector S
    strainLaplacian modes (filteredVelocity chi u) x * P + S.1 * projectorLaplacian chi modes u x +
        (2 : ℝ) • (∑ j : Fin 3, strainGradient modes (filteredVelocity chi u) x j * projectorFirst chi modes u j x) =
      bottomEigenvalueLaplacian chi modes u x • P + thirdEigenvalue S • projectorLaplacian chi modes u x +
        (2 : ℝ) • (∑ j : Fin 3, bottomEigenvalueFirst chi modes u j x • projectorFirst chi modes u j x) := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl
    (fun j _ ↦ second_spectral_relation chi modes u j x hg)
  dsimp only at h ⊢
  simp only [strainLaplacian, projectorLaplacian, bottomEigenvalueLaplacian,
    Fin.sum_univ_three] at h ⊢
  convert! h using 1 <;>
    simp only [add_mul, mul_add, smul_add, mul_smul] <;> module

end Mettapedia.FluidDynamics.NavierStokes.LocalSpatialSpectralRelation
