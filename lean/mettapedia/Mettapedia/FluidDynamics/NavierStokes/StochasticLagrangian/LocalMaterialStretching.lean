import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralDefectSources
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalGradientFlux

/-!
# Material evolution of the actual stretching vector

In `Dₜ(Sω)`, strain self-interaction cancels against the stretching of
vorticity, and the spin square annihilates the same vorticity. The
remaining terms are the actual pressure Hessian and the two viscous
product terms. This is a local identity, not a sign or size estimate for
pressure, and it is established before spatial gradient projection.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalMaterialStretching

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeLocalGradientEquation
open PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian
open LocalMaterialVorticity LocalMaterialStrain LocalSpectralDefectSources
open LocalLowDiffusionBudget LocalAlignmentForcing

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The strain-square terms cancel without any bound on the strain. -/
theorem stretchingRate_cancellation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S R : E →L[ℝ] E) (w f : E) :
    (-S * S + R) w + S (S w + f) = R w + S f := by
  simp only [add_apply, mul_apply_eq_comp, neg_apply, map_add]
  abel

variable {ν T B : ℝ} {u₀ : FourierVelocity}

def stretchingAlong (s : LocalInfiniteVelocitySolution ν u₀ T B) (X : ℝ → X3) (t : ℝ) : R3 :=
  strainAlong s X t (vorticityAlong s X t)

def pressureHessianAlong (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (X : ℝ → X3) (t : ℝ) : R3 →L[ℝ] R3 :=
  realMatrixOperator (spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (X t)))

def strainDiffusionAlong (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (X : ℝ → X3) (t : ℝ) : R3 →L[ℝ] R3 :=
  realMatrixOperator ((ν : ℂ) • matrixLaplacian
    (PancakeLocalStrainEquation.spatialStrain (spatialField s t)) (torusPoint (X t)))

def stretchingDiffusionAlong (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (X : ℝ → X3) (t : ℝ) : R3 :=
  strainDiffusionAlong s X t (vorticityAlong s X t) + strainAlong s X t (diffusionAlong s X t)

theorem pressureDiffusionAlong_eq (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (X : ℝ → X3) (t : ℝ) :
    pressureDiffusionAlong s X t = -pressureHessianAlong s X t + strainDiffusionAlong s X t := by
  simp only [pressureDiffusionAlong, pressureHessianAlong, strainDiffusionAlong,
    realMatrixOperator_add, realMatrixOperator_neg]

theorem strainRemainderAlong_apply_vorticity (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (X : ℝ → X3) (t : ℝ) (hm : Summable (fourierMoment 1 (s.coefficients t))) :
    strainRemainderAlong s X t (vorticityAlong s X t) =
      -(pressureHessianAlong s X t (vorticityAlong s X t)) +
        strainDiffusionAlong s X t (vorticityAlong s X t) := by
  rw [strainRemainderAlong_eq s X t hm, pressureDiffusionAlong_eq]
  simp only [add_apply, mul_apply_eq_comp, neg_apply, spinAlong_vorticityAlong s X t hm,
    map_zero, zero_add]

theorem stretchingAlong_eq (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (X : ℝ → X3) (t : ℝ) :
    stretchingAlong s X t = fullStrainOperator (s.coefficients t) (torusPoint (X t))
      (fullVorticity (s.coefficients t) (torusPoint (X t))) := rfl

variable (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (X : ℝ → X3)
  (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)

include hg hSum hu hX

theorem hasDerivAt_stretchingAlong (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (stretchingAlong s X)
      (-(pressureHessianAlong s X t (vorticityAlong s X t)) + stretchingDiffusionAlong s X t) t := by
  have h := (hasDerivAt_strainAlong s g hg hSum hu X hX t ht).clm_apply
    (hasDerivAt_vorticityAlong s g hg hSum hu X hX t ht)
  rw [stretchingRate_cancellation, strainRemainderAlong_apply_vorticity s X t
    (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)))] at h
  convert! h using 1
  simp only [stretchingDiffusionAlong, add_assoc]

/-- Pressure work keeps its sign; no Hessian norm or eigenvalue gap is introduced. -/
theorem hasDerivAt_stretching_norm_sq (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ ‖stretchingAlong s X τ‖ ^ 2)
      (-2 * ⟪stretchingAlong s X t, pressureHessianAlong s X t (vorticityAlong s X t)⟫ +
        2 * ⟪stretchingAlong s X t, stretchingDiffusionAlong s X t⟫) t := by
  have h := (hasDerivAt_stretchingAlong s g hg hSum hu X hX t ht).norm_sq
  convert h using 1
  simp only [inner_add_right, inner_neg_right]
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalMaterialStretching
