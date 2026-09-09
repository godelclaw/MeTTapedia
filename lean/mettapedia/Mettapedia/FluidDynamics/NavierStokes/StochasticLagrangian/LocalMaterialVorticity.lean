import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMatrixCurlAlgebra
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalMaterialGradient
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalStrainReality
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalNonlinearReconstruction

/-!
# Vorticity evolution along the actual local material flow

The curl of the constructed infinite Fourier velocity obeys
`Dₜ ω = S ω + ν Δω`. The pressure Hessian cancels by symmetry; the spin
annihilates its own axial vector. Diffusion is retained as the ordinary
spatial Laplacian of vorticity.

These are local identities for the unforced equation. They do not give
a global bound for the diffusion term or a misalignment budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalMaterialVorticity

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeLocalMaterialGradient PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalGradientEquation PancakeMatrixDifferentialSymmetry PancakeSpatialGradientRegularity
open PancakeLocalStrainEquation PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian
open PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian PancakeMatrixCurlAlgebra
open PancakeLocalProjectedEquation
open PancakeDyadicDirectionEvolution PancakeInfiniteRealCurl PancakeLocalStrainReality
open PancakePhysicalNonlinearReconstruction PancakeTransverseEnergyFreezing

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The actual curl of the local solution satisfies the strain-diffusion
equation along each material trajectory. -/
theorem hasDerivAt_spatialCurl_material {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ spatialCurl (spatialField s τ) (torusPoint (X τ)))
      ((spatialStrain (spatialField s t) (torusPoint (X t))).mulVec
          (spatialCurl (spatialField s t) (torusPoint (X t))) +
        (nu : ℂ) • spatialLaplacian (spatialCurl (spatialField s t)) (torusPoint (X t))) t := by
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  have hm2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hm
  have ha (y : UnitAddTorus (Fin 3)) (m : Fin 3) : DifferentiableAt ℝ
      (fun h ↦ spatialVelocityGradient (spatialField s t)
        (y + PancakeFourierTranslationCurve.coordinateShift m h)) 0 :=
    HasDerivAt.differentiableAt (F := Fin 3 → Fin 3 → ℂ)
      (hasDerivAt_velocityGradient_shift _ hm2 m y)
  have hda (y : UnitAddTorus (Fin 3)) (m n : Fin 3) : DifferentiableAt ℝ
      (fun h ↦ matrixCoordinateDerivative (spatialVelocityGradient (spatialField s t)) m
        (y + PancakeFourierTranslationCurve.coordinateShift n h)) 0 :=
    HasDerivAt.differentiableAt (F := Fin 3 → Fin 3 → ℂ)
      (hasDerivAt_matrixDerivative_gradient_shift _ hm m n y)
  have htrace : (spatialVelocityGradient (spatialField s t) (torusPoint (X t))).trace = 0 :=
    spatialDivergence_fullFourierField _ hm2 (s.transverse t) _
  have hp := matrixCurl_symmetric _ (spatialHessian_pressure_symmetric _ hm2 (torusPoint (X t)))
  have h := hasDerivAt_matrixCurl _ _ t (velocityGradient_material s g hg hSum hu X hX t ht)
  simpa only [map_add, map_sub, map_smul, matrixCurl_neg_square_trace_zero _ htrace,
    hp, sub_zero, ← spatialLaplacian_matrixCurl _ ha hda, matrixCurl_velocityGradient,
    PancakeLocalStrainEquation.spatialStrain] using h

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-- Real Euclidean vorticity evaluated on a lifted material path. -/
def vorticityAlong (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3) (t : ℝ) : R3 :=
  complexRealPartEuclideanCLM (spatialCurl (spatialField s t) (torusPoint (X t)))

/-- The viscous term on the same path. It is present even in the absence of
an external body force. -/
def diffusionAlong (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3) (t : ℝ) : R3 :=
  nu • complexRealPartEuclideanCLM
    (spatialLaplacian (spatialCurl (spatialField s t)) (torusPoint (X t)))

/-- The strain as an operator on real Euclidean space, on the same path. -/
def strainAlong (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3) (t : ℝ) :
    R3 →L[ℝ] R3 :=
  realMatrixOperator (PancakeLocalStrainEquation.spatialStrain (spatialField s t) (torusPoint (X t)))

/-- The real-valued path definition agrees with the ordinary real curl. -/
theorem vorticityAlong_eq_realSpatialCurl (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) (hm : Summable (fourierMoment 1 (s.coefficients t))) :
    vorticityAlong s X t = realSpatialCurl (realFullField (s.coefficients t)) (torusPoint (X t)) := by
  rw [realSpatialCurl_realFullField _ hm]
  simp only [vorticityAlong, spatialField, spatialCurl_velocity _ hm, realFullField]

/-- The real Hilbert-space equation needed for norm and spectral-defect
estimates is derived from the actual PDE solution. -/
theorem hasDerivAt_vorticityAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (F := R3) (vorticityAlong s X)
      (strainAlong s X t (vorticityAlong s X t) + diffusionAlong s X t) t := by
  have hm := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩))
  have hreal (i j : Fin 3) :
      (PancakeLocalStrainEquation.spatialStrain (spatialField s t) (torusPoint (X t)) i j).im = 0 := by
    have h := congrArg Complex.im (spatialStrain_reality _ hm (s.reality t) (torusPoint (X t)) i j)
    simp only [Complex.conj_im] at h
    dsimp [spatialField]
    linarith
  have h := complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_spatialCurl_material s g hg hSum hu X hX t ht)
  have hscalar (v : VelocityCoefficient) :
      complexRealPartEuclideanCLM ((nu : ℂ) • v) = nu • complexRealPartEuclideanCLM v := by
    ext i
    simp [complexRealPartEuclideanCLM_apply, complexRealPartEuclidean]
  simp only [Function.comp_def, map_add, complexRealPart_mulVec _ _ hreal, hscalar,
    complexRealPartEuclideanCLM_apply] at h
  convert! h using 1

end Mettapedia.FluidDynamics.NavierStokes.LocalMaterialVorticity
