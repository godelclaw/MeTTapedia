import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalMaterialGradient

/-!
# The actual strain equation following fluid particles

The material gradient equation is symmetrized with its ordinary spatial
Laplacian. The signed strain-spin source and actual pressure Hessian survive.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalMaterialStrain

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeLocalMaterialGradient PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalGradientEquation PancakeMatrixDifferentialSymmetry PancakeSpatialGradientRegularity
open PancakeFilteredStrainDynamics PancakeLocalStrainEquation
open PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian

local notation "X3" => Fin 3 → ℝ

theorem strain_material {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ spatialStrain (spatialField s τ) (torusPoint (X τ)))
      (-(spatialStrain (spatialField s t) (torusPoint (X t)) *
            spatialStrain (spatialField s t) (torusPoint (X t)) +
          spatialSpin (spatialField s t) (torusPoint (X t)) *
            spatialSpin (spatialField s t) (torusPoint (X t))) -
        spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (X t)) +
        (nu : ℂ) • matrixLaplacian (spatialStrain (spatialField s t)) (torusPoint (X t))) t := by
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
  have hp : symmetrize (spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (X t))) =
      spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (X t)) := by
    change (1 / 2 : ℂ) • (_ + (spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (X t))).transpose) = _
    rw [spatialHessian_pressure_symmetric _ hm2]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have h := hasDerivAt_symmetrize _ _ t (velocityGradient_material s g hg hSum hu X hX t ht)
  simp only [Matrix.neg_mul, map_add, map_sub, map_neg, map_smul, symmetrize_square, hp,
    ← matrixLaplacian_symmetrize _ ha hda] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalMaterialStrain
