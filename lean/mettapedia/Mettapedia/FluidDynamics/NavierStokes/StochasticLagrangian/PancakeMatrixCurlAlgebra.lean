import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalStrainEquation

/-!
# The axial contraction of the actual velocity gradient

The contraction is the ordinary curl. Finite matrix algebra exposes the
pressure cancellation and the strain action on its own axial vector.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeMatrixCurlAlgebra

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalGradientEquation
open PancakeLocalStrainEquation PancakeFilteredStrainDynamics PancakeInfiniteSpatialCurl
open PancakeMatrixDifferentialSymmetry PancakeInfiniteSpatialLaplacian
open PancakeFourierTranslationCurve

local notation "T3" => UnitAddTorus (Fin 3)
local notation "M3" => Matrix (Fin 3) (Fin 3) ℂ

def matrixCurl : M3 →ₗ[ℂ] VelocityCoefficient where
  toFun a := ![a 2 1 - a 1 2, a 0 2 - a 2 0, a 1 0 - a 0 1]
  map_add' a b := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by ext i; fin_cases i <;> simp <;> ring

theorem matrixCurl_velocityGradient (u : T3 → VelocityCoefficient) (x : T3) :
    matrixCurl (spatialVelocityGradient u x) = spatialCurl u x := rfl

theorem matrixCurl_symmetric (a : M3) (ha : a.transpose = a) : matrixCurl a = 0 := by
  have h (i j : Fin 3) : a j i = a i j := congrFun (congrFun ha i) j
  ext i
  fin_cases i <;> simp [matrixCurl, h]

theorem matrixCurl_neg_square (a : M3) :
    matrixCurl (-a * a) = a.mulVec (matrixCurl a) - a.trace • matrixCurl a := by
  ext i
  fin_cases i <;>
    simp [matrixCurl, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.trace,
      Fin.sum_univ_three] <;> ring

theorem spin_mulVec_matrixCurl (a : M3) :
    (skewSymmetrize a).mulVec (matrixCurl a) = 0 := by
  ext i
  fin_cases i <;>
    simp [matrixCurl, skewSymmetrize, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem strain_mulVec_matrixCurl (a : M3) :
    (symmetrize a).mulVec (matrixCurl a) = a.mulVec (matrixCurl a) := by
  ext i
  fin_cases i <;>
    simp [matrixCurl, symmetrize, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem matrixCurl_neg_square_trace_zero (a : M3) (ha : a.trace = 0) :
    matrixCurl (-a * a) = (symmetrize a).mulVec (matrixCurl a) := by
  rw [matrixCurl_neg_square, ha, zero_smul, sub_zero, strain_mulVec_matrixCurl]

theorem hasDerivAt_matrixCurl (a : ℝ → M3) (da : M3) (t : ℝ)
    (ha : HasDerivAt a da t) :
    HasDerivAt (fun τ ↦ matrixCurl (a τ)) (matrixCurl da) t := by
  have h (i j : Fin 3) := (hasDerivAt_pi.mp ((hasDerivAt_pi.mp ha) i)) j
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (h 2 1).sub (h 1 2)
  · exact (h 0 2).sub (h 2 0)
  · exact (h 1 0).sub (h 0 1)

/-- Axial contraction commutes with an ordinary spatial derivative wherever
the matrix field is differentiable. -/
theorem coordinateDerivative_matrixCurl (a : T3 → M3) (m : Fin 3) (x : T3)
    (ha : DifferentiableAt ℝ (fun h ↦ a (x + coordinateShift m h)) 0) :
    coordinateDerivative (fun y ↦ matrixCurl (a y)) m x =
      matrixCurl (matrixCoordinateDerivative a m x) :=
  (hasDerivAt_matrixCurl (fun h ↦ a (x + coordinateShift m h))
    (matrixCoordinateDerivative a m x) 0
    (DifferentiableAt.hasDerivAt (F := Fin 3 → Fin 3 → ℂ) ha)).deriv

/-- Axial contraction commutes with the actual coordinate Laplacian, not
merely with a formal Fourier multiplier. -/
theorem spatialLaplacian_matrixCurl (a : T3 → M3)
    (ha : ∀ x m, DifferentiableAt ℝ (fun h ↦ a (x + coordinateShift m h)) 0)
    (hda : ∀ x m n, DifferentiableAt ℝ
      (fun h ↦ matrixCoordinateDerivative a m (x + coordinateShift n h)) 0) (x : T3) :
    spatialLaplacian (fun y ↦ matrixCurl (a y)) x = matrixCurl (matrixLaplacian a x) := by
  rw [matrixLaplacian_eq_sum_derivative a ha hda]
  simp only [spatialLaplacian, coordinateDerivative_matrixCurl a _ _ (ha _ _),
    coordinateDerivative_matrixCurl (fun y ↦ matrixCoordinateDerivative a _ y) _ _
      (hda _ _ _), map_sum]

end Mettapedia.FluidDynamics.NavierStokes.PancakeMatrixCurlAlgebra
