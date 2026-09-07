import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalGradientEquation

/-!
# Symmetrization commutes with ordinary matrix transport and diffusion

All spatial operators use ordinary coordinate derivatives. The commutation
laws require and expose the differentiability of the original matrix field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeMatrixDifferentialSymmetry

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalGradientEquation
open PancakeFilteredStrainDynamics PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian
open PancakeSpatialGradientDifferentiation PancakeFourierTranslationCurve

local notation "T3" => UnitAddTorus (Fin 3)
local notation "M3" => Matrix (Fin 3) (Fin 3) ℂ

def matrixCoordinateDerivative (a : T3 → M3) (m : Fin 3) (x : T3) : M3 :=
  deriv (fun h : ℝ ↦ a (x + coordinateShift m h)) 0

theorem hasDerivAt_symmetrize (a : ℝ → M3) (da : M3) (t : ℝ)
    (ha : HasDerivAt a da t) :
    HasDerivAt (fun τ ↦ symmetrize (a τ)) (symmetrize da) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  change HasDerivAt (fun τ ↦ (1 / 2 : ℂ) * (a τ i j + a τ j i))
    ((1 / 2 : ℂ) * (da i j + da j i)) t
  exact (((hasDerivAt_pi.mp ((hasDerivAt_pi.mp ha) i)) j).add
    ((hasDerivAt_pi.mp ((hasDerivAt_pi.mp ha) j)) i)).const_mul _

theorem matrixCoordinateDerivative_symmetrize (a : T3 → M3) (m : Fin 3) (x : T3)
    (ha : DifferentiableAt ℝ (fun h ↦ a (x + coordinateShift m h)) 0) :
    matrixCoordinateDerivative (fun y ↦ symmetrize (a y)) m x =
      symmetrize (matrixCoordinateDerivative a m x) :=
  HasDerivAt.deriv (F := Fin 3 → Fin 3 → ℂ)
    (hasDerivAt_symmetrize (fun h : ℝ ↦ a (x + coordinateShift m h))
      (matrixCoordinateDerivative a m x) 0
      (DifferentiableAt.hasDerivAt (F := Fin 3 → Fin 3 → ℂ) ha))

theorem coordinateDerivative_matrixColumn (a : T3 → M3) (m : Fin 3) (x : T3)
    (ha : DifferentiableAt ℝ (fun h ↦ a (x + coordinateShift m h)) 0) (j : Fin 3) :
    coordinateDerivative (fun y i ↦ a y i j) m x =
      fun i ↦ matrixCoordinateDerivative a m x i j := by
  have hc : HasDerivAt (fun h ↦ fun i ↦ a (x + coordinateShift m h) i j)
      (fun i ↦ matrixCoordinateDerivative a m x i j) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    exact (hasDerivAt_pi.mp ((hasDerivAt_pi.mp ha.hasDerivAt) i)) j
  exact hc.deriv

theorem matrixTransport_eq_sum_derivative (u : T3 → VelocityCoefficient) (a : T3 → M3) (x : T3)
    (ha : ∀ m, DifferentiableAt ℝ (fun h ↦ a (x + coordinateShift m h)) 0) :
    matrixTransport u a x = ∑ m : Fin 3, u x m • matrixCoordinateDerivative a m x := by
  ext i j
  simp only [matrixTransport, spatialTransport, coordinateDerivative_matrixColumn a _ x (ha _),
    Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply, Matrix.smul_apply]

theorem matrixTransport_symmetrize (u : T3 → VelocityCoefficient) (a : T3 → M3) (x : T3)
    (ha : ∀ m, DifferentiableAt ℝ (fun h ↦ a (x + coordinateShift m h)) 0) :
    matrixTransport u (fun y ↦ symmetrize (a y)) x = symmetrize (matrixTransport u a x) := by
  have hs (m : Fin 3) : DifferentiableAt ℝ
      (fun h ↦ symmetrize (a (x + coordinateShift m h))) 0 :=
    HasDerivAt.differentiableAt (F := Fin 3 → Fin 3 → ℂ)
      (hasDerivAt_symmetrize (fun h : ℝ ↦ a (x + coordinateShift m h))
        (matrixCoordinateDerivative a m x) 0
        (DifferentiableAt.hasDerivAt (F := Fin 3 → Fin 3 → ℂ) (ha m)))
  rw [matrixTransport_eq_sum_derivative u _ x hs, matrixTransport_eq_sum_derivative u a x ha]
  simp only [matrixCoordinateDerivative_symmetrize a _ x (ha _), map_sum, map_smul]

theorem matrixLaplacian_eq_sum_derivative (a : T3 → M3)
    (ha : ∀ x m, DifferentiableAt ℝ (fun h ↦ a (x + coordinateShift m h)) 0)
    (hda : ∀ x m n, DifferentiableAt ℝ
      (fun h ↦ matrixCoordinateDerivative a m (x + coordinateShift n h)) 0) (x : T3) :
    matrixLaplacian a x =
      ∑ m : Fin 3, matrixCoordinateDerivative (fun y ↦ matrixCoordinateDerivative a m y) m x := by
  ext i j
  simp only [matrixLaplacian, spatialLaplacian,
    coordinateDerivative_matrixColumn a _ _ (ha _ _),
    coordinateDerivative_matrixColumn (fun y ↦ matrixCoordinateDerivative a _ y) _ _ (hda _ _ _),
    Finset.sum_apply, Matrix.sum_apply]

theorem matrixLaplacian_symmetrize (a : T3 → M3)
    (ha : ∀ x m, DifferentiableAt ℝ (fun h ↦ a (x + coordinateShift m h)) 0)
    (hda : ∀ x m n, DifferentiableAt ℝ
      (fun h ↦ matrixCoordinateDerivative a m (x + coordinateShift n h)) 0) (x : T3) :
    matrixLaplacian (fun y ↦ symmetrize (a y)) x = symmetrize (matrixLaplacian a x) := by
  have hs (x : T3) (m : Fin 3) : DifferentiableAt ℝ
      (fun h ↦ symmetrize (a (x + coordinateShift m h))) 0 :=
    HasDerivAt.differentiableAt (F := Fin 3 → Fin 3 → ℂ)
      (hasDerivAt_symmetrize (fun h : ℝ ↦ a (x + coordinateShift m h))
        (matrixCoordinateDerivative a m x) 0
        (DifferentiableAt.hasDerivAt (F := Fin 3 → Fin 3 → ℂ) (ha x m)))
  have hds (x : T3) (m n : Fin 3) : DifferentiableAt ℝ
      (fun h ↦ matrixCoordinateDerivative (fun y ↦ symmetrize (a y)) m
        (x + coordinateShift n h)) 0 := by
    simp only [matrixCoordinateDerivative_symmetrize a _ _ (ha _ _)]
    exact HasDerivAt.differentiableAt (F := Fin 3 → Fin 3 → ℂ)
      (hasDerivAt_symmetrize
        (fun h : ℝ ↦ matrixCoordinateDerivative a m (x + coordinateShift n h))
        (matrixCoordinateDerivative (fun y ↦ matrixCoordinateDerivative a m y) n x) 0
        (DifferentiableAt.hasDerivAt (F := Fin 3 → Fin 3 → ℂ) (hda x m n)))
  rw [matrixLaplacian_eq_sum_derivative _ hs hds, matrixLaplacian_eq_sum_derivative a ha hda]
  simp only [matrixCoordinateDerivative_symmetrize a _ _ (ha _ _),
    matrixCoordinateDerivative_symmetrize (fun y ↦ matrixCoordinateDerivative a _ y) _ _ (hda _ _ _),
    map_sum]

end Mettapedia.FluidDynamics.NavierStokes.PancakeMatrixDifferentialSymmetry
