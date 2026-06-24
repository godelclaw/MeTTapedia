import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Basic

/-!
# Vector Calculus R3: LocalOperators

Pointwise congruence and elementary bounds for spatial derivatives and vorticity.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped Gradient
open scoped Laplacian
open scoped BigOperators
open scoped ContDiff

section VectorCalculusR3

/-- Spatial coordinate derivatives only depend on the velocity field on the
fixed time slice. -/
theorem spatialDerivativeComponent_congr_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, u t y = v t y) (coord comp : Fin 3) :
    spatialDerivativeComponent u t x coord comp =
      spatialDerivativeComponent v t x coord comp := by
  unfold spatialDerivativeComponent spatialFDeriv
  have hf : (fun y : NSSpace => u t y) = fun y : NSSpace => v t y := funext h
  rw [hf]

/-- The concrete vorticity at a point only depends on the velocity field on
the fixed time slice. -/
theorem spatialVorticity_congr_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, u t y = v t y) :
    spatialVorticity u t x = spatialVorticity v t x := by
  have hderiv :
      ∀ coord comp : Fin 3,
        spatialDerivativeComponent u t x coord comp =
          spatialDerivativeComponent v t x coord comp := by
    intro coord comp
    exact spatialDerivativeComponent_congr_at h coord comp
  ext i
  fin_cases i <;>
    simp [spatialVorticity, hderiv]

/-- The spatial Fréchet derivative only depends on the velocity field on the
fixed time slice. -/
theorem spatialFDeriv_congr_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, u t y = v t y) :
    spatialFDeriv u t x = spatialFDeriv v t x := by
  unfold spatialFDeriv
  have hf : (fun y : NSSpace => u t y) = fun y : NSSpace => v t y := funext h
  rw [hf]

/-- Spatial divergence only depends on the velocity field on the fixed time
slice. -/
theorem spatialDivergence_congr_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, u t y = v t y) :
    spatialDivergence u t x = spatialDivergence v t x := by
  unfold spatialDivergence
  rw [spatialFDeriv_congr_at h]

/-- The convection term only depends on the velocity field on the fixed time
slice. -/
theorem spatialConvection_congr_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, u t y = v t y) :
    spatialConvection u t x = spatialConvection v t x := by
  unfold spatialConvection
  rw [spatialFDeriv_congr_at h, h x]

/-- Spatial Laplacian only depends on the velocity field on the fixed time
slice. -/
theorem spatialLaplacian_congr_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : ∀ y : NSSpace, u t y = v t y) :
    spatialLaplacian u t x = spatialLaplacian v t x := by
  unfold spatialLaplacian
  have hf : (fun y : NSSpace => u t y) = fun y : NSSpace => v t y := funext h
  rw [hf]

/-- Pointwise norm control for the concrete vorticity vector by the six
coordinate derivatives that enter the curl formula. -/
theorem norm_spatialVorticity_le_sum_abs_spatialDerivativeComponent
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    ‖spatialVorticity u t x‖ ≤
      |spatialDerivativeComponent u t x nsCoord1 nsCoord2| +
        |spatialDerivativeComponent u t x nsCoord2 nsCoord1| +
        |spatialDerivativeComponent u t x nsCoord2 nsCoord0| +
        |spatialDerivativeComponent u t x nsCoord0 nsCoord2| +
        |spatialDerivativeComponent u t x nsCoord0 nsCoord1| +
        |spatialDerivativeComponent u t x nsCoord1 nsCoord0| := by
  let d12 := spatialDerivativeComponent u t x nsCoord1 nsCoord2
  let d21 := spatialDerivativeComponent u t x nsCoord2 nsCoord1
  let d20 := spatialDerivativeComponent u t x nsCoord2 nsCoord0
  let d02 := spatialDerivativeComponent u t x nsCoord0 nsCoord2
  let d01 := spatialDerivativeComponent u t x nsCoord0 nsCoord1
  let d10 := spatialDerivativeComponent u t x nsCoord1 nsCoord0
  change
    ‖EuclideanSpace.single nsCoord0 (d12 - d21) +
        EuclideanSpace.single nsCoord1 (d20 - d02) +
        EuclideanSpace.single nsCoord2 (d01 - d10)‖ ≤
      |d12| + |d21| + |d20| + |d02| + |d01| + |d10|
  have hnorm :
      ‖EuclideanSpace.single nsCoord0 (d12 - d21) +
          EuclideanSpace.single nsCoord1 (d20 - d02) +
          EuclideanSpace.single nsCoord2 (d01 - d10)‖ ≤
        |d12 - d21| + |d20 - d02| + |d01 - d10| := by
    calc
      ‖EuclideanSpace.single nsCoord0 (d12 - d21) +
          EuclideanSpace.single nsCoord1 (d20 - d02) +
          EuclideanSpace.single nsCoord2 (d01 - d10)‖
        ≤
          ‖EuclideanSpace.single nsCoord0 (d12 - d21) +
            EuclideanSpace.single nsCoord1 (d20 - d02)‖ +
            ‖EuclideanSpace.single nsCoord2 (d01 - d10)‖ := by
            exact norm_add_le _ _
      _ ≤
          (‖EuclideanSpace.single nsCoord0 (d12 - d21)‖ +
            ‖EuclideanSpace.single nsCoord1 (d20 - d02)‖) +
            ‖EuclideanSpace.single nsCoord2 (d01 - d10)‖ := by
            gcongr
            exact norm_add_le _ _
      _ = |d12 - d21| + |d20 - d02| + |d01 - d10| := by
            simp [add_assoc]
  have h12 : |d12 - d21| ≤ |d12| + |d21| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le d12 (-d21)
  have h20 : |d20 - d02| ≤ |d20| + |d02| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le d20 (-d02)
  have h01 : |d01 - d10| ≤ |d01| + |d10| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le d01 (-d10)
  calc
    ‖EuclideanSpace.single nsCoord0 (d12 - d21) +
        EuclideanSpace.single nsCoord1 (d20 - d02) +
        EuclideanSpace.single nsCoord2 (d01 - d10)‖
      ≤ |d12 - d21| + |d20 - d02| + |d01 - d10| := hnorm
    _ ≤ (|d12| + |d21|) + (|d20| + |d02|) + (|d01| + |d10|) := by
      gcongr
    _ = |d12| + |d21| + |d20| + |d02| + |d01| + |d10| := by
      ring

/-- If every coordinate derivative entering the concrete curl is bounded by a
common constant, then the vorticity norm is bounded by six times that
constant. -/
theorem norm_spatialVorticity_le_of_abs_spatialDerivativeComponent_le
    {u : NSVelocityField} {t : NSTime} {x : NSSpace} {K : ℝ}
    (hK : ∀ coord comp : Fin 3,
      |spatialDerivativeComponent u t x coord comp| ≤ K) :
    ‖spatialVorticity u t x‖ ≤ 6 * K := by
  have hsum := norm_spatialVorticity_le_sum_abs_spatialDerivativeComponent u t x
  have h12 := hK nsCoord1 nsCoord2
  have h21 := hK nsCoord2 nsCoord1
  have h20 := hK nsCoord2 nsCoord0
  have h02 := hK nsCoord0 nsCoord2
  have h01 := hK nsCoord0 nsCoord1
  have h10 := hK nsCoord1 nsCoord0
  nlinarith
end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
