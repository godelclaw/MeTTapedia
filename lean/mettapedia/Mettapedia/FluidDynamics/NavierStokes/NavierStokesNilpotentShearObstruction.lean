import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolutionObstruction

/-!
# Nilpotent Linear Shear Pressure-Residual Obstruction

This module records a finite-dimensional pressure-closure failure for a steady
nilpotent shear chain.  The field `u(x) = (x_1, x_2, 0)` is divergence-free
and has zero Laplacian, but its nonlinear convection leaves a pressure residual
with nonzero curl.  Hence no smooth pressure can make this velocity satisfy the
concrete momentum equation at any viscosity.

This is an algebraic obstruction for a shortcut class.  It is not a
slice-Schwartz solution and does not claim a nonzero positive-viscosity canary.
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

/-- The nilpotent linear shear chain `x ↦ (x_1, x_2, 0)`. -/
def nilpotentLinearShearMap : NSSpace →L[ℝ] NSSpace :=
  ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)).smulRight
      (EuclideanSpace.single nsCoord0 (1 : ℝ)) +
    ((EuclideanSpace.proj nsCoord2 : NSSpace →L[ℝ] ℝ)).smulRight
      (EuclideanSpace.single nsCoord1 (1 : ℝ))

/-- Initial data for the nilpotent linear shear chain. -/
def nilpotentLinearShearInitialVelocity : NSInitialVelocity :=
  nilpotentLinearShearMap

/-- Steady nilpotent linear shear velocity field. -/
def nilpotentLinearShearVelocityField : NSVelocityField :=
  timeIndependentVelocity nilpotentLinearShearInitialVelocity

theorem nilpotentLinearShearMap_apply (x : NSSpace) :
    nilpotentLinearShearMap x =
      EuclideanSpace.single nsCoord0 (x nsCoord1) +
        EuclideanSpace.single nsCoord1 (x nsCoord2) := by
  ext i
  fin_cases i <;> simp [nilpotentLinearShearMap, nsCoord0, nsCoord1, nsCoord2,
    ContinuousLinearMap.smulRight_apply]

/-- The nilpotent shear is divergence-free. -/
theorem spatialDivergence_nilpotentLinearShearVelocityField
    (t : NSTime) (x : NSSpace) :
    spatialDivergence nilpotentLinearShearVelocityField t x = 0 := by
  have h0 :
      (nilpotentLinearShearMap (EuclideanSpace.single nsCoord0 (1 : ℝ))) nsCoord0 = 0 := by
    simp [nilpotentLinearShearMap, nsCoord0, nsCoord1, nsCoord2,
      ContinuousLinearMap.smulRight_apply]
  have h1 :
      (nilpotentLinearShearMap (EuclideanSpace.single nsCoord1 (1 : ℝ))) nsCoord1 = 0 := by
    simp [nilpotentLinearShearMap, nsCoord0, nsCoord1, nsCoord2,
      ContinuousLinearMap.smulRight_apply]
  have h2 :
      (nilpotentLinearShearMap (EuclideanSpace.single nsCoord2 (1 : ℝ))) nsCoord2 = 0 := by
    simp [nilpotentLinearShearMap, nsCoord0, nsCoord1, nsCoord2,
      ContinuousLinearMap.smulRight_apply]
  rw [spatialDivergence]
  unfold spatialFDeriv nilpotentLinearShearVelocityField timeIndependentVelocity
    nilpotentLinearShearInitialVelocity
  rw [nilpotentLinearShearMap.fderiv, Fin.sum_univ_three]
  change
    (nilpotentLinearShearMap (EuclideanSpace.single nsCoord0 (1 : ℝ))) nsCoord0 +
          (nilpotentLinearShearMap (EuclideanSpace.single nsCoord1 (1 : ℝ))) nsCoord1 +
        (nilpotentLinearShearMap (EuclideanSpace.single nsCoord2 (1 : ℝ))) nsCoord2 =
      0
  rw [h0, h1, h2]
  norm_num

/-- The spatial derivative of the nilpotent shear is its defining linear map. -/
theorem spatialFDeriv_nilpotentLinearShearVelocityField
    (t : NSTime) (x : NSSpace) :
    spatialFDeriv nilpotentLinearShearVelocityField t x =
      nilpotentLinearShearMap := by
  unfold spatialFDeriv nilpotentLinearShearVelocityField timeIndependentVelocity
    nilpotentLinearShearInitialVelocity
  exact nilpotentLinearShearMap.fderiv (x := x)

/-- The linear shear has zero spatial Laplacian. -/
theorem spatialLaplacian_nilpotentLinearShearVelocityField
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian nilpotentLinearShearVelocityField t x = 0 := by
  simpa [spatialLaplacian, nilpotentLinearShearVelocityField,
    timeIndependentVelocity, nilpotentLinearShearInitialVelocity] using
    (laplacian_continuousLinearMap_zero (F := NSSpace) nilpotentLinearShearMap x)

/-- The nonlinear convection of the nilpotent shear is the nonzero horizontal
mode `x ↦ (x_2, 0, 0)`. -/
theorem spatialConvection_nilpotentLinearShearVelocityField
    (t : NSTime) (x : NSSpace) :
    spatialConvection nilpotentLinearShearVelocityField t x =
      EuclideanSpace.single nsCoord0 (x nsCoord2) := by
  rw [spatialConvection, spatialFDeriv_nilpotentLinearShearVelocityField]
  rw [nilpotentLinearShearVelocityField, timeIndependentVelocity,
    nilpotentLinearShearInitialVelocity, nilpotentLinearShearMap_apply]
  rw [nilpotentLinearShearMap_apply]
  ext i
  fin_cases i <;> simp [nsCoord0, nsCoord1, nsCoord2]

theorem timeVelocityDerivative_nilpotentLinearShearVelocityField
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative nilpotentLinearShearVelocityField t x = 0 :=
  timeVelocityDerivative_timeIndependentVelocity nilpotentLinearShearInitialVelocity t x

/-- The pressure residual is the negative of the nonlinear convection and is
independent of viscosity. -/
theorem momentumPressureResidual_nilpotentLinearShearVelocityField
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    momentumPressureResidual ν nilpotentLinearShearVelocityField t x =
      -EuclideanSpace.single nsCoord0 (x nsCoord2) := by
  rw [momentumPressureResidual,
    spatialLaplacian_nilpotentLinearShearVelocityField,
    timeVelocityDerivative_nilpotentLinearShearVelocityField,
    spatialConvection_nilpotentLinearShearVelocityField]
  simp

/-- The residual field `x ↦ -(x_2, 0, 0)`. -/
def negativeCoord2HorizontalShearVelocityField : NSVelocityField :=
  fun _ x => -EuclideanSpace.single nsCoord0 (x nsCoord2)

theorem spatialFDeriv_negativeCoord2HorizontalShearVelocityField
    (t : NSTime) (x : NSSpace) :
    spatialFDeriv negativeCoord2HorizontalShearVelocityField t x =
      -((EuclideanSpace.proj nsCoord2 : NSSpace →L[ℝ] ℝ).smulRight
        (EuclideanSpace.single nsCoord0 (1 : ℝ))) := by
  unfold spatialFDeriv negativeCoord2HorizontalShearVelocityField
  let L : NSSpace →L[ℝ] NSSpace :=
    -((EuclideanSpace.proj nsCoord2 : NSSpace →L[ℝ] ℝ).smulRight
      (EuclideanSpace.single nsCoord0 (1 : ℝ)))
  have hfun :
      (fun y : NSSpace => -EuclideanSpace.single nsCoord0 (y nsCoord2)) =
        fun y : NSSpace => L y := by
    funext y
    ext i
    fin_cases i <;> simp [L, nsCoord0, nsCoord2,
      ContinuousLinearMap.smulRight_apply]
  rw [hfun]
  exact L.fderiv (x := x)

/-- The residual has constant nonzero curl. -/
theorem spatialVorticity_negativeCoord2HorizontalShearVelocityField
    (t : NSTime) (x : NSSpace) :
    spatialVorticity negativeCoord2HorizontalShearVelocityField t x =
      EuclideanSpace.single nsCoord1 (-1 : ℝ) := by
  ext i
  fin_cases i <;>
    simp [spatialVorticity, spatialDerivativeComponent,
      spatialFDeriv_negativeCoord2HorizontalShearVelocityField,
      nsCoord0, nsCoord1, nsCoord2, ContinuousLinearMap.smulRight_apply]

/-- The nilpotent shear pressure residual has viscosity-independent nonzero
curl everywhere. -/
theorem spatialVorticity_momentumPressureResidual_nilpotentLinearShearVelocityField
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (momentumPressureResidual ν nilpotentLinearShearVelocityField) t x =
      EuclideanSpace.single nsCoord1 (-1 : ℝ) := by
  rw [spatialVorticity_congr_at
    (u := momentumPressureResidual ν nilpotentLinearShearVelocityField)
    (v := negativeCoord2HorizontalShearVelocityField)
    (t := t) (x := x)]
  · exact spatialVorticity_negativeCoord2HorizontalShearVelocityField t x
  · intro y
    exact momentumPressureResidual_nilpotentLinearShearVelocityField ν t y

theorem spatialVorticity_momentumPressureResidual_nilpotentLinearShearVelocityField_ne_zero
    (ν : ℝ) (t : NSTime) (x : NSSpace) :
    spatialVorticity (momentumPressureResidual ν nilpotentLinearShearVelocityField) t x ≠ 0 := by
  rw [spatialVorticity_momentumPressureResidual_nilpotentLinearShearVelocityField]
  intro h
  have hcoord := congrArg (fun v : NSSpace => v nsCoord1) h
  norm_num [nsCoord1] at hcoord

/-- No smooth pressure can repair the nilpotent shear chain into the concrete
momentum equation at any viscosity. -/
theorem not_exists_smoothPressure_momentumEquation_nilpotentLinearShearVelocityField
    (ν : ℝ) :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ t x,
          timeVelocityDerivative nilpotentLinearShearVelocityField t x +
              spatialConvection nilpotentLinearShearVelocityField t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian nilpotentLinearShearVelocityField t x := by
  exact
    not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
      (ν := ν) (u := nilpotentLinearShearVelocityField)
      ⟨0, 0,
        spatialVorticity_momentumPressureResidual_nilpotentLinearShearVelocityField_ne_zero
          ν 0 0⟩

/-- No slice-Schwartz concrete solution can use the nilpotent shear velocity.
The obstruction is the same nonzero pressure-residual curl. -/
theorem not_exists_schwartzConcreteSolution_velocity_nilpotentLinearShearVelocityField
    (ν : ℝ) :
    ¬ ∃ S : SchwartzConcreteNavierStokesSolution ν,
      S.velocity = nilpotentLinearShearVelocityField := by
  exact
    not_exists_schwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
      (ν := ν) (u := nilpotentLinearShearVelocityField)
      ⟨0, 0,
        spatialVorticity_momentumPressureResidual_nilpotentLinearShearVelocityField_ne_zero
          ν 0 0⟩

/-- The nonzero slice-Schwartz concrete interface is likewise excluded for the
nilpotent shear velocity. -/
theorem not_exists_nonzeroSchwartzConcreteSolution_velocity_nilpotentLinearShearVelocityField
    (ν : ℝ) :
    ¬ ∃ S : NonzeroSchwartzConcreteNavierStokesSolution ν,
      S.velocity = nilpotentLinearShearVelocityField := by
  exact
    not_exists_nonzeroSchwartzConcreteSolution_velocity_of_momentumPressureResidual_vorticity_ne_zero
      (ν := ν) (u := nilpotentLinearShearVelocityField)
      ⟨0, 0,
        spatialVorticity_momentumPressureResidual_nilpotentLinearShearVelocityField_ne_zero
          ν 0 0⟩

end NavierStokes
end FluidDynamics
end Mettapedia
