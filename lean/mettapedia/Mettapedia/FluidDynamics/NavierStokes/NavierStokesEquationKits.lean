import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationCore

/-!
# Concrete Navier-Stokes Differential Kits

This module contains the progressively concrete differential-kit constructors,
ending in the fully concrete Navier-Stokes theorem surface.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section ConcreteEquationTarget

open scoped Laplacian ContDiff

/-- A partially concrete NS differential kit where divergence and divergence-free
initial data are no longer abstract: they are given by the actual trace of the
spatial Fréchet derivative on `ℝ^3`. -/
def mkWithConcreteDivergence
    (timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace)
    (convection : NSVelocityField → NSTime → NSSpace → NSSpace)
    (pressureGradient : NSPressureField → NSTime → NSSpace → NSSpace)
    (laplacian : NSVelocityField → NSTime → NSSpace → NSSpace)
    (smoothVelocity : NSVelocityField → Prop)
    (smoothPressure : NSPressureField → Prop)
    (boundedEnergy : NSVelocityField → Prop)
    (smoothInitialData : NSInitialVelocity → Prop) :
    NavierStokesDifferentialKit where
  timeDerivative := timeDerivative
  convection := convection
  pressureGradient := pressureGradient
  laplacian := laplacian
  divergence := spatialDivergence
  smoothVelocity := smoothVelocity
  smoothPressure := smoothPressure
  boundedEnergy := boundedEnergy
  smoothInitialData := smoothInitialData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

/-- A further partially concrete NS differential kit where both pressure
gradient and divergence are fixed to their actual calculus-side meanings on
`ℝ^3`. -/
def mkWithConcreteGradientAndDivergence
    (timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace)
    (convection : NSVelocityField → NSTime → NSSpace → NSSpace)
    (laplacian : NSVelocityField → NSTime → NSSpace → NSSpace)
    (smoothVelocity : NSVelocityField → Prop)
    (smoothPressure : NSPressureField → Prop)
    (boundedEnergy : NSVelocityField → Prop)
    (smoothInitialData : NSInitialVelocity → Prop) :
    NavierStokesDifferentialKit where
  timeDerivative := timeDerivative
  convection := convection
  pressureGradient := spatialPressureGradient
  laplacian := laplacian
  divergence := spatialDivergence
  smoothVelocity := smoothVelocity
  smoothPressure := smoothPressure
  boundedEnergy := boundedEnergy
  smoothInitialData := smoothInitialData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

/-- A still more concrete NS differential kit where time derivative, pressure
gradient, divergence, and divergence-free initial data are all fixed to their
actual calculus-side meanings on `ℝ × ℝ^3`. -/
def mkWithConcreteTimeGradientAndDivergence
    (convection : NSVelocityField → NSTime → NSSpace → NSSpace)
    (laplacian : NSVelocityField → NSTime → NSSpace → NSSpace)
    (smoothVelocity : NSVelocityField → Prop)
    (smoothPressure : NSPressureField → Prop)
    (boundedEnergy : NSVelocityField → Prop)
    (smoothInitialData : NSInitialVelocity → Prop) :
    NavierStokesDifferentialKit where
  timeDerivative := timeVelocityDerivative
  convection := convection
  pressureGradient := spatialPressureGradient
  laplacian := laplacian
  divergence := spatialDivergence
  smoothVelocity := smoothVelocity
  smoothPressure := smoothPressure
  boundedEnergy := boundedEnergy
  smoothInitialData := smoothInitialData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

/-- A yet more concrete NS differential kit where time derivative, convection,
pressure gradient, divergence, and divergence-free initial data are all fixed
to their actual calculus-side meanings on `ℝ × ℝ^3`. -/
def mkWithConcreteTimeConvectionGradientAndDivergence
    (laplacian : NSVelocityField → NSTime → NSSpace → NSSpace)
    (smoothVelocity : NSVelocityField → Prop)
    (smoothPressure : NSPressureField → Prop)
    (boundedEnergy : NSVelocityField → Prop)
    (smoothInitialData : NSInitialVelocity → Prop) :
    NavierStokesDifferentialKit where
  timeDerivative := timeVelocityDerivative
  convection := spatialConvection
  pressureGradient := spatialPressureGradient
  laplacian := laplacian
  divergence := spatialDivergence
  smoothVelocity := smoothVelocity
  smoothPressure := smoothPressure
  boundedEnergy := boundedEnergy
  smoothInitialData := smoothInitialData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

/-- A fully differential-side concrete NS kit where time derivative, convection,
pressure gradient, Laplacian, divergence, and divergence-free initial data are
all fixed to their actual calculus-side meanings on `ℝ × ℝ^3`. -/
def mkWithConcreteDifferentialOperators
    (smoothVelocity : NSVelocityField → Prop)
    (smoothPressure : NSPressureField → Prop)
    (boundedEnergy : NSVelocityField → Prop)
    (smoothInitialData : NSInitialVelocity → Prop) :
    NavierStokesDifferentialKit where
  timeDerivative := timeVelocityDerivative
  convection := spatialConvection
  pressureGradient := spatialPressureGradient
  laplacian := spatialLaplacian
  divergence := spatialDivergence
  smoothVelocity := smoothVelocity
  smoothPressure := smoothPressure
  boundedEnergy := boundedEnergy
  smoothInitialData := smoothInitialData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

/-- A theorem surface where the full differential operator content and the
smoothness predicates are all concrete; only bounded energy remains abstract. -/
def mkWithConcreteDifferentialOperatorsAndSmoothness
    (boundedEnergy : NSVelocityField → Prop) :
    NavierStokesDifferentialKit where
  timeDerivative := timeVelocityDerivative
  convection := spatialConvection
  pressureGradient := spatialPressureGradient
  laplacian := spatialLaplacian
  divergence := spatialDivergence
  smoothVelocity := smoothSpaceTimeVelocity
  smoothPressure := smoothSpaceTimePressure
  boundedEnergy := boundedEnergy
  smoothInitialData := smoothInitialVelocityData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

/-- A fully concrete theorem surface where the differential operators,
smoothness predicates, and bounded-energy predicate are all literal. -/
def mkFullyConcreteNavierStokesSurface :
    NavierStokesDifferentialKit where
  timeDerivative := timeVelocityDerivative
  convection := spatialConvection
  pressureGradient := spatialPressureGradient
  laplacian := spatialLaplacian
  divergence := spatialDivergence
  smoothVelocity := smoothSpaceTimeVelocity
  smoothPressure := smoothSpaceTimePressure
  boundedEnergy := boundedKineticEnergy
  smoothInitialData := smoothInitialVelocityData
  divergenceFreeInitialData := fun u₀ => ∀ x, initialSpatialDivergence u₀ x = 0

end ConcreteEquationTarget

end NavierStokes
end FluidDynamics
end Mettapedia
