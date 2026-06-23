import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationCore
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationKits
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationProblemData
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationFiniteEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationComponentBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationEquivalences
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationKitIff
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Vector Calculus R3: Basic

Basic coordinates, concrete Navier-Stokes seed fields, and the concrete curl operator on R^3.
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

def nsCoord0 : Fin 3 := ⟨0, by decide⟩

/-- The coordinate `1` in `Fin 3`. -/
def nsCoord1 : Fin 3 := ⟨1, by decide⟩

/-- The coordinate `2` in `Fin 3`. -/
def nsCoord2 : Fin 3 := ⟨2, by decide⟩

/-- Constant velocity field on `ℝ × ℝ^3`. -/
def constantVelocityField (c : NSSpace) : NSVelocityField :=
  fun _ : NSTime => fun _ : NSSpace => c

/-- Constant initial velocity data on `ℝ^3`. -/
def constantInitialVelocity (c : NSSpace) : NSInitialVelocity :=
  fun _ : NSSpace => c

/-- Addition of constant initial data is again constant initial data. -/
theorem constantInitialVelocity_add
    (u v : NSSpace) :
    constantInitialVelocity u + constantInitialVelocity v =
      constantInitialVelocity (u + v) := by
  funext x
  simp [constantInitialVelocity]

/-- Linear shear map `x ↦ (a * x₁, 0, 0)` on `ℝ^3`. -/
def linearShearMap (a : ℝ) : NSSpace →L[ℝ] NSSpace :=
  ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)).smulRight
    (EuclideanSpace.single nsCoord0 a)

/-- Linear shear initial velocity data `x ↦ (a * x₁, 0, 0)` on `ℝ^3`. -/
def linearShearInitialVelocity (a : ℝ) : NSInitialVelocity :=
  linearShearMap a

/-- Steady linear shear velocity field `u(t,x) = (a * x₁, 0, 0)` on
`ℝ × ℝ^3`. -/
def linearShearVelocityField (a : ℝ) : NSVelocityField :=
  fun _ : NSTime => linearShearInitialVelocity a

/-- Initial velocity data `x ↦ (a * x₁, 0, b)` on `ℝ^3`. -/
def linearShearVerticalDriftInitialVelocity (a b : ℝ) : NSInitialVelocity :=
  linearShearInitialVelocity a +
    constantInitialVelocity (EuclideanSpace.single nsCoord2 b)

/-- Steady velocity field `u(t,x) = (a * x₁, 0, b)` on `ℝ × ℝ^3`. -/
def linearShearVerticalDriftVelocityField (a b : ℝ) : NSVelocityField :=
  linearShearVelocityField a +
    constantVelocityField (EuclideanSpace.single nsCoord2 b)

/-- Initial velocity data `x ↦ (a * x₁, b, 0)` on `ℝ^3`. -/
def linearShearHorizontalDriftInitialVelocity (a b : ℝ) : NSInitialVelocity :=
  linearShearInitialVelocity a +
    constantInitialVelocity (EuclideanSpace.single nsCoord1 b)

/-- Steady velocity field `u(t,x) = (a * x₁, b, 0)` on `ℝ × ℝ^3`. -/
def linearShearHorizontalDriftVelocityField (a b : ℝ) : NSVelocityField :=
  linearShearVelocityField a +
    constantVelocityField (EuclideanSpace.single nsCoord1 b)

/-- Initial velocity data `x ↦ (a * x₁, b, c)` on `ℝ^3`. -/
def linearShearFullDriftInitialVelocity (a b c : ℝ) : NSInitialVelocity :=
  linearShearHorizontalDriftInitialVelocity a b +
    constantInitialVelocity (EuclideanSpace.single nsCoord2 c)

/-- Steady velocity field `u(t,x) = (a * x₁, b, c)` on `ℝ × ℝ^3`. -/
def linearShearFullDriftVelocityField (a b c : ℝ) : NSVelocityField :=
  linearShearHorizontalDriftVelocityField a b +
    constantVelocityField (EuclideanSpace.single nsCoord2 c)

/-- Pressure field `p(t,x) = -(a * b) * x₀` balancing the horizontal-drift
shear convection on `ℝ × ℝ^3`. -/
def linearShearHorizontalDriftPressureField (a b : ℝ) : NSPressureField :=
  fun _ : NSTime => fun x : NSSpace => -(a * b * x nsCoord0)

/-- Continuous linear embedding of scalar profiles into the first velocity
component. -/
def coord0Embedding : ℝ →L[ℝ] NSSpace :=
  (1 : ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single nsCoord0 (1 : ℝ))

/-- Scalar initial profile `x ↦ a * sin (k * x₁)` for the non-affine heat-shear
branch. -/
def heatShearInitialScalar (a k : ℝ) : NSSpace → ℝ :=
  fun x => a * Real.sin (k * x nsCoord1)

/-- Scalar space-time profile `a * exp (-(ν * k²) * t) * sin (k * x₁)` solving
the one-dimensional heat equation along the `x₁` direction. -/
def heatShearScalar (ν a k : ℝ) : NSTime → NSSpace → ℝ :=
  fun t x => a * (Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * x nsCoord1))

/-- Initial velocity data for the damped sinusoidal heat-shear family,
`x ↦ (a * sin (k * x₁), 0, 0)`. -/
def heatShearInitialVelocity (a k : ℝ) : NSInitialVelocity :=
  fun x => coord0Embedding (heatShearInitialScalar a k x)

/-- Non-affine heat-shear velocity field
`u(t,x) = (a * exp (-(ν * k²) * t) * sin (k * x₁), 0, 0)`. -/
def heatShearVelocityField (ν a k : ℝ) : NSVelocityField :=
  fun t x => coord0Embedding (heatShearScalar ν a k t x)

/-- General time-amplitude shear ansatz
`u(t,x) = (A t * sin (k * x₁), 0, 0)`.  This isolates the ODE burden on the
amplitude from the spatial vector-calculus calculation. -/
def amplitudeShearVelocityField (A : NSTime → ℝ) (k : ℝ) : NSVelocityField :=
  fun t x => coord0Embedding (A t * Real.sin (k * x nsCoord1))

/-- Initial velocity data for the heat-shear family with constant streamwise
drift, `x ↦ (d + a * sin (k * x₁), 0, 0)`. -/
def heatShearStreamwiseDriftInitialVelocity (a k d : ℝ) : NSInitialVelocity :=
  heatShearInitialVelocity a k +
    constantInitialVelocity (EuclideanSpace.single nsCoord0 d)

/-- Space-time heat-shear family with constant streamwise drift,
`u(t,x) = (d + a * exp (-(ν * k²) * t) * sin (k * x₁), 0, 0)`. -/
def heatShearStreamwiseDriftVelocityField (ν a k d : ℝ) : NSVelocityField :=
  heatShearVelocityField ν a k +
    constantVelocityField (EuclideanSpace.single nsCoord0 d)

/-- Initial velocity data for the heat-shear family with constant drift in the
third component, `x ↦ (a * sin (k * x₁), 0, c)`. -/
def heatShearVerticalDriftInitialVelocity (a k c : ℝ) : NSInitialVelocity :=
  heatShearInitialVelocity a k +
    constantInitialVelocity (EuclideanSpace.single nsCoord2 c)

/-- Space-time heat-shear family with constant drift in the third component,
`u(t,x) = (a * exp (-(ν * k²) * t) * sin (k * x₁), 0, c)`. -/
def heatShearVerticalDriftVelocityField (ν a k c : ℝ) : NSVelocityField :=
  heatShearVelocityField ν a k +
    constantVelocityField (EuclideanSpace.single nsCoord2 c)

/-- Initial velocity data for the heat-shear family with both constant
streamwise and vertical drifts, `x ↦ (d + a * sin (k * x₁), 0, c)`. -/
def heatShearFullDriftInitialVelocity (a k d c : ℝ) : NSInitialVelocity :=
  heatShearStreamwiseDriftInitialVelocity a k d +
    constantInitialVelocity (EuclideanSpace.single nsCoord2 c)

/-- Space-time heat-shear family with both constant streamwise and vertical
drifts, `u(t,x) = (d + a * exp (-(ν * k²) * t) * sin (k * x₁), 0, c)`. -/
def heatShearFullDriftVelocityField (ν a k d c : ℝ) : NSVelocityField :=
  heatShearStreamwiseDriftVelocityField ν a k d +
    constantVelocityField (EuclideanSpace.single nsCoord2 c)

/-- Initial velocity data for the transported heat-shear family,
`x ↦ (a * sin (k * x₁), b, 0)`. -/
def heatShearTransportInitialVelocity (a k b : ℝ) : NSInitialVelocity :=
  heatShearInitialVelocity a k +
    constantInitialVelocity (EuclideanSpace.single nsCoord1 b)

/-- Scalar space-time profile
`a * exp (-(ν * k²) * t) * sin (k * (x₁ - b * t))` solving the one-dimensional
advection-diffusion equation along the `x₁` direction with transport speed
`b`. -/
def heatShearTransportScalar (ν a k b : ℝ) : NSTime → NSSpace → ℝ :=
  fun t x => a * (Real.exp (-(ν * k ^ (2 : ℕ)) * t) * Real.sin (k * (x nsCoord1 - b * t)))

/-- Transported non-affine heat-shear velocity field
`u(t,x) = (a * exp (-(ν * k²) * t) * sin (k * (x₁ - b * t)), b, 0)`. -/
def heatShearTransportVelocityField (ν a k b : ℝ) : NSVelocityField :=
  (fun t x => coord0Embedding (heatShearTransportScalar ν a k b t x)) +
    constantVelocityField (EuclideanSpace.single nsCoord1 b)

/-- Transported shear with an arbitrary time amplitude,
`u(t,x) = (A t * sin (k * (x₁ - b * t)), b, 0)`. -/
def amplitudeShearTransportVelocityField
    (A : NSTime → ℝ) (k b : ℝ) : NSVelocityField :=
  (fun t x => coord0Embedding (A t * Real.sin (k * (x nsCoord1 - b * t)))) +
    constantVelocityField (EuclideanSpace.single nsCoord1 b)

/-- Initial velocity data for the transported heat-shear family with additional
constant streamwise and vertical drifts,
`x ↦ (d + a * sin (k * x₁), b, c)`. -/
def heatShearTransportFullDriftInitialVelocity (a k b d c : ℝ) : NSInitialVelocity :=
  heatShearTransportInitialVelocity a k b +
    constantInitialVelocity
      (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)

/-- Transported non-affine heat-shear velocity field with additional constant
streamwise and vertical drifts,
`u(t,x) = (d + a * exp (-(ν * k²) * t) * sin (k * (x₁ - b * t)), b, c)`. -/
def heatShearTransportFullDriftVelocityField (ν a k b d c : ℝ) : NSVelocityField :=
  heatShearTransportVelocityField ν a k b +
    constantVelocityField
      (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)

/-- Directional derivative of the `comp` component of a velocity field in the
spatial coordinate direction `coord`. -/
def spatialDerivativeComponent
    (u : NSVelocityField) (t : NSTime) (x : NSSpace)
    (coord comp : Fin 3) : ℝ :=
  (spatialFDeriv u t x (EuclideanSpace.single coord (1 : ℝ))) comp

/-- Concrete vorticity / curl operator on `ℝ^3`. -/
def spatialVorticity (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  EuclideanSpace.single nsCoord0
      (spatialDerivativeComponent u t x nsCoord1 nsCoord2 -
        spatialDerivativeComponent u t x nsCoord2 nsCoord1) +
    EuclideanSpace.single nsCoord1
      (spatialDerivativeComponent u t x nsCoord2 nsCoord0 -
        spatialDerivativeComponent u t x nsCoord0 nsCoord2) +
    EuclideanSpace.single nsCoord2
      (spatialDerivativeComponent u t x nsCoord0 nsCoord1 -
        spatialDerivativeComponent u t x nsCoord1 nsCoord0)
end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia
