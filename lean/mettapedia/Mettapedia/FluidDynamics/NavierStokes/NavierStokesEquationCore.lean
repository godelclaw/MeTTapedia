import Mettapedia.FluidDynamics.NavierStokes.FeffermanTargetBack
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Concrete Navier-Stokes Equation Core

This module fixes the concrete time/space domains, field types, smoothness
predicates, differential operators, kinetic-energy predicates, and abstract
differential kit used by the Navier-Stokes route-audit surface.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section ConcreteEquationTarget

open scoped Laplacian ContDiff

/-- Spatial domain for the local NS target: `ℝ^3`. -/
abbrev NSSpace := EuclideanSpace ℝ (Fin 3)

/-- Time parameter for the local NS target. -/
abbrev NSTime := ℝ

/-- Vector-valued velocity fields on `ℝ × ℝ^3`. -/
abbrev NSVelocityField := NSTime → NSSpace → NSSpace

/-- Scalar-valued space-time fields on `ℝ × ℝ^3`. -/
abbrev NSScalarField := NSTime → NSSpace → ℝ

/-- Pressure fields on `ℝ × ℝ^3`. -/
abbrev NSPressureField := NSScalarField

/-- Initial velocity data on `ℝ^3`. -/
abbrev NSInitialVelocity := NSSpace → NSSpace

/-- Space-time domain `ℝ × ℝ^3` for the concrete NS theorem surface. -/
abbrev NSSpacetime := NSTime × NSSpace

/-- Uncurried space-time form of a velocity field. -/
def spaceTimeVelocityMap (u : NSVelocityField) : NSSpacetime → NSSpace :=
  fun tx => u tx.1 tx.2

/-- Uncurried space-time form of a pressure field. -/
def spaceTimePressureMap (p : NSPressureField) : NSSpacetime → ℝ :=
  fun tx => p tx.1 tx.2

/-- Concrete `C^∞` smoothness predicate for velocity fields on `ℝ × ℝ^3`. -/
def smoothSpaceTimeVelocity (u : NSVelocityField) : Prop :=
  ContDiff ℝ ∞ (spaceTimeVelocityMap u)

/-- Concrete `C^∞` smoothness predicate for pressure fields on `ℝ × ℝ^3`. -/
def smoothSpaceTimePressure (p : NSPressureField) : Prop :=
  ContDiff ℝ ∞ (spaceTimePressureMap p)

/-- Concrete `C^∞` smoothness predicate for initial velocity data on `ℝ^3`. -/
def smoothInitialVelocityData (u₀ : NSInitialVelocity) : Prop :=
  ContDiff ℝ ∞ u₀

/-- Spatial Fréchet derivative of a velocity field at fixed time. -/
def spatialFDeriv (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    NSSpace →L[ℝ] NSSpace :=
  fderiv ℝ (fun y : NSSpace => u t y) x

/-- Spatial divergence on `ℝ^3`, defined as the trace of the spatial Fréchet
derivative against the standard Euclidean basis. -/
def spatialDivergence (u : NSVelocityField) (t : NSTime) (x : NSSpace) : ℝ :=
  ∑ i : Fin 3, (spatialFDeriv u t x (EuclideanSpace.single i (1 : ℝ))) i

/-- Divergence of the initial velocity data on `ℝ^3`. -/
def initialSpatialDivergence (u₀ : NSInitialVelocity) (x : NSSpace) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ u₀ x (EuclideanSpace.single i (1 : ℝ))) i

/-- Time Fréchet derivative of a velocity field at fixed spatial point. -/
def timeFDeriv (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    ℝ →L[ℝ] NSSpace :=
  fderiv ℝ (fun s : NSTime => u s x) t

/-- Time derivative `∂ₜ u` on `ℝ × ℝ^3`, defined by applying the time Fréchet
derivative to the unit time direction. -/
def timeVelocityDerivative (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  timeFDeriv u t x (1 : ℝ)

/-- Convection term `(u · ∇)u` on `ℝ × ℝ^3`, defined by applying the spatial
Fréchet derivative to the current velocity vector. -/
def spatialConvection (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  spatialFDeriv u t x (u t x)

/-- Spatial pressure gradient on `ℝ^3`, defined by the actual gradient of the
scalar pressure field at fixed time. -/
def spatialPressureGradient (p : NSPressureField) (t : NSTime) (x : NSSpace) : NSSpace :=
  gradient (fun y : NSSpace => p t y) x

/-- Spatial Laplacian on `ℝ^3`, defined by the actual Laplacian of the fixed-time
velocity slice. -/
def spatialLaplacian (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  Δ (fun y : NSSpace => u t y) x

/-- Pointwise kinetic-energy density `|u(t,x)|^2` on `ℝ^3`. -/
def kineticEnergyDensity (u : NSVelocityField) (t : NSTime) : NSSpace → ℝ :=
  fun x => ‖u t x‖ ^ (2 : ℕ)

/-- Spatial kinetic energy of a velocity slice, measured against Lebesgue volume
on `ℝ^3`. -/
def kineticEnergyAt (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, kineticEnergyDensity u t x ∂(MeasureTheory.volume : MeasureTheory.Measure NSSpace)

/-- Pointwise initial kinetic-energy density `|u₀(x)|^2` on `ℝ^3`. -/
def initialKineticEnergyDensity (u₀ : NSInitialVelocity) : NSSpace → ℝ :=
  fun x => ‖u₀ x‖ ^ (2 : ℕ)

/-- Finite-energy admissibility for concrete initial data on `ℝ^3`. -/
def finiteInitialKineticEnergy (u₀ : NSInitialVelocity) : Prop :=
  MeasureTheory.Integrable (initialKineticEnergyDensity u₀)
    (MeasureTheory.volume : MeasureTheory.Measure NSSpace)

/-- Concrete bounded-energy predicate: the kinetic energy is integrable on every
time slice and uniformly bounded in time. -/
def boundedKineticEnergy (u : NSVelocityField) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
    MeasureTheory.Integrable (kineticEnergyDensity u t)
      (MeasureTheory.volume : MeasureTheory.Measure NSSpace) ∧
      kineticEnergyAt u t ≤ C

/-- Differential-operator kit for a concrete NS theorem statement.  The hard
analytic work still lives in these operators and regularity predicates, but the
equation itself is now explicit. -/
structure NavierStokesDifferentialKit where
  timeDerivative : NSVelocityField → NSTime → NSSpace → NSSpace
  convection : NSVelocityField → NSTime → NSSpace → NSSpace
  pressureGradient : NSPressureField → NSTime → NSSpace → NSSpace
  laplacian : NSVelocityField → NSTime → NSSpace → NSSpace
  divergence : NSVelocityField → NSTime → NSSpace → ℝ
  smoothVelocity : NSVelocityField → Prop
  smoothPressure : NSPressureField → Prop
  boundedEnergy : NSVelocityField → Prop
  smoothInitialData : NSInitialVelocity → Prop
  divergenceFreeInitialData : NSInitialVelocity → Prop

end ConcreteEquationTarget

end NavierStokes
end FluidDynamics
end Mettapedia
