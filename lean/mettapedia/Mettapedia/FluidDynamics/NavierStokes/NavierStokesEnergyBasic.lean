import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Basic
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3LocalOperators
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Smoothness
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3FirstOrder
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3PressureObstructions
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Laplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Momentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Vorticity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportProfiles
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportDerivatives
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportLaplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportMomentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportVorticity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3VorticityNorms
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Navier-Stokes Energy: Basic

Basic energy, enstrophy, dissipation, and pressure-pairing definitions on the concrete R^3 surface.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

abbrev NSStdBasisIndex := Fin (Module.finrank ℝ NSSpace)

/-- Canonical orthonormal basis of the concrete NS space `ℝ^3`. -/
abbrev nsStdBasis : OrthonormalBasis NSStdBasisIndex ℝ NSSpace :=
  stdOrthonormalBasis ℝ NSSpace

/-- Spatial enstrophy density: squared norm of the spatial velocity derivative.
This is the concrete dissipation density used in the energy identity. -/
def enstrophyDensity (u : NSVelocityField) (t : NSTime) : NSSpace → ℝ :=
  fun x => ‖spatialFDeriv u t x‖ ^ (2 : ℕ)

/-- Total enstrophy of a time slice. -/
def enstrophyAt (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, enstrophyDensity u t x ∂volume

/-- Coordinatewise enstrophy density using the standard orthonormal basis of
`ℝ^3`. This is the dissipation density that matches the Laplacian
integration-by-parts identity on Schwartz slices. -/
def coordinateEnstrophyDensity (u : NSVelocityField) (t : NSTime) : NSSpace → ℝ :=
  fun x =>
    ∑ i : NSStdBasisIndex,
      ‖spatialFDeriv u t x (nsStdBasis i)‖ ^ (2 : ℕ)

/-- Total coordinatewise enstrophy of a time slice. -/
def coordinateEnstrophyAt (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, coordinateEnstrophyDensity u t x ∂volume

/-- Viscous energy dissipation rate `ν ∫ ‖∇u‖²`. -/
def energyDissipationRate (u : NSVelocityField) (ν : ℝ) (t : NSTime) : ℝ :=
  ν * enstrophyAt u t

/-- Corrected viscous energy dissipation rate
`ν ∫ Σᵢ |∂ᵢu|²`. This is the concrete rate matching the Laplacian
integration-by-parts identity on `ℝ^3`. -/
def coordinateEnergyDissipationRate (u : NSVelocityField) (ν : ℝ) (t : NSTime) : ℝ :=
  ν * coordinateEnstrophyAt u t

/-- The conventional `1 / 2`-normalized kinetic energy. -/
def normalizedKineticEnergy (u : NSVelocityField) (t : NSTime) : ℝ :=
  (1 / 2 : ℝ) * kineticEnergyAt u t

/-- Kinetic-energy density is pointwise nonnegative. -/
theorem kineticEnergyDensity_nonneg
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    0 ≤ kineticEnergyDensity u t x := by
  simp [kineticEnergyDensity]

/-- The unguarded spatial kinetic-energy integral is nonnegative.  This uses
mathlib's convention that the Bochner integral of a nonintegrable nonnegative
function is still `0`, so finite-energy statements still need an explicit
integrability guard. -/
theorem kineticEnergyAt_nonneg
    (u : NSVelocityField) (t : NSTime) :
    0 ≤ kineticEnergyAt u t := by
  rw [kineticEnergyAt]
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => kineticEnergyDensity_nonneg u t x)

/-- Normalized kinetic energy is nonnegative. -/
theorem normalizedKineticEnergy_nonneg
    (u : NSVelocityField) (t : NSTime) :
    0 ≤ normalizedKineticEnergy u t := by
  exact mul_nonneg (by norm_num) (kineticEnergyAt_nonneg u t)

/-- Enstrophy density is pointwise nonnegative. -/
theorem enstrophyDensity_nonneg
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    0 ≤ enstrophyDensity u t x := by
  simp [enstrophyDensity]

/-- Coordinatewise enstrophy density is pointwise nonnegative. -/
theorem coordinateEnstrophyDensity_nonneg
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    0 ≤ coordinateEnstrophyDensity u t x := by
  unfold coordinateEnstrophyDensity
  exact Finset.sum_nonneg fun i _ => by positivity

/-- Total enstrophy is nonnegative on the unguarded integral surface. -/
theorem enstrophyAt_nonneg
    (u : NSVelocityField) (t : NSTime) :
    0 ≤ enstrophyAt u t := by
  rw [enstrophyAt]
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => enstrophyDensity_nonneg u t x)

/-- Total coordinatewise enstrophy is nonnegative on the unguarded integral
surface. -/
theorem coordinateEnstrophyAt_nonneg
    (u : NSVelocityField) (t : NSTime) :
    0 ≤ coordinateEnstrophyAt u t := by
  rw [coordinateEnstrophyAt]
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => coordinateEnstrophyDensity_nonneg u t x)

/-- Nonnegative viscosity gives nonnegative conventional dissipation rate. -/
theorem energyDissipationRate_nonneg
    (u : NSVelocityField) {ν : ℝ} (hν : 0 ≤ ν) (t : NSTime) :
    0 ≤ energyDissipationRate u ν t := by
  exact mul_nonneg hν (enstrophyAt_nonneg u t)

/-- Nonnegative viscosity gives nonnegative corrected coordinatewise
dissipation rate. -/
theorem coordinateEnergyDissipationRate_nonneg
    (u : NSVelocityField) {ν : ℝ} (hν : 0 ≤ ν) (t : NSTime) :
    0 ≤ coordinateEnergyDissipationRate u ν t := by
  exact mul_nonneg hν (coordinateEnstrophyAt_nonneg u t)

/-- The corrected energy identity has a nonpositive right-hand side for
nonnegative viscosity. -/
theorem neg_coordinateEnergyDissipationRate_nonpos
    (u : NSVelocityField) {ν : ℝ} (hν : 0 ≤ ν) (t : NSTime) :
    -(coordinateEnergyDissipationRate u ν t) ≤ 0 := by
  exact neg_nonpos.mpr (coordinateEnergyDissipationRate_nonneg u hν t)

/-- The space integrand `u · ∂ₜu` appearing in the energy identity. -/
def timeEnergyPairing (u : NSVelocityField) (t : NSTime) : NSSpace → ℝ :=
  fun x => ⟪u t x, timeVelocityDerivative u t x⟫

/-- The space integrand `u · (u · ∇)u` from the nonlinear transport term. -/
def convectionEnergyPairing (u : NSVelocityField) (t : NSTime) : NSSpace → ℝ :=
  fun x => ⟪u t x, spatialConvection u t x⟫

/-- The space integrand `u · ∇p` from the pressure term. -/
def pressureEnergyPairing
    (u : NSVelocityField) (p : NSPressureField) (t : NSTime) : NSSpace → ℝ :=
  fun x => ⟪u t x, spatialPressureGradient p t x⟫

/-- The pressure energy pairing is additive in the pressure field whenever both
spatial pressure slices are differentiable at every point of the time slice. -/
theorem pressureEnergyPairing_add
    (u : NSVelocityField) {p q : NSPressureField} (t : NSTime)
    (hp : ∀ x, DifferentiableAt ℝ (fun y : NSSpace => p t y) x)
    (hq : ∀ x, DifferentiableAt ℝ (fun y : NSSpace => q t y) x) :
    pressureEnergyPairing u (p + q) t =
      fun x : NSSpace => pressureEnergyPairing u p t x + pressureEnergyPairing u q t x := by
  funext x
  rw [pressureEnergyPairing, pressureEnergyPairing, pressureEnergyPairing]
  rw [spatialPressureGradient_add (p := p) (q := q) (hp x) (hq x)]
  simp [inner_add_right]

/-- The pressure energy pairing against zero pressure vanishes identically. -/
theorem pressureEnergyPairing_zero_right
    (u : NSVelocityField) (t : NSTime) :
    pressureEnergyPairing u (0 : NSPressureField) t = fun _ : NSSpace => 0 := by
  funext x
  simp [pressureEnergyPairing, spatialPressureGradient_zero]

/-- The pressure energy pairing against a time-only pressure gauge vanishes
identically. -/
theorem pressureEnergyPairing_timeOnly
    (u : NSVelocityField) (π : NSTime → ℝ) (t : NSTime) :
    pressureEnergyPairing u (fun s : NSTime => fun _ : NSSpace => π s) t =
      fun _ : NSSpace => 0 := by
  funext x
  simp [pressureEnergyPairing, spatialPressureGradient_timeOnly]

/-- Against the coordinate-linear pressure field `p(t,x) = c * x₀`, the
pressure energy pairing is exactly `c` times the `x₀`-component of the
velocity. -/
theorem pressureEnergyPairing_coord0Linear
    (u : NSVelocityField) (c : ℝ) (t : NSTime) :
    pressureEnergyPairing
        u (fun _ : NSTime => fun y : NSSpace => c * y nsCoord0) t =
      fun x : NSSpace => c * (u t x) nsCoord0 := by
  funext x
  rw [pressureEnergyPairing, spatialPressureGradient_coord0Linear]
  simp [EuclideanSpace.inner_single_right, nsCoord0]

/-- The pressure energy pairing against a linear pressure field
`p(t,x) = ⟪c, x⟫` is exactly `u · c`. -/
theorem pressureEnergyPairing_linear
    (u : NSVelocityField) (c : NSSpace) (t : NSTime) :
    pressureEnergyPairing u (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t =
      fun x : NSSpace => ⟪u t x, c⟫ := by
  funext x
  rw [pressureEnergyPairing]
  have hgrad :
      spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t x = c := by
    unfold spatialPressureGradient
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    refine (((InnerProductSpace.toDual ℝ NSSpace) c)).hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards with y
    simp [InnerProductSpace.toDual_apply_apply]
  rw [hgrad]

/-- The pressure energy pairing against an affine-in-space pressure gauge
`p(t,x) = ⟪c(t), x⟫ + π(t)` depends only on the linear part, hence is exactly
`u · c(t)`. -/
theorem pressureEnergyPairing_affine
    (u : NSVelocityField) (c : NSTime → NSSpace) (π : NSTime → ℝ) (t : NSTime) :
    pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) t =
      fun x : NSSpace => ⟪u t x, c t⟫ := by
  funext x
  rw [pressureEnergyPairing]
  have hgrad :
      spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) t x = c t := by
    unfold spatialPressureGradient
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    refine
      (((((InnerProductSpace.toDual ℝ NSSpace) (c t))).hasFDerivAt).add_const (π t)).congr_of_eventuallyEq ?_
    filter_upwards with y
    simp [InnerProductSpace.toDual_apply_apply]
  rw [hgrad]
end NavierStokes
end FluidDynamics
end Mettapedia
