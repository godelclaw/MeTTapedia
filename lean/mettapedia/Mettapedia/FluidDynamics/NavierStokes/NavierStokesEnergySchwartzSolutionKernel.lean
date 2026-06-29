import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzSolution
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeBoundedEnergyGlobal
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzDivergenceFreeData
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3PressureObstructions

/-!
# Slice-Schwartz Energy Kernel and Nonzero Finite-Mode Surface

This module factors the cancellation and dissipation conclusions of the
slice-Schwartz concrete energy identity into a reusable kernel. It also factors
the exact momentum-closure consequences that every candidate must satisfy.  The
strongest current finite-mode constructor remains explicit: a bounded nonzero
two-profile Schwartz ansatz with a genuine pointwise pressure-slice momentum
closure inhabits the nonzero slice-Schwartz solution interface.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- Reusable cancellation/dissipation kernel extracted from a concrete
slice-Schwartz Navier-Stokes solution. -/
structure SchwartzEnergyIdentityKernel
    (ν : ℝ) (u : NSVelocityField) (p : NSPressureField) where
  pressureCancellation :
    ∀ t, ∫ x, pressureEnergyPairing u p t x ∂volume = 0
  convectionCancellation :
    ∀ t, ∫ x, convectionEnergyPairing u t x ∂volume = 0
  viscousFormula : CoordinateViscousEnergyPairingFormula u
  coordinateIdentity :
    ∀ t,
      HasDerivAt (normalizedKineticEnergy u)
        (-(coordinateEnergyDissipationRate u ν t)) t
  meaningfulIdentity :
    ∀ t,
      Integrable (kineticEnergyDensity u t) ∧
        HasDerivAt (normalizedKineticEnergy u)
          (-(coordinateEnergyDissipationRate u ν t)) t

/-- Reusable momentum-closure kernel extracted from a concrete slice-Schwartz
Navier-Stokes solution.  It records the literal PDE, incompressibility, and the
pressure-residual compatibility condition that later candidate generators must
pass before searching for pressure slices. -/
structure SchwartzMomentumClosureKernel
    (ν : ℝ) (u : NSVelocityField) (p : NSPressureField) where
  smoothPressure : smoothSpaceTimePressure p
  momentumEquation :
    ∀ t x,
      timeVelocityDerivative u t x + spatialConvection u t x +
          spatialPressureGradient p t x =
        ν • spatialLaplacian u t x
  incompressible : ∀ t x, spatialDivergence u t x = 0
  pressureResidual_eq_gradient :
    pressureGradientVelocityField p = momentumPressureResidual ν u
  pressureResidual_vorticity_zero :
    ∀ t x, spatialVorticity (momentumPressureResidual ν u) t x = 0

/-- Combined reusable kernel for the slice-Schwartz concrete solution
interface: energy identity plus pressure/momentum closure. -/
structure SchwartzConcreteSolutionKernel
    (ν : ℝ) (u : NSVelocityField) (p : NSPressureField) where
  energy : SchwartzEnergyIdentityKernel ν u p
  momentum : SchwartzMomentumClosureKernel ν u p

namespace SchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : SchwartzConcreteNavierStokesSolution ν)

/-- The reusable energy kernel carried by any slice-Schwartz concrete solution. -/
def energyIdentityKernel :
    SchwartzEnergyIdentityKernel ν S.velocity S.pressure where
  pressureCancellation := S.pressureEnergyCancellation
  convectionCancellation := S.convectionEnergyCancellation
  viscousFormula := S.coordinateViscousEnergyPairingFormula
  coordinateIdentity := S.coordinateEnergyDissipationIdentity
  meaningfulIdentity := S.meaningfulCoordinateEnergyDissipationIdentity

/-- The reusable momentum-closure kernel carried by any slice-Schwartz
concrete solution. -/
def momentumClosureKernel :
    SchwartzMomentumClosureKernel ν S.velocity S.pressure where
  smoothPressure := S.smooth_pressure
  momentumEquation := S.momentumEquation_explicit
  incompressible := S.spatialDivergence_zero
  pressureResidual_eq_gradient :=
    pressureGradientVelocityField_eq_momentumPressureResidual_of_momentumEquation
      S.momentumEquation_explicit
  pressureResidual_vorticity_zero :=
    spatialVorticity_momentumPressureResidual_of_momentumEquation
      S.smooth_pressure S.momentumEquation_explicit

/-- The full reusable kernel carried by any slice-Schwartz concrete solution. -/
def concreteSolutionKernel :
    SchwartzConcreteSolutionKernel ν S.velocity S.pressure where
  energy := S.energyIdentityKernel
  momentum := S.momentumClosureKernel

end SchwartzConcreteNavierStokesSolution

/-- Nonzero refinement of the slice-Schwartz concrete solution interface. -/
structure NonzeroSchwartzConcreteNavierStokesSolution (ν : ℝ)
    extends SchwartzConcreteNavierStokesSolution ν where
  nonzero_velocity : ∃ t x, velocity t x ≠ 0

namespace NonzeroSchwartzConcreteNavierStokesSolution

variable {ν : ℝ} (S : NonzeroSchwartzConcreteNavierStokesSolution ν)

/-- Nonzero solutions inherit the same reusable energy kernel. -/
def energyIdentityKernel :
    SchwartzEnergyIdentityKernel ν S.velocity S.pressure :=
  S.toSchwartzConcreteNavierStokesSolution.energyIdentityKernel

/-- Nonzero solutions inherit the same reusable momentum-closure kernel. -/
def momentumClosureKernel :
    SchwartzMomentumClosureKernel ν S.velocity S.pressure :=
  S.toSchwartzConcreteNavierStokesSolution.momentumClosureKernel

/-- Nonzero solutions inherit the combined reusable solution kernel. -/
def concreteSolutionKernel :
    SchwartzConcreteSolutionKernel ν S.velocity S.pressure :=
  S.toSchwartzConcreteNavierStokesSolution.concreteSolutionKernel

/-- Compact nonzero packet: a witness of nonzero velocity plus the full energy
kernel. -/
theorem nonzero_and_energyIdentityKernel :
    (∃ t x, S.velocity t x ≠ 0) ∧
      SchwartzEnergyIdentityKernel ν S.velocity S.pressure :=
  ⟨S.nonzero_velocity, S.energyIdentityKernel⟩

/-- Compact nonzero packet with both the energy identity and the momentum
closure kernels. -/
theorem nonzero_and_concreteSolutionKernel :
    (∃ t x, S.velocity t x ≠ 0) ∧
      SchwartzConcreteSolutionKernel ν S.velocity S.pressure :=
  ⟨S.nonzero_velocity, S.concreteSolutionKernel⟩

/-- Reusable nonzero energy/momentum packet.  Any nonzero slice-Schwartz
concrete solution carries the nonzero witness, both energy cancellations, the
viscous identity, the meaningful energy identity, the literal momentum equation,
incompressibility, and the pressure-residual curl gate. -/
theorem nonzero_energyMomentumCanary_packet :
    (∃ t x, S.velocity t x ≠ 0) ∧
      SchwartzEnergyIdentityKernel ν S.velocity S.pressure ∧
      SchwartzMomentumClosureKernel ν S.velocity S.pressure ∧
      SchwartzConcreteSolutionKernel ν S.velocity S.pressure ∧
      (∀ t, ∫ x, pressureEnergyPairing S.velocity S.pressure t x ∂volume = 0) ∧
      (∀ t, ∫ x, convectionEnergyPairing S.velocity t x ∂volume = 0) ∧
      CoordinateViscousEnergyPairingFormula S.velocity ∧
      (∀ t,
        HasDerivAt (normalizedKineticEnergy S.velocity)
          (-(coordinateEnergyDissipationRate S.velocity ν t)) t) ∧
      (∀ t,
        Integrable (kineticEnergyDensity S.velocity t) ∧
          HasDerivAt (normalizedKineticEnergy S.velocity)
            (-(coordinateEnergyDissipationRate S.velocity ν t)) t) ∧
      (∀ t x,
        timeVelocityDerivative S.velocity t x + spatialConvection S.velocity t x +
            spatialPressureGradient S.pressure t x =
          ν • spatialLaplacian S.velocity t x) ∧
      (∀ t x, spatialDivergence S.velocity t x = 0) ∧
      pressureGradientVelocityField S.pressure = momentumPressureResidual ν S.velocity ∧
      (∀ t x, spatialVorticity (momentumPressureResidual ν S.velocity) t x = 0) := by
  let K := S.concreteSolutionKernel
  exact
    ⟨S.nonzero_velocity,
      K.energy,
      K.momentum,
      K,
      K.energy.pressureCancellation,
      K.energy.convectionCancellation,
      K.energy.viscousFormula,
      K.energy.coordinateIdentity,
      K.energy.meaningfulIdentity,
      K.momentum.momentumEquation,
      K.momentum.incompressible,
      K.momentum.pressureResidual_eq_gradient,
      K.momentum.pressureResidual_vorticity_zero⟩

end NonzeroSchwartzConcreteNavierStokesSolution

/-- A bounded two-profile Schwartz ansatz with Schwartz pressure slices and the
literal pointwise momentum equation inhabits the slice-Schwartz concrete
solution interface. The theorem keeps the pressure-slice momentum closure as a
real analytic input rather than hiding it in the constructor. -/
def twoModeSchwartzPressureSlice_schwartzConcreteSolution_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hp : smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    SchwartzConcreteNavierStokesSolution ν where
  velocity := twoModeSchwartzVelocity a b f g
  pressure := fun s : NSTime => fun y : NSSpace => q s y
  smooth_velocity := smoothSpaceTimeVelocity_twoModeSchwartzVelocity ha hb f g
  smooth_pressure := hp
  momentum_equation :=
    satisfiesMomentumEquation_mkFullyConcreteNavierStokesSurface_iff.mpr heq
  incompressible :=
    isIncompressible_mkFullyConcreteNavierStokesSurface_iff.mpr
      (spatialDivergence_twoModeSchwartzVelocity_zero a b f g hfDiv hgDiv)
  bounded_energy :=
    boundedKineticEnergy_twoModeSchwartzVelocity_of_abs_le
      a b f g A B haBound hbBound
  velocitySlice := fun t => a t • f + b t • g
  velocitySlice_eq := by
    intro t x
    rfl
  pressureSlice := q
  pressureSlice_eq := by
    intro t x
    rfl
  energy_derivative :=
    EnergyDerivativeFormula_of_add_scalar_smul_schwartz
      a (deriv a) b (deriv b) f g
      (hasDerivAt_deriv_of_contDiff ha)
      (hasDerivAt_deriv_of_contDiff hb)

/-- Nonzero version of the pressure-slice finite-mode constructor. The
nonzero witness is explicit in the returned structure, so zero-amplitude or
cancelling two-mode data cannot satisfy this interface by accident. -/
def twoModeSchwartzPressureSlice_nonzeroSchwartzConcreteSolution_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hp : smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hnonzero : ∃ t x, twoModeSchwartzVelocity a b f g t x ≠ 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    NonzeroSchwartzConcreteNavierStokesSolution ν where
  toSchwartzConcreteNavierStokesSolution :=
    twoModeSchwartzPressureSlice_schwartzConcreteSolution_of_momentumEquation
      ha hb f g A B q hp haBound hbBound hfDiv hgDiv heq
  nonzero_velocity := hnonzero

/-- Expanded-closure version of the nonzero constructor. This is the generator
entrypoint for finite-mode searches: the closure is written in profile-level
terms and then compiled to the literal concrete momentum equation. -/
def twoModeSchwartzPressureSlice_nonzeroSchwartzConcreteSolution_of_explicitClosure
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hp : smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hnonzero : ∃ t x, twoModeSchwartzVelocity a b f g t x ≠ 0)
    (hclosure : ∀ t x,
      deriv a t • f x + deriv b t • g x +
            ((a t ^ (2 : ℕ)) •
                spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              (a t * b t) •
                spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
              (a t * b t) •
                spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
              (b t ^ (2 : ℕ)) •
                spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x) +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) •
          (a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            b t • spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    NonzeroSchwartzConcreteNavierStokesSolution ν :=
  twoModeSchwartzPressureSlice_nonzeroSchwartzConcreteSolution_of_momentumEquation
    ha hb f g A B q hp haBound hbBound hfDiv hgDiv hnonzero
    (momentumEquation_twoModeSchwartzVelocity_schwartzPressureSlice_of_explicitClosure
      ha hb ν f g q hclosure)

/-- Constant-one specialization: if two divergence-free Schwartz profiles
have a nonzero sum and their expanded pressure-slice closure holds, the
finite-mode class yields a nonzero slice-Schwartz concrete solution. -/
def oneOneTwoModeSchwartzPressureSlice_nonzeroSchwartzConcreteSolution_of_explicitClosure
    (f g : NSSchwartzInitialVelocity)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hp : smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    NonzeroSchwartzConcreteNavierStokesSolution ν :=
  twoModeSchwartzPressureSlice_nonzeroSchwartzConcreteSolution_of_explicitClosure
    (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
    contDiff_const contDiff_const f g 1 1 q hp
    (by intro t; simp) (by intro t; simp) hfDiv hgDiv
    (oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero f g hfg)
    (by
      intro t x
      simpa using hclosure t x)

/-- Energy-kernel consequence for the nonzero finite-mode constructor. -/
theorem
    twoModeSchwartzPressureSlice_nonzero_energyIdentityKernel_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hp : smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hnonzero : ∃ t x, twoModeSchwartzVelocity a b f g t x ≠ 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    (∃ t x, twoModeSchwartzVelocity a b f g t x ≠ 0) ∧
      SchwartzEnergyIdentityKernel ν
        (twoModeSchwartzVelocity a b f g)
        (fun s : NSTime => fun y : NSSpace => q s y) := by
  let S :=
    twoModeSchwartzPressureSlice_nonzeroSchwartzConcreteSolution_of_momentumEquation
      ha hb f g A B q hp haBound hbBound hfDiv hgDiv hnonzero heq
  exact S.nonzero_and_energyIdentityKernel

/-- One-profile stationary inviscid constructor.  A nonzero divergence-free
Schwartz initial velocity, together with a Schwartz pressure slice whose
spatial gradient balances the stationary convection term, gives a nonzero
slice-Schwartz concrete solution at viscosity `0`.

This is the exact surface needed for stationary localized Euler-style canary
searches.  The pressure-closure equation is still explicit; the constructor
does not hide it or claim positive-viscosity Navier-Stokes regularity. -/
def stationaryInviscidSchwartzPressureSlice_nonzeroSchwartzConcreteSolution
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (q : 𝓢(NSSpace, ℝ))
    (hnonzero : ∃ x : NSSpace, u₀.1 x ≠ 0)
    (hstationary : ∀ t x,
      spatialConvection (timeIndependentVelocity (u₀.1 : NSInitialVelocity)) t x +
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x =
        0) :
    NonzeroSchwartzConcreteNavierStokesSolution 0 where
  toSchwartzConcreteNavierStokesSolution := {
    velocity := timeIndependentVelocity (u₀.1 : NSInitialVelocity)
    pressure := fun _ : NSTime => fun y : NSSpace => q y
    smooth_velocity :=
      smoothSpaceTimeVelocity_timeIndependentVelocity
        (smoothInitialVelocityData_of_schwartzDivergenceFreeInitialVelocity u₀)
    smooth_pressure := by
      simpa using
        smoothSpaceTimePressure_scalar_smul_schwartzPressure
          (ρ := fun _ : NSTime => (1 : ℝ)) contDiff_const q
    momentum_equation :=
      satisfiesMomentumEquation_mkFullyConcreteNavierStokesSurface_iff.mpr
        (by
          intro t x
          rw [timeVelocityDerivative_timeIndependentVelocity]
          simpa using hstationary t x)
    incompressible :=
      isIncompressible_mkFullyConcreteNavierStokesSurface_iff.mpr
        (by
          intro t x
          rw [spatialDivergence_timeIndependentVelocity]
          exact u₀.2 x)
    bounded_energy := by
      have hbounded :
          boundedKineticEnergy
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (1 : ℝ)) s • u₀.1 y +
                (fun _ : NSTime => (0 : ℝ)) s • (0 : NSSchwartzInitialVelocity) y) :=
        boundedKineticEnergy_of_add_scalar_smul_schwartz_of_abs_le
          (fun _ : NSTime => (1 : ℝ)) (fun _ : NSTime => (0 : ℝ))
          u₀.1 (0 : NSSchwartzInitialVelocity) 1 0
          (by intro t; simp)
          (by intro t; simp)
      change
        boundedKineticEnergy
          (fun _ : NSTime => fun y : NSSpace => (u₀.1 : NSInitialVelocity) y)
      simpa using hbounded
    velocitySlice := fun _ : NSTime => u₀.1
    velocitySlice_eq := by
      intro t x
      rfl
    pressureSlice := fun _ : NSTime => q
    pressureSlice_eq := by
      intro t x
      rfl
    energy_derivative := by
      have hderiv :
          EnergyDerivativeFormula
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (1 : ℝ)) s • u₀.1 y +
                (fun _ : NSTime => (0 : ℝ)) s • (0 : NSSchwartzInitialVelocity) y) :=
        EnergyDerivativeFormula_of_add_scalar_smul_schwartz
          (fun _ : NSTime => (1 : ℝ)) (fun _ : NSTime => (0 : ℝ))
          (fun _ : NSTime => (0 : ℝ)) (fun _ : NSTime => (0 : ℝ))
          u₀.1 (0 : NSSchwartzInitialVelocity)
          (by intro t; simpa using hasDerivAt_const t (1 : ℝ))
          (by intro t; simpa using hasDerivAt_const t (0 : ℝ))
      change
        EnergyDerivativeFormula
          (fun _ : NSTime => fun y : NSSpace => (u₀.1 : NSInitialVelocity) y)
      simpa using hderiv
  }
  nonzero_velocity := by
    rcases hnonzero with ⟨x, hx⟩
    exact ⟨0, x, by simpa [timeIndependentVelocity] using hx⟩

/-- Kernel packet for the stationary inviscid one-profile constructor. -/
theorem stationaryInviscidSchwartzPressureSlice_nonzero_concreteSolutionKernel
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (q : 𝓢(NSSpace, ℝ))
    (hnonzero : ∃ x : NSSpace, u₀.1 x ≠ 0)
    (hstationary : ∀ t x,
      spatialConvection (timeIndependentVelocity (u₀.1 : NSInitialVelocity)) t x +
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x =
        0) :
    (∃ t x, timeIndependentVelocity (u₀.1 : NSInitialVelocity) t x ≠ 0) ∧
      SchwartzConcreteSolutionKernel 0
        (timeIndependentVelocity (u₀.1 : NSInitialVelocity))
        (fun _ : NSTime => fun y : NSSpace => q y) := by
  let S :=
    stationaryInviscidSchwartzPressureSlice_nonzeroSchwartzConcreteSolution
      u₀ q hnonzero hstationary
  exact S.nonzero_and_concreteSolutionKernel

/-- Explicit energy-identity canary packet for the stationary inviscid
one-profile constructor.  The returned witness is a genuine nonzero
`NonzeroSchwartzConcreteNavierStokesSolution` at viscosity `0`, with its
velocity and pressure fixed definitionally to the supplied stationary data,
and with the universal slice-Schwartz cancellations and zero-viscosity energy
identity exposed directly rather than hidden behind the kernel record. -/
theorem stationaryInviscidSchwartzPressureSlice_nonzero_energyIdentityCanary_packet
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity)
    (q : 𝓢(NSSpace, ℝ))
    (hnonzero : ∃ x : NSSpace, u₀.1 x ≠ 0)
    (hstationary : ∀ t x,
      spatialConvection (timeIndependentVelocity (u₀.1 : NSInitialVelocity)) t x +
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x =
        0) :
    ∃ S : NonzeroSchwartzConcreteNavierStokesSolution 0,
      S.velocity = timeIndependentVelocity (u₀.1 : NSInitialVelocity) ∧
        S.pressure = (fun _ : NSTime => fun y : NSSpace => q y) ∧
        (∃ t x, S.velocity t x ≠ 0) ∧
        SchwartzEnergyIdentityKernel 0 S.velocity S.pressure ∧
        SchwartzConcreteSolutionKernel 0 S.velocity S.pressure ∧
        (∀ t, ∫ x, pressureEnergyPairing S.velocity S.pressure t x ∂volume = 0) ∧
        (∀ t, ∫ x, convectionEnergyPairing S.velocity t x ∂volume = 0) ∧
        CoordinateViscousEnergyPairingFormula S.velocity ∧
        (∀ t, HasDerivAt (normalizedKineticEnergy S.velocity) 0 t) ∧
        (∀ t,
          Integrable (kineticEnergyDensity S.velocity t) ∧
            HasDerivAt (normalizedKineticEnergy S.velocity) 0 t) := by
  let S :=
    stationaryInviscidSchwartzPressureSlice_nonzeroSchwartzConcreteSolution
      u₀ q hnonzero hstationary
  refine ⟨S, rfl, rfl, S.nonzero_velocity, S.energyIdentityKernel,
    S.concreteSolutionKernel, S.pressureEnergyCancellation,
    S.convectionEnergyCancellation, S.coordinateViscousEnergyPairingFormula,
    ?_, ?_⟩
  · intro t
    simpa [coordinateEnergyDissipationRate] using
      S.coordinateEnergyDissipationIdentity t
  · intro t
    rcases S.meaningfulCoordinateEnergyDissipationIdentity t with ⟨hInt, hderiv⟩
    exact ⟨hInt, by simpa [coordinateEnergyDissipationRate] using hderiv⟩

end NavierStokes
end FluidDynamics
end Mettapedia
