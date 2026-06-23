import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzDissipationViscous
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzDissipationConvection
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzDissipationBounded

/-!
# Navier-Stokes Energy: Meaningful Schwartz Core Identity

Semantic layer split from `NavierStokesEnergyMeaningfulSchwartz`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- The repaired bounded-energy guarded coordinate energy identity holds for a
two-profile Schwartz superposition once the scalar coefficients are uniformly
bounded and the concrete PDE hypotheses are supplied. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (p : NSPressureField) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hintegrable :
      EnergyPairingIntegrable (fun s y => a s • f y + b s • g y) p)
    (hboundary :
      ∀ t,
        ∫ x, pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t x ∂volume = 0)
    (hnonlinear :
      ∀ t,
        ∫ x, convectionEnergyPairing (fun s y => a s • f y + b s • g y) t x ∂volume = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_boundedKineticEnergy
      (u := fun s y => a s • f y + b s • g y)
      (p := p)
      (ν := ν)
      (boundedKineticEnergy_of_add_scalar_smul_schwartz_of_abs_le a b f g A B haBound hbBound)
      (EnergyDerivativeFormula_of_add_scalar_smul_schwartz a a' b b' f g ha hb)
      heq
      hintegrable
      (CoordinateViscousEnergyPairingFormula_of_add_scalar_smul_schwartz a b f g)
      hboundary
      hnonlinear

/-- The repaired bounded-energy coordinate energy identity for a two-profile
Schwartz superposition no longer needs a separate nonlinear-cancellation
hypothesis once both profiles are divergence-free in the standard coordinates
of `ℝ^3`. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (p : NSPressureField) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hintegrable :
      EnergyPairingIntegrable (fun s y => a s • f y + b s • g y) p)
    (hboundary :
      ∀ t,
        ∫ x, pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t x ∂volume = 0)
    (hfdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i = 0)
    (hgdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} g x) i = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le
      a a' b b' f g A B p ν haBound hbBound ha hb heq hintegrable hboundary
      (integral_convectionEnergyPairing_of_add_scalar_smul_schwartz_of_divergenceFree
        a b f g hfdiv hgdiv)

/-- The two-profile Schwartz energy theorem needs only pressure-pairing
integrability as an extra hypothesis: the viscous and convection pairings are
automatically integrable on this concrete class. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree_of_pressureIntegrable
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (p : NSPressureField) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hpressureIntegrable :
      ∀ t,
        Integrable (pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t))
    (hboundary :
      ∀ t,
        ∫ x, pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t x ∂volume = 0)
    (hfdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i = 0)
    (hgdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} g x) i = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  have hintegrable :
      EnergyPairingIntegrable (fun s y => a s • f y + b s • g y) p := by
    intro t
    refine ⟨?_, ?_, hpressureIntegrable t⟩
    · exact
        integrable_laplacianEnergyPairing_of_schwartzSlice
          (u := fun s y => a s • f y + b s • g y)
          (t := t)
          (f := (a t) • f + (b t) • g)
          (hslice := by intro x; rfl)
    · exact
        integrable_convectionEnergyPairing_of_schwartzSlice
          (u := fun s y => a s • f y + b s • g y)
          (t := t)
          (f := (a t) • f + (b t) • g)
          (hslice := by intro x; rfl)
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree
      a a' b b' f g A B p ν haBound hbBound ha hb heq hintegrable hboundary hfdiv hgdiv

/-- The two-profile Schwartz energy theorem only needs the combined velocity
field to be divergence-free on each time slice; it does not require separate
profilewise divergence hypotheses. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (p : NSPressureField) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hpressureIntegrable :
      ∀ t,
        Integrable (pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t))
    (hboundary :
      ∀ t,
        ∫ x, pressureEnergyPairing (fun s y => a s • f y + b s • g y) p t x ∂volume = 0)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  have hintegrable :
      EnergyPairingIntegrable (fun s y => a s • f y + b s • g y) p := by
    intro t
    refine ⟨?_, ?_, hpressureIntegrable t⟩
    · exact
        integrable_laplacianEnergyPairing_of_schwartzSlice
          (u := fun s y => a s • f y + b s • g y)
          (t := t)
          (f := (a t) • f + (b t) • g)
          (hslice := by intro x; rfl)
    · exact
        integrable_convectionEnergyPairing_of_schwartzSlice
          (u := fun s y => a s • f y + b s • g y)
          (t := t)
          (f := (a t) • f + (b t) • g)
          (hslice := by intro x; rfl)
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le
      a a' b b' f g A B p ν haBound hbBound ha hb heq hintegrable hboundary
      (integral_convectionEnergyPairing_of_add_scalar_smul_schwartz_of_spatialDivergence_zero
        a b f g hdiv)

end NavierStokes
end FluidDynamics
end Mettapedia
