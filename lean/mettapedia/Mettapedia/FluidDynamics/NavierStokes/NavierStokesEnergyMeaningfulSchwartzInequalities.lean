import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyMeaningfulSchwartzAffineScalar

/-!
# Navier-Stokes Energy: Meaningful Schwartz Energy Inequalities

Semantic layer split from `NavierStokesEnergyMeaningfulSchwartz`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- Energy-inequality form for the concrete bounded two-profile Schwartz class
with affine plus localized Schwartz pressure: under nonnegative viscosity, the
normalized kinetic energy is antitone in time. -/
theorem normalizedKineticEnergy_antitone_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient
            ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
              fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    Antitone (normalizedKineticEnergy (fun s y => a s • f y + b s • g y)) := by
  refine
    antitone_of_hasDerivAt_nonpos
      (f' := fun t =>
        -(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t))
      ?_ ?_
  · intro t
    exact
      (meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
        a a' b b' f g A B c π ρ q ν haBound hbBound ha hb heq hdiv t).2
  · intro t
    exact
      neg_coordinateEnergyDissipationRate_nonpos
        (fun s y => a s • f y + b s • g y) hν t

/-- Two-time energy inequality for the concrete bounded two-profile Schwartz
class with affine plus localized Schwartz pressure. -/
theorem normalizedKineticEnergy_between_zero_and_initial_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient
            ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
              fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    0 ≤ normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₁ ∧
      normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₁ ≤
        normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₀ := by
  refine ⟨normalizedKineticEnergy_nonneg _ t₁, ?_⟩
  exact
    (normalizedKineticEnergy_antitone_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      a a' b b' f g A B c π ρ q hν haBound hbBound ha hb heq hdiv) ht

/-- Standard kinetic-energy two-time bound for the concrete bounded
two-profile Schwartz class with affine plus localized Schwartz pressure. -/
theorem kineticEnergyAt_between_zero_and_initial_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient
            ((fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) +
              fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0)
    {t₀ t₁ : NSTime} (ht : t₀ ≤ t₁) :
    0 ≤ kineticEnergyAt (fun s y => a s • f y + b s • g y) t₁ ∧
      kineticEnergyAt (fun s y => a s • f y + b s • g y) t₁ ≤
        kineticEnergyAt (fun s y => a s • f y + b s • g y) t₀ := by
  refine ⟨kineticEnergyAt_nonneg _ t₁, ?_⟩
  have hnorm :
      normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₁ ≤
        normalizedKineticEnergy (fun s y => a s • f y + b s • g y) t₀ :=
    (normalizedKineticEnergy_antitone_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
      a a' b b' f g A B c π ρ q hν haBound hbBound ha hb heq hdiv) ht
  unfold normalizedKineticEnergy at hnorm
  nlinarith

end NavierStokes
end FluidDynamics
end Mettapedia
