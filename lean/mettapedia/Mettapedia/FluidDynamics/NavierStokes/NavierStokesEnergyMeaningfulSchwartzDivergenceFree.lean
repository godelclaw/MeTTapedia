import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyMeaningfulSchwartzCore

/-!
# Navier-Stokes Energy: Meaningful Schwartz Divergence-Free Shortcuts

Semantic layer split from `NavierStokesEnergyMeaningfulSchwartz`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- The two-profile Schwartz energy theorem closes completely on the concrete
zero-pressure lane once the profiles are divergence-free. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree_zeroPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (0 : NSPressureField) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
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
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree_of_pressureIntegrable
      a a' b b' f g A B (0 : NSPressureField) ν haBound hbBound ha hb heq
      (by
        intro t
        rw [pressureEnergyPairing_zero_right]
        exact integrable_zero NSSpace ℝ (volume : Measure NSSpace))
      (by
        intro t
        rw [pressureEnergyPairing_zero_right]
        simp)
      hfdiv hgdiv

/-- The two-profile Schwartz energy theorem also closes on the standard
time-only pressure gauge class once the profiles are divergence-free. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree_timeOnlyPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (π : NSTime → ℝ) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun s : NSTime => fun _ : NSSpace => π s) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
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
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_divergenceFree_of_pressureIntegrable
      a a' b b' f g A B (fun s : NSTime => fun _ : NSSpace => π s) ν
      haBound hbBound ha hb heq
      (by
        intro t
        rw [pressureEnergyPairing_timeOnly]
        exact integrable_zero NSSpace ℝ (volume : Measure NSSpace))
      (by
        intro t
        rw [pressureEnergyPairing_timeOnly]
        simp)
      hfdiv hgdiv

end NavierStokes
end FluidDynamics
end Mettapedia
