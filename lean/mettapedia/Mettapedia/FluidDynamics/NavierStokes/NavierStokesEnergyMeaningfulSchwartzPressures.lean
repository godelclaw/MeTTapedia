import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyMeaningfulSchwartzCore

/-!
# Navier-Stokes Energy: Meaningful Schwartz Elementary Pressure Lanes

Semantic layer split from `NavierStokesEnergyMeaningfulSchwartz`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- The corrected two-profile coordinate energy identity closes completely for
the concrete class with slice-wise divergence-free flow and a time-only
pressure gauge. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_timeOnlyPressure
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
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
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
      hdiv

/-- The corrected two-profile coordinate energy identity also closes for the
coordinate-linear pressure gauge `p(t,x) = c * x₀` under slice-wise
divergence-free flow. On this Schwartz class, the needed zero-mean condition on
the pressured component is derived internally from the divergence-free
hypothesis. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_coord0LinearPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B c : ℝ)
    (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => c * y nsCoord0) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B (fun _ : NSTime => fun y : NSSpace => c * y nsCoord0) ν
      haBound hbBound ha hb heq
      (by
        intro t
        let coord0 :
            𝓢(NSSpace, ℝ) :=
          SchwartzMap.bilinLeftCLM
            (ContinuousLinearMap.apply ℝ ℝ)
            (g := fun _ : NSSpace => (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ))
            (by fun_prop)
            ((a t) • f + (b t) • g)
        have hcoord :
            (fun x : NSSpace => c * ((a t) • f x + (b t) • g x) nsCoord0) =
              fun x : NSSpace => c * coord0 x := by
          funext x
          simp [coord0, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
        have hpair :
            pressureEnergyPairing
                (fun s y => a s • f y + b s • g y)
                (fun _ : NSTime => fun y : NSSpace => c * y nsCoord0) t =
              fun x : NSSpace => c * coord0 x := by
          rw [pressureEnergyPairing_coord0Linear]
          exact hcoord
        rw [hpair]
        exact coord0.integrable.const_mul c)
      (by
        intro t
        rw [pressureEnergyPairing_coord0Linear]
        rw [integral_const_mul]
        rw [integral_coord0_zero_of_schwartzSlice_of_spatialDivergence_zero
          (u := fun s y => a s • f y + b s • g y)
          (t := t)
          (f := (a t) • f + (b t) • g)
          (hslice := by intro x; rfl)
          (hdiv := by intro x; exact hdiv t x)]
        simp)
      hdiv

/-- The corrected two-profile coordinate energy identity closes for every
time-independent linear pressure gauge `p(t,x) = ⟪c, x⟫` under slice-wise
divergence-free flow. The needed boundary cancellation is discharged
coordinatewise from the divergence-free Schwartz slice theorem. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_linearPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSSpace) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) ν
      haBound hbBound ha hb heq
      (by
        intro t
        exact
          integrable_pressureEnergyPairing_linear_of_schwartzSlice
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (c := c)
            (hslice := by intro x; rfl))
      (by
        intro t
        exact
          integral_pressureEnergyPairing_linear_of_schwartzSlice_of_spatialDivergence_zero
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (c := c)
            (hslice := by intro x; rfl)
            (hdiv := by intro x; exact hdiv t x))
      hdiv

/-- The corrected two-profile coordinate energy identity closes for the full
affine pressure gauge class `p(t,x) = ⟪c(t), x⟫ + π(t)` under slice-wise
divergence-free flow. The time-only part contributes no spatial gradient, and
the linear part cancels coordinatewise from the divergence-free Schwartz slice
theorem. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affinePressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B (fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) ν
      haBound hbBound ha hb heq
      (by
        intro t
        rw [pressureEnergyPairing_affine]
        simpa [pressureEnergyPairing_linear] using
          integrable_pressureEnergyPairing_linear_of_schwartzSlice
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (c := c t)
            (hslice := by intro x; rfl))
      (by
        intro t
        rw [pressureEnergyPairing_affine]
        simpa [pressureEnergyPairing_linear] using
          integral_pressureEnergyPairing_linear_of_schwartzSlice_of_spatialDivergence_zero
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (c := c t)
            (hslice := by intro x; rfl)
            (hdiv := by intro x; exact hdiv t x))
      hdiv

/-- The corrected two-profile coordinate energy identity closes for the genuine
non-affine Schwartz pressure class `p(t,x) = ρ(t) * q(x)` under slice-wise
divergence-free flow. The pressure term cancels by coordinatewise integration by
parts against the fixed Schwartz scalar profile `q`. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_scalarSchwartzPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) (ν : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x +
          spatialConvection (fun s y => a s • f y + b s • g y) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ν : ℝ) • spatialLaplacian (fun s y => a s • f y + b s • g y) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B (fun s : NSTime => fun y : NSSpace => ρ s * q y) ν
      haBound hbBound ha hb heq
      (by
        intro t
        exact
          integrable_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (ρ := ρ)
            (q := q)
            (hslice := by intro x; rfl))
      (by
        intro t
        exact
          integral_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure_of_spatialDivergence_zero
            (u := fun s y => a s • f y + b s • g y)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (ρ := ρ)
            (q := q)
            (hslice := by intro x; rfl)
            (hdiv := by intro x; exact hdiv t x))
      hdiv

end NavierStokes
end FluidDynamics
end Mettapedia
