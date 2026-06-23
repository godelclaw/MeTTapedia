import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyMeaningfulSchwartzCore

/-!
# Navier-Stokes Energy: Meaningful Schwartz Affine Plus Scalar Pressure

Semantic layer split from `NavierStokesEnergyMeaningfulSchwartz`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- The corrected two-profile coordinate energy identity closes for the
combined pressure class consisting of an affine gauge plus a localized Schwartz
pressure profile. This packages the affine cancellation and the Schwartz
integration-by-parts cancellation on the same concrete `ℝ × ℝ^3` surface. -/
theorem meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) (ν : ℝ)
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
    ∀ t,
      MeasureTheory.Integrable
          (kineticEnergyDensity (fun s y => a s • f y + b s • g y) t) ∧
        HasDerivAt
          (normalizedKineticEnergy (fun s y => a s • f y + b s • g y))
          (-(coordinateEnergyDissipationRate (fun s y => a s • f y + b s • g y) ν t)) t := by
  let u : NSVelocityField := fun s y => a s • f y + b s • g y
  let pAffine : NSPressureField := fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s
  let pSchwartz : NSPressureField := fun s : NSTime => fun y : NSSpace => ρ s * q y
  have hpAffineDiff (t : NSTime) :
      ∀ x, DifferentiableAt ℝ (fun y : NSSpace => pAffine t y) x := by
    intro x
    have hderiv :
        HasFDerivAt (fun y : NSSpace => ⟪c t, y⟫ + π t)
          ((InnerProductSpace.toDual ℝ NSSpace) (c t)) x := by
      simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
        ((((InnerProductSpace.toDual ℝ NSSpace) (c t))).hasFDerivAt).add_const (π t)
    exact hderiv.differentiableAt
  have hpSchwartzDiff (t : NSTime) :
      ∀ x, DifferentiableAt ℝ (fun y : NSSpace => pSchwartz t y) x := by
    intro x
    exact (q.differentiableAt.const_mul (ρ t))
  exact
    meaningfulCoordinateEnergyDissipationIdentity_smooth_of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_of_pressureIntegrable
      a a' b b' f g A B (pAffine + pSchwartz) ν
      haBound hbBound ha hb
      (by
        intro t x
        simpa [u, pAffine, pSchwartz] using heq t x)
      (by
        intro t
        have hPairAdd :
            pressureEnergyPairing u (pAffine + pSchwartz) t =
              fun x : NSSpace =>
                pressureEnergyPairing u pAffine t x +
                  pressureEnergyPairing u pSchwartz t x :=
          pressureEnergyPairing_add u t (hpAffineDiff t) (hpSchwartzDiff t)
        have hAffineInt :
            Integrable (pressureEnergyPairing u pAffine t) := by
          rw [pressureEnergyPairing_affine]
          simpa [pressureEnergyPairing_linear, u, pAffine] using
            integrable_pressureEnergyPairing_linear_of_schwartzSlice
              (u := u)
              (t := t)
              (f := (a t) • f + (b t) • g)
              (c := c t)
              (hslice := by intro x; rfl)
        have hSchwartzInt :
            Integrable (pressureEnergyPairing u pSchwartz t) :=
          integrable_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure
            (u := u)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (ρ := ρ)
            (q := q)
            (hslice := by intro x; rfl)
        rw [hPairAdd]
        exact hAffineInt.add hSchwartzInt)
      (by
        intro t
        have hPairAdd :
            pressureEnergyPairing u (pAffine + pSchwartz) t =
              fun x : NSSpace =>
                pressureEnergyPairing u pAffine t x +
                  pressureEnergyPairing u pSchwartz t x :=
          pressureEnergyPairing_add u t (hpAffineDiff t) (hpSchwartzDiff t)
        have hAffineInt :
            Integrable (pressureEnergyPairing u pAffine t) := by
          rw [pressureEnergyPairing_affine]
          simpa [pressureEnergyPairing_linear, u, pAffine] using
            integrable_pressureEnergyPairing_linear_of_schwartzSlice
              (u := u)
              (t := t)
              (f := (a t) • f + (b t) • g)
              (c := c t)
              (hslice := by intro x; rfl)
        have hSchwartzInt :
            Integrable (pressureEnergyPairing u pSchwartz t) :=
          integrable_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure
            (u := u)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (ρ := ρ)
            (q := q)
            (hslice := by intro x; rfl)
        have hAffineIntegral :
            ∫ x, pressureEnergyPairing u pAffine t x ∂volume = 0 := by
          rw [pressureEnergyPairing_affine]
          simpa [pressureEnergyPairing_linear, u, pAffine] using
            integral_pressureEnergyPairing_linear_of_schwartzSlice_of_spatialDivergence_zero
              (u := u)
              (t := t)
              (f := (a t) • f + (b t) • g)
              (c := c t)
              (hslice := by intro x; rfl)
              (hdiv := by intro x; exact hdiv t x)
        have hSchwartzIntegral :
            ∫ x, pressureEnergyPairing u pSchwartz t x ∂volume = 0 :=
          integral_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure_of_spatialDivergence_zero
            (u := u)
            (t := t)
            (f := (a t) • f + (b t) • g)
            (ρ := ρ)
            (q := q)
            (hslice := by intro x; rfl)
            (hdiv := by intro x; exact hdiv t x)
        rw [hPairAdd]
        rw [integral_add hAffineInt hSchwartzInt, hAffineIntegral, hSchwartzIntegral]
        simp)
      (by
        intro t x
        simpa [u] using hdiv t x)

end NavierStokes
end FluidDynamics
end Mettapedia
