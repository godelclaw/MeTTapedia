import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridgeCore

/-!
# Zero and Two-Mode BKM Bridge Regressions

This module checks zero two-mode Schwartz bridge witnesses and the basic
nonzero two-mode BKM premise regressions.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeSchwartzBKMBridgeRegression

theorem two_mode_schwartz_divergence_free_zero_bridge_finite_time_witness_regression :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            0 0
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (fun x => by simpa using (initialSpatialDivergence_zero x))
            (fun x => by simpa using (initialSpatialDivergence_zero x))).1 : NSInitialVelocity) 0,
        W.velocity =
            twoModeSchwartzVelocity
              (fun _ : NSTime => 0) (fun _ : NSTime => 0)
              (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity) ∧
          W.pressure =
            affineAddScalarSchwartzPressure
              (fun _ : NSTime => 0)
              (fun _ : NSTime => 0)
              (fun _ : NSTime => 0)
              (0 : 𝓢(NSSpace, ℝ)) := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      (f := (0 : NSSchwartzInitialVelocity))
      (g := (0 : NSSchwartzInitialVelocity))
      (A := 0)
      (B := 0)
      (c := fun _ : NSTime => 0)
      (π := fun _ : NSTime => 0)
      (ρ := fun _ : NSTime => 0)
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : NSSpace)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (by intro t; simp)
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
        0
        (fun _ : NSTime => 0)
        (0 : NSSchwartzInitialVelocity)
        (0 : NSSchwartzInitialVelocity)
        (0 : 𝓢(NSSpace, ℝ)))

theorem two_mode_schwartz_divergence_free_zero_bridge_BKM_premise_regression :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            0 0
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (fun x => by simpa using (initialSpatialDivergence_zero x))
            (fun x => by simpa using (initialSpatialDivergence_zero x))).1 : NSInitialVelocity) 0,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity 0 Ω ∧
            integrableVorticityEnvelopeOn Ω 0 Bint := by
  have hω :
      uniformVorticityBoundUpTo
        (twoModeSchwartzVelocity
          (fun _ : NSTime => 0) (fun _ : NSTime => 0)
          (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity))
        0 0 := by
    simpa [twoModeSchwartzVelocity_zero_zero] using
      (uniformVorticityBoundUpTo_zero 0)
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation_and_uniformVorticityBound
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      (f := (0 : NSSchwartzInitialVelocity))
      (g := (0 : NSSchwartzInitialVelocity))
      (A := 0)
      (B := 0)
      (c := fun _ : NSTime => 0)
      (π := fun _ : NSTime => 0)
      (ρ := fun _ : NSTime => 0)
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (K := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : NSSpace)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (by intro t; simp)
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
        0
        (fun _ : NSTime => 0)
        (0 : NSSchwartzInitialVelocity)
        (0 : NSSchwartzInitialVelocity)
        (0 : 𝓢(NSSpace, ℝ)))
      hω

theorem two_mode_schwartz_divergence_free_zero_bridge_internal_BKM_premise_regression :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            0 0
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (fun x => by simpa using (initialSpatialDivergence_zero x))
            (fun x => by simpa using (initialSpatialDivergence_zero x))).1 : NSInitialVelocity) 0,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity 0 Ω ∧
            integrableVorticityEnvelopeOn Ω 0 Bint := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      (f := (0 : NSSchwartzInitialVelocity))
      (g := (0 : NSSchwartzInitialVelocity))
      (A := 0)
      (B := 0)
      (c := fun _ : NSTime => 0)
      (π := fun _ : NSTime => 0)
      (ρ := fun _ : NSTime => 0)
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : NSSpace)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (by intro t; simp)
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
        0
        (fun _ : NSTime => 0)
        (0 : NSSchwartzInitialVelocity)
        (0 : NSSchwartzInitialVelocity)
        (0 : 𝓢(NSSpace, ℝ)))

theorem one_one_two_mode_schwartz_nonzero_inviscid_zero_pressure_BKM_premise_regression
    (f g : NSSchwartzInitialVelocity) {T : ℝ}
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace)) ∧
      ∃ W :
          ExplicitFiniteTimeRegularityWitness 0
            (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = (0 : NSPressureField) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    oneOneTwoModeSchwartzVelocity_nonzero_inviscidZeroPressure_BKMPremise_of_convectionClosure
      f g hfg hfDiv hgDiv hclosure

theorem one_one_two_mode_schwartz_nonzero_pos_viscosity_pressure_repaired_BKM_premise_regression
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) {T : ℝ}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hpressure : ∀ t x,
        spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    (∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace)) ∧
      ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    oneOneTwoModeSchwartzVelocity_nonzero_posViscosity_BKMPremise_of_inviscidClosure_pressureGradient
      hν f g c π ρ q hc hπ hρ hfg hfDiv hgDiv hclosure hpressure

end NavierStokesFiniteModeSchwartzBKMBridgeRegression
end NavierStokes
end FluidDynamics
end Mettapedia
