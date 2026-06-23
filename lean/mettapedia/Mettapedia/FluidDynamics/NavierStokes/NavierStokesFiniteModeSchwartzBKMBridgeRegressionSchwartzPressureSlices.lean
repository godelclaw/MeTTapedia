import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridgeRegressionAffineObstructions

/-!
# Schwartz-Pressure Slice BKM Bridge Regressions

This module checks Schwartz-pressure slice witnesses, zero envelopes, and
canonical gauge witnesses in the equal-amplitude antiprofile corridor.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeSchwartzBKMBridgeRegression

theorem two_mode_schwartz_divergence_free_zero_bridge_schwartz_pressure_slice_witness_regression :
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
            (fun s : NSTime => fun y : NSSpace => (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
  have hp :
      smoothSpaceTimePressure
        (fun s : NSTime => fun y : NSSpace =>
          (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation_schwartzPressureSlice
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      (f := (0 : NSSchwartzInitialVelocity))
      (g := (0 : NSSchwartzInitialVelocity))
      (A := 0)
      (B := 0)
      (q := fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      hp
      le_rfl
      (by intro t; simp)
      (by intro t; simp)
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (by
        intro t x
        simpa [twoModeSchwartzVelocity_zero_zero] using
          momentumEquation_zeroVelocityField_timeOnlyPressure 0 (fun _ : NSTime => 0) t x)

theorem two_mode_schwartz_divergence_free_zero_bridge_schwartz_pressure_slice_BKM_premise_regression :
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
  have hp :
      smoothSpaceTimePressure
        (fun s : NSTime => fun y : NSSpace =>
          (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation_schwartzPressureSlice
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      (f := (0 : NSSchwartzInitialVelocity))
      (g := (0 : NSSchwartzInitialVelocity))
      (A := 0)
      (B := 0)
      (q := fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      hp
      le_rfl
      (by intro t; simp)
      (by intro t; simp)
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (by
        intro t x
        simpa [twoModeSchwartzVelocity_zero_zero] using
          momentumEquation_zeroVelocityField_timeOnlyPressure 0 (fun _ : NSTime => 0) t x)

theorem two_mode_schwartz_divergence_free_zero_bridge_explicitClosure_schwartz_pressure_slice_BKM_premise_regression :
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
  have hp :
      smoothSpaceTimePressure
        (fun s : NSTime => fun y : NSSpace =>
          (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_explicitClosure_schwartzPressureSlice
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      (f := (0 : NSSchwartzInitialVelocity))
      (g := (0 : NSSchwartzInitialVelocity))
      (A := 0)
      (B := 0)
      (q := fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      hp
      le_rfl
      (by intro t; simp)
      (by intro t; simp)
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (fun x => by simpa using (initialSpatialDivergence_zero x))
      (by
        intro t x
        simpa using spatialPressureGradient_zero t x)

theorem one_one_antiprofile_schwartz_pressure_slice_zero_BKM_premise_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity 0 Ω ∧
            integrableVorticityEnvelopeOn Ω 0 Bint := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_oneOneAntiProfile_schwartzPressureSlice_zeroPressure
      (ν := 0)
      (T := 0)
      le_rfl
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem equal_amplitude_antiprofile_schwartz_pressure_slice_zero_BKM_premise_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity 0 Ω ∧
            integrableVorticityEnvelopeOn Ω 0 Bint := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure
      (a := fun _ : NSTime => 0)
      (A := 0)
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem equal_amplitude_antiprofile_schwartz_pressure_slice_zero_BKM_zero_witness_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          (fun s : NSTime => fun y : NSSpace =>
            (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity 0 Ω ∧
            integrableVorticityEnvelopeOn Ω 0 Bint := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_zeroWitness
      (a := fun _ : NSTime => 0)
      (A := 0)
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem equal_amplitude_antiprofile_schwartz_pressure_slice_zero_BKM_zero_envelope_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          (fun s : NSTime => fun y : NSSpace =>
            (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) ∧
        vorticityEnvelopeOn W.velocity 0 (fun _ : NSTime => 0) ∧
          integrableVorticityEnvelopeOn (fun _ : NSTime => 0) 0 0 := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_zeroWitness_zeroEnvelope
      (a := fun _ : NSTime => 0)
      (A := 0)
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem equal_amplitude_antiprofile_schwartz_pressure_slice_zero_BKM_canonical_zero_witness_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
      W = zeroFiniteTimeRegularityWitness 0 0 ∧
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) ∧
          vorticityEnvelopeOn W.velocity 0 (fun _ : NSTime => 0) ∧
            integrableVorticityEnvelopeOn (fun _ : NSTime => 0) 0 0 := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_canonicalZeroWitness
      (a := fun _ : NSTime => 0)
      (A := 0)
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      le_rfl
      (by intro t; simp)
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem equal_amplitude_antiprofile_affine_time_only_pressure_BKM_zero_envelope_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          affineAddScalarSchwartzPressure (fun _ : NSTime => 0)
            (fun _ : NSTime => (1 : ℝ)) (fun _ : NSTime => 0)
            (0 : 𝓢(NSSpace, ℝ)) ∧
        vorticityEnvelopeOn W.velocity 0 (fun _ : NSTime => 0) ∧
          integrableVorticityEnvelopeOn (fun _ : NSTime => 0) 0 0 := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_affineTimeOnlyPressure_zeroWitness_zeroEnvelope
      (a := fun _ : NSTime => 0)
      (A := 0)
      (π := fun _ : NSTime => (1 : ℝ))
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ)))
      le_rfl
      (by intro t; simp)
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))

theorem equal_amplitude_antiprofile_affine_time_only_pressure_BKM_canonical_gauge_witness_regression :
    ∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
      W =
          (zeroFiniteTimeRegularityWitness 0 0).addTimeOnlyPressure
            (fun _ : NSTime => (1 : ℝ))
            (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ))) ∧
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure (fun _ : NSTime => 0)
              (fun _ : NSTime => (1 : ℝ)) (fun _ : NSTime => 0)
              (0 : 𝓢(NSSpace, ℝ)) ∧
          vorticityEnvelopeOn W.velocity 0 (fun _ : NSTime => 0) ∧
            integrableVorticityEnvelopeOn (fun _ : NSTime => 0) 0 0 := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_affineTimeOnlyPressure_canonicalGaugeWitness
      (a := fun _ : NSTime => 0)
      (A := 0)
      (π := fun _ : NSTime => (1 : ℝ))
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0)
      (T := 0)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ)))
      le_rfl
      (by intro t; simp)
      (0 : NSSchwartzInitialVelocity)
      (fun x => by simpa using (initialSpatialDivergence_zero x))


end NavierStokesFiniteModeSchwartzBKMBridgeRegression
end NavierStokes
end FluidDynamics
end Mettapedia
