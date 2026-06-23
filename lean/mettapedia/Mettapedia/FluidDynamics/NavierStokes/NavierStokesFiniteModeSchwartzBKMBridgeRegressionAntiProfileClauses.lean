import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridgeRegressionZeroVelocityAffinePressure
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMEqualAmplitudeClassification

/-!
# Equal-Amplitude Antiprofile BKM Clause Regressions

This module checks exact and no-go regressions for equal-amplitude antiprofile
BKM data and repaired finite-energy BKM clauses.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeSchwartzBKMBridgeRegression

theorem equal_amplitude_antiprofile_full_affine_localized_pressure_momentum_exact_collapsed_regression
    (a : NSTime → ℝ) (ν : ℝ) (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    (∀ t x,
        timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      (∀ t, c t = 0) ∧
        ((∃ t, ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  exact
    momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zero_and_schwartzPressureGradient_zero_if_nonzeroAmplitude
      a ν c π ρ f q

theorem equal_amplitude_antiprofile_arbitrary_pressure_momentum_exact_regression
    (a : NSTime → ℝ) (ν : ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∀ t x,
        timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialPressureGradient p t x =
          (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  exact
    momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
      a ν f p

theorem equal_amplitude_antiprofile_full_affine_localized_pressure_BKM_exact_collapsed_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  exact
    BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
      a c π ρ f q hc hπ hρ

theorem equal_amplitude_antiprofile_BKM_data_iff_zero_velocity_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_zeroVelocity a f p

theorem equal_amplitude_antiprofile_BKM_data_arbitrary_pressure_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
      a f hp

theorem equal_amplitude_antiprofile_BKM_data_arbitrary_pressure_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField)
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) a f (p := p) hfail

theorem equal_amplitude_antiprofile_initial_full_affine_localized_pressure_BKM_exact_collapsed_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  exact
    BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
      a c π ρ f q hc hπ hρ

theorem equal_amplitude_antiprofile_initial_BKM_data_iff_zero_velocity_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVelocity a f p

theorem equal_amplitude_antiprofile_initial_BKM_data_arbitrary_pressure_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
      a f hp

theorem equal_amplitude_antiprofile_initial_BKM_data_arbitrary_pressure_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField)
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) a f (p := p) hfail

theorem finite_energy_BKM_clause_zero_but_antiprofile_arbitrary_pressure_BKM_data_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField)
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = p ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_zero_and_not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) a f (p := p) hfail

theorem finite_energy_BKM_clause_antiprofile_initial_but_arbitrary_pressure_BKM_data_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField)
    (hfail :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness
            ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = p ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) a f (p := p) hfail

theorem finite_energy_BKM_clause_zero_and_antiprofile_arbitrary_pressure_BKM_data_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_zero_and_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
      (ν := ν) (T := T) a f hp

theorem finite_energy_BKM_clause_antiprofile_initial_and_arbitrary_pressure_BKM_data_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_spatialPressureGradient_zero
      (ν := ν) (T := T) a f hp

theorem finite_energy_BKM_clause_zero_and_antiprofile_full_affine_localized_BKM_data_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_zero_and_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
      (ν := ν) (T := T) a c π ρ f q hc hπ hρ

theorem finite_energy_BKM_clause_antiprofile_initial_and_full_affine_localized_BKM_data_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
      (ν := ν) (T := T) a c π ρ f q hc hπ hρ

theorem equal_amplitude_antiprofile_full_affine_localized_pressure_BKM_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
      a c π ρ f q hc hπ hρ hbad

theorem equal_amplitude_antiprofile_initial_full_affine_localized_pressure_BKM_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
      a c π ρ f q hc hπ hρ hbad

theorem finite_energy_BKM_clause_zero_but_antiprofile_full_affine_localized_BKM_data_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T ∧
      ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_zero_and_not_exists_BKMData_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
      a c π ρ f q hc hπ hρ hbad

theorem finite_energy_BKM_clause_antiprofile_initial_but_matching_BKM_data_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hbad :
      (∃ t, 0 ≤ t ∧ t ≤ T ∧ c t ≠ 0) ∨
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∃ W :
          ExplicitFiniteTimeRegularityWitness
            ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
          W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_exists_BKMData_equalAmplitudeAntiProfileInitialVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_on_or_active_schwartzPressureGradient_ne_zero
      a c π ρ f q hc hπ hρ hbad

theorem finite_energy_BKM_clause_antiprofile_initial_but_momentum_equation_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hbad :
      (∃ t, c t ≠ 0) ∨
        ((∃ t, ρ t ≠ 0) ∧
          ∃ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x ≠ 0)) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_of_exists_affineCoeff_ne_zero_or_active_schwartzPressureGradient_ne_zero
      a c π ρ f q hbad

theorem finite_energy_BKM_clause_antiprofile_initial_but_arbitrary_pressure_momentum_equation_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField)
    (hbad : ∃ t, ∃ x, spatialPressureGradient p t x ≠ 0) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ¬ ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient p t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_not_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := ν) (T := T) a f p hbad

theorem finite_energy_BKM_clause_antiprofile_initial_and_arbitrary_pressure_momentum_equation_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient p t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
      (ν := ν) (T := T) a f p

theorem finite_energy_BKM_clause_antiprofile_initial_and_arbitrary_pressure_BKM_data_and_momentum_equation_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (ExplicitFiniteEnergyBKMContinuationClause
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T ∧
      (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ∧
      ∀ t x,
          timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
              spatialPressureGradient p t x =
            (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_equalAmplitudeAntiProfileInitialVelocity_and_BKMData_equalAmplitudeAntiProfileInitialVelocity_and_momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
      (ν := ν) (T := T) a f hp

end NavierStokesFiniteModeSchwartzBKMBridgeRegression
end NavierStokes
end FluidDynamics
end Mettapedia
