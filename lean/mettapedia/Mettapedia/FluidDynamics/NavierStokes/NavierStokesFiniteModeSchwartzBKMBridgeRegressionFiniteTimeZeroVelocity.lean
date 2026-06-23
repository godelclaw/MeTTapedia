import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridgeRegressionAntiProfileClauses

/-!
# Finite-Time and Zero-Velocity BKM Bridge Regressions

This module checks finite-time antiprofile witness classifications and
zero-velocity pressure-gradient impossibility regressions.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeSchwartzBKMBridgeRegression

theorem finite_time_witness_antiprofile_initial_arbitrary_pressure_exact_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧ W.pressure = p) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    exists_ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_iff_spatialPressureGradient_zero_on
      (ν := ν) (T := T) a f hp

theorem finite_time_witness_antiprofile_initial_arbitrary_pressure_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hbad :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧ W.pressure = p := by
  exact
    not_exists_ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_of_exists_spatialPressureGradient_ne_zero_on
      (ν := ν) (T := T) a f hbad

theorem finite_time_witness_antiprofile_initial_internal_pressure_zero_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (W :
      ExplicitFiniteTimeRegularityWitness
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T)
    (hWvel : W.velocity = twoModeSchwartzVelocity a a f (-f)) :
    ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient W.pressure t x = 0 := by
  exact
    ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_implies_spatialPressureGradient_pressure_zero_on
      a f W hWvel

theorem finite_time_witness_antiprofile_initial_zero_BKM_envelope_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (W :
      ExplicitFiniteTimeRegularityWitness
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T)
    (hWvel : W.velocity = twoModeSchwartzVelocity a a f (-f)) :
    vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  exact
    ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_has_zero_vorticityEnvelope
      a f W hWvel

theorem BKM_data_antiprofile_initial_zero_vorticity_envelope_zero_budget_normal_form_regression
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
      ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure = p ∧
          vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
            integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  exact
    BKMData_equalAmplitudeAntiProfileInitialVelocity_iff_zeroVorticityEnvelope_zeroBudget
      a f p

theorem finite_time_witness_antiprofile_initial_internal_pressure_no_go_regression
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient W.pressure t x ≠ 0 := by
  exact
    not_exists_ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_of_exists_pressure_spatialPressureGradient_ne_zero_on
      a f

theorem zero_velocity_BKM_data_pressure_gradient_zero_regression
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact BKMData_zeroVelocity_implies_spatialPressureGradient_zero hData

theorem zero_velocity_BKM_data_initial_velocity_zero_regression
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    u0 = 0 := by
  exact BKMData_zeroVelocity_implies_initialVelocity_zero hData

theorem zero_velocity_BKM_data_initial_velocity_and_pressure_gradient_zero_regression
    {ν T : ℝ} {u0 : NSInitialVelocity} {p : NSPressureField}
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    u0 = 0 ∧
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    BKMData_zeroVelocity_implies_initialVelocity_zero_and_spatialPressureGradient_zero
      hData

theorem zero_velocity_BKM_data_exact_classification_regression
    {ν T : ℝ} {u0 : NSInitialVelocity} (p : NSPressureField)
    (hp : smoothSpaceTimePressure p) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = p ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧
        ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  exact
    BKMData_zeroVelocity_iff_initialVelocity_zero_and_spatialPressureGradient_zero
      hp

theorem zero_velocity_BKM_data_time_only_pressure_iff_initial_zero_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 := by
  exact
    BKMData_zeroVelocity_timeOnlyPressure_iff_initialVelocity_zero
      π hπ

theorem zero_velocity_BKM_data_time_only_pressure_exists_regression
    {ν T : ℝ} (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    BKMData_zeroVelocity_timeOnlyPressure (ν := ν) (T := T) π hπ

theorem zero_velocity_BKM_data_time_only_pressure_nonzero_initial_impossible_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) (hu0 : u0 ≠ 0) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = (fun t : NSTime => fun _ : NSSpace => π t) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  exact
    not_exists_BKMData_zeroVelocity_timeOnlyPressure_of_initialVelocity_ne_zero
      π hπ hu0

theorem zero_velocity_BKM_data_nonzero_initial_velocity_impossible_regression :
    ¬
      (∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          (constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ))) 0,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = (0 : NSPressureField) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity 0 Ω ∧
              integrableVorticityEnvelopeOn Ω 0 Bint) := by
  refine
    not_exists_BKMData_zeroVelocity_of_initialVelocity_ne_zero
      (ν := 0)
      (T := 0)
      (u0 := constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ)))
      (p := (0 : NSPressureField))
      ?_
  intro hzero
  have hpoint :
      (constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ)))
          (0 : NSSpace) =
        (0 : NSInitialVelocity) (0 : NSSpace) := by
    exact congrFun hzero (0 : NSSpace)
  have hcoordZero :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 =
        (0 : NSSpace) nsCoord0 := by
    exact congrArg (fun v : NSSpace => v nsCoord0) hpoint
  simp [nsCoord0] at hcoordZero

theorem zero_velocity_BKM_data_nonzero_initial_or_pressure_gradient_impossible_regression :
    ¬
      (∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          (constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ))) 0,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            (fun _ : NSTime => fun y : NSSpace => (1 : ℝ) * y nsCoord0) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity 0 Ω ∧
              integrableVorticityEnvelopeOn Ω 0 Bint) := by
  refine
    not_exists_BKMData_zeroVelocity_of_initialVelocity_ne_zero_or_exists_spatialPressureGradient_ne_zero
      (ν := 0)
      (T := 0)
      (u0 := constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ)))
      (p := fun _ : NSTime => fun y : NSSpace => (1 : ℝ) * y nsCoord0)
      ?_
  refine Or.inr ?_
  refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
  rw [spatialPressureGradient_coord0Linear]
  intro hzero
  have hcoordZero :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 =
        (0 : NSSpace) nsCoord0 := by
    exact congrArg (fun v : NSSpace => v nsCoord0) hzero
  simp [nsCoord0] at hcoordZero

theorem zero_velocity_BKM_data_nonzero_pressure_gradient_impossible_regression :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            (fun _ : NSTime => fun y : NSSpace => (1 : ℝ) * y nsCoord0) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity 0 Ω ∧
              integrableVorticityEnvelopeOn Ω 0 Bint) := by
  refine
    not_exists_BKMData_zeroVelocity_of_exists_spatialPressureGradient_ne_zero
      (ν := 0)
      (T := 0)
      (u0 := (0 : NSInitialVelocity))
      (p := fun _ : NSTime => fun y : NSSpace => (1 : ℝ) * y nsCoord0)
      ?_
  refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
  rw [spatialPressureGradient_coord0Linear]
  intro hzero
  have hcoordZero :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 =
        (0 : NSSpace) nsCoord0 := by
    exact congrArg (fun v : NSSpace => v nsCoord0) hzero
  simp [nsCoord0] at hcoordZero

end NavierStokesFiniteModeSchwartzBKMBridgeRegression
end NavierStokes
end FluidDynamics
end Mettapedia
