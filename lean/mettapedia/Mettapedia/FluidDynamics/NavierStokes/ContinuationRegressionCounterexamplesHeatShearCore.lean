import Mettapedia.FluidDynamics.NavierStokes.ContinuationRegressionCounterexamplesAffineShear

/-!
# Undrifted Heat-Shear Continuation Counterexample Regressions

This module checks undrifted heat-shear momentum, vorticity bounds,
finite-energy exclusions, candidate gaps, and repaired clause regressions.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression

theorem heat_shear_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearVelocityField 1 1 1) t x +
        spatialConvection (heatShearVelocityField 1 1 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (heatShearVelocityField 1 1 1) t x := by
  simpa using momentumEquation_heatShearVelocityField_zeroPressure 1 1 1 t x

theorem heat_shear_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (heatShearVelocityField 1 1 1) T 1 := by
  simpa using uniformVorticityBoundUpTo_heatShearVelocityField 1 1 1 T (by positivity)

theorem heat_shear_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearVelocityField 1 1 1) T (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using heatShearVelocityField_has_constantBKMEnvelope 1 1 1 T (by positivity) hT

theorem heat_shear_vertical_drift_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearVerticalDriftVelocityField 1 1 1 1) t x +
        spatialConvection (heatShearVerticalDriftVelocityField 1 1 1 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (heatShearVerticalDriftVelocityField 1 1 1 1) t x := by
  simpa using momentumEquation_heatShearVerticalDriftVelocityField_zeroPressure 1 1 1 1 t x

theorem heat_shear_vertical_drift_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (heatShearVerticalDriftVelocityField 1 1 1 1) T 1 := by
  simpa using
    uniformVorticityBoundUpTo_heatShearVerticalDriftVelocityField 1 1 1 1 T (by positivity)

theorem heat_shear_vertical_drift_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearVerticalDriftVelocityField 1 1 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using
    heatShearVerticalDriftVelocityField_has_constantBKMEnvelope 1 1 1 1 T
      (by positivity) hT

theorem heat_shear_full_drift_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearFullDriftVelocityField 1 1 1 1 1) t x +
        spatialConvection (heatShearFullDriftVelocityField 1 1 1 1 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (heatShearFullDriftVelocityField 1 1 1 1 1) t x := by
  simpa using momentumEquation_heatShearFullDriftVelocityField_zeroPressure 1 1 1 1 1 t x

theorem heat_shear_full_drift_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (heatShearFullDriftVelocityField 1 1 1 1 1) T 1 := by
  simpa using
    uniformVorticityBoundUpTo_heatShearFullDriftVelocityField 1 1 1 1 1 T (by positivity)

theorem heat_shear_full_drift_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearFullDriftVelocityField 1 1 1 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using
    heatShearFullDriftVelocityField_has_constantBKMEnvelope 1 1 1 1 1 T
      (by positivity) hT

theorem heat_shear_transport_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportVelocityField 1 1 1 1) t x +
        spatialConvection (heatShearTransportVelocityField 1 1 1 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (heatShearTransportVelocityField 1 1 1 1) t x := by
  simpa using momentumEquation_heatShearTransportVelocityField_zeroPressure 1 1 1 1 t x

theorem heat_shear_transport_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (heatShearTransportVelocityField 1 1 1 1) T 1 := by
  simpa using
    uniformVorticityBoundUpTo_heatShearTransportVelocityField 1 1 1 1 T (by positivity)

theorem heat_shear_transport_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportVelocityField 1 1 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using
    heatShearTransportVelocityField_has_constantBKMEnvelope 1 1 1 1 T
      (by positivity) hT

theorem heat_shear_transport_full_drift_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) t x +
        spatialConvection (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) t x := by
  simpa using
    momentumEquation_heatShearTransportFullDriftVelocityField_zeroPressure 1 1 1 1 1 1 t x

theorem heat_shear_transport_full_drift_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) T 1 := by
  simpa using
    uniformVorticityBoundUpTo_heatShearTransportFullDriftVelocityField 1 1 1 1 1 1 T
      (by positivity)

theorem heat_shear_transport_full_drift_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using
    heatShearTransportFullDriftVelocityField_has_constantBKMEnvelope 1 1 1 1 1 1 T
      (by positivity) hT

theorem heat_shear_not_finite_initial_energy_regression :
    ¬ finiteInitialKineticEnergy (heatShearInitialVelocity 1 1) := by
  exact not_finiteInitialKineticEnergy_heatShearInitialVelocity (a := 1) (k := 1) (by simp) (by simp)

theorem heat_shear_direct_unbounded_energy_regression :
    ¬ boundedKineticEnergy (heatShearVelocityField 1 1 1) := by
  exact
    not_boundedKineticEnergy_heatShearVelocityField
      (ν := 1) (a := 1) (k := 1) (by simp) (by simp)

theorem heat_shear_direct_unbounded_energy_up_to_regression
    {T : ℝ} (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearVelocityField 1 1 1) T := by
  exact
    not_boundedKineticEnergyUpTo_heatShearVelocityField
      (ν := 1) (a := 1) (k := 1) (by simp) (by simp) hT

theorem heat_shear_not_in_repaired_structured_domain_regression :
    ¬ Nonempty { P : FiniteEnergyAdmissibleNavierStokesProblemData //
        P.initialVelocity = heatShearInitialVelocity 1 1 } := by
  exact
    not_nonempty_FiniteEnergyAdmissibleNavierStokesProblemData_heatShearInitialVelocity
      (a := 1) (k := 1) (by simp) (by simp)

theorem heat_shear_concrete_candidate_without_global_output_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity 1 1) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput 1 (heatShearInitialVelocity 1 1) := by
  simpa using
    heatShearInitialVelocity_exhibits_concreteCandidate_without_globalOutput
      (ν := 1) (a := 1) (k := 1) (by simp) (by simp)

theorem heat_shear_uniform_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1 (heatShearInitialVelocity 1 1) T) := by
  simpa using
    heatShearInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (by simp) (by simp) (by positivity) hT

theorem heat_shear_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (heatShearInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_heatShearInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) hν (by simp) (by simp) hT

theorem heat_shear_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν (heatShearInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) hν (by simp) (by simp)

theorem heat_shear_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearInitialVelocity 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearInitialVelocity_without_regularity
      (ν := ν) (a := 1) (k := 1) hν (by simp) (by simp)

theorem heat_shear_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearInitialVelocity 1 1
          smooth_initial := smoothInitialVelocityData_heatShearInitialVelocity 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearInitialVelocity 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_heatShearInitialVelocity
      (ν := ν) (a := 1) (k := 1) hν (by simp) (by simp)

theorem heat_shear_BKM_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearInitialVelocity 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1 (heatShearInitialVelocity 1 1) T) := by
  simpa using
    heatShearInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (by simp) (by simp) (by positivity) hT

theorem heat_shear_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity 1 1) := by
  exact
    ExplicitBKMContinuationClause_heatShearInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) hν (by simp) (by simp) hT

theorem heat_shear_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause ν (heatShearInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_heatShearInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) hν (by simp) (by simp)

end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
