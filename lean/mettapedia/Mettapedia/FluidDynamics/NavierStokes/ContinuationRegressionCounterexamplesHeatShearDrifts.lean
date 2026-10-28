import Mettapedia.FluidDynamics.NavierStokes.ContinuationRegressionCounterexamplesHeatShearCore

/-!
# Drift Heat-Shear Continuation Counterexample Regressions

This module checks streamwise, vertical, and full constant-drift heat-shear
finite-energy exclusions, candidate gaps, and repaired clause regressions.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression

theorem heat_shear_streamwise_drift_not_finite_initial_energy_regression :
    ¬ finiteInitialKineticEnergy (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  exact
    not_finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity
      (a := 1) (k := 1) (d := 1) (by simp)

theorem heat_shear_streamwise_drift_direct_unbounded_energy_regression :
    ¬ boundedKineticEnergy (heatShearStreamwiseDriftVelocityField 1 1 1 1) := by
  exact
    not_boundedKineticEnergy_heatShearStreamwiseDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (d := 1) (by simp)

theorem heat_shear_streamwise_drift_direct_unbounded_energy_up_to_regression
    {T : ℝ} (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearStreamwiseDriftVelocityField 1 1 1 1) T := by
  exact
    not_boundedKineticEnergyUpTo_heatShearStreamwiseDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (d := 1) (by simp) hT

theorem heat_shear_streamwise_drift_concrete_candidate_without_global_output_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity 1 1 1) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput 1
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  simpa using
    heatShearStreamwiseDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
      (ν := 1) (a := 1) (k := 1) (d := 1) (by simp)

theorem heat_shear_streamwise_drift_uniform_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity 1 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) T) := by
  simpa using
    heatShearStreamwiseDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (d := 1) (by simp) (by positivity) hT

theorem heat_shear_streamwise_drift_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) hν (by simp) hT

theorem heat_shear_streamwise_drift_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearStreamwiseDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) hν (by simp)

theorem heat_shear_streamwise_drift_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearStreamwiseDriftInitialVelocity 1 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (k := 1) (d := 1) hν (by simp)

theorem heat_shear_streamwise_drift_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearStreamwiseDriftInitialVelocity 1 1 1
          smooth_initial := smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity 1 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity 1 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_heatShearStreamwiseDriftInitialVelocity
      (ν := ν) (a := 1) (k := 1) (d := 1) hν (by simp)

theorem heat_shear_streamwise_drift_BKM_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearStreamwiseDriftInitialVelocity 1 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) T) := by
  simpa using
    heatShearStreamwiseDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (d := 1) (by simp) (by positivity) hT

theorem heat_shear_streamwise_drift_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) hν (by simp) hT

theorem heat_shear_streamwise_drift_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearStreamwiseDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_heatShearStreamwiseDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) hν (by simp)

theorem heat_shear_vertical_drift_not_finite_initial_energy_regression :
    ¬ finiteInitialKineticEnergy (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  exact
    not_finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity
      (a := 1) (k := 1) (c := 1) (by simp) (by simp)

theorem heat_shear_vertical_drift_direct_unbounded_energy_regression :
    ¬ boundedKineticEnergy (heatShearVerticalDriftVelocityField 1 1 1 1) := by
  exact
    not_boundedKineticEnergy_heatShearVerticalDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (c := 1) (by simp) (by simp)

theorem heat_shear_vertical_drift_direct_unbounded_energy_up_to_regression
    {T : ℝ} (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearVerticalDriftVelocityField 1 1 1 1) T := by
  exact
    not_boundedKineticEnergyUpTo_heatShearVerticalDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (c := 1) (by simp) (by simp) hT

theorem heat_shear_vertical_drift_concrete_candidate_without_global_output_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity 1 1 1) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput 1
        (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  simpa using
    heatShearVerticalDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
      (ν := 1) (a := 1) (k := 1) (c := 1) (by simp) (by simp)

theorem heat_shear_vertical_drift_uniform_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity 1 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1 (heatShearVerticalDriftInitialVelocity 1 1 1) T) := by
  simpa using
    heatShearVerticalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (c := 1) (by simp) (by simp) (by positivity) hT

theorem heat_shear_vertical_drift_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (heatShearVerticalDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (c := 1) hν (by simp) (by simp) hT

theorem heat_shear_vertical_drift_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearVerticalDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (c := 1) hν (by simp) (by simp)

theorem heat_shear_vertical_drift_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearVerticalDriftInitialVelocity 1 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (k := 1) (c := 1) hν (by simp) (by simp)

theorem heat_shear_vertical_drift_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearVerticalDriftInitialVelocity 1 1 1
          smooth_initial := smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity 1 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity 1 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_heatShearVerticalDriftInitialVelocity
      (ν := ν) (a := 1) (k := 1) (c := 1) hν (by simp) (by simp)

theorem heat_shear_vertical_drift_BKM_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearVerticalDriftInitialVelocity 1 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1 (heatShearVerticalDriftInitialVelocity 1 1 1) T) := by
  simpa using
    heatShearVerticalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (c := 1) (by simp) (by simp) (by positivity) hT

theorem heat_shear_vertical_drift_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (heatShearVerticalDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitBKMContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (c := 1) hν (by simp) (by simp) hT

theorem heat_shear_vertical_drift_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearVerticalDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_heatShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (c := 1) hν (by simp) (by simp)

theorem heat_shear_full_drift_not_finite_initial_energy_regression :
    ¬ finiteInitialKineticEnergy (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  exact
    not_finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity
      (a := 1) (k := 1) (d := 1) (c := 1) (by simp)

theorem heat_shear_full_drift_direct_unbounded_energy_regression :
    ¬ boundedKineticEnergy (heatShearFullDriftVelocityField 1 1 1 1 1) := by
  exact
    not_boundedKineticEnergy_heatShearFullDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (d := 1) (c := 1) (by simp)

theorem heat_shear_full_drift_direct_unbounded_energy_up_to_regression
    {T : ℝ} (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearFullDriftVelocityField 1 1 1 1 1) T := by
  exact
    not_boundedKineticEnergyUpTo_heatShearFullDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (d := 1) (c := 1) (by simp) hT

theorem heat_shear_full_drift_concrete_candidate_without_global_output_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity 1 1 1 1) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput 1
        (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  simpa using
    heatShearFullDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
      (ν := 1) (a := 1) (k := 1) (d := 1) (c := 1) (by simp)

theorem heat_shear_full_drift_uniform_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity 1 1 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearFullDriftInitialVelocity 1 1 1 1) T) := by
  simpa using
    heatShearFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (d := 1) (c := 1) (by simp) (by positivity) hT

theorem heat_shear_full_drift_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) (c := 1) hν (by simp) hT

theorem heat_shear_full_drift_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearFullDriftInitialVelocity 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_full_drift_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearFullDriftInitialVelocity 1 1 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (k := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_full_drift_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearFullDriftInitialVelocity 1 1 1 1
          smooth_initial := smoothInitialVelocityData_heatShearFullDriftInitialVelocity 1 1 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity 1 1 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_heatShearFullDriftInitialVelocity
      (ν := ν) (a := 1) (k := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_full_drift_BKM_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearFullDriftInitialVelocity 1 1 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearFullDriftInitialVelocity 1 1 1 1) T) := by
  simpa using
    heatShearFullDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (d := 1) (c := 1) (by simp) (by positivity) hT

theorem heat_shear_full_drift_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  exact
    ExplicitBKMContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) (c := 1) hν (by simp) hT

theorem heat_shear_full_drift_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearFullDriftInitialVelocity 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity 1 1 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_heatShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (d := 1) (c := 1) hν (by simp)

end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
