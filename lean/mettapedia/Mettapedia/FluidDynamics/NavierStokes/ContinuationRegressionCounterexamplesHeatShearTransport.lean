import Mettapedia.FluidDynamics.NavierStokes.ContinuationRegressionCounterexamplesHeatShearDrifts

/-!
# Transported Heat-Shear Continuation Counterexample Regressions

This module checks transported and transported-full-drift heat-shear
finite-energy exclusions, candidate gaps, and repaired clause regressions.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression

theorem heat_shear_transport_not_finite_initial_energy_regression :
    ¬ finiteInitialKineticEnergy (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    not_finiteInitialKineticEnergy_heatShearTransportInitialVelocity
      (a := 1) (k := 1) (b := 1) (by simp)

theorem heat_shear_transport_direct_unbounded_energy_regression :
    ¬ boundedKineticEnergy (heatShearTransportVelocityField 1 1 1 1) := by
  exact
    not_boundedKineticEnergy_heatShearTransportVelocityField
      (ν := 1) (a := 1) (k := 1) (b := 1) (by simp)

theorem heat_shear_transport_direct_unbounded_energy_up_to_regression
    {T : ℝ} (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearTransportVelocityField 1 1 1 1) T := by
  exact
    not_boundedKineticEnergyUpTo_heatShearTransportVelocityField
      (ν := 1) (a := 1) (k := 1) (b := 1) (by simp) hT

theorem heat_shear_transport_concrete_candidate_without_global_output_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity 1 1 1) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput 1
        (heatShearTransportInitialVelocity 1 1 1) := by
  simpa using
    heatShearTransportInitialVelocity_exhibits_concreteCandidate_without_globalOutput
      (ν := 1) (a := 1) (k := 1) (b := 1) (by simp)

theorem heat_shear_transport_uniform_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity 1 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearTransportInitialVelocity 1 1 1) T) := by
  simpa using
    heatShearTransportInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (b := 1) (by simp) (by positivity) hT

theorem heat_shear_transport_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν
        (heatShearTransportInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_heatShearTransportInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) hν (by simp) hT

theorem heat_shear_transport_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearTransportInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) hν (by simp)

theorem heat_shear_transport_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearTransportInitialVelocity 1 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportInitialVelocity_without_regularity
      (ν := ν) (a := 1) (k := 1) (b := 1) hν (by simp)

theorem heat_shear_transport_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportInitialVelocity 1 1 1
          smooth_initial := smoothInitialVelocityData_heatShearTransportInitialVelocity 1 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportInitialVelocity 1 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_heatShearTransportInitialVelocity
      (ν := ν) (a := 1) (k := 1) (b := 1) hν (by simp)

theorem heat_shear_transport_BKM_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportInitialVelocity 1 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearTransportInitialVelocity 1 1 1) T) := by
  simpa using
    heatShearTransportInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (b := 1) (by simp) (by positivity) hT

theorem heat_shear_transport_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν
        (heatShearTransportInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    ExplicitBKMContinuationClause_heatShearTransportInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) hν (by simp) hT

theorem heat_shear_transport_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearTransportInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) hν (by simp)

theorem heat_shear_transport_full_drift_not_finite_initial_energy_regression :
    ¬ finiteInitialKineticEnergy (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact
    not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity
      (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) (by simp)

theorem heat_shear_transport_full_drift_direct_unbounded_energy_regression :
    ¬ boundedKineticEnergy (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) := by
  exact
    not_boundedKineticEnergy_heatShearTransportFullDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) (by simp)

theorem heat_shear_transport_full_drift_direct_unbounded_energy_up_to_regression
    {T : ℝ} (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearTransportFullDriftVelocityField 1 1 1 1 1 1) T := by
  exact
    not_boundedKineticEnergyUpTo_heatShearTransportFullDriftVelocityField
      (ν := 1) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) (by simp) hT

theorem heat_shear_transport_full_drift_concrete_candidate_without_global_output_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x,
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) u ∧
      ¬ boundedKineticEnergy u) ∧
      ¬ ExplicitConcreteNavierStokesGlobalOutput 1
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  simpa using
    heatShearTransportFullDriftInitialVelocity_exhibits_concreteCandidate_without_globalOutput
      (ν := 1) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) (by simp)

theorem heat_shear_transport_full_drift_uniform_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) T) := by
  simpa using
    heatShearTransportFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1)
      (by simp) (by positivity) hT

theorem heat_shear_transport_full_drift_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) hν (by simp) hT

theorem heat_shear_transport_full_drift_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_transport_full_drift_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_transport_full_drift_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportFullDriftInitialVelocity 1 1 1 1 1
          smooth_initial := smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity 1 1 1 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity 1 1 1 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_heatShearTransportFullDriftInitialVelocity
      (ν := ν) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) hν (by simp)

theorem heat_shear_transport_full_drift_BKM_candidate_gap_regression
    {T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness 1
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) T) := by
  simpa using
    heatShearTransportFullDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := 1) (T := T) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1)
      (by simp) (by positivity) hT

theorem heat_shear_transport_full_drift_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact
    ExplicitBKMContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) hν (by simp) hT

theorem heat_shear_transport_full_drift_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity 1 1 1 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_heatShearTransportFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (k := 1) (b := 1) (d := 1) (c := 1) hν (by simp)

end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
