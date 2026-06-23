import Mettapedia.FluidDynamics.NavierStokes.ContinuationRegressionCounterexamplesBasic
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMInitialVelocityExamplesConstant
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMInitialVelocityExamplesAffineShear
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMInitialVelocityExamplesHeatShear
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMCandidatesConstant
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMCandidatesAffineShear
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMCandidatesHeatShear
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMCandidatesEnvelopeOperations
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityConstantContinuation

/-!
# Affine-Shear Continuation Counterexample Regressions

This module checks linear, vertical-drift, horizontal-drift, and full-drift
affine-shear repaired regularity, uniform-vorticity, and BKM counterexamples.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression

theorem linear_shear_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearInitialVelocity 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearInitialVelocity_without_regularity
      (ν := ν) hν (by simp)

theorem affine_shear_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (b := 1) hν (by simp)

theorem horizontal_affine_shear_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (b := 1) hν (by simp)

theorem constant_velocity_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := constantInitialVelocity nonzeroConstantVelocity
          smooth_initial := smoothInitialVelocityData_constantInitialVelocity
            nonzeroConstantVelocity
          divergence_free_initial := by
            intro x
            simpa using
              initialSpatialDivergence_constantInitialVelocity
                nonzeroConstantVelocity x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_constantInitialVelocity
      (ν := ν) hν nonzeroConstantVelocity_ne_zero

theorem linear_shear_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearInitialVelocity 1
          smooth_initial := smoothInitialVelocityData_linearShearInitialVelocity 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearInitialVelocity 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_linearShearInitialVelocity
      (ν := ν) hν (by simp)

theorem affine_shear_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearVerticalDriftInitialVelocity 1 1
          smooth_initial := smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearVerticalDriftInitialVelocity 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_linearShearVerticalDriftInitialVelocity
      (ν := ν) hν (by simp)

theorem horizontal_affine_shear_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearHorizontalDriftInitialVelocity 1 1
          smooth_initial := smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_linearShearHorizontalDriftInitialVelocity
      (ν := ν) hν (by simp)

theorem constant_velocity_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (constantInitialVelocity nonzeroConstantVelocity) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (constantInitialVelocity nonzeroConstantVelocity) := by
  exact
    ExplicitUniformVorticityContinuationClause_constantInitialVelocity_without_regularity
      (ν := ν) (T := T) hν nonzeroConstantVelocity_ne_zero hT

theorem constant_velocity_uniform_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity nonzeroConstantVelocity) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν
          (constantInitialVelocity nonzeroConstantVelocity) T) := by
  exact
    constantInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) nonzeroConstantVelocity_ne_zero hT

theorem constant_velocity_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (constantInitialVelocity nonzeroConstantVelocity) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (constantInitialVelocity nonzeroConstantVelocity) := by
  exact
    ExplicitBKMContinuationClause_constantInitialVelocity_without_regularity
      (ν := ν) (T := T) hν nonzeroConstantVelocity_ne_zero hT

theorem constant_velocity_BKM_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity nonzeroConstantVelocity) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν
          (constantInitialVelocity nonzeroConstantVelocity) T) := by
  exact
    constantInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) nonzeroConstantVelocity_ne_zero hT

theorem constant_velocity_time_only_pressure_BKM_candidate_gap_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ 1 →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          (1 : ℝ) • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ 1 → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity nonzeroConstantVelocity) u ∧
      vorticityEnvelopeOn u 1 (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) 1 (1 * B) ∧
      ¬ boundedKineticEnergyUpTo u 1) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness 1 (constantInitialVelocity nonzeroConstantVelocity) 1) := by
  exact
    constantInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
      (ν := 1) (T := 1)
      nonzeroConstantVelocity_ne_zero
      (by norm_num)
      (fun t : NSTime => fun _ : NSSpace => t + 1)
      (smoothSpaceTimePressure_timeOnly (by simpa using
        (contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun s : NSTime => s + 1))))
      (fun t x => spatialPressureGradient_timeOnly (fun s : NSTime => s + 1) t x)

theorem linear_shear_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (linearShearInitialVelocity 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_linearShearInitialVelocity_without_regularity
      (ν := ν) (T := T) hν (by simp) hT

theorem linear_shear_uniform_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (linearShearInitialVelocity 1) T) := by
  exact
    linearShearInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (by simp) hT

theorem linear_shear_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearInitialVelocity 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity 1) := by
  exact
    ExplicitBKMContinuationClause_linearShearInitialVelocity_without_regularity
      (ν := ν) (T := T) hν (by simp) hT

theorem linear_shear_BKM_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearInitialVelocity 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (linearShearInitialVelocity 1) T) := by
  exact
    linearShearInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (by simp) hT

theorem affine_shear_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp) hT

theorem affine_shear_uniform_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearVerticalDriftInitialVelocity 1 1) T) := by
  exact
    linearShearVerticalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (b := 1) (by simp) hT

theorem affine_shear_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearVerticalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) := by
  exact
    ExplicitBKMContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp) hT

theorem affine_shear_BKM_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearVerticalDriftInitialVelocity 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearVerticalDriftInitialVelocity 1 1) T) := by
  exact
    linearShearVerticalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (b := 1) (by simp) hT

theorem horizontal_affine_shear_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp) hT

theorem horizontal_affine_shear_uniform_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity 1 1) T) := by
  exact
    linearShearHorizontalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (b := 1) (by simp) hT

theorem horizontal_affine_shear_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearHorizontalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) := by
  exact
    ExplicitBKMContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp) hT

theorem horizontal_affine_shear_BKM_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearHorizontalDriftInitialVelocity 1 1) T) := by
  exact
    linearShearHorizontalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (b := 1) (by simp) hT

theorem horizontal_affine_shear_time_only_pressure_uniform_candidate_gap_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ 1 →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          (1 : ℝ) • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ 1 → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity 1 1) u ∧
      uniformVorticityBoundUpTo u 1 B ∧
      ¬ boundedKineticEnergyUpTo u 1) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness 1 (linearShearHorizontalDriftInitialVelocity 1 1) 1) := by
  exact
    linearShearHorizontalDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness_addTimeOnlyPressure
      (ν := 1) (T := 1) (a := 1) (b := 1) (by simp) (by norm_num)
      (fun s : NSTime => s + 1)
      (by simpa using
        (contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun s : NSTime => s + 1)))

theorem horizontal_affine_shear_time_only_pressure_BKM_candidate_gap_regression :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ 1 →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          (1 : ℝ) • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ 1 → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearHorizontalDriftInitialVelocity 1 1) u ∧
      vorticityEnvelopeOn u 1 (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) 1 (1 * B) ∧
      ¬ boundedKineticEnergyUpTo u 1) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness 1 (linearShearHorizontalDriftInitialVelocity 1 1) 1) := by
  exact
    linearShearHorizontalDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness_addTimeOnlyPressure
      (ν := 1) (T := 1) (a := 1) (b := 1) (by simp) (by norm_num)
      (fun s : NSTime => s + 1)
      (by simpa using
        (contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun s : NSTime => s + 1)))

theorem constant_velocity_repaired_uniform_clause_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (constantInitialVelocity nonzeroConstantVelocity) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_constantInitialVelocity
      (ν := ν) (T := T) nonzeroConstantVelocity_ne_zero

theorem constant_velocity_repaired_BKM_clause_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause
      ν (constantInitialVelocity nonzeroConstantVelocity) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_constantInitialVelocity
      (ν := ν) (T := T) nonzeroConstantVelocity_ne_zero

theorem linear_shear_repaired_uniform_clause_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (linearShearInitialVelocity 1) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearInitialVelocity
      (ν := ν) (T := T) (by simp)

theorem linear_shear_repaired_BKM_clause_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν (linearShearInitialVelocity 1) T := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_linearShearInitialVelocity
      (ν := ν) (T := T) (by simp)

theorem constant_velocity_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (constantInitialVelocity nonzeroConstantVelocity) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (constantInitialVelocity nonzeroConstantVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_constantInitialVelocity_without_regularity
      (ν := ν) (T := T) hν nonzeroConstantVelocity_ne_zero

theorem constant_velocity_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (constantInitialVelocity nonzeroConstantVelocity) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (constantInitialVelocity nonzeroConstantVelocity) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_constantInitialVelocity_without_regularity
      (ν := ν) (T := T) hν nonzeroConstantVelocity_ne_zero

theorem linear_shear_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearInitialVelocity 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearInitialVelocity 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearInitialVelocity_without_regularity
      (ν := ν) (T := T) hν (by simp)

theorem linear_shear_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (linearShearInitialVelocity 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearInitialVelocity 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_linearShearInitialVelocity_without_regularity
      (ν := ν) (T := T) hν (by simp)

theorem affine_shear_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp)

theorem affine_shear_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_linearShearVerticalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp)

theorem horizontal_affine_shear_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp)

theorem horizontal_affine_shear_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_linearShearHorizontalDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) hν (by simp)

theorem full_drift_affine_shear_repaired_regularity_without_regularity_regression
    {ν : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (a := 1) (b := 1) (c := 1) hν (by simp)

theorem full_drift_affine_shear_structured_clause_false_regression
    {ν : ℝ} (hν : 0 < ν) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearFullDriftInitialVelocity 1 1 1
          smooth_initial := smoothInitialVelocityData_linearShearFullDriftInitialVelocity 1 1 1
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity 1 1 1 x } := by
  exact
    not_concreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity
      (ν := ν) hν (by simp)

theorem full_drift_affine_shear_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) (c := 1) hν (by simp) hT

theorem full_drift_affine_shear_uniform_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity 1 1 1) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearFullDriftInitialVelocity 1 1 1) T) := by
  exact
    linearShearFullDriftInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (b := 1) (c := 1) (by simp) hT

theorem full_drift_affine_shear_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ExplicitBKMContinuationClause ν (linearShearFullDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitBKMContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) (c := 1) hν (by simp) hT

theorem full_drift_affine_shear_BKM_candidate_gap_regression
    {ν T : ℝ} (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (linearShearFullDriftInitialVelocity 1 1 1) u ∧
      vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty
        (ExplicitFiniteTimeRegularityWitness ν (linearShearFullDriftInitialVelocity 1 1 1) T) := by
  exact
    linearShearFullDriftInitialVelocity_exhibits_BKMCandidate_without_finiteTimeWitness
      (ν := ν) (T := T) (a := 1) (b := 1) (c := 1) (by simp) hT

theorem full_drift_affine_shear_repaired_uniform_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) (c := 1) hν (by simp)

theorem full_drift_affine_shear_repaired_BKM_clause_without_regularity_regression
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitFiniteEnergyBKMContinuationClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity 1 1 1) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_linearShearFullDriftInitialVelocity_without_regularity
      (ν := ν) (T := T) (a := 1) (b := 1) (c := 1) hν (by simp)

theorem linear_shear_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearVelocityField 1) t x +
        spatialConvection (linearShearVelocityField 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (linearShearVelocityField 1) t x := by
  simpa using momentumEquation_linearShearVelocityField_zeroPressure 1 1 t x

theorem linear_shear_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (linearShearVelocityField 1) T 1 := by
  simpa using uniformVorticityBoundUpTo_linearShearVelocityField 1 T

theorem linear_shear_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearVelocityField 1) T (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using linearShearVelocityField_has_constantBKMEnvelope 1 T hT

theorem affine_shear_zero_pressure_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearVerticalDriftVelocityField 1 1) t x +
        spatialConvection (linearShearVerticalDriftVelocityField 1 1) t x +
        spatialPressureGradient (0 : NSPressureField) t x =
      spatialLaplacian (linearShearVerticalDriftVelocityField 1 1) t x := by
  simpa using momentumEquation_linearShearVerticalDriftVelocityField_zeroPressure 1 1 1 t x

theorem affine_shear_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (linearShearVerticalDriftVelocityField 1 1) T 1 := by
  simpa using uniformVorticityBoundUpTo_linearShearVerticalDriftVelocityField 1 1 T

theorem affine_shear_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearVerticalDriftVelocityField 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using linearShearVerticalDriftVelocityField_has_constantBKMEnvelope 1 1 T hT

theorem horizontal_affine_shear_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearHorizontalDriftVelocityField 1 1) t x +
        spatialConvection (linearShearHorizontalDriftVelocityField 1 1) t x +
        spatialPressureGradient (linearShearHorizontalDriftPressureField 1 1) t x =
      spatialLaplacian (linearShearHorizontalDriftVelocityField 1 1) t x := by
  simpa using momentumEquation_linearShearHorizontalDriftVelocityField 1 1 1 t x

theorem horizontal_affine_shear_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (linearShearHorizontalDriftVelocityField 1 1) T 1 := by
  simpa using uniformVorticityBoundUpTo_linearShearHorizontalDriftVelocityField 1 1 T

theorem horizontal_affine_shear_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearHorizontalDriftVelocityField 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using linearShearHorizontalDriftVelocityField_has_constantBKMEnvelope 1 1 T hT

theorem full_drift_affine_shear_momentum_regression
    (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (linearShearFullDriftVelocityField 1 1 1) t x +
        spatialConvection (linearShearFullDriftVelocityField 1 1 1) t x +
        spatialPressureGradient (linearShearHorizontalDriftPressureField 1 1) t x =
      spatialLaplacian (linearShearFullDriftVelocityField 1 1 1) t x := by
  simpa using momentumEquation_linearShearFullDriftVelocityField 1 1 1 1 t x

theorem full_drift_affine_shear_uniform_bound_regression
    (T : ℝ) :
    uniformVorticityBoundUpTo (linearShearFullDriftVelocityField 1 1 1) T 1 := by
  simpa using uniformVorticityBoundUpTo_linearShearFullDriftVelocityField 1 1 1 T

theorem full_drift_affine_shear_BKM_envelope_regression
    {T : ℝ} (hT : 0 ≤ T) :
    vorticityEnvelopeOn (linearShearFullDriftVelocityField 1 1 1) T
        (fun _ : NSTime => 1) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 1) T T := by
  simpa using linearShearFullDriftVelocityField_has_constantBKMEnvelope 1 1 1 T hT

end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
