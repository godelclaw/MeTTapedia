import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityLinearShearFiniteWitnesses

/-!
# Uniform-vorticity continuation regression: constant and linear-shear exactness checks.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesUniformVorticityContinuationTargetRegression

theorem constant_initial_velocity_global_output_exact_regression
    {ν : ℝ} {c : NSSpace} :
    ExplicitConcreteNavierStokesGlobalOutput ν (constantInitialVelocity c) ↔ c = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff

theorem constant_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {c : NSSpace} :
    ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) ↔ c = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity_iff hν

theorem constant_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {c : NSSpace} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := constantInitialVelocity c
          smooth_initial := smoothInitialVelocityData_constantInitialVelocity c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_constantInitialVelocity c x } ↔
      c = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_constantInitialVelocity_iff hν

theorem constant_initial_velocity_finite_initial_energy_exact_regression
    {c : NSSpace} :
    finiteInitialKineticEnergy (constantInitialVelocity c) ↔ c = 0 := by
  exact finiteInitialKineticEnergy_constantInitialVelocity_iff

theorem linear_shear_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν (linearShearInitialVelocity a) ↔ a = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity_iff

theorem linear_shear_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) ↔ a = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity_iff hν

theorem linear_shear_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearInitialVelocity a
          smooth_initial := smoothInitialVelocityData_linearShearInitialVelocity a
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearInitialVelocity a x } ↔
      a = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_linearShearInitialVelocity_iff hν

theorem linear_shear_full_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a b c : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearFullDriftInitialVelocity a b c) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity_iff

theorem linear_shear_full_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a b c : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearFullDriftInitialVelocity a b c) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_iff hν

theorem linear_shear_full_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a b c : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearFullDriftInitialVelocity a b c
          smooth_initial := smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x } ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity_iff hν

theorem linear_shear_initial_velocity_finite_initial_energy_exact_regression
    {a : ℝ} :
    finiteInitialKineticEnergy (linearShearInitialVelocity a) ↔
      a = 0 := by
  exact finiteInitialKineticEnergy_linearShearInitialVelocity_iff

theorem linear_shear_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (linearShearInitialVelocity a) T) ↔
      a = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity_iff hT

theorem linear_shear_vertical_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a b : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearVerticalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_linearShearVerticalDriftInitialVelocity_iff

theorem linear_shear_vertical_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a b : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearVerticalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity_iff hν

theorem linear_shear_vertical_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a b : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearVerticalDriftInitialVelocity a b
          smooth_initial := smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity a b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearVerticalDriftInitialVelocity a b x } ↔
      a = 0 ∧ b = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_linearShearVerticalDriftInitialVelocity_iff hν

theorem linear_shear_vertical_drift_initial_velocity_finite_initial_energy_exact_regression
    {a b : ℝ} :
    finiteInitialKineticEnergy (linearShearVerticalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  exact finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity_iff

theorem linear_shear_vertical_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a b : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (linearShearVerticalDriftInitialVelocity a b) T) ↔
      a = 0 ∧ b = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity_iff hT

theorem linear_shear_horizontal_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a b : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearHorizontalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_linearShearHorizontalDriftInitialVelocity_iff

theorem linear_shear_horizontal_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a b : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearHorizontalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity_iff hν

theorem linear_shear_horizontal_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a b : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearHorizontalDriftInitialVelocity a b
          smooth_initial := smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity a b x } ↔
      a = 0 ∧ b = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_linearShearHorizontalDriftInitialVelocity_iff hν

theorem linear_shear_horizontal_drift_initial_velocity_finite_initial_energy_exact_regression
    {a b : ℝ} :
    finiteInitialKineticEnergy (linearShearHorizontalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  exact finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity_iff

theorem linear_shear_horizontal_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a b : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (linearShearHorizontalDriftInitialVelocity a b) T) ↔
      a = 0 ∧ b = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity_iff hT

theorem linear_shear_full_drift_initial_velocity_finite_initial_energy_exact_regression
    {a b c : ℝ} :
    finiteInitialKineticEnergy (linearShearFullDriftInitialVelocity a b c) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  exact finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_iff

theorem linear_shear_full_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a b c : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (linearShearFullDriftInitialVelocity a b c) T) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity_iff hT

end NavierStokesUniformVorticityContinuationTargetRegression
end NavierStokes
end FluidDynamics
end Mettapedia
