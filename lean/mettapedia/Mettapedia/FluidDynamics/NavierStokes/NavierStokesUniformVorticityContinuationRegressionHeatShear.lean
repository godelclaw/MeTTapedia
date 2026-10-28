import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityZeroWitness

/-!
# Uniform-vorticity continuation regression: heat-shear exactness checks.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesUniformVorticityContinuationTargetRegression

theorem heat_shear_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a k : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearInitialVelocity a k) ↔
      a * k = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_heatShearInitialVelocity_iff

theorem heat_shear_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearInitialVelocity a k) ↔
      a * k = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity_iff hν

theorem heat_shear_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearInitialVelocity a k
          smooth_initial := smoothInitialVelocityData_heatShearInitialVelocity a k
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearInitialVelocity a k x } ↔
      a * k = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_heatShearInitialVelocity_iff hν

theorem heat_shear_initial_velocity_finite_initial_energy_exact_regression
    {a k : ℝ} :
    finiteInitialKineticEnergy (heatShearInitialVelocity a k) ↔
      a * k = 0 := by
  exact finiteInitialKineticEnergy_heatShearInitialVelocity_iff

theorem heat_shear_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a k : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearInitialVelocity a k) T) ↔
      a * k = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity_iff hT

theorem heat_shear_streamwise_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a k d : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearStreamwiseDriftInitialVelocity a k d) ↔
      d = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_heatShearStreamwiseDriftInitialVelocity_iff

theorem heat_shear_streamwise_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k d : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearStreamwiseDriftInitialVelocity a k d) ↔
      d = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity_iff hν

theorem heat_shear_streamwise_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k d : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearStreamwiseDriftInitialVelocity a k d
          smooth_initial := smoothInitialVelocityData_heatShearStreamwiseDriftInitialVelocity a k d
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearStreamwiseDriftInitialVelocity a k d x } ↔
      d = 0 ∧ a * k = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_heatShearStreamwiseDriftInitialVelocity_iff hν

theorem heat_shear_streamwise_drift_initial_velocity_finite_initial_energy_exact_regression
    {a k d : ℝ} :
    finiteInitialKineticEnergy (heatShearStreamwiseDriftInitialVelocity a k d) ↔
      d = 0 ∧ a * k = 0 := by
  exact finiteInitialKineticEnergy_heatShearStreamwiseDriftInitialVelocity_iff

theorem heat_shear_streamwise_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a k d : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearStreamwiseDriftInitialVelocity a k d) T) ↔
      d = 0 ∧ a * k = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_heatShearStreamwiseDriftInitialVelocity_iff hT

theorem heat_shear_vertical_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a k c : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearVerticalDriftInitialVelocity a k c) ↔
      c = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_heatShearVerticalDriftInitialVelocity_iff

theorem heat_shear_vertical_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k c : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearVerticalDriftInitialVelocity a k c) ↔
      c = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity_iff hν

theorem heat_shear_vertical_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k c : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearVerticalDriftInitialVelocity a k c
          smooth_initial := smoothInitialVelocityData_heatShearVerticalDriftInitialVelocity a k c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearVerticalDriftInitialVelocity a k c x } ↔
      c = 0 ∧ a * k = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_heatShearVerticalDriftInitialVelocity_iff hν

theorem heat_shear_vertical_drift_initial_velocity_finite_initial_energy_exact_regression
    {a k c : ℝ} :
    finiteInitialKineticEnergy (heatShearVerticalDriftInitialVelocity a k c) ↔
      c = 0 ∧ a * k = 0 := by
  exact finiteInitialKineticEnergy_heatShearVerticalDriftInitialVelocity_iff

theorem heat_shear_vertical_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a k c : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearVerticalDriftInitialVelocity a k c) T) ↔
      c = 0 ∧ a * k = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_heatShearVerticalDriftInitialVelocity_iff hT

theorem heat_shear_full_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a k d c : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearFullDriftInitialVelocity a k d c) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff

theorem heat_shear_full_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k d c : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearFullDriftInitialVelocity a k d c) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_iff hν

theorem heat_shear_full_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k d c : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearFullDriftInitialVelocity a k d c
          smooth_initial := smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x } ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_heatShearFullDriftInitialVelocity_iff hν

theorem heat_shear_full_drift_initial_velocity_finite_initial_energy_exact_regression
    {a k d c : ℝ} :
    finiteInitialKineticEnergy (heatShearFullDriftInitialVelocity a k d c) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity_iff

theorem heat_shear_full_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a k d c : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearFullDriftInitialVelocity a k d c) T) ↔
      d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_heatShearFullDriftInitialVelocity_iff hT

theorem heat_shear_transport_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a k b : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearTransportInitialVelocity a k b) ↔
      b = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportInitialVelocity_iff

theorem heat_shear_transport_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k b : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportInitialVelocity a k b) ↔
      b = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_heatShearTransportInitialVelocity_iff hν

theorem heat_shear_transport_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k b : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportInitialVelocity a k b
          smooth_initial := smoothInitialVelocityData_heatShearTransportInitialVelocity a k b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportInitialVelocity a k b x } ↔
      b = 0 ∧ a * k = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_heatShearTransportInitialVelocity_iff hν

theorem heat_shear_transport_initial_velocity_finite_initial_energy_exact_regression
    {a k b : ℝ} :
    finiteInitialKineticEnergy (heatShearTransportInitialVelocity a k b) ↔
      b = 0 ∧ a * k = 0 := by
  exact finiteInitialKineticEnergy_heatShearTransportInitialVelocity_iff

theorem heat_shear_transport_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a k b : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearTransportInitialVelocity a k b) T) ↔
      b = 0 ∧ a * k = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportInitialVelocity_iff hT

theorem heat_shear_transport_full_drift_initial_velocity_global_output_exact_regression
    {ν : ℝ} {a k b d c : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (heatShearTransportFullDriftInitialVelocity a k b d c) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity_iff

theorem heat_shear_transport_full_drift_initial_velocity_regularity_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k b d c : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (heatShearTransportFullDriftInitialVelocity a k b d c) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact ExplicitConcreteNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_iff hν

theorem heat_shear_transport_full_drift_initial_velocity_concrete_clause_exact_regression
    {ν : ℝ} (hν : 0 < ν) {a k b d c : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearTransportFullDriftInitialVelocity a k b d c
          smooth_initial := smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x } ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact concreteNavierStokesGlobalRegularityClause_heatShearTransportFullDriftInitialVelocity_iff hν

theorem heat_shear_transport_full_drift_initial_velocity_finite_initial_energy_exact_regression
    {a k b d c : ℝ} :
    finiteInitialKineticEnergy (heatShearTransportFullDriftInitialVelocity a k b d c) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity_iff

theorem heat_shear_transport_full_drift_initial_velocity_nonempty_witness_exact_regression
    {ν T : ℝ} (hT : 0 ≤ T) {a k b d c : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (heatShearTransportFullDriftInitialVelocity a k b d c) T) ↔
      b = 0 ∧ d = 0 ∧ c = 0 ∧ a * k = 0 := by
  exact nonempty_ExplicitFiniteTimeRegularityWitness_heatShearTransportFullDriftInitialVelocity_iff hT

end NavierStokesUniformVorticityContinuationTargetRegression
end NavierStokes
end FluidDynamics
end Mettapedia
