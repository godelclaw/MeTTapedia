import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityRepairedFiniteEnergyWitnesses

/-!
# Uniform-vorticity continuation regression: repaired finite-energy clause checks.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesUniformVorticityContinuationTargetRegression

theorem constant_initial_velocity_repaired_clause_unconditional_regression
    {ν : ℝ} {c : NSSpace} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (constantInitialVelocity c) := by
  exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_constantInitialVelocity_all

theorem linear_shear_full_drift_initial_velocity_repaired_clause_unconditional_regression
    {ν : ℝ} {a b c : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearFullDriftInitialVelocity a b c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_all

theorem heat_shear_full_drift_initial_velocity_repaired_clause_unconditional_regression
    {ν : ℝ} {a k d c : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearFullDriftInitialVelocity a k d c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_all

theorem heat_shear_transport_full_drift_initial_velocity_repaired_clause_unconditional_regression
    {ν : ℝ} {a k b d c : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_all

theorem constant_initial_velocity_repaired_structured_clause_unconditional_regression
    {ν : ℝ} (hν : 0 < ν) {c : NSSpace}
    (hfinite : finiteInitialKineticEnergy (constantInitialVelocity c)) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := constantInitialVelocity c
         smooth_initial := smoothInitialVelocityData_constantInitialVelocity c
         divergence_free_initial := by
           intro x
           simpa using initialSpatialDivergence_constantInitialVelocity c x
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_constantInitialVelocity_all
      hν hfinite

theorem linear_shear_full_drift_initial_velocity_repaired_structured_clause_unconditional_regression
    {ν : ℝ} (hν : 0 < ν) {a b c : ℝ}
    (hfinite : finiteInitialKineticEnergy (linearShearFullDriftInitialVelocity a b c)) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := linearShearFullDriftInitialVelocity a b c
         smooth_initial := smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c
         divergence_free_initial := by
           intro x
           simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity_all
      hν hfinite

theorem heat_shear_full_drift_initial_velocity_repaired_structured_clause_unconditional_regression
    {ν : ℝ} (hν : 0 < ν) {a k d c : ℝ}
    (hfinite : finiteInitialKineticEnergy (heatShearFullDriftInitialVelocity a k d c)) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := heatShearFullDriftInitialVelocity a k d c
         smooth_initial := smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c
         divergence_free_initial := by
           intro x
           simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_heatShearFullDriftInitialVelocity_all
      hν hfinite

theorem heat_shear_transport_full_drift_initial_velocity_repaired_structured_clause_unconditional_regression
    {ν : ℝ} (hν : 0 < ν) {a k b d c : ℝ}
    (hfinite : finiteInitialKineticEnergy (heatShearTransportFullDriftInitialVelocity a k b d c)) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := heatShearTransportFullDriftInitialVelocity a k b d c
         smooth_initial := smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c
         divergence_free_initial := by
           intro x
           simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_heatShearTransportFullDriftInitialVelocity_all
      hν hfinite

end NavierStokesUniformVorticityContinuationTargetRegression
end NavierStokes
end FluidDynamics
end Mettapedia
