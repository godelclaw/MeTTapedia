import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityEnergyObstructions
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearEnergyTransport

/-!
# Uniform-vorticity continuation regression: obstruction and wrapper checks.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesUniformVorticityContinuationTargetRegression

theorem finite_time_witness_pressure_residual_vorticity_zero_on_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialVorticity (momentumPressureResidual ν W.velocity) t x = 0 := by
  exact
    ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_zero_on
      (ν := ν) (T := T) (u₀ := u₀) W (t := t) (x := x) ht0 htT

theorem finite_time_witness_velocity_eq_pressure_residual_vorticity_zero_on_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hWvel : W.velocity = u)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    spatialVorticity (momentumPressureResidual ν u) t x = 0 := by
  exact
    ExplicitFiniteTimeRegularityWitness.spatialVorticity_momentumPressureResidual_of_velocity_eq_zero_on
      (ν := ν) (T := T) (u₀ := u₀) W hWvel (t := t) (x := x) ht0 htT

theorem finite_time_witness_velocity_residual_curl_obstruction_regression
    {ν T : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      0 ≤ t ∧ t ≤ T ∧
        spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ∃ W : ExplicitFiniteTimeRegularityWitness ν u₀ T,
      W.velocity = u := by
  exact
    not_exists_ExplicitFiniteTimeRegularityWitness_velocity_of_momentumPressureResidual_vorticity_ne_zero_on
      hcurl

theorem explicit_global_output_exists_velocity_wrapper_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ ↔
      ∃ u : NSVelocityField,
        ExplicitConcreteNavierStokesGlobalOutputWithVelocity ν u₀ u := by
  exact ExplicitConcreteNavierStokesGlobalOutput_iff_exists_velocity

theorem explicit_global_output_with_velocity_pressure_residual_vorticity_zero_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (h : ExplicitConcreteNavierStokesGlobalOutputWithVelocity ν u₀ u)
    (t : NSTime) (x : NSSpace) :
    spatialVorticity (momentumPressureResidual ν u) t x = 0 := by
  exact
    ExplicitConcreteNavierStokesGlobalOutputWithVelocity.spatialVorticity_momentumPressureResidual_zero
      (ν := ν) (u₀ := u₀) (u := u) h t x

theorem explicit_global_output_with_velocity_residual_curl_obstruction_regression
    {ν : ℝ} {u₀ : NSInitialVelocity} {u : NSVelocityField}
    (hcurl : ∃ t : NSTime, ∃ x : NSSpace,
      spatialVorticity (momentumPressureResidual ν u) t x ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutputWithVelocity ν u₀ u := by
  exact
    not_ExplicitConcreteNavierStokesGlobalOutputWithVelocity_of_momentumPressureResidual_vorticity_ne_zero
      hcurl

theorem generic_time_zero_nonintegrability_blocks_constant_field_bounded_energy_regression
    {c : NSSpace} (hc : c ≠ 0) :
    ¬ boundedKineticEnergy (constantVelocityField c) := by
  exact
    not_boundedKineticEnergy_of_not_integrable_kineticEnergyDensity_zero
      (u := constantVelocityField c)
      (not_integrable_kineticEnergyDensity_constantVelocityField hc 0)

theorem generic_time_zero_nonintegrability_blocks_constant_field_bounded_energy_up_to_regression
    {c : NSSpace} {T : ℝ}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (constantVelocityField c) T := by
  exact
    not_boundedKineticEnergyUpTo_of_not_integrable_kineticEnergyDensity_zero
      (u := constantVelocityField c)
      (not_integrable_kineticEnergyDensity_constantVelocityField hc 0)
      hT

theorem generic_nonfinite_initial_energy_blocks_transport_full_drift_bounded_energy_up_to_regression
    {ν a k b d c T : ℝ}
    (hb : b ≠ 0)
    (hT : 0 ≤ T) :
    ¬ boundedKineticEnergyUpTo (heatShearTransportFullDriftVelocityField ν a k b d c) T := by
  exact
    not_boundedKineticEnergyUpTo_of_matchesInitialVelocity_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c)
      (u := heatShearTransportFullDriftVelocityField ν a k b d c)
      (not_finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity hb)
      hT
      (matchesInitialVelocity_heatShearTransportFullDriftVelocityField ν a k b d c)

end NavierStokesUniformVorticityContinuationTargetRegression
end NavierStokes
end FluidDynamics
end Mettapedia
