import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTiltFreezing

/-! Regression and axiom audit for pressure energy and direction freezing. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPressureEnergyAudit

open MeasureTheory PeriodicFourierTriad PancakeAnisotropyDepletion LocalPressureCommutator
open FourierPressureTiltEnergy FourierPressureTiltFreezing SpectralTiltFreezing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (e : R3) : lineDistanceSq e e = 0 := by simp [lineDistanceSq]

example (e : R3) : lineDistanceSq e (-e) = 0 := by simp [lineDistanceSq]

example (R : R3 →L[ℝ] R3) (e : R3) :
    ‖lineRemainder (-e) (R (-e))‖ = ‖lineRemainder e (R e)‖ := by
  rw [transverse_action_neg, norm_neg]

example (outputs : Finset Wavevector) (u : FourierVelocity) :
    hessianEnergy (fun _ ↦ 0) outputs u = 0 := by simp [hessianEnergy, pressureAmplitude]

example (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity)
    (e : R3) (he : ‖e‖ = 1) :
    (∫ x : T3, ‖lineRemainder e (filteredPressureOperator chi outputs u x e)‖ ^ 2) ≤
      (1 / 4 : ℝ) * hessianEnergy chi outputs u :=
  (integral_transverse_pressure_sq_le_angularEnergy chi outputs u e).trans
    (angularEnergy_le_quarter_hessianEnergy chi outputs u e he)

end Mettapedia.FluidDynamics.NavierStokes.FourierPressureEnergyAudit

#print axioms ContinuousLinearMap.norm_apply_sq_le_sum_orthonormalBasis
#print axioms ContinuousLinearMap.norm_sq_le_sum_orthonormalBasis
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltFreezing.abs_rayleigh_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltFreezing.norm_transverse_action_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltFreezing.norm_transverse_action_sq_le_frozen
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltFreezing.transverse_action_neg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltFreezing.norm_transverse_action_sq_le_lineDistance
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltEnergy.coefficientEnergy_real_multiple
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltEnergy.coefficientEnergy_tiltCoefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltEnergy.fullEnergy_tiltCoefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltEnergy.transverse_pressure_eq_real_reconstruction
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltEnergy.continuous_transverse_pressure
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltEnergy.integral_transverse_pressure_sq_le_angularEnergy
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltEnergy.angularEnergy_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltEnergy.angularEnergy_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltEnergy.angularEnergy_le_quarter_hessianEnergy
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltEnergy.angularEnergy_le_of_longitudinal_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureHessianEnergy.fullEnergy_actionCoefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureHessianEnergy.pressure_apply_eq_real_reconstruction
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureHessianEnergy.integral_pressure_apply_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureHessianEnergy.sum_actionEnergy_orthonormalBasis
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureHessianEnergy.continuous_filteredPressureOperator
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureHessianEnergy.integrable_pressure_norm_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureHessianEnergy.integral_pressure_norm_sq_le_hessianEnergy
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltFreezing.norm_variable_transverse_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltFreezing.aestronglyMeasurable_variable_transverse
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltFreezing.integrable_variable_transverse_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltFreezing.integral_variable_transverse_sq_le_hessianEnergy
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltFreezing.integral_variable_transverse_sq_le_frozen
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltFreezing.integral_variable_transverse_sq_le_of_cone
