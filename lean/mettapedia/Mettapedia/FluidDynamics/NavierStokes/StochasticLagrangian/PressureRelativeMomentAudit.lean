import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentRelativeMoment

/-! Checks for common-translation cancellation and relative kernel moments. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureRelativeMomentAudit

open MeasureTheory FrequencyPairPeriodization PressureCoherentRelativeMoment
open PressureLowOutputSymbol (pairEquiv)
open PressureCoherentDivergenceEnvelope (physicalEnvelope scaledEnvelope)
open PressureLowOutputCutoff (ratio)
open PancakeBilinearPeriodization (firstTorusDisplacement secondTorusDisplacement)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- An arbitrarily large common translation does not alter the separation. -/
example (v w : R3) : relativeDisplacement (pairEquiv.symm (v + w, w)) = v := by
  simp [relativeDisplacement]

/-- Equal input displacements also cancel after passing to the quotient. -/
example (w : R3) :
    relativeTorusDisplacement (torusProjection (pairEquiv.symm (w, w))) = 0 := by
  rw [relativeTorusDisplacement_projection]
  ext i
  simp [relativeDisplacement]

/-- The relative quotient norm has the half-period cap, not the sum of two caps. -/
example (q : T6) : ‖relativeTorusDisplacement q‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (norm_relativeTorusDisplacement_le_half q) 2

/-- The zero-output endpoint is included without dividing by the output ratio. -/
example (H : E6 → ℝ) (m : ℕ) :
    (∫ x : E6, ‖relativeDisplacement x‖ ^ m * physicalEnvelope H 0 x) = 0 := by
  rw [integral_relativeMoment_physicalEnvelope]
  simp [ratio]

/-- The second moment has inverse input scale squared and no inverse output ratio. -/
example (H : E6 → ℝ) (N : ℝ) (hN : 0 < N) (t : ℝ) :
    (∫ x : E6, ‖relativeDisplacement x‖ ^ 2 * scaledEnvelope H N hN t x) =
      |ratio t| / N ^ 2 * ∫ x : E6, ‖(pairEquiv x).1‖ ^ 2 * H x := by
  rw [integral_relativeMoment_scaledEnvelope]
  ring

/-- A constant field pays no separation cost, even for distinct input locations. -/
example {F : Type*} [NormedAddCommGroup F] (v : F) (M : T6 → ℝ) (x : T3) :
    (∫ q : T6, ‖(fun _ : T3 ↦ v) (x - firstTorusDisplacement q) -
      (fun _ : T3 ↦ v) (x - secondTorusDisplacement q)‖ ^ 2 * M q) = 0 := by
  simp

end Mettapedia.FluidDynamics.NavierStokes.PressureRelativeMomentAudit

#print axioms Mettapedia.Analysis.DensityLinearChange.integral_mul_pullbackDensity
#print axioms Mettapedia.Analysis.DensityLinearChange.integrable_mul_pullbackDensity
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.continuous_relativeDisplacement
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.continuous_relativeTorusDisplacement
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.relativeTorusDisplacement_projection
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.norm_relativeTorusDisplacement_projection_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.norm_relativeTorusDisplacement_le_half
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.lintegral_relativeMoment_periodize_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.integrable_relativeMoment_periodize
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.integral_relativeMoment_periodize_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.norm_translated_field_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.integrable_and_integral_translated_field_sub_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentRelativeMoment.relativeDisplacement_spatialChange_symm
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentRelativeMoment.relativeDisplacement_dilation_symm
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentRelativeMoment.integral_relativeMoment_physicalEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentRelativeMoment.integral_relativeMoment_scaledEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentRelativeMoment.integrable_firstCoordinateMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentRelativeMoment.integrable_relativeMoment_physicalEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentRelativeMoment.integrable_relativeMoment_scaledEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentRelativeMoment.exists_uniform_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentRelativeMoment.exists_uniform_periodic_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentRelativeMoment.exists_uniform_periodic_fieldDifference_bound
