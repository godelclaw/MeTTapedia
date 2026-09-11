import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootEnvelope

/-! Shared exceptional sets, zero ratio, and simultaneous dyadic envelope regressions. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureEnvelopeAudit

open MeasureTheory FrequencyPairPeriodization FrequencyPairEnvelope
open PressureDyadicEnvelope PressurePeriodicEnvelope PressureDyadicPeriodization
open PressureLowOutputDyadicBudget

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The same exceptional set works for an uncountable interval of imaginary amplitudes. -/
example (H : E6 → ℝ) (hn : ∀ x, 0 ≤ H x) (hm : Measurable H) (hi : Integrable H) :
    ∀ᵐ q : T6, ∀ a : ℝ, |a| ≤ 1 →
      ‖periodize (fun x ↦ (a : ℂ) * Complex.I * (H x : ℂ)) q‖ ≤ periodize H q := by
  have hb (a : {a : ℝ // |a| ≤ 1}) (x : E6) :
      ‖(a.1 : ℂ) * Complex.I * (H x : ℂ)‖ ≤ H x := by
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hn x)]
    exact (mul_le_mul_of_nonneg_right a.2 (hn x)).trans_eq (one_mul _)
  have h := ae_norm_periodize_family_le
    (fun a : {a : ℝ // |a| ≤ 1} ↦ fun x ↦ (a.1 : ℂ) * Complex.I * (H x : ℂ)) H hn hm hi hb
  filter_upwards [h] with q hq a ha
  exact hq ⟨a, ha⟩

example (H : E6 → ℝ) : physicalEnvelope H 0 = 0 := by
  simp [physicalEnvelope, PressureLowOutputCutoff.ratio]

example (H : E6 → ℝ) (N : ℝ) (hN : 0 < N) : scaledEnvelope H N hN 0 = 0 := by
  ext x
  simp [scaledEnvelope, physicalEnvelope, PressureLowOutputCutoff.ratio,
    Mettapedia.Analysis.DensityLinearChange.pullbackDensity]

/-- Both infinite band choice and the full unit sphere occur after the almost-everywhere quantifier. -/
example (N : ℝ) (hN : 0 < N) :
    ∃ M : ℕ → T6 → ℝ,
      (∀ᵐ q : T6, ∀ n : ℕ, ∀ e : R3, ‖e‖ = 1 →
        ‖periodicKernel N hN (dyadicParameter n) e q‖ ≤ M n q) ∧
      Summable (fun n ↦ ∫ q : T6, M n q) := by
  obtain ⟨_C0, _C1, _hC0, _hC1, M, h⟩ := exists_uniform_dyadic_envelope
  exact ⟨M N hN, (h N hN).2.1, (h N hN).2.2.1⟩

end Mettapedia.FluidDynamics.NavierStokes.PressureEnvelopeAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairEnvelope.periodize_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairEnvelope.ae_summable_envelope_orbit
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairEnvelope.ae_norm_periodize_family_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairEnvelope.integrable_moment_periodize
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairEnvelope.integral_moment_periodize_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.exists_basis_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.physicalEnvelope_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.continuous_physicalEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.integrable_physicalEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.mass_physicalEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.norm_physicalKernel_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.norm_scaledKernel_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.integrable_moment_physicalEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.firstMoment_physicalEnvelope_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.mass_scaledEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.firstMoment_scaledEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.norm_operatorKernel_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicEnvelope.exists_uniform_operator_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePeriodicEnvelope.exists_uniform_periodic_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePeriodicEnvelope.exists_uniform_dyadic_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootEnvelope.ae_sum_norm_rootLocalizationIntegrand_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootEnvelope.exists_uniform_rootLocalization_envelope
