import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentChannelAction

/-! Channel count, phase, zero-ratio, normalization, and uniform-envelope checks. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelAudit

open MeasureTheory PressureCoherentDivergenceChannel
open PressureCoherentDivergenceChannelKernel
open PressureCoherentDivergenceOperatorKernel
open PressureCoherentChannelEnvelopeBudget
open PressureLowOutputSymbol (pairEquiv)
open scoped SchwartzMap FourierTransform

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example : Fintype.card Factor = 7 := by decide

example (N : ℝ) (hN : 0 < N) (e : R3) (c : Factor) (i : Fin 3) :
    scaledKernel N hN (0, e) c i = 0 := by
  ext x
  simp [scaledKernel, physicalKernel, PressureLowOutputCutoff.ratio,
    Mettapedia.Analysis.SchwartzDilation.dilate, Mettapedia.Analysis.SchwartzLinearChange.pullback_apply]

example (e : R3) (he : ‖e‖ = 1) (i : Fin 3) : ‖outputOperator e i‖ = 1 :=
  norm_outputOperator_unit e he i

example (e : R3) (i : Fin 3) (u v : C3) :
    outputOperator e i (Complex.I • u) (Complex.I • v) = -outputOperator e i u v := by
  simp only [map_smul, smul_apply, smul_smul, Complex.I_mul_I, neg_one_smul]

example : scaledMultiplier 8 (.first 1)
    (WithLp.toLp 2 ![1, 16, 0], WithLp.toLp 2 ![0, 0, -24]) = 2 := by norm_num

example : scaledMultiplier 8 (.second 2)
    (WithLp.toLp 2 ![1, 16, 0], WithLp.toLp 2 ![0, 0, -24]) = -3 := by
  change (8⁻¹ * (-24) : ℝ) = -3
  norm_num

example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3)
    (ξ : EuclideanSpace ℝ (Fin 6)) :
    (𝓕 (operatorKernel N hN t e (.first j))) ξ =
      ((N⁻¹ * (pairEquiv ξ).1 j : ℝ) : ℂ) •
        (𝓕 (operatorKernel N hN t e .undifferentiated)) ξ := by
  simpa only [scaledMultiplier_first] using fourier_operatorKernel_factor N hN t e (.first j) ξ

-- The envelope is chosen before the arbitrary direction and channel families.
example : ∃ C : ℝ, 0 ≤ C ∧ ∃ M : (N : ℝ) → 0 < N → ℕ → ℕ → T6 → ℝ,
    ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : ℕ → ℕ → R3, (∀ j m, ‖e j m‖ = 1) →
      ∀ c : ℕ → ℕ → Factor,
      ∀ᵐ q : T6, ∀ j m,
        ‖matchedPeriodicKernel N hN j m (e j m) (c j m) q‖ ≤ M N hN j m q := by
  obtain ⟨C, hC, M, hb⟩ := exists_uniform_matched_envelope
  refine ⟨C, hC, M, fun N hN e he c ↦ ?_⟩
  filter_upwards [(hb N hN).2] with q hq j m
  exact hq j m (e j m) (he j m) (c j m)

example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor) (g : C(T3, C3)) :
    PressureCoherentChannelAction.action N hN t e c 0 g = 0 := by
  ext x
  simp [PressureCoherentChannelAction.action_apply, PressureKernelAction.kernelAction]

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ,
    ∀ e : ℕ → ℕ → R3, (∀ j m, ‖e j m‖ = 1) → ∀ c : ℕ → ℕ → Factor,
    ∀ f g : C(T3, C3), ∀ a b : C(T3, ℂ),
      ‖PressureCoherentChannelAction.sumAction N hN J e c (a • f) (b • g)‖ ≤
        C * (1 / 2 : ℝ) ^ J * ‖a • f‖ * ‖b • g‖ := by
  obtain ⟨C, hC, hb⟩ := PressureCoherentChannelAction.exists_uniform_sumAction_bound
  exact ⟨C, hC, fun N hN J e he c f g a b ↦ hb N hN J e he c (a • f) (b • g)⟩

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceChannel.contDiff_entry
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceChannel.exists_uniform_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceChannelKernel.multiplier_frequencyChange
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceChannelKernel.scaledKernel_undifferentiated
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceChannelKernel.fourier_scaledKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceOperatorKernel.norm_outputOperator
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceOperatorKernel.operatorKernel_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceOperatorKernel.fourier_operatorKernel_factor
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceOperatorKernel.norm_operatorKernel_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceEnvelope.exists_uniform_operator_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelPeriodization.integrable_periodicKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelPeriodization.mFourierCoeff_periodicKernel_factor
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelPeriodization.exists_uniform_periodic_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelEnvelopeBudget.exists_uniform_matched_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelEnvelopeBudget.exists_uniform_matched_envelope_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelAction.norm_action_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelAction.exists_uniform_action_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelAction.summable_matchedAction
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelAction.exists_uniform_sumAction_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelAction.action_localization
