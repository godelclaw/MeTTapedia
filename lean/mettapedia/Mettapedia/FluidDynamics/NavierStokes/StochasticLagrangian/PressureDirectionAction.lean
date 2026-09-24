import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDirectionOperatorKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureHighInputAction

/-!
# Direction stability of the complete high-input pressure action

The direction gap survives actual kernel integration, output-band summation,
and the complete high-input operator tail. The estimates act on continuous
fields and retain the quarter-geometric input-index gain.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDirectionAction

open MeasureTheory PressureDyadicPeriodization PressureDyadicBilinearAction
open PressureContinuousBilinearAction PressureFixedOutputSymbol PressureFixedOutputAction
open PressureHighInputAction PressureFixedOutputEnvelope PressureLowOutputDyadicBudget
open PressureLowOutputCutoff (ratio)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Field" => C(T3, C3)
local notation "FieldOp" => Field →L[ℂ] Field →L[ℂ] Field
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (C3 →L[ℂ] C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup (Field →L[ℂ] Field) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (Field →L[ℂ] Field) := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace (Field →L[ℂ] Field) := ContinuousLinearMap.instCompleteSpace
local instance : NormedAddCommGroup FieldOp := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ FieldOp := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace FieldOp := ContinuousLinearMap.instCompleteSpace
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_uniform_band_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e f : R3, ‖e‖ ≤ 1 → ‖f‖ ≤ 1 →
      ‖bandOperator N hN t e - bandOperator N hN t f‖ ≤ (ratio t) ^ 2 * ‖e - f‖ * C := by
  obtain ⟨C, hC, hb⟩ := PressureDirectionOperatorKernel.exists_uniform_periodic_mass
  refine ⟨C, hC, ?_⟩
  intro N hN t ht e f he hf
  rw [bandOperator, bandOperator, ← bilinearAction_sub_kernel]
  exact (norm_bilinearAction_le _ _).trans (hb N hN t ht e f he hf)

theorem exists_uniform_fixed_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ j : ℕ, ∀ e f : R3,
      ‖e‖ = 1 → ‖f‖ = 1 →
      ‖operator N hN j e - operator N hN j f‖ ≤ (C * (1 / 4 : ℝ) ^ j) * ‖e - f‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_band_bound
  refine ⟨C / 49152, by positivity, ?_⟩
  intro N hN j e f he hf
  have hle (m : ℕ) : ‖bandOperator (inputScale N j) (inputScale_pos N hN j)
      (dyadicParameter (j + m)) e - bandOperator (inputScale N j) (inputScale_pos N hN j)
      (dyadicParameter (j + m)) f‖ ≤
        ((C / 65536) * (1 / 4 : ℝ) ^ j * ‖e - f‖) * (1 / 4 : ℝ) ^ m := by
    have h := hb (inputScale N j) (inputScale_pos N hN j) _ (dyadicParameter_mem (j + m)) e f he.le hf.le
    rw [ratio_sq_matched] at h
    exact h.trans_eq (by ring)
  have hs := hasSum_quarter.mul_left ((C / 65536) * (1 / 4 : ℝ) ^ j * ‖e - f‖)
  have hn := hs.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  rw [operator, operator, ← (summable_operator_bands N hN j e he).tsum_sub
    (summable_operator_bands N hN j f hf)]
  exact (norm_tsum_le_tsum_norm hn).trans
    ((hn.tsum_le_tsum hle hs.summable).trans_eq (by rw [hs.tsum_eq]; ring))

theorem exists_uniform_tail_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ, ∀ e f : R3,
      ‖e‖ = 1 → ‖f‖ = 1 →
      ‖tailOperator N hN J e - tailOperator N hN J f‖ ≤ (C * (1 / 4 : ℝ) ^ J) * ‖e - f‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_fixed_bound
  refine ⟨4 * C / 3, by positivity, ?_⟩
  intro N hN J e f he hf
  have hle (j : ℕ) : ‖operator N hN (J + j) e - operator N hN (J + j) f‖ ≤
      (C * (1 / 4 : ℝ) ^ J * ‖e - f‖) * (1 / 4 : ℝ) ^ j :=
    (hb N hN (J + j) e f he hf).trans_eq (by rw [pow_add]; ring)
  have hs := hasSum_quarter.mul_left (C * (1 / 4 : ℝ) ^ J * ‖e - f‖)
  have hn := hs.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  rw [tailOperator, tailOperator, ← (summable_operators N hN J e he).tsum_sub
    (summable_operators N hN J f hf)]
  exact (norm_tsum_le_tsum_norm hn).trans
    ((hn.tsum_le_tsum hle hs.summable).trans_eq (by rw [hs.tsum_eq]; ring))

theorem exists_uniform_field_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ, ∀ e f : R3,
      ‖e‖ = 1 → ‖f‖ = 1 → ∀ u v : Field, ∀ x : T3,
      ‖tailOperator N hN J e u v x - tailOperator N hN J f u v x‖ ≤
        (C * (1 / 4 : ℝ) ^ J) * ‖e - f‖ * ‖u‖ * ‖v‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_tail_bound
  refine ⟨C, hC, ?_⟩
  intro N hN J e f he hf u v x
  let B := tailOperator N hN J e - tailOperator N hN J f
  have h : ‖B u v x‖ ≤ ‖B‖ * ‖u‖ * ‖v‖ :=
    (ContinuousMap.norm_coe_le_norm (B u v) x).trans
      (((B u).le_opNorm v).trans (mul_le_mul_of_nonneg_right (B.le_opNorm u) (norm_nonneg v)))
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hb N hN J e f he hf) (norm_nonneg u)) (norm_nonneg v))

end Mettapedia.FluidDynamics.NavierStokes.PressureDirectionAction
