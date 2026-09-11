import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureContinuousBilinearAction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicAction

/-!
# The output-band pressure sum as a bounded bilinear field operator

The series converges in bilinear operator norm, not merely for each fixed
pair of fields. Its evaluation agrees with the previously constructed
continuous-field output-band sum.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicBilinearAction

open MeasureTheory PressureContinuousBilinearAction PressureDyadicPeriodization
open PressureLowOutputDyadicBudget (dyadicParameter)

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Field" => C(T3, C3)
local notation "FieldOp" => Field →L[ℂ] Field →L[ℂ] Field

local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
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

def bandOperator (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) : FieldOp :=
  bilinearAction (periodicKernel N hN t e) (integrable_periodicKernel N hN t e)

@[simp] theorem bandOperator_apply (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (f g : Field) :
    bandOperator N hN t e f g = PressureDyadicAction.action N hN t e f g := rfl

theorem exists_uniform_operator_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 →
      Summable (fun n : ℕ ↦ ‖bandOperator N hN (dyadicParameter n) e‖) ∧
      (∑' n : ℕ, ‖bandOperator N hN (dyadicParameter n) e‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_mass_budget
  refine ⟨C, hC, ?_⟩
  intro N hN e he
  obtain ⟨hs, hbound⟩ := hb N hN e he
  have hle (n : ℕ) := norm_bilinearAction_le _ (integrable_periodicKernel N hN (dyadicParameter n) e)
  have hsum := Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hle hs
  exact ⟨hsum, (hsum.tsum_le_tsum hle hs).trans hbound⟩

theorem summable_bandOperator (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1) :
    Summable (fun n : ℕ ↦ bandOperator N hN (dyadicParameter n) e) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_operator_budget
  exact (hb N hN e he).1.of_norm

def sumOperator (N : ℝ) (hN : 0 < N) (e : R3) : FieldOp :=
  ∑' n : ℕ, bandOperator N hN (dyadicParameter n) e

theorem sumOperator_apply (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1) (f g : Field) :
    sumOperator N hN e f g = PressureDyadicAction.sumAction N hN e f g := by
  have h := (ContinuousLinearMap.apply ℂ Field g).hasSum
    ((ContinuousLinearMap.apply ℂ (Field →L[ℂ] Field) f).hasSum
      (summable_bandOperator N hN e he).hasSum)
  exact h.tsum_eq.symm

theorem exists_uniform_sumOperator_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ e : R3, ‖e‖ = 1 →
      ‖sumOperator N hN e‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_operator_budget
  exact ⟨C, hC, fun N hN e he ↦
    (norm_tsum_le_tsum_norm (hb N hN e he).1).trans (hb N hN e he).2⟩

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicBilinearAction
