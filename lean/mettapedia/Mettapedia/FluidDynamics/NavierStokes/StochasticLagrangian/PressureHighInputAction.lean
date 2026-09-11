import Mettapedia.Analysis.DyadicHighPass
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputAction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputEnvelope

/-!
# The complete high-input pressure operator

The fixed-output operators are summed in bilinear operator norm over every
high-input tail. The input annuli form an exact high-pass multiplier, whose
complement is a low-pass multiplier at the initial input scale.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureHighInputAction

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator FourierPressureTraceSymbol
open PressureFixedOutputSymbol PressureFixedOutputAction PressureFixedOutputEnvelope
open PressureDyadicBilinearAction PressureContinuousBilinearAction PressureDyadicPeriodization
open PressureLowOutputDyadicBudget
open Mettapedia.Analysis.DyadicAnnulus

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

def inputMultiplier (N : ℝ) (J : ℕ) (k : Wavevector) : ℝ :=
  Mettapedia.Analysis.DyadicHighPass.multiplier ((inputScale N J)⁻¹ • realFrequency k)

theorem hasSum_inputCutoff (N : ℝ) (J : ℕ) (k : Wavevector) :
    HasSum (fun j : ℕ ↦ normalizedCutoff ((inputScale N (J + j))⁻¹ • realFrequency k))
      (inputMultiplier N J k) := by
  unfold inputMultiplier
  have hs := Mettapedia.Analysis.DyadicHighPass.hasSum_annuli
    ((inputScale N J)⁻¹ • realFrequency k)
  convert hs using 1
  ext j
  congr 1
  simp only [inputScale, pow_add, mul_inv_rev, ← inv_pow, one_div, smul_smul]
  congr 1
  ring

theorem exists_uniform_fixed_operator_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ j : ℕ, ∀ e : R3, ‖e‖ = 1 →
      ‖operator N hN j e‖ ≤ C * (1 / 4 : ℝ) ^ j := by
  obtain ⟨C0, C1, hC0, hC1, M, hb⟩ := exists_uniform_envelope
  refine ⟨C0, hC0, ?_⟩
  intro N hN j e he
  obtain ⟨hM, hK, hbudget⟩ := hb N hN
  have hle (m : ℕ) : ‖bandOperator (inputScale N j) (inputScale_pos N hN j)
      (dyadicParameter (j + m)) e‖ ≤ ∫ q : T6, M N hN j m q := by
    have hi := integrable_periodicKernel (inputScale N j) (inputScale_pos N hN j)
      (dyadicParameter (j + m)) e
    exact (norm_bilinearAction_le _ hi).trans
      (integral_mono_ae hi.norm (hM j m).2.2.1 (hK.mono (fun _ h ↦ h j m e he)))
  have hs := (hbudget j).1.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  exact (norm_tsum_le_tsum_norm hs).trans
    ((hs.tsum_le_tsum hle (hbudget j).1).trans (hbudget j).2.1)

theorem exists_uniform_tail_operator_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ, ∀ e : R3, ‖e‖ = 1 →
      Summable (fun j : ℕ ↦ ‖operator N hN (J + j) e‖) ∧
      (∑' j : ℕ, ‖operator N hN (J + j) e‖) ≤ C * (1 / 4 : ℝ) ^ J := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_fixed_operator_bound
  refine ⟨4 * C / 3, by positivity, ?_⟩
  intro N hN J e he
  have hle (j : ℕ) : ‖operator N hN (J + j) e‖ ≤
      (C * (1 / 4 : ℝ) ^ J) * (1 / 4 : ℝ) ^ j :=
    (hb N hN (J + j) e he).trans_eq (by rw [pow_add]; ring)
  have hs := hasSum_quarter.mul_left (C * (1 / 4 : ℝ) ^ J)
  have ha := hs.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  exact ⟨ha, (ha.tsum_le_tsum hle hs.summable).trans_eq (by rw [hs.tsum_eq]; ring)⟩

theorem summable_operators (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3) (he : ‖e‖ = 1) :
    Summable (fun j : ℕ ↦ operator N hN (J + j) e) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_tail_operator_budget
  exact (hb N hN J e he).1.of_norm

def tailOperator (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3) : FieldOp :=
  ∑' j : ℕ, operator N hN (J + j) e

set_option maxHeartbeats 800000 in
theorem hasSum_tailOperator_apply (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3) (he : ‖e‖ = 1)
    (f g : Field) :
    HasSum (fun j : ℕ ↦ operator N hN (J + j) e f g) (tailOperator N hN J e f g) := by
  have hs : HasSum (fun j : ℕ ↦ operator N hN (J + j) e) (tailOperator N hN J e) :=
    (summable_operators N hN J e he).hasSum
  exact (ContinuousLinearMap.apply ℂ Field g).hasSum
    ((ContinuousLinearMap.apply ℂ (Field →L[ℂ] Field) f).hasSum hs)

end Mettapedia.FluidDynamics.NavierStokes.PressureHighInputAction
