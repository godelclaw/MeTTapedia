import Mettapedia.GSLT.Distinction.Probabilistic.FinitePredictionArray
import Mettapedia.ProbabilityTheory.FiniteApproximateLumpability

/-!
# Numerical error budgets for finite prediction

The exact array target uses real semiring arithmetic. A native floating-point
provider performs rounded multiplication and addition. This file isolates that
second approximation: uniform absolute operation bounds accumulate along the
same ordered row, output-coordinate bounds add in ℓ¹, and numerical error adds
to the model's approximate observation-square budget.

No structure here asserts that a particular C operation satisfies these
bounds. That concrete IEEE-754 obligation requires round-to-nearest execution,
finite normal intermediates and a separately qualified native correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic.FinitePredictionRounding

open Mettapedia.Algebra
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.ProbabilityTheory.FiniteApproximateLumpability
open Mettapedia.GSLT.Scope
open scoped BigOperators

variable {n : Nat} {S T C : Type*} [Fintype S] [Fintype T]

/-- Rounded scalar operations with uniform absolute-error certificates. -/
structure AbsoluteRoundingOps where
  multiply : ℝ → ℝ → ℝ
  add : ℝ → ℝ → ℝ
  multiplyError : ℝ
  addError : ℝ
  multiplyError_nonneg : 0 ≤ multiplyError
  addError_nonneg : 0 ≤ addError
  multiply_error : ∀ left right,
    |multiply left right - left * right| ≤ multiplyError
  add_error : ∀ left right,
    |add left right - (left + right)| ≤ addError

/-- One indexed rounded row, with the same occurrence order as the exact
`SparseLinearMap.rowRun`. -/
def roundedRow {I : Type*} (operations : AbsoluteRoundingOps)
    (entries : List (I × ℝ)) (values : I → ℝ) : ℝ → ℝ
  | initial => entries.foldl
      (fun total entry => operations.add total
        (operations.multiply entry.2 (values entry.1))) initial

def rowErrorBudget (operations : AbsoluteRoundingOps) (entries : Nat) : ℝ :=
  entries * (operations.multiplyError + operations.addError)

/-- Rounded execution differs from the exact ordered fold by the initial
error plus one multiplication and one addition budget per occurrence. -/
theorem roundedRow_error {I : Type*} (operations : AbsoluteRoundingOps)
    (entries : List (I × ℝ)) (values : I → ℝ) (roundedInitial exactInitial : ℝ) :
    |roundedRow operations entries values roundedInitial -
        SparseLinearMap.rowRun entries values exactInitial| ≤
      |roundedInitial - exactInitial| + rowErrorBudget operations entries.length := by
  induction entries generalizing roundedInitial exactInitial with
  | nil => simp [roundedRow, SparseLinearMap.rowRun, rowErrorBudget]
  | cons entry rest induction =>
      simp only [roundedRow, List.foldl_cons, SparseLinearMap.rowRun]
      apply (induction
        (operations.add roundedInitial
          (operations.multiply entry.2 (values entry.1)))
        (exactInitial + entry.2 * values entry.1)).trans
      have middle :
          |(roundedInitial + operations.multiply entry.2 (values entry.1)) -
              (exactInitial + entry.2 * values entry.1)| ≤
            |roundedInitial - exactInitial| + operations.multiplyError := by
        calc
          |(roundedInitial + operations.multiply entry.2 (values entry.1)) -
              (exactInitial + entry.2 * values entry.1)| =
              |(roundedInitial - exactInitial) +
                (operations.multiply entry.2 (values entry.1) -
                  entry.2 * values entry.1)| := by
            congr 1
            ring
          _ ≤ |roundedInitial - exactInitial| +
                |operations.multiply entry.2 (values entry.1) -
                  entry.2 * values entry.1| := abs_add_le _ _
          _ ≤ |roundedInitial - exactInitial| + operations.multiplyError :=
            add_le_add_right (operations.multiply_error _ _)
              |roundedInitial - exactInitial|
      have step :
          |operations.add roundedInitial
              (operations.multiply entry.2 (values entry.1)) -
            (exactInitial + entry.2 * values entry.1)| ≤
          |roundedInitial - exactInitial| +
            (operations.multiplyError + operations.addError) := by
        calc
          |operations.add roundedInitial
              (operations.multiply entry.2 (values entry.1)) -
            (exactInitial + entry.2 * values entry.1)| ≤
              |operations.add roundedInitial
                  (operations.multiply entry.2 (values entry.1)) -
                (roundedInitial + operations.multiply entry.2 (values entry.1))| +
              |(roundedInitial + operations.multiply entry.2 (values entry.1)) -
                (exactInitial + entry.2 * values entry.1)| := abs_sub_le _ _ _
          _ ≤ operations.addError +
              (|roundedInitial - exactInitial| + operations.multiplyError) :=
            add_le_add (operations.add_error _ _) middle
          _ = |roundedInitial - exactInitial| +
              (operations.multiplyError + operations.addError) := by ring
      calc
        |operations.add roundedInitial
              (operations.multiply entry.2 (values entry.1)) -
            (exactInitial + entry.2 * values entry.1)| +
            rowErrorBudget operations rest.length ≤
          (|roundedInitial - exactInitial| +
            (operations.multiplyError + operations.addError)) +
            rowErrorBudget operations rest.length :=
          add_le_add_left step _
        _ = |roundedInitial - exactInitial| +
            rowErrorBudget operations (entry :: rest).length := by
          simp only [rowErrorBudget, List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- The coefficient row supplied to both the exact and rounded array loops. -/
def predictionEntries (enumeration : Fin n ≃ S) (kernel : S → Prob T)
    (target : T) : List (Fin n × ℝ) :=
  (List.finRange n).map fun input =>
    (input, (kernel (enumeration input)).1 target)

def roundedPredictionRow (operations : AbsoluteRoundingOps)
    (enumeration : Fin n ≃ S) (prior : Prob S) (kernel : S → Prob T)
    (target : T) : ℝ :=
  roundedRow operations (predictionEntries enumeration kernel target)
    (fun input => prior.1 (enumeration input)) 0

/-- The exact ordered row represented by `predictionEntries` is stochastic
bind, independently of the rounded evaluator. -/
theorem exact_predictionEntries (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (target : T) :
    SparseLinearMap.rowRun (predictionEntries enumeration kernel target)
      (fun input => prior.1 (enumeration input)) 0 = (bind prior kernel).1 target := by
  rw [SparseLinearMap.rowRun_eq]
  simp only [zero_add, predictionEntries, List.map_map, Function.comp_def,
    ← Fin.sum_univ_def, bind_apply]
  rw [enumeration.sum_comp
    (fun source => (kernel source).1 target * prior.1 source)]
  exact Finset.sum_congr rfl fun source _ => mul_comm _ _

theorem roundedPredictionRow_error (operations : AbsoluteRoundingOps)
    (enumeration : Fin n ≃ S) (prior : Prob S) (kernel : S → Prob T)
    (target : T) :
    |roundedPredictionRow operations enumeration prior kernel target -
        (bind prior kernel).1 target| ≤ rowErrorBudget operations n := by
  rw [← exact_predictionEntries enumeration prior kernel target]
  apply (roundedRow_error operations (predictionEntries enumeration kernel target)
    (fun input => prior.1 (enumeration input)) 0 0).trans_eq
  simp [rowErrorBudget, predictionEntries]

/-- ℓ¹ distance between arbitrary finite real coordinate families. Rounded
outputs need not themselves satisfy simplex laws. -/
def vectorL1 (first second : T → ℝ) : ℝ :=
  ∑ target, |first target - second target|

theorem vectorL1_nonneg (first second : T → ℝ) : 0 ≤ vectorL1 first second :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

@[simp] theorem vectorL1_self (vector : T → ℝ) : vectorL1 vector vector = 0 := by
  simp [vectorL1]

theorem vectorL1_triangle (first middle last : T → ℝ) :
    vectorL1 first last ≤ vectorL1 first middle + vectorL1 middle last := by
  simp only [vectorL1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun target _ => abs_sub_le _ _ _

/-- Coordinate bounds sum to a finite-vector ℓ¹ numerical budget. -/
theorem roundedPrediction_l1 (operations : AbsoluteRoundingOps)
    (enumeration : Fin n ≃ S) (prior : Prob S) (kernel : S → Prob T) :
    vectorL1 (roundedPredictionRow operations enumeration prior kernel)
      (bind prior kernel).1 ≤
        Fintype.card T * rowErrorBudget operations n := by
  unfold vectorL1
  calc
    (∑ target, |roundedPredictionRow operations enumeration prior kernel target -
        (bind prior kernel).1 target|) ≤
      ∑ _target : T, rowErrorBudget operations n :=
        Finset.sum_le_sum fun target _ =>
          roundedPredictionRow_error operations enumeration prior kernel target
    _ = Fintype.card T * rowErrorBudget operations n := by simp

def vectorTotal (vector : T → ℝ) : ℝ := ∑ target, vector target

def rawRefusal (vector : T → ℝ) : ℝ := 1 - vectorTotal vector

/-- Missing-mass error is bounded by coordinate ℓ¹ error. -/
theorem rawRefusal_error_le (first second : T → ℝ) :
    |rawRefusal first - rawRefusal second| ≤ vectorL1 first second := by
  unfold rawRefusal vectorTotal vectorL1
  rw [show (1 - ∑ target, first target) - (1 - ∑ target, second target) =
      -(∑ target, (first target - second target)) by
    rw [Finset.sum_sub_distrib]
    ring, abs_neg]
  exact Finset.abs_sum_le_sum_abs _ _

/-- If the native provider also rounds its final enabled-mass sum, that
additional error adds to the coordinate budget. This is the contract of its
`raw_refusal` receipt field; clamping a negative refusal is a later policy. -/
theorem reportedRefusal_error_le (rounded exact : T → ℝ)
    (reportedEnabled sumError : ℝ)
    (sumBound : |reportedEnabled - vectorTotal rounded| ≤ sumError) :
    |(1 - reportedEnabled) - rawRefusal exact| ≤
      sumError + vectorL1 rounded exact := by
  calc
    |(1 - reportedEnabled) - rawRefusal exact| =
        |reportedEnabled - vectorTotal exact| := by
      unfold rawRefusal
      rw [abs_sub_comm]
      congr 1
      ring
    _ ≤ |reportedEnabled - vectorTotal rounded| +
        |vectorTotal rounded - vectorTotal exact| := abs_sub_le _ _ _
    _ ≤ sumError + vectorL1 rounded exact :=
      add_le_add sumBound (by
        unfold vectorTotal vectorL1
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _)

section Observation

variable [Fintype C] [DecidableEq C]

/-- Numerical error and model-abstraction error add. The native provider may
compute the observed fine kernel directly; no independence premise appears. -/
theorem rounded_observed_prediction_le (operations : AbsoluteRoundingOps)
    (enumeration : Fin n ≃ S) (view : S → C)
    (fine : S → Prob S) (coarse : C → Prob C) (δ : ℝ)
    (rows : ApproxRows view view fine coarse δ) (prior : Prob S) :
    vectorL1
      (roundedPredictionRow operations enumeration prior
        (fun state => coarsen (fine state) view))
      (bind (coarsen prior view) coarse).1 ≤
        Fintype.card C * rowErrorBudget operations n + δ := by
  have numerical := roundedPrediction_l1 operations enumeration prior
    (fun state => coarsen (fine state) view)
  have model := prediction_le view view fine coarse δ rows prior
  rw [coarsen_bind] at model
  exact (vectorL1_triangle _
    (bind prior (fun state => coarsen (fine state) view)).1 _).trans
      (add_le_add numerical model)

/-- The combined native/model budget is itself an approximate commuting
square, ready for the existing square-composition machinery. -/
theorem rounded_approxSquare (operations : AbsoluteRoundingOps)
    (enumeration : Fin n ≃ S) (view : S → C)
    (fine : S → Prob S) (coarse : C → Prob C) (δ : ℝ)
    (rows : ApproxRows view view fine coarse δ) :
    ApproxSquare vectorL1 (fun prior => coarsen prior view) id
      (fun prior => roundedPredictionRow operations enumeration prior
        (fun state => coarsen (fine state) view))
      (fun prior => (bind prior coarse).1)
      (Fintype.card C * rowErrorBudget operations n + δ) :=
  fun prior => rounded_observed_prediction_le operations enumeration view
    fine coarse δ rows prior

end Observation

/-! ## Binary64 budget exported by the native provider -/

/-- Unit roundoff for round-to-nearest binary64. This constant alone does not
certify that a native execution satisfied the rounding model. -/
noncomputable def binary64UnitRoundoff : ℝ := 2⁻¹ ^ (53 : ℕ)

/-- The provider's conservative per-row receipt: one `u` multiplication error
and one `2u` addition error per input occurrence. -/
noncomputable def binary64RowBudget (inputs : Nat) : ℝ :=
  inputs * (binary64UnitRoundoff + 2 * binary64UnitRoundoff)

theorem binary64RowBudget_eq (inputs : Nat) :
    binary64RowBudget inputs = inputs * (3 * binary64UnitRoundoff) := by
  unfold binary64RowBudget
  ring

namespace Controls

def exactOperations : AbsoluteRoundingOps where
  multiply := (· * ·)
  add := (· + ·)
  multiplyError := 0
  addError := 0
  multiplyError_nonneg := le_rfl
  addError_nonneg := le_rfl
  multiply_error := by simp
  add_error := by simp

theorem exact_operations_recover_bind (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (target : T) :
    roundedPredictionRow exactOperations enumeration prior kernel target =
      (bind prior kernel).1 target := by
  have bound := roundedPredictionRow_error exactOperations enumeration prior kernel target
  have absoluteZero :
      |roundedPredictionRow exactOperations enumeration prior kernel target -
        (bind prior kernel).1 target| = 0 := by
    apply le_antisymm
    · simpa [rowErrorBudget, exactOperations] using bound
    · exact abs_nonneg _
  exact sub_eq_zero.mp (abs_eq_zero.mp absoluteZero)

def upwardBiased : AbsoluteRoundingOps where
  multiply := (· * ·)
  add := fun left right => left + right + 1
  multiplyError := 0
  addError := 1
  multiplyError_nonneg := le_rfl
  addError_nonneg := zero_le_one
  multiply_error := by simp
  add_error := by intro; simp

/-- A one-unit addition error per occurrence reaches the two-entry budget. -/
theorem additive_rounding_budget_is_real :
    roundedRow upwardBiased [(0, 1), (0, 1)] (fun _ : Nat => 1) 0 = 4 ∧
      SparseLinearMap.rowRun [(0, 1), (0, 1)] (fun _ : Nat => 1) 0 = 2 ∧
      rowErrorBudget upwardBiased 2 = 2 := by
  norm_num [roundedRow, SparseLinearMap.rowRun, rowErrorBudget, upwardBiased]

end Controls

end Mettapedia.GSLT.Distinction.Probabilistic.FinitePredictionRounding
