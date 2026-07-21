import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceConditioningData
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationExecutable
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankSemantics

/-!
# Transparent conditioning checks for the exact evaluation inverse

The generated payload stores the independently computed row-l1 fractions.
This layer decodes them and states their integer cross-multiplication bound;
the expensive equality with the inverse matrix is replayed in bounded chunks.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceConditioningExecutable

open HypercubicDimension16PhysicalTraceConditioningData
open HypercubicDimension16PhysicalTraceEvaluationExecutable
open HypercubicDimension16TraceRankCertificate
open HypercubicDimension16TraceRankSemantics

@[reducible] def encodedInverseRowL1 (row : Fin 98) : Int × Nat :=
  inverseRowL1.getD row.1 (0, 1)

@[reducible] def decodedEncodedInverseRowL1 (row : Fin 98) : ℚ :=
  let value := encodedInverseRowL1 row
  (value.1 : ℚ) / value.2

@[reducible] def inverseAbsExactFraction
    (row column : Fin 98) : ExactFraction :=
  let value := encodedEvaluationInverseFraction row column
  (Int.ofNat value.1.natAbs, Int.ofNat value.2)

@[reducible] def inverseRowL1ExactFold (row : Fin 98) : ExactFraction :=
  (List.ofFn (fun column : Fin 98 => inverseAbsExactFraction row column)).foldl
    fractionAdd fractionZero

@[reducible] def encodedInverseRowL1Fraction
    (row : Fin 98) : ExactFraction :=
  let value := encodedInverseRowL1 row
  fractionOfEncoded value.1 value.2

/-- Integer-only evidence that every inverse denominator is positive and that
the transparent exact-fraction fold equals the independently stored row sum. -/
@[reducible] def EncodedInverseRowL1ReplayValid (row : Fin 98) : Prop :=
  (∀ column : Fin 98,
    (encodedEvaluationInverseFraction row column).2 > 0) ∧
  (inverseRowL1ExactFold row).2 ≠ 0 ∧
  (encodedInverseRowL1Fraction row).2 ≠ 0 ∧
  fractionEqual (inverseRowL1ExactFold row)
      (encodedInverseRowL1Fraction row) = true

/-- An integer-only check of positivity and comparison with the candidate
maximum. -/
@[reducible] def EncodedInverseRowL1Bound (row : Fin 98) : Prop :=
  let value := encodedInverseRowL1 row
  value.2 > 0 ∧ value.1 ≥ 0 ∧
    value.1 * 245314432 ≤ 4913129483781 * value.2

theorem fractionValue_foldl_fractionAdd
    (values : List ExactFraction) (initial : ExactFraction)
    (hinitial : FractionValid initial)
    (hvalues : ∀ value ∈ values, FractionValid value) :
    fractionValue (values.foldl fractionAdd initial) =
      fractionValue initial + (values.map fractionValue).sum := by
  induction values generalizing initial with
  | nil => simp
  | cons head tail induction =>
      have hhead : FractionValid head := hvalues head (by simp)
      have htail : ∀ value ∈ tail, FractionValid value := by
        intro value hvalue
        exact hvalues value (by simp [hvalue])
      rw [List.foldl_cons,
        induction (fractionAdd initial head)
          (fractionValid_add hinitial hhead) htail,
        fractionValue_add hinitial hhead]
      simp
      ring

theorem fractionValue_inverseAbsExactFraction_eq_decoded
    (row column : Fin 98) :
    fractionValue (inverseAbsExactFraction row column) =
      decodedEvaluationInverseAbs row column := by
  simp [fractionValue, inverseAbsExactFraction,
    decodedEvaluationInverseAbs]

theorem decodedEvaluationInverseAbs_eq_abs
    (row column : Fin 98)
    (hdenominator :
      (encodedEvaluationInverseFraction row column).2 > 0) :
    decodedEvaluationInverseAbs row column =
      |decodedEvaluationInverse row column| := by
  let value := encodedEvaluationInverseFraction row column
  have hdenominatorQ : (0 : ℚ) < value.2 := by
    exact_mod_cast hdenominator
  unfold decodedEvaluationInverseAbs decodedEvaluationInverse
  change (value.1.natAbs : ℚ) / value.2 =
    |(value.1 : ℚ) / value.2|
  rw [abs_div, abs_of_pos hdenominatorQ]
  congr 1
  simpa using congrArg (fun z : Int => (z : ℚ))
    (Int.natCast_natAbs value.1)

theorem decodedEvaluationInverseRowL1_eq_encoded_of_replay
    (row : Fin 98) (hreplay : EncodedInverseRowL1ReplayValid row) :
    decodedEvaluationInverseRowL1 row =
      decodedEncodedInverseRowL1 row := by
  have hfold := fractionValue_foldl_fractionAdd
    (List.ofFn (fun column : Fin 98 => inverseAbsExactFraction row column))
    fractionZero fractionValid_zero (by
      intro value hvalue
      rw [List.mem_ofFn] at hvalue
      rcases hvalue with ⟨column, rfl⟩
      change Int.ofNat
          (encodedEvaluationInverseFraction row column).2 ≠ 0
      exact Int.ofNat_ne_zero.mpr (ne_of_gt (hreplay.1 column)))
  have hfoldValue :
      fractionValue (inverseRowL1ExactFold row) =
        decodedEvaluationInverseRowL1 row := by
    rw [inverseRowL1ExactFold, hfold, fractionValue_zero, zero_add]
    rw [List.map_ofFn, List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro column _
    exact fractionValue_inverseAbsExactFraction_eq_decoded row column
  have hequal := fractionEqual_sound hreplay.2.1 hreplay.2.2.1
    hreplay.2.2.2
  rw [hfoldValue, encodedInverseRowL1Fraction,
    fractionValue_ofEncoded] at hequal
  exact hequal

theorem decodedEvaluationInverseRowL1_eq_sum_abs
    (row : Fin 98)
    (hdenominators : ∀ column : Fin 98,
      (encodedEvaluationInverseFraction row column).2 > 0) :
    decodedEvaluationInverseRowL1 row =
      ∑ column : Fin 98, |decodedEvaluationInverse row column| := by
  apply Finset.sum_congr rfl
  intro column _
  exact decodedEvaluationInverseAbs_eq_abs row column
    (hdenominators column)

theorem decodedEncodedInverseRowL1_le_real_of_bound (row : Fin 98)
    (hbound : EncodedInverseRowL1Bound row) :
    (decodedEncodedInverseRowL1 row : ℝ) ≤
      (4913129483781 : ℝ) / 245314432 := by
  let value := encodedInverseRowL1 row
  have hden : (0 : ℝ) < value.2 := by
    exact_mod_cast hbound.1
  have hconstantDen : (0 : ℝ) < (245314432 : ℕ) := by norm_num
  unfold decodedEncodedInverseRowL1
  change ((((value.1 : ℚ) / value.2 : ℚ)) : ℝ) ≤ _
  push_cast
  apply (div_le_div_iff₀ hden hconstantDen).2
  exact_mod_cast hbound.2.2

end HypercubicDimension16PhysicalTraceConditioningExecutable
end YangMills
end QuantumTheory
end Mettapedia
