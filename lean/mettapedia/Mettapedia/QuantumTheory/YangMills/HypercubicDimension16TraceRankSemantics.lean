import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateCore
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Tactic

/-!
# Rational semantics of the sparse trace-rank replay

The computational checker uses unreduced integer numerator-denominator pairs.
This file interprets those pairs in `ℚ` and proves that every checker
operation has the advertised rational-row semantics.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankSemantics

open HypercubicDimension16TraceRankCertificate

def fractionValue (value : ExactFraction) : ℚ :=
  (value.1 : ℚ) / (value.2 : ℚ)

def FractionValid (value : ExactFraction) : Prop := value.2 ≠ 0

def SparseRowValid (row : ExactSparseRow) : Prop :=
  ∀ entry ∈ row, FractionValid entry.2

def SparseColumnsStrict : ExactSparseRow → Prop
  | [] => True
  | [_] => True
  | first :: second :: remaining =>
      first.1 < second.1 ∧ SparseColumnsStrict (second :: remaining)

@[simp] theorem fractionValue_zero : fractionValue fractionZero = 0 := by
  norm_num [fractionValue, fractionZero]

@[simp] theorem fractionValue_ofInt (value : Int) :
    fractionValue (fractionOfInt value) = (value : ℚ) := by
  simp [fractionValue, fractionOfInt]

theorem fractionValue_ofEncoded (numerator : Int) (denominator : Nat) :
    fractionValue (fractionOfEncoded numerator denominator) =
      (numerator : ℚ) / (denominator : ℚ) := by
  simp [fractionValue, fractionOfEncoded]

@[simp] theorem fractionValue_neg (value : ExactFraction) :
    fractionValue (fractionNeg value) = -fractionValue value := by
  rcases value with ⟨numerator, denominator⟩
  change (-(numerator : ℚ)) / (denominator : ℚ) =
    -((numerator : ℚ) / (denominator : ℚ))
  rw [neg_div]

theorem fractionValue_add {left right : ExactFraction}
    (hleft : FractionValid left) (hright : FractionValid right) :
    fractionValue (fractionAdd left right) =
      fractionValue left + fractionValue right := by
  rcases left with ⟨leftNumerator, leftDenominator⟩
  rcases right with ⟨rightNumerator, rightDenominator⟩
  simp only [FractionValid, fractionValue, fractionAdd] at hleft hright ⊢
  norm_cast at hleft hright
  push_cast
  field_simp

theorem fractionValue_mul {left right : ExactFraction}
    (hleft : FractionValid left) (hright : FractionValid right) :
    fractionValue (fractionMul left right) =
      fractionValue left * fractionValue right := by
  rcases left with ⟨leftNumerator, leftDenominator⟩
  rcases right with ⟨rightNumerator, rightDenominator⟩
  simp only [FractionValid, fractionValue, fractionMul] at hleft hright ⊢
  norm_cast at hleft hright
  push_cast
  field_simp

theorem fractionValue_div {left right : ExactFraction}
    (hleft : FractionValid left) (hright : FractionValid right)
    (hrightNumerator : right.1 ≠ 0) :
    fractionValue (fractionDiv left right) =
      fractionValue left / fractionValue right := by
  rcases left with ⟨leftNumerator, leftDenominator⟩
  rcases right with ⟨rightNumerator, rightDenominator⟩
  simp only [FractionValid, fractionValue, fractionDiv] at hleft hright hrightNumerator ⊢
  norm_cast at hleft hright hrightNumerator
  push_cast
  field_simp

theorem fractionEqual_sound {left right : ExactFraction}
    (hleft : FractionValid left) (hright : FractionValid right)
    (hequal : fractionEqual left right = true) :
    fractionValue left = fractionValue right := by
  rcases left with ⟨leftNumerator, leftDenominator⟩
  rcases right with ⟨rightNumerator, rightDenominator⟩
  simp only [FractionValid, fractionEqual, fractionValue] at hleft hright hequal ⊢
  norm_cast at hleft hright
  have hcross : leftNumerator * rightDenominator =
      rightNumerator * leftDenominator := of_decide_eq_true hequal
  have hcross' : leftNumerator * rightDenominator =
      leftDenominator * rightNumerator := by
    simpa [mul_comm] using hcross
  field_simp
  exact_mod_cast hcross'

theorem fractionIsZero_eq_true_iff (value : ExactFraction) :
    fractionIsZero value = true ↔ value.1 = 0 := by
  simp [fractionIsZero]

theorem fractionIsZero_eq_false_iff (value : ExactFraction) :
    fractionIsZero value = false ↔ value.1 ≠ 0 := by
  simp [fractionIsZero]

theorem fractionValue_eq_zero_of_isZero {value : ExactFraction}
    (hzero : fractionIsZero value = true) : fractionValue value = 0 := by
  rw [fractionIsZero_eq_true_iff] at hzero
  simp [fractionValue, hzero]

@[simp] theorem fractionValid_zero : FractionValid fractionZero := by
  simp [FractionValid, fractionZero]

@[simp] theorem fractionValid_ofInt (value : Int) :
    FractionValid (fractionOfInt value) := by
  simp [FractionValid, fractionOfInt]

theorem fractionValid_neg {value : ExactFraction} (hvalue : FractionValid value) :
    FractionValid (fractionNeg value) := by
  simpa [FractionValid, fractionNeg] using hvalue

theorem fractionValid_add {left right : ExactFraction}
    (hleft : FractionValid left) (hright : FractionValid right) :
    FractionValid (fractionAdd left right) := by
  rcases left with ⟨leftNumerator, leftDenominator⟩
  rcases right with ⟨rightNumerator, rightDenominator⟩
  simp only [FractionValid, fractionAdd] at hleft hright ⊢
  exact mul_ne_zero hleft hright

theorem fractionValid_mul {left right : ExactFraction}
    (hleft : FractionValid left) (hright : FractionValid right) :
    FractionValid (fractionMul left right) := by
  rcases left with ⟨leftNumerator, leftDenominator⟩
  rcases right with ⟨rightNumerator, rightDenominator⟩
  simp only [FractionValid, fractionMul] at hleft hright ⊢
  exact mul_ne_zero hleft hright

theorem fractionValid_div {left right : ExactFraction}
    (hleft : FractionValid left) (hrightNumerator : right.1 ≠ 0) :
    FractionValid (fractionDiv left right) := by
  rcases left with ⟨leftNumerator, leftDenominator⟩
  rcases right with ⟨rightNumerator, rightDenominator⟩
  simp only [FractionValid, fractionDiv] at hleft hrightNumerator ⊢
  exact mul_ne_zero hleft hrightNumerator

theorem fractionRegular_sound {value : ExactFraction}
    (hregular : fractionRegular value = true) :
    value.1 ≠ 0 ∧ FractionValid value := by
  simpa [fractionRegular, FractionValid] using hregular

theorem exactSparseRowWellFormed_sound : ∀ {row : ExactSparseRow},
    exactSparseRowWellFormed row = true →
      SparseRowValid row ∧ SparseColumnsStrict row ∧
        ∀ entry ∈ row, entry.2.1 ≠ 0
  | [], _ => by
      simp [SparseRowValid, SparseColumnsStrict]
  | [entry], hwellFormed => by
      have hregular : fractionRegular entry.2 = true := by
        simpa [exactSparseRowWellFormed] using hwellFormed
      rcases fractionRegular_sound hregular with ⟨hnumerator, hvalid⟩
      constructor
      · intro target htarget
        simp only [List.mem_singleton] at htarget
        subst target
        exact hvalid
      · constructor
        · simp [SparseColumnsStrict]
        · intro target htarget
          simp only [List.mem_singleton] at htarget
          subst target
          exact hnumerator
  | entry :: next :: remaining, hwellFormed => by
      have hparts : fractionRegular entry.2 = true ∧
          entry.1 < next.1 ∧
          exactSparseRowWellFormed (next :: remaining) = true := by
        simpa [exactSparseRowWellFormed, Bool.and_eq_true] using hwellFormed
      rcases fractionRegular_sound hparts.1 with ⟨hnumerator, hvalid⟩
      rcases exactSparseRowWellFormed_sound hparts.2.2 with
        ⟨hremainingValid, hremainingStrict, hremainingNumerator⟩
      constructor
      · intro target htarget
        rcases List.mem_cons.mp htarget with rfl | htarget
        · exact hvalid
        · exact hremainingValid target htarget
      · constructor
        · exact ⟨hparts.2.1, hremainingStrict⟩
        · intro target htarget
          rcases List.mem_cons.mp htarget with rfl | htarget
          · exact hnumerator
          · exact hremainingNumerator target htarget

theorem sparseColumnsStrict_head_lt_of_mem_tail
    {entry target : Nat × ExactFraction} : ∀ {remaining : ExactSparseRow},
      SparseColumnsStrict (entry :: remaining) → target ∈ remaining →
        entry.1 < target.1
  | [], _, htarget => by simp at htarget
  | next :: rest, hstrict, htarget => by
      rcases List.mem_cons.mp htarget with rfl | htarget
      · exact hstrict.1
      · exact lt_trans hstrict.1
          (sparseColumnsStrict_head_lt_of_mem_tail hstrict.2 htarget)

theorem maxSupportColumn_nonempty (entry : Nat × ExactFraction) :
    ∀ remaining : ExactSparseRow,
      ∃ pivot, maxSupportColumn (entry :: remaining) = some pivot
  | [] => ⟨entry.1, rfl⟩
  | next :: rest => by
      rcases maxSupportColumn_nonempty next rest with ⟨pivot, hpivot⟩
      exact ⟨pivot, by simp [maxSupportColumn, hpivot]⟩

theorem sparseColumn_le_maxSupport {row : ExactSparseRow} {pivot : Nat}
    (hstrict : SparseColumnsStrict row)
    (hmax : maxSupportColumn row = some pivot)
    {entry : Nat × ExactFraction} (hentry : entry ∈ row) :
    entry.1 ≤ pivot := by
  induction row generalizing entry with
  | nil => simp at hentry
  | cons first remaining inductionHypothesis =>
      cases remaining with
      | nil =>
          simp only [List.mem_singleton] at hentry
          subst entry
          have hpivot : first.1 = pivot := by
            simpa [maxSupportColumn] using hmax
          exact hpivot.le
      | cons second rest =>
          rcases maxSupportColumn_nonempty second rest with
            ⟨remainingPivot, hremainingPivot⟩
          have hpivot : remainingPivot = pivot := by
            simpa [maxSupportColumn, hremainingPivot] using hmax
          subst remainingPivot
          have hremainingMax :
              maxSupportColumn (second :: rest) = some pivot := by
            exact hremainingPivot
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact le_trans (Nat.le_of_lt hstrict.1)
              (inductionHypothesis hstrict.2 hremainingMax (by simp))
          · exact inductionHypothesis hstrict.2 hremainingMax hentry

theorem fractionValue_ne_zero {value : ExactFraction}
    (hnumerator : value.1 ≠ 0) (hvalid : FractionValid value) :
    fractionValue value ≠ 0 := by
  apply div_ne_zero
  · exact_mod_cast hnumerator
  · exact_mod_cast hvalid

theorem maxSupportColumn_normalize (coefficient : ExactFraction) :
    ∀ row : ExactSparseRow,
      maxSupportColumn (normalizeRow coefficient row) = maxSupportColumn row
  | [] => rfl
  | entry :: remaining => by
      change (match maxSupportColumn (normalizeRow coefficient remaining) with
        | none => some entry.1
        | some finalColumn => some finalColumn) =
        match maxSupportColumn remaining with
        | none => some entry.1
        | some finalColumn => some finalColumn
      rw [maxSupportColumn_normalize coefficient remaining]

theorem exactSparseRowEqual_maxSupport : ∀ {left right : ExactSparseRow},
    exactSparseRowEqual left right = true →
      maxSupportColumn left = maxSupportColumn right
  | [], [], _ => rfl
  | [], _ :: _, hequal => by simp [exactSparseRowEqual] at hequal
  | _ :: _, [], hequal => by simp [exactSparseRowEqual] at hequal
  | left :: leftRemaining, right :: rightRemaining, hequal => by
      have hparts : left.1 = right.1 ∧
          exactSparseRowEqual leftRemaining rightRemaining = true := by
        simp only [exactSparseRowEqual, Bool.and_eq_true] at hequal
        exact ⟨of_decide_eq_true hequal.1.1, hequal.2⟩
      simp only [maxSupportColumn]
      rw [exactSparseRowEqual_maxSupport hparts.2, hparts.1]

def sparseRowValue : ExactSparseRow → Nat →₀ ℚ
  | [] => 0
  | entry :: remaining =>
      Finsupp.single entry.1 (fractionValue entry.2) +
        sparseRowValue remaining

@[simp] theorem sparseRowValue_nil : sparseRowValue [] = 0 := rfl

@[simp] theorem sparseRowValue_cons (entry : Nat × ExactFraction)
    (remaining : ExactSparseRow) :
    sparseRowValue (entry :: remaining) =
      Finsupp.single entry.1 (fractionValue entry.2) +
        sparseRowValue remaining := rfl

theorem sparseRowValue_apply_eq_zero_of_columns_lt
    {row : ExactSparseRow} {column : Nat}
    (hcolumns : ∀ entry ∈ row, entry.1 < column) :
    sparseRowValue row column = 0 := by
  induction row with
  | nil => simp
  | cons entry remaining inductionHypothesis =>
      have hhead := hcolumns entry (by simp)
      have htail : ∀ target ∈ remaining, target.1 < column := by
        intro target htarget
        exact hcolumns target (by simp [htarget])
      rw [sparseRowValue_cons]
      simp [ne_of_lt hhead, inductionHypothesis htail]

theorem sparseRowValue_apply_eq_zero_above_max
    {row : ExactSparseRow} {pivot column : Nat}
    (hstrict : SparseColumnsStrict row)
    (hmax : maxSupportColumn row = some pivot) (habove : pivot < column) :
    sparseRowValue row column = 0 :=
  sparseRowValue_apply_eq_zero_of_columns_lt fun entry hentry =>
    lt_of_le_of_lt (sparseColumn_le_maxSupport hstrict hmax hentry) habove

theorem sparseRowValue_apply_max_ne_zero : ∀ {row : ExactSparseRow}
    {pivot : Nat}, SparseColumnsStrict row → SparseRowValid row →
      (∀ entry ∈ row, entry.2.1 ≠ 0) →
      maxSupportColumn row = some pivot →
      sparseRowValue row pivot ≠ 0
  | [], _, _, _, _, hmax => by simp [maxSupportColumn] at hmax
  | [entry], pivot, _, hvalid, hnumerator, hmax => by
      have hpivot : entry.1 = pivot := by
        simpa [maxSupportColumn] using Option.some.inj hmax
      rw [← hpivot]
      simp only [sparseRowValue_cons, sparseRowValue_nil,
        add_zero, Finsupp.single_eq_same]
      exact fractionValue_ne_zero
        (hnumerator entry (by simp)) (hvalid entry (by simp))
  | entry :: next :: remaining, pivot, hstrict, hvalid,
      hnumerator, hmax => by
      rcases maxSupportColumn_nonempty next remaining with
        ⟨remainingPivot, hremainingPivot⟩
      have hpivot : remainingPivot = pivot := by
        simpa [maxSupportColumn, hremainingPivot] using hmax
      subst remainingPivot
      have hnextLe : next.1 ≤ pivot :=
        sparseColumn_le_maxSupport hstrict.2 hremainingPivot (by simp)
      have hentryLt : entry.1 < pivot := lt_of_lt_of_le hstrict.1 hnextLe
      have htailValid : SparseRowValid (next :: remaining) := by
        intro target htarget
        exact hvalid target (by simp [htarget])
      have htailNumerator : ∀ target ∈ next :: remaining,
          target.2.1 ≠ 0 := by
        intro target htarget
        exact hnumerator target (by simp [htarget])
      have htailNonzero := sparseRowValue_apply_max_ne_zero hstrict.2
        htailValid htailNumerator hremainingPivot
      rw [sparseRowValue_cons]
      simpa [ne_of_lt hentryLt] using htailNonzero

theorem linearIndependent_of_distinct_maxSupport
    {index : Type*} [DecidableEq index]
    {vectors : index → Nat →₀ ℚ} {pivot : index → Nat}
    (hpivot : Function.Injective pivot)
    (hdiagonal : ∀ i, vectors i (pivot i) ≠ 0)
    (habove : ∀ i column, pivot i < column → vectors i column = 0) :
    LinearIndependent ℚ vectors := by
  rw [linearIndependent_iff']
  intro support coefficient hsum i hi
  by_contra hcoefficient
  let active := support.filter fun j => coefficient j ≠ 0
  have hactive : active.Nonempty := by
    exact ⟨i, by simp [active, hi, hcoefficient]⟩
  obtain ⟨maxIndex, hmaxActive, hmax⟩ :=
    Finset.exists_max_image active pivot hactive
  have hmaxSupport : maxIndex ∈ support :=
    (Finset.mem_filter.mp hmaxActive).1
  have hmaxCoefficient : coefficient maxIndex ≠ 0 :=
    (Finset.mem_filter.mp hmaxActive).2
  have hevaluation :
      ∑ j ∈ support, coefficient j * vectors j (pivot maxIndex) = 0 := by
    simpa using congrArg (fun row : Nat →₀ ℚ => row (pivot maxIndex)) hsum
  rw [Finset.sum_eq_single maxIndex] at hevaluation
  · exact (mul_ne_zero hmaxCoefficient (hdiagonal maxIndex)) hevaluation
  · intro j hjSupport hjNe
    by_cases hjCoefficient : coefficient j = 0
    · simp [hjCoefficient]
    · have hjActive : j ∈ active := by
        simp [active, hjSupport, hjCoefficient]
      have hjLe := hmax j hjActive
      have hjLt : pivot j < pivot maxIndex := lt_of_le_of_ne hjLe fun hequal =>
        hjNe (hpivot hequal)
      simp [habove j (pivot maxIndex) hjLt]
  · exact fun hnotMem => (hnotMem hmaxSupport).elim

theorem sparseRowValid_tail {entry : Nat × ExactFraction}
    {remaining : ExactSparseRow}
    (hvalid : SparseRowValid (entry :: remaining)) :
    SparseRowValid remaining := by
  intro target htarget
  exact hvalid target (by simp [htarget])

theorem sparseRowValid_head {entry : Nat × ExactFraction}
    {remaining : ExactSparseRow}
    (hvalid : SparseRowValid (entry :: remaining)) :
    FractionValid entry.2 :=
  hvalid entry (by simp)

theorem sparseRowValid_cons_iff {entry : Nat × ExactFraction}
    {remaining : ExactSparseRow} :
    SparseRowValid (entry :: remaining) ↔
      FractionValid entry.2 ∧ SparseRowValid remaining := by
  simp [SparseRowValid]

theorem fractionValid_coefficientAt {row : ExactSparseRow}
    (hrow : SparseRowValid row) (column : Nat) :
    FractionValid (coefficientAt column row) := by
  induction row with
  | nil => exact fractionValid_zero
  | cons entry remaining inductionHypothesis =>
      have hentry := sparseRowValid_head hrow
      have hremaining := sparseRowValid_tail hrow
      simp only [coefficientAt]
      split
      · exact hentry
      · split
        · exact fractionValid_zero
        · exact inductionHypothesis hremaining

theorem sparseRowValid_addAt {column : Nat} {delta : ExactFraction}
    {row : ExactSparseRow} (hdelta : FractionValid delta)
    (hrow : SparseRowValid row) :
    SparseRowValid (addAt column delta row) := by
  induction row with
  | nil =>
      simp only [addAt]
      split
      · simp [SparseRowValid]
      · simpa [SparseRowValid] using hdelta
  | cons entry remaining inductionHypothesis =>
      have hentry := sparseRowValid_head hrow
      have hremaining := sparseRowValid_tail hrow
      simp only [addAt]
      split
      · split
        · exact hrow
        · exact sparseRowValid_cons_iff.mpr ⟨hdelta,
            sparseRowValid_cons_iff.mpr ⟨hentry, hremaining⟩⟩
      · split
        · exact sparseRowValid_cons_iff.mpr
            ⟨hentry, inductionHypothesis hremaining⟩
        · split
          · exact hremaining
          · exact sparseRowValid_cons_iff.mpr
              ⟨fractionValid_add hentry hdelta, hremaining⟩

theorem sparseRowValue_addAt {column : Nat} {delta : ExactFraction}
    {row : ExactSparseRow} (hdelta : FractionValid delta)
    (hrow : SparseRowValid row) :
    sparseRowValue (addAt column delta row) =
      sparseRowValue row + Finsupp.single column (fractionValue delta) := by
  induction row with
  | nil =>
      simp only [addAt]
      split <;> rename_i hzero
      · have hvalue := fractionValue_eq_zero_of_isZero hzero
        simp [hvalue]
      · simp [sparseRowValue]
  | cons entry remaining inductionHypothesis =>
      have hentry := sparseRowValid_head hrow
      have hremaining := sparseRowValid_tail hrow
      simp only [addAt]
      split <;> rename_i hcolumnLeft
      · split <;> rename_i hzero
        · have hvalue := fractionValue_eq_zero_of_isZero hzero
          simp [hvalue]
        · simp only [sparseRowValue_cons]
          abel
      · split <;> rename_i hentryLeft
        · rw [sparseRowValue_cons,
            inductionHypothesis hremaining, sparseRowValue_cons]
          abel
        · have hcolumn : column = entry.1 := by omega
          have hupdatedValue : fractionValue (fractionAdd entry.2 delta) =
              fractionValue entry.2 + fractionValue delta :=
            fractionValue_add hentry hdelta
          split <;> rename_i hzero
          · have hvalueZero := fractionValue_eq_zero_of_isZero hzero
            have hsumZero : fractionValue entry.2 + fractionValue delta = 0 := by
              rw [← hupdatedValue]
              exact hvalueZero
            classical
            ext target
            by_cases htarget : entry.1 = target
            · simp [sparseRowValue, hcolumn, htarget]
              linarith
            · simp [sparseRowValue, hcolumn, htarget]
          · classical
            ext target
            by_cases htarget : entry.1 = target
            · simp [sparseRowValue, hcolumn, htarget]
              rw [hupdatedValue]
              ring
            · simp [sparseRowValue, hcolumn, htarget]

theorem exactSparseRowEqual_sound :
    ∀ {left right : ExactSparseRow},
      SparseRowValid left → SparseRowValid right →
      exactSparseRowEqual left right = true →
      sparseRowValue left = sparseRowValue right
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hequal => by simp at hequal
  | _ :: _, [], _, _, hequal => by simp at hequal
  | left :: leftRemaining, right :: rightRemaining,
      hleftValid, hrightValid, hequal => by
      simp only [exactSparseRowEqual, Bool.and_eq_true] at hequal
      have hcolumn : left.1 = right.1 := of_decide_eq_true hequal.1.1
      have hvalue := fractionEqual_sound
        (sparseRowValid_head hleftValid)
        (sparseRowValid_head hrightValid) hequal.1.2
      have hremaining := exactSparseRowEqual_sound
        (sparseRowValid_tail hleftValid)
        (sparseRowValid_tail hrightValid) hequal.2
      simp only [sparseRowValue_cons, hcolumn, hvalue, hremaining]

theorem sparseRowValid_subtractScaled {row : ExactSparseRow}
    {coefficient : ExactFraction} {basis : ExactSparseRow}
    (hrow : SparseRowValid row) (hcoefficient : FractionValid coefficient)
    (hbasis : SparseRowValid basis) :
    SparseRowValid (subtractScaled row coefficient basis) := by
  induction basis generalizing row with
  | nil => simpa [subtractScaled] using hrow
  | cons entry remaining inductionHypothesis =>
      have hentry := sparseRowValid_head hbasis
      have hremaining := sparseRowValid_tail hbasis
      have hdelta : FractionValid
          (fractionNeg (fractionMul coefficient entry.2)) :=
        fractionValid_neg (fractionValid_mul hcoefficient hentry)
      have hnext := sparseRowValid_addAt (column := entry.1) hdelta hrow
      simpa [subtractScaled] using
        inductionHypothesis hnext hremaining

theorem sparseRowValue_subtractScaled {row : ExactSparseRow}
    {coefficient : ExactFraction} {basis : ExactSparseRow}
    (hrow : SparseRowValid row) (hcoefficient : FractionValid coefficient)
    (hbasis : SparseRowValid basis) :
    sparseRowValue (subtractScaled row coefficient basis) =
      sparseRowValue row - fractionValue coefficient • sparseRowValue basis := by
  induction basis generalizing row with
  | nil => simp [subtractScaled]
  | cons entry remaining inductionHypothesis =>
      have hentry := sparseRowValid_head hbasis
      have hremaining := sparseRowValid_tail hbasis
      have hproduct : FractionValid (fractionMul coefficient entry.2) :=
        fractionValid_mul hcoefficient hentry
      have hdelta : FractionValid
          (fractionNeg (fractionMul coefficient entry.2)) :=
        fractionValid_neg hproduct
      have hnext := sparseRowValid_addAt (column := entry.1) hdelta hrow
      rw [show subtractScaled row coefficient (entry :: remaining) =
          subtractScaled
            (addAt entry.1 (fractionNeg (fractionMul coefficient entry.2)) row)
            coefficient remaining by rfl,
        inductionHypothesis hnext hremaining,
        sparseRowValue_addAt hdelta hrow,
        fractionValue_neg,
        fractionValue_mul hcoefficient hentry,
        sparseRowValue_cons]
      ext column
      simp
      ring

theorem sparseRowValid_normalize {coefficient : ExactFraction}
    {row : ExactSparseRow} (hrow : SparseRowValid row)
    (hcoefficientNumerator : coefficient.1 ≠ 0) :
    SparseRowValid (normalizeRow coefficient row) := by
  intro entry hentry
  simp only [normalizeRow, List.mem_map] at hentry
  rcases hentry with ⟨source, hsource, rfl⟩
  exact fractionValid_div (hrow source hsource) hcoefficientNumerator

theorem sparseRowValue_normalize {coefficient : ExactFraction}
    {row : ExactSparseRow} (hrow : SparseRowValid row)
    (hcoefficientValid : FractionValid coefficient)
    (hcoefficientNumerator : coefficient.1 ≠ 0) :
    sparseRowValue (normalizeRow coefficient row) =
      (fractionValue coefficient)⁻¹ • sparseRowValue row := by
  induction row with
  | nil => simp [normalizeRow]
  | cons entry remaining inductionHypothesis =>
      have hentry := sparseRowValid_head hrow
      have hremaining := sparseRowValid_tail hrow
      simp only [normalizeRow, List.map_cons, sparseRowValue_cons]
      rw [fractionValue_div hentry hcoefficientValid hcoefficientNumerator,
        inductionHypothesis hremaining]
      ext column
      simp [div_eq_mul_inv, mul_comm, mul_left_comm]

end HypercubicDimension16TraceRankSemantics
end YangMills
end QuantumTheory
end Mettapedia
