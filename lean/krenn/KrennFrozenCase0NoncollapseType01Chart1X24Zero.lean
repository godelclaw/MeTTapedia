import KrennFrozenCase0NoncollapseType01Pivot
import KrennFrozenCase0NoncollapseType01Chart1X24ZeroCertificate

/-!
Kernel connector for the strictly certified `w_24_11 = 0` half of physical
non-collapse type-01 pivot chart 1.

The structural layer proves equal pivot coefficients and four forced zeros.
It then instantiates the 72-variable strict certificate with the corresponding
canonical case-0 values and the field inverses whose nonzero hypotheses were
proved upstream.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart1X24Zero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart1X24ZeroCertificate
open Krenn.SparseCertificate
open MvPolynomial

def selectedSourceIndex : Fin 20 → Fin 747 := ![
  606, 318, 380, 652, 193, 181, 549, 505, 605, 646,
  346, 745, 345, 475, 300, 354, 349, 332, 336, 746
]

theorem selected_source_not_determinant
    (index : Fin 20) (slot : Fin 18) :
    determinantSourceIndex slot ≠ selectedSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, selectedSourceIndex]

def forcingSourceIndex : Fin 4 → Fin 747 := ![544, 599, 600, 547]

theorem forcing_source_not_determinant
    (index : Fin 4) (slot : Fin 18) :
    determinantSourceIndex slot ≠ forcingSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, forcingSourceIndex]

noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 72 → R := ![
  slotDeterminant values 1,
  (factorGb values)⁻¹,
  (factorL values)⁻¹,
  (values 28)⁻¹,
  (slotDeterminant values 1)⁻¹,
  values 0, values 1, values 2,
  values 3, values 4, values 5,
  values 6, values 7, values 8,
  values 9, values 10, values 11, values 12, values 13,
  values 14, values 15, (values 15)⁻¹, values 16,
  values 17, values 18, values 19, values 20, values 21,
  values 22, values 24,
  values 25, values 26, values 27, values 28, values 29,
  values 30, values 31, values 32,
  values 33, values 34, values 35, values 37, values 38,
  values 39, values 40,
  values 41, values 42, values 43,
  values 44, values 45, values 46,
  values 47, values 49,
  values 50, values 52,
  values 53, values 54, values 56, (values 56)⁻¹,
  values 58, values 59, values 60,
  values 61, values 62, values 66, values 67, values 68,
  values 69, values 71,
  values 72, values 73, values 74
]

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Reductions common to every point of pivot chart 1.  They do not depend on
the later split on `w_24_11`; both halves reuse this kernel proof. -/
theorem chart1_common_reductions
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values) :
    values 36 = values 28 ∧
      values 70 = -values 56 ∧ values 64 = -values 51 ∧
      values 63 = 0 ∧ values 55 = 0 ∧
      values 57 = 0 ∧ values 65 = 0 := by
  rcases chart with ⟨h23, h12⟩
  have h13 : values 36 = values 28 :=
    equal_coefficients_of_w23_zero values base hdet h23
  have leftZero : slotLeft values 1 = 0 :=
    (left_kill_or_collapse values base 1).resolve_left hdet
  have rightZero : slotRight values 1 = 0 :=
    (right_kill_or_collapse values base 1).resolve_left hdet
  have h35 : values 70 = -values 56 := by
    have productZero : values 28 * (values 70 + values 56) = 0 := by
      simpa [slotLeft, h23, h13, mul_add] using leftZero
    have sumZero := (mul_eq_zero.mp productZero).resolve_left h12
    exact eq_neg_of_add_eq_zero_left sumZero
  have h34 : values 64 = -values 51 := by
    have productZero : values 28 * (values 64 + values 51) = 0 := by
      simpa [slotRight, h23, h13, mul_add] using rightZero
    have sumZero := (mul_eq_zero.mp productZero).resolve_left h12
    exact eq_neg_of_add_eq_zero_left sumZero
  have force0 : sourceValue values (forcingSourceIndex 0) = 0 :=
    base (forcingSourceIndex 0)
      (fun slot => forcing_source_not_determinant 0 slot)
  have force1 : sourceValue values (forcingSourceIndex 1) = 0 :=
    base (forcingSourceIndex 1)
      (fun slot => forcing_source_not_determinant 1 slot)
  have force2 : sourceValue values (forcingSourceIndex 2) = 0 :=
    base (forcingSourceIndex 2)
      (fun slot => forcing_source_not_determinant 2 slot)
  have force3 : sourceValue values (forcingSourceIndex 3) = 0 :=
    base (forcingSourceIndex 3)
      (fun slot => forcing_source_not_determinant 3 slot)
  have h34_10 : values 63 = 0 := by
    have productZero : values 28 * values 63 = 0 := by
      simp [sourceValue, forcingSourceIndex,
        Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly] at force0
      rw [h23, h13, h35] at force0
      ring_nf at force0 ⊢
      exact force0
    exact (mul_eq_zero.mp productZero).resolve_left h12
  have h25_10 : values 55 = 0 := by
    have productZero : values 28 * values 55 = 0 := by
      simp [sourceValue, forcingSourceIndex,
        Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly] at force1
      rw [h23, h13, h34] at force1
      ring_nf at force1 ⊢
      exact force1
    exact (mul_eq_zero.mp productZero).resolve_left h12
  have h25_12 : values 57 = 0 := by
    have productZero : values 28 * values 57 = 0 := by
      simp [sourceValue, forcingSourceIndex,
        Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly] at force2
      rw [h23, h13, h34] at force2
      ring_nf at force2 ⊢
      exact force2
    exact (mul_eq_zero.mp productZero).resolve_left h12
  have h34_12 : values 65 = 0 := by
    have productZero : values 28 * values 65 = 0 := by
      simp [sourceValue, forcingSourceIndex,
        Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly] at force3
      rw [h23, h13, h35] at force3
      ring_nf at force3 ⊢
      exact force3
    exact (mul_eq_zero.mp productZero).resolve_left h12
  exact ⟨h13, h35, h34, h34_10, h25_10, h25_12, h34_12⟩

/-- Canonical amplitude row whose chart-1 reduction factors as the product of
the two remaining pivot sums. -/
def pivotSumSourceIndex : Fin 747 := 363

theorem pivot_sum_source_not_determinant (slot : Fin 18) :
    determinantSourceIndex slot ≠ pivotSumSourceIndex := by
  fin_cases slot <;>
    simp [determinantSourceIndex, pivotSumSourceIndex]

/-- Every point of pivot chart 1 lies either on the opposite-pivot chart or
on the equal-secondary-coefficient chart.  This is the kernel version of the
next exhaustive finite split. -/
theorem chart1_pivot_sum_or_equal
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values) :
    values 51 + values 56 = 0 ∨ values 31 = values 39 := by
  have reductions := chart1_common_reductions values base hdet chart
  rcases reductions with
    ⟨_h13, h35, h34, _h34_10, _h25_10, _h25_12, _h34_12⟩
  have source : sourceValue values pivotSumSourceIndex = 0 :=
    base pivotSumSourceIndex pivot_sum_source_not_determinant
  have product :
      (values 39 - values 31) * (values 51 + values 56) = 0 := by
    simp [sourceValue, pivotSumSourceIndex,
      Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly] at source
    rw [h34, h35] at source
    ring_nf at source ⊢
    exact source
  rcases mul_eq_zero.mp product with differenceZero | sumZero
  · right
    exact (sub_eq_zero.mp differenceZero).symm
  · exact Or.inl sumZero

/-- The `w_24_11 = 0` half of type-01 pivot chart 1 is impossible. -/
theorem refutes_slot1_chart1_w24_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 = 0) : False := by
  rcases chart with ⟨h23, h12⟩
  have h13 : values 36 = values 28 :=
    equal_coefficients_of_w23_zero values base hdet h23
  have leftZero : slotLeft values 1 = 0 :=
    (left_kill_or_collapse values base 1).resolve_left hdet
  have rightZero : slotRight values 1 = 0 :=
    (right_kill_or_collapse values base 1).resolve_left hdet
  have h35 : values 70 = -values 56 := by
    have productZero : values 28 * (values 70 + values 56) = 0 := by
      simpa [slotLeft, h23, h13, mul_add] using leftZero
    have sumZero := (mul_eq_zero.mp productZero).resolve_left h12
    exact eq_neg_of_add_eq_zero_left sumZero
  have h34 : values 64 = -values 51 := by
    have productZero : values 28 * (values 64 + values 51) = 0 := by
      simpa [slotRight, h23, h13, mul_add] using rightZero
    have sumZero := (mul_eq_zero.mp productZero).resolve_left h12
    exact eq_neg_of_add_eq_zero_left sumZero
  obtain ⟨hL, hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
  have hProduct : values 15 * values 56 ≠ 0 := by
    simpa [factorGb, h24] using hGb
  have h04 : values 15 ≠ 0 := by
    intro h
    exact hProduct (by simp [h])
  have h25 : values 56 ≠ 0 := by
    intro h
    exact hProduct (by simp [h])
  have force0 : sourceValue values (forcingSourceIndex 0) = 0 :=
    base (forcingSourceIndex 0)
      (fun slot => forcing_source_not_determinant 0 slot)
  have force1 : sourceValue values (forcingSourceIndex 1) = 0 :=
    base (forcingSourceIndex 1)
      (fun slot => forcing_source_not_determinant 1 slot)
  have force2 : sourceValue values (forcingSourceIndex 2) = 0 :=
    base (forcingSourceIndex 2)
      (fun slot => forcing_source_not_determinant 2 slot)
  have force3 : sourceValue values (forcingSourceIndex 3) = 0 :=
    base (forcingSourceIndex 3)
      (fun slot => forcing_source_not_determinant 3 slot)
  have h34_10 : values 63 = 0 := by
    have productZero : values 28 * values 63 = 0 := by
      simp [sourceValue, forcingSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly] at force0
      rw [h23, h13, h35] at force0
      ring_nf at force0 ⊢
      exact force0
    exact (mul_eq_zero.mp productZero).resolve_left h12
  have h25_10 : values 55 = 0 := by
    have productZero : values 28 * values 55 = 0 := by
      simp [sourceValue, forcingSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly] at force1
      rw [h23, h13, h34] at force1
      ring_nf at force1 ⊢
      exact force1
    exact (mul_eq_zero.mp productZero).resolve_left h12
  have h25_12 : values 57 = 0 := by
    have productZero : values 28 * values 57 = 0 := by
      simp [sourceValue, forcingSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly] at force2
      rw [h23, h13, h34] at force2
      ring_nf at force2 ⊢
      exact force2
    exact (mul_eq_zero.mp productZero).resolve_left h12
  have h34_12 : values 65 = 0 := by
    have productZero : values 28 * values 65 = 0 := by
      simp [sourceValue, forcingSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly] at force3
      rw [h23, h13, h35] at force3
      ring_nf at force3 ⊢
      exact force3
    exact (mul_eq_zero.mp productZero).resolve_left h12
  have sourceZero (index : Fin 20) :
      sourceValue values (selectedSourceIndex index) = 0 :=
    base (selectedSourceIndex index)
      (fun slot => selected_source_not_determinant index slot)
  have source0 := sourceZero 0
  have source1 := sourceZero 1
  have source2 := sourceZero 2
  have source3 := sourceZero 3
  have source4 := sourceZero 4
  have source5 := sourceZero 5
  have source6 := sourceZero 6
  have source7 := sourceZero 7
  have source8 := sourceZero 8
  have source9 := sourceZero 9
  have source10 := sourceZero 10
  have source11 := sourceZero 11
  have source12 := sourceZero 12
  have source13 := sourceZero 13
  have source14 := sourceZero 14
  have source15 := sourceZero 15
  have source16 := sourceZero 16
  have source17 := sourceZero 17
  have source18 := sourceZero 18
  have source19 := sourceZero 19
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source0
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source1
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source2
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source3
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source4
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source5
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source6
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source7
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source8
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source9
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source10
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source11
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source12
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source13
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source14
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source15
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source16
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source17
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source18
  simp [sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    h23, h13, h24, h35, h34,
    h34_10, h25_10, h25_12, h34_12] at source19
  apply selectedHasNoCommonZero (leafValues values)
  intro index
  fin_cases index
  all_goals
    simp [selectedEquations, selectedIndices,
      parentEquations, leafValues,
      sourceValue, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2,
      factorL, factorGb,
      h23, h13, h24, h35, h34,
      h34_10, h25_10, h25_12, h34_12,
      hdet, hL, h12, h04, h25]
  all_goals try assumption
  all_goals ring_nf at source5 source6 source17 ⊢
  all_goals assumption

#print axioms refutes_slot1_chart1_w24_zero
#print axioms chart1_pivot_sum_or_equal

end Krenn.FrozenCase0NoncollapseType01Chart1X24Zero
