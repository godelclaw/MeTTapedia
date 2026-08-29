import KrennFrozenCase0NoncollapseType01Chart1BothNonzero
import KrennFrozenCase0NoncollapseType01Chart1DiagzeroAB00Certificate
import KrennFrozenCase0NoncollapseType01Chart1DiagzeroAB10Certificate
import KrennFrozenCase0NoncollapseType01Chart1DiagzeroAB01Certificate
import KrennFrozenCase0NoncollapseType01Chart1DiagzeroAB11Certificate

/-!
Kernel connector for the last diagonal-zero subchart of physical
non-collapse type 01, pivot chart 1.

Here both cycle pivots and their sum are nonzero, the secondary coefficients
agree, and `w_02_11 = w_03_11 = w_01_22 = 0`.  Two canonical rows first show
that `w_45_11` is nonzero.  The chart is then split exhaustively on

* `A = w_12_00 * w_25_11 - 1`, and
* `B = w_13_00 * w_24_11 + 1`.

The four leaves below are bound to strict exact certificates.  Only the
certificate-selected equations are reflected into the kernel.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart1Diagzero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart1X24Zero
open Krenn.FrozenCase0NoncollapseType01Chart1BothNonzero
open Krenn.SparseCertificate
open MvPolynomial

def column2FactorA {R : Type*} [CommRing R] (values : Fin 75 → R) : R :=
  values 25 * values 56 - 1

def column2FactorB {R : Type*} [CommRing R] (values : Fin 75 → R) : R :=
  values 33 * values 51 + 1

/-- Canonical rows reached by exact polynomial matching from the selected
profile rows.  The profile system and the canonical 747-row freeze use
different row orders. -/
def leafSourceIndex : Fin 25 → Fin 747 := ![
  607, 321, 606, 318, 380, 652, 189, 193, 653, 710,
  605, 556, 280, 275, 22, 295, 304, 299, 300, 354,
  349, 343, 336, 737, 746
]

theorem leaf_source_not_determinant
    (index : Fin 25) (slot : Fin 18) :
    determinantSourceIndex slot ≠ leafSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, leafSourceIndex]

noncomputable def branch00Values {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 68 → R := ![
  (values 73)⁻¹, slotDeterminant values 1, (factorGb values)⁻¹,
  (factorL values)⁻¹, (values 51 + values 56)⁻¹, (values 28)⁻¹,
  (slotDeterminant values 1)⁻¹, values 1, values 3, values 5,
  values 6, values 8, values 9, values 10, values 11, values 12,
  values 13, values 14, values 15, values 16, values 17, values 18,
  values 19, values 20, values 21, values 22, values 24, values 26,
  values 27, values 28, values 29, values 30, values 31, values 32,
  values 34, values 35, values 37, values 38, values 40, values 41,
  values 42, values 43, values 44, values 45, values 46, values 47,
  values 49, values 50, values 51, (values 51)⁻¹, values 52,
  values 53, values 54, values 56, (values 56)⁻¹, values 58,
  values 59, values 60, values 61, values 62, values 66, values 67,
  values 68, values 69, values 71, values 72, values 73, values 74
]

noncomputable def branch10Values {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 67 → R := ![
  (values 73)⁻¹, (column2FactorA values)⁻¹, slotDeterminant values 1,
  (factorGb values)⁻¹, (factorL values)⁻¹,
  (values 51 + values 56)⁻¹, (values 28)⁻¹,
  (slotDeterminant values 1)⁻¹, values 1, values 3, values 5,
  values 6, values 8, values 9, values 11, values 12, values 14,
  values 15, values 17, values 18, values 19, values 20, values 21,
  values 22, values 24, values 25, values 26, values 27, values 28,
  values 29, values 30, values 31, values 32, values 34, values 35,
  values 37, values 38, values 40, values 41, values 42, values 43,
  values 44, values 45, values 46, values 47, values 49, values 50,
  values 51, (values 51)⁻¹, values 52, values 53, values 54,
  values 56, (values 56)⁻¹, values 58, values 59, values 60,
  values 61, values 62, values 66, values 67, values 68, values 69,
  values 71, values 72, values 73, values 74
]

noncomputable def branch01Values {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 67 → R := ![
  (values 73)⁻¹, (column2FactorB values)⁻¹, slotDeterminant values 1,
  (factorGb values)⁻¹, (factorL values)⁻¹,
  (values 51 + values 56)⁻¹, (values 28)⁻¹,
  (slotDeterminant values 1)⁻¹, values 1, values 3, values 5,
  values 6, values 8, values 9, values 10, values 11, values 12,
  values 13, values 14, values 15, values 16, values 17, values 19,
  values 20, values 22, values 26, values 27, values 28, values 29,
  values 30, values 31, values 32, values 33, values 34, values 35,
  values 37, values 38, values 40, values 41, values 42, values 43,
  values 44, values 45, values 46, values 47, values 49, values 50,
  values 51, (values 51)⁻¹, values 52, values 53, values 54,
  values 56, (values 56)⁻¹, values 58, values 59, values 60,
  values 61, values 62, values 66, values 67, values 68, values 69,
  values 71, values 72, values 73, values 74
]

noncomputable def branch11Values {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 66 → R := ![
  (values 73)⁻¹, (column2FactorA values)⁻¹,
  (column2FactorB values)⁻¹, slotDeterminant values 1,
  (factorGb values)⁻¹, (factorL values)⁻¹,
  (values 51 + values 56)⁻¹, (values 28)⁻¹,
  (slotDeterminant values 1)⁻¹, values 1, values 3, values 5,
  values 6, values 8, values 9, values 11, values 12, values 14,
  values 15, values 17, values 19, values 20, values 22, values 25,
  values 26, values 27, values 28, values 29, values 30, values 31,
  values 32, values 33, values 34, values 35, values 37, values 38,
  values 40, values 41, values 42, values 43, values 44, values 45,
  values 46, values 47, values 49, values 50, values 51,
  (values 51)⁻¹, values 52, values 53, values 54, values 56,
  (values 56)⁻¹, values 58, values 59, values 60, values 61,
  values 62, values 66, values 67, values 68, values 69, values 71,
  values 72, values 73, values 74
]

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-- The diagonal `w_45_11` cannot vanish on this chart.  Otherwise canonical
rows 607 and 606 force `factorL * (w_24_11+w_25_11)=0`. -/
theorem w45_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hpivotSum : values 51 + values 56 ≠ 0)
    (heq : values 31 = values 39)
    (h02 : values 4 = 0) : values 73 ≠ 0 := by
  have reductions := chart1_common_reductions values base hdet chart
  rcases reductions with
    ⟨h13, h35, h34, h34_10, h25_10, h25_12, h34_12⟩
  rcases chart with ⟨h23, h12⟩
  have h01 := w01_zero_of_both_pivots_nonzero
    values base hdet ⟨h23, h12⟩ h24 h25
  have h01_22 := w01_22_zero_of_equal_secondary
    values base hdet ⟨h23, h12⟩ h24 h25 heq
  have hdiag := diagonal_sum_zero_of_both_pivots_nonzero
    values base hdet ⟨h23, h12⟩ h24 h25
  have h03 : values 7 = 0 := by linear_combination hdiag - h02
  obtain ⟨hL, _hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
  have source0 : sourceValue values (leafSourceIndex 0) = 0 :=
    base (leafSourceIndex 0) (fun slot => leaf_source_not_determinant 0 slot)
  have source2 : sourceValue values (leafSourceIndex 2) = 0 :=
    base (leafSourceIndex 2) (fun slot => leaf_source_not_determinant 2 slot)
  intro h45
  simp (config := { maxSteps := 3000000 }) [sourceValue, leafSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h01_22, h02, h03, h13, h35, h34, h34_10,
    h25_10, h25_12, h34_12, h23, heq, h45] at source0 source2
  have product : factorL values * (values 51 + values 56) = 0 := by
    change (values 25 + values 33) * (values 51 + values 56) = 0
    linear_combination source2 - source0
  exact hL ((mul_eq_zero.mp product).resolve_right hpivotSum)

/-- A nonzero `A` kills the three colour-2 entries on edge 04. -/
theorem w04_column2_zero_of_factorA_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hA : column2FactorA values ≠ 0) :
    values 10 = 0 ∧ values 13 = 0 ∧ values 16 = 0 := by
  have reductions := chart1_common_reductions values base hdet chart
  rcases reductions with
    ⟨_h13, h35, _h34, _h34_10, _h25_10, _h25_12, h34_12⟩
  have h01 := w01_zero_of_both_pivots_nonzero
    values base hdet chart h24 h25
  have source1 : sourceValue values (leafSourceIndex 1) = 0 :=
    base (leafSourceIndex 1) (fun slot => leaf_source_not_determinant 1 slot)
  have source12 : sourceValue values (leafSourceIndex 12) = 0 :=
    base (leafSourceIndex 12) (fun slot => leaf_source_not_determinant 12 slot)
  have source16 : sourceValue values (leafSourceIndex 16) = 0 :=
    base (leafSourceIndex 16) (fun slot => leaf_source_not_determinant 16 slot)
  simp (config := { maxSteps := 3000000 }) [sourceValue, leafSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly, column2FactorA,
    h01, h35, h34_12] at source1 source12 source16
  have product1 : values 10 * column2FactorA values = 0 := by
    simp only [column2FactorA]
    linear_combination -source1
  have product12 : values 13 * column2FactorA values = 0 := by
    simp only [column2FactorA]
    linear_combination -source12
  have product16 : values 16 * column2FactorA values = 0 := by
    simp only [column2FactorA]
    linear_combination -source16
  constructor
  · exact (mul_eq_zero.mp product1).resolve_right hA
  constructor
  · exact (mul_eq_zero.mp product12).resolve_right hA
  · exact (mul_eq_zero.mp product16).resolve_right hA

/-- A nonzero `B` kills the three colour-2 entries on edge 05. -/
theorem w05_column2_zero_of_factorB_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hB : column2FactorB values ≠ 0) :
    values 18 = 0 ∧ values 21 = 0 ∧ values 24 = 0 := by
  have reductions := chart1_common_reductions values base hdet chart
  rcases reductions with
    ⟨_h13, _h35, _h34, _h34_10, _h25_10, h25_12, _h34_12⟩
  have h01 := w01_zero_of_both_pivots_nonzero
    values base hdet chart h24 h25
  have source3 : sourceValue values (leafSourceIndex 3) = 0 :=
    base (leafSourceIndex 3) (fun slot => leaf_source_not_determinant 3 slot)
  have source13 : sourceValue values (leafSourceIndex 13) = 0 :=
    base (leafSourceIndex 13) (fun slot => leaf_source_not_determinant 13 slot)
  have source18 : sourceValue values (leafSourceIndex 18) = 0 :=
    base (leafSourceIndex 18) (fun slot => leaf_source_not_determinant 18 slot)
  simp (config := { maxSteps := 3000000 }) [sourceValue, leafSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly, column2FactorB,
    h01, h25_12] at source3 source13 source18
  have product3 : values 18 * column2FactorB values = 0 := by
    simp only [column2FactorB]
    linear_combination source3
  have product13 : values 21 * column2FactorB values = 0 := by
    simp only [column2FactorB]
    linear_combination source13
  have product18 : values 24 * column2FactorB values = 0 := by
    simp only [column2FactorB]
    linear_combination source18
  constructor
  · exact (mul_eq_zero.mp product3).resolve_right hB
  constructor
  · exact (mul_eq_zero.mp product13).resolve_right hB
  · exact (mul_eq_zero.mp product18).resolve_right hB

private structure DiagzeroData {R : Type*} [Field R]
    (values : Fin 75 → R) : Prop where
  h23 : values 48 = 0
  h12 : values 28 ≠ 0
  h01 : values 0 = 0
  h01_22 : values 2 = 0
  h02 : values 4 = 0
  h03 : values 7 = 0
  h13 : values 36 = values 28
  h35 : values 70 = -values 56
  h34 : values 64 = -values 51
  h34_10 : values 63 = 0
  h25_10 : values 55 = 0
  h25_12 : values 57 = 0
  h34_12 : values 65 = 0
  heq : values 31 = values 39
  affine : values 23 = values 15 + slotDeterminant values 1
  hL : factorL values ≠ 0
  hGb : factorGb values ≠ 0
  h45 : values 73 ≠ 0

private theorem common_data
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hpivotSum : values 51 + values 56 ≠ 0)
    (heq : values 31 = values 39)
    (h02 : values 4 = 0) : DiagzeroData values := by
  rcases chart with ⟨h23, h12⟩
  have reductions := chart1_common_reductions values base hdet ⟨h23, h12⟩
  rcases reductions with
    ⟨h13, h35, h34, h34_10, h25_10, h25_12, h34_12⟩
  have h01 := w01_zero_of_both_pivots_nonzero
    values base hdet ⟨h23, h12⟩ h24 h25
  have h01_22 := w01_22_zero_of_equal_secondary
    values base hdet ⟨h23, h12⟩ h24 h25 heq
  have hdiag := diagonal_sum_zero_of_both_pivots_nonzero
    values base hdet ⟨h23, h12⟩ h24 h25
  have h03 : values 7 = 0 := by linear_combination hdiag - h02
  have affine : values 23 = values 15 + slotDeterminant values 1 := by
    simp [slotDeterminant, slotA1, slotB1, slotA2, slotB2]
  obtain ⟨hL, hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
  have h45 := w45_nonzero values base hdet ⟨h23, h12⟩ h24 h25
    hpivotSum heq h02
  exact ⟨h23, h12, h01, h01_22, h02, h03, h13, h35, h34,
    h34_10, h25_10, h25_12, h34_12, heq, affine, hL, hGb, h45⟩

private theorem refutes_branch00
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hpivotSum : values 51 + values 56 ≠ 0)
    (heq : values 31 = values 39)
    (h02 : values 4 = 0)
    (hA : column2FactorA values = 0)
    (hB : column2FactorB values = 0) : False := by
  obtain ⟨h23, h12, h01, h01_22, h02, h03, h13, h35, h34,
      h34_10, h25_10, h25_12, h34_12, heq, affine, hL, hGb, h45⟩ :=
    common_data values base hdet chart h24 h25 hpivotSum heq h02
  have h12_00 : values 25 = (values 56)⁻¹ := by
    have product : values 25 * values 56 = 1 := by
      simpa [column2FactorA] using sub_eq_zero.mp hA
    simpa [one_div] using (eq_div_iff h25).2 product
  have h13_00 : values 33 = -(values 51)⁻¹ := by
    have product : values 33 * values 51 = -1 := by
      simpa [column2FactorB] using (eq_neg_of_add_eq_zero_left hB)
    simpa [div_eq_mul_inv] using (eq_div_iff h24).2 product
  have source15 : sourceValue values (leafSourceIndex 15) = 0 :=
    base (leafSourceIndex 15) (fun slot => leaf_source_not_determinant 15 slot)
  have source17 : sourceValue values (leafSourceIndex 17) = 0 :=
    base (leafSourceIndex 17) (fun slot => leaf_source_not_determinant 17 slot)
  have factorGbInverse :
      factorGb values * (factorGb values)⁻¹ - 1 = 0 := by simp [hGb]
  have h24Inverse : values 51 * (values 51)⁻¹ - 1 = 0 := by simp [h24]
  have h25Inverse : values 56 * (values 56)⁻¹ - 1 = 0 := by simp [h25]
  simp (config := { maxSteps := 3000000 }) [sourceValue, leafSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h01_22, h02, h03, h13, h35, h34, h34_10,
    h25_10, h25_12, h34_12, h23, heq] at source15 source17
  rw [affine] at source15 source17
  apply
    Krenn.FrozenCase0NoncollapseType01Chart1DiagzeroAB00Certificate.selectedHasNoCommonZero
      (branch00Values values)
  intro index
  fin_cases index
  all_goals
    simp (config := { maxSteps := 3000000 }) [
      Krenn.FrozenCase0NoncollapseType01Chart1DiagzeroAB00Certificate.selectedEquations,
      branch00Values,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2,
      factorGb, h24, h25]
  · rw [affine]
    rw [h12_00] at source15
    field_simp [h25] at source15 ⊢
    ring_nf at source15 ⊢
    exact source15
  · rw [h13_00] at source17
    field_simp [h24, h25] at source17
    ring_nf at source17 ⊢
    have product : values 15 * values 56 = 0 := by
      linear_combination -source17
    exact (mul_eq_zero.mp product).resolve_right h25
  · simp only [factorGb] at factorGbInverse
    ring_nf at factorGbInverse ⊢
    exact factorGbInverse

private theorem refutes_branch10
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hpivotSum : values 51 + values 56 ≠ 0)
    (heq : values 31 = values 39)
    (h02 : values 4 = 0)
    (hA : column2FactorA values ≠ 0)
    (hB : column2FactorB values = 0) : False := by
  obtain ⟨h23, h12, h01, h01_22, h02, h03, h13, h35, h34,
      h34_10, h25_10, h25_12, h34_12, heq, affine, _hL, _hGb, _h45⟩ :=
    common_data values base hdet chart h24 h25 hpivotSum heq h02
  obtain ⟨h04_02, h04_12, h04_22⟩ :=
    w04_column2_zero_of_factorA_nonzero values base hdet chart h24 h25 hA
  have h13_00 : values 33 = -(values 51)⁻¹ := by
    have product : values 33 * values 51 = -1 := by
      simpa [column2FactorB] using (eq_neg_of_add_eq_zero_left hB)
    simpa [div_eq_mul_inv] using (eq_div_iff h24).2 product
  have source6 : sourceValue values (leafSourceIndex 6) = 0 :=
    base (leafSourceIndex 6) (fun slot => leaf_source_not_determinant 6 slot)
  have source8 : sourceValue values (leafSourceIndex 8) = 0 :=
    base (leafSourceIndex 8) (fun slot => leaf_source_not_determinant 8 slot)
  have source11 : sourceValue values (leafSourceIndex 11) = 0 :=
    base (leafSourceIndex 11) (fun slot => leaf_source_not_determinant 11 slot)
  have source19 : sourceValue values (leafSourceIndex 19) = 0 :=
    base (leafSourceIndex 19) (fun slot => leaf_source_not_determinant 19 slot)
  have source20 : sourceValue values (leafSourceIndex 20) = 0 :=
    base (leafSourceIndex 20) (fun slot => leaf_source_not_determinant 20 slot)
  have source21 : sourceValue values (leafSourceIndex 21) = 0 :=
    base (leafSourceIndex 21) (fun slot => leaf_source_not_determinant 21 slot)
  have source23 : sourceValue values (leafSourceIndex 23) = 0 :=
    base (leafSourceIndex 23) (fun slot => leaf_source_not_determinant 23 slot)
  have source24 : sourceValue values (leafSourceIndex 24) = 0 :=
    base (leafSourceIndex 24) (fun slot => leaf_source_not_determinant 24 slot)
  simp (config := { maxSteps := 3000000 }) [sourceValue, leafSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h01_22, h02, h03, h13, h35, h34, h34_10,
    h25_10, h25_12, h34_12, h23, heq, h13_00,
    h04_02, h04_12, h04_22] at source6 source8 source11 source19 source20 source21 source23 source24
  rw [affine] at source21 source23
  apply
    Krenn.FrozenCase0NoncollapseType01Chart1DiagzeroAB10Certificate.selectedHasNoCommonZero
      (branch10Values values)
  intro index
  fin_cases index
  all_goals
    simp (config := { maxSteps := 3000000 }) [
      Krenn.FrozenCase0NoncollapseType01Chart1DiagzeroAB10Certificate.selectedEquations,
      branch10Values,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2,
      h04_02, h04_12, h04_22, h24, h25]
  all_goals
    ring_nf at source6 source8 source11 source19 source20 source21 source23 source24 ⊢
  all_goals try assumption
  · rw [affine]
    ring_nf
    linear_combination source21
  · rw [affine]
    rw [heq]
    ring_nf
    exact source23

private theorem refutes_branch01
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hpivotSum : values 51 + values 56 ≠ 0)
    (heq : values 31 = values 39)
    (h02 : values 4 = 0)
    (hA : column2FactorA values = 0)
    (hB : column2FactorB values ≠ 0) : False := by
  obtain ⟨h23, h12, h01, h01_22, h02, h03, h13, h35, h34,
      h34_10, h25_10, h25_12, h34_12, heq, affine, hL, _hGb, _h45⟩ :=
    common_data values base hdet chart h24 h25 hpivotSum heq h02
  obtain ⟨h05_02, h05_12, h05_22⟩ :=
    w05_column2_zero_of_factorB_nonzero values base hdet chart h24 h25 hB
  have h12_00 : values 25 = (values 56)⁻¹ := by
    have product : values 25 * values 56 = 1 := by
      simpa [column2FactorA] using sub_eq_zero.mp hA
    simpa [one_div] using (eq_div_iff h25).2 product
  have source0 : sourceValue values (leafSourceIndex 0) = 0 :=
    base (leafSourceIndex 0) (fun slot => leaf_source_not_determinant 0 slot)
  have source2 : sourceValue values (leafSourceIndex 2) = 0 :=
    base (leafSourceIndex 2) (fun slot => leaf_source_not_determinant 2 slot)
  have source4 : sourceValue values (leafSourceIndex 4) = 0 :=
    base (leafSourceIndex 4) (fun slot => leaf_source_not_determinant 4 slot)
  have source5 : sourceValue values (leafSourceIndex 5) = 0 :=
    base (leafSourceIndex 5) (fun slot => leaf_source_not_determinant 5 slot)
  have source7 : sourceValue values (leafSourceIndex 7) = 0 :=
    base (leafSourceIndex 7) (fun slot => leaf_source_not_determinant 7 slot)
  have source9 : sourceValue values (leafSourceIndex 9) = 0 :=
    base (leafSourceIndex 9) (fun slot => leaf_source_not_determinant 9 slot)
  have source10 : sourceValue values (leafSourceIndex 10) = 0 :=
    base (leafSourceIndex 10) (fun slot => leaf_source_not_determinant 10 slot)
  have source14 : sourceValue values (leafSourceIndex 14) = 0 :=
    base (leafSourceIndex 14) (fun slot => leaf_source_not_determinant 14 slot)
  have source15 : sourceValue values (leafSourceIndex 15) = 0 :=
    base (leafSourceIndex 15) (fun slot => leaf_source_not_determinant 15 slot)
  have source19 : sourceValue values (leafSourceIndex 19) = 0 :=
    base (leafSourceIndex 19) (fun slot => leaf_source_not_determinant 19 slot)
  have source20 : sourceValue values (leafSourceIndex 20) = 0 :=
    base (leafSourceIndex 20) (fun slot => leaf_source_not_determinant 20 slot)
  have source22 : sourceValue values (leafSourceIndex 22) = 0 :=
    base (leafSourceIndex 22) (fun slot => leaf_source_not_determinant 22 slot)
  have source24 : sourceValue values (leafSourceIndex 24) = 0 :=
    base (leafSourceIndex 24) (fun slot => leaf_source_not_determinant 24 slot)
  simp (config := { maxSteps := 3000000 }) [sourceValue, leafSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h01_22, h02, h03, h13, h35, h34, h34_10,
    h25_10, h25_12, h34_12, h23, heq, h12_00,
    h05_02, h05_12, h05_22] at source0 source2 source4 source5 source7 source9 source10 source14 source15 source19 source20 source22 source24
  rw [affine] at source14 source15
  simp [h25] at source0 source15
  apply
    Krenn.FrozenCase0NoncollapseType01Chart1DiagzeroAB01Certificate.selectedHasNoCommonZero
      (branch01Values values)
  intro index
  fin_cases index
  all_goals
    simp (config := { maxSteps := 3000000 }) [
      Krenn.FrozenCase0NoncollapseType01Chart1DiagzeroAB01Certificate.selectedEquations,
      branch01Values,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h12_00, h05_02, h05_12, h05_22,
      hdet, hL, h24, h25]
  all_goals
    ring_nf at source0 source2 source4 source5 source7 source9 source10 source14 source15 source19 source20 source22 source24 ⊢
  all_goals try assumption
  · rcases source15 with hsum | hzero
    · linear_combination -((values 56)⁻¹ * values 51) * hsum
    · exact (h24 hzero).elim
  · rw [← h12_00]
    have inverseIdentity : (factorL values)⁻¹ * factorL values = 1 := by
      simp [hL]
    simp only [factorL] at inverseIdentity
    simp only [factorL]
    linear_combination inverseIdentity

private theorem refutes_branch11
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hpivotSum : values 51 + values 56 ≠ 0)
    (heq : values 31 = values 39)
    (h02 : values 4 = 0)
    (hA : column2FactorA values ≠ 0)
    (hB : column2FactorB values ≠ 0) : False := by
  obtain ⟨h23, h12, h01, h01_22, h02, h03, h13, h35, h34,
      h34_10, h25_10, h25_12, h34_12, heq, _affine, _hL, _hGb, h45⟩ :=
    common_data values base hdet chart h24 h25 hpivotSum heq h02
  obtain ⟨h04_02, h04_12, h04_22⟩ :=
    w04_column2_zero_of_factorA_nonzero values base hdet chart h24 h25 hA
  obtain ⟨h05_02, h05_12, h05_22⟩ :=
    w05_column2_zero_of_factorB_nonzero values base hdet chart h24 h25 hB
  have source5 : sourceValue values (leafSourceIndex 5) = 0 :=
    base (leafSourceIndex 5) (fun slot => leaf_source_not_determinant 5 slot)
  have source6 : sourceValue values (leafSourceIndex 6) = 0 :=
    base (leafSourceIndex 6) (fun slot => leaf_source_not_determinant 6 slot)
  have source7 : sourceValue values (leafSourceIndex 7) = 0 :=
    base (leafSourceIndex 7) (fun slot => leaf_source_not_determinant 7 slot)
  have source8 : sourceValue values (leafSourceIndex 8) = 0 :=
    base (leafSourceIndex 8) (fun slot => leaf_source_not_determinant 8 slot)
  have source19 : sourceValue values (leafSourceIndex 19) = 0 :=
    base (leafSourceIndex 19) (fun slot => leaf_source_not_determinant 19 slot)
  have source20 : sourceValue values (leafSourceIndex 20) = 0 :=
    base (leafSourceIndex 20) (fun slot => leaf_source_not_determinant 20 slot)
  have source24 : sourceValue values (leafSourceIndex 24) = 0 :=
    base (leafSourceIndex 24) (fun slot => leaf_source_not_determinant 24 slot)
  simp (config := { maxSteps := 3000000 }) [sourceValue, leafSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h01_22, h02, h03, h13, h35, h34, h34_10,
    h25_10, h25_12, h34_12, h23, heq,
    h04_02, h04_12, h04_22, h05_02, h05_12, h05_22] at source5 source6 source7 source8 source19 source20 source24
  apply
    Krenn.FrozenCase0NoncollapseType01Chart1DiagzeroAB11Certificate.selectedHasNoCommonZero
      (branch11Values values)
  intro index
  fin_cases index
  all_goals
    simp (config := { maxSteps := 3000000 }) [
      Krenn.FrozenCase0NoncollapseType01Chart1DiagzeroAB11Certificate.selectedEquations,
      branch11Values,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h04_02, h04_12, h04_22, h05_02, h05_12, h05_22]
  all_goals
    ring_nf at source5 source6 source7 source8 source19 source20 source24 ⊢
  all_goals assumption

/-- The four exact certificate leaves exhaust the diagonal-zero subchart. -/
theorem refutes_equal_secondary_w02_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hpivotSum : values 51 + values 56 ≠ 0)
    (heq : values 31 = values 39)
    (h02 : values 4 = 0) : False := by
  by_cases hA : column2FactorA values = 0
  · by_cases hB : column2FactorB values = 0
    · exact refutes_branch00 values base hdet chart h24 h25 hpivotSum heq h02 hA hB
    · exact refutes_branch01 values base hdet chart h24 h25 hpivotSum heq h02 hA hB
  · by_cases hB : column2FactorB values = 0
    · exact refutes_branch10 values base hdet chart h24 h25 hpivotSum heq h02 hA hB
    · exact refutes_branch11 values base hdet chart h24 h25 hpivotSum heq h02 hA hB

/-- The equal-secondary branch is impossible: split on `w_02_11`. -/
theorem refutes_equal_secondary
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hpivotSum : values 51 + values 56 ≠ 0)
    (heq : values 31 = values 39) : False := by
  by_cases h02 : values 4 = 0
  · exact refutes_equal_secondary_w02_zero
      values base hdet chart h24 h25 hpivotSum heq h02
  · exact refutes_equal_secondary_w02_nonzero
      values base hdet chart h24 h25 heq h02

#print axioms w45_nonzero
#print axioms w04_column2_zero_of_factorA_nonzero
#print axioms w05_column2_zero_of_factorB_nonzero
#print axioms refutes_equal_secondary_w02_zero
#print axioms refutes_equal_secondary

end Krenn.FrozenCase0NoncollapseType01Chart1Diagzero
