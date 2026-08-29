import KrennFrozenCase0NoncollapseType01Chart1BothNonzero
import KrennFrozenCase0NoncollapseType01Chart1SumzeroBranch01Certificate
import KrennFrozenCase0NoncollapseType01Chart1SumzeroBranch10Certificate

/-!
Kernel connector for the opposite-pivot (`w_24_11 + w_25_11 = 0`) half of
physical non-collapse type 01, pivot chart 1.

An exhaustive split on `w_25_00` has two strict exact certificates.  The
second coordinate used during discovery is absent from both selected
certificate subfamilies, so it is not part of the theorem.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart1Sumzero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart1X24Zero
open Krenn.FrozenCase0NoncollapseType01Chart1BothNonzero
open Krenn.SparseCertificate
open MvPolynomial

def branchZeroSourceIndex : Fin 18 → Fin 747 := ![
  744, 643, 642, 453, 722, 366, 607, 500, 376,
  724, 606, 632, 146, 637, 295, 299, 298, 302
]

def branchNonzeroSourceIndex : Fin 25 → Fin 747 := ![
  156, 607, 184, 67, 218, 368, 159, 606, 652, 189,
  254, 193, 653, 150, 32, 605, 556, 24, 139, 299,
  144, 534, 431, 336, 746
]

theorem branchZero_source_not_determinant
    (index : Fin 18) (slot : Fin 18) :
    determinantSourceIndex slot ≠ branchZeroSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, branchZeroSourceIndex]

theorem branchNonzero_source_not_determinant
    (index : Fin 25) (slot : Fin 18) :
    determinantSourceIndex slot ≠ branchNonzeroSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, branchNonzeroSourceIndex]

noncomputable def branchZeroValues {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 69 → R := ![
  slotDeterminant values 1, (factorGb values)⁻¹,
  (factorL values)⁻¹, (values 28)⁻¹,
  (slotDeterminant values 1)⁻¹,
  values 1, values 2, values 3, values 4, values 5,
  values 6, values 7, values 8, values 9, values 10,
  values 11, values 12, values 13, values 14, values 15,
  values 16, values 17, values 18, values 19, values 20,
  values 21, values 22, values 24, values 25, values 26,
  values 27, values 28, values 29, values 30, values 31,
  values 32, values 33, values 34, values 35, values 37,
  values 38, values 39, values 40, values 41, values 42,
  values 43, values 44, values 45, values 46, values 47,
  values 49, values 50, values 51, (values 51)⁻¹,
  values 52, values 53, values 54, values 58, values 60,
  values 61, values 62, values 66, values 68, values 69,
  values 71, values 72, values 73, values 74, 0
]

noncomputable def branchNonzeroValues {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 69 → R := ![
  slotDeterminant values 1, (factorGb values)⁻¹,
  (factorL values)⁻¹, (values 28)⁻¹,
  (slotDeterminant values 1)⁻¹,
  values 1, values 2, values 3, values 4, values 5,
  values 6, values 7, values 8, values 9, values 10,
  values 11, values 12, values 13, values 14, values 15,
  values 16, values 17, values 18, values 19, values 20,
  values 21, values 22, values 24, values 25, values 26,
  values 27, values 28, values 29, values 30, values 31,
  values 32, values 33, values 34, values 35, values 37,
  values 38, values 39, values 40, values 41, values 42,
  values 43, values 44, values 45, values 46, values 47,
  values 49, values 50, values 51, (values 51)⁻¹,
  values 52, values 53, values 54, values 58, values 60,
  values 61, values 62, values 66, values 68, values 69,
  values 71, values 72, values 73, values 74, (values 53)⁻¹
]

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

private theorem common_data
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0) :
    values 0 = 0 ∧ values 36 = values 28 ∧
      values 70 = values 51 ∧ values 64 = -values 51 ∧
      values 63 = 0 ∧ values 55 = 0 ∧ values 57 = 0 ∧
      values 65 = 0 ∧ values 67 = 0 ∧ values 59 = 0 ∧
      values 23 = values 15 + slotDeterminant values 1 := by
  have reductions := chart1_common_reductions values base hdet chart
  rcases reductions with
    ⟨h13, h35, h34, h34_10, h25_10, h25_12, h34_12⟩
  have h01 := w01_zero_of_both_pivots_nonzero
    values base hdet chart h24 h25
  obtain ⟨h34_21, h25_21⟩ :=
    sum_zero_linear_reductions values base hdet chart h24 h25 hsum
  have h56 : values 56 = -values 51 := by
    linear_combination hsum
  have h70 : values 70 = values 51 := by
    rw [h35, h56]
    simp
  have affine : values 23 = values 15 + slotDeterminant values 1 := by
    simp [slotDeterminant, slotA1, slotB1, slotA2, slotB2]
  exact ⟨h01, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine⟩

private theorem refutes_w25_00_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h53 : values 53 = 0) : False := by
  rcases chart with ⟨h23, h12⟩
  obtain ⟨h01, h13, h70, h34, h34_10, h25_10, h25_12,
      h34_12, h34_21, h25_21, affine⟩ :=
    common_data values base hdet ⟨h23, h12⟩ h24 h25 hsum
  have h56 : values 56 = -values 51 := by
    linear_combination hsum
  have detInverse :
      slotDeterminant values 1 * (slotDeterminant values 1)⁻¹ - 1 = 0 := by
    simp [hdet]
  have pivotInverse : values 28 * (values 28)⁻¹ - 1 = 0 := by
    simp [h12]
  have h24Inverse : values 51 * (values 51)⁻¹ - 1 = 0 := by
    simp [h24]
  have sourceZero (index : Fin 18) :
      sourceValue values (branchZeroSourceIndex index) = 0 :=
    base (branchZeroSourceIndex index)
      (fun slot => branchZero_source_not_determinant index slot)
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
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source0
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source1
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source2
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source3
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source4
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source5
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source6
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source7
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source8
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source9
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source10
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source11
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source12
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine, h53,
    hdet, h12, h24] at source13
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, h53,
    hdet, h12, h24] at source14
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, h53,
    hdet, h12, h24] at source15
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, h53,
    hdet, h12, h24] at source16
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchZeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, h53,
    hdet, h12, h24] at source17
  rw [h56] at source8 source10 source15 source17
  have source3' : values 3 * values 72 + values 50 * values 17 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right h12
    linear_combination source3
  have source7' :
      values 72 * values 6 + values 69 * values 9 + values 61 * values 17 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right h12
    linear_combination source7
  simp [slotDeterminant, slotA1, slotB1, slotA2, slotB2] at detInverse
  apply
    Krenn.FrozenCase0NoncollapseType01Chart1SumzeroBranch01Certificate.selectedHasNoCommonZero
      (branchZeroValues values)
  intro index
  fin_cases index
  all_goals
    simp (config := { maxSteps := 3000000 }) [
      Krenn.FrozenCase0NoncollapseType01Chart1SumzeroBranch01Certificate.selectedEquations,
      branchZeroValues,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2,
      factorL, factorGb,
      h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
      h34_12, h34_21, h25_21, h53,
      hdet, h12, h24]
  all_goals try assumption
  all_goals ring_nf at source0 source1 source2 source3 source3' source4 source5 source6 source7 source7' source8 source9 source10 source11 source12 source13 source14 source15 source16 source17 detInverse pivotInverse h24Inverse ⊢
  all_goals assumption

private theorem refutes_w25_00_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h53 : values 53 ≠ 0) : False := by
  rcases chart with ⟨h23, h12⟩
  obtain ⟨h01, h13, h70, h34, h34_10, h25_10, h25_12,
      h34_12, h34_21, h25_21, affine⟩ :=
    common_data values base hdet ⟨h23, h12⟩ h24 h25 hsum
  have h56 : values 56 = -values 51 := by
    linear_combination hsum
  have h53Inverse : values 53 * (values 53)⁻¹ - 1 = 0 := by
    simp [h53]
  have sourceZero (index : Fin 25) :
      sourceValue values (branchNonzeroSourceIndex index) = 0 :=
    base (branchNonzeroSourceIndex index)
      (fun slot => branchNonzero_source_not_determinant index slot)
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
  have source20 := sourceZero 20
  have source21 := sourceZero 21
  have source22 := sourceZero 22
  have source23 := sourceZero 23
  have source24 := sourceZero 24
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source0
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source1
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source2
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source3
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source4
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source5
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source6
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source7
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source8
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source9
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source10
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source11
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source12
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source13
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source14
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source15
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source16
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source17
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source18
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21,
    hdet, h12, h24, h53] at source19
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source20
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source21
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source22
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source23
  simp (config := { maxSteps := 3000000 }) [sourceValue, branchNonzeroSourceIndex,
    Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGb,
    h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
    h34_12, h34_21, h25_21, affine,
    hdet, h12, h24, h53] at source24
  rw [h56] at source7 source9 source19
  have source4' : values 54 * values 10 + values 3 * values 74 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right h12
    linear_combination source4
  have source10' : values 18 * values 68 + values 10 * values 71 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right h12
    linear_combination source10
  have source21' :
      values 74 * values 8 + values 68 * values 24 + values 71 * values 16 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right h12
    linear_combination source21
  apply
    Krenn.FrozenCase0NoncollapseType01Chart1SumzeroBranch10Certificate.selectedHasNoCommonZero
      (branchNonzeroValues values)
  intro index
  fin_cases index
  all_goals
    simp (config := { maxSteps := 3000000 }) [
      Krenn.FrozenCase0NoncollapseType01Chart1SumzeroBranch10Certificate.selectedEquations,
      branchNonzeroValues,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2,
      factorL, factorGb,
      h01, h23, h13, h70, h34, h34_10, h25_10, h25_12,
      h34_12, h34_21, h25_21,
      hdet, h12, h24, h53]
  all_goals try assumption
  all_goals ring_nf at source0 source1 source2 source3 source4 source4' source5 source6 source7 source8 source9 source10 source10' source11 source12 source13 source14 source15 source16 source17 source18 source19 source20 source21 source21' source22 source23 source24 h53Inverse ⊢
  all_goals assumption

/-- The opposite-pivot half of type-01 pivot chart 1 is impossible. -/
theorem refutes_slot1_chart1_sumzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart1 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0) : False := by
  by_cases h53 : values 53 = 0
  · exact refutes_w25_00_zero values base hdet chart h24 h25 hsum h53
  · exact refutes_w25_00_nonzero values base hdet chart h24 h25 hsum h53

#print axioms refutes_slot1_chart1_sumzero

end Krenn.FrozenCase0NoncollapseType01Chart1Sumzero
