import KrennFrozenCase0NoncollapseType01Chart3
import KrennFrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate

/-!
Semantic bridge from canonical case-0 values to one strict leaf
of the chart-3 only-w24 branch.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03Zero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3
open Krenn.SparseCertificate
open MvPolynomial

def selectedSourceIndex : Fin 23 → Fin 747 := ![
  607, 606, 377, 388, 738, 552, 556, 469, 646, 346, 645, 644, 745, 727, 351, 696, 360, 354, 349, 298, 343, 737, 746
]

theorem selected_source_not_determinant (index : Fin 23)
    (slot : Fin 18) :
    determinantSourceIndex slot ≠ selectedSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, selectedSourceIndex]

noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 66 → R := ![
  slotDeterminant values 1,
  (factorGb values)⁻¹,
  (factorL values)⁻¹,
  (slotDeterminant values 1)⁻¹,
  values 0,
  values 1,
  values 2,
  values 3,
  values 4,
  values 5,
  values 7,
  values 8,
  values 9,
  values 11,
  values 12,
  values 14,
  values 15,
  values 17,
  values 18,
  values 19,
  values 20,
  values 21,
  values 22,
  values 24,
  values 25,
  values 26,
  values 27,
  values 29,
  values 30,
  values 31,
  values 32,
  values 33,
  values 34,
  values 38,
  values 39,
  values 40,
  values 41,
  values 42,
  values 43,
  values 44,
  values 45,
  values 46,
  values 47,
  values 49,
  values 50,
  values 51,
  values 52,
  values 53,
  values 54,
  values 55,
  values 57,
  values 58,
  values 59,
  values 60,
  values 63,
  values 64,
  values 65,
  values 67,
  values 69,
  values 70,
  values 71,
  values 72,
  values 73,
  values 74,
  (values 51)⁻¹,
  (values 33)⁻¹
]

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem refutes_slot1_chart3_only_w24_w03_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h25 : values 56 = 0)
    (h13_12 : values 37 = 0)
    (h13_10 : values 35 = 0)
    (h34_00 : values 61 = 0)
    (h34_02 : values 62 = 0)
    (h34_20 : values 66 = 0)
    (h34_22 : values 68 = 0)
    (h04_02 : values 10 = 0)
    (h04_12 : values 13 = 0)
    (h04_22 : values 16 = 0)
    (h03_00 : values 6 = 0)
    (h24 : values 51 ≠ 0)
    (h13_00 : values 33 ≠ 0)
    : False := by
  rcases chart with ⟨hChart23, hChart12, hChart13⟩
  have hDelta : values 23 - values 15 ≠ 0 := by
    simpa [slotDeterminant, slotA1, slotB1, slotA2, slotB2] using hdet
  have hGb : factorGb values ≠ 0 :=
    (noncollapse_factor_geometry values base hdet).2.1
  have hGbFormula : factorGb values = values 23 * values 51 := by
    simp [factorGb, slotDeterminant, slotA1, slotB1, slotA2, slotB2, h25]
  have h05_21 : values 23 ≠ 0 := by
    rw [hGbFormula] at hGb
    exact (mul_ne_zero_iff.mp hGb).1
  have source0 : sourceValue values (selectedSourceIndex 0) = 0 :=
    base (selectedSourceIndex 0)
      (selected_source_not_determinant 0)
  have source1 : sourceValue values (selectedSourceIndex 1) = 0 :=
    base (selectedSourceIndex 1)
      (selected_source_not_determinant 1)
  have source2 : sourceValue values (selectedSourceIndex 2) = 0 :=
    base (selectedSourceIndex 2)
      (selected_source_not_determinant 2)
  have source3 : sourceValue values (selectedSourceIndex 3) = 0 :=
    base (selectedSourceIndex 3)
      (selected_source_not_determinant 3)
  have source4 : sourceValue values (selectedSourceIndex 4) = 0 :=
    base (selectedSourceIndex 4)
      (selected_source_not_determinant 4)
  have source5 : sourceValue values (selectedSourceIndex 5) = 0 :=
    base (selectedSourceIndex 5)
      (selected_source_not_determinant 5)
  have source6 : sourceValue values (selectedSourceIndex 6) = 0 :=
    base (selectedSourceIndex 6)
      (selected_source_not_determinant 6)
  have source7 : sourceValue values (selectedSourceIndex 7) = 0 :=
    base (selectedSourceIndex 7)
      (selected_source_not_determinant 7)
  have source8 : sourceValue values (selectedSourceIndex 8) = 0 :=
    base (selectedSourceIndex 8)
      (selected_source_not_determinant 8)
  have source9 : sourceValue values (selectedSourceIndex 9) = 0 :=
    base (selectedSourceIndex 9)
      (selected_source_not_determinant 9)
  have source10 : sourceValue values (selectedSourceIndex 10) = 0 :=
    base (selectedSourceIndex 10)
      (selected_source_not_determinant 10)
  have source11 : sourceValue values (selectedSourceIndex 11) = 0 :=
    base (selectedSourceIndex 11)
      (selected_source_not_determinant 11)
  have source12 : sourceValue values (selectedSourceIndex 12) = 0 :=
    base (selectedSourceIndex 12)
      (selected_source_not_determinant 12)
  have source13 : sourceValue values (selectedSourceIndex 13) = 0 :=
    base (selectedSourceIndex 13)
      (selected_source_not_determinant 13)
  have source14 : sourceValue values (selectedSourceIndex 14) = 0 :=
    base (selectedSourceIndex 14)
      (selected_source_not_determinant 14)
  have source15 : sourceValue values (selectedSourceIndex 15) = 0 :=
    base (selectedSourceIndex 15)
      (selected_source_not_determinant 15)
  have source16 : sourceValue values (selectedSourceIndex 16) = 0 :=
    base (selectedSourceIndex 16)
      (selected_source_not_determinant 16)
  have source17 : sourceValue values (selectedSourceIndex 17) = 0 :=
    base (selectedSourceIndex 17)
      (selected_source_not_determinant 17)
  have source18 : sourceValue values (selectedSourceIndex 18) = 0 :=
    base (selectedSourceIndex 18)
      (selected_source_not_determinant 18)
  have source19 : sourceValue values (selectedSourceIndex 19) = 0 :=
    base (selectedSourceIndex 19)
      (selected_source_not_determinant 19)
  have source20 : sourceValue values (selectedSourceIndex 20) = 0 :=
    base (selectedSourceIndex 20)
      (selected_source_not_determinant 20)
  have source21 : sourceValue values (selectedSourceIndex 21) = 0 :=
    base (selectedSourceIndex 21)
      (selected_source_not_determinant 21)
  have source22 : sourceValue values (selectedSourceIndex 22) = 0 :=
    base (selectedSourceIndex 22)
      (selected_source_not_determinant 22)
  apply Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedHasNoCommonZero (leafValues values)
  intro index
  fin_cases index
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source0 ⊢
    ring_nf at source0 ⊢
    exact source0
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source1 ⊢
    ring_nf at source1 ⊢
    exact source1
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source2 ⊢
    ring_nf at source2 ⊢
    exact source2
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source3 ⊢
    ring_nf at source3 ⊢
    exact source3
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source4 ⊢
    ring_nf at source4 ⊢
    exact source4
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source5 ⊢
    ring_nf at source5 ⊢
    exact source5
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source6 ⊢
    ring_nf at source6 ⊢
    exact source6
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source7 ⊢
    ring_nf at source7 ⊢
    exact source7
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source8 ⊢
    ring_nf at source8 ⊢
    exact source8
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source9 ⊢
    ring_nf at source9 ⊢
    exact source9
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source10 ⊢
    ring_nf at source10 ⊢
    exact source10
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source11 ⊢
    ring_nf at source11 ⊢
    exact source11
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source12 ⊢
    ring_nf at source12 ⊢
    exact source12
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source13 ⊢
    ring_nf at source13 ⊢
    exact source13
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source14 ⊢
    ring_nf at source14 ⊢
    exact source14
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source15 ⊢
    ring_nf at source15 ⊢
    exact source15
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source16 ⊢
    ring_nf at source16 ⊢
    exact source16
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source17 ⊢
    ring_nf at source17 ⊢
    exact source17
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source18 ⊢
    ring_nf at source18 ⊢
    exact source18
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source19 ⊢
    ring_nf at source19 ⊢
    exact source19
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source20 ⊢
    ring_nf at source20 ⊢
    exact source20
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source21 ⊢
    ring_nf at source21 ⊢
    exact source21
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00] at source22 ⊢
    ring_nf at source22 ⊢
    exact source22
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00, hGbFormula]
    field_simp [h24, h05_21]
    ring
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03ZeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h25, h13_12, h13_10, h34_00, h34_02, h34_20, h34_22, h04_02, h04_12, h04_22, h03_00, h24, h13_00, h13_00]

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03Zero.refutes_slot1_chart3_only_w24_w03_zero

end Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03Zero
