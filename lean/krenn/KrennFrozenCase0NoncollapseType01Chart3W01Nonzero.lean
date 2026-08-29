import KrennFrozenCase0NoncollapseType01Chart3
import KrennFrozenCase0NoncollapseType01Chart3W01NonzeroCertificate

/-!
Semantic bridge from canonical case-0 values to one strictly
certified substituted leaf of the chart-3 only-w25 branch.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3W01Nonzero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3
open Krenn.SparseCertificate
open MvPolynomial

def selectedSourceIndex : Fin 7 → Fin 747 := ![
  318, 652, 320, 231, 349, 336, 746
]

theorem selected_source_not_determinant (index : Fin 7)
    (slot : Fin 18) :
    determinantSourceIndex slot ≠ selectedSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, selectedSourceIndex]

noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 67 → R := ![
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
  values 9,
  values 10,
  values 11,
  values 12,
  values 13,
  values 14,
  values 15,
  values 16,
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
  values 50,
  values 52,
  values 53,
  values 54,
  values 55,
  values 56,
  values 61,
  values 62,
  values 63,
  values 64,
  values 65,
  values 66,
  values 67,
  values 68,
  values 69,
  values 70,
  values 71,
  values 72,
  values 73,
  values 74,
  (values 56)⁻¹,
  (values 42)⁻¹,
  (values 1)⁻¹
]

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem refutes_slot1_chart3_w01_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 = 0)
    (h13_12 : values 37 = 0)
    (h13_10 : values 35 = 0)
    (h03_00 : values 6 = 0)
    (h03_22 : values 8 = 0)
    (h12_12 : values 29 = 0)
    (h23_22 : values 49 = 0)
    (h25_12 : values 57 = 0)
    (h25_20 : values 58 = 0)
    (h25_21 : values 59 = 0)
    (h25_22 : values 60 = 0)
    (h25 : values 56 ≠ 0)
    (h14_11 : values 42 ≠ 0)
    (h01_11 : values 1 ≠ 0)
    : False := by
  rcases chart with ⟨hChart23, hChart12, hChart13⟩
  have hDelta : values 23 - values 15 ≠ 0 := by
    simpa [slotDeterminant, slotA1, slotB1, slotA2, slotB2] using hdet
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
  apply Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedHasNoCommonZero (leafValues values)
  intro index
  fin_cases index
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h24, h13_12, h13_10, h03_00, h03_22, h12_12, h23_22, h25_12, h25_20, h25_21, h25_22, h25, h14_11, h01_11] at source0 ⊢
    ring_nf at source0 ⊢
    exact source0
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h24, h13_12, h13_10, h03_00, h03_22, h12_12, h23_22, h25_12, h25_20, h25_21, h25_22, h25, h14_11, h01_11] at source1 ⊢
    ring_nf at source1 ⊢
    exact source1
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h24, h13_12, h13_10, h03_00, h03_22, h12_12, h23_22, h25_12, h25_20, h25_21, h25_22, h25, h14_11, h01_11] at source2 ⊢
    ring_nf at source2 ⊢
    exact source2
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h24, h13_12, h13_10, h03_00, h03_22, h12_12, h23_22, h25_12, h25_20, h25_21, h25_22, h25, h14_11, h01_11] at source3 ⊢
    ring_nf at source3 ⊢
    exact source3
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h24, h13_12, h13_10, h03_00, h03_22, h12_12, h23_22, h25_12, h25_20, h25_21, h25_22, h25, h14_11, h01_11] at source4 ⊢
    ring_nf at source4 ⊢
    exact source4
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h24, h13_12, h13_10, h03_00, h03_22, h12_12, h23_22, h25_12, h25_20, h25_21, h25_22, h25, h14_11, h01_11] at source5 ⊢
    ring_nf at source5 ⊢
    exact source5
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedEquations, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.selectedIndices, Krenn.FrozenCase0NoncollapseType01Chart3W01NonzeroCertificate.parentEquations, selectedSourceIndex, leafValues, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb, hChart23, hChart12, hChart13, h24, h13_12, h13_10, h03_00, h03_22, h12_12, h23_22, h25_12, h25_20, h25_21, h25_22, h25, h14_11, h01_11] at source6 ⊢
    ring_nf at source6 ⊢
    exact source6

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3W01Nonzero.refutes_slot1_chart3_w01_nonzero

end Krenn.FrozenCase0NoncollapseType01Chart3W01Nonzero
