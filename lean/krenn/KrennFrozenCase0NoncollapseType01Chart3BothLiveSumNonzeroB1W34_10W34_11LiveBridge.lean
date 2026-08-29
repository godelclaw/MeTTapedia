import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveBridge
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate

/-!
Semantic reflection of the strict B1 leaf discovered with `w_34_10` and
`w_34_11` live.  Its selected equations do not use the `w_34_11` inverse,
so the transported theorem proves the stronger result requiring only
`w_34_10` live (with the already forced `w_34_12 = 0`).  Every selected
canonical row is transported from the frozen case-0 source; the remaining
rows are explicit factor or inverse relations justified below.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveBridge

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

def selectedSourceIndex : Fin 32 → Fin 747 := ![
  606, 381, 720, 382, 384, 388, 390, 350, 363, 604, 512, 710, 40, 605, 556, 660, 645, 644, 745, 663, 727, 22, 174, 360, 175, 348, 349, 488, 735, 450, 631, 746]

theorem selected_source_not_determinant (index : Fin 32) (slot : Fin 18) :
    determinantSourceIndex slot ≠ selectedSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, selectedSourceIndex]

noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 76 → R := ![
  (values 51)⁻¹,
  (values 56)⁻¹,
  slotDeterminant values 1,
  (factorGb values)⁻¹,
  (factorL values)⁻¹,
  (values 51 + values 56)⁻¹,
  (slotDeterminant values 1)⁻¹,
  values 0,
  values 1,
  values 2,
  values 3,
  values 4,
  values 5,
  values 6,
  values 7,
  values 8,
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
  values 56,
  values 58,
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
  (values 1)⁻¹,
  (values 63)⁻¹,
  (values 64)⁻¹
]

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedSimpArgs false in
theorem refutes_chart3_b1_w34_10_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0) (h01 : values 1 ≠ 0)
    (h12_12 : values 29 = 0)
    (h34_10 : values 63 ≠ 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet ⟨h23, h12, h13⟩ h24 h25
  have h13_12 : values 37 = 0 :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge.w13_12_zero_of_bothlive_sum_nonzero
      values base ⟨h23, h12, h13⟩ h13_10 hsum
  have h12_10 : values 27 = 0 :=
    (Krenn.FrozenCase0NoncollapseType01Chart3BothLive.chart3_surviving_coordinates
      values base hdet ⟨h23, h12, h13⟩).2.2
  obtain ⟨h25_12, h25_21, h25_22⟩ :=
    w25_tail_zero_of_both_opposite_pivots_live values base hdet ⟨h23, h12, h13⟩ h24 h25 h12_12 h01
  obtain ⟨h34_12, h34_20, h34_21, h34_22⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveBridge.w34_tail_zero_of_chart3_w12_10_w13_12_zero_w01_live
      values base ⟨h23, h12, h13⟩ h12_10 h13_12 h01
  obtain ⟨hL, hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
  have hDelta : values 23 - values 15 ≠ 0 := by
    simpa [slotDeterminant, slotA1, slotB1, slotA2, slotB2] using hdet
  have source0 : sourceValue values (selectedSourceIndex 0) = 0 :=
    base (selectedSourceIndex 0) (selected_source_not_determinant 0)
  have source1 : sourceValue values (selectedSourceIndex 1) = 0 :=
    base (selectedSourceIndex 1) (selected_source_not_determinant 1)
  have source2 : sourceValue values (selectedSourceIndex 2) = 0 :=
    base (selectedSourceIndex 2) (selected_source_not_determinant 2)
  have source3 : sourceValue values (selectedSourceIndex 3) = 0 :=
    base (selectedSourceIndex 3) (selected_source_not_determinant 3)
  have source4 : sourceValue values (selectedSourceIndex 4) = 0 :=
    base (selectedSourceIndex 4) (selected_source_not_determinant 4)
  have source5 : sourceValue values (selectedSourceIndex 5) = 0 :=
    base (selectedSourceIndex 5) (selected_source_not_determinant 5)
  have source6 : sourceValue values (selectedSourceIndex 6) = 0 :=
    base (selectedSourceIndex 6) (selected_source_not_determinant 6)
  have source7 : sourceValue values (selectedSourceIndex 7) = 0 :=
    base (selectedSourceIndex 7) (selected_source_not_determinant 7)
  have source8 : sourceValue values (selectedSourceIndex 8) = 0 :=
    base (selectedSourceIndex 8) (selected_source_not_determinant 8)
  have source9 : sourceValue values (selectedSourceIndex 9) = 0 :=
    base (selectedSourceIndex 9) (selected_source_not_determinant 9)
  have source10 : sourceValue values (selectedSourceIndex 10) = 0 :=
    base (selectedSourceIndex 10) (selected_source_not_determinant 10)
  have source11 : sourceValue values (selectedSourceIndex 11) = 0 :=
    base (selectedSourceIndex 11) (selected_source_not_determinant 11)
  have source12 : sourceValue values (selectedSourceIndex 12) = 0 :=
    base (selectedSourceIndex 12) (selected_source_not_determinant 12)
  have source13 : sourceValue values (selectedSourceIndex 13) = 0 :=
    base (selectedSourceIndex 13) (selected_source_not_determinant 13)
  have source14 : sourceValue values (selectedSourceIndex 14) = 0 :=
    base (selectedSourceIndex 14) (selected_source_not_determinant 14)
  have source15 : sourceValue values (selectedSourceIndex 15) = 0 :=
    base (selectedSourceIndex 15) (selected_source_not_determinant 15)
  have source16 : sourceValue values (selectedSourceIndex 16) = 0 :=
    base (selectedSourceIndex 16) (selected_source_not_determinant 16)
  have source17 : sourceValue values (selectedSourceIndex 17) = 0 :=
    base (selectedSourceIndex 17) (selected_source_not_determinant 17)
  have source18 : sourceValue values (selectedSourceIndex 18) = 0 :=
    base (selectedSourceIndex 18) (selected_source_not_determinant 18)
  have source19 : sourceValue values (selectedSourceIndex 19) = 0 :=
    base (selectedSourceIndex 19) (selected_source_not_determinant 19)
  have source20 : sourceValue values (selectedSourceIndex 20) = 0 :=
    base (selectedSourceIndex 20) (selected_source_not_determinant 20)
  have source21 : sourceValue values (selectedSourceIndex 21) = 0 :=
    base (selectedSourceIndex 21) (selected_source_not_determinant 21)
  have source22 : sourceValue values (selectedSourceIndex 22) = 0 :=
    base (selectedSourceIndex 22) (selected_source_not_determinant 22)
  have source23 : sourceValue values (selectedSourceIndex 23) = 0 :=
    base (selectedSourceIndex 23) (selected_source_not_determinant 23)
  have source24 : sourceValue values (selectedSourceIndex 24) = 0 :=
    base (selectedSourceIndex 24) (selected_source_not_determinant 24)
  have source25 : sourceValue values (selectedSourceIndex 25) = 0 :=
    base (selectedSourceIndex 25) (selected_source_not_determinant 25)
  have source26 : sourceValue values (selectedSourceIndex 26) = 0 :=
    base (selectedSourceIndex 26) (selected_source_not_determinant 26)
  have source27 : sourceValue values (selectedSourceIndex 27) = 0 :=
    base (selectedSourceIndex 27) (selected_source_not_determinant 27)
  have source28 : sourceValue values (selectedSourceIndex 28) = 0 :=
    base (selectedSourceIndex 28) (selected_source_not_determinant 28)
  have source29 : sourceValue values (selectedSourceIndex 29) = 0 :=
    base (selectedSourceIndex 29) (selected_source_not_determinant 29)
  have source30 : sourceValue values (selectedSourceIndex 30) = 0 :=
    base (selectedSourceIndex 30) (selected_source_not_determinant 30)
  have source31 : sourceValue values (selectedSourceIndex 31) = 0 :=
    base (selectedSourceIndex 31) (selected_source_not_determinant 31)
  apply Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedHasNoCommonZero (leafValues values)
  intro index
  fin_cases index
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source0 ⊢ <;>
      ring_nf at source0 ⊢ <;>
      exact source0
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source1 ⊢ <;>
      ring_nf at source1 ⊢ <;>
      exact source1
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source2 ⊢ <;>
      ring_nf at source2 ⊢ <;>
      exact source2
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source3 ⊢ <;>
      ring_nf at source3 ⊢ <;>
      exact source3
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source4 ⊢ <;>
      ring_nf at source4 ⊢ <;>
      exact source4
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source5 ⊢ <;>
      ring_nf at source5 ⊢ <;>
      exact source5
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source6 ⊢ <;>
      ring_nf at source6 ⊢ <;>
      exact source6
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source7 ⊢ <;>
      ring_nf at source7 ⊢ <;>
      exact source7
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source8 ⊢ <;>
      ring_nf at source8 ⊢ <;>
      exact source8
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source9 ⊢ <;>
      ring_nf at source9 ⊢ <;>
      exact source9
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source10 ⊢ <;>
      ring_nf at source10 ⊢ <;>
      exact source10
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source11 ⊢ <;>
      ring_nf at source11 ⊢ <;>
      exact source11
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source12 ⊢
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source13 ⊢ <;>
      ring_nf at source13 ⊢ <;>
      exact source13
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source14 ⊢ <;>
      ring_nf at source14 ⊢ <;>
      exact source14
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source15 ⊢ <;>
      ring_nf at source15 ⊢ <;>
      exact source15
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source16 ⊢ <;>
      ring_nf at source16 ⊢ <;>
      exact source16
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source17 ⊢ <;>
      ring_nf at source17 ⊢ <;>
      exact source17
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source18 ⊢ <;>
      ring_nf at source18 ⊢ <;>
      exact source18
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source19 ⊢ <;>
      ring_nf at source19 ⊢ <;>
      exact source19
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source20 ⊢ <;>
      ring_nf at source20 ⊢ <;>
      exact source20
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source21 ⊢ <;>
      ring_nf at source21 ⊢ <;>
      exact source21
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source22 ⊢ <;>
      ring_nf at source22 ⊢ <;>
      exact source22
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source23 ⊢ <;>
      ring_nf at source23 ⊢ <;>
      exact source23
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source24 ⊢ <;>
      ring_nf at source24 ⊢ <;>
      exact source24
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source25 ⊢ <;>
      ring_nf at source25 ⊢ <;>
      exact source25
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source26 ⊢ <;>
      ring_nf at source26 ⊢ <;>
      exact source26
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source27 ⊢ <;>
      ring_nf at source27 ⊢ <;>
      exact source27
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source28 ⊢ <;>
      ring_nf at source28 ⊢ <;>
      exact source28
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source29 ⊢ <;>
      ring_nf at source29 ⊢ <;>
      exact source29
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source30 ⊢ <;>
      ring_nf at source30 ⊢ <;>
      exact source30
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_10, h34_12, h34_20, h34_21, h34_22] at source31 ⊢ <;>
      ring_nf at source31 ⊢ <;>
      exact source31
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2, mul_inv_cancel₀ hDelta]
  · have s295 : sourceValue values 295 = 0 :=
      base 295 (fun slot => amplitude_source_not_determinant 0 slot)
    have s299 : sourceValue values 299 = 0 :=
      base 299 (fun slot => amplitude_source_not_determinant 1 slot)
    have s360 : sourceValue values 360 = 0 :=
      base 360 (fun slot => amplitude_source_not_determinant 2 slot)
    have reflected := reflected_factor_identity values
    rw [s295, s299, s360] at reflected
    have hReflected : -slotDeterminant values 1 + factorL values * factorGa values = 0 := by
      simpa using reflected.symm
    have identity :
        eval₂Hom (Int.castRingHom R) (leafValues values) (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations 33).toPoly =
          -slotDeterminant values 1 + factorL values * factorGa values := by
      simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly,
        slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa]
      ring
    simpa using identity.trans hReflected
  · have hGbInverse : (factorGb values)⁻¹ * factorGb values - 1 = 0 := by
      rw [inv_mul_cancel₀ hGb]
      ring
    have identity :
        eval₂Hom (Int.castRingHom R) (leafValues values) (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations 34).toPoly =
          (factorGb values)⁻¹ * factorGb values - 1 := by
      simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly,
        factorGb, slotDeterminant, slotA1, slotB1, slotA2, slotB2]
      ring
    simpa using identity.trans hGbInverse
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly,
      mul_inv_cancel₀ h24, inv_mul_cancel₀ h24]
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly,
      mul_inv_cancel₀ h25, inv_mul_cancel₀ h25]
  · have hSumInverse : (values 51 + values 56)⁻¹ * (values 51 + values 56) - 1 = 0 := by
      rw [inv_mul_cancel₀ hsum]
      ring
    have identity :
        eval₂Hom (Int.castRingHom R) (leafValues values) (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations 37).toPoly =
          (values 51 + values 56)⁻¹ * (values 51 + values 56) - 1 := by
      simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly]
      ring
    simpa using identity.trans hSumInverse
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly, h12_10]
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly, h12_12]
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly,
      mul_inv_cancel₀ h01, inv_mul_cancel₀ h01]
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly,
      mul_inv_cancel₀ h34_10, inv_mul_cancel₀ h34_10]
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveCertificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly, h34_12]
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveBridge.refutes_chart3_b1_w34_10_live

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_10W34_11LiveBridge
