import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveBridge
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate

/-!
Semantic reflection of the strict B1 `w_05` live/zero certificate.

The selected identity uses no condition on `w_05_00`. This bridge therefore
proves the stronger fact that `w_05_02 ≠ 0` and `w_05_22 = 0` alone refute
the chart-3 B1 geometry, covering both historical b2 and b6 leaves.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05Live02Zero22Bridge

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

def selectedSourceIndex : Fin 12 → Fin 747 := ![
  394, 32, 40, 605, 660, 644, 663, 354, 349, 488, 336, 746
]

theorem selected_source_not_determinant (index : Fin 12) (slot : Fin 18) :
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
  (values 64)⁻¹,
  (values 18)⁻¹
]

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedSimpArgs false in
theorem refutes_chart3_b1_w05_02_live_w05_22_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0) (h01 : values 1 ≠ 0)
    (h12_12 : values 29 = 0)
    (h05_02 : values 18 ≠ 0) (h05_22 : values 24 = 0) : False := by
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
  obtain ⟨_hL, _hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
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
  apply Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedHasNoCommonZero (leafValues values)
  intro index
  fin_cases index
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_12, h34_20, h34_21, h34_22, h05_02, h05_22] at source0 ⊢ <;> ring_nf at source0 ⊢ <;> exact source0
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_12, h34_20, h34_21, h34_22, h05_02, h05_22] at source1 ⊢ <;> ring_nf at source1 ⊢ <;> exact source1
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_12, h34_20, h34_21, h34_22, h05_02, h05_22] at source2 ⊢
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_12, h34_20, h34_21, h34_22, h05_02, h05_22] at source3 ⊢ <;> ring_nf at source3 ⊢ <;> exact source3
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_12, h34_20, h34_21, h34_22, h05_02, h05_22] at source4 ⊢ <;> ring_nf at source4 ⊢ <;> exact source4
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_12, h34_20, h34_21, h34_22, h05_02, h05_22] at source5 ⊢ <;> ring_nf at source5 ⊢ <;> exact source5
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_12, h34_20, h34_21, h34_22, h05_02, h05_22] at source6 ⊢ <;> ring_nf at source6 ⊢ <;> exact source6
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_12, h34_20, h34_21, h34_22, h05_02, h05_22] at source7 ⊢ <;> ring_nf at source7 ⊢ <;> exact source7
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_12, h34_20, h34_21, h34_22, h05_02, h05_22] at source8 ⊢ <;> ring_nf at source8 ⊢ <;> exact source8
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_12, h34_20, h34_21, h34_22, h05_02, h05_22] at source9 ⊢ <;> ring_nf at source9 ⊢ <;> exact source9
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_12, h34_20, h34_21, h34_22, h05_02, h05_22] at source10 ⊢ <;> ring_nf at source10 ⊢ <;> exact source10
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, selectedSourceIndex, sourceValue, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb, h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h25_12, h25_21, h25_22, h34_12, h34_20, h34_21, h34_22, h05_02, h05_22] at source11 ⊢ <;> ring_nf at source11 ⊢ <;> exact source11
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly,
      mul_inv_cancel₀ h25, inv_mul_cancel₀ h25]
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly, h12_10]
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly, h12_12]
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly,
      mul_inv_cancel₀ h01, inv_mul_cancel₀ h01]
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly, h34_12]
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly,
      mul_inv_cancel₀ h05_02, inv_mul_cancel₀ h05_02]
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B2Certificate.selectedEquations, leafValues, SparsePoly.toPoly, SparseTerm.toPoly, h05_22]

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05Live02Zero22Bridge.refutes_chart3_b1_w05_02_live_w05_22_zero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05Live02Zero22Bridge
