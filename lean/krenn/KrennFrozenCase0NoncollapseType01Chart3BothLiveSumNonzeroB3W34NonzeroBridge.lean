import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge
import KrennFrozenCase0NoncollapseType01Chart3W12_12LiveW34Zero
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate

/-!
Semantic bridge for the chart-3, both-live, nonzero-sum B3 branch with
`w_34_11` live.  The strict certificate is small (eleven selected rows), but
its meaning is supplied here from the canonical frozen case-0 equations.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroBridge

open MvPolynomial
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3
open Krenn.SparseCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Canonical source rows driving the recorded B3 monomial-zero closure. -/
def closureSourceIndex : Fin 11 -> Fin 747 :=
  ![46, 148, 154, 328, 329, 162, 163, 325, 125, 128, 602]

theorem closure_source_not_determinant
    (index : Fin 11) (slot : Fin 18) :
    determinantSourceIndex slot ≠ closureSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, closureSourceIndex]

/--
The eleven zero coordinates used by the B3 leaf are consequences of the
named source rows.  This reconstructs the external monomial closure without
trusting its search trace.
-/
theorem closure_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h01 : values 1 ≠ 0) (h12_12 : values 29 ≠ 0)
    (h34 : values 64 ≠ 0) :
    values 61 = 0 /\ values 17 = 0 /\ values 18 = 0 /\ values 65 = 0 /\
      values 66 = 0 /\ values 67 = 0 /\ values 68 = 0 /\ values 57 = 0 /\
      values 24 = 0 /\ values 22 = 0 /\ values 71 = 0 := by
  rcases chart with ⟨h23, h12, h13⟩
  obtain ⟨_h24, _h25, h12_10⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLive.chart3_surviving_coordinates
      values base hdet ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet ⟨h23, h12, h13⟩ h24 h25
  have h13_12 : values 37 = 0 :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge.w13_12_zero_of_bothlive_sum_nonzero
      values base ⟨h23, h12, h13⟩ h13_10 hsum
  have s46 : sourceValue values (closureSourceIndex 0) = 0 :=
    base (closureSourceIndex 0) (closure_source_not_determinant 0)
  have s148 : sourceValue values (closureSourceIndex 1) = 0 :=
    base (closureSourceIndex 1) (closure_source_not_determinant 1)
  have s154 : sourceValue values (closureSourceIndex 2) = 0 :=
    base (closureSourceIndex 2) (closure_source_not_determinant 2)
  have s328 : sourceValue values (closureSourceIndex 3) = 0 :=
    base (closureSourceIndex 3) (closure_source_not_determinant 3)
  have s329 : sourceValue values (closureSourceIndex 4) = 0 :=
    base (closureSourceIndex 4) (closure_source_not_determinant 4)
  have s162 : sourceValue values (closureSourceIndex 5) = 0 :=
    base (closureSourceIndex 5) (closure_source_not_determinant 5)
  have s163 : sourceValue values (closureSourceIndex 6) = 0 :=
    base (closureSourceIndex 6) (closure_source_not_determinant 6)
  have s325 : sourceValue values (closureSourceIndex 7) = 0 :=
    base (closureSourceIndex 7) (closure_source_not_determinant 7)
  have s125 : sourceValue values (closureSourceIndex 8) = 0 :=
    base (closureSourceIndex 8) (closure_source_not_determinant 8)
  have s128 : sourceValue values (closureSourceIndex 9) = 0 :=
    base (closureSourceIndex 9) (closure_source_not_determinant 9)
  have s602 : sourceValue values (closureSourceIndex 10) = 0 :=
    base (closureSourceIndex 10) (closure_source_not_determinant 10)
  have h34_00 : values 61 = 0 := by
    have identity : sourceValue values (closureSourceIndex 0) = values 29 * values 61 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h13_10]
    rw [identity] at s46
    exact (mul_eq_zero.mp s46).resolve_left h12_12
  have h05_00 : values 17 = 0 := by
    have identity : sourceValue values (closureSourceIndex 1) =
        values 17 * values 29 * values 64 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h13]
    rw [identity] at s148
    exact (mul_eq_zero.mp ((mul_eq_zero.mp s148).resolve_right h34)).resolve_right h12_12
  have h05_02 : values 18 = 0 := by
    have identity : sourceValue values (closureSourceIndex 2) =
        values 18 * values 29 * values 64 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h13]
    rw [identity] at s154
    exact (mul_eq_zero.mp ((mul_eq_zero.mp s154).resolve_right h34)).resolve_right h12_12
  have h34_12 : values 65 = 0 := by
    have identity : sourceValue values (closureSourceIndex 3) = values 1 * values 65 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12_10, h13]
    rw [identity] at s328
    exact (mul_eq_zero.mp s328).resolve_left h01
  have h34_20 : values 66 = 0 := by
    have identity : sourceValue values (closureSourceIndex 4) = values 1 * values 66 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12_10, h13_12]
    rw [identity] at s329
    exact (mul_eq_zero.mp s329).resolve_left h01
  have h34_21 : values 67 = 0 := by
    have identity : sourceValue values (closureSourceIndex 5) = values 1 * values 67 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12_10, h13_12]
    rw [identity] at s162
    exact (mul_eq_zero.mp s162).resolve_left h01
  have h34_22 : values 68 = 0 := by
    have identity : sourceValue values (closureSourceIndex 6) = values 1 * values 68 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12_10, h13_12]
    rw [identity] at s163
    exact (mul_eq_zero.mp s163).resolve_left h01
  have h25_12 : values 57 = 0 := by
    have identity : sourceValue values (closureSourceIndex 7) = values 1 * values 57 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12, h13_10]
    rw [identity] at s325
    exact (mul_eq_zero.mp s325).resolve_left h01
  have h05_22 : values 24 = 0 := by
    have identity : sourceValue values (closureSourceIndex 8) = values 24 * values 29 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h13_10]
    rw [identity] at s125
    exact (mul_eq_zero.mp s125).resolve_right h12_12
  have h05_20 : values 22 = 0 := by
    have identity : sourceValue values (closureSourceIndex 9) =
        values 22 * values 29 * values 64 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h13]
    rw [identity] at s128
    exact (mul_eq_zero.mp ((mul_eq_zero.mp s128).resolve_right h34)).resolve_right h12_12
  have h35_22 : values 71 = 0 := by
    have identity : sourceValue values (closureSourceIndex 10) = values 29 * values 71 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h05_02, h13_12]
    rw [identity] at s602
    exact (mul_eq_zero.mp s602).resolve_left h12_12
  exact ⟨h34_00, h05_00, h05_02, h34_12, h34_20, h34_21, h34_22,
    h25_12, h05_22, h05_20, h35_22⟩

/-- Canonical coordinate projection for the 67-variable B3 leaf. -/
noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 -> R) : Fin 67 -> R :=
  ![
    (values 51)⁻¹, (values 56)⁻¹, values 23 - values 15,
    (factorGb values)⁻¹, (factorL values)⁻¹,
    (values 51 + values 56)⁻¹, (slotDeterminant values 1)⁻¹,
    values 0, values 1, values 2, values 3, values 4, values 5,
    values 6, values 7, values 8, values 9, values 10, values 11,
    values 12, values 13, values 14, values 15, values 16,
    values 19, values 20, values 21, values 25, values 26, values 29,
    values 30, values 31, values 32, values 33, values 34, values 38,
    values 39, values 40, values 41, values 42, values 43, values 44,
    values 45, values 46, values 47, values 49, values 50, values 51,
    values 52, values 53, values 54, values 55, values 56, values 58,
    values 59, values 60, values 62, values 63, values 64, values 69,
    values 70, values 72, values 73, values 74,
    (values 29)⁻¹, (values 1)⁻¹, (values 64)⁻¹]

/-- Selected B3 source rows after the closure substitutions. -/
def directSourceIndex : Fin 8 -> Fin 747 := ![182, 605, 727, 354, 349, 343, 735, 746]

theorem direct_source_not_determinant
    (index : Fin 8) (slot : Fin 18) :
    determinantSourceIndex slot ≠ directSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, directSourceIndex]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem direct_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (h23 : values 48 = 0) (h12 : values 28 = 0) (h13 : values 36 = 0)
    (h13_10 : values 35 = 0) (h13_12 : values 37 = 0)
    (h12_10 : values 27 = 0)
    (h34_00 : values 61 = 0) (h05_00 : values 17 = 0)
    (h05_02 : values 18 = 0) (h34_12 : values 65 = 0)
    (h34_20 : values 66 = 0) (h34_21 : values 67 = 0)
    (h34_22 : values 68 = 0) (h25_12 : values 57 = 0)
    (h05_22 : values 24 = 0) (h05_20 : values 22 = 0)
    (h35_22 : values 71 = 0) :
    ∀ index : Fin 8,
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate.selectedEquations
          (Fin.castAdd 3 index)).toPoly = 0 := by
  intro index
  have source : sourceValue values (directSourceIndex index) = 0 :=
    base (directSourceIndex index) (direct_source_not_determinant index)
  fin_cases index <;>
    simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate.selectedEquations,
      sourceValue, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, directSourceIndex,
      h23, h12, h13, h13_10, h13_12, h12_10,
      h34_00, h05_00, h05_02, h34_12, h34_20, h34_21, h34_22,
      h25_12, h05_22, h05_20, h35_22] at source ⊢ <;>
    ring_nf at source ⊢ <;>
    exact source

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem inverse_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R)
    (h24 : values 51 ≠ 0) (hsum : values 51 + values 56 ≠ 0)
    (h01 : values 1 ≠ 0) :
    eval₂Hom (Int.castRingHom R) (leafValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate.selectedEquations 8).toPoly = 0 ∧
    eval₂Hom (Int.castRingHom R) (leafValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate.selectedEquations 9).toPoly = 0 ∧
    eval₂Hom (Int.castRingHom R) (leafValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate.selectedEquations 10).toPoly = 0 := by
  have h24inv : (values 51)⁻¹ * values 51 = 1 := inv_mul_cancel₀ h24
  have hsuminv : (values 51 + values 56)⁻¹ * (values 51 + values 56) = 1 :=
    inv_mul_cancel₀ hsum
  have h01inv : (values 1) * (values 1)⁻¹ = 1 := mul_inv_cancel₀ h01
  constructor
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, h24inv]
  constructor
  · have identity :
        eval₂Hom (Int.castRingHom R) (leafValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate.selectedEquations 9).toPoly =
            (values 51 + values 56)⁻¹ * (values 51 + values 56) - 1 := by
        simp [leafValues,
          Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate.selectedEquations,
          SparsePoly.toPoly, SparseTerm.toPoly]
        ring
    rw [identity, hsuminv]
    ring
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, h01inv]

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000

/-- The live `w_34_11` B3 leaf is impossible by the transported eleven-row
strict exact certificate. -/
theorem refutes_chart3_both_live_sum_nonzero_b3_w34_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h01 : values 1 ≠ 0) (h12_12 : values 29 ≠ 0)
    (h34 : values 64 ≠ 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet ⟨h23, h12, h13⟩ h24 h25
  have h13_12 : values 37 = 0 :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge.w13_12_zero_of_bothlive_sum_nonzero
      values base ⟨h23, h12, h13⟩ h13_10 hsum
  obtain ⟨_h24, _h25, h12_10⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLive.chart3_surviving_coordinates
      values base hdet ⟨h23, h12, h13⟩
  obtain ⟨h34_00, h05_00, h05_02, h34_12, h34_20, h34_21, h34_22,
      h25_12, h05_22, h05_20, h35_22⟩ :=
    closure_zeros values base hdet ⟨h23, h12, h13⟩ h24 h25 hsum h01 h12_12 h34
  have direct := direct_selected_zero values base h23 h12 h13 h13_10 h13_12 h12_10
    h34_00 h05_00 h05_02 h34_12 h34_20 h34_21 h34_22 h25_12 h05_22 h05_20 h35_22
  obtain ⟨inv8, inv9, inv10⟩ := inverse_selected_zero values h24 hsum h01
  apply Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroCertificate.selectedHasNoCommonZero
    (leafValues values)
  intro index
  fin_cases index
  · exact direct 0
  · exact direct 1
  · exact direct 2
  · exact direct 3
  · exact direct 4
  · exact direct 5
  · exact direct 6
  · exact direct 7
  · exact inv8
  · exact inv9
  · exact inv10

/-- The B3 `w_34_11` split is exhaustive. -/
theorem refutes_chart3_both_live_sum_nonzero_b3_w12_12_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h01 : values 1 ≠ 0) (h12_12 : values 29 ≠ 0) : False := by
  by_cases h34 : values 64 = 0
  · exact Krenn.FrozenCase0NoncollapseType01Chart3W12_12LiveW34Zero.refutes_chart3_w12_12_live_w34_zero
      values base hdet chart h12_12 h34
  · exact refutes_chart3_both_live_sum_nonzero_b3_w34_nonzero
      values base hdet chart h24 h25 hsum h01 h12_12 h34

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroBridge.refutes_chart3_both_live_sum_nonzero_b3_w34_nonzero

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroBridge.refutes_chart3_both_live_sum_nonzero_b3_w12_12_live

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB3W34NonzeroBridge
