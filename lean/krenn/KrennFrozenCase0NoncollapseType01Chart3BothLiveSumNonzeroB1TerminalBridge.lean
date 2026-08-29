import KrennFrozenCase0NoncollapseType01Chart3
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate

/-!
Semantic bridge from the canonical case-0 system to the strict terminal
certificate for the chart-3, both-pivots-live, nonzero-sum, `b1` branch.

The bridge is deliberately finite and source-level: twenty selected
certificate rows are canonical source rows after the stated branch
reductions; the other six are explicit factor or inverse relations.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot

noncomputable def terminalValues {R : Type*} [Field R]
    (values : Fin 75 -> R) : Fin 62 -> R :=
  ![
    (values 51)⁻¹, (values 56)⁻¹, values 23 - values 15,
    -(factorL values) * (slotDeterminant values 1)⁻¹,
    -(factorGb values) * (slotDeterminant values 1)⁻¹,
    (values 51 + values 56)⁻¹, (slotDeterminant values 1)⁻¹,
    values 0, values 1, values 2, values 3, values 4, values 5,
    values 6, values 7, values 8, values 9, values 10, values 11,
    values 12, values 13, values 14, values 15, values 16, values 17,
    values 19, values 20, values 21, values 22, values 25, values 30,
    values 31, values 33, values 34, values 38, values 39, values 40,
    values 41, values 42, values 43, values 44, values 45, values 46,
    values 47, values 49, values 50, values 51, values 53, values 54,
    values 55, values 56, values 62, values 64, values 69, values 70,
    values 71, values 72, values 73, values 74,
    (values 1)⁻¹, (values 64)⁻¹, (values 17)⁻¹]

def directSourceIndex : Fin 20 -> Fin 747 := ![
  744, 643, 642, 383, 391, 386, 605, 726, 727, 22,
  295, 360, 591, 347, 494, 349, 705, 737, 674, 746
]

theorem direct_source_not_determinant (index : Fin 20) (slot : Fin 18) :
    determinantSourceIndex slot ≠ directSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, directSourceIndex]

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem w13_12_zero_of_bothlive_sum_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h13_10 : values 35 = 0)
    (hsum : values 51 + values 56 ≠ 0) : values 37 = 0 := by
  have source : sourceValue values 180 = 0 :=
    base 180 (Krenn.FrozenCase0NoncollapseType01Chart3.source180_not_determinant)
  rcases chart with ⟨_h23, h12, _h13⟩
  have identity : sourceValue values 180 = values 37 * (values 51 + values 56) := by
    simp [sourceValue, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h12, h13_10]
    ring
  rw [identity] at source
  exact (mul_eq_zero.mp source).resolve_right hsum

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem terminal_closure_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (h13 : values 36 = 0) (h13_10 : values 35 = 0) (h13_12 : values 37 = 0)
    (h01 : values 1 ≠ 0) (h05 : values 17 ≠ 0) (h34 : values 64 ≠ 0)
    (h05_02 : values 18 = 0) (h05_22 : values 24 = 0)
    (h34_00 : values 61 = 0) (h34_10 : values 63 = 0)
    (h34_12 : values 65 = 0) (h34_20 : values 66 = 0)
    (h34_22 : values 68 = 0) :
    values 27 = 0 ∧ values 29 = 0 ∧ values 67 = 0 ∧ values 58 = 0 ∧
      values 26 = 0 ∧ values 52 = 0 ∧ values 32 = 0 := by
  have s146 : sourceValue values 146 = 0 := by
    apply base 146
    intro slot
    fin_cases slot <;> simp [determinantSourceIndex]
  have s148 : sourceValue values 148 = 0 := by
    apply base 148
    intro slot
    fin_cases slot <;> simp [determinantSourceIndex]
  have s162 : sourceValue values 162 = 0 := by
    apply base 162
    intro slot
    fin_cases slot <;> simp [determinantSourceIndex]
  have s326 : sourceValue values 326 = 0 := by
    apply base 326
    intro slot
    fin_cases slot <;> simp [determinantSourceIndex]
  have s191 : sourceValue values 191 = 0 := by
    apply base 191
    intro slot
    fin_cases slot <;> simp [determinantSourceIndex]
  have s385 : sourceValue values 385 = 0 := by
    apply base 385
    intro slot
    fin_cases slot <;> simp [determinantSourceIndex]
  have s151 : sourceValue values 151 = 0 := by
    apply base 151
    intro slot
    fin_cases slot <;> simp [determinantSourceIndex]
  have h12_10 : values 27 = 0 := by
    have identity : sourceValue values 146 = values 17 * values 27 * values 64 := by
      simp [sourceValue, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h05_02, h05_22, h34_00, h34_10, h34_12, h34_20, h34_22, h13]
    rw [identity] at s146
    exact (mul_eq_zero.mp ((mul_eq_zero.mp s146).resolve_right h34)).resolve_left h05
  have h12_12 : values 29 = 0 := by
    have identity : sourceValue values 148 = values 17 * values 29 * values 64 := by
      simp [sourceValue, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h05_02, h05_22, h34_00, h34_10, h34_12, h34_20, h34_22, h13]
    rw [identity] at s148
    exact (mul_eq_zero.mp ((mul_eq_zero.mp s148).resolve_right h34)).resolve_left h05
  have h34_21 : values 67 = 0 := by
    have identity : sourceValue values 162 = values 1 * values 67 := by
      simp [sourceValue, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h05_02, h05_22, h34_00, h34_10, h34_12, h34_20, h34_22,
        h13_12, h12_10]
    rw [identity] at s162
    exact (mul_eq_zero.mp s162).resolve_left h01
  have h25_20 : values 58 = 0 := by
    have identity : sourceValue values 326 = values 58 * values 1 := by
      simp [sourceValue, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h05_02, h05_22, h34_00, h34_10, h34_12, h34_20, h34_22,
        h13_10, h12_12]
      ring
    rw [identity] at s326
    exact (mul_eq_zero.mp s326).resolve_right h01
  have h12_02 : values 26 = 0 := by
    have identity : sourceValue values 191 = values 17 * values 26 * values 64 := by
      simp [sourceValue, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h05_02, h05_22, h34_00, h34_10, h34_12, h34_20, h34_22,
        h12_10, h12_12, h25_20, h34_21]
    rw [identity] at s191
    exact (mul_eq_zero.mp ((mul_eq_zero.mp s191).resolve_right h34)).resolve_left h05
  have h24_22 : values 52 = 0 := by
    have identity : sourceValue values 385 = values 17 * values 52 := by
      simp [sourceValue, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h05_02, h05_22, h34_00, h34_10, h34_12, h34_20, h34_22,
        h12_10, h12_12, h25_20, h34_21, h12_02]
    rw [identity] at s385
    exact (mul_eq_zero.mp s385).resolve_left h05
  have h12_22 : values 32 = 0 := by
    have identity : sourceValue values 151 = values 17 * values 32 * values 64 := by
      simp [sourceValue, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h05_02, h05_22, h34_00, h34_10, h34_12, h34_20, h34_22,
        h12_10, h12_12, h25_20, h34_21, h12_02, h24_22]
    rw [identity] at s151
    exact (mul_eq_zero.mp ((mul_eq_zero.mp s151).resolve_right h34)).resolve_left h05
  exact ⟨h12_10, h12_12, h34_21, h25_20, h12_02, h24_22, h12_22⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem direct_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (h23 : values 48 = 0) (h12 : values 28 = 0) (h13 : values 36 = 0)
    (h13_10 : values 35 = 0) (h13_12 : values 37 = 0)
    (h25_12 : values 57 = 0) (h25_21 : values 59 = 0) (h25_22 : values 60 = 0)
    (h12_10 : values 27 = 0) (h12_12 : values 29 = 0)
    (h34_10 : values 63 = 0) (h34_12 : values 65 = 0)
    (h05_02 : values 18 = 0) (h05_22 : values 24 = 0)
    (h34_00 : values 61 = 0) (h34_20 : values 66 = 0) (h34_22 : values 68 = 0)
    (h12_02 : values 26 = 0) (h34_21 : values 67 = 0)
    (h25_20 : values 58 = 0) (h24_22 : values 52 = 0) (h12_22 : values 32 = 0) :
    ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) (terminalValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations
          (Fin.castAdd 6 index)).toPoly = 0 := by
  intro index
  have source : sourceValue values (directSourceIndex index) = 0 :=
    base (directSourceIndex index) (direct_source_not_determinant index)
  fin_cases index <;>
    simp [terminalValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations,
      sourceValue, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, directSourceIndex,
      h23, h12, h13, h13_10, h13_12, h25_12, h25_21, h25_22,
      h12_10, h12_12, h34_10, h34_12, h05_02, h05_22,
      h34_00, h34_20, h34_22, h12_02, h34_21, h25_20,
      h24_22, h12_22] at source ⊢ <;>
    ring_nf at source ⊢ <;>
    exact source

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem theta_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (hdet : slotDeterminant values 1 ≠ 0) :
    eval₂Hom (Int.castRingHom R) (terminalValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations 20).toPoly = 0 := by
  have hinv : slotDeterminant values 1 * (slotDeterminant values 1)⁻¹ = 1 :=
    mul_inv_cancel₀ hdet
  have hdet_eq : values 23 - values 15 = slotDeterminant values 1 := by
    simp [slotDeterminant, slotA1, slotB1, slotA2, slotB2]
  simp [terminalValues,
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly, hdet_eq, hinv]

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem factor_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0) :
    eval₂Hom (Int.castRingHom R) (terminalValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations 21).toPoly = 0 ∧
    eval₂Hom (Int.castRingHom R) (terminalValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations 22).toPoly = 0 ∧
    eval₂Hom (Int.castRingHom R) (terminalValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations 23).toPoly = 0 := by
  have s295 : sourceValue values 295 = 0 :=
    base 295 (fun slot => amplitude_source_not_determinant 0 slot)
  have s299 : sourceValue values 299 = 0 :=
    base 299 (fun slot => amplitude_source_not_determinant 1 slot)
  have s360 : sourceValue values 360 = 0 :=
    base 360 (fun slot => amplitude_source_not_determinant 2 slot)
  have original := affine_factor_identity values
  have reflected := reflected_factor_identity values
  rw [s295, s299, s360] at original reflected
  have hOriginal : slotDeterminant values 1 + factorL values * factorGb values = 0 := by
    simpa [factorL, factorGb] using original.symm
  have hReflected : -slotDeterminant values 1 + factorL values * factorGa values = 0 := by
    simpa using reflected.symm
  have hinv : slotDeterminant values 1 * (slotDeterminant values 1)⁻¹ = 1 :=
    mul_inv_cancel₀ hdet
  have hLInverse : factorL values * (-factorGb values * (slotDeterminant values 1)⁻¹) - 1 = 0 := by
    calc
      factorL values * (-factorGb values * (slotDeterminant values 1)⁻¹) - 1 =
          -(slotDeterminant values 1 + factorL values * factorGb values) *
              (slotDeterminant values 1)⁻¹ +
            (slotDeterminant values 1 * (slotDeterminant values 1)⁻¹ - 1) := by ring
      _ = 0 := by rw [hOriginal, hinv]; ring
  have hGbInverse : (-factorL values * (slotDeterminant values 1)⁻¹) * factorGb values - 1 = 0 := by
    calc
      (-factorL values * (slotDeterminant values 1)⁻¹) * factorGb values - 1 =
          -(slotDeterminant values 1 + factorL values * factorGb values) *
              (slotDeterminant values 1)⁻¹ +
            (slotDeterminant values 1 * (slotDeterminant values 1)⁻¹ - 1) := by ring
      _ = 0 := by rw [hOriginal, hinv]; ring
  constructor
  · have identity :
        eval₂Hom (Int.castRingHom R) (terminalValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations 21).toPoly =
            -slotDeterminant values 1 + factorL values * factorGa values := by
        simp [terminalValues,
          Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations,
          SparsePoly.toPoly, SparseTerm.toPoly,
          slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa]
        ring
    rw [identity, hReflected]
  constructor
  · have identity :
        eval₂Hom (Int.castRingHom R) (terminalValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations 22).toPoly =
            factorL values * (-factorGb values * (slotDeterminant values 1)⁻¹) - 1 := by
        simp [terminalValues,
          Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations,
          SparsePoly.toPoly, SparseTerm.toPoly, factorL, factorGb]
        ring
    rw [identity, hLInverse]
  · have identity :
        eval₂Hom (Int.castRingHom R) (terminalValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations 23).toPoly =
            (-factorL values * (slotDeterminant values 1)⁻¹) * factorGb values - 1 := by
        simp [terminalValues,
          Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations,
          SparsePoly.toPoly, SparseTerm.toPoly, factorL, factorGb]
        ring
    rw [identity, hGbInverse]

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem branch_inverse_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (h01 : values 1 ≠ 0) (h34 : values 64 ≠ 0) :
    eval₂Hom (Int.castRingHom R) (terminalValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations 24).toPoly = 0 ∧
    eval₂Hom (Int.castRingHom R) (terminalValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations 25).toPoly = 0 := by
  constructor <;>
    simp [terminalValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ h01, mul_inv_cancel₀ h34]

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000

/-- The named terminal branch is impossible over every characteristic-zero
field.  Its contradiction is the strict 26-generator certificate, with
each generator semantically transported from the canonical system or a
displayed inverse/factor relation. -/
theorem refutes_slot1_chart3_both_live_sum_nonzero_b1_terminal
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h01 : values 1 ≠ 0) (h34 : values 64 ≠ 0) (h05 : values 17 ≠ 0)
    (h05_02 : values 18 = 0) (h05_22 : values 24 = 0)
    (h34_00 : values 61 = 0) (h34_10 : values 63 = 0)
    (h34_12 : values 65 = 0) (h34_20 : values 66 = 0)
    (h34_22 : values 68 = 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    Krenn.FrozenCase0NoncollapseType01Chart3.w13_10_zero_of_both_opposite_pivots_live
      values base hdet ⟨h23, h12, h13⟩ h24 h25
  have h13_12 : values 37 = 0 :=
    w13_12_zero_of_bothlive_sum_nonzero values base ⟨h23, h12, h13⟩ h13_10 hsum
  obtain ⟨h12_10, h12_12, h34_21, h25_20, h12_02, h24_22, h12_22⟩ :=
    terminal_closure_zeros values base h13 h13_10 h13_12 h01 h05 h34
      h05_02 h05_22 h34_00 h34_10 h34_12 h34_20 h34_22
  obtain ⟨h25_12, h25_21, h25_22⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3.w25_tail_zero_of_both_opposite_pivots_live
      values base hdet ⟨h23, h12, h13⟩ h24 h25 h12_12 h01
  have direct := direct_selected_zero values base h23 h12 h13 h13_10 h13_12
    h25_12 h25_21 h25_22 h12_10 h12_12 h34_10 h34_12 h05_02 h05_22
    h34_00 h34_20 h34_22 h12_02 h34_21 h25_20 h24_22 h12_22
  have theta := theta_selected_zero values hdet
  obtain ⟨factor21, factor22, factor23⟩ := factor_selected_zero values base hdet
  obtain ⟨branch24, branch25⟩ := branch_inverse_selected_zero values h01 h34
  apply Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalCertificate.selectedHasNoCommonZero
    (terminalValues values)
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
  · exact direct 8
  · exact direct 9
  · exact direct 10
  · exact direct 11
  · exact direct 12
  · exact direct 13
  · exact direct 14
  · exact direct 15
  · exact direct 16
  · exact direct 17
  · exact direct 18
  · exact direct 19
  · exact theta
  · exact factor21
  · exact factor22
  · exact factor23
  · exact branch24
  · exact branch25

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge.refutes_slot1_chart3_both_live_sum_nonzero_b1_terminal

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge
