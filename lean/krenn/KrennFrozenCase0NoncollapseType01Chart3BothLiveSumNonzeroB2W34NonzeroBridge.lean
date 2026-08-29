import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge
import KrennFrozenCase0NoncollapseType01Chart3W12_12LiveW34Zero
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate

/-!
The semantic part of the chart-3, both-live, nonzero-sum B2 branch with
`w_34_11` live.

The external leaf first performs an eight-row monomial zero closure.  This
file reconstructs that closure directly from named rows of the frozen case-0
system.  The strict certificate is imported above, but is not used until its
selected equations have been separately transported.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroBridge

open MvPolynomial
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3
open Krenn.SparseCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The eight canonical rows used by the recorded monomial closure. -/
def closureSourceIndex : Fin 8 -> Fin 747 := ![46, 148, 154, 160, 161, 125, 128, 602]

theorem closure_source_not_determinant
    (index : Fin 8) (slot : Fin 18) :
    determinantSourceIndex slot ≠ closureSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, closureSourceIndex]

/--
The recorded B2 `w_34_11 ≠ 0` monomial closure is a consequence of the
canonical frozen equations.  It is intentionally stated without invoking the
certificate: the closure remains inspectable as eight elementary products.
-/
theorem closure_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h01 : values 1 = 0) (h12_12 : values 29 ≠ 0)
    (h34 : values 64 ≠ 0) :
    values 61 = 0 /\ values 17 = 0 /\ values 18 = 0 /\ values 20 = 0 /\
      values 21 = 0 /\ values 24 = 0 /\ values 22 = 0 /\ values 71 = 0 := by
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
  have s160 : sourceValue values (closureSourceIndex 3) = 0 :=
    base (closureSourceIndex 3) (closure_source_not_determinant 3)
  have s161 : sourceValue values (closureSourceIndex 4) = 0 :=
    base (closureSourceIndex 4) (closure_source_not_determinant 4)
  have s125 : sourceValue values (closureSourceIndex 5) = 0 :=
    base (closureSourceIndex 5) (closure_source_not_determinant 5)
  have s128 : sourceValue values (closureSourceIndex 6) = 0 :=
    base (closureSourceIndex 6) (closure_source_not_determinant 6)
  have s602 : sourceValue values (closureSourceIndex 7) = 0 :=
    base (closureSourceIndex 7) (closure_source_not_determinant 7)
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
        SparsePoly.toPoly, SparseTerm.toPoly, h01, h12_10, h13, h13_10, h13_12, h34_00]
    rw [identity] at s148
    exact (mul_eq_zero.mp ((mul_eq_zero.mp s148).resolve_right h34)).resolve_right h12_12
  have h05_02 : values 18 = 0 := by
    have identity : sourceValue values (closureSourceIndex 2) =
        values 18 * values 29 * values 64 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h01, h12_10, h13, h13_10, h13_12, h34_00]
    rw [identity] at s154
    exact (mul_eq_zero.mp ((mul_eq_zero.mp s154).resolve_right h34)).resolve_right h12_12
  have h05_11 : values 20 = 0 := by
    have identity : sourceValue values (closureSourceIndex 3) = values 20 * values 29 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h01, h12_10, h13, h13_10, h13_12, h34_00]
    rw [identity] at s160
    exact (mul_eq_zero.mp s160).resolve_right h12_12
  have h05_12 : values 21 = 0 := by
    have identity : sourceValue values (closureSourceIndex 4) = values 21 * values 29 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h01, h12_10, h13, h13_10, h13_12, h34_00]
    rw [identity] at s161
    exact (mul_eq_zero.mp s161).resolve_right h12_12
  have h05_22 : values 24 = 0 := by
    have identity : sourceValue values (closureSourceIndex 5) = values 24 * values 29 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h01, h12_10, h13, h13_10, h13_12, h34_00]
    rw [identity] at s125
    exact (mul_eq_zero.mp s125).resolve_right h12_12
  have h05_20 : values 22 = 0 := by
    have identity : sourceValue values (closureSourceIndex 6) =
        values 22 * values 29 * values 64 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h01, h12_10, h13, h13_10, h13_12, h34_00]
    rw [identity] at s128
    exact (mul_eq_zero.mp ((mul_eq_zero.mp s128).resolve_right h34)).resolve_right h12_12
  have h35_22 : values 71 = 0 := by
    have identity : sourceValue values (closureSourceIndex 7) = values 29 * values 71 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h01, h12_10, h13, h13_10, h13_12, h34_00,
        h05_00, h05_02, h05_11, h05_12, h05_20, h05_22]
    rw [identity] at s602
    exact (mul_eq_zero.mp s602).resolve_left h12_12
  exact ⟨h34_00, h05_00, h05_02, h05_11, h05_12, h05_22, h05_20, h35_22⟩

/-- Values of the strict B2 leaf, expressed directly in the canonical
case-0 coordinates.  The seven auxiliary entries are displayed inverses;
the remaining entries are a source-level coordinate projection. -/
noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 -> R) : Fin 68 -> R :=
  ![
    (values 51)⁻¹, (values 56)⁻¹, values 23 - values 15,
    (factorGb values)⁻¹, (factorL values)⁻¹,
    (values 51 + values 56)⁻¹, (slotDeterminant values 1)⁻¹,
    values 0, values 2, values 3, values 4, values 5,
    values 6, values 7, values 8, values 9, values 10, values 11,
    values 12, values 13, values 14, values 15, values 16,
    values 19, values 25, values 26, values 29, values 30, values 31,
    values 32, values 33, values 34, values 38, values 39, values 40,
    values 41, values 42, values 43, values 44, values 45, values 46,
    values 47, values 49, values 50, values 51, values 52, values 53,
    values 54, values 55, values 56, values 57, values 58, values 59,
    values 60, values 62, values 63, values 64, values 65, values 66,
    values 67, values 68, values 69, values 70, values 72, values 73,
    values 74, (values 29)⁻¹, (values 64)⁻¹]

/-- The first twelve selected leaf generators are direct reductions of these
canonical source rows. -/
def directSourceIndex : Fin 12 -> Fin 747 :=
  ![607, 606, 720, 503, 181, 32, 710, 605, 295, 360, 336, 746]

theorem direct_source_not_determinant
    (index : Fin 12) (slot : Fin 18) :
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
    (h12_10 : values 27 = 0) (h01 : values 1 = 0)
    (h34_00 : values 61 = 0) (h05_00 : values 17 = 0)
    (h05_02 : values 18 = 0) (h05_11 : values 20 = 0)
    (h05_12 : values 21 = 0) (h05_22 : values 24 = 0)
    (h05_20 : values 22 = 0) (h35_22 : values 71 = 0) :
    ∀ index : Fin 12,
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations
          (Fin.castAdd 6 index)).toPoly = 0 := by
  intro index
  have source : sourceValue values (directSourceIndex index) = 0 :=
    base (directSourceIndex index) (direct_source_not_determinant index)
  fin_cases index <;>
    simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations,
      sourceValue, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, directSourceIndex,
      h23, h12, h13, h13_10, h13_12, h12_10, h01,
      h34_00, h05_00, h05_02, h05_11, h05_12, h05_22, h05_20, h35_22] at source ⊢ <;>
    ring_nf at source ⊢ <;>
    exact source

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem theta_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (hdet : slotDeterminant values 1 ≠ 0) :
    eval₂Hom (Int.castRingHom R) (leafValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations 12).toPoly = 0 := by
  have hinv : slotDeterminant values 1 * (slotDeterminant values 1)⁻¹ = 1 :=
    mul_inv_cancel₀ hdet
  have hdet_eq : values 23 - values 15 = slotDeterminant values 1 := by
    simp [slotDeterminant, slotA1, slotB1, slotA2, slotB2]
  simp [leafValues,
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly, hdet_eq, hinv]

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem reflected_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0) :
    eval₂Hom (Int.castRingHom R) (leafValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations 13).toPoly = 0 := by
  have s295 : sourceValue values 295 = 0 :=
    base 295 (fun slot => amplitude_source_not_determinant 0 slot)
  have s299 : sourceValue values 299 = 0 :=
    base 299 (fun slot => amplitude_source_not_determinant 1 slot)
  have s360 : sourceValue values 360 = 0 :=
    base 360 (fun slot => amplitude_source_not_determinant 2 slot)
  have reflected := reflected_factor_identity values
  rw [s295, s299, s360] at reflected
  have hReflected : -slotDeterminant values 1 + factorL values * factorGa values = 0 := by
    simpa using reflected.symm
  have hdet_eq : values 23 - values 15 = slotDeterminant values 1 := by
    simp [slotDeterminant, slotA1, slotB1, slotA2, slotB2]
  have identity :
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations 13).toPoly =
          -slotDeterminant values 1 + factorL values * factorGa values := by
    simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa]
    ring
  rw [identity, hReflected]

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem inverse_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0) (h12_12 : values 29 ≠ 0) :
    eval₂Hom (Int.castRingHom R) (leafValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations 14).toPoly = 0 ∧
    eval₂Hom (Int.castRingHom R) (leafValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations 15).toPoly = 0 ∧
    eval₂Hom (Int.castRingHom R) (leafValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations 16).toPoly = 0 ∧
    eval₂Hom (Int.castRingHom R) (leafValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations 17).toPoly = 0 := by
  have h24inv : (values 51)⁻¹ * values 51 = 1 := inv_mul_cancel₀ h24
  have h25inv : (values 56)⁻¹ * values 56 = 1 := inv_mul_cancel₀ h25
  have hsuminv : (values 51 + values 56)⁻¹ * (values 51 + values 56) = 1 :=
    inv_mul_cancel₀ hsum
  have h12inv : values 29 * (values 29)⁻¹ = 1 := mul_inv_cancel₀ h12_12
  constructor
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, h24inv]
  constructor
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, h25inv]
  constructor
  · have identity :
        eval₂Hom (Int.castRingHom R) (leafValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations 16).toPoly =
            (values 51 + values 56)⁻¹ * (values 51 + values 56) - 1 := by
        simp [leafValues,
          Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations,
          SparsePoly.toPoly, SparseTerm.toPoly]
        ring
    rw [identity, hsuminv]
    ring
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, h12inv]

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000

/-- The chart-3, both-opposite-pivots-live, nonzero-sum B2 leaf with
`w_01_11 = 0`, `w_12_12 ≠ 0`, and `w_34_11 ≠ 0` is impossible.  The final
contradiction is the strict 18-generator identity, after each of its
generators has been transported from frozen canonical source rows or an
explicit inverse/factor relation. -/
theorem refutes_chart3_both_live_sum_nonzero_b2_w34_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h01 : values 1 = 0) (h12_12 : values 29 ≠ 0)
    (h34 : values 64 ≠ 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet ⟨h23, h12, h13⟩ h24 h25
  have h13_12 : values 37 = 0 :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalBridge.w13_12_zero_of_bothlive_sum_nonzero
      values base ⟨h23, h12, h13⟩ h13_10 hsum
  obtain ⟨h34_00, h05_00, h05_02, h05_11, h05_12, h05_22, h05_20, h35_22⟩ :=
    closure_zeros values base hdet ⟨h23, h12, h13⟩ h24 h25 hsum h01 h12_12 h34
  have h12_10 : values 27 = 0 :=
    (Krenn.FrozenCase0NoncollapseType01Chart3BothLive.chart3_surviving_coordinates
      values base hdet ⟨h23, h12, h13⟩).2.2
  have direct := direct_selected_zero values base h23 h12 h13 h13_10 h13_12 h12_10 h01
    h34_00 h05_00 h05_02 h05_11 h05_12 h05_22 h05_20 h35_22
  have theta := theta_selected_zero values hdet
  have reflected := reflected_selected_zero values base hdet
  obtain ⟨inv14, inv15, inv16, inv17⟩ :=
    inverse_selected_zero values h24 h25 hsum h12_12
  apply Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroCertificate.selectedHasNoCommonZero
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
  · exact direct 8
  · exact direct 9
  · exact direct 10
  · exact direct 11
  · exact theta
  · exact reflected
  · exact inv14
  · exact inv15
  · exact inv16
  · exact inv17

/-- The `w_34_11` split is exhaustive: the zero side is a direct factor
geometry contradiction, while the live side is the semantically transported
strict certificate above. -/
theorem refutes_chart3_both_live_sum_nonzero_b2_w12_12_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h01 : values 1 = 0) (h12_12 : values 29 ≠ 0) : False := by
  by_cases h34 : values 64 = 0
  · exact Krenn.FrozenCase0NoncollapseType01Chart3W12_12LiveW34Zero.refutes_chart3_w12_12_live_w34_zero
      values base hdet chart h12_12 h34
  · exact refutes_chart3_both_live_sum_nonzero_b2_w34_nonzero
      values base hdet chart h24 h25 hsum h01 h12_12 h34

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroBridge.closure_zeros

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroBridge.refutes_chart3_both_live_sum_nonzero_b2_w34_nonzero

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroBridge.refutes_chart3_both_live_sum_nonzero_b2_w12_12_live

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB2W34NonzeroBridge
