import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3B6Certificate

/-!
Semantic reflection of the strict `b6` monomial-closure leaf in the
Chart-3, both-pivots-live, zero-sum tree.

The external closure records twelve forced zero coordinates.  Each is
rederived below from a canonical source row and its live support; the final
sixteen-row exact certificate is then replayed over those canonical values.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B6

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

def closureSourceIndex : Fin 12 -> Fin 747 := ![
  147, 53, 72, 46, 28, 121, 125, 243, 549, 250, 466, 412]

def directSourceIndex : Fin 12 -> Fin 747 := ![
  744, 655, 501, 356, 22, 713, 352, 535, 701, 494, 532, 488]

theorem closure_source_not_determinant
    (index : Fin 12) (slot : Fin 18) :
    determinantSourceIndex slot ≠ closureSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, closureSourceIndex]

theorem direct_source_not_determinant
    (index : Fin 12) (slot : Fin 18) :
    determinantSourceIndex slot ≠ directSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, directSourceIndex]

noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 -> R) : Fin 63 -> R := ![
  (values 51)⁻¹,
  slotDeterminant values 1,
  (factorGb values)⁻¹,
  (factorL values)⁻¹,
  (slotDeterminant values 1)⁻¹,
  values 0, values 1, values 2, values 3, values 4, values 5,
  values 6, values 7, values 8, values 12, values 13, values 15,
  values 17, values 18, values 19, values 20, values 21, values 22,
  values 25, values 26, values 29, values 30, values 31, values 32,
  values 33, values 34, values 37, values 38, values 39, values 40,
  values 41, values 42, values 43, values 44, values 45, values 46,
  values 47, values 49, values 51, values 52, values 54, values 55,
  values 57, values 58, values 59, values 60, values 62, values 64,
  values 67, values 68, values 69, values 70, values 71, values 72,
  values 73, values 74, (values 37)⁻¹, (values 29)⁻¹]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
/-- The exact twelve-step monomial-zero closure is forced by canonical rows. -/
theorem closure_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 ≠ 0) (h12_12 : values 29 ≠ 0)
    (h12_10 : values 27 = 0) :
    values 53 = 0 /\ values 9 = 0 /\ values 10 = 0 /\ values 61 = 0 /\
      values 16 = 0 /\ values 14 = 0 /\ values 24 = 0 /\ values 63 = 0 /\
        values 65 = 0 /\ values 66 = 0 /\ values 50 = 0 /\ values 11 = 0 := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart' h24 h25
  have h25eq : values 56 = -values 51 := by
    calc
      values 56 = (values 51 + values 56) - values 51 := by ring
      _ = -values 51 := by rw [hsum]; ring
  have source0 : sourceValue values (closureSourceIndex 0) = 0 :=
    base (closureSourceIndex 0) (closure_source_not_determinant 0)
  have h25_00 : values 53 = 0 := by
    have identity : sourceValue values (closureSourceIndex 0) =
        values 37 * values 53 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq]
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_left h13_12
  have source1 : sourceValue values (closureSourceIndex 1) = 0 :=
    base (closureSourceIndex 1) (closure_source_not_determinant 1)
  have h04_00 : values 9 = 0 := by
    have identity : sourceValue values (closureSourceIndex 1) =
        -(values 9 * values 37 * values 51) := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq, h25_00]
    rw [identity] at source1
    have product : values 9 * values 37 * values 51 = 0 := neg_eq_zero.mp source1
    have left : values 9 * values 37 = 0 :=
      (mul_eq_zero.mp product).resolve_right h24
    exact (mul_eq_zero.mp left).resolve_right h13_12
  have source2 : sourceValue values (closureSourceIndex 2) = 0 :=
    base (closureSourceIndex 2) (closure_source_not_determinant 2)
  have h04_02 : values 10 = 0 := by
    have identity : sourceValue values (closureSourceIndex 2) =
        -(values 10 * values 37 * values 51) := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq, h25_00, h04_00]
    rw [identity] at source2
    have product : values 10 * values 37 * values 51 = 0 := neg_eq_zero.mp source2
    have left : values 10 * values 37 = 0 :=
      (mul_eq_zero.mp product).resolve_right h24
    exact (mul_eq_zero.mp left).resolve_right h13_12
  have source3 : sourceValue values (closureSourceIndex 3) = 0 :=
    base (closureSourceIndex 3) (closure_source_not_determinant 3)
  have h34_00 : values 61 = 0 := by
    have identity : sourceValue values (closureSourceIndex 3) =
        values 29 * values 61 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq, h25_00, h04_00, h04_02]
    rw [identity] at source3
    exact (mul_eq_zero.mp source3).resolve_left h12_12
  have source4 : sourceValue values (closureSourceIndex 4) = 0 :=
    base (closureSourceIndex 4) (closure_source_not_determinant 4)
  have h04_22 : values 16 = 0 := by
    have identity : sourceValue values (closureSourceIndex 4) =
        values 16 * values 37 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq,
        h25_00, h04_00, h04_02, h34_00]
    rw [identity] at source4
    exact (mul_eq_zero.mp source4).resolve_right h13_12
  have source5 : sourceValue values (closureSourceIndex 5) = 0 :=
    base (closureSourceIndex 5) (closure_source_not_determinant 5)
  have h04_20 : values 14 = 0 := by
    have identity : sourceValue values (closureSourceIndex 5) =
        -(values 14 * values 37 * values 51) := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq,
        h25_00, h04_00, h04_02, h34_00, h04_22]
    rw [identity] at source5
    have product : values 14 * values 37 * values 51 = 0 := neg_eq_zero.mp source5
    have left : values 14 * values 37 = 0 :=
      (mul_eq_zero.mp product).resolve_right h24
    exact (mul_eq_zero.mp left).resolve_right h13_12
  have source6 : sourceValue values (closureSourceIndex 6) = 0 :=
    base (closureSourceIndex 6) (closure_source_not_determinant 6)
  have h05_22 : values 24 = 0 := by
    have identity : sourceValue values (closureSourceIndex 6) =
        values 24 * values 29 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq,
        h25_00, h04_00, h04_02, h34_00, h04_22, h04_20]
    rw [identity] at source6
    exact (mul_eq_zero.mp source6).resolve_right h12_12
  have source7 : sourceValue values (closureSourceIndex 7) = 0 :=
    base (closureSourceIndex 7) (closure_source_not_determinant 7)
  have h34_10 : values 63 = 0 := by
    have identity : sourceValue values (closureSourceIndex 7) =
        values 29 * values 63 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq,
        h25_00, h04_00, h04_02, h34_00, h04_22, h04_20, h05_22]
    rw [identity] at source7
    exact (mul_eq_zero.mp source7).resolve_left h12_12
  have source8 : sourceValue values (closureSourceIndex 8) = 0 :=
    base (closureSourceIndex 8) (closure_source_not_determinant 8)
  have h34_12 : values 65 = 0 := by
    have identity : sourceValue values (closureSourceIndex 8) =
        values 29 * values 65 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq,
        h25_00, h04_00, h04_02, h34_00, h04_22, h04_20, h05_22, h34_10]
    rw [identity] at source8
    exact (mul_eq_zero.mp source8).resolve_left h12_12
  have source9 : sourceValue values (closureSourceIndex 9) = 0 :=
    base (closureSourceIndex 9) (closure_source_not_determinant 9)
  have h34_20 : values 66 = 0 := by
    have identity : sourceValue values (closureSourceIndex 9) =
        values 29 * values 66 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq,
        h25_00, h04_00, h04_02, h34_00, h04_22, h04_20, h05_22,
        h34_10, h34_12]
    rw [identity] at source9
    exact (mul_eq_zero.mp source9).resolve_left h12_12
  have source10 : sourceValue values (closureSourceIndex 10) = 0 :=
    base (closureSourceIndex 10) (closure_source_not_determinant 10)
  have h24_00 : values 50 = 0 := by
    have identity : sourceValue values (closureSourceIndex 10) =
        values 37 * values 50 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq,
        h25_00, h04_00, h04_02, h34_00, h04_22, h04_20, h05_22,
        h34_10, h34_12, h34_20]
    rw [identity] at source10
    exact (mul_eq_zero.mp source10).resolve_left h13_12
  have source11 : sourceValue values (closureSourceIndex 11) = 0 :=
    base (closureSourceIndex 11) (closure_source_not_determinant 11)
  have h04_10 : values 11 = 0 := by
    have identity : sourceValue values (closureSourceIndex 11) =
        -(values 11 * values 37 * values 51) := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq,
        h25_00, h04_00, h04_02, h34_00, h04_22, h04_20, h05_22,
        h34_10, h34_12, h34_20, h24_00]
    rw [identity] at source11
    have product : values 11 * values 37 * values 51 = 0 := neg_eq_zero.mp source11
    have left : values 11 * values 37 = 0 :=
      (mul_eq_zero.mp product).resolve_right h24
    exact (mul_eq_zero.mp left).resolve_right h13_12
  exact ⟨h25_00, h04_00, h04_02, h34_00, h04_22, h04_20, h05_22,
    h34_10, h34_12, h34_20, h24_00, h04_10⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem direct_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h13_10 : values 35 = 0) (h12_10 : values 27 = 0)
    (h25eq : values 56 = -values 51)
    (h25_00 : values 53 = 0) (h04_00 : values 9 = 0)
    (h04_02 : values 10 = 0) (h34_00 : values 61 = 0)
    (_h04_22 : values 16 = 0) (h04_20 : values 14 = 0)
    (_h05_22 : values 24 = 0) (h34_10 : values 63 = 0)
    (h34_12 : values 65 = 0) (h34_20 : values 66 = 0)
    (h24_00 : values 50 = 0) (h04_10 : values 11 = 0) :
    forall index : Fin 12,
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate.selectedEquations
          (Fin.castAdd 4 index)).toPoly = 0 := by
  intro index
  rcases chart with ⟨h23, h12, h13⟩
  have source : sourceValue values (directSourceIndex index) = 0 :=
    base (directSourceIndex index) (direct_source_not_determinant index)
  fin_cases index <;>
    simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate.selectedEquations,
      sourceValue, directSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb,
      h23, h12, h13, h13_10, h12_10, h25eq,
      h25_00, h04_00, h04_02, h34_00, h04_20,
      h34_10, h34_12, h34_20, h24_00, h04_10] at source ⊢ <;>
    ring_nf at source ⊢ <;>
    try exact source
  rcases source with (h | h)
  · rcases h with (h | h)
    · simp [h]
    · simp [h]
  · simp [h]

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem inverse_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (hdet : slotDeterminant values 1 ≠ 0)
    (hL : factorL values ≠ 0) (h13_12 : values 37 ≠ 0)
    (h12_12 : values 29 ≠ 0) :
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate.selectedEquations 12).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate.selectedEquations 13).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate.selectedEquations 14).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate.selectedEquations 15).toPoly = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ hdet]
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly]
    field_simp [factorL, hL]
    simp [factorL]
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ h13_12]
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ h12_12]

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000

/-- The named `b6` monomial-closure chart is impossible over every
characteristic-zero field. -/
theorem refutes_chart3_b6
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 ≠ 0) (h12_12 : values 29 ≠ 0)
    (h12_10 : values 27 = 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart' h24 h25
  have h25eq : values 56 = -values 51 := by
    calc
      values 56 = (values 51 + values 56) - values 51 := by ring
      _ = -values 51 := by rw [hsum]; ring
  obtain ⟨h25_00, h04_00, h04_02, h34_00, h04_22, h04_20, h05_22,
      h34_10, h34_12, h34_20, h24_00, h04_10⟩ :=
    closure_zeros values base hdet chart' h24 h25 hsum h13_12 h12_12 h12_10
  have direct := direct_selected_zero values base chart' h13_10 h12_10 h25eq
    h25_00 h04_00 h04_02 h34_00 h04_22 h04_20 h05_22 h34_10 h34_12 h34_20
    h24_00 h04_10
  obtain ⟨hL, _hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
  obtain ⟨inverse0, inverse1, inverse2, inverse3⟩ :=
    inverse_selected_zero values hdet hL h13_12 h12_12
  apply Krenn.FrozenCase0NoncollapseType01Chart3B6Certificate.selectedHasNoCommonZero
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
  · exact inverse0
  · exact inverse1
  · exact inverse2
  · exact inverse3

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B6.closure_zeros
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B6.refutes_chart3_b6

end Krenn.FrozenCase0NoncollapseType01Chart3B6
