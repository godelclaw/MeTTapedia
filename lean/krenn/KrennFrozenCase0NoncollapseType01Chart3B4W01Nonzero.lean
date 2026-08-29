import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3B4W01NonzeroCertificate

/-!
Semantic reflection of the `b4 / w01 != 0` strict leaf of the Chart-3,
both-pivots-live, zero-sum tree.  The six monomial consequences used by the
frozen closure are rederived from canonical rows here; the selected
certificate rows then come directly from canonical rows, except for the
displayed `w_01_11` inverse branch equation.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B4W01Nonzero

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

def closureSourceIndex : Fin 6 -> Fin 747 := ![147, 53, 72, 28, 121, 553]

def directSourceIndex : Fin 22 -> Fin 747 := ![
  156, 607, 371, 159, 5, 556, 645, 328, 163, 644, 745,
  727, 22, 122, 31, 135, 354, 349, 488, 703, 343, 746]

theorem closure_source_not_determinant
    (index : Fin 6) (slot : Fin 18) :
    determinantSourceIndex slot ≠ closureSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, closureSourceIndex]

theorem direct_source_not_determinant
    (index : Fin 22) (slot : Fin 18) :
    determinantSourceIndex slot ≠ directSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, directSourceIndex]

noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 -> R) : Fin 68 -> R := ![
  (values 51)⁻¹, slotDeterminant values 1, (factorGb values)⁻¹,
  (factorL values)⁻¹, (slotDeterminant values 1)⁻¹,
  values 0, values 1, values 2, values 3, values 4, values 5,
  values 6, values 7, values 8, values 11, values 12, values 13,
  values 15, values 17, values 18, values 19, values 20, values 21,
  values 22, values 24, values 25, values 26, values 30, values 31,
  values 32, values 33, values 34, values 37, values 38, values 39,
  values 40, values 41, values 42, values 43, values 44, values 45,
  values 46, values 47, values 49, values 50, values 51, values 54,
  values 55, values 57, values 58, values 59, values 60, values 61,
  values 62, values 63, values 64, values 65, values 66, values 67,
  values 68, values 69, values 70, values 71, values 72, values 73,
  values 74, (values 37)⁻¹, (values 1)⁻¹]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
/-- The six zero coordinates forced before the final `w_01_11` split. -/
theorem closure_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 ≠ 0) (h12_12 : values 29 = 0)
    (h12_10 : values 27 = 0) :
    values 53 = 0 /\ values 9 = 0 /\ values 10 = 0 /\ values 16 = 0 /\
      values 14 = 0 /\ values 52 = 0 := by
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
        h23, h12, h13, h13_10, h12_12, h12_10]
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_left h13_12
  have source1 : sourceValue values (closureSourceIndex 1) = 0 :=
    base (closureSourceIndex 1) (closure_source_not_determinant 1)
  have h04_00 : values 9 = 0 := by
    have identity : sourceValue values (closureSourceIndex 1) =
        values 9 * values 37 * values 56 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_12, h12_10, h25eq]
    rw [identity] at source1
    have productZero : values 9 * values 37 = 0 :=
      (mul_eq_zero.mp source1).resolve_right h25
    exact (mul_eq_zero.mp productZero).resolve_right h13_12
  have source2 : sourceValue values (closureSourceIndex 2) = 0 :=
    base (closureSourceIndex 2) (closure_source_not_determinant 2)
  have h04_02 : values 10 = 0 := by
    have identity : sourceValue values (closureSourceIndex 2) =
        values 10 * values 37 * values 56 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_12, h12_10, h25eq]
    rw [identity] at source2
    have productZero : values 10 * values 37 = 0 :=
      (mul_eq_zero.mp source2).resolve_right h25
    exact (mul_eq_zero.mp productZero).resolve_right h13_12
  have source3 : sourceValue values (closureSourceIndex 3) = 0 :=
    base (closureSourceIndex 3) (closure_source_not_determinant 3)
  have h04_22 : values 16 = 0 := by
    have identity : sourceValue values (closureSourceIndex 3) =
        values 16 * values 37 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12_10]
    rw [identity] at source3
    exact (mul_eq_zero.mp source3).resolve_right h13_12
  have source4 : sourceValue values (closureSourceIndex 4) = 0 :=
    base (closureSourceIndex 4) (closure_source_not_determinant 4)
  have h04_20 : values 14 = 0 := by
    have identity : sourceValue values (closureSourceIndex 4) =
        values 14 * values 37 * values 56 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_10, h25eq]
    rw [identity] at source4
    have productZero : values 14 * values 37 = 0 :=
      (mul_eq_zero.mp source4).resolve_right h25
    exact (mul_eq_zero.mp productZero).resolve_right h13_12
  have source5 : sourceValue values (closureSourceIndex 5) = 0 :=
    base (closureSourceIndex 5) (closure_source_not_determinant 5)
  have h24_22 : values 52 = 0 := by
    have identity : sourceValue values (closureSourceIndex 5) =
        values 37 * values 52 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h04_02, h12_12]
    rw [identity] at source5
    exact (mul_eq_zero.mp source5).resolve_left h13_12
  exact ⟨h25_00, h04_00, h04_02, h04_22, h04_20, h24_22⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
/-- The first twenty-two certificate rows are direct canonical rows after the
recorded chart and monomial-zero reductions. -/
theorem direct_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h13_10 : values 35 = 0) (h13_12 : values 37 ≠ 0)
    (h12_12 : values 29 = 0) (h12_10 : values 27 = 0)
    (h25eq : values 56 = -values 51)
    (h25_00 : values 53 = 0) (h04_00 : values 9 = 0)
    (h04_02 : values 10 = 0) (h04_22 : values 16 = 0)
    (h04_20 : values 14 = 0) (h24_22 : values 52 = 0) :
    forall index : Fin 22,
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B4W01NonzeroCertificate.selectedEquations
          (Fin.castAdd 1 index)).toPoly = 0 := by
  intro index
  rcases chart with ⟨h23, h12, h13⟩
  have source : sourceValue values (directSourceIndex index) = 0 :=
    base (directSourceIndex index) (direct_source_not_determinant index)
  fin_cases index <;>
    simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B4W01NonzeroCertificate.selectedEquations,
      sourceValue, directSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb,
      h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h25eq,
      h25_00, h04_00, h04_02, h04_22, h04_20, h24_22] at source ⊢ <;>
    ring_nf at source ⊢ <;>
    first | exact source | exact mul_eq_zero.mpr source

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem branch_inverse_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (h01 : values 1 ≠ 0) :
    eval₂Hom (Int.castRingHom R) (leafValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3B4W01NonzeroCertificate.selectedEquations 22).toPoly = 0 := by
  simp [leafValues,
    Krenn.FrozenCase0NoncollapseType01Chart3B4W01NonzeroCertificate.selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ h01]

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000

/-- The named `b4 / w01 != 0` chart is impossible over every
characteristic-zero field.  Lean checks the exact integer certificate and
every route from its selected rows back to canonical case-0 rows. -/
theorem refutes_chart3_b4_w01_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 ≠ 0) (h12_12 : values 29 = 0)
    (h12_10 : values 27 = 0) (h01 : values 1 ≠ 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart' h24 h25
  have h25eq : values 56 = -values 51 := by
    calc
      values 56 = (values 51 + values 56) - values 51 := by ring
      _ = -values 51 := by rw [hsum]; ring
  obtain ⟨h25_00, h04_00, h04_02, h04_22, h04_20, h24_22⟩ :=
    closure_zeros values base hdet chart' h24 h25 hsum h13_12 h12_12 h12_10
  have direct :=
    direct_selected_zero values base chart' h13_10 h13_12 h12_12 h12_10 h25eq
      h25_00 h04_00 h04_02 h04_22 h04_20 h24_22
  have branch := branch_inverse_selected_zero values h01
  apply Krenn.FrozenCase0NoncollapseType01Chart3B4W01NonzeroCertificate.selectedHasNoCommonZero
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
  · exact direct 12
  · exact direct 13
  · exact direct 14
  · exact direct 15
  · exact direct 16
  · exact direct 17
  · exact direct 18
  · exact direct 19
  · exact direct 20
  · exact direct 21
  · exact branch

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B4W01Nonzero.closure_zeros
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B4W01Nonzero.refutes_chart3_b4_w01_nonzero

end Krenn.FrozenCase0NoncollapseType01Chart3B4W01Nonzero
