import KrennFrozenCase0NoncollapseType01Chart3B4W01Nonzero
import KrennFrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate

/-!
Semantic reflection of the strict `b4 / w01 = 0` leaf in the Chart-3,
both-pivots-live, zero-sum tree.

The first six monomial consequences are shared with the adjacent
`b4 / w01 != 0` branch.  The `w01 = 0` branch then forces three further
zeros from canonical rows.  Every selected row of the final exact
certificate is rederived from that canonical state or from an explicit
inverse/structural identity.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B4W01Zero

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

def closureSourceIndex : Fin 3 -> Fin 747 := ![162, 163, 409]

def directSourceIndex : Fin 30 -> Fin 747 := ![
  744, 643, 658, 376, 724, 606, 738, 687, 709, 314,
  610, 741, 697, 699, 646, 660, 728, 645, 729, 644,
  745, 408, 412, 22, 291, 111, 586, 358, 594, 360]

theorem closure_source_not_determinant
    (index : Fin 3) (slot : Fin 18) :
    determinantSourceIndex slot ≠ closureSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, closureSourceIndex]

theorem direct_source_not_determinant
    (index : Fin 30) (slot : Fin 18) :
    determinantSourceIndex slot ≠ directSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, directSourceIndex]

noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 -> R) : Fin 63 -> R := ![
  (values 51)⁻¹, slotDeterminant values 1, (factorGb values)⁻¹,
  (factorL values)⁻¹, (slotDeterminant values 1)⁻¹,
  values 0, values 2, values 3, values 4, values 5, values 6,
  values 7, values 8, values 11, values 15, values 17, values 18,
  values 20, values 21, values 22, values 24, values 25, values 26,
  values 30, values 31, values 32, values 33, values 34, values 37,
  values 38, values 39, values 40, values 41, values 42, values 43,
  values 44, values 45, values 46, values 47, values 49, values 50,
  values 51, values 54, values 55, values 57, values 58, values 59,
  values 60, values 61, values 62, values 63, values 64, values 65,
  values 66, values 67, values 68, values 69, values 70, values 71,
  values 72, values 73, values 74, (values 37)⁻¹]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
/-- The final three zero coordinates of the `b4 / w01 = 0` closure. -/
theorem closure_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 ≠ 0) (h12_12 : values 29 = 0)
    (h12_10 : values 27 = 0) (h01 : values 1 = 0) :
    values 53 = 0 /\ values 9 = 0 /\ values 10 = 0 /\ values 16 = 0 /\
      values 14 = 0 /\ values 52 = 0 /\ values 12 = 0 /\
        values 13 = 0 /\ values 19 = 0 := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart' h24 h25
  have h25eq : values 56 = -values 51 := by
    calc
      values 56 = (values 51 + values 56) - values 51 := by ring
      _ = -values 51 := by rw [hsum]; ring
  obtain ⟨h25_00, h04_00, h04_02, h04_22, h04_20, h24_22⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3B4W01Nonzero.closure_zeros
      values base hdet chart' h24 h25 hsum h13_12 h12_12 h12_10
  have source0 : sourceValue values (closureSourceIndex 0) = 0 :=
    base (closureSourceIndex 0) (closure_source_not_determinant 0)
  have h04_11 : values 12 = 0 := by
    have identity : sourceValue values (closureSourceIndex 0) =
        values 12 * values 37 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_12, h12_10, h01, h25eq,
        h25_00, h04_00, h04_02, h04_22, h04_20, h24_22]
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_right h13_12
  have source1 : sourceValue values (closureSourceIndex 1) = 0 :=
    base (closureSourceIndex 1) (closure_source_not_determinant 1)
  have h04_12 : values 13 = 0 := by
    have identity : sourceValue values (closureSourceIndex 1) =
        values 13 * values 37 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_12, h12_10, h01, h25eq,
        h25_00, h04_00, h04_02, h04_22, h04_20, h24_22, h04_11]
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_right h13_12
  have source2 : sourceValue values (closureSourceIndex 2) = 0 :=
    base (closureSourceIndex 2) (closure_source_not_determinant 2)
  have h05_10 : values 19 = 0 := by
    have identity : sourceValue values (closureSourceIndex 2) =
        values 19 * values 37 * values 51 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h12_12, h12_10, h01, h25eq,
        h25_00, h04_00, h04_02, h04_22, h04_20, h24_22, h04_11, h04_12]
    rw [identity] at source2
    have product : values 19 * values 37 = 0 :=
      (mul_eq_zero.mp source2).resolve_right h24
    exact (mul_eq_zero.mp product).resolve_right h13_12
  exact ⟨h25_00, h04_00, h04_02, h04_22, h04_20, h24_22,
    h04_11, h04_12, h05_10⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem direct_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h13_10 : values 35 = 0) (h12_12 : values 29 = 0)
    (h12_10 : values 27 = 0) (h01 : values 1 = 0)
    (h25eq : values 56 = -values 51)
    (h25_00 : values 53 = 0) (h04_00 : values 9 = 0)
    (h04_02 : values 10 = 0) (h04_22 : values 16 = 0)
    (h04_20 : values 14 = 0) (h24_22 : values 52 = 0)
    (h04_11 : values 12 = 0) (h04_12 : values 13 = 0)
    (h05_10 : values 19 = 0) :
    forall index : Fin 30,
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedEquations
          (Fin.castAdd 4 index)).toPoly = 0 := by
  intro index
  rcases chart with ⟨h23, h12, h13⟩
  have source : sourceValue values (directSourceIndex index) = 0 :=
    base (directSourceIndex index) (direct_source_not_determinant index)
  fin_cases index <;>
    simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedEquations,
      sourceValue, directSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa,
      factorGb, h23, h12, h13, h13_10, h12_12, h12_10, h01, h25eq,
      h25_00, h04_00, h04_02, h04_22, h04_20, h24_22,
      h04_11, h04_12, h05_10] at source ⊢ <;>
    ring_nf at source ⊢ <;>
    try exact source
  all_goals rcases source with h | h <;> simp [h]

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem special_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (h24 : values 51 ≠ 0) (h13_12 : values 37 ≠ 0) :
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedEquations 30).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedEquations 31).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedEquations 32).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedEquations 33).toPoly = 0 := by
  have source295 : sourceValue values 295 = 0 :=
    base 295 (fun slot => amplitude_source_not_determinant 0 slot)
  have source299 : sourceValue values 299 = 0 :=
    base 299 (fun slot => amplitude_source_not_determinant 1 slot)
  have source360 : sourceValue values 360 = 0 :=
    base 360 (fun slot => amplitude_source_not_determinant 2 slot)
  have reflected := reflected_factor_identity values
  rw [source295, source299, source360] at reflected
  have hReflected : -slotDeterminant values 1 +
      factorL values * factorGa values = 0 := by
    simpa using reflected.symm
  have hDelta : values 23 - values 15 = slotDeterminant values 1 := by
    simp [slotDeterminant, slotA1, slotB1, slotA2, slotB2]
  have h23 : values 23 = slotDeterminant values 1 + values 15 := by
    calc
      values 23 = (values 23 - values 15) + values 15 := by ring
      _ = slotDeterminant values 1 + values 15 := by rw [hDelta]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ hdet]
  · have identity :
        eval₂Hom (Int.castRingHom R) (leafValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedEquations 31).toPoly =
            -slotDeterminant values 1 + factorL values * factorGa values := by
        simp [leafValues,
          Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedEquations,
          SparsePoly.toPoly, SparseTerm.toPoly, factorL, factorGa, h23]
        ring
    rw [identity, hReflected]
  · have hinv : (values 51)⁻¹ * values 51 = 1 :=
      inv_mul_cancel₀ h24
    simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, hinv]
  · have hinv : values 37 * (values 37)⁻¹ = 1 :=
      mul_inv_cancel₀ h13_12
    simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, hinv]

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000

/-- The named `b4 / w01 = 0` chart is impossible over every
characteristic-zero field. -/
theorem refutes_chart3_b4_w01_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 ≠ 0) (h12_12 : values 29 = 0)
    (h12_10 : values 27 = 0) (h01 : values 1 = 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart' h24 h25
  have h25eq : values 56 = -values 51 := by
    calc
      values 56 = (values 51 + values 56) - values 51 := by ring
      _ = -values 51 := by rw [hsum]; ring
  obtain ⟨h25_00, h04_00, h04_02, h04_22, h04_20, h24_22,
      h04_11, h04_12, h05_10⟩ :=
    closure_zeros values base hdet chart' h24 h25 hsum h13_12 h12_12 h12_10 h01
  have direct := direct_selected_zero values base chart' h13_10 h12_12 h12_10 h01
    h25eq h25_00 h04_00 h04_02 h04_22 h04_20 h24_22 h04_11 h04_12 h05_10
  obtain ⟨special0, special1, special2, special3⟩ :=
    special_selected_zero values base hdet h24 h13_12
  apply Krenn.FrozenCase0NoncollapseType01Chart3B4W01ZeroCertificate.selectedHasNoCommonZero
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
  · exact direct 22
  · exact direct 23
  · exact direct 24
  · exact direct 25
  · exact direct 26
  · exact direct 27
  · exact direct 28
  · exact direct 29
  · exact special0
  · exact special1
  · exact special2
  · exact special3

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B4W01Zero.closure_zeros
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B4W01Zero.refutes_chart3_b4_w01_zero

end Krenn.FrozenCase0NoncollapseType01Chart3B4W01Zero
