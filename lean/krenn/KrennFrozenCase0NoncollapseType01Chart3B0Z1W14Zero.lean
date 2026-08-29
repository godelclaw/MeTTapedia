import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3CanonicalPropagation
import KrennFrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate

/-!
Semantic reflection of the final strict `b0z1 / w14 = 0` leaf in the
Chart-3, both-pivots-live, zero-sum tree.

The certificate is replayed exactly over its reduced frozen system.  This
file also reconstructs its 34 canonical selected rows, four monomial-zero
closure consequences, and five explicit inverse/factor rows from the
canonical case-0 system.  Thus the leaf is attached to mathematics rather
than only to a solver transcript.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14Zero

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

def closureSourceIndex : Fin 4 -> Fin 747 := ![709, 362, 714, 505]

def directSourceIndex : Fin 34 -> Fin 747 := ![
  607, 606, 720, 377, 157, 394, 738, 465, 350, 233, 745, 731,
  22, 26, 295, 304, 27, 300, 131, 360, 177, 31, 591, 135,
  354, 123, 349, 359, 338, 339, 332, 733, 685, 746]

theorem closure_source_not_determinant
    (index : Fin 4) (slot : Fin 18) :
    determinantSourceIndex slot ≠ closureSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, closureSourceIndex]

theorem direct_source_not_determinant
    (index : Fin 34) (slot : Fin 18) :
    determinantSourceIndex slot ≠ directSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, directSourceIndex]

noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 -> R) : Fin 64 -> R := ![
  (values 51)⁻¹, slotDeterminant values 1, (factorGb values)⁻¹,
  (factorL values)⁻¹, (slotDeterminant values 1)⁻¹,
  values 0, values 2, values 3, values 7, values 9, values 10,
  values 11, values 12, values 13, values 14, values 15, values 16,
  values 17, values 18, values 19, values 20, values 21, values 22,
  values 24, values 25, values 26, values 30, values 32, values 33,
  values 34, values 38, values 39, values 40, values 41, values 43,
  values 44, values 45, values 46, values 47, values 50, values 51,
  values 52, values 53, values 54, values 55, values 57, values 58,
  values 59, values 60, values 61, values 62, values 63, values 64,
  values 65, values 66, values 67, values 68, values 69, values 70,
  values 71, values 72, values 73, values 74, (values 45)⁻¹]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
/-- The four canonical monomial consequences used by the frozen closure. -/
theorem closure_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 = 0) (h12_12 : values 29 = 0)
    (_h12_10 : values 27 = 0) (_h01 : values 1 = 0)
    (h15 : values 45 ≠ 0) (h14 : values 42 = 0) :
    values 6 = 0 /\ values 49 = 0 /\ values 8 = 0 /\ values 31 = 0 := by
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
  have h03_00 : values 6 = 0 := by
    have identity : sourceValue values (closureSourceIndex 0) =
        values 6 * values 45 * values 51 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h13_12, h12_12, _h12_10, _h01, h14, h25eq]
    rw [identity] at source0
    have product : values 6 * values 45 = 0 :=
      (mul_eq_zero.mp source0).resolve_right h24
    exact (mul_eq_zero.mp product).resolve_right h15
  have source1 : sourceValue values (closureSourceIndex 1) = 0 :=
    base (closureSourceIndex 1) (closure_source_not_determinant 1)
  have h23_22 : values 49 = 0 := by
    have identity : sourceValue values (closureSourceIndex 1) =
        values 45 * values 49 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h13_12, h12_12, _h12_10, _h01, h14, h25eq]
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_left h15
  have source2 : sourceValue values (closureSourceIndex 2) = 0 :=
    base (closureSourceIndex 2) (closure_source_not_determinant 2)
  have h03_22 : values 8 = 0 := by
    have identity : sourceValue values (closureSourceIndex 2) =
        values 8 * values 45 * values 51 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h13_12, h12_12, _h12_10, _h01, h14, h25eq]
    rw [identity] at source2
    have product : values 8 * values 45 = 0 :=
      (mul_eq_zero.mp source2).resolve_right h24
    exact (mul_eq_zero.mp product).resolve_right h15
  have source3 : sourceValue values (closureSourceIndex 3) = 0 :=
    base (closureSourceIndex 3) (closure_source_not_determinant 3)
  have h12_21 : values 31 = 0 := by
    have identity : sourceValue values (closureSourceIndex 3) = values 31 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h03_00, h25eq]
    rwa [identity] at source3
  exact ⟨h03_00, h23_22, h03_22, h12_21⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem direct_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h13_10 : values 35 = 0) (h13_12 : values 37 = 0)
    (h12_12 : values 29 = 0) (h12_10 : values 27 = 0)
    (h01 : values 1 = 0) (h14 : values 42 = 0)
    (h02_11 : values 4 = 0) (h02_22 : values 5 = 0)
    (h25eq : values 56 = -values 51)
    (h03_00 : values 6 = 0) (h23_22 : values 49 = 0)
    (h03_22 : values 8 = 0) (h12_21 : values 31 = 0) :
    forall index : Fin 34,
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations
          (Fin.castAdd 5 index)).toPoly = 0 := by
  intro index
  rcases chart with ⟨h23, h12, h13⟩
  have source : sourceValue values (directSourceIndex index) = 0 :=
    base (directSourceIndex index) (direct_source_not_determinant index)
  fin_cases index <;>
    simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations,
      sourceValue, directSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa,
      factorGb, h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h01, h14,
      h02_11, h02_22,
      h25eq, h03_00, h23_22, h03_22, h12_21] at source ⊢ <;>
    ring_nf at source ⊢ <;>
    exact source

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem special_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (_h24 : values 51 ≠ 0) (h15 : values 45 ≠ 0)
    (hsum : values 51 + values 56 = 0) :
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations 34).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations 35).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations 36).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations 37).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations 38).toPoly = 0 := by
  obtain ⟨hL, hGb, _hGa⟩ := noncollapse_factor_geometry values base hdet
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
  have h25eq : values 56 = -values 51 := by
    calc
      values 56 = (values 51 + values 56) - values 51 := by ring
      _ = -values 51 := by rw [hsum]; ring
  have hDelta : values 23 - values 15 = slotDeterminant values 1 := by
    simp [slotDeterminant, slotA1, slotB1, slotA2, slotB2]
  have h23 : values 23 = slotDeterminant values 1 + values 15 := by
    calc
      values 23 = (values 23 - values 15) + values 15 := by ring
      _ = slotDeterminant values 1 + values 15 := by rw [hDelta]
  have hGbEq : factorGb values = slotDeterminant values 1 * values 51 := by
    simp [factorGb, h25eq, <- hDelta]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ hdet]
  · have identity :
        eval₂Hom (Int.castRingHom R) (leafValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations 35).toPoly =
            -slotDeterminant values 1 + factorL values * factorGa values := by
        simp [leafValues,
          Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations,
          SparsePoly.toPoly, SparseTerm.toPoly, factorL, factorGa, h23]
        ring
    rw [identity, hReflected]
  · have identity :
        eval₂Hom (Int.castRingHom R) (leafValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations 36).toPoly =
            (factorL values)⁻¹ * factorL values - 1 := by
        simp [leafValues,
          Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations,
          SparsePoly.toPoly, SparseTerm.toPoly, factorL]
        ring
    rw [identity, inv_mul_cancel₀ hL]
    ring
  · have identity :
        eval₂Hom (Int.castRingHom R) (leafValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations 37).toPoly =
            (factorGb values)⁻¹ * factorGb values - 1 := by
        simp [leafValues,
          Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations,
          SparsePoly.toPoly, SparseTerm.toPoly]
        rw [hGbEq]
        ring
    rw [identity, inv_mul_cancel₀ hGb]
    ring
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ h15]

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000

/-- The named `b0z1 / w14 = 0` chart is impossible over every
characteristic-zero field. -/
theorem refutes_chart3_b0z1_w14_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 = 0) (h12_12 : values 29 = 0)
    (h12_10 : values 27 = 0) (h01 : values 1 = 0)
    (h15 : values 45 ≠ 0) (h14 : values 42 = 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart' h24 h25
  have h25eq : values 56 = -values 51 := by
    calc
      values 56 = (values 51 + values 56) - values 51 := by ring
      _ = -values 51 := by rw [hsum]; ring
  obtain ⟨h03_00, h23_22, h03_22, h12_21⟩ :=
    closure_zeros values base hdet chart' h24 h25 hsum
      h13_12 h12_12 h12_10 h01 h15 h14
  obtain ⟨h02_11, h02_22⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3CanonicalPropagation.w02_channel_ends_zero_of_w01_w12_12_zero_w15_live
      values base hdet chart' h24 h25 h01 h12_12 h15
  have direct := direct_selected_zero values base chart' h13_10 h13_12 h12_12 h12_10
    h01 h14 h02_11 h02_22 h25eq h03_00 h23_22 h03_22 h12_21
  obtain ⟨special34, special35, special36, special37, special38⟩ :=
    special_selected_zero values base hdet h24 h15 hsum
  apply Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14ZeroCertificate.selectedHasNoCommonZero
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
  · exact direct 30
  · exact direct 31
  · exact direct 32
  · exact direct 33
  · exact special34
  · exact special35
  · exact special36
  · exact special37
  · exact special38

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14Zero.closure_zeros
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14Zero.refutes_chart3_b0z1_w14_zero

end Krenn.FrozenCase0NoncollapseType01Chart3B0Z1W14Zero
