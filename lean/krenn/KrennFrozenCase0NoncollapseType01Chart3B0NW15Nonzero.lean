import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate

/-!
Semantic reflection of the strict `b0n / w15 != 0` leaf in the chart-3,
both-pivots-live, zero-sum tree.

The certificate itself is an exact 27-row integer identity.  This bridge
binds every selected row to either a named canonical frozen row, a derived
zero from a named canonical row, or one of the displayed inverse/factor
relations.  Thus the contradiction is about the original 747-row system,
not merely the substituted leaf file.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B0NW15Nonzero

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

/-- The nine canonical rows which supply the monomial-zero closure. -/
def closureSourceIndex : Fin 9 -> Fin 747 :=
  ![328, 329, 162, 163, 325, 326, 160, 161, 488]

/-- The twenty selected leaf rows with direct canonical provenance. -/
def directSourceIndex : Fin 20 -> Fin 747 :=
  ![606, 380, 382, 652, 394, 392, 513, 604, 231, 32,
    605, 556, 727, 360, 175, 177, 354, 349, 735, 746]

theorem closure_source_not_determinant
    (index : Fin 9) (slot : Fin 18) :
    determinantSourceIndex slot ≠ closureSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, closureSourceIndex]

theorem direct_source_not_determinant
    (index : Fin 20) (slot : Fin 18) :
    determinantSourceIndex slot ≠ directSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, directSourceIndex]

/-- The exact variable substitution recorded by the frozen leaf. -/
noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 -> R) : Fin 64 -> R := ![
  (values 51)⁻¹, slotDeterminant values 1, (factorGb values)⁻¹,
  (factorL values)⁻¹, (slotDeterminant values 1)⁻¹,
  values 0, values 1, values 2, values 3, values 4,
  values 6, values 7, values 8, values 9, values 10, values 11,
  values 12, values 13, values 14, values 15, values 16, values 17,
  values 18, values 19, values 20, values 21, values 22, values 24,
  values 25, values 26, values 30, values 31, values 32, values 33,
  values 34, values 38, values 39, values 40, values 41, values 42,
  values 43, values 44, values 45, values 46, values 47, values 49,
  values 50, values 51, values 52, values 53, values 54, values 55,
  values 61, values 62, values 63, values 64, values 69, values 70,
  values 71, values 72, values 73, values 74,
  (values 1)⁻¹, (values 45)⁻¹]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
/-- The nine zero coordinates propagated from the branch's canonical rows. -/
theorem closure_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h13_10 : values 35 = 0) (h13_12 : values 37 = 0)
    (h12_12 : values 29 = 0) (h12_10 : values 27 = 0)
    (h01 : values 1 ≠ 0) (h15 : values 45 ≠ 0) :
    values 65 = 0 /\ values 66 = 0 /\ values 67 = 0 /\ values 68 = 0 /\
      values 57 = 0 /\ values 58 = 0 /\ values 59 = 0 /\ values 60 = 0 /\
      values 5 = 0 := by
  rcases chart with ⟨h23, h12, h13⟩
  have source0 : sourceValue values (closureSourceIndex 0) = 0 :=
    base (closureSourceIndex 0) (closure_source_not_determinant 0)
  have h34_12 : values 65 = 0 := by
    have identity : sourceValue values (closureSourceIndex 0) = values 1 * values 65 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12, h13, h13_10, h12_10]
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_left h01
  have source1 : sourceValue values (closureSourceIndex 1) = 0 :=
    base (closureSourceIndex 1) (closure_source_not_determinant 1)
  have h34_20 : values 66 = 0 := by
    have identity : sourceValue values (closureSourceIndex 1) = values 1 * values 66 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h13_12, h12_10]
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_left h01
  have source2 : sourceValue values (closureSourceIndex 2) = 0 :=
    base (closureSourceIndex 2) (closure_source_not_determinant 2)
  have h34_21 : values 67 = 0 := by
    have identity : sourceValue values (closureSourceIndex 2) = values 1 * values 67 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h13_12, h12_10]
    rw [identity] at source2
    exact (mul_eq_zero.mp source2).resolve_left h01
  have source3 : sourceValue values (closureSourceIndex 3) = 0 :=
    base (closureSourceIndex 3) (closure_source_not_determinant 3)
  have h34_22 : values 68 = 0 := by
    have identity : sourceValue values (closureSourceIndex 3) = values 1 * values 68 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h13_12, h12_10]
    rw [identity] at source3
    exact (mul_eq_zero.mp source3).resolve_left h01
  have source4 : sourceValue values (closureSourceIndex 4) = 0 :=
    base (closureSourceIndex 4) (closure_source_not_determinant 4)
  have h25_12 : values 57 = 0 := by
    have identity : sourceValue values (closureSourceIndex 4) = values 1 * values 57 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12, h13_10]
    rw [identity] at source4
    exact (mul_eq_zero.mp source4).resolve_left h01
  have source5 : sourceValue values (closureSourceIndex 5) = 0 :=
    base (closureSourceIndex 5) (closure_source_not_determinant 5)
  have h25_20 : values 58 = 0 := by
    have identity : sourceValue values (closureSourceIndex 5) = values 1 * values 58 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12_12, h13_10]
    rw [identity] at source5
    exact (mul_eq_zero.mp source5).resolve_left h01
  have source6 : sourceValue values (closureSourceIndex 6) = 0 :=
    base (closureSourceIndex 6) (closure_source_not_determinant 6)
  have h25_21 : values 59 = 0 := by
    have identity : sourceValue values (closureSourceIndex 6) = values 1 * values 59 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h13_10, h12_12]
    rw [identity] at source6
    exact (mul_eq_zero.mp source6).resolve_left h01
  have source7 : sourceValue values (closureSourceIndex 7) = 0 :=
    base (closureSourceIndex 7) (closure_source_not_determinant 7)
  have h25_22 : values 60 = 0 := by
    have identity : sourceValue values (closureSourceIndex 7) = values 1 * values 60 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h13_10, h12_12]
    rw [identity] at source7
    exact (mul_eq_zero.mp source7).resolve_left h01
  have source8 : sourceValue values (closureSourceIndex 8) = 0 :=
    base (closureSourceIndex 8) (closure_source_not_determinant 8)
  have h02_22 : values 5 = 0 := by
    have identity : sourceValue values (closureSourceIndex 8) = values 5 * values 45 := by
      simp [sourceValue, closureSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h13_10, h12_12]
    rw [identity] at source8
    exact (mul_eq_zero.mp source8).resolve_right h15
  exact ⟨h34_12, h34_20, h34_21, h34_22, h25_12, h25_20, h25_21, h25_22,
    h02_22⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
/-- The first twenty certificate rows are direct canonical rows after the
recorded chart and monomial-zero reductions. -/
theorem direct_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h13_10 : values 35 = 0) (h13_12 : values 37 = 0)
    (h12_12 : values 29 = 0) (h12_10 : values 27 = 0)
    (h25eq : values 56 = -values 51)
    (h34_12 : values 65 = 0) (h34_20 : values 66 = 0)
    (h34_21 : values 67 = 0) (h34_22 : values 68 = 0)
    (h25_12 : values 57 = 0) (h25_20 : values 58 = 0)
    (h25_21 : values 59 = 0) (h25_22 : values 60 = 0)
    (h02_22 : values 5 = 0) :
    forall index : Fin 20,
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations
          (Fin.castAdd 7 index)).toPoly = 0 := by
  intro index
  rcases chart with ⟨h23, h12, h13⟩
  have source : sourceValue values (directSourceIndex index) = 0 :=
    base (directSourceIndex index) (direct_source_not_determinant index)
  fin_cases index <;>
    simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations,
      sourceValue, directSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGb,
      h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h25eq,
      h34_12, h34_20, h34_21, h34_22,
      h25_12, h25_20, h25_21, h25_22, h02_22] at source ⊢ <;>
    ring_nf at source ⊢ <;>
    exact source

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem theta_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (hdet : slotDeterminant values 1 ≠ 0) :
    eval₂Hom (Int.castRingHom R) (leafValues values)
      (Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations 20).toPoly = 0 := by
  have hinv : slotDeterminant values 1 * (slotDeterminant values 1)⁻¹ = 1 :=
    mul_inv_cancel₀ hdet
  simp [leafValues,
    Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly, hinv]

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem factor_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (hsum : values 51 + values 56 = 0) :
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations 21).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations 22).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations 23).toPoly = 0 := by
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
  have hGbEq : factorGb values = slotDeterminant values 1 * values 51 := by
    simp [factorGb, h25eq, <- hDelta]
    ring
  have hinvL : (factorL values)⁻¹ * factorL values = 1 :=
    inv_mul_cancel₀ hL
  have hinvGb : (factorGb values)⁻¹ * factorGb values = 1 :=
    inv_mul_cancel₀ hGb
  constructor
  · have identity :
        eval₂Hom (Int.castRingHom R) (leafValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations 21).toPoly =
            -slotDeterminant values 1 + factorL values * factorGa values := by
        simp [leafValues,
          Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations,
          SparsePoly.toPoly, SparseTerm.toPoly,
          slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa]
        ring
    rw [identity, hReflected]
  constructor
  · have identity :
        eval₂Hom (Int.castRingHom R) (leafValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations 22).toPoly =
            (factorL values)⁻¹ * factorL values - 1 := by
        simp [leafValues,
          Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations,
          SparsePoly.toPoly, SparseTerm.toPoly, factorL]
        ring
    rw [identity, hinvL]
    ring
  · have identity :
        eval₂Hom (Int.castRingHom R) (leafValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations 23).toPoly =
            (factorGb values)⁻¹ * factorGb values - 1 := by
        simp [leafValues,
          Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations,
          SparsePoly.toPoly, SparseTerm.toPoly]
        rw [hGbEq]
        ring
    rw [identity, hinvGb]
    ring

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem branch_inverse_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R)
    (h24 : values 51 ≠ 0) (h01 : values 1 ≠ 0) (h15 : values 45 ≠ 0) :
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations 24).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations 25).toPoly = 0 /\
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations 26).toPoly = 0 := by
  constructor
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, inv_mul_cancel₀ h24]
  constructor
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ h01]
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ h15]

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000

/-- The named `b0n / w15 != 0` chart is impossible over every
characteristic-zero field.  Lean checks the exact integer certificate and
every route from its selected rows back to canonical case-0 rows. -/
theorem refutes_chart3_b0n_w15_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 = 0) (h12_12 : values 29 = 0)
    (h12_10 : values 27 = 0) (h01 : values 1 ≠ 0)
    (h15 : values 45 ≠ 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart' h24 h25
  have h25eq : values 56 = -values 51 := by
    calc
      values 56 = (values 51 + values 56) - values 51 := by ring
      _ = -values 51 := by rw [hsum]; ring
  obtain ⟨h34_12, h34_20, h34_21, h34_22, h25_12, h25_20, h25_21, h25_22,
      h02_22⟩ :=
    closure_zeros values base chart' h13_10 h13_12 h12_12 h12_10 h01 h15
  have direct := direct_selected_zero values base chart' h13_10 h13_12 h12_12 h12_10
    h25eq h34_12 h34_20 h34_21 h34_22 h25_12 h25_20 h25_21 h25_22 h02_22
  have theta := theta_selected_zero values hdet
  obtain ⟨factor21, factor22, factor23⟩ :=
    factor_selected_zero values base hdet hsum
  obtain ⟨branch24, branch25, branch26⟩ :=
    branch_inverse_selected_zero values h24 h01 h15
  apply Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedHasNoCommonZero
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
  · exact theta
  · exact factor21
  · exact factor22
  · exact factor23
  · exact branch24
  · exact branch25
  · exact branch26

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B0NW15Nonzero.closure_zeros
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B0NW15Nonzero.refutes_chart3_b0n_w15_nonzero

end Krenn.FrozenCase0NoncollapseType01Chart3B0NW15Nonzero
