import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate

/-!
Semantic reflection of the strict B0 `w_34_11 = 0` certificate.

The certificate has twenty-one selected rows.  Sixteen are traced through the
frozen transformation chain to named rows of the canonical 747-row case-0
system; the remaining five are the displayed pivot inverse and four branch
equalities.  The selected-row identity is checked independently in Lean.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroBridge

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

/-- Canonical provenance for the sixteen non-branch selected rows, as traced
through the recorded frozen maps. -/
def directSourceIndex : Fin 16 → Fin 747 := ![
  193, 362, 645, 644, 745, 300, 175, 31,
  591, 354, 349, 488, 703, 333, 735, 746
]

theorem direct_source_not_determinant (index : Fin 16) (slot : Fin 18) :
    determinantSourceIndex slot ≠ directSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, directSourceIndex]

/-- The exact value map recorded by the B0 branch, including its reversible
affine coordinate and existing localization witnesses. -/
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
  values 57,
  values 58,
  values 59,
  values 60,
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
  values 74
]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem direct_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (h12_10 : values 27 = 0) (h13_12 : values 37 = 0)
    (h12_12 : values 29 = 0) (h01 : values 1 = 0)
    (h34 : values 64 = 0) :
    ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedEquations
          (Fin.castAdd 5 index)).toPoly = 0 := by
  intro index
  rcases chart with ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet ⟨h23, h12, h13⟩ h24 h25
  have source : sourceValue values (directSourceIndex index) = 0 :=
    base (directSourceIndex index) (direct_source_not_determinant index)
  fin_cases index <;>
    simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedEquations,
      sourceValue, directSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      slotDeterminant, slotA1, slotB1, slotA2, slotB2, factorL, factorGa, factorGb,
      h23, h12, h13, h13_10, h13_12, h12_10, h12_12, h01, h34] at source ⊢ <;>
    ring_nf at source ⊢ <;>
    exact source

set_option maxRecDepth 500000 in
set_option maxHeartbeats 10000000 in
theorem branch_selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R)
    (h24 : values 51 ≠ 0)
    (h12_10 : values 27 = 0) (h12_12 : values 29 = 0)
    (h01 : values 1 = 0) (h34 : values 64 = 0) :
    eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedEquations 16).toPoly = 0 ∧
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedEquations 17).toPoly = 0 ∧
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedEquations 18).toPoly = 0 ∧
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedEquations 19).toPoly = 0 ∧
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedEquations 20).toPoly = 0 := by
  repeat' apply And.intro
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, inv_mul_cancel₀ h24]
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, h12_10]
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, h12_12]
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, h01]
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, h34]

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000

/-- The B0, `w_34_11 = 0` face is impossible by the exact 21-row identity
replayed above against its canonical source provenance. -/
theorem refutes_chart3_both_live_sum_nonzero_b0_w34_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 ≠ 0)
    (h34 : values 64 = 0) : False := by
  obtain ⟨h12_10, h13_12, h12_12, h01⟩ :=
    Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0Reduction.survivor_has_b0_reductions
      values base hdet chart h24 h25 hsum
  have direct := direct_selected_zero values base hdet chart h24 h25
    h12_10 h13_12 h12_12 h01 h34
  obtain ⟨branch16, branch17, branch18, branch19, branch20⟩ :=
    branch_selected_zero values h24 h12_10 h12_12 h01 h34
  apply Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedHasNoCommonZero
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
  · exact branch16
  · exact branch17
  · exact branch18
  · exact branch19
  · exact branch20

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroBridge.refutes_chart3_both_live_sum_nonzero_b0_w34_zero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroBridge
