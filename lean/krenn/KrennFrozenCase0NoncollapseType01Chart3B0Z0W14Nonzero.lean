import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate

/-!
Semantic reflection of the smallest residual strict leaf in the chart-3
both-pivots-live, zero-sum tree.  The frozen certificate has ten selected
rows, all with a direct canonical-source provenance.  Six source-level
monomial consequences realize the zero closure used by the frozen leaf.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14Nonzero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3
open Krenn.SparseCertificate
open MvPolynomial

def zeroSourceIndex : Fin 6 → Fin 747 := ![709, 362, 645, 532, 738, 505]

def selectedSourceIndex : Fin 10 → Fin 747 := ![
  745, 730, 175, 31, 25, 349, 333, 679, 336, 746
]

theorem zero_source_not_determinant
    (index : Fin 6) (slot : Fin 18) :
    determinantSourceIndex slot ≠ zeroSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, zeroSourceIndex]

theorem selected_source_not_determinant
    (index : Fin 10) (slot : Fin 18) :
    determinantSourceIndex slot ≠ selectedSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, selectedSourceIndex]

noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 64 → R := ![
  (values 51)⁻¹,
  slotDeterminant values 1,
  (factorGb values)⁻¹,
  (factorL values)⁻¹,
  (slotDeterminant values 1)⁻¹,
  values 0, values 2, values 3, values 4, values 5,
  values 9, values 10, values 11, values 12, values 13,
  values 14, values 15, values 16, values 17, values 18,
  values 19, values 20, values 21, values 22, values 24,
  values 25, values 26, values 30, values 32, values 33,
  values 34, values 38, values 39, values 40, values 41,
  values 42, values 43, values 44, values 46, values 50,
  values 51, values 52, values 53, values 54, values 55,
  values 57, values 58, values 59, values 60, values 61,
  values 62, values 63, values 64, values 65, values 66,
  values 67, values 68, values 69, values 70, values 71,
  values 72, values 73, values 74,
  (values 42)⁻¹
]

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The six canonical consequences used by the frozen monomial-zero closure. -/
theorem closure_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 = 0) (h12_12 : values 29 = 0)
    (h12_10 : values 27 = 0) (h01 : values 1 = 0)
    (h15 : values 45 = 0) (h14 : values 42 ≠ 0) :
    values 6 = 0 ∧ values 49 = 0 ∧ values 7 = 0 ∧ values 8 = 0 ∧
      values 47 = 0 ∧ values 31 = 0 := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart' h24 h25
  have h25eq : values 56 = -values 51 := by
    calc
      values 56 = (values 51 + values 56) - values 51 := by ring
      _ = -values 51 := by rw [hsum]; ring
  have source0 : sourceValue values (zeroSourceIndex 0) = 0 :=
    base (zeroSourceIndex 0) (zero_source_not_determinant 0)
  have h03_00 : values 6 = 0 := by
    have identity : sourceValue values (zeroSourceIndex 0) =
        -(values 42 * values 51 * values 6) := by
      simp [sourceValue, zeroSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h01, h15, h25eq]
      ring
    rw [identity] at source0
    have productZero : values 42 * values 51 * values 6 = 0 := neg_eq_zero.mp source0
    exact (mul_eq_zero.mp productZero).resolve_left (mul_ne_zero h14 h24)
  have source1 : sourceValue values (zeroSourceIndex 1) = 0 :=
    base (zeroSourceIndex 1) (zero_source_not_determinant 1)
  have h23_22 : values 49 = 0 := by
    have identity : sourceValue values (zeroSourceIndex 1) = values 42 * values 49 := by
      simp [sourceValue, zeroSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h23, h12, h13, h13_12, h12_12, h15]
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_left h14
  have source2 : sourceValue values (zeroSourceIndex 2) = 0 :=
    base (zeroSourceIndex 2) (zero_source_not_determinant 2)
  have h03_11 : values 7 = 0 := by
    have identity : sourceValue values (zeroSourceIndex 2) = values 42 * values 7 := by
      simp [sourceValue, zeroSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h12, h13, h12_10, h13_10, h01]
      ring
    rw [identity] at source2
    exact (mul_eq_zero.mp source2).resolve_left h14
  have source3 : sourceValue values (zeroSourceIndex 3) = 0 :=
    base (zeroSourceIndex 3) (zero_source_not_determinant 3)
  have h03_22 : values 8 = 0 := by
    have identity : sourceValue values (zeroSourceIndex 3) = values 42 * values 8 := by
      simp [sourceValue, zeroSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h12_10, h13_12]
      ring
    rw [identity] at source3
    exact (mul_eq_zero.mp source3).resolve_left h14
  have source4 : sourceValue values (zeroSourceIndex 4) = 0 :=
    base (zeroSourceIndex 4) (zero_source_not_determinant 4)
  have h23_00 : values 47 = 0 := by
    have identity : sourceValue values (zeroSourceIndex 4) = values 42 * values 47 := by
      simp [sourceValue, zeroSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly,
        h03_00, h12_10, h13_10, h15]
    rw [identity] at source4
    exact (mul_eq_zero.mp source4).resolve_left h14
  have source5 : sourceValue values (zeroSourceIndex 5) = 0 :=
    base (zeroSourceIndex 5) (zero_source_not_determinant 5)
  have h12_21 : values 31 = 0 := by
    have identity : sourceValue values (zeroSourceIndex 5) = values 31 := by
      simp [sourceValue, zeroSourceIndex, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h03_00, h25eq]
    rwa [identity] at source5
  exact ⟨h03_00, h23_22, h03_11, h03_22, h23_00, h12_21⟩

/-- A fully provenance-bound reflection of the `b0z0/w14!=0` strict leaf. -/
theorem refutes_chart3_b0z0_w14_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 = 0) (h12_12 : values 29 = 0)
    (h12_10 : values 27 = 0) (h01 : values 1 = 0)
    (h15 : values 45 = 0) (h14 : values 42 ≠ 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart' h24 h25
  have h25eq : values 56 = -values 51 := by
    calc
      values 56 = (values 51 + values 56) - values 51 := by ring
      _ = -values 51 := by rw [hsum]; ring
  obtain ⟨h03_00, h23_22, h03_11, h03_22, h23_00, h12_21⟩ :=
    closure_zeros values base hdet chart' h24 h25 hsum
      h13_12 h12_12 h12_10 h01 h15 h14
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
  apply Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate.selectedHasNoCommonZero
    (leafValues values)
  intro index
  fin_cases index
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h01, h15, h25eq,
      h03_00, h23_22, h03_11, h03_22, h23_00, h12_21] at source0 ⊢
    ring_nf at source0 ⊢
    exact source0
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h01, h15, h25eq,
      h03_00, h23_22, h03_11, h03_22, h23_00, h12_21] at source1 ⊢
    ring_nf at source1 ⊢
    exact source1
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h01, h15, h25eq,
      h03_00, h23_22, h03_11, h03_22, h23_00, h12_21] at source2 ⊢
    ring_nf at source2 ⊢
    exact source2
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h01, h15, h25eq,
      h03_00, h23_22, h03_11, h03_22, h23_00, h12_21] at source3 ⊢
    ring_nf at source3 ⊢
    exact source3
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h01, h15, h25eq,
      h03_00, h23_22, h03_11, h03_22, h23_00, h12_21] at source4 ⊢
    ring_nf at source4 ⊢
    exact source4
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h01, h15, h25eq,
      h03_00, h23_22, h03_11, h03_22, h23_00, h12_21] at source5 ⊢
    ring_nf at source5 ⊢
    exact source5
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h01, h15, h25eq,
      h03_00, h23_22, h03_11, h03_22, h23_00, h12_21] at source6 ⊢
    ring_nf at source6 ⊢
    exact source6
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h01, h15, h25eq,
      h03_00, h23_22, h03_11, h03_22, h23_00, h12_21] at source7 ⊢
    ring_nf at source7 ⊢
    exact source7
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h01, h15, h25eq,
      h03_00, h23_22, h03_11, h03_22, h23_00, h12_21] at source8 ⊢
    ring_nf at source8 ⊢
    exact source8
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14NonzeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_12, h12_10, h01, h15, h25eq,
      h03_00, h23_22, h03_11, h03_22, h23_00, h12_21] at source9 ⊢
    ring_nf at source9 ⊢
    exact source9

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14Nonzero.closure_zeros
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14Nonzero.refutes_chart3_b0z0_w14_nonzero

end Krenn.FrozenCase0NoncollapseType01Chart3B0Z0W14Nonzero
