import KrennFrozenCase0NoncollapseType01Chart3BothLive
import KrennFrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate

/-!
Semantic reflection of the smallest remaining profile-localized strict leaf
in the chart-3 both-pivots-live, zero-sum tree.

Eight selected rows are direct images of canonical rows.  The remaining two
are inverse witnesses: `theta_0_1_inv` is the inverse of
`w_05_21 - w_04_21`, forced nonzero by non-collapse and the zero pivot sum;
the final branch inverse is the inverse of live `w_12_12`.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15Zero

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3
open Krenn.SparseCertificate
open MvPolynomial

def selectedSourceIndex : Fin 8 → Fin 747 := ![
  607, 606, 720, 687, 181, 645, 745, 360
]

theorem selected_source_not_determinant
    (index : Fin 8) (slot : Fin 18) :
    determinantSourceIndex slot ≠ selectedSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, selectedSourceIndex]

/-- The certificate only uses `branch0_inv_0` through neither its selected
equations nor its multipliers, so its value is immaterial here. -/
noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 → R) : Fin 64 → R := ![
  0,
  values 23 - values 15,
  (factorGb values)⁻¹,
  (factorL values)⁻¹,
  (values 23 - values 15)⁻¹,
  values 0, values 2, values 3, values 4, values 5,
  values 6, values 7, values 8, values 9, values 10,
  values 11, values 12, values 13, values 14, values 15,
  values 16, values 17, values 18, values 19, values 22,
  values 25, values 26, values 29, values 30, values 31,
  values 32, values 33, values 34, values 38, values 39,
  values 40, values 41, values 42, values 43, values 44,
  values 46, values 47, values 49, values 50, values 51,
  values 52, values 53, values 54, values 55, values 57,
  values 58, values 59, values 60, values 63, values 64,
  values 65, values 67, values 69, values 70, values 71,
  values 72, values 73, values 74,
  (values 29)⁻¹
]

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- A fully provenance-bound reflection of the `b2z/w15=0` strict leaf. -/
theorem refutes_chart3_b2z_w15_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (hsum : values 51 + values 56 = 0)
    (h13_12 : values 37 = 0) (h12_12 : values 29 ≠ 0)
    (h12_10 : values 27 = 0) (h01 : values 1 = 0)
    (h15 : values 45 = 0) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live values base hdet chart' h24 h25
  have h25eq : values 56 = -values 51 := by
    calc
      values 56 = (values 51 + values 56) - values 51 := by ring
      _ = -values 51 := by rw [hsum]; ring
  have hGb : factorGb values ≠ 0 :=
    (noncollapse_factor_geometry values base hdet).2.1
  have hGbFactor : factorGb values = (values 23 - values 15) * values 51 := by
    simp [factorGb, h25eq]
    ring
  rw [hGbFactor] at hGb
  have hDelta : values 23 - values 15 ≠ 0 :=
    (mul_ne_zero_iff.mp hGb).1
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
  apply Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate.selectedHasNoCommonZero
    (leafValues values)
  intro index
  fin_cases index
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_10, h01, h15, h25eq] at source0 ⊢
    ring_nf at source0 ⊢
    exact source0
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_10, h01, h15, h25eq] at source1 ⊢
    ring_nf at source1 ⊢
    exact source1
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_10, h01, h15, h25eq] at source2 ⊢
    ring_nf at source2 ⊢
    exact source2
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_10, h01, h15, h25eq] at source3 ⊢
    ring_nf at source3 ⊢
    exact source3
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_10, h01, h15, h25eq] at source4 ⊢
    ring_nf at source4 ⊢
    exact source4
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_10, h01, h15, h25eq] at source5 ⊢
    ring_nf at source5 ⊢
    exact source5
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_10, h01, h15, h25eq] at source6 ⊢
    ring_nf at source6 ⊢
    exact source6
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate.selectedEquations,
      leafValues, sourceValue, selectedSourceIndex, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly,
      h23, h12, h13, h13_10, h13_12, h12_10, h01, h15, h25eq] at source7 ⊢
    ring_nf at source7 ⊢
    exact source7
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate.selectedEquations,
      leafValues, SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ hDelta]
  · simp [Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15ZeroCertificate.selectedEquations,
      leafValues, SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ h12_12]

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15Zero.refutes_chart3_b2z_w15_zero

end Krenn.FrozenCase0NoncollapseType01Chart3B2Z_W15Zero
