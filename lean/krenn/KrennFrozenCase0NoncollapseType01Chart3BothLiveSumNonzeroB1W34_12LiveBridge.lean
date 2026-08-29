import KrennFrozenCase0NoncollapseType01Chart3
import KrennFrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveCertificate

/-!
Semantic reflection of the smallest unimported B1 leaf of the chart-3,
both-pivots-live, nonzero-sum tree.

The strict four-row identity is attached directly to canonical source row
328 and the three displayed branch facts.  In particular, this bridge does
not depend on an artifact label or a historical row ordering.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveBridge

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

/-- Only the coordinates used by the four selected equations need values;
the remaining coordinates are immaterial to this selected-row identity. -/
noncomputable def leafValues {R : Type*} [Field R]
    (values : Fin 75 -> R) : Fin 75 -> R :=
  fun index =>
    if index = 8 then values 1 else
    if index = 33 then values 27 else
    if index = 63 then values 65 else
    if index = 73 then (values 1)⁻¹ else
    if index = 74 then (values 65)⁻¹ else 0

theorem source328_not_determinant (slot : Fin 18) :
    determinantSourceIndex slot ≠ 328 := by
  fin_cases slot <;> simp [determinantSourceIndex]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- The source row behind the four-row certificate has a useful structural
form: in chart 3, live `w_01_11` forces `w_34_12` to vanish as soon as
`w_12_10` vanishes. -/
theorem w34_12_zero_of_chart3_w12_10_zero_w01_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h12_10 : values 27 = 0) (h01 : values 1 ≠ 0) : values 65 = 0 := by
  rcases chart with ⟨_h23, _h12, h13_11⟩
  have source328 : sourceValue values 328 = 0 :=
    base 328 (source328_not_determinant)
  have identity : sourceValue values 328 = values 1 * values 65 := by
    simp [sourceValue, Krenn.FrozenCase0System.equations,
      SparsePoly.toPoly, SparseTerm.toPoly, h12_10, h13_11]
  rw [identity] at source328
  exact (mul_eq_zero.mp source328).resolve_left h01

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Four canonical rows force the downstream `w_34` entries to vanish in
the B1 geometry. This is a source-level propagation lemma, not a claim
about the external split tree. -/
theorem w34_tail_zero_of_chart3_w12_10_w13_12_zero_w01_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h12_10 : values 27 = 0) (h13_12 : values 37 = 0)
    (h01 : values 1 ≠ 0) :
    values 65 = 0 /\ values 66 = 0 /\ values 67 = 0 /\ values 68 = 0 := by
  rcases chart with ⟨_h23, _h12, h13_11⟩
  have source162 : sourceValue values 162 = 0 :=
    base 162 (by
      intro slot
      fin_cases slot <;> simp [determinantSourceIndex])
  have source163 : sourceValue values 163 = 0 :=
    base 163 (by
      intro slot
      fin_cases slot <;> simp [determinantSourceIndex])
  have source329 : sourceValue values 329 = 0 :=
    base 329 (by
      intro slot
      fin_cases slot <;> simp [determinantSourceIndex])
  have h34_12 : values 65 = 0 :=
    w34_12_zero_of_chart3_w12_10_zero_w01_live values base
      ⟨_h23, _h12, h13_11⟩ h12_10 h01
  have h34_20 : values 66 = 0 := by
    have identity : sourceValue values 329 = values 1 * values 66 := by
      simp [sourceValue, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12_10, h13_12]
    rw [identity] at source329
    exact (mul_eq_zero.mp source329).resolve_left h01
  have h34_21 : values 67 = 0 := by
    have identity : sourceValue values 162 = values 1 * values 67 := by
      simp [sourceValue, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12_10, h13_12]
    rw [identity] at source162
    exact (mul_eq_zero.mp source162).resolve_left h01
  have h34_22 : values 68 = 0 := by
    have identity : sourceValue values 163 = values 1 * values 68 := by
      simp [sourceValue, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12_10, h13_12]
    rw [identity] at source163
    exact (mul_eq_zero.mp source163).resolve_left h01
  exact ⟨h34_12, h34_20, h34_21, h34_22⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem selected_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h12_10 : values 27 = 0) (h01 : values 1 ≠ 0)
    (h34_12 : values 65 ≠ 0) :
    forall index : Fin 4,
      eval₂Hom (Int.castRingHom R) (leafValues values)
        (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveCertificate.selectedEquations index).toPoly = 0 := by
  have source328 : sourceValue values 328 = 0 :=
    base 328 (source328_not_determinant)
  intro index
  fin_cases index
  · rcases chart with ⟨_h23, _h12, h13_11⟩
    have selected_eq_source :
        eval₂Hom (Int.castRingHom R) (leafValues values)
          (Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveCertificate.selectedEquations 0).toPoly =
            sourceValue values 328 := by
      simp [leafValues,
        Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveCertificate.selectedEquations,
        sourceValue, Krenn.FrozenCase0System.equations,
        SparsePoly.toPoly, SparseTerm.toPoly, h12_10, h13_11]
    simpa using selected_eq_source.trans source328
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, h12_10]
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ h01]
  · simp [leafValues,
      Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveCertificate.selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly, mul_inv_cancel₀ h34_12]

/-- In B1, a live `w_34_12` is already impossible over every
characteristic-zero field.  No assumption on the other two `w_34` entries
is needed. -/
theorem refutes_chart3_b1_w34_12_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h12_10 : values 27 = 0) (h01 : values 1 ≠ 0)
    (h34_12 : values 65 ≠ 0) : False := by
  apply Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveCertificate.selectedHasNoCommonZero
    (leafValues values)
  exact selected_zero values base chart h12_10 h01 h34_12

#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveBridge.w34_12_zero_of_chart3_w12_10_zero_w01_live
#print axioms
  Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveBridge.refutes_chart3_b1_w34_12_live

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W34_12LiveBridge
