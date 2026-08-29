import KrennFrozenCase0NoncollapseType01Chart3OnlyW24W03Zero
import KrennFrozenCase0NoncollapseType01Chart3OnlyW24W03Nonzero

/-!
The exhaustive assembly of the chart-3 branch where `w_24_11` is live
and `w_25_11` vanishes.  Canonical amplitude rows first force a small
zero pattern and the product `w_03_00 * w_45_11 = 0`; the two resulting
leaves are discharged by strict polynomial certificates replayed against
their original frozen systems.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def reductionSourceIndex : Fin 10 → Fin 747 :=
  ![302, 111, 131, 188, 135, 299, 158, 16, 26, 606]

theorem reduction_source_not_determinant (index : Fin 10)
    (slot : Fin 18) :
    determinantSourceIndex slot ≠ reductionSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, reductionSourceIndex]

theorem w05_21_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (h25 : values 56 = 0) (h24 : values 51 ≠ 0) :
    values 23 ≠ 0 := by
  have hGb : factorGb values ≠ 0 :=
    (noncollapse_factor_geometry values base hdet).2.1
  have hGbFormula : factorGb values = values 23 * values 51 := by
    simp [factorGb, slotDeterminant, slotA1, slotB1, slotA2, slotB2, h25]
  rw [hGbFormula] at hGb
  exact (mul_ne_zero_iff.mp hGb).1

theorem w13_10_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h25 : values 56 = 0) (h24 : values 51 ≠ 0)
    (h05_21 : values 23 ≠ 0) : values 35 = 0 := by
  rcases chart with ⟨_h23, h12, _h13⟩
  have source : sourceValue values (reductionSourceIndex 0) = 0 :=
    base (reductionSourceIndex 0) (reduction_source_not_determinant 0)
  have identity :
      sourceValue values (reductionSourceIndex 0) =
        values 35 * (values 23 * values 51) := by
    simp [sourceValue, reductionSourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly, h12, h25]
    ring
  rw [identity] at source
  exact (mul_eq_zero.mp source).resolve_right (mul_ne_zero h05_21 h24)

theorem w34_even_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (h25 : values 56 = 0) (h05_21 : values 23 ≠ 0) :
    values 61 = 0 ∧ values 62 = 0 ∧ values 66 = 0 ∧ values 68 = 0 := by
  have source0 : sourceValue values (reductionSourceIndex 1) = 0 :=
    base (reductionSourceIndex 1) (reduction_source_not_determinant 1)
  have source1 : sourceValue values (reductionSourceIndex 2) = 0 :=
    base (reductionSourceIndex 2) (reduction_source_not_determinant 2)
  have source2 : sourceValue values (reductionSourceIndex 3) = 0 :=
    base (reductionSourceIndex 3) (reduction_source_not_determinant 3)
  have source3 : sourceValue values (reductionSourceIndex 4) = 0 :=
    base (reductionSourceIndex 4) (reduction_source_not_determinant 4)
  have h0 : values 61 = 0 := by
    have identity : sourceValue values (reductionSourceIndex 1) =
        values 23 * values 61 := by
      simp [sourceValue, reductionSourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h25]
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_left h05_21
  have h1 : values 62 = 0 := by
    have identity : sourceValue values (reductionSourceIndex 2) =
        values 23 * values 62 := by
      simp [sourceValue, reductionSourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h25]
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_left h05_21
  have h2 : values 66 = 0 := by
    simpa [sourceValue, reductionSourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly, h25] using source2
  have h3 : values 68 = 0 := by
    have identity : sourceValue values (reductionSourceIndex 4) =
        values 23 * values 68 := by
      simp [sourceValue, reductionSourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h25]
    rw [identity] at source3
    exact (mul_eq_zero.mp source3).resolve_left h05_21
  exact ⟨h0, h1, h2, h3⟩

theorem w13_00_relation
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (h25 : values 56 = 0) (h05_21 : values 23 ≠ 0) :
    values 33 * values 51 + 1 = 0 := by
  have source : sourceValue values (reductionSourceIndex 5) = 0 :=
    base (reductionSourceIndex 5) (reduction_source_not_determinant 5)
  have identity : sourceValue values (reductionSourceIndex 5) =
      values 23 * (values 33 * values 51 + 1) := by
    simp [sourceValue, reductionSourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly, h25]
    ring
  rw [identity] at source
  exact (mul_eq_zero.mp source).resolve_left h05_21

theorem w13_00_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (relation : values 33 * values 51 + 1 = 0) :
    values 33 ≠ 0 := by
  intro h13
  rw [h13] at relation
  norm_num at relation

theorem w04_even_offdiagonal_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (h34_02 : values 62 = 0) (h13_00 : values 33 ≠ 0) :
    values 10 = 0 ∧ values 13 = 0 ∧ values 16 = 0 := by
  have source0 : sourceValue values (reductionSourceIndex 6) = 0 :=
    base (reductionSourceIndex 6) (reduction_source_not_determinant 6)
  have source1 : sourceValue values (reductionSourceIndex 7) = 0 :=
    base (reductionSourceIndex 7) (reduction_source_not_determinant 7)
  have source2 : sourceValue values (reductionSourceIndex 8) = 0 :=
    base (reductionSourceIndex 8) (reduction_source_not_determinant 8)
  simp [sourceValue, reductionSourceIndex,
    Krenn.FrozenCase0System.equations,
    Krenn.SparseCertificate.SparsePoly.toPoly,
    Krenn.SparseCertificate.SparseTerm.toPoly, h34_02] at source0 source1 source2
  exact ⟨source0.resolve_right h13_00, source1.resolve_right h13_00,
    source2.resolve_right h13_00⟩

theorem w03_00_mul_w45_11_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (h25 : values 56 = 0)
    (relation : values 33 * values 51 + 1 = 0) :
    values 6 * values 73 = 0 := by
  have source : sourceValue values (reductionSourceIndex 9) = 0 :=
    base (reductionSourceIndex 9) (reduction_source_not_determinant 9)
  have identity : sourceValue values (reductionSourceIndex 9) =
      values 6 * values 73 + (values 33 * values 51 + 1) := by
    simp [sourceValue, reductionSourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly, h25]
    ring
  rw [identity, relation] at source
  simpa using source

/-- The whole `w_24_11 ≠ 0, w_25_11 = 0` branch is impossible. -/
theorem refutes_slot1_chart3_only_w24
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 = 0) : False := by
  have h13_12 := w13_12_zero_of_w25_zero
    values base hdet chart h24 h25
  have h05_21 := w05_21_nonzero values base hdet h25 h24
  have h13_10 := w13_10_zero values base chart h25 h24 h05_21
  obtain ⟨h34_00, h34_02, h34_20, h34_22⟩ :=
    w34_even_zero values base h25 h05_21
  have relation := w13_00_relation values base h25 h05_21
  have h13_00 := w13_00_nonzero values relation
  obtain ⟨h04_02, h04_12, h04_22⟩ :=
    w04_even_offdiagonal_zero values base h34_02 h13_00
  have product := w03_00_mul_w45_11_zero values base h25 relation
  by_cases h03_00 : values 6 = 0
  · exact
      Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03Zero.refutes_slot1_chart3_only_w24_w03_zero
        values base hdet chart h25 h13_12 h13_10 h34_00 h34_02
          h34_20 h34_22 h04_02 h04_12 h04_22 h03_00 h24 h13_00
  · have h45_11 : values 73 = 0 :=
      (mul_eq_zero.mp product).resolve_left h03_00
    exact
      Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24W03Nonzero.refutes_slot1_chart3_only_w24_w03_nonzero
        values base hdet chart h25 h13_12 h13_10 h34_00 h34_02
          h34_20 h34_22 h04_02 h04_12 h04_22 h45_11 h24 h13_00 h03_00

#print axioms refutes_slot1_chart3_only_w24

end Krenn.FrozenCase0NoncollapseType01Chart3OnlyW24
