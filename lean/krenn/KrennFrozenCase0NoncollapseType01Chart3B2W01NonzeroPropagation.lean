import KrennFrozenCase0NoncollapseType01Chart3

/-!
Source-level replacement for the monomial-zero closure after the chart-3
`b2` branch chooses `w_01_11` nonzero.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B2W01NonzeroPropagation

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sourceIndex : Fin 5 → Fin 747 := ![328, 329, 162, 163, 325]

theorem source_not_determinant
    (index : Fin 5) (slot : Fin 18) :
    determinantSourceIndex slot ≠ sourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, sourceIndex]

/-- The five zeroes reached by the external `b2/w01!=0` closure are direct
canonical amplitude consequences. -/
theorem b2_w01_nonzero_closure_zeros
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (h13_12 : values 37 = 0) (h12_10 : values 27 = 0)
    (h01 : values 1 ≠ 0) :
    values 65 = 0 ∧ values 66 = 0 ∧ values 67 = 0 ∧
      values 68 = 0 ∧ values 57 = 0 := by
  rcases chart with ⟨h23, h12, h13⟩
  have chart' : PivotChart3 values := ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live
      values base hdet chart' h24 h25
  have source0 : sourceValue values (sourceIndex 0) = 0 :=
    base (sourceIndex 0) (source_not_determinant 0)
  have source1 : sourceValue values (sourceIndex 1) = 0 :=
    base (sourceIndex 1) (source_not_determinant 1)
  have source2 : sourceValue values (sourceIndex 2) = 0 :=
    base (sourceIndex 2) (source_not_determinant 2)
  have source3 : sourceValue values (sourceIndex 3) = 0 :=
    base (sourceIndex 3) (source_not_determinant 3)
  have source4 : sourceValue values (sourceIndex 4) = 0 :=
    base (sourceIndex 4) (source_not_determinant 4)
  have h34_12 : values 65 = 0 := by
    have identity : sourceValue values (sourceIndex 0) = values 1 * values 65 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h12_10, h13]
    rw [identity] at source0
    exact (mul_eq_zero.mp source0).resolve_left h01
  have h34_20 : values 66 = 0 := by
    have identity : sourceValue values (sourceIndex 1) = values 1 * values 66 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h13_12, h12_10]
    rw [identity] at source1
    exact (mul_eq_zero.mp source1).resolve_left h01
  have h34_21 : values 67 = 0 := by
    have identity : sourceValue values (sourceIndex 2) = values 1 * values 67 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h13_12, h12_10]
    rw [identity] at source2
    exact (mul_eq_zero.mp source2).resolve_left h01
  have h34_22 : values 68 = 0 := by
    have identity : sourceValue values (sourceIndex 3) = values 1 * values 68 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h13_12, h12_10]
    rw [identity] at source3
    exact (mul_eq_zero.mp source3).resolve_left h01
  have h25_12 : values 57 = 0 := by
    have identity : sourceValue values (sourceIndex 4) = values 1 * values 57 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly, h12, h13_10]
    rw [identity] at source4
    exact (mul_eq_zero.mp source4).resolve_left h01
  exact ⟨h34_12, h34_20, h34_21, h34_22, h25_12⟩

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B2W01NonzeroPropagation.b2_w01_nonzero_closure_zeros

end Krenn.FrozenCase0NoncollapseType01Chart3B2W01NonzeroPropagation
