import KrennFrozenCase0NoncollapseType01Chart3

/-!
Reusable canonical zero propagation for the type-01, chart-3 non-collapse
branch.

The finite certificate tree repeatedly derives the same two consequences from
canonical rows 644 and 488.  This module records that implication once,
directly against the frozen case-0 equations.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3CanonicalPropagation

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sourceIndex : Fin 2 -> Fin 747 := ![644, 488]

theorem source_not_determinant
    (index : Fin 2) (slot : Fin 18) :
    determinantSourceIndex slot ≠ sourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, sourceIndex]

/-- In chart 3, live `w_15_11` turns the two canonical amplitude rows into
the simultaneous channel vanishing `w_02_11 = w_02_22 = 0`.  No pivot-sum
condition or external certificate is used. -/
theorem w02_channel_ends_zero_of_w01_w12_12_zero_w15_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (h01 : values 1 = 0) (h12_12 : values 29 = 0)
    (h15 : values 45 ≠ 0) :
    values 4 = 0 ∧ values 5 = 0 := by
  rcases chart with ⟨h23, h12, h13⟩
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live
      values base hdet ⟨h23, h12, h13⟩ h24 h25

  have source644 : sourceValue values (sourceIndex 0) = 0 :=
    base (sourceIndex 0) (source_not_determinant 0)
  have h02_11 : values 4 = 0 := by
    have identity : sourceValue values (sourceIndex 0) = values 4 * values 45 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h01, h13_10, h12]
    rw [identity] at source644
    exact (mul_eq_zero.mp source644).resolve_right h15

  have source488 : sourceValue values (sourceIndex 1) = 0 :=
    base (sourceIndex 1) (source_not_determinant 1)
  have h02_22 : values 5 = 0 := by
    have identity : sourceValue values (sourceIndex 1) = values 5 * values 45 := by
      simp [sourceValue, sourceIndex,
        Krenn.FrozenCase0System.equations,
        Krenn.SparseCertificate.SparsePoly.toPoly,
        Krenn.SparseCertificate.SparseTerm.toPoly,
        h13_10, h12_12]
    rw [identity] at source488
    exact (mul_eq_zero.mp source488).resolve_right h15

  exact ⟨h02_11, h02_22⟩

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3CanonicalPropagation.w02_channel_ends_zero_of_w01_w12_12_zero_w15_live

end Krenn.FrozenCase0NoncollapseType01Chart3CanonicalPropagation
