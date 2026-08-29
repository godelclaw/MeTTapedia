import KrennFrozenCase0NoncollapseType01Chart3

/-!
Repeated canonical zero propagation on the type-01, chart-3 branch with
`w_14_11 = 0`.

These are the three elementary consequences that recur in the strict
sum-zero closure traces.  They are stated separately so later branch proofs
can use them without replaying the same sparse-row reductions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3W14ZeroPropagation

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sourceIndex : Fin 3 -> Fin 747 := ![709, 714, 362]

theorem source_not_determinant
    (index : Fin 3) (slot : Fin 18) :
    determinantSourceIndex slot ≠ sourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, sourceIndex]

/-- Canonical row 709 forces `w_03_00 = 0` when its three surviving
factors are live. -/
theorem w03_00_zero_of_w14_zero_w13_10_zero_w15_w24_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h14 : values 42 = 0) (h13_10 : values 35 = 0)
    (h15 : values 45 ≠ 0) (h24 : values 51 ≠ 0) :
    values 6 = 0 := by
  rcases chart with ⟨_h23, h12, _h13⟩
  have source : sourceValue values (sourceIndex 0) = 0 :=
    base (sourceIndex 0) (source_not_determinant 0)
  have identity : sourceValue values (sourceIndex 0) =
      values 6 * values 45 * values 51 := by
    simp [sourceValue, sourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h12, h14, h13_10]
  rw [identity] at source
  have h : values 6 * values 45 = 0 :=
    (mul_eq_zero.mp source).resolve_right h24
  exact (mul_eq_zero.mp h).resolve_right h15

/-- Canonical row 714 forces `w_03_22 = 0` in the corresponding live-factor
subchart. -/
theorem w03_22_zero_of_w14_zero_w13_12_zero_w15_w24_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h14 : values 42 = 0) (h13_12 : values 37 = 0)
    (h15 : values 45 ≠ 0) (h24 : values 51 ≠ 0) :
    values 8 = 0 := by
  rcases chart with ⟨_h23, h12, _h13⟩
  have source : sourceValue values (sourceIndex 1) = 0 :=
    base (sourceIndex 1) (source_not_determinant 1)
  have identity : sourceValue values (sourceIndex 1) =
      values 8 * values 45 * values 51 := by
    simp [sourceValue, sourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h12, h14, h13_12]
  rw [identity] at source
  have h : values 8 * values 45 = 0 :=
    (mul_eq_zero.mp source).resolve_right h24
  exact (mul_eq_zero.mp h).resolve_right h15

/-- Canonical row 362 forces `w_23_22 = 0` without using an external
certificate. -/
theorem w23_22_zero_of_w14_zero_w12_12_w13_12_zero_w15_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (h14 : values 42 = 0) (h12_12 : values 29 = 0)
    (h13_12 : values 37 = 0) (h15 : values 45 ≠ 0) :
    values 49 = 0 := by
  have source : sourceValue values (sourceIndex 2) = 0 :=
    base (sourceIndex 2) (source_not_determinant 2)
  have identity : sourceValue values (sourceIndex 2) =
      values 45 * values 49 := by
    simp [sourceValue, sourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h12_12, h13_12, h14]
  rw [identity] at source
  exact (mul_eq_zero.mp source).resolve_left h15

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3W14ZeroPropagation.w03_00_zero_of_w14_zero_w13_10_zero_w15_w24_live
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3W14ZeroPropagation.w03_22_zero_of_w14_zero_w13_12_zero_w15_w24_live
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3W14ZeroPropagation.w23_22_zero_of_w14_zero_w12_12_w13_12_zero_w15_live

end Krenn.FrozenCase0NoncollapseType01Chart3W14ZeroPropagation
