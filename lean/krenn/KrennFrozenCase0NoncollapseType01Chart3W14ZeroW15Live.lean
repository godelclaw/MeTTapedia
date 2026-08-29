import KrennFrozenCase0NoncollapseType01Chart3W14ZeroPropagation

/-!
A structural closure shared by several strict leaves of the type-01,
chart-3, both-pivots-live branch.

When `w_14_11 = 0` while `w_15_11` is live, the canonical propagation
through row 709 makes `w_03_00` vanish.  Canonical row 502 then forces
`w_12_12` to vanish.  Thus any descendant which also declares
`w_12_12` live is impossible without replaying an external certificate.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3W14ZeroW15Live

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3
open Krenn.FrozenCase0NoncollapseType01Chart3W14ZeroPropagation

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sourceIndex : Fin 1 -> Fin 747 := ![502]

theorem source_not_determinant
    (index : Fin 1) (slot : Fin 18) :
    determinantSourceIndex slot ≠ sourceIndex index := by
  fin_cases index
  fin_cases slot <;> simp [determinantSourceIndex, sourceIndex]

/-- In the both-pivots-live chart, the `w_14_11 = 0`, `w_15_11 ≠ 0`
subchart forces `w_12_12 = 0` directly from canonical rows 709 and 502. -/
theorem w12_12_zero_of_w14_zero_w15_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (h14 : values 42 = 0) (h15 : values 45 ≠ 0) :
    values 29 = 0 := by
  have h13_10 : values 35 = 0 :=
    w13_10_zero_of_both_opposite_pivots_live
      values base hdet chart h24 h25
  have h03_00 : values 6 = 0 :=
    w03_00_zero_of_w14_zero_w13_10_zero_w15_w24_live
      values base chart h14 h13_10 h15 h24
  have source : sourceValue values (sourceIndex 0) = 0 :=
    base (sourceIndex 0) (source_not_determinant 0)
  have identity : sourceValue values (sourceIndex 0) = values 29 := by
    simp [sourceValue, sourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h03_00, h14, h13_10]
  rw [identity] at source
  exact source

/-- A named contradiction form for the strict descendants that declare
`w_12_12` live. -/
theorem refutes_w14_zero_w15_live_w12_12_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart3 values)
    (h24 : values 51 ≠ 0) (h25 : values 56 ≠ 0)
    (h14 : values 42 = 0) (h15 : values 45 ≠ 0)
    (h12_12 : values 29 ≠ 0) : False := by
  exact h12_12 (w12_12_zero_of_w14_zero_w15_live
    values base hdet chart h24 h25 h14 h15)

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3W14ZeroW15Live.w12_12_zero_of_w14_zero_w15_live
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3W14ZeroW15Live.refutes_w14_zero_w15_live_w12_12_live

end Krenn.FrozenCase0NoncollapseType01Chart3W14ZeroW15Live
