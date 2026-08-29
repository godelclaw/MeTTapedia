import KrennFrozenCase0NoncollapseType01Chart3

/-!
The first semantic zero-propagation used by the chart-3 `b2n1` closure.

The external closure trace records `w_03_22 = 0` from a live `w_14_11`.
Here the implication is recovered directly from canonical row 532, so the
closure does not remain an unproved preprocessing step.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B2N1Propagation

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sourceIndex : Fin 747 := 532

theorem source_not_determinant (slot : Fin 18) :
    determinantSourceIndex slot ≠ sourceIndex := by
  fin_cases slot <;> simp [determinantSourceIndex, sourceIndex]

/-- In the `b2n1` geometry, canonical row 532 reduces to
`w_03_22 * w_14_11`; hence live `w_14_11` forces `w_03_22 = 0`. -/
theorem w03_22_zero_of_b2n1_w14_live
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (h13_12 : values 37 = 0) (h12_10 : values 27 = 0)
    (h14 : values 42 ≠ 0) : values 8 = 0 := by
  have source : sourceValue values sourceIndex = 0 :=
    base sourceIndex source_not_determinant
  have identity : sourceValue values sourceIndex = values 8 * values 42 := by
    simp [sourceValue, sourceIndex,
      Krenn.FrozenCase0System.equations,
      Krenn.SparseCertificate.SparsePoly.toPoly,
      Krenn.SparseCertificate.SparseTerm.toPoly,
      h13_12, h12_10]
  rw [identity] at source
  exact (mul_eq_zero.mp source).resolve_right h14

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B2N1Propagation.w03_22_zero_of_b2n1_w14_live

end Krenn.FrozenCase0NoncollapseType01Chart3B2N1Propagation
