import KrennFrozenCase0NoncollapseType01Chart3BothLive

/-!
A direct canonical closure inside the sum-zero side of type-01 pivot chart 3.

The terminal certificate found by the external tree uses a transformed row
which traces back to canonical amplitude row 745.  After the three Chart-3
pivots and the three displayed branch coordinates vanish, that row is simply
`-1 = 0`.  This file proves the stronger statement directly from the frozen
canonical system, so it does not depend on a solver lift or on the temporary
pivot-sum substitution.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0NoncollapseType01Pivot
open Krenn.FrozenCase0NoncollapseType01Chart3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Canonical amplitude row 745 is not one of the eighteen omitted
all-collapse determinant rows. -/
theorem source745_not_determinant (slot : Fin 18) :
    determinantSourceIndex slot ≠ (745 : Fin 747) := by
  fin_cases slot <;> simp [determinantSourceIndex]

/-- The chart-3 specialization of canonical amplitude row 745. -/
theorem source745_chart3_identity
    {R : Type*} [CommRing R]
    (values : Fin 75 -> R) (chart : PivotChart3 values) :
    sourceValue values 745 =
        values 1 * values 51 * values 70 +
        values 1 * values 56 * values 64 +
        values 4 * values 42 * values 70 +
        values 4 * values 45 * values 64 +
        values 7 * values 42 * values 56 +
        values 7 * values 45 * values 51 - 1 := by
  rcases chart with ⟨h23, h12, h13⟩
  simp [sourceValue, Krenn.FrozenCase0System.equations,
    Krenn.SparseCertificate.SparsePoly.toPoly,
    Krenn.SparseCertificate.SparseTerm.toPoly, h23, h12, h13]
  ring

/-- The branch in which `w_01_11`, `w_14_11`, and `w_15_11` vanish is
already contradictory in pivot chart 3.  In particular this closes the
matching sum-zero terminal leaf without using its external certificate. -/
theorem refutes_chart3_w01_w14_w15_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values)
    (h01 : values 1 = 0) (h14 : values 42 = 0) (h15 : values 45 = 0) :
    False := by
  have source : sourceValue values 745 = 0 :=
    base 745 source745_not_determinant
  rw [source745_chart3_identity values chart, h01, h14, h15] at source
  norm_num at source

/-- Consequently the three coordinates used by this terminal split cannot
all vanish in pivot chart 3.  This is the explicit structural cover replacing
the all-zero leaf of the external sum-zero tree. -/
theorem some_w01_w14_w15_nonzero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 -> R) (base : BaseCommonZero values)
    (chart : PivotChart3 values) :
    values 1 ≠ 0 ∨ values 42 ≠ 0 ∨ values 45 ≠ 0 := by
  by_cases h01 : values 1 = 0
  · by_cases h14 : values 42 = 0
    · by_cases h15 : values 45 = 0
      · exact (refutes_chart3_w01_w14_w15_zero values base chart h01 h14 h15).elim
      · exact Or.inr (Or.inr h15)
    · exact Or.inr (Or.inl h14)
  · exact Or.inl h01

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect.source745_chart3_identity
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect.refutes_chart3_w01_w14_w15_zero
#print axioms Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect.some_w01_w14_w15_nonzero

end Krenn.FrozenCase0NoncollapseType01Chart3SumzeroDirect
