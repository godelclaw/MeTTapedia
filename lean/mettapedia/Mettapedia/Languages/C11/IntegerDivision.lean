import Mathlib.Data.Int.ModEq
import Lean.Elab.Tactic.Omega

/-!
# Truncating C11 integer division and remainder

N1570 6.5.5 discards the fractional part toward zero. The declarative relation
states the decomposition and a remainder smaller than the divisor's magnitude,
with the dividend's sign. The executable operation uses Lean's truncating
division rather than Euclidean division. Both directions hold for arbitrary
integers. Target-type representability, including minimum signed value divided
by minus one, is a separate arithmetic check shared by division and remainder.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11

structure IntegerDivision (dividend divisor quotient remainder : Int) : Prop where
  nonzero : divisor ≠ 0
  decomposition : remainder + divisor * quotient = dividend
  nonnegative : 0 ≤ dividend → 0 ≤ remainder ∧ remainder < (divisor.natAbs : Int)
  nonpositive : dividend ≤ 0 → -(divisor.natAbs : Int) < remainder ∧ remainder ≤ 0

def divideIntegers (dividend divisor : Int) : Option (Int × Int) :=
  if divisor = 0 then none else some (dividend.tdiv divisor, dividend.tmod divisor)

theorem divideIntegers_sound (dividend divisor quotient remainder : Int)
    (computed : divideIntegers dividend divisor = some (quotient, remainder)) :
    IntegerDivision dividend divisor quotient remainder := by
  unfold divideIntegers at computed
  split at computed
  · cases computed
  · rename_i nonzero
    have values := Option.some.inj computed
    have quotientEqual : dividend.tdiv divisor = quotient := congrArg Prod.fst values
    have remainderEqual : dividend.tmod divisor = remainder := congrArg Prod.snd values
    rw [← quotientEqual, ← remainderEqual]
    refine ⟨nonzero, Int.tmod_add_mul_tdiv dividend divisor, ?_, ?_⟩
    · intro nonnegative
      exact ((Int.tdiv_tmod_unique nonnegative nonzero).mp ⟨rfl, rfl⟩).2
    · intro nonpositive
      exact ((Int.tdiv_tmod_unique' nonpositive nonzero).mp ⟨rfl, rfl⟩).2

theorem divideIntegers_complete (dividend divisor quotient remainder : Int)
    (division : IntegerDivision dividend divisor quotient remainder) :
    divideIntegers dividend divisor = some (quotient, remainder) := by
  have values : dividend.tdiv divisor = quotient ∧ dividend.tmod divisor = remainder := by
    by_cases nonnegative : 0 ≤ dividend
    · exact (Int.tdiv_tmod_unique nonnegative division.nonzero).mpr
        ⟨division.decomposition, division.nonnegative nonnegative⟩
    · have nonpositive : dividend ≤ 0 := by omega
      exact (Int.tdiv_tmod_unique' nonpositive division.nonzero).mpr
        ⟨division.decomposition, division.nonpositive nonpositive⟩
  simp only [divideIntegers, if_neg division.nonzero, values.1, values.2]

theorem divideIntegers_iff (dividend divisor quotient remainder : Int) :
    divideIntegers dividend divisor = some (quotient, remainder) ↔
      IntegerDivision dividend divisor quotient remainder :=
  ⟨divideIntegers_sound dividend divisor quotient remainder,
    divideIntegers_complete dividend divisor quotient remainder⟩

theorem divideIntegers_none_iff (dividend divisor : Int) :
    divideIntegers dividend divisor = none ↔ divisor = 0 := by
  simp [divideIntegers]

end Mettapedia.Languages.C11
