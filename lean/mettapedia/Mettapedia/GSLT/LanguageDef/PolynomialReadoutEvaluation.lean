import Mettapedia.GSLT.LanguageDef.PolynomialReadoutCalculus

/-!
# Value and operation account of a polynomial readout evaluator

This evaluator executes a readout tree in left-to-right order. It records
primitive query requests, additions and multiplications separately. Its value
agrees with the independent polynomial interpretation. Its operation account
belongs to this evaluator, not to an unqualified native implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PolynomialReadoutEvaluation

open Mettapedia.OSLF.MeTTaIL.Syntax
open PolynomialReadoutCalculus

structure Profile where
  requests : List Pattern
  additions : ℕ
  multiplications : ℕ
  deriving DecidableEq, Repr

structure Result (Value : Type*) where
  value : Value
  profile : Profile

variable {Value : Type*} [CommSemiring Value]

def run (query : Pattern → Value) : Pattern → Result Value
  | .apply "Read" [request] => ⟨query request, ⟨[request], 0, 0⟩⟩
  | .apply "Zero" [] => ⟨0, ⟨[], 0, 0⟩⟩
  | .apply "One" [] => ⟨1, ⟨[], 0, 0⟩⟩
  | .apply "Sum" [first, second] =>
      let left := run query first
      let right := run query second
      ⟨left.value + right.value,
        ⟨left.profile.requests ++ right.profile.requests,
          left.profile.additions + right.profile.additions + 1,
          left.profile.multiplications + right.profile.multiplications⟩⟩
  | .apply "Product" [first, second] =>
      let left := run query first
      let right := run query second
      ⟨left.value * right.value,
        ⟨left.profile.requests ++ right.profile.requests,
          left.profile.additions + right.profile.additions,
          left.profile.multiplications + right.profile.multiplications + 1⟩⟩
  | other => ⟨query other, ⟨[other], 0, 0⟩⟩
termination_by pattern => sizeOf pattern

/-- Execution's value is the independent free-semiring interpretation. -/
theorem run_value (query : Pattern → Value) (term : Pattern) :
    (run query term).value = MvPolynomial.eval₂ (Nat.castRingHom Value) query (polynomial term) := by
  fun_induction run query term <;>
    simp_all +zetaDelta [polynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul]

/-- Changing the primitive values preserves the request order and arithmetic
counts of this fixed tree evaluator. -/
theorem profile_independent {Other : Type*} [CommSemiring Other]
    (first : Pattern → Value) (second : Pattern → Other) (term : Pattern) :
    (run first term).profile = (run second term).profile := by
  fun_induction run first term <;> simp_all +zetaDelta [run]

end Mettapedia.GSLT.LanguageDef.PolynomialReadoutEvaluation
