import Mettapedia.UniversalAI.UniversalHyperprior.DyadicRealization

/-!
# Dyadic division: exponent-shift and rounding controls

The former exponent-subtraction algorithm is retained only as a regression
fixture.  Its inexactness alone would be consistent with approximate division;
the quarter-divisor control establishes the stronger failure of a unit error
bound at precision zero.  The fixed-grid implementation has a general error
theorem in `DyadicValue.div_error`.

The positive controls below independently compare the repaired integer code
with real division.  They cover formerly truncated exponent shifts, a negative
dividend rounded down, and inputs with nontrivial denominators.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.UniversalHyperprior.Dyadic.DivisionControls

open DyadicValue

/-- The old algorithm, confined to regression controls.  Natural subtraction
can discard a negative shift instead of moving its power into the numerator. -/
def truncatedShiftDivision (a b : DyadicValue) (precision : ℕ) : DyadicValue :=
  let num_shifted := a.num * (2 ^ precision : ℤ)
  let result_num := num_shifted / b.num
  ⟨result_num, a.denom_pow + precision - b.denom_pow⟩

/-- Natural subtraction drops the entire denominator shift at precision zero. -/
theorem truncated_shift_reciprocal_power (power : ℕ) :
    (truncatedShiftDivision one ⟨1, power⟩ 0).toReal = 1 := by
  simp [truncatedShiftDivision, one, toReal]

/-- The independently specified real reciprocal retains that exponent. -/
theorem real_reciprocal_power (power : ℕ) :
    one.toReal / (⟨1, power⟩ : DyadicValue).toReal = (2 : ℝ) ^ power := by
  simp [one, toReal]

/-- A nonzero representable divisor did not ensure an exact old result. -/
theorem truncated_shift_half_mismatch :
    (truncatedShiftDivision one ⟨1, 1⟩ 0).toReal = 1 ∧
      one.toReal / (⟨1, 1⟩ : DyadicValue).toReal = 2 ∧
      (truncatedShiftDivision one ⟨1, 1⟩ 0).toReal ≠
        one.toReal / (⟨1, 1⟩ : DyadicValue).toReal := by
  norm_num [truncatedShiftDivision, one, toReal]

/-- The old discrepancy exceeded `2 ^ (-precision)` at precision zero. -/
theorem truncated_shift_quarter_error :
    |(truncatedShiftDivision one ⟨1, 2⟩ 0).toReal -
        one.toReal / (⟨1, 2⟩ : DyadicValue).toReal| = 3 ∧
      1 < |(truncatedShiftDivision one ⟨1, 2⟩ 0).toReal -
        one.toReal / (⟨1, 2⟩ : DyadicValue).toReal| := by
  norm_num [truncatedShiftDivision, one, toReal]

/-- The repaired half reciprocal is exact even at precision zero. -/
theorem div_reciprocal_half_exact :
    (div one ⟨1, 1⟩ 0).toReal = 2 ∧
      (div one ⟨1, 1⟩ 0).toReal =
        one.toReal / (⟨1, 1⟩ : DyadicValue).toReal := by
  norm_num [div, one, toReal]

/-- The repaired quarter reciprocal also retains the numerator shift. -/
theorem div_reciprocal_quarter_exact :
    (div one ⟨1, 2⟩ 0).toReal = 4 ∧
      (div one ⟨1, 2⟩ 0).toReal =
        one.toReal / (⟨1, 2⟩ : DyadicValue).toReal := by
  norm_num [div, one, toReal]

/-- Negative numerators use Euclidean floor, rather than truncation toward zero. -/
theorem div_negative_numerator_floors :
    (div ⟨-1, 0⟩ ⟨3, 0⟩ 2).num = -2 ∧
      (div ⟨-1, 0⟩ ⟨3, 0⟩ 2).toReal = -1 / 2 ∧
      (⟨-1, 0⟩ : DyadicValue).toReal / (⟨3, 0⟩ : DyadicValue).toReal -
        (div ⟨-1, 0⟩ ⟨3, 0⟩ 2).toReal = 1 / 6 := by
  norm_num [div, toReal]

/-- Negative divisors reverse the directed error, for either dividend sign. -/
theorem div_negative_divisor :
    (div ⟨1, 0⟩ ⟨-3, 0⟩ 2).toReal = -1 / 4 ∧
      (⟨1, 0⟩ : DyadicValue).toReal / (⟨-3, 0⟩ : DyadicValue).toReal -
        (div ⟨1, 0⟩ ⟨-3, 0⟩ 2).toReal = -1 / 12 ∧
      (div ⟨-1, 0⟩ ⟨-3, 0⟩ 2).toReal = 1 / 2 ∧
      |(⟨-1, 0⟩ : DyadicValue).toReal / (⟨-3, 0⟩ : DyadicValue).toReal -
        (div ⟨-1, 0⟩ ⟨-3, 0⟩ 2).toReal| < 1 / 4 := by
  norm_num [div, toReal]

/-- The fixed grid may be coarser than the exact quotient; increasing precision
then recovers it, with both input denominator exponents nonzero. -/
theorem div_shifted_denominators :
    (div ⟨1, 3⟩ ⟨1, 1⟩ 1).toReal = 0 ∧
      (⟨1, 3⟩ : DyadicValue).toReal / (⟨1, 1⟩ : DyadicValue).toReal = 1 / 4 ∧
      (div ⟨1, 3⟩ ⟨1, 1⟩ 2).toReal =
        (⟨1, 3⟩ : DyadicValue).toReal / (⟨1, 1⟩ : DyadicValue).toReal := by
  norm_num [div, toReal]

end Mettapedia.UniversalAI.UniversalHyperprior.Dyadic.DivisionControls
