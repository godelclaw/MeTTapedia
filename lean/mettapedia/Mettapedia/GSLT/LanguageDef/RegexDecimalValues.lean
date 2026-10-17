import Mettapedia.GSLT.LanguageDef.RegexSourceProjection
import Mettapedia.Data.String.UnicodeDecimal

/-!
# One Unicode decimal-value interpretation for counts and references

The scalar provider uses the same Unicode decimal block data as the regex
lexical profile and CST count projection. Every recognized value is proved
to be in `0..9`; the generic positional arithmetic therefore applies without
requiring adjacent digits to share a script or decimal block.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexDecimalValues

open Mettapedia.Data.String.UnicodeDecimal
open RegexSourceProjection (decimalDigit?)

theorem decimalDigit_bound (scalar value : Nat) (recognized : decimalDigit? scalar = some value) :
    value < 10 := by
  unfold decimalDigit? at recognized
  obtain ⟨first, found, same⟩ := Option.map_eq_some_iff.mp recognized
  have bounds := List.find?_some found
  simp only [decide_eq_true_eq] at bounds
  omega

def scalarValue? (scalar : Nat) : Option Digit :=
  match recognized : decimalDigit? scalar with
  | none => none
  | some value => some ⟨value, decimalDigit_bound scalar value recognized⟩

def characterValue? (character : Char) : Option Digit := scalarValue? character.toNat

theorem scalarValue_exact (scalar : Nat) :
    (scalarValue? scalar).map Fin.val = decimalDigit? scalar := by
  unfold scalarValue?
  split <;> rename_i recognized <;> simp [recognized]

/-- Forgetting only the finite-value proof recovers exactly the count
projector's actual scalar interpretation. -/
theorem characterValue_exact (character : Char) :
    (characterValue? character).map Fin.val = decimalDigit? character.toNat := scalarValue_exact _

theorem whole_decimal_value (source : List Char) (digits : List Digit)
    (nonempty : source ≠ []) (recognized : recognize characterValue? source = some digits) :
    parse characterValue? source = some (positionalValue digits) := by
  simp [parse, nonempty, recognized, accumulate_positional]

namespace Controls

theorem mixed_decimal_blocks_compose_by_value :
    parse characterValue? "١３".toList = some 13 ∧
    parse characterValue? "０1٣".toList = some 13 := by decide

theorem recently_added_decimal_block_is_ordinary_base_ten :
    (scalarValue? 124402).map Fin.val = some 1 ∧
    (scalarValue? 124410).map Fin.val = some 9 := by decide

theorem superscript_and_punctuation_are_not_decimal_digits :
    characterValue? '³' = none ∧ characterValue? '$' = none ∧ characterValue? '{' = none := by decide

end Controls

#print axioms decimalDigit_bound
#print axioms scalarValue_exact

end Mettapedia.GSLT.LanguageDef.RegexDecimalValues
