import Mettapedia.GSLT.LanguageDef.IndexedInductiveVectorArray

/-!
# Actual array inputs under natural-only checking

These controls retain duplicate and ordered payloads, check the canonical
output at its arithmetic index, and refuse malformed values. Vector iota
citations remain unauthorized even though vector values are well-typed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendTyping.Selected.Controls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies Declaration.IndexedFamily
open VectorMeaning

theorem natural_element : Typed .nil natTm (sortTm elementLevel) := by
  apply FormationSensitive.Typing.cumul (constructors.nat_formed .nil)
  change ∀ valuation : Nat → Nat, 0 ≤ valuation 0
  exact fun _ => Nat.zero_le _

theorem payload_typed (value : Nat) : Typed .nil (numeral value) natTm :=
  constructors.numeral_typed .nil value

def left : Array Nat := #[2, 1, 2]
def right : Array Nat := #[0]

abbrev policy := Programs.ComputationProfiles.naturalOnly
abbrev decoder := Programs.ComputationProfiles.decoder policy

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def checks (term type : Tower.Tm 0) : Bool :=
  (FormationSensitiveElaboration.elaborate rules decoder Programs.choices
    24 .nil term type).isSome

def resultType : Tower.Tm 0 := vecApp natTm (Programs.add (numeral left.size) (numeral right.size))

def verdicts : List (String × Bool) := [
  ("six constructors check with natural-only authority", (List.finRange 6).all fun i => (submission i).isSome),
  ("represented left input", checks (VectorArray.quoteArray natTm numeral left) (vecApp natTm (numeral 3))),
  ("represented right input", checks (VectorArray.quoteArray natTm numeral right) (vecApp natTm (numeral 1))),
  ("canonical result at original arithmetic index", checks (VectorArray.quoteArray natTm numeral (left ++ right)) resultType),
  ("ordered duplicate payloads retained", left ++ right == #[2, 1, 2, 0]),
  ("missing duplicate differs", VectorArray.quoteArray natTm numeral (left ++ right) !=
    VectorArray.quoteArray natTm numeral #[2, 1, 0]),
  ("reordering differs", VectorArray.quoteArray natTm numeral (left ++ right) !=
    VectorArray.quoteArray natTm numeral #[2, 2, 1, 0]),
  ("wrong dependent length refuses", !checks (VectorArray.quoteArray natTm numeral left) (vecApp natTm (numeral 2))),
  ("undeclared payload refuses", !checks (vconsApp natTm zeroTm (.const `MissingPayload) (vnilApp natTm))
    (vecApp natTm (numeral 1))),
  ("type used as value refuses", !checks (vconsApp natTm zeroTm natTm (vnilApp natTm)) (vecApp natTm (numeral 1))),
  ("wrong tail index refuses", !checks (vconsApp natTm (numeral 1) zeroTm (vnilApp natTm)) (vecApp natTm (numeral 2))),
  ("vector nil citation still refused", (decoder.decode Programs.ComputationProfiles.vectorNilCode).isNone)]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

/-- The actual textual function and nonempty arrays instantiate all three
parts: selected input typing, original execution and selected result typing. -/
theorem nonempty_contract :
    FormationSensitive.Judgment rules .nil
      (applyArgs Programs.appendTerm [natTm, numeral left.size, numeral right.size,
        VectorArray.quoteArray natTm numeral left, VectorArray.quoteArray natTm numeral right]) resultType ∧
    AppendMeaning.ProgramExecutes
      (applyArgs Programs.appendTerm [natTm, numeral left.size, numeral right.size,
        VectorArray.quoteArray natTm numeral left, VectorArray.quoteArray natTm numeral right])
      (VectorArray.quoteArray natTm numeral (left ++ right)) ∧
    FormationSensitive.Judgment rules .nil (VectorArray.quoteArray natTm numeral (left ++ right)) resultType :=
  VectorArray.compiled_selected_contract _ AppendSource.append_matches_reference
    natTm numeral natural_element payload_typed left right

#print axioms all_verdicts
#print axioms nonempty_contract

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendTyping.Selected.Controls
