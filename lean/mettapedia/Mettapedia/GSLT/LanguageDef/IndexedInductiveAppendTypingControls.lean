import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendTyping

/-!
# Formed append inputs and information-preservation controls

Natural payloads instantiate the actual closed append function. The existing
checker refuses malformed representations and incorrect dependent indices.
A separate negative shows that payload typing alone does not imply faithful
encoding: a well-typed constant encoder identifies distinct source values.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendTypingControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies Declaration.IndexedFamily SchemaElaboration
open IndexedInductiveNatVec VectorMeaning AppendMeaning AppendTyping

/-- Naturals inhabit the chosen schematic element universe by its actual
cumulative order; the numeric representation does not change that policy. -/
theorem natural_element : Typed .nil natTm (sortTm elementLevel) := by
  apply FormationSensitive.Typing.cumul (nat_formed .nil)
  change ∀ valuation : Nat → Nat, 0 ≤ valuation 0
  exact fun _ => Nat.zero_le _

def payload (value : Bool) : Tower.Tm 0 := if value then succApp zeroTm else zeroTm

theorem payload_typed (value : Bool) : Typed .nil (payload value) natTm := by
  cases value
  · exact zero_typed .nil
  · exact succ_typed (zero_typed .nil)

theorem payload_injective : Function.Injective payload := by
  intro first second same
  cases first <;> cases second <;> simp_all [payload, succApp, zeroTm]

/-- A nonempty instance supplies both formation and execution evidence for
the exact program returned by the selected textual module. -/
theorem nonempty_typed_contract :
    FormationSensitive.Judgment Programs.rules .nil
      (applyArgs Programs.appendTerm [natTm, quoteIndex (Natural.succ Natural.zero),
        quoteIndex (Natural.succ Natural.zero),
        encodeVector natTm payload (Vectors.cons true Vectors.nil),
        encodeVector natTm payload (Vectors.cons false Vectors.nil)])
      (vecApp natTm (Programs.add (numeral 1) (numeral 1))) ∧
    ProgramExecutes (applyArgs Programs.appendTerm [natTm, quoteIndex (Natural.succ Natural.zero),
      quoteIndex (Natural.succ Natural.zero),
      encodeVector natTm payload (Vectors.cons true Vectors.nil),
      encodeVector natTm payload (Vectors.cons false Vectors.nil)])
      (encodeVector natTm payload
        (Vectors.append (Vectors.cons true Vectors.nil) (Vectors.cons false Vectors.nil))) ∧
    FormationSensitive.Judgment Programs.rules .nil
      (encodeVector natTm payload
        (Vectors.append (Vectors.cons true Vectors.nil) (Vectors.cons false Vectors.nil)))
      (vecApp natTm (Programs.add (numeral 1) (numeral 1))) :=
  compiled_contract _ AppendSource.append_matches_reference natTm payload natural_element payload_typed _ _

def collapsed (_ : Bool) : Tower.Tm 0 := zeroTm

theorem collapsed_typed (value : Bool) : Typed .nil (collapsed value) natTm := zero_typed .nil

/-- An actual information-loss example, despite well-typed payloads. -/
theorem typed_encoding_can_lose_information :
    (∀ value, Typed .nil (collapsed value) natTm) ∧
    (Vectors.cons true (Vectors.nil : Vectors.Vector Bool Natural.zero) ≠ Vectors.cons false Vectors.nil) ∧
    encodeVector natTm collapsed (Vectors.cons true Vectors.nil) =
      encodeVector natTm collapsed (Vectors.cons false Vectors.nil) := by
  refine ⟨collapsed_typed, ?_, rfl⟩
  intro same
  have lists := congrArg (fun value => (Vectors.toList value).val) same
  change [true] = [false] at lists
  cases lists

local instance : DecidableRel Programs.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred Programs.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (Programs.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel Programs.rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel Programs.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def checks (term type : Tower.Tm 0) : Bool :=
  (FormationSensitiveElaboration.elaborate Programs.rules Programs.decoder Programs.choices
    24 .nil term type).isSome

def singleton : Tower.Tm 0 := vconsApp natTm zeroTm (payload true) (vnilApp natTm)
def pair : Tower.Tm 0 := vconsApp natTm (numeral 1) (payload false) singleton

def verdicts : List (String × Bool) := [
  ("formed numeral", checks (numeral 2) natTm),
  ("formed empty vector", checks (vnilApp natTm) (vecApp natTm zeroTm)),
  ("formed singleton payload and length", checks singleton (vecApp natTm (numeral 1))),
  ("formed recursive vector", checks pair (vecApp natTm (numeral 2))),
  ("wrong singleton length refuses", !checks singleton (vecApp natTm zeroTm)),
  ("wrong recursive length refuses", !checks pair (vecApp natTm (numeral 1))),
  ("undeclared payload refuses", !checks
    (vconsApp natTm zeroTm (.const `MissingPayload) (vnilApp natTm)) (vecApp natTm (numeral 1))),
  ("type used as a numeric payload refuses", !checks
    (vconsApp natTm zeroTm natTm (vnilApp natTm)) (vecApp natTm (numeral 1))),
  ("declared tail index is checked", !checks
    (vconsApp natTm (numeral 1) (payload true) (vnilApp natTm)) (vecApp natTm (numeral 2)))]

#eval verdicts

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

#print axioms nonempty_typed_contract
#print axioms typed_encoding_can_lose_information
#print axioms all_verdicts

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendTypingControls
