import Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSelectionAuthoring
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.RegexAuthoredComparison
import Mettapedia.Computability.RegularLanguages.AlphabetMap
import Std.Data.String.ToNat

/-!
# Explicit natural payload image of the selection compiler

Constructed native integer payloads are encoded as canonical decimal strings
before admission into the symbolic compiler's string-atom carrier. Decoding is
partial and checks both canonical spelling and the selected native width.
These are mathematical codec/admission laws, not proofs of the C adapter.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSelectionPayload

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

def encode (value : Nat) : String := Nat.repr value

def decode? (text : String) : Option Nat := do
  let value ← text.toNat?
  if encode value == text then some value else none

@[simp] theorem decode_encode (value : Nat) : decode? (encode value) = some value := by
  simp [decode?, encode]

theorem encode_injective : Function.Injective encode := fun _ _ same => Nat.repr_injective same

/-- Native integer payloads cannot be confused by alternative decimal spellings. -/
theorem decode_iff (text : String) (value : Nat) :
    decode? text = some value ↔ text = encode value := by
  constructor
  · intro decoded
    unfold decode? at decoded
    cases parsed : text.toNat? with
    | none => simp [parsed] at decoded
    | some actual =>
        simp only [parsed] at decoded
        change (if encode actual == text then some actual else none) = some value at decoded
        split at decoded
        · cases decoded
          exact (beq_iff_eq.mp (by assumption)).symm
        · simp at decoded
  · intro same
    subst text
    exact decode_encode value

def decodeBounded? (limit : Nat) (text : String) : Option {value : Nat // value < limit} := do
  let value ← decode? text
  if bound : value < limit then some ⟨value, bound⟩ else none

@[simp] theorem decodeBounded_encode (limit : Nat) (value : {value : Nat // value < limit}) :
    decodeBounded? limit (encode value.val) = some value := by
  rcases value with ⟨value, bound⟩
  simp [decodeBounded?, bound]

theorem decodeBounded_reflects (limit : Nat) (text : String)
    (value : {value : Nat // value < limit})
    (decoded : decodeBounded? limit text = some value) : text = encode value.val := by
  unfold decodeBounded? at decoded
  cases parsed : decode? text with
  | none => simp [parsed] at decoded
  | some actual =>
      simp only [parsed] at decoded
      change (if bound : actual < limit then some ⟨actual, bound⟩ else none) = some value at decoded
      split at decoded
      · cases decoded
        exact (decode_iff _ _).mp parsed
      · simp at decoded

abbrev NativeNatural := {value : Nat // value < 4294967296}

def decodeNative? := decodeBounded? 4294967296

theorem native_roundtrip (value : NativeNatural) :
    decodeNative? (encode value.val) = some value := decodeBounded_encode _ _

def atom (value : Nat) : Pattern := .apply (encode value) []

open Mettapedia.Computability.RegularLanguages

/-- The ordinary regex core's String alphabet is interpreted through the
explicit injective decimal representation of scalar identifiers. This is not
an identification of decimal text with the scalar's UTF-8 representation. -/
def coreRequest (pattern : Regex Nat) (input : List Nat) : Pattern :=
  RegexTheory.matchRequest (RegexTheory.encode (mapAlphabet encode pattern))
    (RegexTheory.word (input.map encode))

theorem core_accepts_iff (pattern : Regex Nat) (input : List Nat) :
    RegexTheory.Step (coreRequest pattern input) (RegexTheory.boolean true) ↔
      input ∈ language pattern := by
  rw [coreRequest, RegexAuthoredComparison.match_accepts_iff]
  exact mapped_word_mem_language encode encode_injective pattern input

theorem core_rejects_iff (pattern : Regex Nat) (input : List Nat) :
    RegexTheory.Step (coreRequest pattern input) (RegexTheory.boolean false) ↔
      input ∉ language pattern := by
  rw [coreRequest, RegexAuthoredComparison.match_rejects_iff]
  exact not_congr (mapped_word_mem_language encode encode_injective pattern input)

/-- The encoded payload is admitted by the declared string carrier, not by a
fictional direct embedding of an integer Atom into an AST constructor sort. -/
theorem encoded_payload_admitted (value : Nat)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.HasType RegexSelectionAuthoring.theory free bound
      (atom value) (.base "ReValue") := by
  apply CarrierWellSorted.HasType.builtinAtom
  exact ⟨⟨"ReValue", .builtinString⟩, .head _, rfl, rfl⟩

/-- Explicit abstract-core image of the existing source datatype. This does not
identify native Atom tags with abstract nullary Pattern constructors. -/
def sourceValue : RegexSelection.Pattern → Pattern
  | .zero => .apply "re:zero" []
  | .epsilon => .apply "re:epsilon" []
  | .literal value => .apply "re:literal" [atom value]
  | .any => .apply "re:any" []
  | .class_ ranges => .apply "re:class" [rangeValues ranges]
  | .assertion name => .apply "re:assert" [.apply name []]
  | .seq first second => .apply "re:seq" [sourceValue first, sourceValue second]
  | .alt first second => .apply "re:alt" [sourceValue first, sourceValue second]
  | .optional body greedy => .apply "re:optional" [sourceValue body, preferenceValue greedy]
  | .star body greedy => .apply "re:star" [sourceValue body, preferenceValue greedy]
  | .plus body greedy => .apply "re:plus" [sourceValue body, preferenceValue greedy]
  | .capture group body => .apply "re:capture" [atom group, sourceValue body]
where
  rangeValues : List RegexSelection.ScalarRange → Pattern
    | [] => .apply "LNil" []
    | first :: rest => .apply "LCons" [
        .apply "re:range" [atom first.1, atom first.2], rangeValues rest]
  preferenceValue (greedy : Bool) : Pattern := .apply (if greedy then "Greedy" else "Lazy") []

private theorem string_atom_admitted (value : String)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.HasType RegexSelectionAuthoring.theory free bound
      (.apply value []) (.base "ReValue") := by
  apply CarrierWellSorted.HasType.builtinAtom
  exact ⟨⟨"ReValue", .builtinString⟩, .head _, rfl, rfl⟩

private theorem not_bare (row : GrammarRule) (checked : WellSorted.usesBareCollection? row = false) :
    ¬ WellSorted.UsesBareCollection row := by
  intro bare
  have yes := (WellSorted.usesBareCollection?_eq_true_iff row).mpr bare
  rw [checked] at yes
  cases yes

private theorem range_values_admitted (ranges : List RegexSelection.ScalarRange)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.HasType RegexSelectionAuthoring.theory free bound
      (sourceValue.rangeValues ranges) (.base "ReValue") := by
  induction ranges with
  | nil => exact string_atom_admitted _ free bound
  | cons first rest ih =>
      refine CarrierWellSorted.HasType.constructor
        (rule := RegexSelectionAuthoring.theory.terms[37]) (List.getElem_mem (by decide)) (not_bare _ rfl)
        (.cons trivial rfl ?_ (.cons trivial rfl ih .nil))
      exact CarrierWellSorted.HasType.constructor
        (rule := RegexSelectionAuthoring.theory.terms[38]) (List.getElem_mem (by decide)) (not_bare _ rfl)
        (.cons trivial rfl (encoded_payload_admitted first.1 free bound)
          (.cons trivial rfl (encoded_payload_admitted first.2 free bound) .nil))

/-- Every recursively nested source pattern has a genuinely typed core image,
using the actual constructor rows and explicit string payload encoding. -/
theorem source_value_admitted (pattern : RegexSelection.Pattern)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.HasType RegexSelectionAuthoring.theory free bound
      (sourceValue pattern) (.base "ReValue") := by
  induction pattern with
  | zero | epsilon | any => exact string_atom_admitted _ free bound
  | literal value =>
      exact CarrierWellSorted.HasType.constructor
        (rule := RegexSelectionAuthoring.theory.terms[5]) (List.getElem_mem (by decide)) (not_bare _ rfl)
        (.cons trivial rfl (encoded_payload_admitted value free bound) .nil)
  | class_ ranges =>
      exact CarrierWellSorted.HasType.constructor
        (rule := RegexSelectionAuthoring.theory.terms[7]) (List.getElem_mem (by decide)) (not_bare _ rfl)
        (.cons trivial rfl (range_values_admitted ranges free bound) .nil)
  | assertion name =>
      exact CarrierWellSorted.HasType.constructor
        (rule := RegexSelectionAuthoring.theory.terms[8]) (List.getElem_mem (by decide)) (not_bare _ rfl)
        (.cons trivial rfl (string_atom_admitted name free bound) .nil)
  | seq first second ihFirst ihSecond =>
      exact CarrierWellSorted.HasType.constructor
        (rule := RegexSelectionAuthoring.theory.terms[9]) (List.getElem_mem (by decide)) (not_bare _ rfl)
        (.cons trivial rfl ihFirst (.cons trivial rfl ihSecond .nil))
  | alt first second ihFirst ihSecond =>
      exact CarrierWellSorted.HasType.constructor
        (rule := RegexSelectionAuthoring.theory.terms[10]) (List.getElem_mem (by decide)) (not_bare _ rfl)
        (.cons trivial rfl ihFirst (.cons trivial rfl ihSecond .nil))
  | optional body greedy ih =>
      exact CarrierWellSorted.HasType.constructor
        (rule := RegexSelectionAuthoring.theory.terms[11]) (List.getElem_mem (by decide)) (not_bare _ rfl)
        (.cons trivial rfl ih (.cons trivial rfl (string_atom_admitted _ free bound) .nil))
  | star body greedy ih =>
      exact CarrierWellSorted.HasType.constructor
        (rule := RegexSelectionAuthoring.theory.terms[12]) (List.getElem_mem (by decide)) (not_bare _ rfl)
        (.cons trivial rfl ih (.cons trivial rfl (string_atom_admitted _ free bound) .nil))
  | plus body greedy ih =>
      exact CarrierWellSorted.HasType.constructor
        (rule := RegexSelectionAuthoring.theory.terms[13]) (List.getElem_mem (by decide)) (not_bare _ rfl)
        (.cons trivial rfl ih (.cons trivial rfl (string_atom_admitted _ free bound) .nil))
  | capture group body ih =>
      exact CarrierWellSorted.HasType.constructor
        (rule := RegexSelectionAuthoring.theory.terms[14]) (List.getElem_mem (by decide)) (not_bare _ rfl)
        (.cons trivial rfl (encoded_payload_admitted group free bound) (.cons trivial rfl ih .nil))

theorem source_compiler_invocation_admitted (pattern : RegexSelection.Pattern)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.HasType RegexSelectionAuthoring.theory free bound
      (.apply "re:compile" [sourceValue pattern]) (.base "ReValue") :=
  CarrierWellSorted.HasType.constructor
    (rule := RegexSelectionAuthoring.theory.terms[0]) (List.getElem_mem (by decide)) (not_bare _ rfl)
    (.cons trivial rfl (source_value_admitted pattern free bound) .nil)

/-- Carrier atoms and declared constructors are alternative introduction rules
of the existing judgment. A string carrier does not erase its constructor rows. -/
theorem compound_literal_checked (value : Nat)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.checkHasType RegexSelectionAuthoring.theory free bound
      (.apply "re:literal" [atom value]) (.base "ReValue") = true := by rfl

theorem compound_literal_admitted (value : Nat)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.HasType RegexSelectionAuthoring.theory free bound
      (.apply "re:literal" [atom value]) (.base "ReValue") :=
  CarrierWellSorted.checkHasType_sound (compound_literal_checked value free bound)

/-- A complete actual compiler invocation, not merely an atomic payload, is
admitted by the core's constructor and builtin-atom rules together. -/
theorem capturing_star_invocation_checked (value : Nat)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.checkHasType RegexSelectionAuthoring.theory free bound
      (.apply "re:compile" [.apply "re:capture" [atom 1,
        .apply "re:star" [.apply "re:literal" [atom value], .apply "Greedy" []]]])
      (.base "ReValue") = true := by rfl

theorem capturing_star_invocation_admitted (value : Nat)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.HasType RegexSelectionAuthoring.theory free bound
      (.apply "re:compile" [.apply "re:capture" [atom 1,
        .apply "re:star" [.apply "re:literal" [atom value], .apply "Greedy" []]]])
      (.base "ReValue") :=
  CarrierWellSorted.checkHasType_sound (capturing_star_invocation_checked value free bound)

/-- Dedicated repetitions compose recursively in the admitted compiler packet;
they are not translated to capture-duplicating sequence or alternative trees. -/
theorem nested_optional_plus_invocation_checked (value : Nat)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.checkHasType RegexSelectionAuthoring.theory free bound
      (.apply "re:compile" [.apply "re:optional" [
        .apply "re:plus" [.apply "re:capture" [atom 1,
          .apply "re:literal" [atom value]], .apply "Lazy" []], .apply "Greedy" []]])
      (.base "ReValue") = true := by rfl

theorem nested_plus_optional_invocation_checked (value : Nat)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.checkHasType RegexSelectionAuthoring.theory free bound
      (.apply "re:compile" [.apply "re:plus" [
        .apply "re:capture" [atom 2, .apply "re:optional" [
          .apply "re:literal" [atom value], .apply "Greedy" []]], .apply "Lazy" []]])
      (.base "ReValue") = true := by rfl

theorem missing_repetition_preference_refused
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.checkHasType RegexSelectionAuthoring.theory free bound
      (.apply "re:optional" [.apply "re:epsilon" []]) (.base "ReValue") = false := by rfl

/-- Host payload tags remain distinct before the declared numeric adapter.
The core Pattern datatype alone cannot express this negative: it deliberately
represents both carrier spellings as atomic patterns. -/
theorem raw_integer_is_not_string_payload (value : Nat) :
    Mettapedia.Languages.MeTTa.PeTTa.StdLib.strings [.grounded (.int value)] = none := rfl

theorem encoded_native_string_payload (value : Nat) :
    Mettapedia.Languages.MeTTa.PeTTa.StdLib.strings [.grounded (.string (encode value))] =
      some [encode value] := rfl

theorem wrong_literal_arity_refused (free : WellSorted.FreeTypeContext) (bound : List TypeExpr) :
    CarrierWellSorted.checkHasType RegexSelectionAuthoring.theory free bound
      (.apply "re:literal" [atom 97, atom 98]) (.base "ReValue") = false := by rfl

namespace Controls

theorem canonical_positive : decode? "97" = some 97 := decode_encode 97
theorem zero_positive : decode? "0" = some 0 := decode_encode 0
theorem noncanonical_negative : decode? "097" = none := by
  have parsed : "097".toNat? = some 97 := by
    rw [String.toNat?_eq_some_ofDigitChars (String.isNat_of_isDigit (by decide) (by decide))]
    rfl
  simp [decode?, parsed, encode]
  decide
theorem negative_integer_is_not_a_natural : decode? "-1" = none := by
  have parsed : "-1".toNat? = none := by
    apply String.toNat?_eq_none
    rw [Bool.eq_false_iff]
    intro assumed
    have digits := String.isNat_iff.mp assumed
    simp at digits
  simp [decode?, parsed]
theorem native_width_boundary : decodeNative? "4294967296" = none := by
  change decodeBounded? 4294967296 (encode 4294967296) = none
  simp [decodeBounded?]

end Controls

end Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSelectionPayload
