import Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16
import Mettapedia.GSLT.Parsing.ParserProfileSemantics

/-! Unicode and profile-class formation above the fixed authored word codec.
A closed word alone is not scalar-formation evidence. Out-of-range values,
surrogates, undefined classes and wrong-class scalars are refused explicitly. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Scalar

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

theorem scalar_word_bound (point : Nat) (valid : isUnicodeScalar point = true) : point < 16 ^ 6 := by
  simp only [isUnicodeScalar, decide_eq_true_eq] at valid
  norm_num
  omega

def encode? (point : Nat) : Option Pattern :=
  if valid : isUnicodeScalar point = true then
    some (Radix16Codec.encode ⟨point, scalar_word_bound point valid⟩)
  else none

def decode? (term : Pattern) : Option Nat := do
  let point ← Radix16Codec.decode? term
  if isUnicodeScalar point then some point else none

theorem encode?_isSome_iff (point : Nat) :
    (encode? point).isSome = true ↔ isUnicodeScalar point = true := by
  by_cases valid : isUnicodeScalar point = true <;> simp [encode?, valid]

theorem scalar_roundtrip (point : Nat) (valid : isUnicodeScalar point = true) :
    (encode? point).bind decode? = some point := by
  simp [encode?, valid, decode?, Radix16Codec.decode?_encode]

theorem encode?_typed (point : Nat) (term : Pattern) (accepted : encode? point = some term) :
    ClosedTermWellSorted Radix16Codec.language Radix16Codec.wordSort term := by
  unfold encode? at accepted
  split at accepted
  · cases accepted
    exact Radix16Codec.encode_closed _
  · cases accepted

theorem decode?_formed (term : Pattern) (point : Nat) (accepted : decode? term = some point) :
    Radix16Codec.decode? term = some point ∧ isUnicodeScalar point = true := by
  cases decoded : Radix16Codec.decode? term with
  | none => simp [decode?, decoded] at accepted
  | some actual =>
    by_cases valid : isUnicodeScalar actual = true
    · have same : actual = point := by simpa [decode?, decoded, valid] using accepted
      exact same ▸ ⟨rfl, valid⟩
    · simp [decode?, decoded, valid] at accepted

theorem classEvidence_scalar (profile : ParserProfileLayer) (className : String) (point : Nat)
    (evidence : profile.ClassEvidence className point) : isUnicodeScalar point = true := by
  unfold ParserProfileLayer.ClassEvidence ParserProfileLayer.classAccepts? at evidence
  cases found : profile.class? className with
  | none => simp [found] at evidence
  | some declaration =>
    have accepted : declaration.kind.accepts point = true := by simpa [found] using evidence
    simp only [LexicalClassKind.accepts, Bool.and_eq_true] at accepted
    exact accepted.1

instance (profile : ParserProfileLayer) (className : String) (point : Nat) :
    Decidable (profile.ClassEvidence className point) :=
  inferInstanceAs (Decidable (profile.classAccepts? className point = some true))

def encodeClass? (profile : ParserProfileLayer) (className : String) (point : Nat) : Option Pattern :=
  if profile.ClassEvidence className point then encode? point else none

theorem encodeClass?_isSome_iff (profile : ParserProfileLayer) (className : String) (point : Nat) :
    (encodeClass? profile className point).isSome = true ↔ profile.ClassEvidence className point := by
  by_cases evidence : profile.ClassEvidence className point
  · simp [encodeClass?, evidence, encode?_isSome_iff, classEvidence_scalar _ _ _ evidence]
  · simp [encodeClass?, evidence]

theorem class_roundtrip (profile : ParserProfileLayer) (className : String) (point : Nat)
    (evidence : profile.ClassEvidence className point) :
    (encodeClass? profile className point).bind decode? = some point := by
  simpa only [encodeClass?, if_pos evidence] using scalar_roundtrip point (classEvidence_scalar _ _ _ evidence)

private def control : ParserProfileLayer := {
  name := "ScalarControl", startSort := "Start",
  classes := [⟨"Digit", .points [48,49,50,51,52,53,54,55,56,57]⟩,
    ⟨"String", .except [10,13,34,92]⟩], states := [] }

theorem unicode_and_class_controls :
    (encodeClass? control "String" 955).bind decode? = some 955 ∧
      (encodeClass? control "String" 128512).bind decode? = some 128512 ∧
      encodeClass? control "Digit" 955 = none ∧
      encodeClass? control "String" 34 = none ∧
      encodeClass? control "Unknown" 49 = none ∧
      encode? 55296 = none ∧ encode? 1114112 = none ∧ encode? (16 ^ 6) = none := by
  decide +kernel

#print axioms scalar_roundtrip
#print axioms encode?_typed
#print axioms decode?_formed
#print axioms encodeClass?_isSome_iff
#print axioms class_roundtrip
#print axioms unicode_and_class_controls

end Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Scalar
