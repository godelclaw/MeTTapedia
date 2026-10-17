import Mettapedia.GSLT.LanguageDef.RegexScalarSyntax
import Mettapedia.Data.String.Utf8

/-!
# UTF-8 input to the authored regex syntax

The executable ingress uses the shared verified UTF-8 decoder and the
prepared regex parser plan. The independent source observation instead asks
for a Unicode character sequence whose encoding is exactly the input bytes,
then applies the original-row scalar syntax. Preservation and reflection
therefore cover decoding, lexical classes, structural parsing and complete
packed replay, not merely a caller-supplied selected tree.

These are reference-language theorems. They do not assert a refinement of
the native decoder or parser implementation. Invalid UTF-8 retains its first
error offset and cannot become a completed empty set of source parses.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexTextIngress

open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.GSLT.Parsing
open RegexScalarSyntax

def decodeScalars (bytes : ByteArray) : Except Nat (List Nat) :=
  (Mettapedia.Data.String.Utf8.decode bytes).map
    (fun chars => chars.toList.map Char.toNat)

/-- Raw-byte source meaning is stated through encoding, independently of the
decoder and packed parser used by executable ingress. -/
def Source (bytes : ByteArray) (tree : CST) : Prop :=
  ∃ chars : List Char, chars.utf8Encode = bytes ∧
    Nonempty (RootDerives (chars.map Char.toNat) tree)

def Parsed (bytes : ByteArray) (tree : CST) : Prop :=
  ∃ input, decodeScalars bytes = .ok input ∧
    ParsedBy (forest input) input tree

/-- Loading a prepared plan is independent of input decoding. This operation
constructs only the input-specific reference forest. -/
def prepareInput (bytes : ByteArray) : Except Nat ClassAwarePackedForest.Forest :=
  (decodeScalars bytes).map forest

theorem decodeScalars_encoded (chars : List Char) :
    decodeScalars chars.utf8Encode = .ok (chars.map Char.toNat) := by
  simp [decodeScalars, Mettapedia.Data.String.Utf8.decode_encoded, Except.map]

theorem decodeScalars_success {bytes : ByteArray} {input : List Nat}
    (decoded : decodeScalars bytes = .ok input) :
    ∃ chars : List Char, chars.utf8Encode = bytes ∧ chars.map Char.toNat = input := by
  unfold decodeScalars at decoded
  cases actual : Mettapedia.Data.String.Utf8.decode bytes with
  | error offset => simp [actual, Except.map] at decoded
  | ok chars =>
      simp only [actual, Except.map, Except.ok.injEq] at decoded
      exact ⟨chars.toList, Mettapedia.Data.String.Utf8.encode_decoded actual, decoded⟩

/-- Two-sided source adequacy through the actual decoder and computed full
forest. The source side does not refer to either computation. -/
theorem parsed_iff_source (bytes : ByteArray) (tree : CST) :
    Parsed bytes tree ↔ Source bytes tree := by
  constructor
  · rintro ⟨input, decoded, parsed⟩
    obtain ⟨chars, encoded, values⟩ := decodeScalars_success decoded
    exact ⟨chars, encoded, values ▸ packed_iff_source.mp parsed⟩
  · rintro ⟨chars, encoded, source⟩
    subst bytes
    exact ⟨chars.map Char.toNat, decodeScalars_encoded chars,
      packed_iff_source.mpr source⟩

theorem prepared_forest_success {bytes : ByteArray} {input : List Nat}
    (decoded : decodeScalars bytes = .ok input) :
    prepareInput bytes = .ok (forest input) := by
  simp [prepareInput, decoded, Except.map]

/-- Decoder failure is the exact independently characterized first malformed
scalar boundary. It is not evidence of an empty regex match relation. -/
theorem decodeScalars_error_iff (bytes : ByteArray) (offset : Nat) :
    decodeScalars bytes = .error offset ↔
      Mettapedia.Data.String.Utf8.FirstError bytes offset := by
  rw [← Mettapedia.Data.String.Utf8.decode_error_iff]
  unfold decodeScalars
  cases Mettapedia.Data.String.Utf8.decode bytes <;> simp [Except.map]

theorem malformed_input_not_parsed {bytes : ByteArray} {offset : Nat}
    (malformed : decodeScalars bytes = .error offset) (tree : CST) :
    ¬ Parsed bytes tree := by
  rintro ⟨input, decoded, _⟩
  rw [malformed] at decoded
  cases decoded

theorem malformed_input_has_no_source {bytes : ByteArray} {offset : Nat}
    (malformed : decodeScalars bytes = .error offset) (tree : CST) :
    ¬ Source bytes tree := by
  rw [← parsed_iff_source]
  exact malformed_input_not_parsed malformed tree

/-- Raw-byte ambiguity is reflected exactly, before any explicit tree policy.
The same byte buffer and declared scalar interpretation are used by both sides. -/
theorem ambiguity_iff (bytes : ByteArray) :
    RegexScalarSyntax.Ambiguous (Parsed bytes) ↔
      RegexScalarSyntax.Ambiguous (Source bytes) := by
  simp only [RegexScalarSyntax.Ambiguous, parsed_iff_source]

/-- The source view used for semantic lowering is explicit. Captures and
flags are attributed only after a checked parse has been retained. -/
theorem selected_projection_iff
    (bytes : ByteArray) (policy : CST → Prop)
    (view : RegexSourceProjection.Flags → CettaWire.Term → Option RegexSourceProjection.Form)
    (state : RegexSourceProjection.State) (answer : RegexSourceProjection.Output) :
    (∃ tree, Parsed bytes tree ∧ policy tree ∧
      ∃ fuel, RegexSourceProjection.project view fuel state (wire tree) = some answer) ↔
    ∃ tree, Source bytes tree ∧ policy tree ∧
      RegexSourceProjection.Projects view state (wire tree) answer := by
  constructor
  · rintro ⟨tree, parsed, retained, computed⟩
    exact ⟨tree, (parsed_iff_source bytes tree).mp parsed, retained,
      (RegexSourceProjection.project_iff view state (wire tree) answer).mp computed⟩
  · rintro ⟨tree, source, retained, projected⟩
    exact ⟨tree, (parsed_iff_source bytes tree).mpr source, retained,
      (RegexSourceProjection.project_iff view state (wire tree) answer).mpr projected⟩

namespace Controls

theorem multibyte_scalar_reaches_the_complete_parser :
    Parsed (['λ'].utf8Encode) (RegexScalarSyntax.Controls.rootLiteral 955) := by
  refine (parsed_iff_source _ _).mpr ⟨['λ'], rfl, ?_⟩
  exact ⟨RegexScalarSyntax.Controls.rootLiteralDerivation 955 (by
    change ModuleFormat.RegexSyntaxAuthoring.profile.classAccepts?
      "RxLiteralClass" 955 = some true
    decide)⟩

theorem embedded_nul_is_a_literal_scalar_not_termination :
    Parsed (['\x00'].utf8Encode) (RegexScalarSyntax.Controls.rootLiteral 0) := by
  refine (parsed_iff_source _ _).mpr ⟨['\x00'], rfl, ?_⟩
  exact ⟨RegexScalarSyntax.Controls.rootLiteralDerivation 0 (by
    change ModuleFormat.RegexSyntaxAuthoring.profile.classAccepts?
      "RxLiteralClass" 0 = some true
    decide)⟩

theorem malformed_utf8_retains_the_exact_fault_offset :
    decodeScalars ⟨#[0x61, 0xff, 0x62]⟩ = .error 1 := by decide +kernel

theorem malformed_utf8_does_not_admit_a_replacement_character_parse (tree : CST) :
    ¬ Parsed ⟨#[0x61, 0xff, 0x62]⟩ tree :=
  malformed_input_not_parsed malformed_utf8_retains_the_exact_fault_offset tree

end Controls

end Mettapedia.GSLT.LanguageDef.RegexTextIngress
