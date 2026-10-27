import Mettapedia.GSLT.Parsing.ParserProfileSemantics
import Mettapedia.GSLT.LanguageDef.CettaWireTerm

/-!
# Canonical parser-profile wire

Language-specific parser profiles use this single serialization before the
generic ParserPack compiler consumes them.  The renderer contains no language
dispatch and emits every lexical class and state in source order.
-/

namespace Mettapedia.GSLT.Parsing.ParserProfileWire

open Mettapedia.GSLT.Parsing.ParserProfileSemantics

private def quote (text : String) : String :=
  "\"" ++ (text.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

private def renderList (entries : List String) : String :=
  entries.foldr (fun entry rest => s!"(LCons {entry} {rest})") "LNil"

private def renderCodepoints (codepoints : List Nat) : String :=
  renderList (codepoints.map toString)

private def renderClass (declaration : LexicalClassDecl) : String :=
  match declaration.kind with
  | .points codepoints =>
      s!"(LexicalClassPoints {quote declaration.name} {renderCodepoints codepoints})"
  | .except excluded =>
      s!"(LexicalClassExcept {quote declaration.name} {renderCodepoints excluded})"

private def renderState (state : LexicalStateDecl) : String :=
  s!"(LexicalState {quote state.resultSort} {quote state.className} " ++
    s!"{quote state.ruleLabel})"

/-- Canonical source-order wire rendering of a parser-profile layer. -/
def render (profile : ParserProfileLayer) : String :=
  "(GSLTParserProfileLayerV1\n" ++
    s!"  {quote profile.name}\n" ++
    s!"  {quote profile.startSort}\n" ++
    s!"  {renderList (profile.classes.map renderClass)}\n" ++
    s!"  {renderList (profile.states.map renderState)})\n"

theorem render_nonempty (profile : ParserProfileLayer) :
    render profile ≠ "" := by
  intro empty
  have prefixEmpty := (String.append_eq_empty_iff.mp empty).1
  have prefixEmpty := (String.append_eq_empty_iff.mp prefixEmpty).1
  have prefixEmpty := (String.append_eq_empty_iff.mp prefixEmpty).1
  have prefixEmpty := (String.append_eq_empty_iff.mp prefixEmpty).1
  exact (by decide : "(GSLTParserProfileLayerV1\n" ≠ "") prefixEmpty

#print axioms render_nonempty

/-! ## Exact profile data

The existing ParserPack text renderer remains unchanged. Portable module
exports use the shared physical carrier below. Decoding retains every class
and state occurrence; lexical validity and parser completeness are separate.
-/

open Mettapedia.GSLT.LanguageDef.CettaWire (Term encodeList decodeList)

private def natural? : Term → Option Nat
  | .natural value => some value
  | _ => none

def encodeClass (declaration : LexicalClassDecl) : Term :=
  match declaration.kind with
  | .points values => .application "LexicalClassPoints"
      [.string declaration.name, encodeList Term.natural values]
  | .except excluded => .application "LexicalClassExcept"
      [.string declaration.name, encodeList Term.natural excluded]

def decodeClass? : Term → Option LexicalClassDecl
  | .application "LexicalClassPoints" [.string className, values] =>
      (decodeList natural? values).map (fun decoded => ⟨className, .points decoded⟩)
  | .application "LexicalClassExcept" [.string className, excluded] =>
      (decodeList natural? excluded).map (fun decoded => ⟨className, .except decoded⟩)
  | _ => none

def encodeState (state : LexicalStateDecl) : Term :=
  .application "LexicalState"
    [.string state.resultSort, .string state.className, .string state.ruleLabel]

def decodeState? : Term → Option LexicalStateDecl
  | .application "LexicalState"
      [.string resultSort, .string className, .string ruleLabel] =>
      some ⟨resultSort, className, ruleLabel⟩
  | _ => none

def encode (profile : ParserProfileLayer) : Term :=
  .application "GSLTParserProfileLayerV1"
    [.string profile.name, .string profile.startSort,
      encodeList encodeClass profile.classes, encodeList encodeState profile.states]

def decode? : Term → Option ParserProfileLayer
  | .application "GSLTParserProfileLayerV1"
      [.string profileName, .string startSort, classes, states] => do
      let decodedClasses ← decodeList decodeClass? classes
      let decodedStates ← decodeList decodeState? states
      pure ⟨profileName, startSort, decodedClasses, decodedStates⟩
  | _ => none

@[simp] theorem decodeClass_encodeClass (declaration : LexicalClassDecl) :
    decodeClass? (encodeClass declaration) = some declaration := by
  rcases declaration with ⟨className, kind⟩
  cases kind with
  | points values =>
      simp only [encodeClass, decodeClass?]
      rw [Mettapedia.GSLT.LanguageDef.CettaWire.decodeList_encodeList
        natural? Term.natural (fun _ => rfl)]
      rfl
  | except excluded =>
      simp only [encodeClass, decodeClass?]
      rw [Mettapedia.GSLT.LanguageDef.CettaWire.decodeList_encodeList
        natural? Term.natural (fun _ => rfl)]
      rfl

@[simp] theorem decodeState_encodeState (state : LexicalStateDecl) :
    decodeState? (encodeState state) = some state := by
  cases state
  rfl

@[simp] theorem decode_encode (profile : ParserProfileLayer) :
    decode? (encode profile) = some profile := by
  cases profile
  simp [decode?, encode,
    Mettapedia.GSLT.LanguageDef.CettaWire.decodeList_encodeList]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode? same
  simpa only [decode_encode, Option.some.injEq] using decoded

theorem wrong_class_payload_refused (className : String) :
    decodeClass? (.application "LexicalClassPoints"
      [.string className, .application "LCons" [.string "48", .symbol "LNil"]]) = none := by
  simp [decodeClass?, decodeList, natural?]

theorem extra_profile_field_refused (profileName startSort : String)
    (classes states extra : Term) :
    decode? (.application "GSLTParserProfileLayerV1"
      [.string profileName, .string startSort, classes, states, extra]) = none := rfl

theorem point_and_complement_retained :
    decode? (encode ⟨"mixed", "Start",
      [⟨"same", .points [48, 48]⟩, ⟨"same", .except [48]⟩],
      [⟨"Start", "same", "lex-first"⟩, ⟨"Start", "same", "lex-second"⟩]⟩) =
      some ⟨"mixed", "Start",
        [⟨"same", .points [48, 48]⟩, ⟨"same", .except [48]⟩],
        [⟨"Start", "same", "lex-first"⟩, ⟨"Start", "same", "lex-second"⟩]⟩ :=
  decode_encode _

#print axioms decodeClass_encodeClass
#print axioms decodeState_encodeState
#print axioms decode_encode
#print axioms encode_injective
#print axioms wrong_class_payload_refused
#print axioms extra_profile_field_refused
#print axioms point_and_complement_retained

end Mettapedia.GSLT.Parsing.ParserProfileWire
