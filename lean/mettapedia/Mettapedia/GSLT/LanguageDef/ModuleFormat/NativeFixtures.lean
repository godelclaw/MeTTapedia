import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.GSLT.LanguageDef.RegexTheory

/-!
# Complete finite presentation fixtures for native interchange

These are data-interchange specimens, not extra execution profiles. The large
specimen deliberately exercises every constructor of the portable core,
including annotations whose static obligations must be checked separately.
Its recovery theorem is an instance of the existing complete codec theorem;
it is not a correctness theorem about a native implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.NativeFixtures

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CettaWire (Term)
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra (Entry)
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring (ImportContract)
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation

open ModuleAlgebra.NativeAuthoring

/-- All carrier tags occur physically, not merely in a coverage assertion. -/
def types : List TypeDecl := [
  ⟨"Proc", .ast⟩, ⟨"Label", .tokenLabel⟩, ⟨"Raw", .tokenRaw⟩,
  ⟨"Proof", .tokenProof⟩, ⟨"Path", .tokenPath⟩, ⟨"Int", .builtinInt⟩,
  ⟨"Text", .builtinString⟩, ⟨"Bool", .builtinBool⟩, ⟨"Name", .ast⟩]

/-- Every parameter, syntax operator, policy and collection-algebra branch. -/
def terms : List GrammarRule := [
  { label := "Bind", category := "Proc",
    params := [.abstractionNamed (some "λ\n\"scope\"") "body"
      (.arrow (.base "Name") (.base "Proc"))],
    syntaxPattern := [.terminal "bind", .nonTerminal "body", .separator ",",
      .delimiter "(" ")", .op (.var "body")],
    evalPolicy? := some .rewrite },
  { label := "AnonymousBind", category := "Proc",
    params := [.abstractionNamed none "body" (.arrow (.base "Name") (.base "Proc"))],
    syntaxPattern := [], evalPolicy? := some .fold },
  { label := "BindMany", category := "Proc",
    params := [.multiAbstractionNamed ["x", "y"] "body" (.multiBinder (.base "Proc"))],
    syntaxPattern := [.op (.map (.zip "names" "bodies") ["name", "body"]
      [.nonTerminal "name", .op (.opt [.delimiter "[" "]"])])],
    evalPolicy? := some .oracle },
  { label := "AnonymousMany", category := "Proc",
    params := [.multiAbstractionNamed [] "body" (.multiBinder (.base "Proc"))],
    syntaxPattern := [.op (.sep "items" ";" none)] },
  { label := "Vec", category := "Proc",
    params := [.simple "parts" (.collection .vec (.base "Proc"))],
    syntaxPattern := [.op (.sep "parts" "," (some (.var "parts")))],
    algebra? := some ⟨false, none⟩ },
  { label := "Bag", category := "Proc",
    params := [.simple "parts" (.collection .hashBag (.base "Proc"))],
    syntaxPattern := [], algebra? := some ⟨true, some "Nil"⟩ },
  { label := "Set", category := "Proc",
    params := [.simple "parts" (.collection .hashSet (.base "Proc"))],
    syntaxPattern := [], algebra? := some ⟨false, some "Nil"⟩ },
  { label := "Nil", category := "Proc", params := [], syntaxPattern := [.terminal "nil"] }]

/-- Every pattern constructor, collection kind and optional annotation branch. -/
def pattern : Pattern := .apply "Bundle" [
  .bvar 2, .fvar "$inert", .apply "Nullary" [],
  .lambda none (.bvar 0), .lambda (some "x") (.fvar "body"),
  .multiLambda 2 ["x", "y"] (.subst (.bvar 1) (.bvar 0)),
  .multiLambda 0 [] (.apply "Nil" []),
  .collection .vec [.fvar "a", .fvar "a"] none,
  .collection .hashBag [.fvar "a", .fvar "a"] (some "rest"),
  .collection .hashSet [.fvar "a", .fvar "b"] none]

def premises : List Premise := [
  .freshness ⟨"fresh", .lambda (some "x") (.fvar "body")⟩,
  .congruence (.subst (.bvar 0) (.fvar "argument")) (.fvar "result"),
  .scopedStep ⟨[.base "Name", .base "Proc"], .base "Proc",
    .apply "StepSource" [.bvar 1, .fvar "body"],
    .lambda none (.fvar "result")⟩,
  .relationQuery "Holds" [pattern, .fvar "result"],
  .forAll "parts" "part" (.forAll "others" "other"
    (.relationQuery "Related" [.fvar "part", .fvar "other"])),
  .forAll "parts" "part" (.scopedStep
    ⟨[], .base "Proc", .fvar "part", .fvar "result"⟩)]

def bindings : RuleBindingSpec :=
  ⟨[("body", [.base "Name", .base "Proc"]), ("result", [])],
    [⟨"body", .left, [4, 0], [.bvar 1, .bvar 0]⟩,
     ⟨"body", .right, [0, 1], [.bvar 1, .bvar 0]⟩,
     ⟨"body", .premise 2 0 0, [1], [.bvar 1, .bvar 0]⟩,
     ⟨"result", .premise 4 2 1, [], []⟩]⟩

def annotatedRule : RewriteRule where
  name := "same-label-preserves-distinct-occurrences"
  typeContext := [("body", .arrow (.base "Name") (.base "Proc")),
    ("result", .base "Proc"), ("parts", .collection .hashBag (.base "Proc"))]
  premises := premises
  left := pattern
  right := .lambda (some "display") (.subst (.bvar 1) (.bvar 0))
  bindings := some bindings

def unannotatedRule : RewriteRule where
  name := "plain"
  typeContext := []
  premises := []
  left := .apply "Nil" []
  right := .apply "Nil" []

def complete : LanguageDef where
  name := "Complete λ\n\"interchange\"\\data"
  types := types
  terms := terms
  equations := [
    ⟨"annotated", annotatedRule.typeContext, premises, pattern,
      annotatedRule.right, some bindings⟩,
    ⟨"unannotated", [], [], .apply "Nil" [], .apply "Nil" [], none⟩]
  rewrites := [annotatedRule, annotatedRule, unannotatedRule]

def minimal : LanguageDef where
  name := "Minimal"
  types := []
  terms := []
  equations := []
  rewrites := []

def cores : List (String × LanguageDef) := [
  ("minimal", minimal), ("complete", complete), ("regex", RegexTheory.theory)]

def coreText (language : LanguageDef) : String := Text.render (Wire.language language)

def readCore? (source : String) : Option LanguageDef :=
  (Text.read? source).bind Wire.language?

/-- Exact recovery includes all fields, not only declaration counts. -/
theorem readCore_coreText (language : LanguageDef) :
    readCore? (coreText language) = some language := by
  simp [readCore?, coreText, Wire.language_roundtrip]

theorem complete_recovery : readCore? (coreText complete) = some complete :=
  readCore_coreText complete

theorem regex_recovery : readCore? (coreText RegexTheory.theory) = some RegexTheory.theory :=
  readCore_coreText RegexTheory.theory

theorem duplicate_occurrences_survive :
    (readCore? (coreText complete)).map (fun language => language.rewrites.length) = some 3 := by
  rw [complete_recovery]
  rfl

theorem scoped_premises_survive :
    (readCore? (coreText complete)).map (fun language =>
      language.rewrites.head?.map RewriteRule.premises) = some (some premises) := by
  rw [complete_recovery]
  rfl

theorem dependency_occurrences_survive :
    (readCore? (coreText complete)).map (fun language =>
      language.equations.head?.map Equation.bindings) = some (some (some bindings)) := by
  rw [complete_recovery]
  rfl

def decorated : ExtendedLanguageDef exportLayer := ⟨complete, ["Proc", "Name"]⟩

def decoratedText : String := Portable.renderTheory "exports/1" Portable.exportsCodec decorated

theorem decorated_recovery :
    Portable.readTheory? "exports/1" Portable.exportsCodec decoratedText = some decorated :=
  Portable.readTheory_renderTheory _ _ _

theorem wrong_layer_schema_refused :
    Portable.readTheory? "exports/2" Portable.exportsCodec decoratedText = none :=
  Portable.readTheory_renderTheory_otherSchema _ _ _ _ _ (by decide)

def origin : Term := .application "Origin" [.string "fixture/complete", .natural 1]

def entry : Entry Term Term (ExtendedLanguageDef exportLayer) :=
  ⟨origin, .string "Complete", decorated⟩

def entriesText : String := Portable.renderEntries "exports/1" Portable.exportsCodec [entry, entry]

theorem entry_occurrences_survive :
    Portable.readEntries? "exports/1" Portable.exportsCodec entriesText = some [entry, entry] :=
  Portable.readEntries_renderEntries _ _ _

def envelope : Module upstreamLimits :=
  ⟨⟨"NativeInterchange", [], [
    ⟨"Complete", Value.Wire.quoteTerm (Wire.language complete)⟩,
    ⟨"Regex", Value.Wire.quoteTerm (Wire.language RegexTheory.theory)⟩,
    ⟨"Decorated", Portable.specification "exports/1" Portable.exportsCodec decorated⟩]⟩,
    by decide⟩

theorem envelope_recovery :
    readText? upstreamLimits (renderText upstreamLimits envelope) = some envelope :=
  readText_renderText _ _

theorem recovered_export_is_complete :
    (readText? upstreamLimits (renderText upstreamLimits envelope)).bind (fun module =>
      module.val.exports.head?.bind (fun exported =>
        (Value.Wire.readTerm? exported.spec).bind Wire.language?)) = some complete := by
  rw [envelope_recovery]
  change (Value.Wire.readTerm? (Value.Wire.quoteTerm (Wire.language complete))).bind
    Wire.language? = some complete
  simp

/-- These have well-formed physical terms but malformed complete-core schemas. -/
def refusedCores : List (String × Term) := [
  ("wrong-version", .application "LanguageDefV3"
    [.string "bad", .symbol "LNil", .symbol "LNil", .symbol "LNil", .symbol "LNil"]),
  ("missing-core-field", .application "LanguageDefV2"
    [.string "bad", .symbol "LNil", .symbol "LNil", .symbol "LNil"]),
  ("improper-list", .application "LanguageDefV2"
    [.string "bad", .symbol "NotAList", .symbol "LNil", .symbol "LNil", .symbol "LNil"]),
  ("unknown-carrier", .application "LanguageDefV2"
    [.string "bad", .application "LCons"
      [.application "TypeDecl" [.string "Proc", .symbol "CarrierOther"], .symbol "LNil"],
      .symbol "LNil", .symbol "LNil", .symbol "LNil"])]

def refusedTexts : List (String × String) := [
  ("truncated", "(module:document (LanguageDefV2"),
  ("command", "!(module:document 7)"),
  ("extra-declaration", "(module:document 7)\n(module:document 8)"),
  ("invalid-codepoint", "(module:document (module:codepoints (LCons 1114112 LNil)))")]

#guard refusedCores.all (fun fixture => (Wire.language? fixture.2).isNone)
#guard refusedTexts.all (fun fixture => (Text.read? fixture.2).isNone)
#guard complete.types.length == 9
#guard complete.terms.length == 8
#guard complete.rewrites.length == 3
#guard premises.length == 6
#guard RegexTheory.theory.rewrites.length == 26

end Mettapedia.GSLT.LanguageDef.ModuleFormat.NativeFixtures
