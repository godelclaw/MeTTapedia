import Mettapedia.GSLT.LanguageDef.ModuleFormat.Authoring
import Mettapedia.GSLT.LanguageDef.ExtendedLanguageDef
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.GSLT.Parsing.ParserProfileWire
import Mettapedia.GSLT.Parsing.ExactPresentation
import Std.Data.String.ToNat

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition

/-! ## Portable dependent presentation layers

A portable layer supplies an actual codec for every base language. This is a
capability of a particular layer, not a claim that arbitrary Lean functions,
relations or types can be serialized. Products reuse the established dependent
product layer, and the full core stays the existing five-field LanguageDef.
-/

namespace Portable

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra (Entry)
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker (PartialCodec)
open Mettapedia.GSLT.LanguageDef.CettaWire (Term encodeList decodeList decodeList_encodeList)

universe u v

abbrev LayerCodec (layerSpec : CompositionalLayer.{0, u} LanguageDef) :=
  (base : LanguageDef) → PartialCodec (layerSpec.Fiber base) Term

def coreCodec : PartialCodec LanguageDef Term where
  encode := ModuleAlgebra.NativeAuthoring.Wire.language
  decode := ModuleAlgebra.NativeAuthoring.Wire.language?
  decode_encode := ModuleAlgebra.NativeAuthoring.Wire.language_roundtrip

/-! ## Portable authored syntax

The grammar is an ordinary complete five-field core. Its lexical profile is
retained beside it as data, without adding a field to `LanguageDef` or changing
the module envelope. Reading this specification does not certify lexical
admission, packed parsing, ambiguity selection or execution.
-/

structure SyntaxDescription where
  grammar : LanguageDef
  profile : Parsing.ParserProfileSemantics.ParserProfileLayer
  deriving Repr

/-! The human module language already carries applications, quoted constructor
names, numeral constructors and the shared `LNil`/`LCons` carrier. This adapter reads lexical-profile
data returned by an ordinary authored message. It does not reinterpret a
grammar sort or production name as a lexical declaration. -/

private def sourceString (value : String) : Pattern := .apply value []

private def sourceString? : Pattern → Option String
  | .apply value [] => some value
  | _ => none

private def sourceNatural (value : Nat) : Pattern := .apply (Nat.repr value) []

private def sourceNatural? (value : Pattern) : Option Nat := do
  let text ← sourceString? value
  let number ← text.toNat?
  if Nat.repr number = text then some number else none

private theorem sourceNatural_roundtrip (value : Nat) :
    sourceNatural? (sourceNatural value) = some value := by
  simp [sourceNatural?, sourceNatural, sourceString?, Nat.toNat?_repr]

private def sourceList {α : Type} (encode : α → Pattern) : List α → Pattern
  | [] => .apply "LNil" []
  | value :: values => .apply "LCons" [encode value, sourceList encode values]

private def readSourceList? {α : Type} (decode : Pattern → Option α) :
    Pattern → Option (List α)
  | .apply "LNil" [] => some []
  | .apply "LCons" [value, values] => do
      let head ← decode value
      let tail ← readSourceList? decode values
      pure (head :: tail)
  | _ => none
termination_by term => sizeOf term

private theorem sourceList_roundtrip {α : Type}
    (encode : α → Pattern) (decode : Pattern → Option α)
    (roundtrip : ∀ value, decode (encode value) = some value) (values : List α) :
    readSourceList? decode (sourceList encode values) = some values := by
  induction values with
  | nil => simp [sourceList, readSourceList?]
  | cons value values ih => simp [sourceList, readSourceList?, roundtrip, ih]

private def sourceClass (declaration : Parsing.ParserProfileSemantics.LexicalClassDecl) :
    Pattern :=
  let constructor := match declaration.kind with
    | .points _ => "LexicalClassPoints"
    | .except _ => "LexicalClassExcept"
  let values := match declaration.kind with
    | .points points => points
    | .except excluded => excluded
  .apply constructor [sourceString declaration.name,
    sourceList sourceNatural values]

private def sourceClass? : Pattern → Option Parsing.ParserProfileSemantics.LexicalClassDecl
  | .apply "LexicalClassPoints" [name, points] => do
      let className ← sourceString? name
      let values ← readSourceList? sourceNatural? points
      pure ⟨className, .points values⟩
  | .apply "LexicalClassExcept" [name, excluded] => do
      let className ← sourceString? name
      let values ← readSourceList? sourceNatural? excluded
      pure ⟨className, .except values⟩
  | _ => none

private theorem sourceClass_roundtrip
    (declaration : Parsing.ParserProfileSemantics.LexicalClassDecl) :
    sourceClass? (sourceClass declaration) = some declaration := by
  rcases declaration with ⟨className, points | excluded⟩ <;>
    simp [sourceClass?, sourceClass, sourceString?, sourceString,
      sourceList_roundtrip sourceNatural sourceNatural? sourceNatural_roundtrip]

private def sourceState (state : Parsing.ParserProfileSemantics.LexicalStateDecl) : Pattern :=
  .apply "LexicalState" [sourceString state.resultSort, sourceString state.className,
    sourceString state.ruleLabel]

private def sourceState? : Pattern → Option Parsing.ParserProfileSemantics.LexicalStateDecl
  | .apply "LexicalState" [result, className, ruleLabel] => do
      let resultSort ← sourceString? result
      let scalarClass ← sourceString? className
      let lexicalRule ← sourceString? ruleLabel
      pure ⟨resultSort, scalarClass, lexicalRule⟩
  | _ => none

private theorem sourceState_roundtrip
    (state : Parsing.ParserProfileSemantics.LexicalStateDecl) :
    sourceState? (sourceState state) = some state := by
  cases state
  rfl

def lexicalData (profile : Parsing.ParserProfileSemantics.ParserProfileLayer) : Pattern :=
  .apply "GSLTParserProfileLayerV1" [sourceString profile.name,
    sourceString profile.startSort, sourceList sourceClass profile.classes,
    sourceList sourceState profile.states]

def readLexicalData? : Pattern → Option Parsing.ParserProfileSemantics.ParserProfileLayer
  | .apply "GSLTParserProfileLayerV1"
      [name, start, classes, states] => do
      let profileName ← sourceString? name
      let startSort ← sourceString? start
      let lexicalClasses ← readSourceList? sourceClass? classes
      let lexicalStates ← readSourceList? sourceState? states
      pure ⟨profileName, startSort, lexicalClasses, lexicalStates⟩
  | _ => none

@[simp] theorem lexicalData_roundtrip
    (profile : Parsing.ParserProfileSemantics.ParserProfileLayer) :
    readLexicalData? (lexicalData profile) = some profile := by
  cases profile
  simp [readLexicalData?, lexicalData, sourceString?, sourceString,
    sourceList_roundtrip sourceClass sourceClass? sourceClass_roundtrip,
    sourceList_roundtrip sourceState sourceState? sourceState_roundtrip]

theorem lexicalData_injective : Function.Injective lexicalData := by
  intro left right same
  have decoded := congrArg readLexicalData? same
  simpa using decoded

theorem lexicalData_tail_refused (profileName startSort rest : String)
    (declaration : Parsing.ParserProfileSemantics.LexicalClassDecl) :
    readLexicalData? (.apply "GSLTParserProfileLayerV1"
      [sourceString profileName, sourceString startSort,
        .apply "LCons" [sourceClass declaration, .fvar rest], .apply "LNil" []]) = none := by
  simp [readLexicalData?, sourceString?, sourceString, readSourceList?, sourceClass_roundtrip]

theorem lexicalData_noncanonical_natural_refused :
    readLexicalData? (.apply "GSLTParserProfileLayerV1"
      [.apply "P" [], .apply "S" [],
        .apply "LCons" [.apply "LexicalClassPoints"
          [.apply "Digit" [], .apply "LCons" [.apply "048" [], .apply "LNil" []]],
          .apply "LNil" []], .apply "LNil" []]) = none := by
  have parsed : "048".toNat? = some 48 := by cbv
  have different : Nat.repr 48 ≠ "048" := by cbv
  simp [readLexicalData?, readSourceList?, sourceClass?, sourceString?, sourceNatural?, parsed, different]

#print axioms lexicalData_roundtrip
#print axioms lexicalData_injective
#print axioms lexicalData_tail_refused
#print axioms lexicalData_noncanonical_natural_refused

def syntaxTerm (description : SyntaxDescription) : Term :=
  .application "GSLTSyntaxV1"
    [coreCodec.encode description.grammar,
      Parsing.ParserProfileWire.encode description.profile]

def syntax? : Term → Option SyntaxDescription
  | .application "GSLTSyntaxV1" [grammar, profile] => do
      let decodedGrammar ← coreCodec.decode grammar
      let decodedProfile ← Parsing.ParserProfileWire.decode? profile
      pure ⟨decodedGrammar, decodedProfile⟩
  | _ => none

@[simp] theorem syntax_roundtrip (description : SyntaxDescription) :
    syntax? (syntaxTerm description) = some description := by
  cases description
  simp [syntax?, syntaxTerm, coreCodec.decode_encode,
    Parsing.ParserProfileWire.decode_encode]

def syntaxCodec : PartialCodec SyntaxDescription Term where
  encode := syntaxTerm
  decode := syntax?
  decode_encode := syntax_roundtrip

/-- Typed conversion uses the actual independent decoder and encoder. The
representation law concerns the entire grammar/profile payload. -/
def syntaxPresentation : Parsing.ExactPresentation.Presentation
    (fun _ : Unit => SyntaxDescription) (fun _ : Unit => Term) where
  key := ⟨"gslt:authored-syntax", 1⟩
  expand := fun {_} => syntax?
  view := fun {_} => syntaxTerm
  expand_view := fun {_} => syntax_roundtrip

def syntaxSpecification (description : SyntaxDescription) : Value :=
  Value.Wire.quoteTerm (syntaxTerm description)

def admitSyntaxSpecification? (value : Value) : Option SyntaxDescription :=
  (Value.Wire.readTerm? value).bind syntax?

@[simp] theorem syntaxSpecification_roundtrip (description : SyntaxDescription) :
    admitSyntaxSpecification? (syntaxSpecification description) = some description := by
  simp [admitSyntaxSpecification?, syntaxSpecification]

def syntaxExport (exportName : String) (description : SyntaxDescription) : Export :=
  ⟨exportName, syntaxSpecification description⟩

def readSyntaxExport? (expectedName : String) (entry : Export) : Option SyntaxDescription :=
  if entry.name = expectedName then admitSyntaxSpecification? entry.spec else none

@[simp] theorem readSyntaxExport_syntaxExport (exportName : String)
    (description : SyntaxDescription) :
    readSyntaxExport? exportName (syntaxExport exportName description) = some description := by
  simp [readSyntaxExport?, syntaxExport]

theorem readSyntaxExport_wrong_name (expectedName : String) (entry : Export)
    (different : entry.name ≠ expectedName) : readSyntaxExport? expectedName entry = none := by
  simp [readSyntaxExport?, different]

def renderSyntax (description : SyntaxDescription) : String := Text.render (syntaxTerm description)

def readSyntax? (source : String) : Option SyntaxDescription :=
  (Text.read? source).bind syntax?

@[simp] theorem readSyntax_renderSyntax (description : SyntaxDescription) :
    readSyntax? (renderSyntax description) = some description := by
  simp [readSyntax?, renderSyntax]

theorem syntaxTerm_injective : Function.Injective syntaxTerm := syntaxCodec.encode_injective

theorem syntax_wrong_arity (grammar profile extra : Term) :
    syntax? (.application "GSLTSyntaxV1" [grammar, profile, extra]) = none := rfl

#print axioms syntax_roundtrip
#print axioms syntaxSpecification_roundtrip
#print axioms readSyntaxExport_syntaxExport
#print axioms readSyntaxExport_wrong_name
#print axioms readSyntax_renderSyntax
#print axioms syntaxTerm_injective
#print axioms syntax_wrong_arity

def productCodec {left : CompositionalLayer.{0, u} LanguageDef}
    {right : CompositionalLayer.{0, v} LanguageDef}
    (first : LayerCodec left) (second : LayerCodec right) :
    LayerCodec (left.product right) := fun base => {
  encode := fun value => .application "LayerPair"
    [(first base).encode value.1, (second base).encode value.2]
  decode := fun term => match term with
    | .application "LayerPair" [left, right] =>
        match (first base).decode left, (second base).decode right with
        | some a, some b => some (a, b)
        | _, _ => none
    | _ => none
  decode_encode := by
    intro value
    rcases value with ⟨left, right⟩
    simp [(first base).decode_encode, (second base).decode_encode] }

def theoryTerm {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (theory : ExtendedLanguageDef layerSpec) : Term :=
  .application "ExtendedLanguageDefV1"
    [.string schema, coreCodec.encode theory.toLanguageDef,
      (codec theory.toLanguageDef).encode theory.extension]

def theory? {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) : Term → Option (ExtendedLanguageDef layerSpec)
  | .application "ExtendedLanguageDefV1" [.string actual, language, extension] =>
      if actual ≠ schema then none else
        match coreCodec.decode language with
        | none => none
        | some base => ((codec base).decode extension).map (fun payload => ⟨base, payload⟩)
  | _ => none

@[simp] theorem theory_roundtrip {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (theory : ExtendedLanguageDef layerSpec) :
    theory? schema codec (theoryTerm schema codec theory) = some theory := by
  rcases theory with ⟨base, extension⟩
  simp [theory?, theoryTerm, coreCodec.decode_encode, (codec base).decode_encode]

def theoryCodec {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) :
    PartialCodec (ExtendedLanguageDef layerSpec) Term where
  encode := theoryTerm schema codec
  decode := theory? schema codec
  decode_encode := theory_roundtrip schema codec

/-- A portable theory is an ordinary module export specification. -/
def specification {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (theory : ExtendedLanguageDef layerSpec) : Value :=
  Value.Wire.quoteTerm (theoryTerm schema codec theory)

def admitSpecification? {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (value : Value) :
    Option (ExtendedLanguageDef layerSpec) :=
  match Value.Wire.readTerm? value with
  | none => none
  | some term => theory? schema codec term

@[simp] theorem specification_roundtrip {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (theory : ExtendedLanguageDef layerSpec) :
    admitSpecification? schema codec (specification schema codec theory) = some theory := by
  simp [admitSpecification?, specification]

def renderTheory {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (theory : ExtendedLanguageDef layerSpec) : String :=
  Text.render (theoryTerm schema codec theory)

def readTheory? {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (source : String) :
    Option (ExtendedLanguageDef layerSpec) :=
  match Text.read? source with
  | none => none
  | some term => theory? schema codec term

@[simp] theorem readTheory_renderTheory {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (theory : ExtendedLanguageDef layerSpec) :
    readTheory? schema codec (renderTheory schema codec theory) = some theory := by
  simp [readTheory?, renderTheory]

/-- A reader for another declared layer cannot reinterpret its payload. The
rejection happens before the dependent extension decoder is invoked. -/
theorem readTheory_renderTheory_otherSchema
    {source : CompositionalLayer.{0, u} LanguageDef}
    {target : CompositionalLayer.{0, v} LanguageDef}
    (sourceSchema targetSchema : String) (sourceCodec : LayerCodec source)
    (targetCodec : LayerCodec target) (theory : ExtendedLanguageDef source)
    (different : sourceSchema ≠ targetSchema) :
    readTheory? targetSchema targetCodec (renderTheory sourceSchema sourceCodec theory) = none := by
  unfold readTheory? renderTheory
  rw [Text.read_render]
  simp only [theoryTerm, theory?, if_pos different]

/-- The decoded layer elaborates to exactly the original payload, over the
same core. This invokes the layer's authored elaborator after the text proof. -/
theorem readTheory_elaboration {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (theory : ExtendedLanguageDef layerSpec) :
    (readTheory? schema codec (renderTheory schema codec theory)).bind
      (fun read => (layerSpec.elaborate read.toLanguageDef read.authoredSource).map
        (fun payload => (⟨read.toLanguageDef, payload⟩ : Sigma layerSpec.Fiber))) =
      some ⟨theory.toLanguageDef, theory.extension⟩ := by
  rw [readTheory_renderTheory]
  simp only [Option.bind_some, ExtendedLanguageDef.elaborate_authoredSource, Option.map_some]

/-- Origin and label are physical data independent of the body. -/
def entryTerm {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec)
    (entry : Entry Term Term (ExtendedLanguageDef layerSpec)) : Term :=
  ModuleAlgebra.NativeAuthoring.importEntryTerm
    ⟨entry.origin, entry.label, theoryTerm schema codec entry.body⟩

def entry? {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (term : Term) :
    Option (Entry Term Term (ExtendedLanguageDef layerSpec)) :=
  match ModuleAlgebra.NativeAuthoring.decodeImportEntry? term with
  | none => none
  | some entry => (theory? schema codec entry.body).map (fun body => ⟨entry.origin, entry.label, body⟩)

@[simp] theorem entry_roundtrip {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec)
    (entry : Entry Term Term (ExtendedLanguageDef layerSpec)) :
    entry? schema codec (entryTerm schema codec entry) = some entry := by
  cases entry
  simp [entry?, entryTerm]

def renderEntries {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec)
    (entries : List (Entry Term Term (ExtendedLanguageDef layerSpec))) : String :=
  Text.render (encodeList (entryTerm schema codec) entries)

def readEntries? {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (source : String) :
    Option (List (Entry Term Term (ExtendedLanguageDef layerSpec))) :=
  match Text.read? source with
  | none => none
  | some term => decodeList (entry? schema codec) term

@[simp] theorem readEntries_renderEntries {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec)
    (entries : List (Entry Term Term (ExtendedLanguageDef layerSpec))) :
    readEntries? schema codec (renderEntries schema codec entries) = some entries := by
  simp [readEntries?, renderEntries, decodeList_encodeList]

/-- Full entry lists round-trip before import coherence decides whether an
ancestor is shared. Equal-valued rewrite occurrences inside a body are untouched. -/
theorem renderEntries_injective {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) :
    Function.Injective (renderEntries schema codec) := by
  intro first second same
  have := congrArg (readEntries? schema codec) same
  simpa only [readEntries_renderEntries, Option.some.injEq] using this

def assembleText? {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (name source : String) :
    Option LanguageDef :=
  (readEntries? schema codec source).map fun entries =>
    ModuleAlgebra.NativeAuthoring.assemble name (entries.map fun entry => entry.body.toLanguageDef)

theorem assembleText_renderEntries {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) (name : String)
    (entries : List (Entry Term Term (ExtendedLanguageDef layerSpec))) :
    assembleText? schema codec name (renderEntries schema codec entries) =
      some (ModuleAlgebra.NativeAuthoring.assemble name
        (entries.map fun entry => entry.body.toLanguageDef)) := by
  simp [assembleText?]

/-- Sharing is selected by the established import contract, after inert text
reading. The check sees the complete encoded body, not a name or digest. -/
def checkedEntries? (contract : ModuleAlgebra.NativeAuthoring.ImportContract)
    (source : String) : Option (List (Entry Term Term Term)) := do
  let term ← Text.read? source
  let entries ← decodeList ModuleAlgebra.NativeAuthoring.decodeImportEntry? term
  contract.check? entries

def rawEntry {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec)
    (entry : Entry Term Term (ExtendedLanguageDef layerSpec)) : Entry Term Term Term :=
  ⟨entry.origin, entry.label, theoryTerm schema codec entry.body⟩

private theorem rawEntries_decode {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec)
    (entries : List (Entry Term Term (ExtendedLanguageDef layerSpec))) :
    decodeList ModuleAlgebra.NativeAuthoring.decodeImportEntry?
      (encodeList (entryTerm schema codec) entries) =
      some (entries.map (rawEntry schema codec)) := by
  exact CettaWire.decodeList_encodeList_map _ _ _
    (fun entry => ModuleAlgebra.NativeAuthoring.decodeImportEntry_importEntryTerm
      (rawEntry schema codec entry)) entries

theorem checkedEntries_renderEntries {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (contract : ModuleAlgebra.NativeAuthoring.ImportContract)
    (schema : String) (codec : LayerCodec layerSpec)
    (entries : List (Entry Term Term (ExtendedLanguageDef layerSpec))) :
    checkedEntries? contract (renderEntries schema codec entries) =
      contract.check? (entries.map (rawEntry schema codec)) := by
  simp [checkedEntries?, renderEntries, rawEntries_decode]

theorem rawEntry_injective {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (schema : String) (codec : LayerCodec layerSpec) :
    Function.Injective (rawEntry schema codec) := by
  intro first second same
  have origins := congrArg Entry.origin same
  have labels := congrArg Entry.label same
  have bodies := (theoryCodec schema codec).encode_injective (congrArg Entry.body same)
  cases first
  cases second
  simp_all only [rawEntry, Entry.mk.injEq]

/-- Text composition joins the original declaration occurrences, before the
import contract decides which repeated ancestor is one shared declaration. -/
theorem checkedEntries_append {layerSpec : CompositionalLayer.{0, u} LanguageDef}
    (contract : ModuleAlgebra.NativeAuthoring.ImportContract)
    (schema : String) (codec : LayerCodec layerSpec)
    (first second : List (Entry Term Term (ExtendedLanguageDef layerSpec))) :
    checkedEntries? contract (renderEntries schema codec (first ++ second)) =
      contract.join? (first.map (rawEntry schema codec)) (second.map (rawEntry schema codec)) := by
  rw [checkedEntries_renderEntries, List.map_append]
  rfl

/-- Complete proof-calculus payloads reuse the existing rule and judgment codecs. -/
def calculusCodec : LayerCodec calculusLayer := fun _ => {
  encode := fun calculus => .application "ProofCalculusV1"
    [encodeList InferenceCettaWire.encodeJudgment calculus.judgments,
      encodeList InferenceCettaWire.encodeRule calculus.rules,
      InferenceCettaWire.encodeConversion calculus.conversion]
  decode := fun term => match term with
    | .application "ProofCalculusV1" [judgments, rules, conversion] => do
        pure ⟨← decodeList InferenceCettaWire.decodeJudgment judgments,
          ← decodeList InferenceCettaWire.decodeRule rules,
          ← InferenceCettaWire.decodeConversion conversion⟩
    | _ => none
  decode_encode := by
    intro calculus
    rcases calculus with ⟨judgments, rules, conversion⟩
    simp [decodeList_encodeList] }

/-- Portable text of the complete calculus layer over its original language.
This uses the existing module data surface, not the upstream builder grammar. -/
def renderCalculus (definition : CalculusLanguageDef) : String :=
  renderTheory "calculus/1" calculusCodec definition.toExtended

def readCalculus? (source : String) : Option CalculusLanguageDef :=
  (readTheory? "calculus/1" calculusCodec source).map CalculusLanguageDef.ofExtended

@[simp] theorem readCalculus_renderCalculus (definition : CalculusLanguageDef) :
    readCalculus? (renderCalculus definition) = some definition := by
  simp [readCalculus?, renderCalculus]

/-- Reading transports declarations; the original calculus validator alone
admits them for inference. Malformed or invalid input cannot mint a package. -/
def readValidatedCalculus? (source : String) : Option ValidatedCalculusLanguageDef :=
  (readCalculus? source).bind CalculusLanguageDef.validate?

@[simp] theorem readValidatedCalculus_renderCalculus
    (definition : ValidatedCalculusLanguageDef) :
    readValidatedCalculus? (renderCalculus definition.val) = some definition := by
  simp [readValidatedCalculus?, CalculusLanguageDef.validate?, definition.property]

/-- A wrong layer schema cannot be relabelled into inference authority. -/
theorem readCalculus_wrong_schema (schema : String) (different : schema ≠ "calculus/1")
    (definition : CalculusLanguageDef) :
    readCalculus? (renderTheory schema calculusCodec definition.toExtended) = none := by
  simp [readCalculus?, readTheory?, renderTheory, theory?, theoryTerm, different]

private def string? : Term → Option String
  | .string value => some value
  | _ => none

/-- The existing upstream quotation's export layer is serializable unchanged. -/
def exportsCodec : LayerCodec ModuleAlgebra.UpstreamTheoryQuotation.exportLayer := fun _ => {
  encode := encodeList Term.string
  decode := decodeList string?
  decode_encode := decodeList_encodeList string? Term.string (fun _ => rfl) }

/-- Independent layer products are genuinely compositional: the canonical
payload source still uses the existing product GSLT and its elaboration laws. -/
theorem product_theory_roundtrip
    (theory : ExtendedLanguageDef
      (calculusLayer.product ModuleAlgebra.UpstreamTheoryQuotation.exportLayer)) :
    readTheory? "calculus+exports/1" (productCodec calculusCodec exportsCodec)
        (renderTheory "calculus+exports/1" (productCodec calculusCodec exportsCodec) theory) =
      some theory :=
  readTheory_renderTheory _ _ _

end Portable

end Mettapedia.GSLT.LanguageDef.ModuleFormat
