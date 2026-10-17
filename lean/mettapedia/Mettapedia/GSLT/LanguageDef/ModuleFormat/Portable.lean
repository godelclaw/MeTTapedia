import Mettapedia.GSLT.LanguageDef.ModuleFormat.Authoring
import Mettapedia.GSLT.LanguageDef.ExtendedLanguageDef
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef

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
