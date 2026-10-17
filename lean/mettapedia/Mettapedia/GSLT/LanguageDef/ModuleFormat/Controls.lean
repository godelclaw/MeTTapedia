import Mettapedia.GSLT.LanguageDef.ModuleFormat

/-!
# Module-format controls

These examples exercise envelope admission, ordered payload retention,
reference normalization, dependency linking, qualification and mixed coGSLT
composition. Opaque specifications intentionally include non-language values:
module admission alone must not certify an export's language schema.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.Controls

open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.OSLF.MeTTaIL.Syntax

def commitment : List UInt8 := List.replicate 32 66

def payload : Value := .record [
  ("mettail", .string "language/2"), ("name", .string "Left"),
  ("types", .list [.string "Expr"]),
  ("opaque", .list [.integer (-17), .floatBits 4607182418800017408,
    .boolean true, .nil, .bytes [0, 255]])]

def baseRaw : RawModule := ⟨"Base", [], [⟨"Expr", .string "retained base payload"⟩]⟩
def pairRaw : RawModule := ⟨"Pair", [⟨.registry "base", commitment⟩],
  [⟨"Left", payload⟩, ⟨"Right", .list [.integer 42, .string "unchanged"]⟩]⟩

def baseModule : Module upstreamLimits := ⟨baseRaw, by decide⟩
def pairModule : Module upstreamLimits := ⟨pairRaw, by decide⟩
def pairCatalog : Catalog upstreamLimits := ⟨[pairModule], by decide⟩
def baseCatalog : Catalog upstreamLimits := ⟨[baseModule], by decide⟩
def combinedCatalog : Catalog upstreamLimits := ⟨[pairModule, baseModule], by decide⟩

def snapshot : Snapshot upstreamLimits :=
  ⟨[⟨.registry "base", commitment, baseModule⟩], by decide⟩

def replaceField (value : Value) (key : String) (replacement : Value) : Value :=
  match value with
  | .record fields => .record (fields.map fun field =>
      if field.1 = key then (key, replacement) else field)
  | other => other

def addField (value : Value) (key : String) (entry : Value) : Value :=
  match value with
  | .record fields => .record (fields ++ [(key, entry)])
  | other => other

def removeField (value : Value) (key : String) : Value :=
  match value with
  | .record fields => .record (fields.filter fun field => field.1 != key)
  | other => other

def dependencyValue (uri : String) (bytes : List UInt8) : Value :=
  .record [("commitment", .bytes bytes), ("uri", .string uri)]

def pairValue : Value := encodeRaw pairRaw

def fixtures : List (String × Value × Bool) := [
  ("ordered opaque payloads", pairValue, true),
  ("no dependencies", encodeRaw baseRaw, true),
  ("bare file path", replaceField pairValue "dependencies"
    (.list [dependencyValue "base.mettail" commitment]), true),
  ("explicit file path", replaceField pairValue "dependencies"
    (.list [dependencyValue "file:base.mettail" commitment]), true),
  ("prefix with internal colon", replaceField pairValue "dependencies"
    (.list [dependencyValue "rho:a:b" commitment]), true),
  ("opaque non-language export", encodeRaw {pairRaw with exports := [⟨"Left", .integer 17⟩]}, true),
  ("schema mismatch", replaceField pairValue "mettail" (.string "module/2"), false),
  ("schema wrong carrier", replaceField pairValue "mettail" (.integer 1), false),
  ("unknown envelope field", addField pairValue "surprise" .nil, false),
  ("missing envelope field", removeField pairValue "dependencies", false),
  ("empty module name", encodeRaw {pairRaw with name := ""}, false),
  ("digit first module name", encodeRaw {pairRaw with name := "1Pair"}, false),
  ("non-ASCII module name", encodeRaw {pairRaw with name := "Páir"}, false),
  ("empty exports", encodeRaw {pairRaw with exports := []}, false),
  ("duplicate export", encodeRaw {pairRaw with exports := [⟨"Left", payload⟩, ⟨"Left", .nil⟩]}, false),
  ("invalid export name", encodeRaw {pairRaw with exports := [⟨"Left-x", payload⟩]}, false),
  ("commitment too short", replaceField pairValue "dependencies"
    (.list [dependencyValue "rho:base" (List.replicate 31 66)]), false),
  ("commitment too long", replaceField pairValue "dependencies"
    (.list [dependencyValue "rho:base" (List.replicate 33 66)]), false),
  ("empty registry reference", replaceField pairValue "dependencies"
    (.list [dependencyValue "rho:" commitment]), false),
  ("unsupported reference scheme", replaceField pairValue "dependencies"
    (.list [dependencyValue "https:base" commitment]), false),
  ("duplicate normalized file reference", replaceField pairValue "dependencies"
    (.list [dependencyValue "base.mettail" commitment,
      dependencyValue "file:base.mettail" commitment]), false)]

/-- A single kernel-checked table covers independently specified expectations. -/
theorem fixtures_pass :
    fixtures.all (fun fixture =>
      (decode? upstreamLimits fixture.2.1).isSome == fixture.2.2) = true := by decide

theorem duplicate_record_occurrence_rejected :
    decode? upstreamLimits (addField pairValue "name" (.string "Pair")) = none := by decide

theorem collection_policy_enforced : decode? ⟨0, 1⟩ pairValue = none := by decide

theorem reference_aliases_normalize :
    ModuleRef.parse? "base.mettail" = ModuleRef.parse? "file:base.mettail" := by decide

theorem exact_envelope_roundtrip :
    decode? upstreamLimits pairValue = some pairModule := by decide

theorem exact_ordered_exports :
    (decode? upstreamLimits pairValue).map (fun module => module.val.exports) =
      some [⟨"Left", payload⟩, ⟨"Right", .list [.integer 42, .string "unchanged"]⟩] := by decide

theorem compatible_assembly :
    (catalogSystem upstreamLimits).merge pairCatalog baseCatalog = some combinedCatalog := by decide

theorem conflicting_assembly_rejected :
    (catalogSystem upstreamLimits).merge pairCatalog pairCatalog = none := by decide

theorem linked_dependency_matches :
    (linkDependencies? snapshot pairModule).map (fun entries => entries.map RegistryEntry.declaration) =
      some [baseModule] := by decide

theorem changed_commitment_rejected :
    resolve? snapshot ⟨.registry "base", List.replicate 32 67⟩ = none := by decide

theorem invented_reference_rejected :
    resolve? snapshot ⟨.registry "other", commitment⟩ = none := by decide

theorem exact_export_lookup :
    lookupExport? combinedCatalog "Pair" "Left" = some ⟨"Pair", "Left", payload⟩ := by decide

theorem constructed_spelling_grants_nothing :
    lookupExport? combinedCatalog "rho:Pair" "Left" = none := by decide

theorem malformed_declaration_rejects_bundle :
    elaborateDocument? upstreamLimits (.bundle [.declaration pairValue, .declaration .nil]) =
      none := by
  apply append_rejected_right
  simp [elaborateDocument?, DeclarationDocument.values, decode?, decodeRaw?, Value.record?]

def termLanguage : LanguageDef := {
  name := "Core"
  types := ["Expr"]
  terms := []
  equations := []
  rewrites := [] }

def proofCalculus : ProofCalculus := { judgments := [⟨"Proves", 2⟩] }

/-- This uses the existing proof-calculus layer alongside the new module
layer, with a nonempty proof declaration and nonempty module catalog. -/
theorem mixed_layer_roundtrip :
    (moduleCalculusLayer upstreamLimits).elaborate termLanguage
        ((moduleCalculusLayer upstreamLimits).quote termLanguage (pairCatalog, proofCalculus)) =
      some (pairCatalog, proofCalculus) :=
  moduleCalculus_roundtrip upstreamLimits termLanguage pairCatalog proofCalculus

/-- Opaque export content still supplies no
proof declarations through module-only composition. -/
theorem module_data_does_not_add_proofs :
    (moduleCalculusLayer upstreamLimits).elaborate termLanguage
      [Sum.inl (quoteModules upstreamLimits [pairModule])] =
      some (pairCatalog, ProofCalculus.empty) := by
  have quoted : elaborateCatalog? upstreamLimits
      (quoteModules upstreamLimits [pairModule]) = some pairCatalog :=
    (catalogSystem upstreamLimits).elaboration.elaborate_quote pairCatalog
  exact (moduleCalculus_modules_only upstreamLimits termLanguage
    (quoteModules upstreamLimits [pairModule])).trans (by rw [quoted]; rfl)

def otherRaw : RawModule := ⟨"Other", [], [⟨"Left", .string "other payload"⟩]⟩
def otherModule : Module upstreamLimits := ⟨otherRaw, by decide⟩
def repeatedExportCatalog : Catalog upstreamLimits := ⟨[pairModule, otherModule], by decide⟩

/-- Equal export spellings in distinct module namespaces are permitted and
resolve to their own complete specifications. -/
theorem repeated_export_spelling_is_qualified :
    lookupExport? repeatedExportCatalog "Pair" "Left" = some ⟨"Pair", "Left", payload⟩ ∧
    lookupExport? repeatedExportCatalog "Other" "Left" =
      some ⟨"Other", "Left", .string "other payload"⟩ := by decide

def changedModule : Module upstreamLimits :=
  ⟨{ pairRaw with exports := [⟨"Left", .string "changed payload"⟩] }, by decide⟩
def changedCatalog : Catalog upstreamLimits := ⟨[changedModule], by decide⟩

theorem retained_name_does_not_preserve_payload :
    lookupExport? changedCatalog "Pair" "Left" ≠ lookupExport? pairCatalog "Pair" "Left" := by decide

def emptySnapshot : Snapshot upstreamLimits := ⟨[], by decide⟩

def availablePair : AvailableModule snapshot := ⟨pairModule, by decide⟩

theorem snapshot_admission_accepts :
    decodeAvailable? snapshot pairValue = some availablePair := by decide

theorem snapshot_admission_rejects_missing :
    decodeAvailable? emptySnapshot pairValue = none := by decide

theorem snapshot_layer_roundtrip :
    (availableLayer upstreamLimits).elaborate snapshot
        ((availableLayer upstreamLimits).quote snapshot [availablePair]) = some [availablePair] :=
  (availableLayer upstreamLimits).elaborate_quote snapshot [availablePair]

theorem missing_dependencies_reject_authored_module :
    elaborateAvailable? emptySnapshot (.declaration pairValue) = none := by
  simp [elaborateAvailable?, DeclarationDocument.values, snapshot_admission_rejects_missing]

def checkedPair : CheckedCatalog snapshot := ⟨pairCatalog, by decide⟩

theorem combined_checks_roundtrip :
    (checkedCatalogLayer upstreamLimits).elaborate snapshot
        ((checkedCatalogLayer upstreamLimits).quote snapshot checkedPair) = some checkedPair :=
  (checkedCatalogLayer upstreamLimits).elaborate_quote snapshot checkedPair

theorem combined_checks_reject_missing_dependencies :
    elaborateCheckedCatalog? emptySnapshot (quoteModules upstreamLimits [pairModule]) = none := by
  have quoted : elaborateCatalog? upstreamLimits
      (quoteModules upstreamLimits [pairModule]) = some pairCatalog :=
    (catalogSystem upstreamLimits).elaboration.elaborate_quote pairCatalog
  simp only [elaborateCheckedCatalog?, quoted, Option.bind_some]
  have missing : ¬ CatalogAvailable emptySnapshot pairCatalog := by decide
  simp [admitCheckedCatalog?, missing]

theorem combined_checks_reject_module_name_collision :
    elaborateCheckedCatalog? snapshot (quoteModules upstreamLimits [pairModule, pairModule]) =
      none := by
  apply checkedCatalog_rejects_catalog_failure
  simp only [elaborateCatalog?, elaborate_quoteModules, Option.bind_some]
  have collision : ¬ distinctModules upstreamLimits [pairModule, pairModule] := by decide
  simp [admitCatalog?, collision]

theorem fully_checked_mixed_layer_roundtrip :
    (checkedModuleCalculusLayer upstreamLimits).elaborate (snapshot, termLanguage)
        ((checkedModuleCalculusLayer upstreamLimits).quote
          (snapshot, termLanguage) (checkedPair, proofCalculus)) =
      some (checkedPair, proofCalculus) :=
  checkedModuleCalculus_roundtrip upstreamLimits snapshot termLanguage checkedPair proofCalculus

def checkedBase : CheckedCatalog snapshot := ⟨baseCatalog, by decide⟩
def checkedCombined : CheckedCatalog snapshot := ⟨combinedCatalog, by decide⟩

theorem fully_checked_compatible_assembly :
    mergeCheckedCatalog? snapshot checkedPair checkedBase = some checkedCombined := by decide

theorem fully_checked_conflict_rejected :
    mergeCheckedCatalog? snapshot checkedPair checkedPair = none := by decide


/-! ## Portable presentation/text controls -/

namespace PortableText

open Mettapedia.GSLT.LanguageDef.CettaWire (Term)
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring (ImportContract)
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire.AuthoredRule.Controls

/-- The transport workload includes syntax operators, collection laws, binders,
scoped/quantified premises, explicit substitutions and rule-local dependencies.
Static language admission remains a separate operation. -/
def language : LanguageDef where
  name := "Portable λ\n\"scope\""
  types := [⟨"Name", .ast⟩, ⟨"Proc", .ast⟩, ⟨"Text", .builtinString⟩]
  terms := [
    { label := "Bind", category := "Proc",
      params := [.abstractionNamed (some "x") "body" (.arrow (.base "Name") (.base "Proc"))],
      syntaxPattern := [.terminal "bind", .nonTerminal "body",
        .op (.map (.zip "names" "bodies") ["name", "body"]
          [.op (.opt [.delimiter "(" ")"]), .separator ","])],
      evalPolicy? := some .rewrite },
    { label := "Par", category := "Proc",
      params := [.simple "parts" (.collection .hashBag (.base "Proc"))],
      syntaxPattern := [.op (.sep "parts" "|" (some (.var "parts")))],
      algebra? := some ⟨true, some "Nil"⟩ }]
  equations := [
    { name := "scope-equation", typeContext := annotatedRule.typeContext,
      premises := annotatedRule.premises, left := annotatedRule.left,
      right := annotatedRule.right, bindings := annotatedRule.bindings }]
  rewrites := [annotatedRule, annotatedRule]

def theory : ExtendedLanguageDef (calculusLayer.product exportLayer) where
  toLanguageDef := language
  extension := (proofCalculus, ["Proc", "Name"])

def codec := Portable.productCodec Portable.calculusCodec Portable.exportsCodec

def theoryText : String := Portable.renderTheory "calculus+exports/1" codec theory

theorem complete_scoped_text_roundtrip :
    Portable.readTheory? "calculus+exports/1" codec theoryText = some theory :=
  Portable.readTheory_renderTheory _ _ _

theorem rule_occurrences_survive :
    (Portable.readTheory? "calculus+exports/1" codec theoryText).map
      (fun read => read.rewrites.length) = some 2 := by
  rw [complete_scoped_text_roundtrip]
  rfl

theorem scoped_body_survives :
    (Portable.readTheory? "calculus+exports/1" codec theoryText).map
      (fun read => read.equations.head?.map Equation.right) =
      some (some (.lambda (some "display") (.subst (.bvar 1) (.bvar 0)))) := by
  rw [complete_scoped_text_roundtrip]
  rfl

theorem product_layers_survive :
    (Portable.readTheory? "calculus+exports/1" codec theoryText).map
      (fun read => read.extension) = some (proofCalculus, ["Proc", "Name"]) := by
  rw [complete_scoped_text_roundtrip]
  rfl

def origin : Term := .application "Origin" [.string "library/example", .natural 7]
def entry : Entry Term Term (ExtendedLanguageDef (calculusLayer.product exportLayer)) :=
  ⟨origin, .string "ProcessTheory", theory⟩
def otherOriginEntry : Entry Term Term (ExtendedLanguageDef (calculusLayer.product exportLayer)) :=
  { entry with origin := .application "Origin" [.string "library/other", .natural 7] }

theorem duplicate_source_entries_survive_text :
    Portable.readEntries? "calculus+exports/1" codec
      (Portable.renderEntries "calculus+exports/1" codec [entry, entry]) = some [entry, entry] :=
  Portable.readEntries_renderEntries _ _ _

theorem shared_origin_is_shared_only_at_admission :
    Portable.checkedEntries? .coherentOrigin
      (Portable.renderEntries "calculus+exports/1" codec [entry, entry]) =
      some [Portable.rawEntry "calculus+exports/1" codec entry] := by
  rw [Portable.checkedEntries_renderEntries]
  simp [ImportContract.check?, List.unionCompatible?, List.insertCompatible?]

private theorem label_collision (first second : Entry Term Term Term)
    (different : first ≠ second) (sameLabel : first.label = second.label) :
    ImportContract.coherentOrigin.check? [first, second] = none := by
  have incompatible : ImportContract.coherentOrigin.entryCompatible first second = false := by
    rw [ImportContract.coherentOrigin_formula]
    simp only [if_neg different, sameLabel]
    split <;> rfl
  simp [ImportContract.check?, List.unionCompatible?, List.insertCompatible?,
    Ne.symm different, incompatible]

theorem independent_origins_cannot_claim_one_label :
    Portable.checkedEntries? .coherentOrigin
      (Portable.renderEntries "calculus+exports/1" codec [entry, otherOriginEntry]) = none := by
  rw [Portable.checkedEntries_renderEntries]
  apply label_collision
  · intro same
    have origins := congrArg Entry.origin same
    have differentOrigins : origin ≠ otherOriginEntry.origin := by decide +kernel
    exact differentOrigins origins
  · rfl

theorem composition_uses_existing_join :
    Portable.checkedEntries? .coherentOrigin
      (Portable.renderEntries "calculus+exports/1" codec ([entry] ++ [otherOriginEntry])) =
      ImportContract.coherentOrigin.join?
        [Portable.rawEntry "calculus+exports/1" codec entry]
        [Portable.rawEntry "calculus+exports/1" codec otherOriginEntry] :=
  Portable.checkedEntries_append _ _ _ _ _

def module : Module upstreamLimits :=
  ⟨⟨"PortableScoped", [], [⟨"ProcessTheory",
    Portable.specification "calculus+exports/1" codec theory⟩]⟩, by decide⟩

def moduleText : String := renderText upstreamLimits module

theorem envelope_and_full_payload_roundtrip :
    readText? upstreamLimits moduleText = some module := readText_renderText _ _

theorem recovered_export_elaborates :
    (readText? upstreamLimits moduleText).bind (fun parsed =>
      parsed.val.exports.head?.bind (fun exported =>
        Portable.admitSpecification? "calculus+exports/1" codec exported.spec)) =
      some theory := by
  rw [envelope_and_full_payload_roundtrip]
  change Portable.admitSpecification? _ _ (Portable.specification _ _ theory) = some theory
  exact Portable.specification_roundtrip _ _ _

theorem wrong_layer_schema_is_not_reinterpreted :
    Portable.readTheory? "different-layer/1" codec theoryText = none := by
  exact Portable.readTheory_renderTheory_otherSchema _ _ _ _ _ (by decide)

theorem dropping_rules_changes_the_portable_presentation :
    NativeAuthoring.Wire.language language ≠ NativeAuthoring.Wire.language
      { language with rewrites := [] } := by
  intro same
  have := congrArg LanguageDef.rewrites (NativeAuthoring.Wire.language_injective same)
  cases this

theorem capturing_a_bound_slot_changes_text :
    Text.render (InferenceCettaWire.encodePattern (.lambda none (.bvar 1))) ≠
      Text.render (InferenceCettaWire.encodePattern (.lambda none (.bvar 0))) := by
  intro same
  have patterns := InferenceCettaWire.encodePattern_injective (Text.render_injective same)
  cases patterns

/-- Executable lexical refusal controls complement the structural theorems. -/
def refusedTextSamples : List String := [
  "(module:document (LanguageDefV2",
  "!(module:document 7)",
  "(module:document 7)\n(module:document 8)",
  "(module:document (module:codepoints (LCons 1114112 LNil)))"]

#guard refusedTextSamples.all (fun source => (Text.read? source).isNone)

theorem unicode_quotes_and_newlines_roundtrip :
    Text.read? (Text.render (.string "λ\n\"scope\"\\x")) =
      some (.string "λ\n\"scope\"\\x") := Text.read_render _

theorem variable_looking_symbol_stays_data :
    Text.read? (Text.render (.symbol "$x")) = some (.symbol "$x") := Text.read_render _

theorem reserved_head_stays_a_constructor :
    Text.read? (Text.render (.application "module:codepoints" [.natural 4])) =
      some (.application "module:codepoints" [.natural 4]) := Text.read_render _

theorem byte_level_roundtrip :
    Text.readBytes? (Text.renderBytes (.string "scope λ")) =
      some (.string "scope λ") := Text.readBytes_renderBytes _

end PortableText

end Mettapedia.GSLT.LanguageDef.ModuleFormat.Controls
