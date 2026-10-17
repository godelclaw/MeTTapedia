import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.GSLT.LanguageDef.ExtensionComposition
import Mettapedia.GSLT.LanguageDef.StructuralCoproduct
import Mettapedia.GSLT.Parsing.GrammarPresentationTransport
import Mettapedia.Data.List.FiniteLookup
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OriginView
import Mettapedia.GSLT.LanguageDef.CettaWireEquality
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-!
# Native authoring of composable, complete language fragments

The shared `languageDef!` DSL already produces the canonical five-field
`LanguageDef`. Its fragments enter the existing calculus-extension monoid and
authored-document GSLT here. No declaration schema or extension operation is
duplicated. Ordered extension assembly is distinct from the origin-sensitive
shared-module join: an imported ancestor is supplied once, not deduplicated by
spelling.

Raw fragments may refer to sorts and constructors supplied by another fragment.
Assembly therefore precedes nullary-name resolution and whole-language
validation. This module proves composition of the actual full row data and
commutation with terminal-notation changes. It does not identify the Lean macro
reader with a source lexer or a packed parser for `.module` or English.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open CalculusLanguageExtension

/-- The two established shared-import contracts. Their declaration identities
are independent of the ordered rule occurrences in each body. -/
inductive ImportContract where
  | coherentOrigin
  | structuralView
  deriving Repr, DecidableEq

namespace ImportContract

universe u v w
variable {Origin : Type u} {Label : Type v} {Body : Type w}
  [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body]

def entryCompatible (contract : ImportContract) : Entry Origin Label Body → Entry Origin Label Body → Bool :=
  match contract with
  | .coherentOrigin => ModuleAlgebra.entryCompatible
  | .structuralView => OriginView.entryCompatible

theorem entryCompatible_self (contract : ImportContract) (entry : Entry Origin Label Body) :
    contract.entryCompatible entry entry = true := by
  cases contract <;> simp [entryCompatible]

theorem entryCompatible_symm (contract : ImportContract) (first second : Entry Origin Label Body) :
    contract.entryCompatible first second = contract.entryCompatible second first := by
  cases contract
  · exact ModuleAlgebra.entryCompatible_symm first second
  · exact OriginView.entryCompatible_symm first second

theorem coherentOrigin_formula (first second : Entry Origin Label Body) :
    ImportContract.coherentOrigin.entryCompatible first second =
      if first = second then true else
        if first.origin = second.origin then false else
          if first.label = second.label then false else true := by
  by_cases same : first = second <;>
    by_cases origin : first.origin = second.origin <;>
    by_cases label : first.label = second.label <;>
    simp [entryCompatible, ModuleAlgebra.entryCompatible, same, origin, label]

theorem structuralView_formula (first second : Entry Origin Label Body) :
    ImportContract.structuralView.entryCompatible first second =
      if first.label = second.label then decide (first = second) else true := by
  by_cases label : first.label = second.label <;>
    simp [entryCompatible, OriginView.entryCompatible, label]

def check? (contract : ImportContract) (entries : List (Entry Origin Label Body)) :
    Option (List (Entry Origin Label Body)) :=
  List.unionCompatible? contract.entryCompatible [] entries

def join? (contract : ImportContract) (first second : List (Entry Origin Label Body)) :
    Option (List (Entry Origin Label Body)) := contract.check? (first ++ second)

theorem check_isSome_iff (contract : ImportContract) (entries : List (Entry Origin Label Body)) :
    (contract.check? entries).isSome = true ↔
      match contract with
      | .coherentOrigin => ModuleAlgebra.Valid entries.toFinset
      | .structuralView => OriginView.Valid entries.toFinset := by
  cases contract
  · exact ModuleAlgebra.orderedCheck_isSome_iff entries
  · exact OriginView.orderedCheck_isSome_iff entries

theorem join_toFinset (contract : ImportContract)
    (first second result : List (Entry Origin Label Body))
    (joined : contract.join? first second = some result) :
    result.toFinset = first.toFinset ∪ second.toFinset := by
  simpa only [List.toFinset_nil, Finset.empty_union, List.toFinset_append] using
    List.unionCompatible?_toFinset contract.entryCompatible [] (first ++ second) result joined

/-- The physical import selector names its contract explicitly. -/
def wireTerm : ImportContract → CettaWire.Term
  | .coherentOrigin => .symbol "CoherentOriginV1"
  | .structuralView => .symbol "StructuralOriginViewV1"

end ImportContract

/-- Lossless physical declaration data. Its body may be a complete language
fragment; the import checker never executes that body. -/
def importEntryTerm (entry : Entry CettaWire.Term CettaWire.Term CettaWire.Term) : CettaWire.Term :=
  .application "ModuleEntry" [entry.origin, entry.label, entry.body]

def decodeImportEntry? : CettaWire.Term →
    Option (Entry CettaWire.Term CettaWire.Term CettaWire.Term)
  | .application "ModuleEntry" [origin, label, body] => some ⟨origin, label, body⟩
  | _ => none

@[simp] theorem decodeImportEntry_importEntryTerm
    (entry : Entry CettaWire.Term CettaWire.Term CettaWire.Term) :
    decodeImportEntry? (importEntryTerm entry) = some entry := by
  cases entry
  rfl

theorem importEntryTerm_injective : Function.Injective importEntryTerm := by
  intro first second same
  have decoded := congrArg decodeImportEntry? same
  simpa only [decodeImportEntry_importEntryTerm, Option.some.injEq] using decoded

@[simp] theorem importEntryTerm_eq
    (first second : Entry CettaWire.Term CettaWire.Term CettaWire.Term) :
    importEntryTerm first = importEntryTerm second ↔ first = second :=
  importEntryTerm_injective.eq_iff

abbrev Document := DeclarationDocument CalculusLanguageExtension

/-- Fold through the existing extension composition, retaining every row. -/
def combine (extensions : List CalculusLanguageExtension) : CalculusLanguageExtension :=
  extensions.foldr CalculusLanguageExtension.comp CalculusLanguageExtension.empty

theorem combine_append (first second : List CalculusLanguageExtension) :
    combine (first ++ second) = (combine first).comp (combine second) := by
  induction first with
  | nil => simp [combine, empty_comp]
  | cons head tail ih =>
      simpa only [List.cons_append, combine, List.foldr_cons,
        CalculusLanguageExtension.comp_assoc] using
        congrArg (CalculusLanguageExtension.comp head) ih

def compileDelta (document : Document) : CalculusLanguageExtension := combine document.values

@[simp] theorem compileDelta_declaration (extension : CalculusLanguageExtension) :
    compileDelta (.declaration extension) = extension := by
  simp [compileDelta, combine, DeclarationDocument.values, comp_empty]

theorem compileDelta_bundle_pair (first second : Document) :
    compileDelta (.bundle [first, second]) =
      (compileDelta first).comp (compileDelta second) := by
  simp only [compileDelta, DeclarationDocument.values, DeclarationDocument.valuesList,
    List.append_nil]
  exact combine_append _ _

/-- The same authored GSLT used by other declaration interfaces, interpreted
by the existing extension monoid rather than a new module container. -/
def system : GSLT.CompositionalElaboration CalculusLanguageExtension where
  authoring := ExactDeclarationCodec.documentCompositional CalculusLanguageExtension
  elaboration := {
    elaborate := fun document => some (compileDelta document)
    quote := DeclarationDocument.declaration
    elaborate_quote := by intro extension; simp
    equation := by
      intro first second same
      change first.values = second.values at same
      simp only [compileDelta, same]
    rewrite := by intro first second impossible; exact False.elim impossible }
  emptyPayload := CalculusLanguageExtension.empty
  merge := fun first second => some (first.comp second)
  elaborate_empty := by
    change some (compileDelta (.bundle [])) = some CalculusLanguageExtension.empty
    simp [compileDelta, combine, DeclarationDocument.values, DeclarationDocument.valuesList]
  elaborate_append := by
    intro first second
    change some (compileDelta (.bundle [first, second])) = _
    exact congrArg some (compileDelta_bundle_pair first second)

def layer (Base : Type) : CompositionalLayer Base where
  Fiber := fun _ => CalculusLanguageExtension
  system := fun _ => system

def coGSLT (Base : Type) : CoGSLTLayer Base := (layer Base).toCoGSLTLayer

def compile (base : CalculusLanguageDef) (document : Document) : CalculusLanguageDef :=
  (compileDelta document).apply base

/-- Applying a separately assembled suffix agrees with assembling both
documents first, including every inference row and the base conversion. -/
theorem compile_bundle_pair (base : CalculusLanguageDef) (first second : Document) :
    compile base (.bundle [first, second]) = compile (compile base first) second := by
  rw [compile, compileDelta_bundle_pair, comp_apply]
  rfl

theorem compile_equivalent (base : CalculusLanguageDef) (first second : Document)
    (same : first.values = second.values) : compile base first = compile base second := by
  simp only [compile, compileDelta, same]

theorem compile_appendOnly (base : CalculusLanguageDef) (document : Document) :
    AppendOnlyCalculusRefinement base (compile base document) :=
  apply_appendOnly _ _

/-- Whole-calculus admission is performed after raw extension assembly. -/
def admitCalculus? (base : CalculusLanguageDef) (document : Document) :
    Option ValidatedCalculusLanguageDef :=
  let target := compile base document
  if valid : target.isValid = true then some ⟨target, valid⟩ else none

theorem admitCalculus_isSome_iff (base : CalculusLanguageDef) (document : Document) :
    (admitCalculus? base document).isSome = true ↔ (compile base document).isValid = true := by
  unfold admitCalculus?
  dsimp only
  split <;> simp_all

/-- A core fragment contributes all four row families; its local display
name does not override the assembled language's name. -/
def coreDelta (language : LanguageDef) : CalculusLanguageExtension where
  newTypes := language.types
  newTerms := language.terms
  newEquations := language.equations
  newRewrites := language.rewrites

theorem combine_coreDeltas (languages : List LanguageDef) :
    combine (languages.map coreDelta) =
      { newTypes := languages.flatMap (·.types)
        newTerms := languages.flatMap (·.terms)
        newEquations := languages.flatMap (·.equations)
        newRewrites := languages.flatMap (·.rewrites) } := by
  induction languages with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, combine, List.foldr_cons] at *
      rw [ih]
      simp [coreDelta, CalculusLanguageExtension.comp]

def assembleRaw (langName : String) (fragments : List LanguageDef) : LanguageDef :=
  ((combine (fragments.map coreDelta)).apply
    { toLanguageDef := LanguageDef.empty langName }).toLanguageDef

/-- An independently stated complete-row specification for native assembly. -/
theorem assembleRaw_rows (langName : String) (fragments : List LanguageDef) :
    assembleRaw langName fragments =
      { «name» := langName
        «types» := fragments.flatMap (·.types)
        «terms» := fragments.flatMap (·.terms)
        «equations» := fragments.flatMap (·.equations)
        «rewrites» := fragments.flatMap (·.rewrites) } := by
  simp [assembleRaw, combine_coreDeltas, CalculusLanguageExtension.apply, LanguageDef.empty]

theorem assembleRaw_staged (langName : String) (first second : List LanguageDef) :
    assembleRaw langName (first ++ second) =
      assembleRaw langName [assembleRaw langName first, assembleRaw langName second] := by
  simp [assembleRaw_rows, List.flatMap_append]

/-- A rule's fragment and local row address relocates to one physical authored
row in the assembled language. Repeated fragments retain repeated rows. -/
def assembleRaw_rewriteIndex (langName : String) (fragments : List LanguageDef)
    (occurrence : (fragment : Fin fragments.length) ×
      Fin fragments[fragment].rewrites.length) :
    Fin (assembleRaw langName fragments).rewrites.length :=
  Fin.cast (by simp only [assembleRaw_rows])
    (List.flatMapIndex (·.rewrites) fragments occurrence)

theorem assembleRaw_rewriteIndex_row (langName : String) (fragments : List LanguageDef)
    (occurrence : (fragment : Fin fragments.length) ×
      Fin fragments[fragment].rewrites.length) :
    (assembleRaw langName fragments).rewrites[assembleRaw_rewriteIndex langName fragments occurrence] =
      fragments[occurrence.1].rewrites[occurrence.2] := by
  simpa only [assembleRaw_rows, assembleRaw_rewriteIndex, Fin.getElem_fin, Fin.val_cast] using
    List.getElem_flatMapIndex (·.rewrites) fragments occurrence

theorem assembleRaw_rewriteIndex_bijective (langName : String) (fragments : List LanguageDef) :
    Function.Bijective (assembleRaw_rewriteIndex langName fragments) := by
  have bijective := (List.flatMapIndexEquiv (·.rewrites) fragments).bijective
  exact (Fin.castOrderIso (by simp only [assembleRaw_rows])).bijective.comp bijective

/-- Empty fragments and duplicate rows do not merge physical occurrences. -/
theorem assembleRaw_duplicate_rewrite_occurrences (rule : RewriteRule) :
    let fragment : LanguageDef :=
      { «name» := "Part", «types» := [], «terms» := [], «equations» := [], «rewrites» := [rule, rule] }
    let fragments := [fragment, LanguageDef.empty "Empty", fragment]
    (assembleRaw "Whole" fragments).rewrites = [rule, rule, rule, rule] ∧
      (assembleRaw_rewriteIndex "Whole" fragments
        ⟨⟨0, by change (0 : Nat) < 3; decide⟩, ⟨1, by change (1 : Nat) < 2; decide⟩⟩).val = 1 ∧
      (assembleRaw_rewriteIndex "Whole" fragments
        ⟨⟨2, by change (2 : Nat) < 3; decide⟩, ⟨1, by change (1 : Nat) < 2; decide⟩⟩).val = 3 := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms assembleRaw_rewriteIndex_row
#print axioms assembleRaw_rewriteIndex_bijective
#print axioms assembleRaw_duplicate_rewrite_occurrences

/-- Decompose the real core into independent syntax, equality, and reduction
fragments. This does not make the fragments individually closed or valid. -/
def splitCore (language : LanguageDef) : List LanguageDef :=
  [ { language with «equations» := [], «rewrites» := [] },
    { «name» := language.name, «types» := [], «terms» := [],
      «equations» := language.equations, «rewrites» := [] },
    { «name» := language.name, «types» := [], «terms» := [],
      «equations» := [], «rewrites» := language.rewrites } ]

theorem assembleRaw_splitCore (language : LanguageDef) :
    assembleRaw language.name (splitCore language) = language := by
  cases language
  simp [assembleRaw_rows, splitCore]

/-- Existing structural coproducts and native ordered assembly use exactly
the same full declarations after the selected symbol renamings. -/
theorem assembleRaw_coproduct (langName : String) (leftSymbols rightSymbols : LanguageDefSymbolMap)
    (left right : LanguageDef) :
    assembleRaw langName
      [StructuralCoproduct.renameLanguage (langName ++ ".left") leftSymbols left,
       StructuralCoproduct.renameLanguage (langName ++ ".right") rightSymbols right] =
      StructuralCoproduct.rawCoproduct langName leftSymbols rightSymbols left right := by
  simp [assembleRaw_rows, StructuralCoproduct.rawCoproduct]

/-- Resolve imported nullary names only after the full signature is present. -/
def assemble (langName : String) (fragments : List LanguageDef) : LanguageDef :=
  (assembleRaw langName fragments).resolveNullaryPatterns

theorem assemble_clean (langName : String) (fragments : List LanguageDef)
    (clean : (assembleRaw langName fragments).resolveNullaryClean = true) :
    assemble langName fragments = assembleRaw langName fragments :=
  LanguageDef.resolveNullaryPatterns_eq_self_of_clean _ clean

def admitCore? (langName : String) (fragments : List LanguageDef) : Option ValidatedLanguageDef :=
  let language := assemble langName fragments
  if valid : language.validate = [] then some ⟨language, valid⟩ else none

theorem admitCore_isSome_iff (langName : String) (fragments : List LanguageDef) :
    (admitCore? langName fragments).isSome = true ↔ (assemble langName fragments).validate = [] := by
  unfold admitCore?
  dsimp only
  split <;> simp_all

open Parsing.GrammarPresentationTransport

theorem mapLanguage_assembleRaw (tokens : String ≃ String) (langName : String)
    (fragments : List LanguageDef) :
    mapLanguage tokens (assembleRaw langName fragments) =
      assembleRaw langName (fragments.map (mapLanguage tokens)) := by
  simp [assembleRaw_rows, mapLanguage, List.flatMap_map, List.map_flatMap]

theorem mapLanguage_nullaryLabels (tokens : String ≃ String) (language : LanguageDef) :
    (mapLanguage tokens language).nullaryLabels = language.nullaryLabels := by
  simp [LanguageDef.nullaryLabels, mapLanguage, mapRule, List.filterMap_map,
    Function.comp_def]
  rfl

theorem mapLanguage_resolveNullary (tokens : String ≃ String) (language : LanguageDef) :
    mapLanguage tokens language.resolveNullaryPatterns =
      (mapLanguage tokens language).resolveNullaryPatterns := by
  unfold LanguageDef.resolveNullaryPatterns
  rw [mapLanguage_nullaryLabels]
  rfl

/-- Terminal changes commute with actual assembly and final name resolution.
No grammatical equivalence is silently upgraded to an operational one. -/
theorem mapLanguage_assemble (tokens : String ≃ String) (langName : String)
    (fragments : List LanguageDef) :
    mapLanguage tokens (assemble langName fragments) =
      assemble langName (fragments.map (mapLanguage tokens)) := by
  rw [assemble, mapLanguage_resolveNullary, mapLanguage_assembleRaw]
  rfl


/-! ## Complete portable core rows

The physical carrier is shared with inference packages. These codecs add only
the missing presentation rows: syntax operators, constructor policies,
collection algebras, equations and the five-field language. Binding patterns,
premises and occurrence substitutions retain their existing codecs.
-/

namespace Wire

open Mettapedia.GSLT.LanguageDef.CettaWire (Term encodeList decodeList decodeList_encodeList)
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire (encodePattern decodePattern)
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire.AuthoredRule

private def string? : Term → Option String
  | .string value => some value
  | _ => none

private def boolean : Bool → Term
  | true => .symbol "True"
  | false => .symbol "False"

private def boolean? : Term → Option Bool
  | .symbol "True" => some true
  | .symbol "False" => some false
  | _ => none

@[simp] private theorem boolean_roundtrip (value : Bool) :
    boolean? (boolean value) = some value := by cases value <;> rfl

def carrier : CarrierKind → Term
  | .ast => .symbol "CarrierAst"
  | .tokenLabel => .symbol "CarrierTokenLabel"
  | .tokenRaw => .symbol "CarrierTokenRaw"
  | .tokenProof => .symbol "CarrierTokenProof"
  | .tokenPath => .symbol "CarrierTokenPath"
  | .builtinInt => .symbol "CarrierBuiltinInt"
  | .builtinString => .symbol "CarrierBuiltinString"
  | .builtinBool => .symbol "CarrierBuiltinBool"

def carrier? : Term → Option CarrierKind
  | .symbol "CarrierAst" => some .ast
  | .symbol "CarrierTokenLabel" => some .tokenLabel
  | .symbol "CarrierTokenRaw" => some .tokenRaw
  | .symbol "CarrierTokenProof" => some .tokenProof
  | .symbol "CarrierTokenPath" => some .tokenPath
  | .symbol "CarrierBuiltinInt" => some .builtinInt
  | .symbol "CarrierBuiltinString" => some .builtinString
  | .symbol "CarrierBuiltinBool" => some .builtinBool
  | _ => none

@[simp] theorem carrier_roundtrip (value : CarrierKind) :
    carrier? (carrier value) = some value := by cases value <;> rfl

def typeDecl (value : TypeDecl) : Term :=
  .application "TypeDecl" [.string value.name, carrier value.carrier]

def typeDecl? : Term → Option TypeDecl
  | .application "TypeDecl" [.string name, kind] => do
      pure ⟨name, ← carrier? kind⟩
  | _ => none

@[simp] theorem typeDecl_roundtrip (value : TypeDecl) :
    typeDecl? (typeDecl value) = some value := by cases value; simp [typeDecl, typeDecl?]

mutual
  def syntaxItem : SyntaxItem → Term
    | .terminal text => .application "Terminal" [.string text]
    | .nonTerminal name => .application "NonTerminal" [.string name]
    | .separator text => .application "Separator" [.string text]
    | .delimiter left right => .application "Delimiter" [.string left, .string right]
    | .op operation => .application "SyntaxOp" [syntaxOp operation]

  def syntaxOp : SyntaxPatternOp → Term
    | .var name => .application "SyntaxVar" [.string name]
    | .sep name separator body =>
        .application "SyntaxSep" [.string name, .string separator, optionalSyntaxOp body]
    | .zip left right => .application "SyntaxZip" [.string left, .string right]
    | .map body names items =>
        .application "SyntaxMap" [syntaxOp body, encodeList .string names, syntaxItems items]
    | .opt items => .application "SyntaxOpt" [syntaxItems items]

  def optionalSyntaxOp : Option SyntaxPatternOp → Term
    | none => .symbol "None"
    | some operation => .application "Some" [syntaxOp operation]

  def syntaxItems : List SyntaxItem → Term
    | [] => .symbol "LNil"
    | item :: items => .application "LCons" [syntaxItem item, syntaxItems items]
end

mutual
  def syntaxItem? : Term → Option SyntaxItem
    | .application "Terminal" [.string text] => some (.terminal text)
    | .application "NonTerminal" [.string name] => some (.nonTerminal name)
    | .application "Separator" [.string text] => some (.separator text)
    | .application "Delimiter" [.string left, .string right] => some (.delimiter left right)
    | .application "SyntaxOp" [operation] => .op <$> syntaxOp? operation
    | _ => none
  termination_by value => sizeOf value

  def syntaxOp? : Term → Option SyntaxPatternOp
    | .application "SyntaxVar" [.string name] => some (.var name)
    | .application "SyntaxSep" [.string name, .string separator, body] => do
        pure (.sep name separator (← optionalSyntaxOp? body))
    | .application "SyntaxZip" [.string left, .string right] => some (.zip left right)
    | .application "SyntaxMap" [body, names, items] => do
        pure (.map (← syntaxOp? body) (← decodeList string? names) (← syntaxItems? items))
    | .application "SyntaxOpt" [items] => .opt <$> syntaxItems? items
    | _ => none
  termination_by value => sizeOf value

  def optionalSyntaxOp? : Term → Option (Option SyntaxPatternOp)
    | .symbol "None" => some none
    | .application "Some" [operation] => some <$> syntaxOp? operation
    | _ => none
  termination_by value => sizeOf value

  def syntaxItems? : Term → Option (List SyntaxItem)
    | .symbol "LNil" => some []
    | .application "LCons" [item, items] => do
        pure ((← syntaxItem? item) :: (← syntaxItems? items))
    | _ => none
  termination_by value => sizeOf value
end

private theorem strings_roundtrip (names : List String) :
    decodeList string? (encodeList Term.string names) = some names :=
  decodeList_encodeList string? Term.string (fun _ => rfl) names

mutual
  @[simp] theorem syntaxItem_roundtrip (value : SyntaxItem) :
      syntaxItem? (syntaxItem value) = some value := by
    cases value with
    | terminal text => simp only [syntaxItem, syntaxItem?]
    | nonTerminal name => simp only [syntaxItem, syntaxItem?]
    | separator text => simp only [syntaxItem, syntaxItem?]
    | delimiter left right => simp only [syntaxItem, syntaxItem?]
    | op operation => simp [syntaxItem, syntaxItem?, syntaxOp_roundtrip operation]
  termination_by sizeOf value

  @[simp] theorem syntaxOp_roundtrip (value : SyntaxPatternOp) :
      syntaxOp? (syntaxOp value) = some value := by
    cases value with
    | var name => simp only [syntaxOp, syntaxOp?]
    | sep name separator body =>
        simp [syntaxOp, syntaxOp?, optionalSyntaxOp_roundtrip body]
    | zip left right => simp only [syntaxOp, syntaxOp?]
    | map body names items =>
        simp [syntaxOp, syntaxOp?, syntaxOp_roundtrip body,
          strings_roundtrip, syntaxItems_roundtrip items]
    | opt items => simp [syntaxOp, syntaxOp?, syntaxItems_roundtrip items]
  termination_by sizeOf value

  @[simp] theorem optionalSyntaxOp_roundtrip (value : Option SyntaxPatternOp) :
      optionalSyntaxOp? (optionalSyntaxOp value) = some value := by
    cases value with
    | none => simp only [optionalSyntaxOp, optionalSyntaxOp?]
    | some operation =>
        simp [optionalSyntaxOp, optionalSyntaxOp?, syntaxOp_roundtrip operation]
  termination_by sizeOf value

  @[simp] theorem syntaxItems_roundtrip (value : List SyntaxItem) :
      syntaxItems? (syntaxItems value) = some value := by
    cases value with
    | nil => simp only [syntaxItems, syntaxItems?]
    | cons item items =>
        simp [syntaxItems, syntaxItems?, syntaxItem_roundtrip item, syntaxItems_roundtrip items]
  termination_by sizeOf value
end

def policy : Option TermEvalPolicy → Term
  | none => .symbol "EvalNone"
  | some .rewrite => .symbol "EvalRewrite"
  | some .fold => .symbol "EvalFold"
  | some .oracle => .symbol "EvalOracle"

def policy? : Term → Option (Option TermEvalPolicy)
  | .symbol "EvalNone" => some none
  | .symbol "EvalRewrite" => some (some .rewrite)
  | .symbol "EvalFold" => some (some .fold)
  | .symbol "EvalOracle" => some (some .oracle)
  | _ => none

@[simp] theorem policy_roundtrip (value : Option TermEvalPolicy) :
    policy? (policy value) = some value := by
  cases value with
  | none => rfl
  | some value => cases value <;> rfl

def algebra : Option CollectionAlgebra → Term
  | none => .symbol "AlgebraNone"
  | some value => .application "CollectionAlgebra"
      [boolean value.flatten, InferenceCettaWire.encodeBinder value.unit]

def algebra? : Term → Option (Option CollectionAlgebra)
  | .symbol "AlgebraNone" => some none
  | .application "CollectionAlgebra" [flatten, unit] => do
      pure (some ⟨← boolean? flatten, ← InferenceCettaWire.decodeBinder unit⟩)
  | _ => none

@[simp] theorem algebra_roundtrip (value : Option CollectionAlgebra) :
    algebra? (algebra value) = some value := by
  cases value with
  | none => rfl
  | some value => cases value; simp [algebra, algebra?]

def grammarRule (value : GrammarRule) : Term :=
  .application "GrammarRuleV2" [.string value.label, .string value.category,
    encodeList parameterTerm value.params, syntaxItems value.syntaxPattern,
    policy value.evalPolicy?, algebra value.algebra?]

def grammarRule? : Term → Option GrammarRule
  | .application "GrammarRuleV2" [.string label, .string category, params, syntaxRows, evaluation, laws] => do
      pure ⟨label, category, ← decodeList decodeParameter? params, ← syntaxItems? syntaxRows,
        ← policy? evaluation, ← algebra? laws⟩
  | _ => none

@[simp] theorem grammarRule_roundtrip (value : GrammarRule) :
    grammarRule? (grammarRule value) = some value := by
  cases value
  simp [grammarRule, grammarRule?, decodeList_encodeList]

def equation (value : Equation) : Term :=
  .application "ScopedEquationV1" [.string value.name,
    encodeList typeBindingTerm value.typeContext, encodeList premiseTerm value.premises,
    encodePattern value.left, encodePattern value.right, optionalBindingTerm value.bindings]

def equation? : Term → Option Equation
  | .application "ScopedEquationV1" [.string name, context, premises, left, right, bindings] => do
      pure ⟨name, ← decodeList decodeTypeBinding? context, ← decodeList decodePremise? premises,
        ← decodePattern left, ← decodePattern right, ← decodeOptionalBinding? bindings⟩
  | _ => none

@[simp] theorem equation_roundtrip (value : Equation) :
    equation? (equation value) = some value := by
  cases value
  simp [equation, equation?, decodeList_encodeList]

/-- Complete finite presentation data, before any execution-profile admission. -/
def language (value : LanguageDef) : Term :=
  .application "LanguageDefV2" [.string value.name,
    encodeList typeDecl value.types, encodeList grammarRule value.terms,
    encodeList equation value.equations, encodeList rewriteTerm value.rewrites]

def language? : Term → Option LanguageDef
  | .application "LanguageDefV2" [.string name, types, terms, equations, rewrites] => do
      pure ⟨name, ← decodeList typeDecl? types, ← decodeList grammarRule? terms,
        ← decodeList equation? equations, ← decodeList decodeRewrite? rewrites⟩
  | _ => none

@[simp] theorem language_roundtrip (value : LanguageDef) :
    language? (language value) = some value := by
  cases value
  simp [language, language?, decodeList_encodeList]

/-- Bound indices, display names and rule-local occurrence substitutions are not
quotiented away at this boundary. -/
theorem language_injective : Function.Injective language := by
  intro first second same
  have := congrArg language? same
  simpa only [language_roundtrip, Option.some.injEq] using this

end Wire

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring
