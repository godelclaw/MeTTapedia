import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConstantInterpretation
import Mettapedia.OSLF.Syntax.SignatureMorphismReadback
import Mettapedia.GSLT.LanguageDef.ScopedBindingElaboration
import Mettapedia.OSLF.NativeTypes.Instances.LetCase.Language
import Mettapedia.GSLT.LanguageDef.BindingSignatureSubstitution
import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarations
import Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingSourceChecking
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeAdequacy
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.BindingSignatureEmbedding
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.BindingSignatureInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeJoins
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity

/-!
# Finite authored binding declarations in the cumulative native calculus

Existing decoded base and arrow headers determine one finite native
environment. Every function carrier and constructor type receives actual
formation in that environment, with its original declaration position retained.

The curried binding specialization proves agreement of those independently
decoded parameter types with their complete binding telescopes. Its original
scoped source parser and the checked signature reader recover finite terms
with literal pattern readback, retaining binder spines and variable positions.

The functional interpretation retains base and arrow carriers. Every admitted
binding operator earns a native type from the same finite headers. Structural
abstraction and explicit substitution use derived closed native programs;
substitution executes to the compiled original capture-avoiding instance, with
finite replay evidence and literal raw-source readback. Functional results may
still contain operators whose hidden inputs lie outside this carrier fragment;
the partial reader does not assume global coverage of those operations.

Formation admission and rule authority remain distinct. Matching, conditional
premises, operational observations and equation authority retain their original
source judgments; declaration formation does not supply those facts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration
open BindingSignatureEmbedding

/-- Finite declaration positions determine structural native names. -/
def sortDeclName (language : LanguageDef) (position : Fin language.types.length) : DeclName :=
  .num (.str (.str .anonymous language.name) "GSLT.authored.sort") position.val

def constructorDeclName (language : LanguageDef) (position : Fin language.terms.length) : DeclName :=
  .num (.str (.str .anonymous language.name) "GSLT.authored.constructor") position.val

theorem sortDeclName_injective (language : LanguageDef) :
    Function.Injective (sortDeclName language) := by
  intro first second same
  apply Fin.ext
  exact (Lean.Name.num.inj same).2

theorem constructorDeclName_injective (language : LanguageDef) :
    Function.Injective (constructorDeclName language) := by
  intro first second same
  apply Fin.ext
  exact (Lean.Name.num.inj same).2

theorem constructor_ne_sort (language : LanguageDef)
    (constructor : Fin language.terms.length) (sort : Fin language.types.length) :
    constructorDeclName language constructor ≠ sortDeclName language sort := by
  simp [constructorDeclName, sortDeclName]

/-- Original decoded arrow carriers become actual native function types. -/
def carrierType {language : LanguageDef} : NativeSignature.Carrier language → Tower.Tm 0
  | .sort position => .const (sortDeclName language position)
  | .function domain codomain => closedArrow (carrierType domain) (carrierType codomain)

def parameterTypes {language : LanguageDef} :
    List (NativeSignature.Carrier language) → Tower.Tm 0 → Tower.Tm 0
  | [], result => result
  | parameter :: parameters, result =>
      closedArrow (carrierType parameter) (parameterTypes parameters result)

def headerType {language : LanguageDef} (header : NativeSignature.Header language) : Tower.Tm 0 :=
  parameterTypes header.parameters (.const (sortDeclName language header.result))

def sortEntry : Entry Tower.Head := ⟨.head (.sort Tower.zero), none⟩

def headerEntry {language : LanguageDef} (header : NativeSignature.Header language) : Entry Tower.Head :=
  ⟨headerType header, none⟩

def sortDeclarations (language : LanguageDef) : List (DeclName × Entry Tower.Head) :=
  List.ofFn (fun position => (sortDeclName language position, sortEntry))

namespace Headers

variable {language : LanguageDef}

def constructorDeclarations (source : NativeSignature.Installation language) :
    List (DeclName × Entry Tower.Head) :=
  List.ofFn (fun position : source.Constructor =>
    (constructorDeclName language (source.origin position), headerEntry source.headers[position]))

def declarationList (source : NativeSignature.Installation language) : List (DeclName × Entry Tower.Head) :=
  sortDeclarations language ++ constructorDeclarations source

def signature (source : NativeSignature.Installation language) : Signature Tower.Head :=
  .ofList (declarationList source)

def rules (source : NativeSignature.Installation language) : Rules Tower.Head :=
  extendRules Tower.rules (signature source)

theorem origin_position (source : NativeSignature.Installation language) (position : source.Constructor) :
    (source.origin position).val = position.val := by
  have related := source.constructor_correspondence.get (i := position.val)
    (by rw [List.length_finRange, ← source.constructor_count]; exact position.isLt) position.isLt
  have equal := related.1
  simpa only [List.get_eq_getElem, List.getElem_finRange, Fin.getElem_fin, Fin.val_mk, Fin.val_cast, NativeSignature.Installation.origin] using congrArg Fin.val equal

theorem origin_injective (source : NativeSignature.Installation language) :
    Function.Injective source.origin := by
  intro first second same
  apply Fin.ext
  rw [← origin_position source first, ← origin_position source second]
  exact congrArg Fin.val same

theorem sort_lookup (source : NativeSignature.Installation language) (sort : Fin language.types.length) :
    (signature source).entries (sortDeclName language sort) = some sortEntry := by
  rw [signature, declarationList, Signature.entries_ofList_append, sortDeclarations,
    Signature.entries_ofFn (sortDeclName language) (fun _ => sortEntry)
      (sortDeclName_injective language) sort]
  rfl

private theorem lookup_none {Head : Type} (entries : List (DeclName × Entry Head))
    (name : DeclName) (missing : ∀ entry ∈ entries, name ≠ entry.1) :
    (Signature.ofList entries).entries name = none := by
  induction entries with
  | nil => rfl
  | cons entry entries inductionHypothesis =>
      simp only [Signature.ofList, List.foldr, Signature.insert]
      rw [if_neg (missing entry List.mem_cons_self)]
      exact inductionHypothesis (fun value member => missing value (List.mem_cons_of_mem _ member))

theorem constructor_lookup (source : NativeSignature.Installation language) (position : source.Constructor) :
    (signature source).entries (constructorDeclName language (source.origin position)) =
      some (headerEntry source.headers[position]) := by
  have noSort : (Signature.ofList (sortDeclarations language)).entries
      (constructorDeclName language (source.origin position)) = none := by
    apply lookup_none
    intro entry member
    obtain ⟨sort, rfl⟩ := List.mem_ofFn.mp member
    exact constructor_ne_sort language (source.origin position) sort
  rw [signature, declarationList, Signature.entries_ofList_append, noSort]
  exact Signature.entries_ofFn (fun position => constructorDeclName language (source.origin position))
    (fun position => headerEntry source.headers[position])
    ((constructorDeclName_injective language).comp (origin_injective source)) position

private theorem closedArrow_formed (source : NativeSignature.Installation language)
    {domain codomain : Tower.Tm 0}
    (domainFormed : FormationSensitive.Typing (rules source) .nil domain (.head (.sort Tower.zero)))
    (codomainFormed : FormationSensitive.Typing (rules source) .nil codomain (.head (.sort Tower.zero))) :
    FormationSensitive.Typing (rules source) .nil (closedArrow domain codomain) (.head (.sort Tower.zero)) := by
  have lifted := codomainFormed.renameTyping (Δ := .snoc .nil domain) (ρ := Fin.elim0)
    (fun index => Fin.elim0 index)
  apply FormationSensitive.Typing.cumul
    (.piForm domainFormed (.sort Tower.zero) lifted (.sort Tower.zero) (.sorts Tower.zero Tower.zero))
  intro valuation
  simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval, Tower.zero, LevelTower.zero]

theorem sortType_formed (source : NativeSignature.Installation language) (sort : Fin language.types.length) :
    FormationSensitive.Typing (rules source) .nil (.const (sortDeclName language sort)) (.head (.sort Tower.zero)) := by
  exact FormationSensitive.Typing.const (R := rules source) (by change (signature source).typeOf? _ = _; rw [Signature.typeOf?, sort_lookup source]; rfl)
    (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))

theorem carrierType_formed (source : NativeSignature.Installation language) (carrier : NativeSignature.Carrier language) :
    FormationSensitive.Typing (rules source) .nil (carrierType carrier) (.head (.sort Tower.zero)) := by
  induction carrier with
  | sort position => exact sortType_formed source position
  | function domain codomain domainIH codomainIH =>
      exact closedArrow_formed source domainIH codomainIH

theorem parameterTypes_formed (source : NativeSignature.Installation language)
    (parameters : List (NativeSignature.Carrier language)) {result : Tower.Tm 0}
    (formed : FormationSensitive.Typing (rules source) .nil result (.head (.sort Tower.zero))) :
    FormationSensitive.Typing (rules source) .nil (parameterTypes parameters result) (.head (.sort Tower.zero)) := by
  induction parameters with
  | nil => exact formed
  | cons parameter parameters inductionHypothesis =>
      exact closedArrow_formed source (carrierType_formed source parameter) inductionHypothesis

theorem headerType_formed (source : NativeSignature.Installation language) (header : NativeSignature.Header language) :
    FormationSensitive.Typing (rules source) .nil (headerType header) (.head (.sort Tower.zero)) :=
  parameterTypes_formed source header.parameters (sortType_formed source header.result)

theorem constructor_typing (source : NativeSignature.Installation language) (position : source.Constructor) :
    FormationSensitive.Typing (rules source) .nil
      (.const (constructorDeclName language (source.origin position))) (headerType source.headers[position]) := by
  simpa only [TelescopeAbstraction.liftClosed_zero] using
    (FormationSensitive.Typing.const (R := rules source) (Γ := .nil)
      (by change (signature source).typeOf? _ = _; rw [Signature.typeOf?, constructor_lookup source]; rfl)
      (headerType_formed source source.headers[position]) (.sort Tower.zero))

theorem declaration_count (source : NativeSignature.Installation language) :
    (declarationList source).length = language.types.length + language.terms.length := by
  simp only [declarationList, List.length_append, sortDeclarations, List.length_ofFn,
    constructorDeclarations, source.constructor_count]

/-- The selected native entry retains its original source decoding equation. -/
theorem header_decoded (source : NativeSignature.Installation language) (position : source.Constructor) :
    NativeSignature.decodeHeader? language (source.origin position) = some source.headers[position] := by
  have related := (NativeSignature.decodeList_sound source.decoded).get (i := position.val)
    (by rw [List.length_finRange, ← source.constructor_count]; exact position.isLt) position.isLt
  have index : (List.finRange language.terms.length).get
      ⟨position.val, by rw [List.length_finRange, ← source.constructor_count]; exact position.isLt⟩ =
      source.origin position := by
    apply Fin.ext
    simpa only [List.get_eq_getElem, List.getElem_finRange, Fin.val_cast, Fin.val_mk] using
      (origin_position source position).symm
  rw [index] at related
  simpa only [List.get_eq_getElem, Fin.getElem_fin] using related

def constructorFor (source : NativeSignature.Installation language) (index : Fin language.terms.length) :
    source.Constructor := ⟨index.val, by rw [source.constructor_count]; exact index.isLt⟩

theorem constructorFor_origin (source : NativeSignature.Installation language)
    (index : Fin language.terms.length) : source.origin (constructorFor source index) = index := by
  apply Fin.ext
  exact origin_position source _

/-- Every entry is opaque; no unrecorded unfolding enters this package. -/
theorem value_lookup (source : NativeSignature.Installation language) (name : DeclName) :
    (signature source).valueOf? name = none := by
  cases selected : (signature source).entries name with
  | none => simp [Signature.valueOf?, selected]
  | some entry =>
      have membership := Signature.entries_ofList_mem (declarationList source) selected
      rcases List.mem_append.mp membership with sort | constructor
      · obtain ⟨position, same⟩ := List.mem_ofFn.mp sort
        have entrySame : entry = sortEntry := (congrArg Prod.snd same).symm
        simp [Signature.valueOf?, selected, entrySame, sortEntry]
      · obtain ⟨position, same⟩ := List.mem_ofFn.mp constructor
        have entrySame : entry = headerEntry source.headers[position] := (congrArg Prod.snd same).symm
        simp [Signature.valueOf?, selected, entrySame, headerEntry]

theorem wellFormed (source : NativeSignature.Installation language) :
    (signature source).WellFormed Tower.rules where
  fresh := by intro name entry _selected; rfl
  types := by
    intro name type selected
    unfold Signature.typeOf? at selected
    cases entrySelected : (signature source).entries name with
    | none => simp [entrySelected] at selected
    | some entry =>
        have typeSame : entry.type = type := by simpa [entrySelected] using selected
        have membership := Signature.entries_ofList_mem (declarationList source) entrySelected
        rcases List.mem_append.mp membership with sort | constructor
        · obtain ⟨position, same⟩ := List.mem_ofFn.mp sort
          have entrySame : entry = sortEntry := (congrArg Prod.snd same).symm
          subst entry
          subst type
          exact ⟨.sort (.succ Tower.zero), .sort _, .headType (.sort Tower.zero)⟩
        · obtain ⟨position, same⟩ := List.mem_ofFn.mp constructor
          have entrySame : entry = headerEntry source.headers[position] := (congrArg Prod.snd same).symm
          subst entry
          subst type
          exact ⟨.sort Tower.zero, .sort _, (headerType_formed source _).toRaw⟩
  values := by
    intro name type value _selected impossible
    rw [value_lookup] at impossible
    cases impossible
  noSelfDelta := by
    intro name value impossible
    rw [value_lookup] at impossible
    cases impossible
  declaredPreserves := by
    intro n gamma left right type impossible _typed
    rw [signature, Signature.computation_ofList] at impossible
    exact impossible.elim

theorem constructor_judgment (source : NativeSignature.Installation language) (position : source.Constructor) :
    FormationSensitive.Judgment (rules source) .nil
      (.const (constructorDeclName language (source.origin position))) (headerType source.headers[position]) :=
  ⟨.nil, constructor_typing source position⟩

end Headers

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Curried

open Mettapedia.OSLF
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration BindingSignatureEmbedding

namespace Source

abbrev CarrierSort (language : LanguageDef) := Fin language.types.length

def sortName (language : LanguageDef) (position : CarrierSort language) : String :=
  language.types[position.val].name

abbrev signature (language : LanguageDef) :=
  (CurriedBindingLanguage.signature language).reindexSorts (sortName language)

def projection (language : LanguageDef) :=
  (CurriedBindingLanguage.signature language).reindexProjection (sortName language)

theorem sortName_injective {language : LanguageDef} (unique : language.typeNames.Nodup) :
    Function.Injective (sortName language) := by
  intro first second same
  apply Fin.ext
  apply (unique.getElem_inj_iff (hi := by simpa only [LanguageDef.typeNames, List.length_map] using first.isLt)
    (hj := by simpa only [LanguageDef.typeNames, List.length_map] using second.isLt)).mp
  simpa only [LanguageDef.typeNames, List.getElem_map, sortName] using same

theorem findSort_roundtrip {language : LanguageDef} (unique : language.typeNames.Nodup)
    (sort : CarrierSort language) :
    NativeSignature.findSort? language (sortName language sort) = some sort := by
  obtain ⟨found, accepted⟩ := NativeSignature.findSort?_complete (language := language)
    (name := sortName language sort) ⟨sort, rfl⟩
  have same := sortName_injective unique (NativeSignature.findSort?_sound accepted)
  cases same
  exact accepted

abbrev Operator (language : LanguageDef) := (sort : CarrierSort language) × (signature language).Op sort

def operatorIndex {language : LanguageDef} (operator : Operator language) :
    Fin language.terms.length := operator.2.original.index

def operator? {language : LanguageDef} (admitted : BindingSemanticAdmission.Admitted language)
    (index : Fin language.terms.length) : Option (Operator language) :=
  match selected : NativeSignature.findSort? language language.terms[index.val].category with
  | none => none
  | some result =>
      let original : (CurriedBindingLanguage.signature language).Op (sortName language result) :=
        ⟨index, (NativeSignature.findSort?_sound selected).symm,
          admitted _ (List.getElem_mem index.isLt)⟩
      ((CurriedBindingLanguage.signature language).reindexOperator? (sortName language)
        (NativeSignature.findSort? language)
        (fun _ _ known => NativeSignature.findSort?_sound known) original).map (Sigma.mk result)

def operators {language : LanguageDef} (admitted : BindingSemanticAdmission.Admitted language) :
    List (Operator language) :=
  (List.finRange language.terms.length).filterMap (operator? admitted)

private theorem origin_ext {language : LanguageDef} {sort : String}
    {first second : CurriedBindingLanguage.Origin language sort}
    (same : first.index = second.index) : first = second := by
  rcases first with ⟨first, _, _⟩
  rcases second with ⟨second, _, _⟩
  cases same
  rfl

theorem operatorIndex_injective {language : LanguageDef} (unique : language.typeNames.Nodup) :
    Function.Injective (operatorIndex (language := language)) := by
  rintro ⟨firstSort, first⟩ ⟨secondSort, second⟩ same
  change first.original.index = second.original.index at same
  have sorts : firstSort = secondSort := sortName_injective unique (by
    rw [← first.original.category, ← second.original.category, same])
  cases sorts
  have original : first.original = second.original := origin_ext same
  have equal := Binding.ReindexedOperator.original_injective (sortName_injective unique) original
  cases equal
  rfl

theorem operator?_roundtrip {language : LanguageDef} (unique : language.typeNames.Nodup)
    (admitted : BindingSemanticAdmission.Admitted language) (operator : Operator language) :
    operator? admitted (operatorIndex operator) = some operator := by
  rcases operator with ⟨sort, operator⟩
  have category := operator.original.category
  have selected : NativeSignature.findSort? language
      language.terms[operator.original.index.val].category = some sort := by
    rw [category]
    exact findSort_roundtrip unique sort
  unfold operator? operatorIndex
  split
  · rename_i rejected
    rw [selected] at rejected
    cases rejected
  · rename_i actual found
    have equal : actual = sort := Option.some.inj (found.symm.trans selected)
    cases equal
    have lifted := (CurriedBindingLanguage.signature language).reindexOperator?_roundtrip
      (sortName language) (NativeSignature.findSort? language)
      (fun _ _ known => NativeSignature.findSort?_sound known)
      (findSort_roundtrip unique) operator
    exact congrArg (Option.map (Sigma.mk sort)) lifted

theorem operator_mem {language : LanguageDef} (unique : language.typeNames.Nodup)
    (admitted : BindingSemanticAdmission.Admitted language) (operator : Operator language) :
    operator ∈ operators admitted := by
  exact List.mem_filterMap.mpr ⟨operatorIndex operator, List.mem_finRange _,
    operator?_roundtrip unique admitted operator⟩

private theorem mapM_exists {A B : Type} (decode : A → Option B) (source : List A)
    (available : ∀ value ∈ source, ∃ translated, decode value = some translated) :
    ∃ translated, source.mapM decode = some translated := by
  induction source with
  | nil => exact ⟨[], rfl⟩
  | cons head tail inductionHypothesis =>
      obtain ⟨headValue, first⟩ := available head List.mem_cons_self
      obtain ⟨tailValues, later⟩ := inductionHypothesis
        (fun value member => available value (List.mem_cons_of_mem _ member))
      exact ⟨headValue :: tailValues, by simp [List.mapM_cons, first, later]⟩

private theorem binderSpine_names {type : TypeExpr} {domains : List String} {result : String}
    (spine : BindingSemanticAdmission.BinderSpine type domains result) :
    type.baseNames = domains ++ [result] := by
  induction spine with
  | result => rfl
  | binder domain spine inductionHypothesis =>
      simp only [TypeExpr.baseNames, inductionHypothesis, List.cons_append, List.nil_append]

private theorem admittedType_names {language : LanguageDef} {type : TypeExpr}
    (formed : NativeSignature.AdmittedType language type) :
    ∀ name ∈ type.baseNames, ∃ position : CarrierSort language, sortName language position = name := by
  induction formed with
  | sort position =>
      intro name member
      simp only [TypeExpr.baseNames, List.mem_singleton] at member
      exact ⟨position, member.symm⟩
  | function _ _ left right =>
      intro name member
      rcases List.mem_append.mp member with first | second
      · exact left name first
      · exact right name second

private theorem interpreted_slot_names {parameter : TermParam} {scope : List String}
    {result : String} {type : TypeExpr}
    (meaning : BindingSemanticAdmission.ParameterMeaning parameter scope result)
    (interpreted : Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter = some type)
    (name : String) (member : name ∈ scope ++ [result]) : name ∈ type.baseNames := by
  cases meaning with
  | data =>
      simp only [Mettapedia.GSLT.LanguageDef.WellSorted.parameterType?, Option.some.injEq] at interpreted
      cases interpreted
      simpa only [TypeExpr.baseNames, List.nil_append] using member
  | shorthand =>
      simp only [Mettapedia.GSLT.LanguageDef.WellSorted.parameterType?, Option.some.injEq] at interpreted
      cases interpreted
      exact member
  | binding binder bodyName domain spine =>
      simp only [Mettapedia.GSLT.LanguageDef.WellSorted.parameterType?, Option.some.injEq] at interpreted
      cases interpreted
      simpa [TypeExpr.baseNames, binderSpine_names spine,
        List.mem_append, List.mem_reverse, or_assoc, or_left_comm, or_comm] using member

theorem arity_available {language : LanguageDef}
    (headers : ∀ index, NativeSignature.AdmittedHeader language index)
    {sort : String} (operator : (CurriedBindingLanguage.signature language).Op sort) :
    ∃ arity, ((CurriedBindingLanguage.signature language).arity operator).mapM
      (Binding.SortArityDecoder.decodeArity (NativeSignature.findSort? language)) = some arity := by
  change ∃ arity, (CurriedBindingLanguage.slots language.terms[operator.index.val].params).mapM
    (Binding.SortArityDecoder.decodeArity (NativeSignature.findSort? language)) = some arity
  apply mapM_exists
  intro slot member
  obtain ⟨parameter, parameterMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨scope, result, meaning⟩ := operator.parameters parameter parameterMember
  obtain ⟨type, interpreted, formed⟩ := (headers operator.index).1 parameter parameterMember
  have available : ∀ name ∈ scope ++ [result],
      ∃ position, NativeSignature.findSort? language name = some position := by
    intro name nameMember
    exact NativeSignature.findSort?_complete
      (admittedType_names formed name (interpreted_slot_names meaning interpreted name nameMember))
  obtain ⟨bound, boundDecoded⟩ := mapM_exists (NativeSignature.findSort? language) scope
    (fun name nameMember => available name (List.mem_append_left _ nameMember))
  obtain ⟨resultValue, resultDecoded⟩ := available result
    (List.mem_append_right _ (List.mem_singleton_self _))
  refine ⟨(bound, resultValue), ?_⟩
  rw [CurriedBindingLanguage.slot_meaning meaning]
  simp [Binding.SortArityDecoder.decodeArity, boundDecoded, resultDecoded]


theorem operator?_complete {language : LanguageDef}
    (headers : ∀ index, NativeSignature.AdmittedHeader language index)
    (admitted : BindingSemanticAdmission.Admitted language) (index : Fin language.terms.length) :
    ∃ operator, operator? admitted index = some operator := by
  obtain ⟨result, selected⟩ := NativeSignature.findSort?_complete (headers index).2
  let original : (CurriedBindingLanguage.signature language).Op (sortName language result) :=
    ⟨index, (NativeSignature.findSort?_sound selected).symm,
      admitted _ (List.getElem_mem index.isLt)⟩
  obtain ⟨arity, decoded⟩ := arity_available headers original
  unfold operator?
  split
  · rename_i missing
    rw [selected] at missing
    cases missing
  · rename_i actual found
    have same : actual = result := Option.some.inj (found.symm.trans selected)
    cases same
    dsimp only
    unfold Binding.Signature.reindexOperator?
    split
    · rename_i missing
      change (CurriedBindingLanguage.slots language.terms[index.val].params).mapM
        (Binding.SortArityDecoder.decodeArity (NativeSignature.findSort? language)) = none at missing
      change (CurriedBindingLanguage.slots language.terms[index.val].params).mapM
        (Binding.SortArityDecoder.decodeArity (NativeSignature.findSort? language)) = some arity at decoded
      rw [decoded] at missing
      cases missing
    · exact ⟨_, rfl⟩

theorem operator?_index {language : LanguageDef}
    (admitted : BindingSemanticAdmission.Admitted language)
    (index : Fin language.terms.length) (operator : Operator language)
    (accepted : operator? admitted index = some operator) : operatorIndex operator = index := by
  unfold operator? at accepted
  split at accepted
  · cases accepted
  · rename_i result selected
    obtain ⟨lifted, decoded, same⟩ := Option.map_eq_some_iff.mp accepted
    cases same
    have original := (CurriedBindingLanguage.signature language).reindexOperator?_original
      (sortName language) (NativeSignature.findSort? language)
      (fun _ _ known => NativeSignature.findSort?_sound known) _ lifted decoded
    exact congrArg CurriedBindingLanguage.Origin.index original

theorem operators_origins {language : LanguageDef}
    (headers : ∀ index, NativeSignature.AdmittedHeader language index)
    (admitted : BindingSemanticAdmission.Admitted language) :
    (operators admitted).map operatorIndex = List.finRange language.terms.length := by
  suffices ∀ indices : List (Fin language.terms.length),
      (indices.filterMap (operator? admitted)).map operatorIndex = indices from
    this _
  intro indices
  induction indices with
  | nil => rfl
  | cons index indices inductionHypothesis =>
      obtain ⟨operator, accepted⟩ := operator?_complete headers admitted index
      simp only [List.filterMap_cons, accepted, List.map_cons,
        operator?_index admitted index operator accepted, inductionHypothesis]


theorem operators_length {language : LanguageDef}
    (headers : ∀ index, NativeSignature.AdmittedHeader language index)
    (admitted : BindingSemanticAdmission.Admitted language) :
    (operators admitted).length = language.terms.length := by
  change ((List.finRange language.terms.length).filterMap (operator? admitted)).length = _
  have exactLength : ((List.finRange language.terms.length).filterMap
      (operator? admitted)).length = (List.finRange language.terms.length).length := by
    apply List.filterMap_length_eq_length.mpr
    intro index _member
    obtain ⟨operator, accepted⟩ := operator?_complete headers admitted index
    simp only [accepted, Option.isSome_some]
  simpa only [List.length_finRange] using exactLength


def context? (language : LanguageDef) (bound : List String) :
    Option (List (CarrierSort language)) := bound.mapM (NativeSignature.findSort? language)

theorem context?_readback {language : LanguageDef} {bound : List String}
    {decoded : List (CarrierSort language)} (accepted : context? language bound = some decoded) :
    decoded.map (sortName language) = bound :=
  Binding.SortArityDecoder.mapM_sound (sortName language) (NativeSignature.findSort? language)
    (fun _ _ known => NativeSignature.findSort?_sound known) bound decoded accepted

theorem context?_roundtrip {language : LanguageDef} (unique : language.typeNames.Nodup)
    (bound : List (CarrierSort language)) :
    context? language (bound.map (sortName language)) = some bound :=
  Binding.SortArityDecoder.mapM_roundtrip (sortName language) (NativeSignature.findSort? language)
    (findSort_roundtrip unique) bound

def readback {language : LanguageDef} {bound : Binding.Ctx (signature language)}
    {sort : CarrierSort language} (term : Binding.Term (signature language) bound sort) : Pattern :=
  CurriedBindingLanguage.toPattern ((projection language).onTerm term)

theorem readback_typed {language : LanguageDef} {bound : Binding.Ctx (signature language)}
    {sort : CarrierSort language} (term : Binding.Term (signature language) bound sort) :
    Mettapedia.GSLT.LanguageDef.WellSorted.HasType language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext (bound.map (sortName language)))
      (readback term) (.base (sortName language sort)) :=
  CurriedBindingLanguage.toPattern_typed ((projection language).onTerm term)

theorem readback_parsed {language : LanguageDef}
    (binding : BindingSemanticAdmission.Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    {bound : Binding.Ctx (signature language)} {sort : CarrierSort language}
    (term : Binding.Term (signature language) bound sort) :
    CurriedBindingLanguage.SourceChecking.parse? binding (bound.map (sortName language))
      (sortName language sort) (readback term) =
      some ⟨(projection language).onTerm term, rfl⟩ :=
  CurriedBindingLanguage.SourceChecking.parse?_printed binding labels ((projection language).onTerm term)


theorem reindex_original_complete {language : LanguageDef}
    (unique : language.typeNames.Nodup)
    (headers : ∀ index, NativeSignature.AdmittedHeader language index)
    {bound : List (CarrierSort language)} {sort : CarrierSort language}
    (original : Binding.Term (CurriedBindingLanguage.signature language)
      (bound.map (sortName language)) (sortName language sort)) :
    ∃ term, (CurriedBindingLanguage.signature language).reindexTerm? (sortName language)
      (NativeSignature.findSort? language) (fun _ _ known => NativeSignature.findSort?_sound known)
      original = some term := by
  apply (CurriedBindingLanguage.signature language).reindexTerm?_complete
    (sortName language) (NativeSignature.findSort? language)
    (fun _ _ known => NativeSignature.findSort?_sound known) (sortName_injective unique)
  intro result operator
  obtain ⟨arity, decoded⟩ := arity_available headers operator
  unfold Binding.Signature.reindexOperator?
  split
  · rename_i absent
    have impossible : some arity = none := decoded.symm.trans absent
    cases impossible
  · exact ⟨_, rfl⟩


theorem sort_declared {language : LanguageDef} (sort : CarrierSort language) :
    sortName language sort ∈ language.typeNames := by
  exact List.mem_map.mpr ⟨language.types[sort.val], List.getElem_mem sort.isLt, rfl⟩

theorem findSort_declared {language : LanguageDef} {name : String} {sort : CarrierSort language}
    (accepted : NativeSignature.findSort? language name = some sort) : name ∈ language.typeNames := by
  rw [← NativeSignature.findSort?_sound accepted]
  exact sort_declared sort

theorem findSort_exists {language : LanguageDef} {name : String}
    (declared : name ∈ language.typeNames) :
    ∃ sort, NativeSignature.findSort? language name = some sort := by
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp declared
  have bound' : index < language.types.length := by
    simpa only [LanguageDef.typeNames, List.length_map] using bound
  apply NativeSignature.findSort?_complete
  exact ⟨⟨index, bound'⟩, by simpa only [LanguageDef.typeNames, List.getElem_map] using same⟩

theorem context?_complete {language : LanguageDef} {bound : List String}
    (declared : ∀ name ∈ bound, name ∈ language.typeNames) :
    ∃ decoded, context? language bound = some decoded :=
  mapM_exists (NativeSignature.findSort? language) bound (fun name member => findSort_exists (declared name member))


end Source


def names (language : LanguageDef) : BindingSignatureEmbedding.Names (Source.signature language) where
  sort := sortDeclName language
  operator := fun operator => constructorDeclName language operator.original.index

private theorem carrier_source_injective {language : LanguageDef}
    (unique : language.typeNames.Nodup) :
    Function.Injective (NativeSignature.Carrier.source (language := language)) := by
  intro first
  induction first with
  | sort first =>
      intro second same
      cases second with
      | sort second =>
          have positions := Source.sortName_injective unique (TypeExpr.base.inj same)
          exact congrArg NativeSignature.Carrier.sort positions
      | function domain codomain => cases same
  | function domain codomain domainIH codomainIH =>
      intro second same
      cases second with
      | sort second => cases same
      | function left right =>
          exact congrArg₂ NativeSignature.Carrier.function
            (domainIH (TypeExpr.arrow.inj same).1) (codomainIH (TypeExpr.arrow.inj same).2)

private def spineType : List String → String → TypeExpr
  | [], result => .base result
  | domain :: domains, result => .arrow (.base domain) (spineType domains result)

private theorem spine_type {type : TypeExpr} {domains : List String} {result : String}
    (spine : BindingSemanticAdmission.BinderSpine type domains result) :
    type = spineType domains result := by
  induction spine with
  | result => rfl
  | binder domain spine inductionHypothesis => exact congrArg (TypeExpr.arrow (.base domain)) inductionHypothesis

private def spineCarrier {language : LanguageDef} :
    List (Source.CarrierSort language) → Source.CarrierSort language → NativeSignature.Carrier language
  | [], result => .sort result
  | domain :: domains, result => .function (.sort domain) (spineCarrier domains result)

private theorem spineCarrier_source {language : LanguageDef}
    (domains : List (Source.CarrierSort language)) (result : Source.CarrierSort language) :
    (spineCarrier domains result).source = spineType (domains.map (Source.sortName language)) (Source.sortName language result) := by
  induction domains with
  | nil => rfl
  | cons domain domains inductionHypothesis =>
      exact congrArg (TypeExpr.arrow (.base (Source.sortName language domain))) inductionHypothesis

private theorem telescopeType_append {language : LanguageDef}
    (first second : List (Source.CarrierSort language)) (result : Tower.Tm 0) :
    telescopeType (names language) (first ++ second) result =
      telescopeType (names language) second (telescopeType (names language) first result) := by
  induction first generalizing result with
  | nil => rfl
  | cons sort first inductionHypothesis => exact inductionHypothesis _

private theorem spineCarrier_type {language : LanguageDef}
    (domains : List (Source.CarrierSort language)) (result : Source.CarrierSort language) :
    carrierType (spineCarrier domains result) = bindingType (names language) domains.reverse result := by
  induction domains with
  | nil => rfl
  | cons domain domains inductionHypothesis =>
      simp only [spineCarrier, carrierType, inductionHypothesis, List.reverse_cons,
        bindingType, telescopeType_append, telescopeType]
      rfl

/-- Original independently decoded parameter carriers agree with the native
function telescope of their exact finite binding arity. -/
theorem parameter_type {language : LanguageDef} (unique : language.typeNames.Nodup)
    {parameter : TermParam} {scope : List String} {result : String}
    (meaning : BindingSemanticAdmission.ParameterMeaning parameter scope result)
    (carrier : NativeSignature.Carrier language)
    (interpreted : Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter = some carrier.source)
    (bound : List (Source.CarrierSort language)) (sort : Source.CarrierSort language)
    (boundsRead : bound.map (Source.sortName language) = scope)
    (resultRead : Source.sortName language sort = result) :
    carrierType carrier = bindingType (names language) bound sort := by
  obtain ⟨domains, sourceSpine, ordered⟩ :=
    CurriedBindingLanguage.parameter_spine meaning carrier interpreted
  have sourceEqual : carrier.source = (spineCarrier bound.reverse sort).source := by
    rw [spine_type sourceSpine, spineCarrier_source, List.map_reverse, boundsRead,
      ← ordered, List.reverse_reverse, resultRead]
  rw [carrier_source_injective unique sourceEqual, spineCarrier_type, List.reverse_reverse]

private theorem parameterTypes_agree {language : LanguageDef} (unique : language.typeNames.Nodup)
    (parameters : List TermParam)
    (supported : ∀ parameter ∈ parameters, ∃ scope result,
      BindingSemanticAdmission.ParameterMeaning parameter scope result)
    (carriers : List (NativeSignature.Carrier language))
    (interpreted : List.Forall₂ (fun parameter carrier =>
      Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter = some carrier.source) parameters carriers)
    (arity : List (List (Source.CarrierSort language) × Source.CarrierSort language))
    (read : CurriedBindingLanguage.slots parameters = Binding.mapArities (Source.sortName language) arity)
    (result : Tower.Tm 0) :
    parameterTypes carriers result = argumentsType (names language) arity result := by
  induction interpreted generalizing arity with
  | nil =>
      cases arity with
      | nil => rfl
      | cons first rest => cases read
  | @cons parameter carrier parameters carriers first interpreted inductionHypothesis =>
      cases arity with
      | nil => cases read
      | cons slot arity =>
          rcases slot with ⟨bound, sort⟩
          have aligned : CurriedBindingLanguage.slot parameter =
              (bound.map (Source.sortName language), Source.sortName language sort) ∧
              CurriedBindingLanguage.slots parameters = Binding.mapArities (Source.sortName language) arity :=
            List.cons.inj read
          obtain ⟨scope, declaredResult, meaning⟩ := supported parameter List.mem_cons_self
          have slotRead := (CurriedBindingLanguage.slot_meaning meaning).symm.trans aligned.1
          have nativeType := parameter_type unique meaning carrier first bound sort
            (congrArg Prod.fst slotRead).symm (congrArg Prod.snd slotRead).symm
          exact congrArg₂ closedArrow nativeType
            (inductionHypothesis (fun p member => supported p (List.mem_cons_of_mem _ member)) arity aligned.2)

/-- The two independently constructed constructor types agree on the actual
original decoded header, including all finite binding spines. -/
theorem operator_type {language : LanguageDef} (source : NativeSignature.Installation language)
    (unique : language.typeNames.Nodup) {sort : Source.CarrierSort language}
    (operator : (Source.signature language).Op sort) :
    headerType source.headers[Headers.constructorFor source operator.original.index] =
      operatorType (names language) operator := by
  let position := Headers.constructorFor source operator.original.index
  have decoded := Headers.header_decoded source position
  have correct := (NativeSignature.decodeHeader?_sound decoded).2
  have original : source.headers[position].origin = operator.original.index :=
    Headers.constructorFor_origin source operator.original.index
  have headerParameters : List.Forall₂ (fun parameter carrier =>
      Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter = some carrier.source)
      language.terms[operator.original.index.val].params source.headers[position].parameters := by
    simpa only [original] using correct.1
  have resultSame : source.headers[position].result = sort := by
    apply Source.sortName_injective unique
    have headerCategory : Source.sortName language source.headers[position].result =
        language.terms[source.headers[position].origin.val].category := by
      simpa only [Source.sortName, Fin.getElem_fin] using correct.2
    have categories := congrArg
      (fun index : Fin language.terms.length => (language.terms[index.val]'index.isLt).category) original
    exact headerCategory.trans (categories.trans operator.original.category)
  change parameterTypes source.headers[position].parameters (.const (sortDeclName language source.headers[position].result)) =
    argumentsType (names language) operator.arity (sortType (names language) sort)
  rw [resultSame]
  exact parameterTypes_agree unique _ operator.original.parameters _ headerParameters operator.arity
    operator.projects _


private theorem related_left {A B : Type} {relation : A → B → Prop}
    {left : List A} {right : List B} (related : List.Forall₂ relation left right) :
    ∀ value ∈ left, ∃ result, relation value result := by
  induction related with
  | nil => intro value member; cases member
  | cons first _ inductionHypothesis =>
      intro value member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨_, first⟩
      · exact inductionHypothesis value inRest

private theorem header_admitted {language : LanguageDef} {index : Fin language.terms.length}
    {header : NativeSignature.Header language}
    (decoded : NativeSignature.decodeHeader? language index = some header) :
    NativeSignature.AdmittedHeader language index := by
  obtain ⟨same, correct⟩ := NativeSignature.decodeHeader?_sound decoded
  cases same
  constructor
  · intro parameter member
    obtain ⟨carrier, interpreted⟩ := related_left correct.1 parameter member
    exact ⟨carrier.source, interpreted, carrier.admitted⟩
  · exact ⟨header.result, correct.2⟩

private theorem installation_admitted {language : LanguageDef}
    (source : NativeSignature.Installation language) :
    ∀ index, NativeSignature.AdmittedHeader language index := by
  intro index
  obtain ⟨header, decoded⟩ := related_left
    (NativeSignature.decodeList_sound source.decoded) index (List.mem_finRange index)
  exact header_admitted decoded

/-- Signature admission retains original header decoding, binder meanings
and both authored name inventories. Rule and equation authority are separate. -/
structure Installation (language : LanguageDef) where
  original : NativeSignature.Installation language
  sortNames : language.typeNames.Nodup
  constructorNames : (language.terms.map (·.label)).Nodup
  binding : BindingSemanticAdmission.Admitted language

def install? (language : LanguageDef) : Option (Installation language) :=
  if sortNames : language.typeNames.Nodup then
    if constructorNames : (language.terms.map (·.label)).Nodup then
      if supported : BindingSemanticAdmission.check language = true then
        (NativeSignature.install? language).map fun original =>
          ⟨original, sortNames, constructorNames,
            (BindingSemanticAdmission.check_exact language).mp supported⟩
      else none
    else none
  else none

theorem install?_complete {language : LanguageDef} (sortNames : language.typeNames.Nodup)
    (constructorNames : (language.terms.map (·.label)).Nodup)
    (binding : BindingSemanticAdmission.Admitted language)
    (headers : ∀ index, NativeSignature.AdmittedHeader language index) :
    ∃ installed, install? language = some installed := by
  obtain ⟨original, decoded⟩ := NativeSignature.install?_complete headers
  unfold install?
  rw [dif_pos sortNames, dif_pos constructorNames,
    dif_pos ((BindingSemanticAdmission.check_exact language).mpr binding), decoded]
  exact ⟨_, rfl⟩

theorem install?_exact (language : LanguageDef) :
    (∃ installed, install? language = some installed) ↔
      language.typeNames.Nodup ∧ (language.terms.map (·.label)).Nodup ∧
      BindingSemanticAdmission.Admitted language ∧
      (∀ index, NativeSignature.AdmittedHeader language index) := by
  constructor
  · rintro ⟨installed, _accepted⟩
    exact ⟨installed.sortNames, installed.constructorNames, installed.binding,
      installation_admitted installed.original⟩
  · rintro ⟨sortNames, constructorNames, binding, headers⟩
    exact install?_complete sortNames constructorNames binding headers

theorem install?_complete_of_validate {language : LanguageDef}
    (valid : language.validate = []) (binding : BindingSemanticAdmission.Admitted language) :
    ∃ installed, install? language = some installed :=
  install?_complete (LanguageDef.typeNames_nodup_of_validate_eq_nil language valid)
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil language valid) binding
    (BindingSemanticAdmission.admittedHeaders_of_validate valid binding)

namespace Installation

variable {language : LanguageDef}

def declarationList (installed : Installation language) :=
  Headers.declarationList installed.original

def signature (installed : Installation language) :=
  Headers.signature installed.original

def rules (installed : Installation language) :=
  Headers.rules installed.original

theorem declaration_count (installed : Installation language) :
    installed.declarationList.length = language.types.length + language.terms.length :=
  Headers.declaration_count installed.original

def sortRealization (installed : Installation language) :
    BindingSignatureEmbedding.SortRealization (names language) installed.rules where
  typeUniverse := .sort Tower.zero
  above := .sort (.succ Tower.zero)
  joined := .sort (.max Tower.zero Tower.zero)
  universeTyped := .sort Tower.zero
  universeIs := .sort Tower.zero
  aboveIs := .sort (.succ Tower.zero)
  joinSelf := .sorts Tower.zero Tower.zero
  collapseSelf := by
    intro valuation
    simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval, Tower.zero, LevelTower.zero]
  sortLookup := by
    intro sort
    change Source.CarrierSort language at sort
    change (Headers.signature installed.original).typeOf? (sortDeclName language sort) = some _
    rw [Presentation.Declaration.Signature.typeOf?, Headers.sort_lookup]
    rfl

def realization (installed : Installation language) :
    BindingSignatureEmbedding.Realization (names language) installed.rules where
  toSortRealization := installed.sortRealization
  operatorLookup := by
    intro sort operator
    let position := Headers.constructorFor installed.original operator.original.index
    have known := Headers.constructor_lookup installed.original position
    have origin := Headers.constructorFor_origin installed.original operator.original.index
    change (Headers.signature installed.original).typeOf?
      (constructorDeclName language operator.original.index) = some _
    rw [← origin, Presentation.Declaration.Signature.typeOf?, known]
    exact congrArg some (operator_type installed.original installed.sortNames operator)

theorem wellFormed (installed : Installation language) :
    installed.signature.WellFormed Tower.rules :=
  Headers.wellFormed installed.original

theorem source_judgment (installed : Installation language)
    {gamma : Binding.Ctx (Source.signature language)} {sort : Source.CarrierSort language}
    (term : Binding.Term (Source.signature language) gamma sort) :
    FormationSensitive.Judgment installed.rules
      (BindingSignatureEmbedding.context (names language) gamma)
      (BindingSignatureEmbedding.encode (names language) term)
      (BindingSignatureEmbedding.sortType (names language) sort) :=
  installed.realization.encode_judgment term

theorem schema_judgment (installed : Installation language)
    {metas : List (Binding.MetaArity (Source.signature language))}
    {ambient source target : Binding.Ctx (Source.signature language)}
    (bodies : Binding.ContextualAssignment (Source.signature language) metas ambient)
    (environment : Binding.Sub (Source.signature language) ambient target)
    (valuation : Binding.Sub (Source.signature language) source target)
    {sort : Source.CarrierSort language}
    (schema : Binding.Term (Binding.withMetas (Source.signature language) metas) source sort) :
    FormationSensitive.Judgment installed.rules
      (BindingSignatureEmbedding.context (names language) target)
      (BindingSignatureEmbedding.Schema.compile (names language) bodies environment valuation schema)
      (BindingSignatureEmbedding.sortType (names language) sort) :=
  BindingSignatureEmbedding.Schema.compile_judgment installed.realization
    bodies environment valuation schema

abbrev Parsed (language : LanguageDef) (bound : List (Source.CarrierSort language))
    (sort : Source.CarrierSort language) (pattern : Pattern) :=
  {term : Binding.Term (Source.signature language) bound sort // Source.readback term = pattern}

def parse? (installed : Installation language) (bound : List (Source.CarrierSort language))
    (sort : Source.CarrierSort language) (pattern : Pattern) : Option (Parsed language bound sort pattern) := do
  let original ← CurriedBindingLanguage.SourceChecking.parse? installed.binding
    (bound.map (Source.sortName language)) (Source.sortName language sort) pattern
  match decoded : (CurriedBindingLanguage.signature language).reindexTerm? (Source.sortName language)
      (NativeSignature.findSort? language) (fun _ _ known => NativeSignature.findSort?_sound known)
      original.val with
  | none => none
  | some term => some ⟨term, by
      have projects := (CurriedBindingLanguage.signature language).reindexTerm?_projects
        (Source.sortName language) (NativeSignature.findSort? language)
        (fun _ _ known => NativeSignature.findSort?_sound known) original.val term decoded
      change (Source.projection language).onTerm term = original.val at projects
      exact (congrArg CurriedBindingLanguage.toPattern projects).trans original.property⟩

theorem parsed_judgment (installed : Installation language)
    {bound : List (Source.CarrierSort language)} {sort : Source.CarrierSort language}
    {pattern : Pattern} (parsed : Parsed language bound sort pattern) :
    FormationSensitive.Judgment installed.rules (BindingSignatureEmbedding.context (names language) bound)
      (BindingSignatureEmbedding.encode (names language) parsed.val)
      (BindingSignatureEmbedding.sortType (names language) sort) :=
  installed.realization.encode_judgment parsed.val

theorem parsed_source (_installed : Installation language)
    {bound : List (Source.CarrierSort language)} {sort : Source.CarrierSort language}
    {pattern : Pattern} (parsed : Parsed language bound sort pattern) :
    Mettapedia.GSLT.LanguageDef.WellSorted.HasType language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext (bound.map (Source.sortName language)))
      pattern (.base (Source.sortName language sort)) ∧
      isObjectPattern pattern = true ∧ pattern.hasCanonicalBinderMetadata = true := by
  rw [← parsed.property]
  exact ⟨Source.readback_typed parsed.val,
    CurriedBindingLanguage.toPattern_object ((Source.projection language).onTerm parsed.val),
    CurriedBindingLanguage.toPattern_canonical ((Source.projection language).onTerm parsed.val)⟩


theorem parse?_complete (installed : Installation language)
    {bound : List (Source.CarrierSort language)} {sort : Source.CarrierSort language}
    {pattern : Pattern}
    (source : Mettapedia.GSLT.LanguageDef.WellSorted.HasType language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext (bound.map (Source.sortName language)))
      pattern (.base (Source.sortName language sort)) ∧
      isObjectPattern pattern = true ∧ pattern.hasCanonicalBinderMetadata = true) :
    ∃ parsed, installed.parse? bound sort pattern = some parsed := by
  obtain ⟨original, accepted⟩ := Option.isSome_iff_exists.mp
    ((CurriedBindingLanguage.SourceChecking.parse?_exact installed.binding _ _ _).mpr source)
  obtain ⟨term, decoded⟩ := Source.reindex_original_complete installed.sortNames
    (installation_admitted installed.original) original.val
  unfold parse?
  rw [accepted]
  simp only [Option.bind_eq_bind, Option.bind_some]
  split
  · rename_i absent
    rw [decoded] at absent
    cases absent
  · exact ⟨_, rfl⟩

theorem parse?_exact (installed : Installation language)
    (bound : List (Source.CarrierSort language)) (sort : Source.CarrierSort language) (pattern : Pattern) :
    (installed.parse? bound sort pattern).isSome = true ↔
      Mettapedia.GSLT.LanguageDef.WellSorted.HasType language
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
        (Mettapedia.GSLT.Poly.BindingLanguage.typeContext (bound.map (Source.sortName language)))
        pattern (.base (Source.sortName language sort)) ∧
        isObjectPattern pattern = true ∧ pattern.hasCanonicalBinderMetadata = true := by
  constructor
  · intro accepted
    obtain ⟨parsed, _found⟩ := Option.isSome_iff_exists.mp accepted
    exact installed.parsed_source parsed
  · intro source
    obtain ⟨parsed, accepted⟩ := installed.parse?_complete source
    simp only [accepted, Option.isSome_some]

theorem parse?_readback (installed : Installation language)
    {bound : List (Source.CarrierSort language)} {sort : Source.CarrierSort language}
    (term : Binding.Term (Source.signature language) bound sort) :
    installed.parse? bound sort (Source.readback term) = some ⟨term, rfl⟩ := by
  have original := Source.readback_parsed installed.binding installed.constructorNames term
  have decoded := (CurriedBindingLanguage.signature language).reindexTerm?_roundtrip
    (Source.sortName language) (NativeSignature.findSort? language)
    (fun _ _ known => NativeSignature.findSort?_sound known)
    (Source.findSort_roundtrip installed.sortNames) term
  unfold parse?
  rw [original]
  simp only [Option.bind_eq_bind, Option.bind_some]
  split
  · rename_i absent
    have impossible : some term = none := decoded.symm.trans absent
    cases impossible
  · rename_i selected found
    have same : selected = term := Option.some.inj (found.symm.trans decoded)
    cases same
    rfl

theorem source_readback_injective (installed : Installation language)
    {bound : List (Source.CarrierSort language)} {sort : Source.CarrierSort language} :
    Function.Injective (Source.readback (language := language) (bound := bound) (sort := sort)) := by
  intro first second same
  let erase : Pattern → Option (Binding.Term (Source.signature language) bound sort) :=
    fun pattern => (installed.parse? bound sort pattern).map (fun parsed => parsed.val)
  have read := congrArg erase same
  change ((installed.parse? bound sort (Source.readback first)).map (fun parsed => parsed.val)) =
    ((installed.parse? bound sort (Source.readback second)).map (fun parsed => parsed.val)) at read
  simp only [installed.parse?_readback, Option.map_some] at read
  exact Option.some.inj read


/-- A named request retains its exact original scope and result sort while
carrying the finite indices earned by declaration admission. -/
structure NamedParsed (language : LanguageDef) (bound : List String) (sort : String)
    (pattern : Pattern) where
  context : List (Source.CarrierSort language)
  result : Source.CarrierSort language
  contextRead : context.map (Source.sortName language) = bound
  resultRead : Source.sortName language result = sort
  value : Parsed language context result pattern

def parseNamed? (installed : Installation language) (bound : List String) (sort : String)
    (pattern : Pattern) : Option (NamedParsed language bound sort pattern) :=
  match contextRead : Source.context? language bound with
  | none => none
  | some context =>
      match resultRead : NativeSignature.findSort? language sort with
      | none => none
      | some result =>
          (installed.parse? context result pattern).map fun value =>
            ⟨context, result, Source.context?_readback contextRead,
              NativeSignature.findSort?_sound resultRead, value⟩

theorem namedParsed_source (installed : Installation language)
    {bound : List String} {sort : String} {pattern : Pattern}
    (parsed : NamedParsed language bound sort pattern) :
    (∀ name ∈ bound, name ∈ language.typeNames) ∧ sort ∈ language.typeNames ∧
      HasType language FreeTypeContext.empty (Mettapedia.GSLT.Poly.BindingLanguage.typeContext bound)
        pattern (.base sort) ∧ isObjectPattern pattern = true ∧
        pattern.hasCanonicalBinderMetadata = true := by
  constructor
  · intro name member
    rw [← parsed.contextRead] at member
    obtain ⟨position, _present, same⟩ := List.mem_map.mp member
    exact same ▸ Source.sort_declared position
  · constructor
    · exact parsed.resultRead ▸ Source.sort_declared parsed.result
    · have source := installed.parsed_source parsed.value
      simpa only [parsed.contextRead, parsed.resultRead] using source

theorem parseNamed?_complete (installed : Installation language)
    {bound : List String} {sort : String} {pattern : Pattern}
    (source : (∀ name ∈ bound, name ∈ language.typeNames) ∧ sort ∈ language.typeNames ∧
      HasType language FreeTypeContext.empty (Mettapedia.GSLT.Poly.BindingLanguage.typeContext bound)
        pattern (.base sort) ∧ isObjectPattern pattern = true ∧
        pattern.hasCanonicalBinderMetadata = true) :
    ∃ parsed, installed.parseNamed? bound sort pattern = some parsed := by
  obtain ⟨context, contextRead⟩ := Source.context?_complete source.1
  obtain ⟨result, resultRead⟩ := Source.findSort_exists source.2.1
  have sourceTyped : HasType language FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext (context.map (Source.sortName language)))
      pattern (.base (Source.sortName language result)) ∧
      isObjectPattern pattern = true ∧ pattern.hasCanonicalBinderMetadata = true := by
    have resultSame : Source.sortName language result = sort := NativeSignature.findSort?_sound resultRead
    rw [Source.context?_readback contextRead, resultSame]
    exact source.2.2
  obtain ⟨value, valueRead⟩ := installed.parse?_complete sourceTyped
  unfold parseNamed?
  split
  · rename_i missing
    rw [contextRead] at missing
    cases missing
  · rename_i selected found
    have same : selected = context := Option.some.inj (found.symm.trans contextRead)
    cases same
    split
    · rename_i missing
      rw [resultRead] at missing
      cases missing
    · rename_i chosen found
      have same : chosen = result := Option.some.inj (found.symm.trans resultRead)
      cases same
      rw [valueRead]
      exact ⟨_, rfl⟩

theorem parseNamed?_exact (installed : Installation language) (bound : List String)
    (sort : String) (pattern : Pattern) :
    (installed.parseNamed? bound sort pattern).isSome = true ↔
      (∀ name ∈ bound, name ∈ language.typeNames) ∧ sort ∈ language.typeNames ∧
      HasType language FreeTypeContext.empty (Mettapedia.GSLT.Poly.BindingLanguage.typeContext bound)
        pattern (.base sort) ∧ isObjectPattern pattern = true ∧
        pattern.hasCanonicalBinderMetadata = true := by
  constructor
  · intro accepted
    obtain ⟨parsed, _found⟩ := Option.isSome_iff_exists.mp accepted
    exact installed.namedParsed_source parsed
  · intro source
    obtain ⟨parsed, accepted⟩ := installed.parseNamed?_complete source
    simp only [accepted, Option.isSome_some]


end Installation

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Curried

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

open Mettapedia.OSLF
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation BindingSignatureEmbedding

variable {language : LanguageDef}

abbrev Carrier (language : LanguageDef) := NativeSignature.Carrier language

abbrev signature (language : LanguageDef) :=
  (signatureOf language).reindexSorts (NativeSignature.Carrier.source (language := language))

def projection (language : LanguageDef) :=
  (signatureOf language).reindexProjection (NativeSignature.Carrier.source (language := language))

theorem decodeType_source {language : LanguageDef} (unique : language.typeNames.Nodup)
    (carrier : Carrier language) : NativeSignature.decodeType? language carrier.source = some carrier := by
  induction carrier with
  | sort position =>
      exact congrArg (Option.map NativeSignature.Carrier.sort)
        (Curried.Source.findSort_roundtrip unique position)
  | function domain codomain domainIH codomainIH =>
      simp only [NativeSignature.Carrier.source, NativeSignature.decodeType?, domainIH, codomainIH,
        Option.bind_eq_bind, Option.bind_some, pure]

theorem carrier_source_injective {language : LanguageDef} (unique : language.typeNames.Nodup) :
    Function.Injective (NativeSignature.Carrier.source (language := language)) := by
  intro first second same
  have decoded := congrArg (NativeSignature.decodeType? language) same
  exact Option.some.inj (by simpa only [decodeType_source unique] using decoded)

def readback {language : LanguageDef} {bound : Binding.Ctx (signature language)}
    {sort : Carrier language} (term : Binding.Term (signature language) bound sort) : Pattern :=
  erase ((projection language).onTerm term)

theorem readback_typed {language : LanguageDef} {bound : Binding.Ctx (signature language)}
    {sort : Carrier language} (term : Binding.Term (signature language) bound sort) :
    Mettapedia.GSLT.LanguageDef.WellSorted.HasType language
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      (bound.map NativeSignature.Carrier.source) (readback term) sort.source :=
  erase_typed ((projection language).onTerm term)

def operator? {language : LanguageDef} {result : Carrier language}
    (original : (signatureOf language).Op result.source) :
    Option ((signature language).Op result) :=
  (signatureOf language).reindexOperator? NativeSignature.Carrier.source
    (NativeSignature.decodeType? language) (fun _ _ known => NativeSignature.decodeType?_sound known) original

theorem operator?_roundtrip {language : LanguageDef} (unique : language.typeNames.Nodup)
    {result : Carrier language} (operator : (signature language).Op result) :
    operator? operator.original = some operator :=
  (signatureOf language).reindexOperator?_roundtrip NativeSignature.Carrier.source
    (NativeSignature.decodeType? language) (fun _ _ known => NativeSignature.decodeType?_sound known)
    (decodeType_source unique) operator

def term? {language : LanguageDef} {bound : List (Carrier language)} {sort : Carrier language}
    (original : Binding.Term (signatureOf language) (bound.map NativeSignature.Carrier.source) sort.source) :
    Option (Binding.Term (signature language) bound sort) :=
  (signatureOf language).reindexTerm? NativeSignature.Carrier.source (NativeSignature.decodeType? language)
    (fun _ _ known => NativeSignature.decodeType?_sound known) original

theorem term?_readback {language : LanguageDef} {bound : List (Carrier language)} {sort : Carrier language}
    (original : Binding.Term (signatureOf language) (bound.map NativeSignature.Carrier.source) sort.source)
    (selected : Binding.Term (signature language) bound sort) (accepted : term? original = some selected) :
    (projection language).onTerm selected = original :=
  (signatureOf language).reindexTerm?_projects NativeSignature.Carrier.source
    (NativeSignature.decodeType? language) (fun _ _ known => NativeSignature.decodeType?_sound known)
    original selected accepted

theorem term?_roundtrip {language : LanguageDef} (unique : language.typeNames.Nodup)
    {bound : List (Carrier language)} {sort : Carrier language}
    (selected : Binding.Term (signature language) bound sort) :
    term? ((projection language).onTerm selected) = some selected :=
  (signatureOf language).reindexTerm?_roundtrip NativeSignature.Carrier.source
    (NativeSignature.decodeType? language) (fun _ _ known => NativeSignature.decodeType?_sound known)
    (decodeType_source unique) selected

/-- The source constructor metadata selects its actual declaration row. -/
def constructorIndex {language : LanguageDef} (rule : GrammarRule) (member : rule ∈ language.terms) :
    Fin language.terms.length := ⟨language.terms.idxOf rule, List.idxOf_lt_length_iff.mpr member⟩

theorem constructorIndex_read {language : LanguageDef} (rule : GrammarRule) (member : rule ∈ language.terms) :
    language.terms[(constructorIndex rule member).val] = rule :=
  List.getElem_idxOf (List.idxOf_lt_length_iff.mpr member)

private theorem related_left {A B : Type} {relation : A → B → Prop}
    {left : List A} {right : List B} (related : List.Forall₂ relation left right) :
    ∀ value ∈ left, ∃ result, relation value result := by
  induction related with
  | nil => intro value member; cases member
  | cons first _ inductionHypothesis =>
      intro value member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨_, first⟩
      · exact inductionHypothesis value inRest

/-- Header admission supplies the original independent parameter types;
no binding-shape adequacy theorem is an argument of this result. -/
theorem constructor_parameters (source : NativeSignature.Installation language)
    (rule : GrammarRule) (member : rule ∈ language.terms) :
    List.Forall₂ (fun parameter carrier =>
      Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter = some carrier.source)
      rule.params source.headers[Headers.constructorFor source (constructorIndex rule member)].parameters := by
  let position := Headers.constructorFor source (constructorIndex rule member)
  have correct := (NativeSignature.decodeHeader?_sound (Headers.header_decoded source position)).2
  have original := Headers.constructorFor_origin source (constructorIndex rule member)
  have selected : language.terms[source.headers[position].origin.val] = rule := by
    have indexed := congrArg (fun index : Fin language.terms.length => language.terms[index.val]'index.isLt) original
    exact indexed.trans (constructorIndex_read rule member)
  simpa only [selected] using correct.1

theorem no_collection_constructor (source : NativeSignature.Installation language)
    (rule : GrammarRule) (member : rule ∈ language.terms)
    (name : String) (kind : CollType) (element : TypeExpr) :
    rule.params ≠ [.simple name (.collection kind element)] := by
  intro shape
  have typed := constructor_parameters source rule member
  rw [shape] at typed
  obtain ⟨carrier, first⟩ := related_left typed _ (List.mem_singleton_self _)
  simp only [Mettapedia.GSLT.LanguageDef.WellSorted.parameterType?, Option.some.injEq] at first
  cases carrier <;> cases first

private theorem source_not_collection (carrier : Carrier language) (kind : CollType) (element : TypeExpr) :
    carrier.source ≠ .collection kind element := by
  cases carrier <;> intro impossible <;> cases impossible

private theorem source_not_multiArrow (carrier : Carrier language) (domain codomain : TypeExpr) :
    carrier.source ≠ .arrow (.multiBinder domain) codomain := by
  cases carrier with
  | sort => intro impossible; cases impossible
  | function first last =>
      intro impossible
      have domainEqual := (TypeExpr.arrow.inj impossible).1
      cases first <;> cases domainEqual

/-- Structural operator images retain the independently specified source result
and the actual functional carrier which admitted it. -/
def operatorImage (source : NativeSignature.Installation language) :
    {result : TypeExpr} → (operator : Operator language result) →
    (sort : Carrier language) → sort.source = result → Tower.Tm 0
  | _, .constructor rule member _ _, _, _ =>
      .const (constructorDeclName language (constructorIndex rule member))
  | _, .collectionConstructor rule member name kind element shape _, _, _ =>
      False.elim (no_collection_constructor source rule member name kind element
        ((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2)
  | _, .lambda _ _, _, _ => ClosedOperators.Derived.identity
  | _, .multiLambda domain codomain _, sort, resultRead =>
      False.elim (source_not_multiArrow sort domain codomain resultRead)
  | _, .subst _ _, _, _ => ClosedOperators.Derived.identity
  | _, .collection kind element _, sort, resultRead =>
      False.elim (source_not_collection sort kind element resultRead)

/-- Structural abstraction and substitution use native computation. Ordinary
constructors use their actual finite declared constants. -/
def images (source : NativeSignature.Installation language) :
    ClosedOperators.Images (signature language) Tower.Head :=
  fun {sort} operator => operatorImage source operator.original sort rfl

/-- Native type formation is obtained from the concrete finite header package. -/
def formation (source : NativeSignature.Installation language) :
    ClosedOperators.Formation (S := signature language) carrierType (Headers.rules source) where
  typeUniverse := .sort Tower.zero
  joined := .sort (.max Tower.zero Tower.zero)
  universeIs := .sort Tower.zero
  joinSelf := .sorts Tower.zero Tower.zero
  collapseSelf := by
    intro valuation
    simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval, Tower.zero, LevelTower.zero]
  typeFormed := Headers.carrierType_formed source

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

open Mettapedia.OSLF
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation BindingSignatureEmbedding

variable {language : LanguageDef}

private theorem singleton_scope {A : Type} (map : A → TypeExpr)
    {bound : List A} {domain : TypeExpr} (read : [domain] = bound.map map) :
    ∃ value, bound = [value] ∧ map value = domain := by
  have length : bound.length = 1 := by
    have counts := congrArg List.length read
    simpa only [List.length_cons, List.length_nil, List.length_map] using counts.symm
  obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp length
  exact ⟨value, rfl, (List.cons.inj read).1.symm⟩

/-- Every independently specified parameter scope agrees with its original
header function carrier after exact functional sort decoding. -/
theorem parameter_scope_type (unique : language.typeNames.Nodup)
    {parameter : TermParam} {sourceBound : List TypeExpr} {sourceResult : TypeExpr}
    (scope : ParameterScope parameter sourceBound sourceResult)
    (bound : List (Carrier language)) (result carrier : Carrier language)
    (boundRead : sourceBound = bound.map NativeSignature.Carrier.source)
    (resultRead : sourceResult = result.source)
    (interpreted : Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter = some carrier.source) :
    carrierType carrier = ClosedOperators.bindingType (S := signature language) carrierType bound result := by
  cases scope with
  | simple name type =>
      have length := congrArg List.length boundRead
      have empty : bound = [] := List.length_eq_zero_iff.mp (by simpa only [List.length_nil, List.length_map] using length.symm)
      subst bound
      simp only [Mettapedia.GSLT.LanguageDef.WellSorted.parameterType?, Option.some.injEq] at interpreted
      have same := carrier_source_injective unique (interpreted.symm.trans resultRead)
      cases same
      rfl
  | abstraction binder name domain codomain =>
      obtain ⟨domainCarrier, rfl, domainRead⟩ := singleton_scope NativeSignature.Carrier.source boundRead
      simp only [Mettapedia.GSLT.LanguageDef.WellSorted.parameterType?, Option.some.injEq] at interpreted
      have sourceSame : carrier.source = (NativeSignature.Carrier.function domainCarrier result).source :=
        interpreted.symm.trans (congrArg₂ TypeExpr.arrow domainRead.symm resultRead)
      have same := carrier_source_injective unique sourceSame
      cases same
      rfl
  | abstractionBase binder name sort =>
      obtain ⟨domainCarrier, rfl, domainRead⟩ := singleton_scope NativeSignature.Carrier.source boundRead
      simp only [Mettapedia.GSLT.LanguageDef.WellSorted.parameterType?, Option.some.injEq] at interpreted
      have sourceSame : carrier.source = (NativeSignature.Carrier.function domainCarrier result).source :=
        interpreted.symm.trans (congrArg₂ TypeExpr.arrow domainRead.symm resultRead)
      have same := carrier_source_injective unique sourceSame
      cases same
      rfl
  | multiAbstraction binders name domain codomain count =>
      simp only [Mettapedia.GSLT.LanguageDef.WellSorted.parameterType?, Option.some.injEq] at interpreted
      cases carrier with
      | sort position => cases interpreted
      | function first last =>
          have domainEqual := (TypeExpr.arrow.inj interpreted).1
          cases first <;> cases domainEqual
  | multiAbstractionBase binders name sort count =>
      simp only [Mettapedia.GSLT.LanguageDef.WellSorted.parameterType?, Option.some.injEq] at interpreted
      cases carrier with
      | sort position => cases interpreted
      | function first last =>
          have domainEqual := (TypeExpr.arrow.inj interpreted).1
          cases first <;> cases domainEqual

theorem parameter_scopes_type (unique : language.typeNames.Nodup)
    {parameters : List TermParam} {sourceArity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes parameters sourceArity)
    (carriers : List (Carrier language))
    (interpreted : List.Forall₂ (fun parameter carrier =>
      Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter = some carrier.source) parameters carriers)
    (arity : List (List (Carrier language) × Carrier language))
    (read : sourceArity = Binding.mapArities NativeSignature.Carrier.source arity) (result : Tower.Tm 0) :
    parameterTypes carriers result =
      ClosedOperators.argumentsType (S := signature language) carrierType arity result := by
  induction scopes generalizing carriers arity with
  | nil =>
      cases interpreted
      cases arity with
      | nil => rfl
      | cons first rest => cases read
  | @cons parameter parameters sourceBound sourceResult sourceRest scope scopes inductionHypothesis =>
      cases interpreted with
      | @cons _ carrier _ carriers first later =>
          cases arity with
          | nil => cases read
          | cons slot arity =>
              rcases slot with ⟨bound, sort⟩
              have aligned := List.cons.inj read
              have header := parameter_scope_type unique scope bound sort carrier
                (congrArg Prod.fst aligned.1) (congrArg Prod.snd aligned.1) first
              exact congrArg₂ closedArrow header
                (inductionHypothesis carriers later arity aligned.2)

/-- A whole ordinary constructor has exactly the native type earned by the
actual finite declaration selected from its original source metadata. -/
theorem constructor_type (source : NativeSignature.Installation language)
    (unique : language.typeNames.Nodup)
    (rule : GrammarRule) (member : rule ∈ language.terms)
    {sourceArity : List (List TypeExpr × TypeExpr)} (scopes : ParameterScopes rule.params sourceArity)
    (arity : List (List (Carrier language) × Carrier language))
    (read : sourceArity = Binding.mapArities NativeSignature.Carrier.source arity)
    (sort : Carrier language) (resultRead : sort.source = .base rule.category) :
    headerType source.headers[Headers.constructorFor source (constructorIndex rule member)] =
      ClosedOperators.argumentsType (S := signature language) carrierType arity (carrierType sort) := by
  let position := Headers.constructorFor source (constructorIndex rule member)
  have correct := (NativeSignature.decodeHeader?_sound (Headers.header_decoded source position)).2
  have original := Headers.constructorFor_origin source (constructorIndex rule member)
  have selected : language.terms[source.headers[position].origin.val] = rule := by
    have indexed := congrArg (fun index : Fin language.terms.length => language.terms[index.val]'index.isLt) original
    exact indexed.trans (constructorIndex_read rule member)
  have headerResult : (NativeSignature.Carrier.sort source.headers[position].result).source = sort.source := by
    have category : language.types[source.headers[position].result.val].name =
        language.terms[source.headers[position].origin.val].category := by
      simpa only [Fin.getElem_fin] using correct.2
    have selectedCategory := congrArg GrammarRule.category selected
    exact (congrArg TypeExpr.base (category.trans selectedCategory)).trans resultRead.symm
  have resultSame := carrier_source_injective unique headerResult
  unfold headerType
  change parameterTypes source.headers[position].parameters
    (carrierType (NativeSignature.Carrier.sort source.headers[position].result)) = _
  rw [resultSame]
  exact parameter_scopes_type unique scopes _ (constructor_parameters source rule member) arity read _

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

open Mettapedia.OSLF
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation BindingSignatureEmbedding

variable {language : LanguageDef}

private theorem singleton_preimage {A B : Type} (map : A → B)
    {value : B} {values : List A} (read : [value] = values.map map) :
    ∃ selected, values = [selected] ∧ map selected = value := by
  have length : values.length = 1 := by
    have counts := congrArg List.length read
    simpa only [List.length_cons, List.length_nil, List.length_map] using counts.symm
  obtain ⟨selected, rfl⟩ := List.length_eq_one_iff.mp length
  exact ⟨selected, rfl, (List.cons.inj read).1.symm⟩

/-- Retained substitution operations carry a decoded domain and the exact two
source argument scopes. This need not hold for excluded source operators. -/
theorem substitution_arity (unique : language.typeNames.Nodup)
    (domain : TypeExpr) (result : Carrier language)
    (arity : List (List (Carrier language) × Carrier language))
    (read : [([domain], result.source), ([], domain)] =
      Binding.mapArities NativeSignature.Carrier.source arity) :
    ∃ selected, domain = selected.source ∧ arity = [([selected], result), ([], selected)] := by
  cases arity with
  | nil => cases read
  | cons first rest =>
      cases rest with
      | nil => cases (List.cons.inj read).2
      | cons second rest =>
          rcases first with ⟨firstBound, firstResult⟩
          rcases second with ⟨secondBound, secondResult⟩
          have rows := List.cons.inj read
          have later := List.cons.inj rows.2
          have restEmpty : rest = [] := by
            have counts := congrArg List.length later.2
            exact List.length_eq_zero_iff.mp (by simpa only [Binding.mapArities, List.length_map, List.length_nil] using counts.symm)
          obtain ⟨boundDomain, firstBoundEq, domainEq⟩ :=
            singleton_preimage NativeSignature.Carrier.source (congrArg Prod.fst rows.1)
          change firstBound = [boundDomain] at firstBoundEq
          have firstResultEq : firstResult = result :=
            carrier_source_injective unique (congrArg Prod.snd rows.1).symm
          have secondBoundEmpty : secondBound = [] := by
            have counts := congrArg List.length (congrArg Prod.fst later.1)
            exact List.length_eq_zero_iff.mp (by simpa only [Binding.mapArity, List.length_map, List.length_nil] using counts.symm)
          have secondResultEq : secondResult = boundDomain :=
            carrier_source_injective unique ((congrArg Prod.snd later.1).symm.trans domainEq.symm)
          exact ⟨boundDomain, domainEq.symm, by rw [restEmpty, firstBoundEq, firstResultEq, secondBoundEmpty, secondResultEq]⟩

/-- Each original admitted operator image earns its actual native argument type. -/
theorem operatorImage_typed (source : NativeSignature.Installation language)
    (unique : language.typeNames.Nodup) {result : TypeExpr}
    (original : Operator language result) (sort : Carrier language)
    (resultRead : sort.source = result)
    (arity : List (List (Carrier language) × Carrier language))
    (projects : (signatureOf language).arity original =
      Binding.mapArities NativeSignature.Carrier.source arity) :
    FormationSensitive.Typing (Headers.rules source) .nil
      (operatorImage source original sort resultRead)
      (ClosedOperators.argumentsType (S := signature language) carrierType arity (carrierType sort)) := by
  cases original with
  | constructor rule member ordinary parameters =>
      have typed := Headers.constructor_typing source
        (Headers.constructorFor source (constructorIndex rule member))
      rw [Headers.constructorFor_origin,
        constructor_type source unique rule member parameters arity projects sort resultRead] at typed
      exact typed
  | collectionConstructor rule member name kind element shape count =>
      exact False.elim (no_collection_constructor source rule member name kind element
        ((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2)
  | lambda domain codomain =>
      cases sort with
      | sort position => cases resultRead
      | function first last =>
          have aligned := TypeExpr.arrow.inj resultRead
          have canonicalRead : Binding.mapArities NativeSignature.Carrier.source arity =
              Binding.mapArities NativeSignature.Carrier.source [([first], last)] := by
            simpa only [signatureOf, Binding.mapArities, Binding.mapArity,
              List.map_cons, List.map_nil, aligned.1, aligned.2] using projects.symm
          have same := Binding.mapArities_injective (carrier_source_injective unique) canonicalRead
          subst arity
          exact ClosedOperators.Derived.identity_typing (formation source)
            ((formation source).typeFormed (.function first last))
  | multiLambda domain codomain count =>
      cases sort with
      | sort position => cases resultRead
      | function first last =>
          have domains := (TypeExpr.arrow.inj resultRead).1
          cases first <;> cases domains
  | subst domain codomain =>
      have read : [([domain], sort.source), ([], domain)] =
          Binding.mapArities NativeSignature.Carrier.source arity := by
        simpa only [signatureOf, ← resultRead] using projects
      obtain ⟨input, _, arityEq⟩ := substitution_arity unique domain sort arity read
      subst arity
      exact ClosedOperators.Derived.identity_typing (formation source)
        ((formation source).typeFormed (.function input sort))
  | collection kind element count =>
      cases sort <;> cases resultRead

/-- All retained operators are formed in the single installed native signature. -/
def realization (source : NativeSignature.Installation language)
    (unique : language.typeNames.Nodup) :
    ClosedOperators.Realization (S := signature language) carrierType (images source) (Headers.rules source) where
  toFormation := formation source
  imageTyped := fun operator => operatorImage_typed source unique operator.original _ rfl operator.arity operator.projects

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

open Mettapedia.OSLF
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation BindingSignatureEmbedding

variable {language : LanguageDef}

/-- The original structural abstraction, with its actual decoded binding scope. -/
def abstraction {bound : List (Carrier language)} {domain result : Carrier language}
    (body : Binding.Term (signature language) (domain :: bound) result) :
    Binding.Term (signature language) bound (.function domain result) :=
  .op ⟨.lambda domain.source result.source, [([domain], result)], rfl⟩ (.cons body .nil)

/-- The original explicit substitution operation; evaluation remains a separate
operation, with its literal endpoint and finite native evidence below. -/
def substitution {bound : List (Carrier language)} {domain result : Carrier language}
    (body : Binding.Term (signature language) (domain :: bound) result)
    (argument : Binding.Term (signature language) bound domain) :
    Binding.Term (signature language) bound result :=
  .op ⟨.subst domain.source result.source, [([domain], result), ([], domain)], rfl⟩
    (.cons body (.cons argument .nil))

theorem abstraction_readback {bound : List (Carrier language)} {domain result : Carrier language}
    (body : Binding.Term (signature language) (domain :: bound) result) :
    readback (abstraction body) = .lambda none (readback body) := by
  change Pattern.lambda none (erase (Binding.mapTerm (projection language)
    (Binding.liftVarMap NativeSignature.Carrier.source (Binding.mapVar NativeSignature.Carrier.source) [domain]) body)) = _
  apply congrArg (Pattern.lambda none)
  apply congrArg erase
  exact Binding.mapTerm_congr (projection language) _ _ (fun _ position => by cases position <;> rfl) body

theorem substitution_readback {bound : List (Carrier language)} {domain result : Carrier language}
    (body : Binding.Term (signature language) (domain :: bound) result)
    (argument : Binding.Term (signature language) bound domain) :
    readback (substitution body argument) = .subst (readback body) (readback argument) := by
  change Pattern.subst (erase (Binding.mapTerm (projection language)
    (Binding.liftVarMap NativeSignature.Carrier.source (Binding.mapVar NativeSignature.Carrier.source) [domain]) body))
    (readback argument) = _
  apply congrArg (fun term => Pattern.subst term (readback argument))
  apply congrArg erase
  exact Binding.mapTerm_congr (projection language) _ _ (fun _ position => by cases position <;> rfl) body

/-- The native contractum reads back to the already defined raw source
instantiation, including every binder under which the variable occurs. -/
theorem inst_readback {bound : List (Carrier language)} {domain result : Carrier language}
    (body : Binding.Term (signature language) (domain :: bound) result)
    (argument : Binding.Term (signature language) bound domain) :
    readback (Binding.inst body argument) =
      MeTTaIL.Substitution.instantiateBVar (readback argument) (readback body) := by
  have transported := Binding.mapTerm_inst (S := signature language) (T := signatureOf language)
    (projection language) body argument
  have erased := congrArg (fun term : Binding.Term (signatureOf language)
    (bound.map NativeSignature.Carrier.source) result.source => erase term) transported
  exact erased.trans (erase_bind_extend _ _)

/-- Formation follows from actual finite declarations, not a whole-term
adequacy premise. -/
theorem compiled_judgment (source : NativeSignature.Installation language)
    (unique : language.typeNames.Nodup)
    {bound : List (Carrier language)} {sort : Carrier language}
    (term : Binding.Term (signature language) bound sort) :
    FormationSensitive.Judgment (Headers.rules source) (ClosedOperators.typeContext carrierType bound)
      (ClosedOperators.compile (images source) term) (liftClosed (carrierType sort)) :=
  (realization source unique).compile_judgment term

theorem compile_abstraction (source : NativeSignature.Installation language)
    {bound : List (Carrier language)} {domain result : Carrier language}
    (body : Binding.Term (signature language) (domain :: bound) result) :
    ClosedOperators.compile (images source) (abstraction body) =
      .app (liftClosed ClosedOperators.Derived.identity)
        (.lam (ClosedOperators.compile (images source) body)) := rfl

theorem compile_substitution (source : NativeSignature.Installation language)
    {bound : List (Carrier language)} {domain result : Carrier language}
    (body : Binding.Term (signature language) (domain :: bound) result)
    (argument : Binding.Term (signature language) bound domain) :
    ClosedOperators.compile (images source) (substitution body argument) =
      .app (.app (liftClosed ClosedOperators.Derived.identity)
        (.lam (ClosedOperators.compile (images source) body)))
        (ClosedOperators.compile (images source) argument) := rfl

/-- A directed native execution exposes the supplied source abstraction. -/
theorem abstraction_steps (source : NativeSignature.Installation language)
    {bound : List (Carrier language)} {domain result : Carrier language}
    (body : Binding.Term (signature language) (domain :: bound) result) :
    TelescopeAbstraction.BetaSteps
      (ClosedOperators.compile (images source) (abstraction body))
      (.lam (ClosedOperators.compile (images source) body)) :=
  ClosedOperators.Derived.introduction_steps _

/-- The native execution endpoint is the compiled original source instance. -/
theorem substitution_steps (source : NativeSignature.Installation language)
    {bound : List (Carrier language)} {domain result : Carrier language}
    (body : Binding.Term (signature language) (domain :: bound) result)
    (argument : Binding.Term (signature language) bound domain) :
    TelescopeAbstraction.BetaSteps
      (ClosedOperators.compile (images source) (substitution body argument))
      (ClosedOperators.compile (images source) (Binding.inst body argument)) :=
  ClosedOperators.Derived.compiledSubstitution_steps (images source) body argument

/-- Explicit evidence replays against the actual compiled source redex and
contractum. The declared head policy and authored roots are not consulted. -/
theorem substitution_checked (source : NativeSignature.Installation language)
    {RootCode : Nat → Type} (headEq : Tower.Head → Tower.Head → Prop) [DecidableRel headEq]
    (decodeRoot : {n : Nat} → RootCode n → Option (Tower.Tm n × Tower.Tm n))
    {bound : List (Carrier language)} {domain result : Carrier language}
    (body : Binding.Term (signature language) (domain :: bound) result)
    (argument : Binding.Term (signature language) bound domain) :
    (ClosedOperators.Derived.substitutionCode (RootCode := RootCode)
      (ClosedOperators.compile (images source) body)
      (ClosedOperators.compile (images source) argument)).check headEq decodeRoot
      (ClosedOperators.compile (images source) (substitution body argument))
      (ClosedOperators.compile (images source) (Binding.inst body argument)) = true :=
  ClosedOperators.Derived.compiledSubstitution_checked headEq decodeRoot (images source) body argument

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

open Mettapedia.OSLF
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation BindingSignatureEmbedding

variable {language : LanguageDef}

/-- A virtual name for the shared derived identity program. It is never
installed as a polymorphic constant declaration. -/
def identityName (language : LanguageDef) : DeclName :=
  .str (.str .anonymous language.name) "GSLT.authored.identity"

private theorem constructor_ne_identity (position : Fin language.terms.length) :
    constructorDeclName language position ≠ identityName language := by
  intro impossible
  cases impossible

/-- A structural name writer for the intermediate source contexts. Native
sort meanings themselves remain the already formed carrierType expressions. -/
def appendSortName : Carrier language → DeclName → DeclName
  | .sort position, tail => .num (.str tail "base") position.val
  | .function domain codomain, tail =>
      .str (appendSortName domain (appendSortName codomain tail)) "arrow"

def virtualSortName (sort : Carrier language) : DeclName :=
  appendSortName sort (.str (.str .anonymous language.name) "GSLT.authored.functional")

/-- Primitive intermediate names come from the original operator, with its
actual admitted result retained in the impossible cases. -/
def operatorIntermediateName (source : NativeSignature.Installation language) :
    {result : TypeExpr} → (operator : Operator language result) →
    (sort : Carrier language) → sort.source = result → DeclName
  | _, .constructor rule member _ _, _, _ =>
      constructorDeclName language (constructorIndex rule member)
  | _, .collectionConstructor rule member name kind element shape _, _, _ =>
      False.elim (no_collection_constructor source rule member name kind element
        ((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2)
  | _, .lambda _ _, _, _ => identityName language
  | _, .multiLambda domain codomain _, sort, resultRead => by
      cases sort with
      | sort position => cases resultRead
      | function first last =>
          have domains := (TypeExpr.arrow.inj resultRead).1
          cases first <;> cases domains
  | _, .subst _ _, _, _ => identityName language
  | _, .collection _ _ _, sort, resultRead => by cases sort <;> cases resultRead

/-- These names are an uninstalled intermediate notation for the existing
schema compiler; the installed environment remains Headers.signature. -/
def virtualNames (source : NativeSignature.Installation language) : Names (signature language) where
  sort := virtualSortName
  operator := fun {sort} operator => operatorIntermediateName source operator.original sort rfl

/-- Only the shared program name expands. Actual finite constructor names
retain their independently formed declarations. -/
def expansion (language : LanguageDef) : ConstantExpansion.Bodies Tower.Head :=
  fun name => if name = identityName language then ClosedOperators.Derived.identity else .const name

/-- The primitive expansion law is proved from each original operation. -/
theorem operatorIntermediate_expands (source : NativeSignature.Installation language)
    {result : TypeExpr} (operator : Operator language result)
    (sort : Carrier language) (resultRead : sort.source = result) :
    expansion language (operatorIntermediateName source operator sort resultRead) =
      operatorImage source operator sort resultRead := by
  cases operator with
  | constructor rule member ordinary parameters =>
      exact if_neg (constructor_ne_identity (constructorIndex rule member))
  | collectionConstructor rule member name kind element shape count =>
      exact False.elim (no_collection_constructor source rule member name kind element
        ((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2)
  | lambda domain codomain => exact if_pos rfl
  | multiLambda domain codomain count =>
      cases sort with
      | sort position => cases resultRead
      | function first last =>
          have domains := (TypeExpr.arrow.inj resultRead).1
          cases first <;> cases domains
  | subst domain codomain => exact if_pos rfl
  | collection kind element count => cases sort <;> cases resultRead

theorem operators_expand (source : NativeSignature.Installation language)
    {sort : Carrier language} (operator : (signature language).Op sort) :
    expansion language ((virtualNames source).operator operator) = images source operator :=
  operatorIntermediate_expands source operator.original sort rfl

/-- Reuse the existing full contextual schema compiler, including its original
metavariable bodies, ambient inputs and simultaneous source valuation. -/
def schemaProgram (source : NativeSignature.Installation language)
    {metas : List (Binding.MetaArity (signature language))}
    {ambient : Binding.Ctx (signature language)}
    (bodies : Binding.ContextualAssignment (signature language) metas ambient)
    {input target : Binding.Ctx (signature language)} {sort : Carrier language}
    (environment : Binding.Sub (signature language) ambient target)
    (valuation : Binding.Sub (signature language) input target)
    (term : Binding.Term (Binding.withMetas (signature language) metas) input sort) :
    Tower.Tm target.length :=
  ClosedOperators.Schema.program (expansion language) (virtualNames source) bodies environment valuation term

def schemaEvidence (source : NativeSignature.Installation language)
    {metas : List (Binding.MetaArity (signature language))}
    {ambient : Binding.Ctx (signature language)}
    (bodies : Binding.ContextualAssignment (signature language) metas ambient)
    {input target : Binding.Ctx (signature language)} {sort : Carrier language}
    (environment : Binding.Sub (signature language) ambient target)
    (valuation : Binding.Sub (signature language) input target)
    (term : Binding.Term (Binding.withMetas (signature language) metas) input sort) :
    StructuralConversionCode.Code Tower.Head (fun _ => Empty) target.length :=
  ClosedOperators.Schema.evidence (expansion language) (virtualNames source) bodies environment valuation term

/-- Formation is earned for the unreduced schema program in the real finite
native declaration environment, with its actual arrow-valued sort meanings. -/
theorem schemaProgram_judgment (source : NativeSignature.Installation language)
    (unique : language.typeNames.Nodup)
    {metas : List (Binding.MetaArity (signature language))}
    {ambient : Binding.Ctx (signature language)}
    (bodies : Binding.ContextualAssignment (signature language) metas ambient)
    {input target : Binding.Ctx (signature language)} {sort : Carrier language}
    (environment : Binding.Sub (signature language) ambient target)
    (valuation : Binding.Sub (signature language) input target)
    (term : Binding.Term (Binding.withMetas (signature language) metas) input sort) :
    FormationSensitive.Judgment (Headers.rules source)
      (ClosedOperators.typeContext carrierType target)
      (schemaProgram source bodies environment valuation term) (liftClosed (carrierType sort)) :=
  ClosedOperators.Schema.program_judgment (realization source unique)
    (expansion language) (virtualNames source) (operators_expand source)
    bodies environment valuation term

/-- The actual expanded certificate replays to the original contextual source
instance interpreted with derived native abstraction and substitution. -/
theorem schemaEvidence_checked (source : NativeSignature.Installation language)
    {metas : List (Binding.MetaArity (signature language))}
    {ambient : Binding.Ctx (signature language)}
    (bodies : Binding.ContextualAssignment (signature language) metas ambient)
    {input target : Binding.Ctx (signature language)} {sort : Carrier language}
    (environment : Binding.Sub (signature language) ambient target)
    (valuation : Binding.Sub (signature language) input target)
    (term : Binding.Term (Binding.withMetas (signature language) metas) input sort) :
    (schemaEvidence source bodies environment valuation term).check
      (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      (schemaProgram source bodies environment valuation term)
      (ClosedOperators.compile (images source)
        (Binding.ContextualAssignment.instantiate bodies environment valuation term)) = true :=
  ClosedOperators.Schema.evidence_checked (expansion language) (virtualNames source)
    (images source) (operators_expand source) bodies environment valuation term

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Controls.Outputs

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration
open SchemaElaboration

private abbrev L := Mettapedia.OSLF.NativeTypes.Instances.LetCase.language
private abbrev letRule := Mettapedia.OSLF.NativeTypes.Instances.LetCase.letRule
private abbrev caseRule := Mettapedia.OSLF.NativeTypes.Instances.LetCase.caseRule
private abbrev V := Mettapedia.OSLF.NativeTypes.Instances.LetCase.value
private abbrev C := Mettapedia.OSLF.NativeTypes.Instances.LetCase.computation
private def letSpec : RuleBindingSpec := letRule.bindings.get (by decide)
private def caseSpec : RuleBindingSpec := caseRule.bindings.get (by decide)
private def letOutput := (outputAssembly L letRule letSpec .right).walk
  (sourceHeight letRule.right) [] [] letRule.right C
private def caseOutput := (outputAssembly L caseRule caseSpec .right).walk
  (sourceHeight caseRule.right) [] [] caseRule.right C

private def unitOp : (signatureOf L).Op V :=
  .constructor L.terms[0] (by decide)
    (by simp [Mettapedia.GSLT.LanguageDef.WellSorted.UsesBareCollection, L,
      Mettapedia.OSLF.NativeTypes.Instances.LetCase.language]) .nil
private def returnOp : (signatureOf L).Op C :=
  .constructor L.terms[2] (by decide)
    (by simp [Mettapedia.GSLT.LanguageDef.WellSorted.UsesBareCollection, L,
      Mettapedia.OSLF.NativeTypes.Instances.LetCase.language,
      Mettapedia.OSLF.NativeTypes.Instances.LetCase.value])
    (.cons (.simple "value" V) .nil)
private def letBodies : (index : Fin (metaArities (language := L) letRule letSpec).length) →
    Term (signatureOf L) ((metaArities letRule letSpec).get index).1
      ((metaArities letRule letSpec).get index).2 :=
  Fin.cases (.op unitOp .nil)
    (Fin.cases (.op returnOp (.cons (.var .zero) .nil)) (fun index => Fin.elim0 index))
private def caseBodies : (index : Fin (metaArities (language := L) caseRule caseSpec).length) →
    Term (signatureOf L) ((metaArities caseRule caseSpec).get index).1
      ((metaArities caseRule caseSpec).get index).2 :=
  Fin.cases (.op unitOp .nil)
    (Fin.cases (.op unitOp .nil)
      (Fin.cases (.op returnOp (.cons (.var (.succ .zero)) .nil)) (fun index => Fin.elim0 index)))
private def letRaw : Assignment :=
  [("V", ⟨[], 0, .apply "Unit" []⟩), ("B", ⟨[V], 0, .apply "Return" [.bvar 0]⟩)]
private def caseRaw : Assignment :=
  [("L", ⟨[], 0, .apply "Unit" []⟩), ("R", ⟨[], 0, .apply "Unit" []⟩),
   ("B", ⟨[V,V], 0, .apply "Return" [.bvar 1]⟩)]

private def pairOp : (signatureOf L).Op V :=
  .constructor L.terms[1] (by decide)
    (by simp [Mettapedia.GSLT.LanguageDef.WellSorted.UsesBareCollection, L,
      Mettapedia.OSLF.NativeTypes.Instances.LetCase.language,
      Mettapedia.OSLF.NativeTypes.Instances.LetCase.value])
    (.cons (.simple "left" V) (.cons (.simple "right" V) .nil))
private def unitValue {context : List TypeExpr} : Term (signatureOf L) context V := .op unitOp .nil
private def pairValue {context : List TypeExpr} : Term (signatureOf L) context V :=
  .op pairOp (.cons unitValue (.cons unitValue .nil))
private def caseDistinctBodies : (index : Fin (metaArities (language := L) caseRule caseSpec).length) →
    Term (signatureOf L) ((metaArities caseRule caseSpec).get index).1
      ((metaArities caseRule caseSpec).get index).2 :=
  Fin.cases unitValue (Fin.cases pairValue
    (Fin.cases (.op returnOp (.cons (.var .zero) .nil)) (fun index => Fin.elim0 index)))
private def caseDistinctRaw : Assignment :=
  [("L", ⟨[], 0, .apply "Unit" []⟩),
   ("R", ⟨[], 0, .apply "Pair" [.apply "Unit" [], .apply "Unit" []]⟩),
   ("B", ⟨[V,V], 0, .apply "Return" [.bvar 0]⟩)]
private def letOpenBodies : AmbientCorrespondence.AmbientBodies L letRule letSpec [V] :=
  Fin.cases (.var .zero)
    (Fin.cases (.op returnOp (.cons (.var (.succ .zero)) .nil)) (fun index => Fin.elim0 index))
private def letOpenRaw : Assignment :=
  [("V", ⟨[], 1, .bvar 0⟩), ("B", ⟨[V], 1, .apply "Return" [.bvar 1]⟩)]
private def caseOpenBodies : AmbientCorrespondence.AmbientBodies L caseRule caseSpec [V] :=
  Fin.cases unitValue (Fin.cases pairValue
    (Fin.cases (.op returnOp (.cons (.var (.succ (.succ .zero))) .nil)) (fun index => Fin.elim0 index)))
private def caseOpenRaw : Assignment :=
  [("L", ⟨[], 1, .apply "Unit" []⟩),
   ("R", ⟨[], 1, .apply "Pair" [.apply "Unit" [], .apply "Unit" []]⟩),
   ("B", ⟨[V,V], 1, .apply "Return" [.bvar 2]⟩)]
private def repeatedSpec : RuleBindingSpec := { caseSpec with
  occurrences := caseSpec.occurrences.map fun occurrence =>
    if occurrence.site == .right then { occurrence with arguments := [.bvar 0, .bvar 0] }
    else occurrence }
private def repeatedRule : RewriteRule := { caseRule with bindings := some repeatedSpec }
private def repeatedOutput := (outputAssembly L repeatedRule repeatedSpec .right).walk
  (sourceHeight repeatedRule.right) [] [] repeatedRule.right C
private def repeatedBodies : (index : Fin (metaArities (language := L) repeatedRule repeatedSpec).length) →
    Term (signatureOf L) ((metaArities repeatedRule repeatedSpec).get index).1
      ((metaArities repeatedRule repeatedSpec).get index).2 := caseDistinctBodies
private def repeatedLanguage : LanguageDef := { L with rewrites := [repeatedRule] }


/-- Independent source and target observations for the actual LetCase declarations. -/
def checks : List (String × Bool) :=
  [("output/old-let-output-refused", (elaborateAuthoredSchema? L ⟨0, by decide⟩ .right C).isNone),
   ("output/old-case-output-refused", (elaborateAuthoredSchema? L ⟨1, by decide⟩ .right C).isNone),
   ("output/new-let-output-admitted", (elaborateAuthoredOutput? L ⟨0, by decide⟩ .right C).isSome),
   ("output/new-case-output-admitted", (elaborateAuthoredOutput? L ⟨1, by decide⟩ .right C).isSome),
   ("output/let-source-kept", (letOutput.map (fun output => readback output.representation) == some letRule.right)),
   ("output/case-source-kept", (caseOutput.map (fun output => readback output.representation) == some caseRule.right)),
   ("output/let-instantiation-agrees", (letOutput.map (fun output => erase (instantiate letBodies output.term)) ==
      reduct? letRule letSpec 0 letRaw)),
   ("output/case-instantiation-agrees", (caseOutput.map (fun output => erase (instantiate caseBodies output.term)) ==
      reduct? caseRule caseSpec 0 caseRaw)),
   ("output/let-result", (letOutput.map (fun output => erase (instantiate letBodies output.term)) ==
      some (.apply "Return" [.apply "Unit" []]))),
   ("output/case-result", (caseOutput.map (fun output => erase (instantiate caseBodies output.term)) ==
      some (.apply "Return" [.apply "Unit" []]))),
   ("output/let-physical-occurrences", (letOutput.map (fun output => output.occurrences.map (fun ⟨_,_,path,name,_,_⟩ => (path,name))) ==
      some [([0],"B"),([1],"V")])),
   ("output/case-physical-occurrences", (caseOutput.map (fun output => output.occurrences.map (fun ⟨_,_,path,name,_,_⟩ => (path,name))) ==
      some [([0,0],"B"),([0,1],"R"),([1],"L")])),
   ("output/wrong-result-type-refused", (elaborateAuthoredOutput? L ⟨0, by decide⟩ .right V).isNone),
   ("output/input-unchanged", ((inputAssembly L letRule letSpec .left).walk (sourceHeight letRule.left) [] [] letRule.left C).isSome),
   ("output/distinct-case-arguments", (caseOutput.map (fun output => erase (instantiate caseDistinctBodies output.term)) ==
      some (.apply "Return" [.apply "Unit" []]))),
   ("output/distinct-case-engine-agrees", (caseOutput.map (fun output => erase (instantiate caseDistinctBodies output.term)) ==
      reduct? caseRule caseSpec 0 caseDistinctRaw)),
   ("output/ambient-let-kept", (letOutput.map (fun output => erase (outputInstantiation letOpenBodies output.term)) ==
      some (.apply "Return" [.bvar 0]))),
   ("output/ambient-let-engine-agrees", (letOutput.map (fun output => erase (outputInstantiation letOpenBodies output.term)) ==
      reduct? letRule letSpec 1 letOpenRaw)),
   ("output/ambient-let-capture-refused", (letOutput.map (fun output => erase (outputInstantiation letOpenBodies output.term)) !=
      some (.apply "Return" [.apply "Unit" []]))),
   ("output/ambient-case-kept", (caseOutput.map (fun output => erase (outputInstantiation caseOpenBodies output.term)) ==
      some (.apply "Return" [.bvar 0]))),
   ("output/ambient-case-engine-agrees", (caseOutput.map (fun output => erase (outputInstantiation caseOpenBodies output.term)) ==
      reduct? caseRule caseSpec 1 caseOpenRaw)),
   ("output/ambient-case-capture-refused", (caseOutput.map (fun output => erase (outputInstantiation caseOpenBodies output.term)) !=
      some (.apply "Return" [.apply "Pair" [.apply "Unit" [], .apply "Unit" []]]))),
   ("output/repeated-arguments-admitted", (elaborateAuthoredOutput? repeatedLanguage ⟨0, by decide⟩ .right C).isSome),
   ("output/repeated-arguments-not-input", (elaborateInputOccurrence? L repeatedRule repeatedSpec [V,V] .right [0,0] "B" C).isNone),
   ("output/repeated-arguments-computed", (repeatedOutput.map (fun output => erase (instantiate repeatedBodies output.term)) ==
      some (.apply "Return" [.apply "Pair" [.apply "Unit" [], .apply "Unit" []]]))),
   ("output/repeated-arguments-engine-agrees", (repeatedOutput.map (fun output => erase (instantiate repeatedBodies output.term)) ==
      reduct? repeatedRule repeatedSpec 0 caseDistinctRaw))]

theorem checks_pass : checks.all Prod.snd = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Controls.Outputs

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Controls.Schemas

open Mettapedia.OSLF Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation BindingSignatureEmbedding ClosedOperators
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

private abbrev language := Mettapedia.OSLF.NativeTypes.Instances.LetCase.language
private abbrev V : Functional.Carrier language := .sort ⟨0, by decide⟩
private abbrev C : Functional.Carrier language := .sort ⟨1, by decide⟩
private abbrev Sig := Functional.signature language
private def source : NativeSignature.Installation language := (NativeSignature.install? language).get (by decide)
private theorem unique : language.typeNames.Nodup := by decide

private def returnOp : Sig.Op C :=
  ⟨.constructor language.terms[2] (by decide)
    (by simp [Mettapedia.GSLT.LanguageDef.WellSorted.UsesBareCollection, language, Mettapedia.OSLF.NativeTypes.Instances.LetCase.language,
      Mettapedia.OSLF.NativeTypes.Instances.LetCase.value])
    (.cons (.simple "value" V.source) .nil), [([], V)], rfl⟩
private def caseOp : Sig.Op C :=
  ⟨.constructor language.terms[4] (by decide)
    (by simp [Mettapedia.GSLT.LanguageDef.WellSorted.UsesBareCollection, language, Mettapedia.OSLF.NativeTypes.Instances.LetCase.language])
    (.cons (.simple "value" V.source) (.cons (.abstraction none "body" V.source (.arrow V.source C.source)) .nil)),
    [([], V), ([V], .function V C)], rfl⟩
private def abstractionOp : Sig.Op (.function V C) :=
  ⟨.lambda V.source C.source, [([V], C)], rfl⟩
private def substitutionOp : Sig.Op C :=
  ⟨.subst V.source C.source, [([V], C), ([], V)], rfl⟩
private abbrev metas : List (Binding.MetaArity Sig) := [([V, V], C)]
private def bodies : Binding.ContextualAssignment Sig metas [V] :=
  Fin.cases (.op returnOp (.cons (.var (.succ (.succ .zero))) .nil)) (fun index => Fin.elim0 index)
private def identity : Binding.Sub Sig [V] [V] := fun _ position => .var position
private def call : Binding.Term (Binding.withMetas Sig metas) [V, V, V] C :=
  .op (.inr (.mk 0)) (.cons (.var (.succ .zero)) (.cons (.var .zero) .nil))
private def schema : Binding.Term (Binding.withMetas Sig metas) [V] C :=
  .op (.inl caseOp) (.cons (.var .zero)
    (.cons (.op (.inl abstractionOp) (.cons call .nil)) .nil))
private def expected : Binding.Term Sig [V] C :=
  .op caseOp (.cons (.var .zero)
    (.cons (abstraction (.op returnOp (.cons (.var (.succ (.succ .zero))) .nil))) .nil))
private def captured : Binding.Term Sig [V] C :=
  .op caseOp (.cons (.var .zero)
    (.cons (abstraction (.op returnOp (.cons (.var .zero) .nil))) .nil))

example : FormationSensitive.Judgment (Headers.rules source) (typeContext carrierType [V])
    (compile (images source) expected) (liftClosed (carrierType C)) := compiled_judgment source unique _

example : FormationSensitive.Judgment (Headers.rules source) (typeContext carrierType [V])
    (schemaProgram source bodies identity identity schema) (liftClosed (carrierType C)) :=
  schemaProgram_judgment source unique _ _ _ _

private def nestedSchema : Binding.Term (Binding.withMetas Sig metas) [V] C :=
  .op (.inl substitutionOp)
    (.cons (.op (.inl returnOp) (.cons (.var (.succ .zero)) .nil))
      (.cons (.var .zero) .nil))
private def instantiatedNested : Binding.Term Sig [V] C :=
  substitution (.op returnOp (.cons (.var (.succ .zero)) .nil)) (.var .zero)

example : FormationSensitive.Judgment (Headers.rules source) (typeContext carrierType [V])
    (compile (images source) instantiatedNested) (liftClosed (carrierType C)) := compiled_judgment source unique _

example : FormationSensitive.Judgment (Headers.rules source) (typeContext carrierType [V])
    (schemaProgram source bodies identity identity nestedSchema) (liftClosed (carrierType C)) :=
  schemaProgram_judgment source unique _ _ _ _


/-- Independent source and target observations for the actual LetCase declarations. -/
def checks : List (String × Bool) :=
  let program := schemaProgram source bodies identity identity schema
  let code := schemaEvidence source bodies identity identity schema
  let result := compile (images source) expected
  let nestedProgram := schemaProgram source bodies identity identity nestedSchema
  let nestedCode := schemaEvidence source bodies identity identity nestedSchema
  [("functional-schema/source-instance", (compile (images source) (Binding.ContextualAssignment.instantiate bodies identity identity schema) == result)),
   ("functional-schema/native-original-replay", (code.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot program result)),
   ("functional-schema/capture-refused", (!(code.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot program (compile (images source) captured)))),
   ("functional-schema/retained-ambient-metavalue", (code.stepCount == 3)),
   ("functional-schema/literal-source-readback", (readback expected == .apply "Case" [.bvar 0, .lambda none (.lambda none (.apply "Return" [.bvar 2]))])),
   ("functional-schema/actual-constructor-name", ((virtualNames source).operator caseOp == constructorDeclName language ⟨4, by decide⟩)),
   ("functional-schema/shared-derived-id", ((virtualNames source).operator abstractionOp == (virtualNames source).operator substitutionOp)),
   ("functional-schema/id-is-program", (expansion language ((virtualNames source).operator abstractionOp) == Derived.identity)),
   ("functional-schema/id-not-installed", ((Headers.signature source).typeOf? (identityName language)).isNone),
   ("functional-schema/native-types-retain-arrow", (carrierType (NativeSignature.Carrier.function V C) == closedArrow (carrierType V) (carrierType C))),
   ("functional-schema/substitution-not-lost", (nestedCode.check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      nestedProgram (compile (images source) instantiatedNested))),
   ("functional-schema/substitution-source-readback", (readback instantiatedNested == .subst (.apply "Return" [.bvar 1]) (.bvar 0)))]

theorem checks_pass : checks.all Prod.snd = true := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Controls.Schemas


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

open Mettapedia.OSLF
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation BindingSignatureEmbedding

variable {language : LanguageDef}

/-- Independent admission for an actual used operator's argument scopes. -/
def FunctionalArity {sort : TypeExpr} (operator : Operator language sort) : Prop :=
  ∀ slot ∈ (signatureOf language).arity operator,
    (∀ type ∈ slot.1, NativeSignature.AdmittedType language type) ∧
      NativeSignature.AdmittedType language slot.2

abbrev operatorReader (language : LanguageDef) :=
  (signatureOf language).reindexOperatorReader NativeSignature.Carrier.source
    (NativeSignature.decodeType? language) (fun _ _ known => NativeSignature.decodeType?_sound known)

private theorem decode_types {types : List TypeExpr}
    (admitted : ∀ type ∈ types, NativeSignature.AdmittedType language type) :
    ∃ carriers, types.mapM (NativeSignature.decodeType? language) = some carriers := by
  induction types with
  | nil => exact ⟨[], rfl⟩
  | cons type types inductionHypothesis =>
      obtain ⟨carrier, first⟩ := NativeSignature.decodeType?_complete (admitted type List.mem_cons_self)
      obtain ⟨carriers, rest⟩ := inductionHypothesis (fun type member => admitted type (List.mem_cons_of_mem _ member))
      exact ⟨carrier :: carriers, by simp only [List.mapM_cons, first, rest, Option.bind_eq_bind, Option.bind_some, pure]⟩

private theorem decode_slot (slot : List TypeExpr × TypeExpr)
    (admitted : (∀ type ∈ slot.1, NativeSignature.AdmittedType language type) ∧
      NativeSignature.AdmittedType language slot.2) :
    ∃ selected, Binding.SortArityDecoder.decodeArity (NativeSignature.decodeType? language) slot = some selected := by
  obtain ⟨bound, boundsRead⟩ := decode_types admitted.1
  obtain ⟨sort, sortRead⟩ := NativeSignature.decodeType?_complete admitted.2
  exact ⟨(bound, sort), by simp only [Binding.SortArityDecoder.decodeArity, boundsRead, sortRead, Option.bind_eq_bind, Option.bind_some, pure]⟩

theorem decode_arity_complete {arity : List (List TypeExpr × TypeExpr)}
    (admitted : ∀ slot ∈ arity,
      (∀ type ∈ slot.1, NativeSignature.AdmittedType language type) ∧
      NativeSignature.AdmittedType language slot.2) :
    ∃ selected, arity.mapM (Binding.SortArityDecoder.decodeArity (NativeSignature.decodeType? language)) = some selected := by
  induction arity with
  | nil => exact ⟨[], rfl⟩
  | cons slot arity inductionHypothesis =>
      obtain ⟨selected, first⟩ := decode_slot slot (admitted slot List.mem_cons_self)
      obtain ⟨rest, later⟩ := inductionHypothesis (fun slot member => admitted slot (List.mem_cons_of_mem _ member))
      exact ⟨selected :: rest, by simp only [List.mapM_cons, first, later, Option.bind_eq_bind, Option.bind_some, pure]⟩

/-- The original used-arity condition constructs the primitive reader result. -/
theorem operator_supported {sort : TypeExpr} (operator : Operator language sort)
    (admitted : FunctionalArity operator) :
    Binding.SigMor.OperatorReader.SupportedOperator (projection language) (operatorReader language) operator := by
  intro selectedSort same
  cases same
  obtain ⟨arity, decoded⟩ := decode_arity_complete admitted
  dsimp only [signatureOf, projection, Binding.Signature.reindexProjection] at decoded
  have present : ((operatorReader language).read operator).isSome = true := by
    unfold operatorReader Binding.Signature.reindexOperatorReader Binding.Signature.reindexOperator?
    dsimp only
    split
    · rename_i missing
      have impossible : (none : Option (List (List (Carrier language) × Carrier language))) = some arity :=
        missing.symm.trans decoded
      cases impossible
    · rfl
  exact Option.isSome_iff_exists.mp present

/-- Every retained operation has independently admitted source scopes. -/
theorem image_operator_supported {sort : Carrier language} (operator : (signature language).Op sort) :
    FunctionalArity operator.original := by
  intro slot member
  rw [operator.projects] at member
  obtain ⟨⟨bound, result⟩, _present, same⟩ := List.mem_map.mp member
  cases same
  refine ⟨?_, result.admitted⟩
  intro type present
  obtain ⟨carrier, _member, same⟩ := List.mem_map.mp present
  cases same
  exact carrier.admitted

/-- All operators of a projected intrinsic term have the same independent
source admission, including under every declared binding telescope. -/
theorem image_supported {bound : List (Carrier language)} {sort : Carrier language}
    (term : Binding.Term (signature language) bound sort) :
    ((projection language).onTerm term).AllOperators FunctionalArity :=
  Binding.Term.allOperators_mapTerm (projection language)
    image_operator_supported (Binding.mapVar NativeSignature.Carrier.source) term

/-- Every independently supported original term is read by the actual parser. -/
theorem term?_complete_on (unique : language.typeNames.Nodup)
    {bound : List (Carrier language)} {sort : Carrier language}
    (original : Binding.Term (signatureOf language) (bound.map NativeSignature.Carrier.source) sort.source)
    (admitted : original.AllOperators FunctionalArity) :
    ∃ selected, term? original = some selected :=
  Binding.SigMor.OperatorReader.readTerm_complete_on (projection language) (operatorReader language)
    (carrier_source_injective unique) original (admitted.mono operator_supported)

theorem term?_supported {bound : List (Carrier language)} {sort : Carrier language}
    (original : Binding.Term (signatureOf language) (bound.map NativeSignature.Carrier.source) sort.source)
    (selected : Binding.Term (signature language) bound sort) (accepted : term? original = some selected) :
    original.AllOperators FunctionalArity := by
  rw [← term?_readback original selected accepted]
  exact image_supported selected

/-- Exact original-source coverage is local to the operations actually used,
not a claim that the complete source signature has functional arity. -/
theorem term?_exact (unique : language.typeNames.Nodup)
    {bound : List (Carrier language)} {sort : Carrier language}
    (original : Binding.Term (signatureOf language) (bound.map NativeSignature.Carrier.source) sort.source) :
    (∃ selected, term? original = some selected) ↔ original.AllOperators FunctionalArity :=
  ⟨fun ⟨selected, accepted⟩ => term?_supported original selected accepted,
    term?_complete_on unique original⟩

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional
open Mettapedia.OSLF
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration BindingSignatureEmbedding
set_option autoImplicit false
variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}

/-- Actual source declaration positions, with independently decoded dependency
and result sorts. The original rule and its binding specification remain owners. -/
structure RuleMetavariables (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) where
  entries : List (Binding.MetaArity (signature language))
  decoded : (metaArities (language := language) rule spec).mapM
    (Binding.SortArityDecoder.decodeArity (NativeSignature.decodeType? language)) = some entries

def RuleMetavariables.toInterface (metadata : RuleMetavariables language rule spec) :
    Binding.SortArityDecoder.Interface (NativeSignature.decodeType? language)
      (metaArities (language := language) rule spec) := ⟨metadata.entries, metadata.decoded⟩

def ruleMetavariables? (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) :
    Option (RuleMetavariables language rule spec) :=
  match decoded : (metaArities (language := language) rule spec).mapM
      (Binding.SortArityDecoder.decodeArity (NativeSignature.decodeType? language)) with
  | none => none
  | some entries => some ⟨entries, decoded⟩

/-- Decoding retains the complete dependency telescope at every source row. -/
theorem RuleMetavariables.projects (metadata : RuleMetavariables language rule spec) :
    (projection language).mapMetas metadata.entries = metaArities rule spec :=
  Binding.SortArityDecoder.decodeArities_sound NativeSignature.Carrier.source
    (NativeSignature.decodeType? language) (fun _ _ decoded => NativeSignature.decodeType?_sound decoded)
    _ _ metadata.decoded

theorem RuleMetavariables.length (metadata : RuleMetavariables language rule spec) :
    metadata.entries.length = rule.typeContext.length := by
  exact (metadata.toInterface.length NativeSignature.Carrier.source
    (fun _ _ decoded => NativeSignature.decodeType?_sound decoded)).trans
    (metaArities_length (language := language) rule spec)

/-- Coverage is stated on the original meta-interface, before native decoding. -/
def MetavariablesAdmitted (language : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec) : Prop :=
  ∀ entry ∈ metaArities (language := language) rule spec,
    (∀ type ∈ entry.1, NativeSignature.AdmittedType language type) ∧
      NativeSignature.AdmittedType language entry.2

theorem ruleMetavariables?_complete (admitted : MetavariablesAdmitted language rule spec) :
    ∃ metadata, ruleMetavariables? language rule spec = some metadata := by
  obtain ⟨entries, found⟩ := decode_arity_complete admitted
  refine ⟨⟨entries, found⟩, ?_⟩
  unfold ruleMetavariables?
  split
  · rename_i missing
    rw [found] at missing
    cases missing
  · rename_i actual parsed
    have same : actual = entries := Option.some.inj (parsed.symm.trans found)
    cases same
    rfl

theorem RuleMetavariables.admitted (metadata : RuleMetavariables language rule spec) :
    MetavariablesAdmitted language rule spec := by
  intro entry member
  rw [← metadata.projects] at member
  obtain ⟨⟨dependencies, result⟩, _present, same⟩ := List.mem_map.mp member
  cases same
  refine ⟨?_, result.admitted⟩
  intro type present
  obtain ⟨carrier, _member, same⟩ := List.mem_map.mp present
  cases same
  exact carrier.admitted

theorem ruleMetavariables?_exact :
    (∃ metadata, ruleMetavariables? language rule spec = some metadata) ↔
      MetavariablesAdmitted language rule spec := by
  constructor
  · rintro ⟨metadata, _⟩
    exact metadata.admitted
  · exact ruleMetavariables?_complete

/-- Meta-function arguments follow the source dependency and ambient order. -/
def functionCarrier : List (Carrier language) → Carrier language → Carrier language
  | [], result => result
  | domain :: rest, result => functionCarrier rest (.function domain result)

theorem functionCarrier_type (dependencies : List (Carrier language)) (result : Carrier language) :
    carrierType (functionCarrier dependencies result) =
      ClosedOperators.spineType (S := signature language) carrierType dependencies (carrierType result) := by
  induction dependencies generalizing result with
  | nil => rfl
  | cons domain rest inductionHypothesis =>
      simpa only [functionCarrier, ClosedOperators.spineType, carrierType] using
        inductionHypothesis (.function domain result)

def RuleMetavariables.parameterSorts (metadata : RuleMetavariables language rule spec)
    (ambient : List (Carrier language)) : List (Carrier language) :=
  metadata.entries.map (fun entry => functionCarrier (entry.1 ++ ambient) entry.2)

def RuleMetavariables.parameterIndex (metadata : RuleMetavariables language rule spec)
    (ambient : List (Carrier language)) (index : Fin metadata.entries.length) :
    Fin (metadata.parameterSorts ambient).length :=
  ⟨index.val, by simpa only [RuleMetavariables.parameterSorts, List.length_map] using index.isLt⟩

def RuleMetavariables.parameterContext (metadata : RuleMetavariables language rule spec)
    (ambient : List (Carrier language)) : Ctx Tower.Head (metadata.parameterSorts ambient).length :=
  ClosedOperators.typeContext (S := signature language) carrierType (metadata.parameterSorts ambient)

/-- This is the actual native telescope lookup at the original meta position. -/
theorem RuleMetavariables.parameter_lookup (metadata : RuleMetavariables language rule spec)
    (ambient : List (Carrier language)) (index : Fin metadata.entries.length) :
    Ctx.lookup (metadata.parameterContext ambient) (metadata.parameterIndex ambient index) =
      liftClosed (ClosedOperators.spineType (S := signature language) carrierType (List.append (metadata.entries.get index).1 ambient)
        (carrierType (metadata.entries.get index).2)) := by
  have known := ClosedOperators.Formation.typeContext_lookup (S := signature language) (Head := Tower.Head) carrierType
    (Binding.varOfIdx (S := signature language) (metadata.parameterSorts ambient)
      (metadata.parameterIndex ambient index))
  rw [Binding.varIdx_varOfIdx (S := signature language) (metadata.parameterSorts ambient)
    (metadata.parameterIndex ambient index)] at known
  have selected : (metadata.parameterSorts ambient).get (metadata.parameterIndex ambient index) =
      functionCarrier (List.append (metadata.entries.get index).1 ambient) (metadata.entries.get index).2 :=
    List.getElem_map (fun (entry : Binding.MetaArity (signature language)) =>
      functionCarrier (List.append entry.1 ambient) entry.2)
      (l := metadata.entries) (i := index.val)
  apply known.trans
  apply (congrArg (fun carrier : Carrier language => liftClosed (carrierType carrier)) selected).trans
  exact congrArg liftClosed (functionCarrier_type _ _)

theorem RuleMetavariables.parameterContext_formed (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ambient : List (Carrier language)) :
    FormationSensitive.ContextFormation (Headers.rules source) (metadata.parameterContext ambient) :=
  (formation source).typeContext_formed _


/-- Rule positions and metavariable positions are separate structural tags. -/
def RuleMetavariables.namePrefix (language : LanguageDef) (ruleIndex : Nat) : DeclName :=
  .num (.str (.str .anonymous language.name) "GSLT.authored.metavariable") ruleIndex

def RuleMetavariables.declarationName (metadata : RuleMetavariables language rule spec)
    (ruleIndex : Nat) (index : Fin metadata.entries.length) : DeclName :=
  .num (RuleMetavariables.namePrefix language ruleIndex) index.val

def RuleMetavariables.positions (metadata : RuleMetavariables language rule spec)
    (ruleIndex : Nat) (ambient : List (Carrier language)) :
    DeclName → Option (Fin (metadata.parameterSorts ambient).length)
  | .num storedPrefix index =>
      if storedPrefix == RuleMetavariables.namePrefix language ruleIndex then
        if valid : index < metadata.entries.length then
          some (metadata.parameterIndex ambient ⟨index, valid⟩)
        else none
      else none
  | _ => none

theorem RuleMetavariables.positions_declared (metadata : RuleMetavariables language rule spec)
    (ruleIndex : Nat) (ambient : List (Carrier language)) (index : Fin metadata.entries.length) :
    metadata.positions ruleIndex ambient (metadata.declarationName ruleIndex index) =
      some (metadata.parameterIndex ambient index) := by
  simp [RuleMetavariables.positions, RuleMetavariables.declarationName, index.isLt]

theorem RuleMetavariables.declarationName_injective (metadata : RuleMetavariables language rule spec)
    (ruleIndex : Nat) : Function.Injective (metadata.declarationName ruleIndex) := by
  intro first second same
  apply Fin.ext
  exact (Lean.Name.num.inj same).2

theorem RuleMetavariables.positions_sort (metadata : RuleMetavariables language rule spec)
    (ruleIndex : Nat) (ambient : List (Carrier language)) (sort : Fin language.types.length) :
    metadata.positions ruleIndex ambient (sortDeclName language sort) = none := by
  simp [RuleMetavariables.positions, RuleMetavariables.namePrefix, sortDeclName]

theorem RuleMetavariables.positions_constructor (metadata : RuleMetavariables language rule spec)
    (ruleIndex : Nat) (ambient : List (Carrier language)) (constructor : Fin language.terms.length) :
    metadata.positions ruleIndex ambient (constructorDeclName language constructor) = none := by
  simp [RuleMetavariables.positions, RuleMetavariables.namePrefix, constructorDeclName]

theorem RuleMetavariables.positions_identity (metadata : RuleMetavariables language rule spec)
    (ruleIndex : Nat) (ambient : List (Carrier language)) :
    metadata.positions ruleIndex ambient (identityName language) = none := rfl

def RuleMetavariables.entry (metadata : RuleMetavariables language rule spec)
    (ambient : List (Carrier language)) (index : Fin metadata.entries.length) : Entry Tower.Head :=
  ⟨carrierType (functionCarrier (List.append (metadata.entries.get index).1 ambient)
      (metadata.entries.get index).2), none⟩

def RuleMetavariables.declarations (metadata : RuleMetavariables language rule spec)
    (ruleIndex : Nat) (ambient : List (Carrier language)) : List (DeclName × Entry Tower.Head) :=
  List.ofFn (fun index => (metadata.declarationName ruleIndex index, metadata.entry ambient index))

def RuleMetavariables.templateSignature (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) : Signature Tower.Head :=
  .ofList (metadata.declarations ruleIndex ambient ++ Headers.declarationList source)

theorem header_entries_opaque (source : NativeSignature.Installation language)
    (name : DeclName) (value : Entry Tower.Head)
    (member : (name, value) ∈ Headers.declarationList source) : value.value? = none := by
  rcases List.mem_append.mp member with sortMember | constructorMember
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp sortMember
    have entrySame : sortEntry = value := congrArg Prod.snd same
    rw [← entrySame]
    rfl
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp constructorMember
    have entrySame : headerEntry source.headers[index] = value := congrArg Prod.snd same
    rw [← entrySame]
    rfl

theorem RuleMetavariables.headers_unselected (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) (name : DeclName) (value : Entry Tower.Head)
    (member : (name, value) ∈ Headers.declarationList source) :
    metadata.positions ruleIndex ambient name = none := by
  rcases List.mem_append.mp member with sortMember | constructorMember
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp sortMember
    have nameSame : sortDeclName language index = name := congrArg Prod.fst same
    rw [← nameSame]
    exact metadata.positions_sort ruleIndex ambient index
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp constructorMember
    have nameSame : constructorDeclName language (source.origin index) = name := congrArg Prod.fst same
    rw [← nameSame]
    exact metadata.positions_constructor ruleIndex ambient _

/-- Lookup is computed from the actual finite list, not assumed by an adapter. -/
theorem RuleMetavariables.template_lookup (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) (index : Fin metadata.entries.length) :
    (metadata.templateSignature source ruleIndex ambient).entries (metadata.declarationName ruleIndex index) =
      some (metadata.entry ambient index) := by
  exact Declaration.FiniteParameters.lookup (Headers.declarationList source)
    (metadata.declarationName ruleIndex) (fun index => (metadata.entry ambient index).type)
    (metadata.declarationName_injective ruleIndex) index

theorem RuleMetavariables.entry_formed (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ambient : List (Carrier language))
    (index : Fin metadata.entries.length) :
    FormationSensitive.Typing (Headers.rules source) .nil (metadata.entry ambient index).type
      (.head (formation source).typeUniverse) :=
  (formation source).typeFormed _


/-- Abstraction of meta-functions never captures a declared source sort. -/
theorem RuleMetavariables.type_dependencies_kept (metadata : RuleMetavariables language rule spec)
    (ruleIndex : Nat) (ambient : List (Carrier language)) (sort : Carrier language) :
    ∀ name ∈ ConstantExpansion.constantNames (carrierType sort),
      metadata.positions ruleIndex ambient name = none := by
  induction sort with
  | sort position =>
      intro name present
      have same : name = sortDeclName language position := by
        simpa only [carrierType, ConstantExpansion.constantNames, List.mem_singleton] using present
      subst name
      exact metadata.positions_sort ruleIndex ambient position
  | function domain codomain domainKept codomainKept =>
      intro name present
      have member : name ∈ ConstantExpansion.constantNames (carrierType domain) ++
          ConstantExpansion.constantNames (carrierType codomain) := by
        simpa only [carrierType, closedArrow, ConstantExpansion.constantNames,
          ConstantExpansion.constantNames_liftClosed] using present
      exact (List.mem_append.mp member).elim (domainKept name) (codomainKept name)

/-- A name refused by the actual finite selector occurs in no selected entry. -/
theorem RuleMetavariables.declarations_missing (metadata : RuleMetavariables language rule spec)
    (ruleIndex : Nat) (ambient : List (Carrier language)) (name : DeclName)
    (unselected : metadata.positions ruleIndex ambient name = none) :
    (Signature.ofList (metadata.declarations ruleIndex ambient)).entries name = none := by
  exact Declaration.FiniteParameters.missing (metadata.declarationName ruleIndex)
    (fun index => (metadata.entry ambient index).type) (metadata.positions ruleIndex ambient)
    (metadata.parameterIndex ambient) (metadata.positions_declared ruleIndex ambient) name unselected

/-- All unselected original native declarations retain their literal entry. -/
theorem RuleMetavariables.template_kept (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) (name : DeclName)
    (unselected : metadata.positions ruleIndex ambient name = none) :
    (metadata.templateSignature source ruleIndex ambient).entries name =
      (Headers.signature source).entries name := by
  exact Declaration.FiniteParameters.kept (Headers.declarationList source)
    (metadata.declarationName ruleIndex) (fun index => (metadata.entry ambient index).type)
    (metadata.positions ruleIndex ambient) (metadata.parameterIndex ambient)
    (metadata.positions_declared ruleIndex ambient) name unselected

/-- A selected source-header name is a real finite sort or constructor row. -/
theorem header_name (source : NativeSignature.Installation language)
    {name : DeclName} {entry : Entry Tower.Head}
    (known : (Headers.signature source).entries name = some entry) :
    (∃ sort, name = sortDeclName language sort) ∨
      (∃ constructor, name = constructorDeclName language constructor) := by
  have member := Signature.entries_ofList_mem (Headers.declarationList source) known
  rcases List.mem_append.mp member with sortMember | constructorMember
  · obtain ⟨sort, same⟩ := List.mem_ofFn.mp sortMember
    exact Or.inl ⟨sort, (congrArg Prod.fst same).symm⟩
  · obtain ⟨constructor, same⟩ := List.mem_ofFn.mp constructorMember
    exact Or.inr ⟨source.origin constructor, (congrArg Prod.fst same).symm⟩

/-- The actual fresh finite parameter declarations extend the installed
source headers without changing their identity or authorizing computation. -/
theorem RuleMetavariables.template_extends (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) :
    (Headers.signature source).Extends (metadata.templateSignature source ruleIndex ambient) := by
  exact Declaration.FiniteParameters.extends_original (Headers.declarationList source)
    (metadata.declarationName ruleIndex) (fun index => (metadata.entry ambient index).type)
    (metadata.positions ruleIndex ambient) (metadata.parameterIndex ambient)
    (metadata.positions_declared ruleIndex ambient) (metadata.headers_unselected source ruleIndex ambient)

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional
open Mettapedia.OSLF
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration BindingSignatureEmbedding
set_option autoImplicit false
variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}

def RuleMetavariables.templateRules (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) : Rules Tower.Head :=
  extendRules Tower.rules (metadata.templateSignature source ruleIndex ambient)

def RuleMetavariables.templateFormation (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) :
    ClosedOperators.Formation (S := signature language) carrierType (metadata.templateRules source ruleIndex ambient) where
  typeUniverse := (formation source).typeUniverse
  joined := (formation source).joined
  universeIs := (formation source).universeIs
  joinSelf := (formation source).joinSelf
  collapseSelf := (formation source).collapseSelf
  typeFormed := fun sort => ((formation source).typeFormed sort).monoSignature
    (metadata.template_extends source ruleIndex ambient)

def RuleMetavariables.templateRealization (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (unique : language.typeNames.Nodup)
    (ruleIndex : Nat) (ambient : List (Carrier language)) :
    ClosedOperators.Realization carrierType (images source) (metadata.templateRules source ruleIndex ambient) where
  toFormation := metadata.templateFormation source ruleIndex ambient
  imageTyped := fun operator => ((realization source unique).imageTyped operator).monoSignature
    (metadata.template_extends source ruleIndex ambient)

theorem RuleMetavariables.function_lookup (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) (index : Fin metadata.entries.length) :
    (metadata.templateRules source ruleIndex ambient).constantType (metadata.declarationName ruleIndex index) =
      some (metadata.entry ambient index).type := by
  apply combinedType_of_signature Tower.rules _ rfl
  simp only [Signature.typeOf?, metadata.template_lookup source ruleIndex ambient index, Option.map_some]

theorem RuleMetavariables.function_typed (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) (index : Fin metadata.entries.length) :
    FormationSensitive.Typing (metadata.templateRules source ruleIndex ambient) .nil
      (.const (metadata.declarationName ruleIndex index)) (metadata.entry ambient index).type := by
  have formed := (metadata.entry_formed source ambient index).monoSignature
    (metadata.template_extends source ruleIndex ambient)
  have typed := FormationSensitive.Typing.const (Γ := Ctx.nil)
    (metadata.function_lookup source ruleIndex ambient index) formed (formation source).universeIs
  simpa only [TelescopeAbstraction.liftClosed_zero] using typed

/-- Every actual selected template entry remains opaque. -/
theorem RuleMetavariables.template_value_none (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) (name : DeclName) :
    (metadata.templateSignature source ruleIndex ambient).valueOf? name = none := by
  exact Declaration.FiniteParameters.value_none (Headers.declarationList source)
    (metadata.declarationName ruleIndex) (fun index => (metadata.entry ambient index).type)
    (header_entries_opaque source) name

/-- The template rules license no source root computation; native beta is
part of the existing structural calculus, not an extra template axiom. -/
theorem RuleMetavariables.rulesMap (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) :
    ConstantSubstitution.RulesMap (metadata.templateRules source ruleIndex ambient) (Headers.rules source) := by
  exact Declaration.FiniteParameters.rulesMap Tower.rules (fun impossible => impossible.elim)
    (Headers.declarationList source) (metadata.declarationName ruleIndex)
    (fun index => (metadata.entry ambient index).type) (header_entries_opaque source)
    (Headers.signature source)

/-- Source constant lookup exposes the actual selected finite entry. -/
theorem RuleMetavariables.constant_entry (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) {name : DeclName} {type : Tower.Tm 0}
    (known : (metadata.templateRules source ruleIndex ambient).constantType name = some type) :
    ∃ entry, (metadata.templateSignature source ruleIndex ambient).entries name = some entry ∧
      entry.type = type := by
  exact Declaration.FiniteParameters.constant_entry Tower.rules (fun _ => rfl)
    (Headers.declarationList source) (metadata.declarationName ruleIndex)
    (fun index => (metadata.entry ambient index).type) known

theorem RuleMetavariables.parameterTypes_dependencies_kept
    (metadata : RuleMetavariables language rule spec) (ruleIndex : Nat)
    (ambient : List (Carrier language)) (parameters : List (Carrier language)) (result : Tower.Tm 0)
    (resultKept : ∀ name ∈ ConstantExpansion.constantNames result,
      metadata.positions ruleIndex ambient name = none) :
    ∀ name ∈ ConstantExpansion.constantNames (parameterTypes parameters result),
      metadata.positions ruleIndex ambient name = none := by
  induction parameters with
  | nil => exact resultKept
  | cons parameter parameters inductionHypothesis =>
      intro name present
      have member : name ∈ ConstantExpansion.constantNames (carrierType parameter) ++
          ConstantExpansion.constantNames (parameterTypes parameters result) := by
        simpa only [parameterTypes, closedArrow, ConstantExpansion.constantNames,
          ConstantExpansion.constantNames_liftClosed] using present
      exact (List.mem_append.mp member).elim
        (metadata.type_dependencies_kept ruleIndex ambient parameter name) (inductionHypothesis name)

theorem RuleMetavariables.header_dependencies_kept
    (metadata : RuleMetavariables language rule spec) (ruleIndex : Nat)
    (ambient : List (Carrier language)) (header : NativeSignature.Header language) :
    ∀ name ∈ ConstantExpansion.constantNames (headerType header),
      metadata.positions ruleIndex ambient name = none := by
  apply metadata.parameterTypes_dependencies_kept
  intro name present
  have same : name = sortDeclName language header.result := by
    simpa only [ConstantExpansion.constantNames, List.mem_singleton] using present
  subst name
  exact metadata.positions_sort ruleIndex ambient header.result

/-- Neither source sort types, constructor types nor new function types
capture a metavariable constant during parameter abstraction. -/
theorem RuleMetavariables.template_dependencies_kept
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) {name : DeclName} {type : Tower.Tm 0}
    (known : (metadata.templateRules source ruleIndex ambient).constantType name = some type) :
    ∀ dependency ∈ ConstantExpansion.constantNames type,
      metadata.positions ruleIndex ambient dependency = none := by
  obtain ⟨entry, selected, sameType⟩ := metadata.constant_entry source ruleIndex ambient known
  subst type
  have member := Signature.entries_ofList_mem
    (metadata.declarations ruleIndex ambient ++ Headers.declarationList source) selected
  rcases List.mem_append.mp member with metaMember | originalMember
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp metaMember
    have entryEq : metadata.entry ambient index = entry := congrArg Prod.snd same
    rw [← entryEq]
    exact metadata.type_dependencies_kept ruleIndex ambient _
  · rcases List.mem_append.mp originalMember with sortMember | constructorMember
    · obtain ⟨index, same⟩ := List.mem_ofFn.mp sortMember
      have entryEq : sortEntry = entry := congrArg Prod.snd same
      rw [← entryEq]
      intro dependency impossible
      cases impossible
    · obtain ⟨index, same⟩ := List.mem_ofFn.mp constructorMember
      have entryEq : headerEntry source.headers[index] = entry := congrArg Prod.snd same
      rw [← entryEq]
      exact metadata.header_dependencies_kept ruleIndex ambient _

/-- Original selected headers have independently formed native types. -/
theorem header_entry_formed (source : NativeSignature.Installation language)
    {name : DeclName} {entry : Entry Tower.Head}
    (known : (Headers.signature source).entries name = some entry) :
    ∃ universeHead, FormationSensitive.Typing (Headers.rules source) .nil entry.type (.head universeHead) ∧
      (Headers.rules source).isUniverse universeHead := by
  have member := Signature.entries_ofList_mem (Headers.declarationList source) known
  rcases List.mem_append.mp member with sortMember | constructorMember
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp sortMember
    have entryEq : sortEntry = entry := congrArg Prod.snd same
    rw [← entryEq]
    exact ⟨.sort (.succ Tower.zero), .headType (.sort Tower.zero), .sort _⟩
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp constructorMember
    have entryEq : headerEntry source.headers[index] = entry := congrArg Prod.snd same
    rw [← entryEq]
    exact ⟨.sort Tower.zero, Headers.headerType_formed source _, .sort _⟩


/-- An actually selected primitive name resolves to the original parameter
slot and its independently formed function type. -/
theorem RuleMetavariables.selected_lookup (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) {name : DeclName} {type : Tower.Tm 0}
    {position : Fin (metadata.parameterSorts ambient).length}
    (known : (metadata.templateRules source ruleIndex ambient).constantType name = some type)
    (chosen : metadata.positions ruleIndex ambient name = some position) :
    Ctx.lookup (metadata.parameterContext ambient) position = liftClosed type := by
  apply Declaration.FiniteParameters.selected_lookup Tower.rules (fun _ => rfl)
    (Headers.declarationList source) (metadata.declarationName ruleIndex)
    (fun index => (metadata.entry ambient index).type) (metadata.positions ruleIndex ambient)
    (metadata.parameterIndex ambient) (metadata.positions_declared ruleIndex ambient)
    (metadata.headers_unselected source ruleIndex ambient) (metadata.parameterContext ambient) _ known chosen
  intro index
  exact (metadata.parameter_lookup ambient index).trans
    (congrArg liftClosed (functionCarrier_type
      (List.append (metadata.entries.get index).1 ambient) (metadata.entries.get index).2).symm)

/-- Kept names retain both their original literal type and its refined
formation in the actual destination signature. -/
theorem RuleMetavariables.kept_type (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) {name : DeclName} {type : Tower.Tm 0}
    (known : (metadata.templateRules source ruleIndex ambient).constantType name = some type)
    (unchosen : metadata.positions ruleIndex ambient name = none) :
    (Headers.rules source).constantType name = some type ∧
      ∃ universeHead, FormationSensitive.Typing (Headers.rules source) .nil type (.head universeHead) ∧
        (Headers.rules source).isUniverse universeHead := by
  obtain ⟨entry, selected, sameType⟩ := metadata.constant_entry source ruleIndex ambient known
  rw [metadata.template_kept source ruleIndex ambient name unchosen] at selected
  constructor
  · apply combinedType_of_signature Tower.rules _ rfl
    simp only [Signature.typeOf?, selected, Option.map_some, sameType]
  · rw [← sameType]
    exact header_entry_formed source selected

/-- Actual finite source declarations and literal native context lookups earn
the primitive contract for all parameterized template derivations. -/
theorem RuleMetavariables.parameter_values_typed (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) :
    ConstantSubstitution.TypedValues (metadata.templateRules source ruleIndex ambient) (Headers.rules source)
      (metadata.parameterContext ambient) (ConstantSubstitution.parameterValues (metadata.positions ruleIndex ambient)) :=
  ConstantSubstitution.TypedValues.ofDeclarationParameters
    (metadata.template_dependencies_kept source ruleIndex ambient)
    (metadata.selected_lookup source ruleIndex ambient)
    (metadata.kept_type source ruleIndex ambient)


/-- Every selected declaration type in the finite intermediate signature is
formed before the native function parameters are abstracted. -/
theorem RuleMetavariables.template_type_formed (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) {name : DeclName} {type : Tower.Tm 0}
    (known : (metadata.templateSignature source ruleIndex ambient).typeOf? name = some type) :
    ∃ universeHead, FormationSensitive.Typing (metadata.templateRules source ruleIndex ambient)
        .nil type (.head universeHead) ∧ Tower.rules.isUniverse universeHead := by
  have actual : (metadata.templateRules source ruleIndex ambient).constantType name = some type := known
  obtain ⟨entry, selected, sameType⟩ := metadata.constant_entry source ruleIndex ambient actual
  subst type
  have member := Signature.entries_ofList_mem
    (metadata.declarations ruleIndex ambient ++ Headers.declarationList source) selected
  rcases List.mem_append.mp member with metaMember | originalMember
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp metaMember
    have entryEq : metadata.entry ambient index = entry := congrArg Prod.snd same
    rw [← entryEq]
    exact ⟨(formation source).typeUniverse,
      (metadata.entry_formed source ambient index).monoSignature
        (metadata.template_extends source ruleIndex ambient), (formation source).universeIs⟩
  · rcases List.mem_append.mp originalMember with sortMember | constructorMember
    · obtain ⟨index, same⟩ := List.mem_ofFn.mp sortMember
      have entryEq : sortEntry = entry := congrArg Prod.snd same
      rw [← entryEq]
      exact ⟨.sort (.succ Tower.zero), .headType (.sort Tower.zero), .sort _⟩
    · obtain ⟨index, same⟩ := List.mem_ofFn.mp constructorMember
      have entryEq : headerEntry source.headers[index] = entry := congrArg Prod.snd same
      rw [← entryEq]
      exact ⟨.sort Tower.zero, (Headers.headerType_formed source _).monoSignature
        (metadata.template_extends source ruleIndex ambient), .sort _⟩

/-- Actual finite native installation, including freshness, formation and
opaque definition/refusal discipline. -/
theorem RuleMetavariables.template_wellFormed (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) :
    (metadata.templateSignature source ruleIndex ambient).WellFormed Tower.rules := by
  exact Declaration.FiniteParameters.wellFormed Tower.rules (fun _ => rfl)
    (Headers.declarationList source) (metadata.declarationName ruleIndex)
    (fun index => (metadata.entry ambient index).type) (header_entries_opaque source)
    (fun _ _ known => metadata.template_type_formed source ruleIndex ambient known)

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional
open Mettapedia.OSLF
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation BindingSignatureEmbedding
set_option autoImplicit false
variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}

private def castSchemaRows {source : Binding.Signature}
    {first second : List (Binding.MetaArity source)} (same : first = second)
    {bound : Binding.Ctx source} {sort : source.Srt}
    (term : Binding.Term (Binding.withMetas source first) bound sort) :
    Binding.Term (Binding.withMetas source second) bound sort := same ▸ term

/-- The original schema is transported only across the computed equality of
its metavariable rows. No syntax or binding argument is normalized. -/
def RuleMetavariables.schemaSource (metadata : RuleMetavariables language rule spec)
    {bound : List (Carrier language)} {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) bound sort) :
    Binding.Term (Binding.withMetas (signatureOf language) (metaArities rule spec))
      (bound.map NativeSignature.Carrier.source) sort.source :=
  castSchemaRows metadata.projects (((projection language).withMetas metadata.entries).onTerm term)

def RuleMetavariables.schema? (metadata : RuleMetavariables language rule spec)
    {bound : List (Carrier language)} {sort : Carrier language}
    (original : Binding.Term (Binding.withMetas (signatureOf language) (metaArities rule spec))
      (bound.map NativeSignature.Carrier.source) sort.source) :
    Option (Binding.Term (Binding.withMetas (signature language) metadata.entries) bound sort) :=
  Binding.SigMor.OperatorReader.readTerm ((projection language).withMetas metadata.entries)
    (Binding.SigMor.OperatorReader.withMetas (projection language) (operatorReader language) metadata.entries)
    (castSchemaRows metadata.projects.symm original)

private theorem schema_cast_cancel {source : Binding.Signature}
    {first second : List (Binding.MetaArity source)} (same : first = second)
    {bound : Binding.Ctx source} {sort : source.Srt}
    (term : Binding.Term (Binding.withMetas source second) bound sort) :
    castSchemaRows same (castSchemaRows same.symm term) = term := by
  cases same
  rfl

theorem RuleMetavariables.schema?_readback
    (metadata : RuleMetavariables language rule spec)
    {bound : List (Carrier language)} {sort : Carrier language}
    (original : Binding.Term (Binding.withMetas (signatureOf language) (metaArities rule spec))
      (bound.map NativeSignature.Carrier.source) sort.source)
    (selected : Binding.Term (Binding.withMetas (signature language) metadata.entries) bound sort)
    (accepted : metadata.schema? original = some selected) :
    metadata.schemaSource selected = original := by
  have projected := Binding.SigMor.OperatorReader.readTerm_projects
    ((projection language).withMetas metadata.entries)
    (Binding.SigMor.OperatorReader.withMetas (projection language) (operatorReader language) metadata.entries)
    (castSchemaRows metadata.projects.symm original) selected accepted
  exact (congrArg (fun term => castSchemaRows metadata.projects term) projected).trans
    (schema_cast_cancel metadata.projects original)

theorem RuleMetavariables.schema?_roundtrip
    (metadata : RuleMetavariables language rule spec) (unique : language.typeNames.Nodup)
    {bound : List (Carrier language)} {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) bound sort) :
    metadata.schema? (metadata.schemaSource term) = some term := by
  have casts : castSchemaRows metadata.projects.symm (metadata.schemaSource term) =
      ((projection language).withMetas metadata.entries).onTerm term := by
    exact schema_cast_cancel metadata.projects.symm _
  unfold RuleMetavariables.schema?
  apply (congrArg (Binding.SigMor.OperatorReader.readTerm
    ((projection language).withMetas metadata.entries)
    (Binding.SigMor.OperatorReader.withMetas (projection language) (operatorReader language) metadata.entries)) casts).trans
  exact Binding.SigMor.OperatorReader.readWithMetas_roundtrip
    (projection language) (operatorReader language) (fun operator => operator?_roundtrip unique operator)
    metadata.entries term

/-- Fixed-fibre source coding is injective because the executed reader
recovers every original operator, dependency argument and binder position. -/
theorem RuleMetavariables.schemaSource_injective
    (metadata : RuleMetavariables language rule spec) (unique : language.typeNames.Nodup)
    {bound : List (Carrier language)} {sort : Carrier language} :
    Function.Injective (metadata.schemaSource (bound := bound) (sort := sort)) := by
  intro first second same
  have decoded := congrArg (fun original => metadata.schema? original) same
  exact Option.some.inj ((metadata.schema?_roundtrip unique first).symm.trans
    (decoded.trans (metadata.schema?_roundtrip unique second)))

/-- The source profile checks actual primitive argument scopes; declared
metavariable operators use their independently decoded interface. -/
def FunctionalSchemaOperator {metas : List (Binding.MetaArity (signatureOf language))}
    {sort : TypeExpr}
    (operator : (Binding.withMetas (signatureOf language) metas).Op sort) : Prop :=
  match operator with
  | .inl primitive => FunctionalArity primitive
  | .inr _ => True

private theorem castSchemaRows_supported
    {first second : List (Binding.MetaArity (signatureOf language))} (same : first = second)
    {bound : List TypeExpr} {sort : TypeExpr}
    {term : Binding.Term (Binding.withMetas (signatureOf language) first) bound sort}
    (supported : term.AllOperators FunctionalSchemaOperator) :
    (castSchemaRows same term).AllOperators FunctionalSchemaOperator := by
  cases same
  exact supported

/-- Actual used constructor support, not a globally assumed availability
callback, suffices for complete reading of the original source schema. -/
theorem RuleMetavariables.schema?_complete_on
    (metadata : RuleMetavariables language rule spec) (unique : language.typeNames.Nodup)
    {bound : List (Carrier language)} {sort : Carrier language}
    (original : Binding.Term (Binding.withMetas (signatureOf language) (metaArities rule spec))
      (bound.map NativeSignature.Carrier.source) sort.source)
    (supported : original.AllOperators FunctionalSchemaOperator) :
    ∃ selected, metadata.schema? original = some selected := by
  have retained := castSchemaRows_supported metadata.projects.symm supported
  apply Binding.SigMor.OperatorReader.readWithMetas_complete_on
    (projection language) (operatorReader language) (carrier_source_injective unique) metadata.entries
    (castSchemaRows metadata.projects.symm original)
  apply retained.mono
  intro sort operator required
  cases operator with
  | inl primitive => exact operator_supported primitive required
  | inr _ => trivial

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Controls.ScopedEndpoints

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration
private abbrev V : TypeExpr := .base "Value"
private def step : ScopedStepPremise := {
  binders := [V], resultType := V,
  source := .subst (.bvar 1) (.bvar 0), target := .bvar 0 }
private def rule : RewriteRule := {
  name := "ScopedOutput", typeContext := [], premises := [.scopedStep step],
  left := .apply "Unit" [], right := .apply "Unit" [],
  bindings := some { dependencies := [] } }
private def language : LanguageDef :=
  { Mettapedia.OSLF.NativeTypes.Instances.LetCase.language with rewrites := [rule] }

def checks : List (String × Bool) := [
  ("actual-let-source-premise", (elaborateAuthoredOutput?
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.language ⟨3, by decide⟩
    (.premise 0 0 0) (.base "Computation")).isSome),
  ("actual-let-target-premise", (elaborateAuthoredOutput?
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.language ⟨3, by decide⟩
    (.premise 0 0 1) (.base "Computation")).isSome),
  ("actual-let-retains-one-binder", ((elaborateAuthoredOutput?
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.language ⟨3, by decide⟩
    (.premise 0 0 0) (.base "Computation")).map fun value => value.locals) == some [.base "Value"]),
  ("actual-case-source-premise", (elaborateAuthoredOutput?
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.language ⟨4, by decide⟩
    (.premise 0 0 0) (.base "Computation")).isSome),
  ("actual-case-target-premise", (elaborateAuthoredOutput?
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.language ⟨4, by decide⟩
    (.premise 0 0 1) (.base "Computation")).isSome),
  ("actual-case-retains-two-binders", ((elaborateAuthoredOutput?
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.language ⟨4, by decide⟩
    (.premise 0 0 0) (.base "Computation")).map fun value => value.locals) ==
      some [.base "Value", .base "Value"]),
  ("actual-case-wrong-carrier-refuses", (elaborateAuthoredOutput?
    Mettapedia.OSLF.NativeTypes.Instances.LetCase.language ⟨4, by decide⟩
    (.premise 0 0 0) (.base "Value")).isNone),
  ("original-step-binders", siteBinders? rule (.premise 0 0 0) == some [V]),
  ("both-endpoints-keep-binders", siteBinders? rule (.premise 0 0 1) == some [V]),
  ("invalid-endpoint-refuses", (siteBinders? rule (.premise 0 0 2)).isNone),
  ("invalid-quantifier-refuses", (siteBinders? rule (.premise 0 1 0)).isNone),
  ("invalid-premise-refuses", (siteBinders? rule (.premise 1 0 0)).isNone),
  ("authored-wrapper-uses-original-scope", (elaborateAuthoredOutput? language ⟨0, by decide⟩ (.premise 0 0 0) V).isSome),
  ("actual-scoped-source-admitted", (elaborateAuthoredOutput? language ⟨0, by decide⟩ (.premise 0 0 0) V).isSome),
  ("actual-scoped-target-admitted", (elaborateAuthoredOutput? language ⟨0, by decide⟩ (.premise 0 0 1) V).isSome),
  ("source-raw-substitution-retained", ((elaborateAuthoredOutput? language ⟨0, by decide⟩ (.premise 0 0 0) V).map fun value => value.source) == some step.source),
  ("source-binder-list-retained", ((elaborateAuthoredOutput? language ⟨0, by decide⟩ (.premise 0 0 0) V).map fun value => value.locals) == some step.binders),
  ("wrong-sort-refused", (elaborateAuthoredOutput? language ⟨0, by decide⟩ (.premise 0 0 0) (.arrow V V)).isNone)
]
theorem checks_pass : checks.all Prod.snd = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Controls.ScopedEndpoints

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Controls.OutputArguments

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration
private abbrev V : TypeExpr := .base "Value"
private abbrev C : TypeExpr := .base "Computation"
private def unit : Pattern := .apply "Unit" []
private def pair : Pattern := .apply "Pair" [unit, unit]
private def spec (argument : Pattern) : RuleBindingSpec := {
  dependencies := [("B", [V])]
  occurrences := [
    { name := "B", site := .left, path := [1, 0], arguments := [.bvar 0] },
    { name := "B", site := .right, path := [], arguments := [argument] } ] }
private def rule (argument : Pattern) : RewriteRule := {
  name := "GroundDependency", typeContext := [("B", C)], premises := [],
  left := .apply "Let" [.apply "Return" [unit], .lambda none (.fvar "B")],
  right := .fvar "B", bindings := some (spec argument) }
private def language (argument : Pattern) : LanguageDef :=
  { Mettapedia.OSLF.NativeTypes.Instances.LetCase.language with rewrites := [rule argument] }
private def ground? (source : Pattern) (sort : TypeExpr) :=
  groundOutputTerm? (language pair) (rule pair) (spec pair) .right [] source sort
private def occurrence? (argument : Pattern) :=
  elaborateOutputOccurrence? (language argument) (rule argument) (spec argument)
    [] .right [] "B" C
private def output? (argument : Pattern) :=
  (outputAssembly (language argument) (rule argument) (spec argument) .right).walk
    (sourceHeight (.fvar "B")) [] [] (.fvar "B") C
private def raw : Assignment := [
  ("B", { dependencies := [V], ambient := 0, body := .apply "Return" [.bvar 0] }) ]
private def explicit : Pattern := .subst (.bvar 0) unit

def checks : List (String × Bool) := [
  ("original-ground-metadata-admitted", admittedFor (rule pair) (spec pair)),
  ("dependency-sort-declared", dependencySortsDeclared (language pair) (spec pair)),
  ("input-inverse-spine-still-admitted", (compileSchemaWithFuel? (language pair) (rule pair)
    (spec pair) .left (sourceHeight (rule pair).left) [] [] (rule pair).left C).isSome),
  ("old-variable-only-output-refuses-ground-term", (elaborateOccurrence? (language pair)
    (rule pair) (spec pair) [] .right [] "B" C).isNone),
  ("new-output-accepts-ground-constructor", (occurrence? pair).isSome),
  ("new-output-retains-exact-argument", ((occurrence? pair).map fun value =>
    eraseArguments value.arguments) == some [pair]),
  ("whole-output-accepts-ground-constructor", (output? pair).isSome),
  ("whole-output-retains-source-metavariable", ((output? pair).map fun value =>
    readback value.representation) == some (.fvar "B")),
  ("actual-source-applies-constructor-argument", instantiateAt? (rule pair) (spec pair)
    0 .right [] 0 raw (.fvar "B") == some (.apply "Return" [pair])),
  ("ground-unit-admitted", (ground? unit V).isSome),
  ("ground-pair-admitted", (ground? pair V).isSome),
  ("ground-lambda-admitted", (ground? (.lambda none (.bvar 0)) (.arrow V V)).isSome),
  ("ground-lambda-body-retained", ((ground? (.lambda none (.bvar 0)) (.arrow V V)).map
    fun value => erase value.val) == some (.lambda none (.bvar 0))),
  ("ground-explicit-substitution-admitted", (ground? explicit V).isSome),
  ("ground-explicit-substitution-not-normalized", ((ground? explicit V).map
    fun value => erase value.val) == some explicit),
  ("dependency-explicit-substitution-admitted", (occurrence? explicit).isSome),
  ("dependency-explicit-substitution-retained", ((occurrence? explicit).map
    fun value => eraseArguments value.arguments) == some [explicit]),
  ("actual-source-retains-data-substitution", instantiateAt? (rule explicit) (spec explicit)
    0 .right [] 0 raw (.fvar "B") == some (.apply "Return" [explicit])),
  ("ground-free-variable-refuses", (ground? (.fvar "B") C).isNone),
  ("ground-out-of-scope-variable-refuses", (ground? (.bvar 0) V).isNone),
  ("ground-lambda-capture-refuses", (ground? (.lambda none (.bvar 1)) (.arrow V V)).isNone),
  ("ground-constructor-wrong-sort-refuses", (ground? unit C).isNone),
  ("ground-unknown-constructor-refuses", (ground? (.apply "Unknown" []) V).isNone),
  ("dependency-wrong-sort-refuses", (occurrence? (.apply "Return" [unit])).isNone),
  ("dependency-unknown-constructor-refuses", (occurrence? (.apply "Unknown" [])).isNone),
  ("dependency-dangling-variable-refuses", (occurrence? (.bvar 0)).isNone),
  ("ground-metadata-does-not-admit-fvar", (occurrence? (.fvar "B")).isNone),
  ("ground-argument-arity-refuses", (groundOutputArguments? (language pair) (rule pair)
    (spec pair) .right [] [unit] []).isNone)
]
theorem checks_pass : checks.all Prod.snd = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Controls.OutputArguments

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Controls.RuleMetavariables

open Mettapedia.OSLF Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration BindingSignatureEmbedding ClosedOperators
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

private abbrev language := Mettapedia.OSLF.NativeTypes.Instances.LetCase.language
private abbrev rule := Mettapedia.OSLF.NativeTypes.Instances.LetCase.caseRule
private def spec : RuleBindingSpec := rule.bindings.getD { dependencies := [] }
private abbrev V : Functional.Carrier language := .sort ⟨0, by decide⟩
private abbrev C : Functional.Carrier language := .sort ⟨1, by decide⟩
private abbrev Sig := Functional.signature language
private def source : NativeSignature.Installation language :=
  (NativeSignature.install? language).get (by decide)
private theorem unique : language.typeNames.Nodup := by decide
private def metadata : RuleMetavariables language rule spec :=
  (ruleMetavariables? language rule spec).get (by decide +kernel)
private def bodyIndex : Fin metadata.entries.length := ⟨2, by decide⟩
private def call : Binding.Term (Binding.withMetas Sig metadata.entries) [V, V] C :=
  .op (.inr (.mk bodyIndex)) (.cons (.var (.succ .zero)) (.cons (.var .zero) .nil))
private def reversed : Binding.Term (Binding.withMetas Sig metadata.entries) [V, V] C :=
  .op (.inr (.mk bodyIndex)) (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))

private def codeNames : Names (Binding.withMetas Sig metadata.entries) where
  sort := (virtualNames source).sort
  operator operator := match operator with
    | .inl primitive => (virtualNames source).operator primitive
    | .inr (.mk index) => metadata.declarationName 1 index
private def code {bound : Binding.Ctx Sig} {sort : Sig.Srt}
    (term : Binding.Term (Binding.withMetas Sig metadata.entries) bound sort) : Tower.Tm bound.length :=
  encode codeNames term

example : (metadata.templateSignature source 1 [V]).WellFormed Tower.rules :=
  metadata.template_wellFormed source 1 [V]
example : FormationSensitive.Typing (metadata.templateRules source 1 [V]) .nil
    (.const (metadata.declarationName 1 bodyIndex)) (metadata.entry [V] bodyIndex).type :=
  metadata.function_typed source 1 [V] bodyIndex
example : ConstantSubstitution.TypedValues (metadata.templateRules source 1 [V]) (Headers.rules source)
    (metadata.parameterContext [V]) (ConstantSubstitution.parameterValues (metadata.positions 1 [V])) :=
  metadata.parameter_values_typed source 1 [V]
example : metadata.schema? (metadata.schemaSource call) = some call :=
  metadata.schema?_roundtrip unique call
example : metadata.schemaSource call ≠ metadata.schemaSource reversed := by
  intro same
  have decoded := congrArg (fun original => (metadata.schema? original).map code) same
  rw [metadata.schema?_roundtrip unique call, metadata.schema?_roundtrip unique reversed] at decoded
  exact (by decide +kernel : code call ≠ code reversed) (Option.some.inj decoded)

def checks : List (String × Bool) := [
  ("actual-case-interface-decodes", (ruleMetavariables? language rule spec).isSome),
  ("actual-three-meta-rows", metadata.entries.length == 3),
  ("original-dependency-telescope-retained", (metadata.entries.get bodyIndex).1 == [V, V]),
  ("original-result-retained", (metadata.entries.get bodyIndex).2 == C),
  ("finite-meta-declaration-count", (metadata.declarations 1 [V]).length == 3),
  ("finite-full-declaration-count", (metadata.declarations 1 [V] ++ Headers.declarationList source).length == 10),
  ("actual-meta-lookup", (metadata.templateSignature source 1 [V]).typeOf?
    (metadata.declarationName 1 bodyIndex) == some (metadata.entry [V] bodyIndex).type),
  ("meta-parameter-position-retained", metadata.positions 1 [V] (metadata.declarationName 1 bodyIndex) ==
    some (metadata.parameterIndex [V] bodyIndex)),
  ("meta-parameter-actual-ctx-lookup", Ctx.lookup (metadata.parameterContext [V]) (metadata.parameterIndex [V] bodyIndex) ==
    liftClosed (spineType (S := Sig) carrierType [V, V, V] (carrierType C))),
  ("meta-parameter-wrong-rule-refuses", (metadata.positions 2 [V] (metadata.declarationName 1 bodyIndex)).isNone),
  ("meta-parameter-unknown-row-refuses", (metadata.positions 1 [V] (.num (RuleMetavariables.namePrefix language 1) 3)).isNone),
  ("meta-parameter-sort-not-captured", (metadata.positions 1 [V] (sortDeclName language ⟨0, by decide⟩)).isNone),
  ("meta-parameter-constructor-not-captured", (metadata.positions 1 [V] (constructorDeclName language ⟨4, by decide⟩)).isNone),
  ("meta-parameter-derived-identity-not-captured", (metadata.positions 1 [V] (identityName language)).isNone),
  ("actual-sort-declaration-kept", (metadata.templateSignature source 1 [V]).typeOf? (sortDeclName language ⟨0, by decide⟩) ==
    (Headers.signature source).typeOf? (sortDeclName language ⟨0, by decide⟩)),
  ("actual-constructor-declaration-kept", (metadata.templateSignature source 1 [V]).typeOf? (constructorDeclName language ⟨4, by decide⟩) ==
    (Headers.signature source).typeOf? (constructorDeclName language ⟨4, by decide⟩)),
  ("meta-constants-remain-opaque", ((metadata.templateSignature source 1 [V]).valueOf? (metadata.declarationName 1 bodyIndex)).isNone),
  ("original-schema-reader-retains-meta-arguments", (metadata.schema? (metadata.schemaSource call)).map code == some (code call)),
  ("original-schema-reader-retains-reversed-arguments", (metadata.schema? (metadata.schemaSource reversed)).map code == some (code reversed)),
  ("source-meta-argument-order-distinguishes", !((metadata.schema? (metadata.schemaSource call)).map code == (metadata.schema? (metadata.schemaSource reversed)).map code))
]
theorem checks_pass : checks.all Prod.snd = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Controls.RuleMetavariables


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

open Mettapedia.OSLF
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration BindingSignatureEmbedding

variable {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}

/-- Read the actual parameter context position at the retained source row. -/
def RuleMetavariables.sourceIndex (metadata : RuleMetavariables language rule spec)
    (ambient : List (Carrier language))
    (position : Fin (metadata.parameterSorts ambient).length) : Fin metadata.entries.length :=
  ⟨position.val, by
    simpa only [RuleMetavariables.parameterSorts, List.length_map] using position.isLt⟩

theorem RuleMetavariables.parameterIndex_sourceIndex
    (metadata : RuleMetavariables language rule spec) (ambient : List (Carrier language))
    (position : Fin (metadata.parameterSorts ambient).length) :
    metadata.parameterIndex ambient (metadata.sourceIndex ambient position) = position := Fin.ext rfl

theorem RuleMetavariables.sourceIndex_parameterIndex
    (metadata : RuleMetavariables language rule spec) (ambient : List (Carrier language))
    (position : Fin metadata.entries.length) :
    metadata.sourceIndex ambient (metadata.parameterIndex ambient position) = position := Fin.ext rfl

/-- The original finite declaration selector, with its parameter-context
index read back at the unchanged source metavariable position. -/
def RuleMetavariables.sourcePositions (metadata : RuleMetavariables language rule spec)
    (ruleIndex : Nat) (name : DeclName) : Option (Fin metadata.entries.length) :=
  (metadata.positions ruleIndex [] name).map (metadata.sourceIndex [])

theorem RuleMetavariables.sourcePositions_declared
    (metadata : RuleMetavariables language rule spec) (ruleIndex : Nat)
    (index : Fin metadata.entries.length) :
    metadata.sourcePositions ruleIndex (metadata.declarationName ruleIndex index) = some index := by
  simp only [RuleMetavariables.sourcePositions, metadata.positions_declared, Option.map_some]
  rfl

/-- Every actual constructor name and derived structural-program name is
outside the finite metavariable declaration block. -/
theorem RuleMetavariables.positions_intermediate
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    (ambient : List (Carrier language)) {result : TypeExpr} (operator : Operator language result)
    (sort : Carrier language) (resultRead : sort.source = result) :
    metadata.positions ruleIndex ambient
      (operatorIntermediateName source operator sort resultRead) = none := by
  cases operator with
  | constructor declaration member ordinary parameters =>
      exact metadata.positions_constructor ruleIndex ambient _
  | collectionConstructor declaration member name kind element shape count =>
      exact False.elim (no_collection_constructor source declaration member name kind element
        ((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2)
  | lambda domain codomain => exact metadata.positions_identity ruleIndex ambient
  | multiLambda domain codomain count =>
      cases sort with
      | sort position => cases resultRead
      | function first last =>
          have domains := (TypeExpr.arrow.inj resultRead).1
          cases first <;> cases domains
  | subst domain codomain => exact metadata.positions_identity ruleIndex ambient
  | collection kind element count => cases sort <;> cases resultRead

theorem RuleMetavariables.sourcePositions_operator
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    {sort : Carrier language} (operator : (signature language).Op sort) :
    metadata.sourcePositions ruleIndex ((virtualNames source).operator operator) = none := by
  change Option.map _ (metadata.positions ruleIndex []
    (operatorIntermediateName source operator.original sort rfl)) = none
  rw [metadata.positions_intermediate]
  rfl

theorem RuleMetavariables.declarationName_ne_identity
    (metadata : RuleMetavariables language rule spec) (ruleIndex : Nat)
    (index : Fin metadata.entries.length) :
    metadata.declarationName ruleIndex index ≠ identityName language := by
  intro impossible
  cases impossible

/-- Source rule templates contain the actual finite metavariable constants.
The ambient environment is supplied only at specialization. -/
def RuleMetavariables.fixedTemplate (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    {input : Binding.Ctx (signature language)} {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) input sort) :
    Tower.Tm input.length :=
  ConstantExpansion.expand (expansion language)
    (BindingSignatureEmbedding.Schema.fixedTemplate (virtualNames source)
      (fun index => .const (metadata.declarationName ruleIndex index)) term)

theorem RuleMetavariables.entry_empty_type
    (metadata : RuleMetavariables language rule spec) (index : Fin metadata.entries.length) :
    (metadata.entry [] index).type =
      ClosedOperators.bindingType carrierType (metadata.entries.get index).1 (metadata.entries.get index).2 := by
  let dependencies : List (Carrier language) := (metadata.entries.get index).1
  let result : Carrier language := (metadata.entries.get index).2
  have emptyAmbient : List.append dependencies [] = dependencies := List.append_nil dependencies
  have carrierEq := congrArg (fun sorts : List (Carrier language) =>
    carrierType (functionCarrier sorts result)) emptyAmbient
  exact carrierEq.trans (functionCarrier_type dependencies result)

/-- All function constants in the unreduced fixed template have types earned
from the actual finite declaration list and source dependency telescopes. -/
theorem RuleMetavariables.fixedTemplate_typing
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (unique : language.typeNames.Nodup)
    (ruleIndex : Nat) {input : Binding.Ctx (signature language)} {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) input sort) :
    FormationSensitive.Typing (metadata.templateRules source ruleIndex [])
      (ClosedOperators.typeContext carrierType input)
      (metadata.fixedTemplate source ruleIndex term) (liftClosed (carrierType sort)) := by
  apply ClosedOperators.Schema.fixedTemplate_typing
    (metadata.templateRealization source unique ruleIndex [])
    (expansion language) (virtualNames source) (operators_expand source)
  intro index
  have typed := metadata.function_typed source ruleIndex [] index
  have typeEq := metadata.entry_empty_type index
  have typedActual := (congrArg (fun type => FormationSensitive.Typing
    (metadata.templateRules source ruleIndex []) .nil
    (.const (metadata.declarationName ruleIndex index)) type) typeEq).mp typed
  simpa only [ConstantExpansion.expand, expansion,
    if_neg (metadata.declarationName_ne_identity ruleIndex index),
    TelescopeAbstraction.liftClosed_zero] using typedActual

/-- Original finite metadata now supplies both selector hypotheses of the
ambient-uniform specialization theorem. -/
theorem RuleMetavariables.fixedTemplate_specialize
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    {ambient input target : Binding.Ctx (signature language)}
    (bodies : Binding.ContextualAssignment (signature language) metadata.entries ambient)
    (environment : Binding.Sub (signature language) ambient target)
    (valuation : Binding.Sub (signature language) input target)
    {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) input sort) :
    ConstantExpansion.expand (expansion language)
      (ConstantSubstitution.interpret
        (ConstantSubstitution.specializedValues (metadata.sourcePositions ruleIndex)
          (BindingSignatureEmbedding.Schema.ambientFunctions (virtualNames source)
            (BindingSignatureEmbedding.Schema.bodyPrograms (virtualNames source) bodies) environment))
        (encodeSub (virtualNames source) valuation)
        (BindingSignatureEmbedding.Schema.fixedTemplate (virtualNames source)
          (fun index => .const (metadata.declarationName ruleIndex index)) term)) =
      schemaProgram source bodies environment valuation term :=
  ClosedOperators.Schema.fixedTemplate_specialize (expansion language) (virtualNames source)
    (metadata.declarationName ruleIndex) (metadata.sourcePositions ruleIndex)
    (metadata.sourcePositions_operator source ruleIndex)
    (metadata.sourcePositions_declared ruleIndex) bodies environment valuation term

/-- The original certificate replays the actual fixed-template specialization
all the way to the original contextual source instance. -/
theorem RuleMetavariables.fixedTemplate_evidence_checked
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    {ambient input target : Binding.Ctx (signature language)}
    (bodies : Binding.ContextualAssignment (signature language) metadata.entries ambient)
    (environment : Binding.Sub (signature language) ambient target)
    (valuation : Binding.Sub (signature language) input target)
    {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) input sort) :
    (schemaEvidence source bodies environment valuation term).check (fun _ _ => False)
      FormationCheckedTelescopePrograms.noRoot
      (ConstantExpansion.expand (expansion language)
        (ConstantSubstitution.interpret
          (ConstantSubstitution.specializedValues (metadata.sourcePositions ruleIndex)
            (BindingSignatureEmbedding.Schema.ambientFunctions (virtualNames source)
              (BindingSignatureEmbedding.Schema.bodyPrograms (virtualNames source) bodies) environment))
          (encodeSub (virtualNames source) valuation)
          (BindingSignatureEmbedding.Schema.fixedTemplate (virtualNames source)
            (fun index => .const (metadata.declarationName ruleIndex index)) term)))
      (ClosedOperators.compile (images source)
        (Binding.ContextualAssignment.instantiate bodies environment valuation term)) = true :=
  ClosedOperators.Schema.fixedTemplate_evidence_checked (expansion language) (virtualNames source)
    (images source) (operators_expand source) (metadata.declarationName ruleIndex)
    (metadata.sourcePositions ruleIndex) (metadata.sourcePositions_operator source ruleIndex)
    (metadata.sourcePositions_declared ruleIndex) bodies environment valuation term

/-- Real source bodies yield native function values only after applying the
actual caller's ambient environment, with source dependency positions retained. -/
def RuleMetavariables.bodyFunctionValues
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language)
    {ambient target : Binding.Ctx (signature language)}
    (bodies : Binding.ContextualAssignment (signature language) metadata.entries ambient)
    (environment : Binding.Sub (signature language) ambient target) :
    Sub Tower.Head (metadata.parameterSorts []).length target.length :=
  fun position => ConstantExpansion.expand (expansion language)
    (BindingSignatureEmbedding.Schema.ambientFunctions (virtualNames source)
      (BindingSignatureEmbedding.Schema.bodyPrograms (virtualNames source) bodies) environment
      (metadata.sourceIndex [] position))

/-- The native telescope arguments are typed from the original source body
at every finite meta row, not from an arbitrary target-function assumption. -/
theorem RuleMetavariables.bodyFunctionValues_typed
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (unique : language.typeNames.Nodup)
    (ruleIndex : Nat) {ambient target : Binding.Ctx (signature language)}
    (bodies : Binding.ContextualAssignment (signature language) metadata.entries ambient)
    (environment : Binding.Sub (signature language) ambient target) :
    FormationSensitive.CtxMor (Headers.rules source) (metadata.parameterContext [])
      (ClosedOperators.typeContext carrierType target) (metadata.bodyFunctionValues source bodies environment) := by
  intro position
  let sourcePosition := metadata.sourceIndex [] position
  have lookup := metadata.selected_lookup source ruleIndex []
    (metadata.function_lookup source ruleIndex [] sourcePosition)
    (metadata.positions_declared ruleIndex [] sourcePosition)
  rw [metadata.parameterIndex_sourceIndex] at lookup
  rw [metadata.entry_empty_type] at lookup
  change FormationSensitive.Typing _ _
    (metadata.bodyFunctionValues source bodies environment position)
    (subst (metadata.bodyFunctionValues source bodies environment)
      (Ctx.lookup (metadata.parameterContext []) position))
  rw [lookup, subst_liftClosed]
  exact ClosedOperators.Schema.ambientFunctions_typing (realization source unique)
    (expansion language) (virtualNames source) (operators_expand source) bodies environment sourcePosition

/-- Actual finite function parameters commute with the derived operator
interpretation. The sole derived identity image cannot capture a rule parameter. -/
theorem RuleMetavariables.expand_specialization
    (metadata : RuleMetavariables language rule spec) (ruleIndex : Nat)
    {input target : Nat} (arguments : Sub Tower.Head (metadata.parameterSorts []).length target)
    (assignment : Sub Tower.Head input target) (term : Tower.Tm input) :
    ConstantSubstitution.interpret
      (ConstantSubstitution.specializedValues (metadata.positions ruleIndex [])
        (fun position => ConstantExpansion.expand (expansion language) (arguments position)))
      (fun position => ConstantExpansion.expand (expansion language) (assignment position))
      (ConstantExpansion.expand (expansion language) term) =
    ConstantExpansion.expand (expansion language)
      (ConstantSubstitution.interpret
        (ConstantSubstitution.specializedValues (metadata.positions ruleIndex []) arguments)
        assignment term) := by
  rw [ConstantSubstitution.interpret_expand, ConstantSubstitution.expand_interpret]
  congr 1
  funext name
  by_cases derived : name = identityName language
  · subst name
    simp [expansion, ConstantSubstitution.specializedValues, metadata.positions_identity,
      ClosedOperators.Derived.identity, ConstantSubstitution.interpret,
      ConstantExpansion.expand, liftSub, liftClosed, rename, liftRen]
  · simp only [expansion, if_neg derived, ConstantSubstitution.interpret]
    cases selected : metadata.positions ruleIndex [] name with
    | none => simp [ConstantSubstitution.specializedValues, selected,
        ConstantExpansion.expand, expansion, derived, liftClosed, rename]
    | some position => simp only [ConstantSubstitution.specializedValues, selected]

/-- The stored, already expanded native template specializes to the
original source-body compiler using its actual finite parameter table. -/
theorem RuleMetavariables.fixedTemplate_body_specialize
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    {ambient input target : Binding.Ctx (signature language)}
    (bodies : Binding.ContextualAssignment (signature language) metadata.entries ambient)
    (environment : Binding.Sub (signature language) ambient target)
    (valuation : Binding.Sub (signature language) input target)
    {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) input sort) :
    ConstantSubstitution.interpret
      (ConstantSubstitution.specializedValues (metadata.positions ruleIndex [])
        (metadata.bodyFunctionValues source bodies environment))
      (ClosedOperators.compileSub (images source) valuation)
      (metadata.fixedTemplate source ruleIndex term) =
    schemaProgram source bodies environment valuation term := by
  let functions : Fin metadata.entries.length → Tower.Tm target.length :=
    BindingSignatureEmbedding.Schema.ambientFunctions (virtualNames source)
    (BindingSignatureEmbedding.Schema.bodyPrograms (virtualNames source) bodies) environment
  let arguments : Sub Tower.Head (metadata.parameterSorts []).length target.length :=
    fun position => functions (metadata.sourceIndex [] position)
  have rows : ConstantSubstitution.specializedValues (metadata.positions ruleIndex []) arguments =
      ConstantSubstitution.specializedValues (metadata.sourcePositions ruleIndex) functions := by
    funext name
    cases selected : metadata.positions ruleIndex [] name <;>
      simp only [ConstantSubstitution.specializedValues, RuleMetavariables.sourcePositions,
        selected, Option.map_none, Option.map_some, arguments]
  have commute := metadata.expand_specialization ruleIndex arguments
    (encodeSub (virtualNames source) valuation)
    (BindingSignatureEmbedding.Schema.fixedTemplate (virtualNames source)
      (fun index => .const (metadata.declarationName ruleIndex index)) term)
  rw [rows, ClosedOperators.expand_encodeSub (expansion language) (virtualNames source)
    (images source) (operators_expand source) valuation] at commute
  exact commute.trans (metadata.fixedTemplate_specialize source ruleIndex bodies environment valuation term)

/-- Close only the original schema's bound inputs; the function constants
still refer to the one actual finite rule declaration block. -/
def RuleMetavariables.closedTemplate (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    {input : Binding.Ctx (signature language)} {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) input sort) : Tower.Tm 0 :=
  TelescopeAbstraction.closeTerm (ClosedOperators.typeContext carrierType input)
    (metadata.fixedTemplate source ruleIndex term)

theorem RuleMetavariables.closedTemplate_typing
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (unique : language.typeNames.Nodup)
    (ruleIndex : Nat) {input : Binding.Ctx (signature language)} {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) input sort) :
    FormationSensitive.Typing (metadata.templateRules source ruleIndex []) .nil
      (metadata.closedTemplate source ruleIndex term)
      (TelescopeAbstraction.closeType (ClosedOperators.typeContext carrierType input)
        (liftClosed (carrierType sort))) :=
  (metadata.templateFormation source ruleIndex []).closeTerm_typing
    ((metadata.templateFormation source ruleIndex []).typeFormed sort)
    _ (metadata.fixedTemplate_typing source unique ruleIndex term)

/-- Abstract the actual finite metavariable constants into native function
parameters. The result is one closed program, independent of every caller. -/
def RuleMetavariables.parameterProgram (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    {input : Binding.Ctx (signature language)} {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) input sort) : Tower.Tm 0 :=
  ConstantSubstitution.parameterProgram (metadata.parameterContext []) (metadata.positions ruleIndex [])
    (metadata.closedTemplate source ruleIndex term)

/-- Primitive source declaration lookup earns formation for the entire
closed rule program, before any function value or caller is supplied. -/
theorem RuleMetavariables.parameterProgram_typing
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (unique : language.typeNames.Nodup)
    (ruleIndex : Nat) {input : Binding.Ctx (signature language)} {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) input sort) :
    FormationSensitive.Typing (Headers.rules source) .nil
      (metadata.parameterProgram source ruleIndex term)
      (TelescopeAbstraction.closeType (metadata.parameterContext [])
        (ConstantSubstitution.parameterTerm (metadata.positions ruleIndex [])
          (TelescopeAbstraction.closeType (ClosedOperators.typeContext carrierType input)
            (liftClosed (carrierType sort))))) :=
  ConstantSubstitution.parameterProgram_typing (metadata.rulesMap source ruleIndex [])
    (FormationSensitive.towerUniverseRegularity.includeSignature (Headers.signature source))
    (fun first second => FormationCheckedTelescopePrograms.tower_joins first second)
    (metadata.parameterContext_formed source [])
    (metadata.closedTemplate_typing source unique ruleIndex term)
    (metadata.parameter_values_typed source ruleIndex [])

/-- Apply the one closed program to the actual body-derived native
functions. Formation includes the unreduced call and its destination context. -/
theorem RuleMetavariables.parameterApplication_judgment
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (unique : language.typeNames.Nodup)
    (ruleIndex : Nat) {input ambient target : Binding.Ctx (signature language)}
    (bodies : Binding.ContextualAssignment (signature language) metadata.entries ambient)
    (environment : Binding.Sub (signature language) ambient target)
    {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) input sort) :
    FormationSensitive.Judgment (Headers.rules source) (ClosedOperators.typeContext carrierType target)
      (TelescopeAbstraction.applyClosed (metadata.parameterContext [])
        (metadata.bodyFunctionValues source bodies environment)
        (liftClosed (metadata.parameterProgram source ruleIndex term)))
      (ConstantSubstitution.interpret
        (ConstantSubstitution.specializedValues (metadata.positions ruleIndex [])
          (metadata.bodyFunctionValues source bodies environment)) Fin.elim0
        (TelescopeAbstraction.closeType (ClosedOperators.typeContext carrierType input)
          (liftClosed (carrierType sort)))) :=
  ConstantSubstitution.parameterApplication_judgment (metadata.rulesMap source ruleIndex [])
    (FormationSensitive.towerUniverseRegularity.includeSignature (Headers.signature source))
    (fun first second => FormationCheckedTelescopePrograms.tower_joins first second)
    (metadata.parameterContext_formed source [])
    (metadata.closedTemplate_typing source unique ruleIndex term)
    (metadata.parameter_values_typed source ruleIndex [])
    ((formation source).typeContext_formed target) _
    (metadata.bodyFunctionValues_typed source unique ruleIndex bodies environment)

/-- Parameter application executes the existing finite telescope certificate,
with the actual body functions and retained source declaration selector. -/
theorem RuleMetavariables.parameterApplication_checked
    (metadata : RuleMetavariables language rule spec)
    (source : NativeSignature.Installation language) (ruleIndex : Nat)
    {input ambient target : Binding.Ctx (signature language)}
    (bodies : Binding.ContextualAssignment (signature language) metadata.entries ambient)
    (environment : Binding.Sub (signature language) ambient target)
    {sort : Carrier language}
    (term : Binding.Term (Binding.withMetas (signature language) metadata.entries) input sort) :
    (FormationCheckedTelescopePrograms.applicationCode (metadata.parameterContext [])
      (metadata.bodyFunctionValues source bodies environment)
      (ConstantSubstitution.parameterTerm (metadata.positions ruleIndex [])
        (metadata.closedTemplate source ruleIndex term))).check (fun _ _ => False)
      FormationCheckedTelescopePrograms.noRoot
      (TelescopeAbstraction.applyClosed (metadata.parameterContext [])
        (metadata.bodyFunctionValues source bodies environment)
        (liftClosed (metadata.parameterProgram source ruleIndex term)))
      (ConstantSubstitution.interpret
        (ConstantSubstitution.specializedValues (metadata.positions ruleIndex [])
          (metadata.bodyFunctionValues source bodies environment)) Fin.elim0
        (metadata.closedTemplate source ruleIndex term)) = true :=
  ConstantSubstitution.parameterProgram_checked (metadata.parameterContext [])
    (metadata.positions ruleIndex []) (metadata.bodyFunctionValues source bodies environment)
    (metadata.closedTemplate source ruleIndex term)



end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Controls.FixedTemplates

open Mettapedia.OSLF Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation BindingSignatureEmbedding
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Functional

private abbrev language := Mettapedia.OSLF.NativeTypes.Instances.LetCase.language
private abbrev rule := Mettapedia.OSLF.NativeTypes.Instances.LetCase.caseRule
private def spec : RuleBindingSpec := rule.bindings.getD { dependencies := [] }
private abbrev V : Carrier language := .sort ⟨0, by decide⟩
private abbrev C : Carrier language := .sort ⟨1, by decide⟩
private abbrev Sig := signature language
private def source : NativeSignature.Installation language :=
  (NativeSignature.install? language).get (by decide)
private theorem unique : language.typeNames.Nodup := by decide
private def metadata : RuleMetavariables language rule spec :=
  (ruleMetavariables? language rule spec).get (by decide +kernel)
private def returnOp : Sig.Op C :=
  ⟨.constructor language.terms[2] (by decide)
    (by simp [Mettapedia.GSLT.LanguageDef.WellSorted.UsesBareCollection, language,
      Mettapedia.OSLF.NativeTypes.Instances.LetCase.language,
      Mettapedia.OSLF.NativeTypes.Instances.LetCase.value])
    (.cons (.simple "value" V.source) .nil), [([], V)], rfl⟩
private def first : Fin metadata.entries.length := ⟨0, by decide⟩
private def last : Fin metadata.entries.length := ⟨2, by decide⟩
private def call : Binding.Term (Binding.withMetas Sig metadata.entries) [] V := .op (.inr (.mk first)) .nil
private def dependencyCall : Binding.Term (Binding.withMetas Sig metadata.entries) [V, V] C :=
  .op (.inr (.mk last)) (.cons (.var (.succ .zero)) (.cons (.var .zero) .nil))
private def reversedCall : Binding.Term (Binding.withMetas Sig metadata.entries) [V, V] C :=
  .op (.inr (.mk last)) (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))
private def bodies : Binding.ContextualAssignment Sig metadata.entries [V, V] :=
  Fin.cases (.var .zero) (Fin.cases (.var (.succ .zero))
    (Fin.cases (.op returnOp (.cons (.var .zero) .nil)) (fun position => Fin.elim0 position)))
private def ambientBodies : Binding.ContextualAssignment Sig metadata.entries [V, V] :=
  Fin.cases (.var .zero) (Fin.cases (.var (.succ .zero))
    (Fin.cases (.op returnOp (.cons (.var (.succ (.succ .zero))) .nil))
      (fun position => Fin.elim0 position)))
private def environment : Binding.Sub Sig [V, V] [V, V] := fun _ position => .var position
private def swapped : Binding.Sub Sig [V, V] [V, V] := fun _ position =>
  match position with
  | .zero => .var (.succ .zero)
  | .succ .zero => .var .zero
private def empty : Binding.Sub Sig [] [V, V] := fun _ position => nomatch position

example : FormationSensitive.Typing (Headers.rules source) .nil
    (metadata.parameterProgram source 1 call)
    (TelescopeAbstraction.closeType (metadata.parameterContext [])
      (ConstantSubstitution.parameterTerm (metadata.positions 1 [])
        (TelescopeAbstraction.closeType (ClosedOperators.typeContext (S := Sig) carrierType [])
          (liftClosed (carrierType V))))) :=
  metadata.parameterProgram_typing source unique 1 call

example : FormationSensitive.CtxMor (Headers.rules source) (metadata.parameterContext [])
    (ClosedOperators.typeContext carrierType [V, V]) (metadata.bodyFunctionValues source bodies swapped) :=
  metadata.bodyFunctionValues_typed source unique 1 bodies swapped

private def application (env : Binding.Sub Sig [V, V] [V, V]) : Tower.Tm 2 :=
  TelescopeAbstraction.applyClosed (metadata.parameterContext [])
    (metadata.bodyFunctionValues source bodies env) (liftClosed (metadata.parameterProgram source 1 call))
private def parameterCode (env : Binding.Sub Sig [V, V] [V, V]) :
    StructuralConversionCode.Code Tower.Head (fun _ => Empty) 2 :=
  FormationCheckedTelescopePrograms.applicationCode (metadata.parameterContext [])
    (metadata.bodyFunctionValues source bodies env)
    (ConstantSubstitution.parameterTerm (metadata.positions 1 []) (metadata.closedTemplate source 1 call))
private def specialized (env : Binding.Sub Sig [V, V] [V, V]) : Tower.Tm 2 :=
  ConstantSubstitution.interpret
    (ConstantSubstitution.specializedValues (metadata.positions 1 [])
      (metadata.bodyFunctionValues source bodies env)) Fin.elim0 (metadata.closedTemplate source 1 call)
private def wrongProgram : Tower.Tm 2 :=
  TelescopeAbstraction.applyClosed (metadata.parameterContext [])
    (metadata.bodyFunctionValues source bodies environment)
    (liftClosed (ConstantSubstitution.parameterProgram (metadata.parameterContext [])
      (metadata.positions 2 []) (metadata.closedTemplate source 1 call)))

private def replay (term : Binding.Term (Binding.withMetas Sig metadata.entries) [V, V] C)
    (given : Binding.ContextualAssignment Sig metadata.entries [V, V])
    (expected : Tower.Tm 2) : Bool :=
  (schemaEvidence source given environment environment term).check (fun _ _ => False)
    FormationCheckedTelescopePrograms.noRoot
    (schemaProgram source given environment environment term) expected

def checks : List (String × Bool) := [
  ("actual-fixed-template-retains-original-rule-name",
    metadata.fixedTemplate source 1 call == .const (metadata.declarationName 1 first)),
  ("actual-rule-index-distinguishes-fixed-template",
    !(metadata.fixedTemplate source 1 call == metadata.fixedTemplate source 2 call)),
  ("actual-finite-source-position",
    metadata.sourcePositions 1 (metadata.declarationName 1 last) == some last),
  ("unknown-rule-source-position-refuses",
    (metadata.sourcePositions 2 (metadata.declarationName 1 last)).isNone),
  ("constructor-source-position-refuses",
    (metadata.sourcePositions 1 (constructorDeclName language ⟨2, by decide⟩)).isNone),
  ("derived-program-source-position-refuses",
    (metadata.sourcePositions 1 (identityName language)).isNone),
  ("actual-function-arguments-use-caller-environment",
    !(metadata.bodyFunctionValues source bodies environment (metadata.parameterIndex [] first) ==
      metadata.bodyFunctionValues source bodies swapped (metadata.parameterIndex [] first))),
  ("one-closed-program-original-caller",
    (parameterCode environment).check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      (application environment) (specialized environment)),
  ("one-closed-program-changed-caller",
    (parameterCode swapped).check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      (application swapped) (specialized swapped)),
  ("changed-caller-endpoint-refuses",
    !((parameterCode environment).check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      (application environment) (specialized swapped))),
  ("wrong-rule-selector-refuses",
    !((parameterCode environment).check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      wrongProgram (specialized environment))),
  ("parameter-application-count-is-actual-finite-row-count", (parameterCode environment).stepCount == 3),
  ("parameter-specialization-retains-source-program",
    specialized environment == schemaProgram source bodies environment empty call),
  ("parameter-specialization-retains-changed-source-program",
    specialized swapped == schemaProgram source bodies swapped empty call),
  ("actual-body-dependency-source-replay", replay dependencyCall bodies
    (ClosedOperators.compile (images source)
      (Binding.ContextualAssignment.instantiate bodies environment environment dependencyCall))),
  ("dependency-order-refuses", !(replay dependencyCall bodies
    (ClosedOperators.compile (images source)
      (Binding.ContextualAssignment.instantiate bodies environment environment reversedCall)))),
  ("ambient-body-source-replay", replay dependencyCall ambientBodies
    (ClosedOperators.compile (images source)
      (Binding.ContextualAssignment.instantiate ambientBodies environment environment dependencyCall))),
  ("ambient-body-capture-refuses", !(replay dependencyCall ambientBodies
    (ClosedOperators.compile (images source)
      (Binding.ContextualAssignment.instantiate bodies environment environment dependencyCall))))
]

#guard checks.all Prod.snd

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations.Controls.FixedTemplates
