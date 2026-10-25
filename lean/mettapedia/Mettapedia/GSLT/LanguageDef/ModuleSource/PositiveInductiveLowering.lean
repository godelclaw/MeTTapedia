import Mettapedia.GSLT.LanguageDef.ModuleSource.Syntax
import Mettapedia.TypeTheory.PositiveInductiveBlock
import Mettapedia.TypeTheory.IndexedPositiveContainer

/-!
# Textual registered-container declarations into positive blocks

The common `.module` reader already represents applications such as
`List (Tree A)` in `InductiveSyntax.Term`.  This module supplies the checked
lowering boundary from that syntax to the staged positive-inductive grammar.

A codec owns name resolution for one selected family profile.  Its two-sided
laws make accepted field and result spellings canonical.  The generic
lowerer retains field and constructor names, rejects function fields, and
keeps the registry witness for every nested container.  Quoting and lowering
are inverse both for individual constructor telescopes and for a complete
single-family `.module` block.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLowering

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.PositiveInductiveBlock
open InductiveSyntax

universe u

/-- Meaning assigned to one textual constructor field.  A nested meaning
retains the registry equality that licenses its positive container. -/
inductive FieldMeaning (registry : Registry) (I : Interface.{u})
    (context : List I.SortCode) where
  | data (sort : I.SortCode)
  | recursive (index : I.IndexExpr context)
  | nested (containerName : String) (container : Container)
      (registered : registry.lookup containerName = some container)
      (index : I.IndexExpr context)

/-- Profile-specific resolution for one textual family.  Scope handling is
explicit so named indices can use nearest-binder resolution. -/
structure Codec (registry : Registry) (I : Interface.{u})
    (parameterCount : Nat) (context : List I.SortCode) where
  Scope : List I.SortCode → Type u
  initialScope : Scope context
  bindData : ∀ {current}, String → (sort : I.SortCode) →
    Scope current → Scope (sort :: current)
  block : ∀ {current}, String → Scope current → Scope current
  classify : ∀ {current}, Scope current → Term →
    Option (FieldMeaning registry I current)
  classify_arrow : ∀ {current} (scope : Scope current) (domain codomain : Term),
    classify scope (.arrow domain codomain) = none
  quoteField : ∀ {current}, Scope current →
    FieldMeaning registry I current → Term
  classify_quote : ∀ {current} (scope : Scope current)
    (meaning : FieldMeaning registry I current),
    classify scope (quoteField scope meaning) = some meaning
  quote_classify : ∀ {current} (scope : Scope current) (source : Term)
    (meaning : FieldMeaning registry I current),
    classify scope source = some meaning → quoteField scope meaning = source
  result? : ∀ {current}, Scope current → Term → Option (I.IndexExpr current)
  quoteResult : ∀ {current}, Scope current → I.IndexExpr current → Term
  result_quote : ∀ {current} (scope : Scope current) (index : I.IndexExpr current),
    result? scope (quoteResult scope index) = some index
  quote_result : ∀ {current} (scope : Scope current) (source : Term)
    (index : I.IndexExpr current),
    result? scope source = some index → quoteResult scope index = source
  familyName : String
  parameters : List Binder
  indices : List Binder
  sort : Term

/-- Resolved positive telescope retaining authored field names. -/
inductive Code {registry : Registry} {I : Interface.{u}} {parameterCount : Nat} :
    List I.SortCode → Type (u + 1) where
  | result {context} (index : I.IndexExpr context) :
      Code (registry := registry) (parameterCount := parameterCount) context
  | data {context} (fieldName : String) (sort : I.SortCode)
      (rest : Code (registry := registry) (parameterCount := parameterCount)
        (sort :: context)) :
      Code (registry := registry) (parameterCount := parameterCount) context
  | recursive {context} (fieldName : String) (index : I.IndexExpr context)
      (rest : Code (registry := registry) (parameterCount := parameterCount) context) :
      Code (registry := registry) (parameterCount := parameterCount) context
  | nested {context} (fieldName containerName : String) (container : Container)
      (registered : registry.lookup containerName = some container)
      (index : I.IndexExpr context)
      (rest : Code (registry := registry) (parameterCount := parameterCount) context) :
      Code (registry := registry) (parameterCount := parameterCount) context

namespace Code

variable {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
  {context : List I.SortCode}

/-- Forget textual field names after they have served scope resolution. -/
def erase : {current : List I.SortCode} →
    Code (registry := registry) (I := I) (parameterCount := parameterCount) current →
      PositiveInductiveBlock.Code registry I parameterCount current
  | _, .result index => .result index
  | _, .data _ sort rest => .data sort (erase rest)
  | _, .recursive _ index rest => .recursive index (erase rest)
  | _, .nested _ name container _ index rest =>
      .nested name container index (erase rest)

theorem erase_registered : {current : List I.SortCode} →
    (code : Code (registry := registry) (I := I)
      (parameterCount := parameterCount) current) →
      RawCode.WellRegistered code.erase
  | _, .result _ => trivial
  | _, .data _ _ rest => erase_registered rest
  | _, .recursive _ _ rest => erase_registered rest
  | _, .nested _ _ _ registered _ rest =>
      ⟨registered, erase_registered rest⟩

/-- The same resolved constructor can use the richer indexed-container
grammar without weakening its source registry or its family indices. -/
def eraseIndexed {current : List I.SortCode}
    (code : Code (registry := registry) (I := I)
      (parameterCount := parameterCount) current) :
    IndexedPositiveContainer.Code I (IndexedPositiveContainer.Unindexed.liftRegistry registry I)
      parameterCount current :=
  IndexedPositiveContainer.Unindexed.liftCode code.erase code.erase_registered

/-- The two erasures retain equivalent shapes and recursive occurrences,
with the same required child index at each occurrence. -/
def erasureSignatureEquiv {current : List I.SortCode}
    (code : Code (registry := registry) (I := I)
      (parameterCount := parameterCount) current) :
    IndexedPolynomial.SignatureEquiv
      (PositiveInductiveBlock.Code.polynomial code.erase)
      (IndexedPositiveContainer.Code.polynomial code.eraseIndexed) :=
  IndexedPositiveContainer.Unindexed.signatureEquiv code.erase code.erase_registered

/-- Recover the canonical textual telescope and result. -/
def quote (codec : Codec registry I parameterCount context) :
    {current : List I.SortCode} → codec.Scope current →
      Code (registry := registry) (I := I) (parameterCount := parameterCount) current →
        List Binder × Term
  | _, scope, .result index => ([], codec.quoteResult scope index)
  | _, scope, .data name sort rest =>
      let quoted := quote codec (codec.bindData name sort scope) rest
      (⟨name, codec.quoteField scope (.data sort)⟩ :: quoted.1, quoted.2)
  | _, scope, .recursive name index rest =>
      let quoted := quote codec (codec.block name scope) rest
      (⟨name, codec.quoteField scope (.recursive index)⟩ :: quoted.1, quoted.2)
  | _, scope, .nested fieldName containerName container registered index rest =>
      let quoted := quote codec (codec.block fieldName scope) rest
      (⟨fieldName, codec.quoteField scope
        (.nested containerName container registered index)⟩ :: quoted.1, quoted.2)

end Code

/-- Lower one canonical textual telescope. Function fields are refused by
the codec law rather than erased. -/
def lowerCode {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} (codec : Codec registry I parameterCount context) :
    {current : List I.SortCode} → codec.Scope current → Term → List Binder →
      Option (Code (registry := registry) (I := I) (parameterCount := parameterCount) current)
  | _, scope, result, [] => (codec.result? scope result).map .result
  | _, scope, result, field :: rest =>
      match codec.classify scope field.type with
      | none => none
      | some meaning =>
          match meaning with
          | .data sort =>
              (lowerCode codec (codec.bindData field.name sort scope) result rest).map
                (Code.data field.name sort)
          | .recursive index =>
              (lowerCode codec (codec.block field.name scope) result rest).map
                (Code.recursive field.name index)
          | .nested containerName container registered index =>
              (lowerCode codec (codec.block field.name scope) result rest).map
                (Code.nested field.name containerName container registered index)

@[simp] theorem lowerCode_quote
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} (codec : Codec registry I parameterCount context) :
    ∀ {current : List I.SortCode} (scope : codec.Scope current)
      (code : Code (registry := registry) (I := I)
        (parameterCount := parameterCount) current),
      lowerCode codec scope (code.quote codec scope).2 (code.quote codec scope).1 =
        some code := by
  intro current scope code
  induction code with
  | result index => simp [Code.quote, lowerCode, codec.result_quote]
  | data name sort rest ih =>
      simp [Code.quote, lowerCode, codec.classify_quote, ih]
  | recursive name index rest ih =>
      simp [Code.quote, lowerCode, codec.classify_quote, ih]
  | nested fieldName containerName container registered index rest ih =>
      simp [Code.quote, lowerCode, codec.classify_quote, ih]

theorem quote_lowerCode
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} (codec : Codec registry I parameterCount context)
    {current : List I.SortCode} (scope : codec.Scope current) :
    ∀ (fields : List Binder) (result : Term)
      (code : Code (registry := registry) (I := I)
        (parameterCount := parameterCount) current),
      lowerCode codec scope result fields = some code →
        code.quote codec scope = (fields, result) := by
  intro fields
  induction fields generalizing current with
  | nil =>
      intro result code accepted
      cases found : codec.result? scope result with
      | none => simp [lowerCode, found] at accepted
      | some index =>
          have same : Code.result index = code := by
            simpa [lowerCode, found] using accepted
          subst code
          simp [Code.quote, codec.quote_result scope result index found]
  | cons field rest ih =>
      intro result code accepted
      cases classified : codec.classify scope field.type with
      | none => simp [lowerCode, classified] at accepted
      | some meaning =>
          cases meaning with
          | data sort =>
              cases lowered : lowerCode codec
                  (codec.bindData field.name sort scope) result rest with
              | none => simp [lowerCode, classified, lowered] at accepted
              | some tail =>
                  have same : Code.data field.name sort tail = code := by
                    simpa [lowerCode, classified, lowered] using accepted
                  subst code
                  have tailQuote := ih (codec.bindData field.name sort scope)
                    result tail lowered
                  simp [Code.quote, codec.quote_classify scope field.type (.data sort)
                    classified, tailQuote]
          | recursive index =>
              cases lowered : lowerCode codec (codec.block field.name scope)
                  result rest with
              | none => simp [lowerCode, classified, lowered] at accepted
              | some tail =>
                  have same : Code.recursive field.name index tail = code := by
                    simpa [lowerCode, classified, lowered] using accepted
                  subst code
                  have tailQuote := ih (codec.block field.name scope) result tail lowered
                  simp [Code.quote, codec.quote_classify scope field.type (.recursive index)
                    classified, tailQuote]
          | nested containerName container registered index =>
              cases lowered : lowerCode codec (codec.block field.name scope)
                  result rest with
              | none => simp [lowerCode, classified, lowered] at accepted
              | some tail =>
                  have same : Code.nested field.name containerName container
                      registered index tail = code := by
                    simpa [lowerCode, classified, lowered] using accepted
                  subst code
                  have tailQuote := ih (codec.block field.name scope) result tail lowered
                  simp [Code.quote, codec.quote_classify scope field.type
                    (.nested containerName container registered index) classified,
                    tailQuote]


structure ResolvedConstructor {registry : Registry} {I : Interface.{u}}
    {parameterCount : Nat} (context : List I.SortCode) where
  name : String
  body : Code (registry := registry) (I := I) (parameterCount := parameterCount) context

def lowerConstructor {registry : Registry} {I : Interface.{u}}
    {parameterCount : Nat} {context : List I.SortCode}
    (codec : Codec registry I parameterCount context)
    (source : InductiveSyntax.Constructor) :
    Option (ResolvedConstructor (registry := registry) (I := I)
      (parameterCount := parameterCount) context) :=
  (lowerCode codec codec.initialScope source.result source.fields).map
    fun body => ⟨source.name, body⟩

def ResolvedConstructor.quote {registry : Registry} {I : Interface.{u}}
    {parameterCount : Nat} {context : List I.SortCode}
    (codec : Codec registry I parameterCount context)
    (constructor : ResolvedConstructor (registry := registry) (I := I)
      (parameterCount := parameterCount) context) : InductiveSyntax.Constructor :=
  let quoted := constructor.body.quote codec codec.initialScope
  ⟨constructor.name, quoted.1, quoted.2⟩

@[simp] theorem lowerConstructor_quote
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} (codec : Codec registry I parameterCount context)
    (constructor : ResolvedConstructor (registry := registry) (I := I)
      (parameterCount := parameterCount) context) :
    lowerConstructor codec (constructor.quote codec) = some constructor := by
  cases constructor with
  | mk name body => simp [ResolvedConstructor.quote, lowerConstructor]

theorem quote_lowerConstructor
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} (codec : Codec registry I parameterCount context)
    (source : InductiveSyntax.Constructor)
    (constructor : ResolvedConstructor (registry := registry) (I := I)
      (parameterCount := parameterCount) context)
    (accepted : lowerConstructor codec source = some constructor) :
    constructor.quote codec = source := by
  unfold lowerConstructor at accepted
  cases lowered : lowerCode codec codec.initialScope source.result source.fields with
  | none => simp [lowered] at accepted
  | some body =>
      have same : (⟨source.name, body⟩ : ResolvedConstructor context) = constructor := by
        simpa [lowered] using accepted
      subst constructor
      simp [ResolvedConstructor.quote,
        quote_lowerCode codec codec.initialScope source.fields source.result body lowered]

structure ResolvedFamily {registry : Registry} {I : Interface.{u}}
    {parameterCount : Nat} (context : List I.SortCode) where
  constructors : List (ResolvedConstructor (registry := registry) (I := I)
    (parameterCount := parameterCount) context)
  uniqueNames : (constructors.map (fun constructor => constructor.name)).Nodup

def ResolvedFamily.erase {registry : Registry} {I : Interface.{u}}
    {parameterCount : Nat} {context : List I.SortCode}
    (family : ResolvedFamily (registry := registry) (I := I)
      (parameterCount := parameterCount) context) :
    PositiveInductiveBlock.Admitted registry I parameterCount context where
  constructors := family.constructors.map fun constructor =>
    ⟨constructor.name, constructor.body.erase⟩
  uniqueNames := by
    simpa [Function.comp_def] using family.uniqueNames

theorem ResolvedFamily.erase_registered {registry : Registry} {I : Interface.{u}}
    {parameterCount : Nat} {context : List I.SortCode}
    (family : ResolvedFamily (registry := registry) (I := I)
      (parameterCount := parameterCount) context) : family.erase.WellRegistered := by
  intro constructor member
  dsimp only [ResolvedFamily.erase] at member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  exact original.body.erase_registered

def ResolvedFamily.quote {registry : Registry} {I : Interface.{u}}
    {parameterCount : Nat} {context : List I.SortCode}
    (codec : Codec registry I parameterCount context)
    (family : ResolvedFamily (registry := registry) (I := I)
      (parameterCount := parameterCount) context) : InductiveSyntax.Family :=
  ⟨codec.familyName, codec.parameters, codec.indices, codec.sort,
    family.constructors.map (ResolvedConstructor.quote codec)⟩

def lowerFamily {registry : Registry} {I : Interface.{u}}
    {parameterCount : Nat} {context : List I.SortCode}
    (codec : Codec registry I parameterCount context)
    (source : InductiveSyntax.Family) :
    Option (ResolvedFamily (registry := registry) (I := I)
      (parameterCount := parameterCount) context) := do
  if source.name ≠ codec.familyName ∨ source.parameters ≠ codec.parameters ∨
      source.indices ≠ codec.indices ∨ source.sort ≠ codec.sort then none
  else
    let constructors ← source.constructors.mapM (lowerConstructor codec)
    if unique : (constructors.map fun constructor => constructor.name).Nodup then
      some ⟨constructors, unique⟩
    else none

private theorem lowerConstructors_quote
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} (codec : Codec registry I parameterCount context)
    (constructors : List (ResolvedConstructor (registry := registry) (I := I)
      (parameterCount := parameterCount) context)) :
    constructors.mapM
      (lowerConstructor codec ∘ ResolvedConstructor.quote codec) = some constructors := by
  induction constructors with
  | nil => rfl
  | cons head tail ih => simp [ih]

@[simp] theorem lowerFamily_quote
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} (codec : Codec registry I parameterCount context)
    (family : ResolvedFamily (registry := registry) (I := I)
      (parameterCount := parameterCount) context) :
    lowerFamily codec (family.quote codec) = some family := by
  cases family with
  | mk constructors uniqueNames =>
      unfold ResolvedFamily.quote lowerFamily
      simp only [ne_eq, not_true_eq_false, false_or, ↓reduceIte]
      have mapMEqual :
          (constructors.map (ResolvedConstructor.quote codec)).mapM
              (lowerConstructor codec) =
            constructors.mapM
              (lowerConstructor codec ∘ ResolvedConstructor.quote codec) := by
        induction constructors with
        | nil => rfl
        | cons head tail ih => simp [List.mapM_cons, Function.comp_def]
      rw [mapMEqual, lowerConstructors_quote]
      simp [uniqueNames]

private theorem quoteConstructors_of_lower
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} (codec : Codec registry I parameterCount context) :
    ∀ (source : List InductiveSyntax.Constructor)
      (target : List (ResolvedConstructor (registry := registry) (I := I)
        (parameterCount := parameterCount) context)),
      source.mapM (lowerConstructor codec) = some target →
        target.map (ResolvedConstructor.quote codec) = source := by
  intro source
  induction source with
  | nil =>
      intro target accepted
      simp at accepted
      subst target
      rfl
  | cons head tail ih =>
      intro target accepted
      cases headResult : lowerConstructor codec head with
      | none => simp [List.mapM_cons, headResult] at accepted
      | some loweredHead =>
          cases tailResult : tail.mapM (lowerConstructor codec) with
          | none => simp [List.mapM_cons, headResult, tailResult] at accepted
          | some loweredTail =>
              have same : loweredHead :: loweredTail = target := by
                simpa [List.mapM_cons, headResult, tailResult] using accepted
              subst target
              simp [quote_lowerConstructor codec head loweredHead headResult,
                ih loweredTail tailResult]

theorem quote_lowerFamily
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} (codec : Codec registry I parameterCount context)
    (source : InductiveSyntax.Family)
    (family : ResolvedFamily (registry := registry) (I := I)
      (parameterCount := parameterCount) context)
    (accepted : lowerFamily codec source = some family) :
    family.quote codec = source := by
  unfold lowerFamily at accepted
  split at accepted
  · contradiction
  · rename_i header
    push Not at header
    obtain ⟨name, parameters, indices, sort⟩ := header
    cases lowered : source.constructors.mapM (lowerConstructor codec) with
    | none => simp [lowered] at accepted
    | some constructors =>
        by_cases unique : (constructors.map fun constructor => constructor.name).Nodup
        · have same : (⟨constructors, unique⟩ : ResolvedFamily context) = family := by
            simpa [lowered, unique] using accepted
          subst family
          cases source with
          | mk sourceName sourceParameters sourceIndices sourceSort sourceConstructors =>
              simp only at name parameters indices sort
              subst sourceName sourceParameters sourceIndices sourceSort
              simp [ResolvedFamily.quote,
                quoteConstructors_of_lower codec sourceConstructors constructors lowered]
        · simp [lowered, unique] at accepted

/-- Exact unlowered shell of a direct `.module` fragment with one family. -/
structure SingleFamilySource where
  moduleName : String
  theoryName : String
  family : InductiveSyntax.Family

def SingleFamilySource.quote (source : SingleFamilySource) : Module :=
  ⟨[], source.moduleName,
    [⟨source.theoryName, [], .extend none [.inductives [source.family]]⟩],
    some ([source.theoryName], [])⟩

/-- Imports, joins, theory parameters and extra blocks are refused rather than
dropped. -/
def selectSingleFamily : Module → Option SingleFamilySource
  | ⟨[], moduleName,
      [⟨theoryName, [], .extend none [.inductives [family]]⟩],
      some ([entry], [])⟩ =>
        if entry = theoryName then some ⟨moduleName, theoryName, family⟩ else none
  | _ => none

theorem selectSingleFamily_exact (source : Module) (selected : SingleFamilySource)
    (accepted : selectSingleFamily source = some selected) :
    selected.quote = source := by
  unfold selectSingleFamily at accepted
  split at accepted
  · split at accepted
    · rename_i same
      cases Option.some.inj accepted
      simp only [SingleFamilySource.quote, same]
    · cases accepted
  · cases accepted

structure ResolvedModule {registry : Registry} {I : Interface.{u}}
    {parameterCount : Nat} (context : List I.SortCode) where
  moduleName : String
  theoryName : String
  family : ResolvedFamily (registry := registry) (I := I)
    (parameterCount := parameterCount) context

def ResolvedModule.quote {registry : Registry} {I : Interface.{u}}
    {parameterCount : Nat} {context : List I.SortCode}
    (codec : Codec registry I parameterCount context)
    (resolved : ResolvedModule (registry := registry) (I := I)
      (parameterCount := parameterCount) context) : Module :=
  (SingleFamilySource.mk resolved.moduleName resolved.theoryName
    (resolved.family.quote codec)).quote

def lowerModule {registry : Registry} {I : Interface.{u}}
    {parameterCount : Nat} {context : List I.SortCode}
    (codec : Codec registry I parameterCount context) (source : Module) :
      Option (ResolvedModule (registry := registry) (I := I)
        (parameterCount := parameterCount) context) :=
  match selectSingleFamily source with
  | none => none
  | some selected =>
      match lowerFamily codec selected.family with
      | none => none
      | some family => some ⟨selected.moduleName, selected.theoryName, family⟩

@[simp] theorem lowerModule_quote
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} (codec : Codec registry I parameterCount context)
    (resolved : ResolvedModule (registry := registry) (I := I)
      (parameterCount := parameterCount) context) :
    lowerModule codec (resolved.quote codec) = some resolved := by
  cases resolved
  simp [ResolvedModule.quote, SingleFamilySource.quote, selectSingleFamily, lowerModule]

theorem quote_lowerModule
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} (codec : Codec registry I parameterCount context)
    (source : Module)
    (resolved : ResolvedModule (registry := registry) (I := I)
      (parameterCount := parameterCount) context)
    (accepted : lowerModule codec source = some resolved) :
    resolved.quote codec = source := by
  unfold lowerModule at accepted
  cases selectedResult : selectSingleFamily source with
  | none => simp [selectedResult] at accepted
  | some selected =>
      cases familyResult : lowerFamily codec selected.family with
      | none => simp [selectedResult, familyResult] at accepted
      | some family =>
          have same :
              (⟨selected.moduleName, selected.theoryName, family⟩ :
                ResolvedModule context) = resolved := by
            simpa [selectedResult, familyResult] using accepted
          subst resolved
          rw [ResolvedModule.quote]
          rw [quote_lowerFamily codec selected.family family familyResult]
          exact selectSingleFamily_exact source selected selectedResult

#print axioms lowerCode_quote
#print axioms quote_lowerCode
#print axioms lowerFamily_quote
#print axioms quote_lowerFamily
#print axioms lowerModule_quote
#print axioms quote_lowerModule

end Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLowering
