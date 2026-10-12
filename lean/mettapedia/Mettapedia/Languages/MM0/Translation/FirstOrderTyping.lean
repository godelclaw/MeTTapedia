import Mettapedia.Languages.MM0.Translation.FirstOrderSyntax
import Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitution
import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules

/-!
# Many-sorted first-order declarations compiled to MM0

The source typing judgment is `WellSorted.HasType`, derived from the authored
`LanguageDef`. This translation admits ordinary parameters at declared base
sorts. Object binders, function types, and collections require other fragments.
Declaration names and their authored order remain available beside MM0's
numeric signature. Context translation uses regular variables with empty
bound-variable dependencies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderTyping

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Kernel FirstOrderSyntax

def sortNames (language : LanguageDef) : List String := language.types.map (·.name)

def constructorNames (language : LanguageDef) : List String := language.terms.map (·.label)

/-- Only a declared base sort has a first-order MM0 sort index. -/
def type? (sorts : List String) : TypeExpr → Option Nat
  | .base name => index? sorts name
  | _ => none

def parameters? (sorts : List String) : List TermParam → Option Context
  | [] => some []
  | .simple _ type :: parameters => do
      let sort ← type? sorts type
      let remaining ← parameters? sorts parameters
      pure (.regular sort ∅ :: remaining)
  | _ => none

/-- Compile the actual constructor declaration, including its ordered formals. -/
def declaration? (sorts : List String) (rule : GrammarRule) : Option TermDecl := do
  let arguments ← parameters? sorts rule.params
  let result ← index? sorts rule.category
  pure ⟨arguments, result, ∅⟩

def context? (sorts : List String) : List TypeExpr → Option Context
  | [] => some []
  | type :: types => do
      let sort ← type? sorts type
      let remaining ← context? sorts types
      pure (.regular sort ∅ :: remaining)

theorem type?_reference {localSorts joinedSorts : List String} {type : TypeExpr}
    {localIndex joinedIndex : Nat}
    (before : type? localSorts type = some localIndex)
    (after : type? joinedSorts type = some joinedIndex) :
    references? localSorts joinedSorts localIndex = some joinedIndex := by
  cases type <;> simp [type?] at before after
  exact references?_of_name before after

/-- A decidable admission condition on one authored syntax signature. -/
structure Signature where
  language : LanguageDef
  distinctSorts : (sortNames language).Nodup
  distinctConstructors : (constructorNames language).Nodup
  ordinaryConstructors : ∀ rule ∈ language.terms,
    ∃ declaration, declaration? (sortNames language) rule = some declaration

namespace Signature

def sorts (source : Signature) : List String := sortNames source.language
def names (source : Signature) : List String := constructorNames source.language

/-- A target index refers to the source constructor at that same position. -/
def termSignature (source : Signature) : TermSignature := fun index => do
  let rule ← source.language.terms[index]?
  declaration? source.sorts rule

def check (language : LanguageDef) : Bool :=
  decide (sortNames language).Nodup && decide (constructorNames language).Nodup &&
    language.terms.all (fun rule => (declaration? (sortNames language) rule).isSome)

/-- The source fragment is admitted from its declarations, rather than from
a caller-supplied semantic correctness certificate. -/
def admit? (language : LanguageDef) : Option Signature :=
  if sortsDistinct : (sortNames language).Nodup then
    if constructorsDistinct : (constructorNames language).Nodup then
      if ordinary : language.terms.all
          (fun rule => (declaration? (sortNames language) rule).isSome) = true then
        some {
          language := language
          distinctSorts := sortsDistinct
          distinctConstructors := constructorsDistinct
          ordinaryConstructors := by
            intro rule member
            have admitted := List.all_eq_true.mp ordinary rule member
            cases result : declaration? (sortNames language) rule with
            | none => simp [result] at admitted
            | some declaration => exact ⟨declaration, rfl⟩ }
      else none
    else none
  else none

theorem admit?_isSome_iff (language : LanguageDef) :
    (admit? language).isSome = true ↔ check language = true := by
  by_cases sortsDistinct : (sortNames language).Nodup
  · by_cases constructorsDistinct : (constructorNames language).Nodup
    · by_cases ordinary : language.terms.all
        (fun rule => (declaration? (sortNames language) rule).isSome) = true <;>
        simp [admit?, check, sortsDistinct, constructorsDistinct, ordinary]
    · simp [admit?, check, sortsDistinct, constructorsDistinct]
  · simp [admit?, check, sortsDistinct]

theorem admit?_language {language : LanguageDef} {source : Signature}
    (admitted : admit? language = some source) : source.language = language := by
  unfold admit? at admitted
  split at admitted <;> try contradiction
  split at admitted <;> try contradiction
  split at admitted <;> try contradiction
  cases admitted
  rfl

end Signature

/-- One source-context entry becomes an ordinary MM0 variable of its sort. -/
def EntryEncodes (sorts : List String) (type : TypeExpr) (binder : Binder) : Prop :=
  ∃ sort, type? sorts type = some sort ∧ binder = .regular sort ∅

abbrev ContextEncodes (sorts : List String) := List.Forall₂ (EntryEncodes sorts)

theorem context?_eq_some_iff (sorts : List String) (types : List TypeExpr) (context : Context) :
    context? sorts types = some context ↔ ContextEncodes sorts types context := by
  induction types generalizing context with
  | nil => cases context <;> simp [context?, ContextEncodes]
  | cons type types ih =>
      cases found : type? sorts type with
      | none =>
          cases context <;> simp [context?, found, ContextEncodes, EntryEncodes]
      | some sort =>
          cases context with
          | nil =>
              cases rest : context? sorts types <;> simp [context?, found, rest, ContextEncodes]
          | cons binder remaining =>
              cases rest : context? sorts types <;>
                simp [context?, found, rest, ContextEncodes, EntryEncodes, ← ih, eq_comm]

theorem EntryEncodes.relocate {localSorts joinedSorts : List String} {type : TypeExpr}
    {original image : Binder}
    (before : EntryEncodes localSorts type original)
    (after : EntryEncodes joinedSorts type image) :
    original.relocateSort? (references? localSorts joinedSorts) = some image := by
  obtain ⟨localIndex, localFound, rfl⟩ := before
  obtain ⟨joinedIndex, joinedFound, rfl⟩ := after
  simp [Binder.relocateSort?, type?_reference localFound joinedFound]

theorem ContextEncodes.relocate {localSorts joinedSorts : List String}
    {types : List TypeExpr} {original image : Context}
    (before : ContextEncodes localSorts types original)
    (after : ContextEncodes joinedSorts types image) :
    original.relocateSorts? (references? localSorts joinedSorts) = some image := by
  induction before generalizing image with
  | nil => cases after; rfl
  | cons first rest ih =>
      cases after with
      | cons imageFirst imageRest =>
          have tail := ih imageRest
          unfold Context.relocateSorts? at tail
          simp [Context.relocateSorts?, first.relocate imageFirst, tail]

theorem ContextEncodes.lookup {sorts : List String} {types : List TypeExpr} {context : Context}
    (encoded : ContextEncodes sorts types context) {index : Nat} {type : TypeExpr}
    (found : types[index]? = some type) :
    ∃ binder, context[index]? = some binder ∧ EntryEncodes sorts type binder := by
  induction encoded generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                subst type
                exact ⟨_, rfl, head⟩
      | succ index => exact ih found

theorem ContextEncodes.lookup_source {sorts : List String} {types : List TypeExpr}
    {context : Context} (encoded : ContextEncodes sorts types context)
    {index : Nat} {binder : Binder} (found : context[index]? = some binder) :
    ∃ type, types[index]? = some type ∧ EntryEncodes sorts type binder := by
  induction encoded generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                subst binder
                exact ⟨_, rfl, head⟩
      | succ index => exact ih found

theorem type?_injective {sorts : List String} {first second : TypeExpr} {sort : Nat}
    (left : type? sorts first = some sort) (right : type? sorts second = some sort) : first = second := by
  cases first <;> cases second <;> simp [type?] at left right
  rename_i first second
  exact congrArg TypeExpr.base (Option.some.inj
    ((getElem?_index? left).symm.trans (getElem?_index? right)))

theorem getElem?_named {α : Type} (items : List α) (name : α → String)
    (distinct : (items.map name).Nodup) {item : α} (member : item ∈ items)
    {index : Nat} (found : index? (items.map name) (name item) = some index) :
    items[index]? = some item := by
  have nameFound := getElem?_index? found
  rw [List.getElem?_map] at nameFound
  cases lookup : items[index]? with
  | none => simp [lookup] at nameFound
  | some actual =>
      have sameName : name actual = name item := by simpa [lookup] using nameFound
      have same := List.inj_on_of_nodup_map distinct (List.mem_of_getElem? lookup) member sameName
      subst actual
      rfl

theorem Signature.lookup {source : Signature} {rule : GrammarRule} {index : Nat}
    (member : rule ∈ source.language.terms) (found : index? source.names rule.label = some index) :
    source.termSignature index = declaration? source.sorts rule := by
  have lookup := getElem?_named source.language.terms GrammarRule.label
    source.distinctConstructors member found
  simp [Signature.termSignature, lookup]

theorem Signature.lookup_source {source : Signature} {index : Nat} {declaration : TermDecl}
    (lookup : source.termSignature index = some declaration) :
    ∃ rule, source.language.terms[index]? = some rule ∧
      declaration? source.sorts rule = some declaration := by
  cases found : source.language.terms[index]? with
  | none => simp [Signature.termSignature, found] at lookup
  | some rule =>
      exact ⟨rule, rfl, by simpa [Signature.termSignature, found] using lookup⟩

theorem parameters?_ordinary {sorts : List String} {parameters : List TermParam}
    {context : Context} (compiled : parameters? sorts parameters = some context) :
    ∀ binder ∈ context, ∃ sort, binder = .regular sort ∅ := by
  induction parameters generalizing context with
  | nil => simp only [parameters?, Option.some.injEq] at compiled
           subst context
           simp
  | cons parameter parameters ih =>
      cases parameter with
      | simple name type =>
          cases found : type? sorts type with
          | none => simp [parameters?, found] at compiled
          | some sort =>
              cases rest : parameters? sorts parameters with
              | none => simp [parameters?, found, rest] at compiled
              | some remaining =>
                  have same : Binder.regular sort ∅ :: remaining = context := by
                    simpa [parameters?, found, rest] using compiled
                  subst context
                  intro binder member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact ⟨sort, rfl⟩
                  · exact ih rest binder member
      | _ => simp [parameters?] at compiled

theorem declaration?_fields {sorts : List String} {rule : GrammarRule} {declaration : TermDecl}
    (compiled : declaration? sorts rule = some declaration) :
    parameters? sorts rule.params = some declaration.arguments ∧
      index? sorts rule.category = some declaration.resultSort ∧ declaration.dependencies = ∅ := by
  cases parameters : parameters? sorts rule.params with
  | none => simp [declaration?, parameters] at compiled
  | some arguments =>
      cases result : index? sorts rule.category with
      | none => simp [declaration?, parameters, result] at compiled
      | some sort =>
          have same : (⟨arguments, sort, ∅⟩ : TermDecl) = declaration := by
            simpa [declaration?, parameters, result] using compiled
          subst declaration
          exact ⟨rfl, rfl, rfl⟩

theorem parameters?_relocate {localSorts joinedSorts : List String} {parameters : List TermParam}
    {original image : Context}
    (before : parameters? localSorts parameters = some original)
    (after : parameters? joinedSorts parameters = some image) :
    original.relocateSorts? (references? localSorts joinedSorts) = some image := by
  induction parameters generalizing original image with
  | nil =>
      simp only [parameters?, Option.some.injEq] at before after
      subst original
      subst image
      rfl
  | cons parameter parameters ih =>
      cases parameter with
      | simple formal type =>
          obtain ⟨localIndex, localFound, localTail, localRest, sameLocal⟩ :
              ∃ sort, type? localSorts type = some sort ∧
                ∃ tail, parameters? localSorts parameters = some tail ∧
                  Binder.regular sort ∅ :: tail = original := by
            simpa [parameters?, Option.bind_eq_some_iff] using before
          obtain ⟨joinedIndex, joinedFound, joinedTail, joinedRest, sameJoined⟩ :
              ∃ sort, type? joinedSorts type = some sort ∧
                ∃ tail, parameters? joinedSorts parameters = some tail ∧
                  Binder.regular sort ∅ :: tail = image := by
            simpa [parameters?, Option.bind_eq_some_iff] using after
          subst original
          subst image
          have tail := ih localRest joinedRest
          unfold Context.relocateSorts? at tail
          simp [Context.relocateSorts?, Binder.relocateSort?,
            type?_reference localFound joinedFound, tail]
      | _ => simp [parameters?] at before

theorem declaration?_relocate {localSorts joinedSorts : List String} {rule : GrammarRule}
    {original image : TermDecl}
    (before : declaration? localSorts rule = some original)
    (after : declaration? joinedSorts rule = some image) :
    original.relocate? (references? localSorts joinedSorts) = some image := by
  obtain ⟨originalArguments, originalResult, originalDependencies⟩ := declaration?_fields before
  obtain ⟨imageArguments, imageResult, imageDependencies⟩ := declaration?_fields after
  have arguments := parameters?_relocate originalArguments imageArguments
  have result := references?_of_name originalResult imageResult
  simp [TermDecl.relocate?, arguments, result, originalDependencies, ← imageDependencies]

theorem parameters?_no_bare_collection {sorts : List String} {rule : GrammarRule}
    {context : Context} (compiled : parameters? sorts rule.params = some context) :
    ¬ UsesBareCollection rule := by
  rintro ⟨name, collection, element, shape⟩
  simp [shape, parameters?, type?] at compiled

theorem parameters?_eq_nil_iff (sorts : List String) (parameters : List TermParam) :
    parameters? sorts parameters = some [] ↔ parameters = [] := by
  cases parameters with
  | nil => simp [parameters?]
  | cons parameter parameters =>
      cases parameter with
      | simple name type =>
          cases found : type? sorts type <;> cases rest : parameters? sorts parameters <;>
            simp [parameters?, found, rest]
      | _ => simp [parameters?]

mutual
  /-- Translation preserves the authored typing judgment, in the actual ambient context. -/
  theorem preserves_type {source : Signature} {bound : List TypeExpr} {context : Context}
      {pattern : Pattern} {expression : Preterm} {type : TypeExpr} {sort : Nat}
      (encoded : Encodes source.names pattern expression)
      (contexts : ContextEncodes source.sorts bound context)
      (typing : HasType source.language FreeTypeContext.empty bound pattern type)
      (sortEncoding : type? source.sorts type = some sort) :
      Preterm.HasType source.termSignature context expression [] sort := by
    cases encoded with
    | boundVariable index =>
        cases typing with
        | bvar lookup =>
            obtain ⟨binder, targetLookup, index, found, same⟩ := contexts.lookup lookup
            have sortSame : index = sort := Option.some.inj (found.symm.trans sortEncoding)
            subst index
            subst binder
            exact .var targetLookup
    | @constructor name index arguments expressions found encodedArguments =>
        cases typing with
        | @constructor _ rule _ member _ argumentsTyped =>
            obtain ⟨declaration, compiled⟩ := source.ordinaryConstructors rule member
            obtain ⟨parameters, result, _⟩ := declaration?_fields compiled
            have sortSame : declaration.resultSort = sort := by
              exact Option.some.inj (result.symm.trans sortEncoding)
            have headLookup : source.termSignature index = some declaration :=
              (source.lookup member found).trans compiled
            have argumentsFit := preserves_arguments encodedArguments contexts argumentsTyped parameters
            apply (Preterm.HasType.applyArgs_iff _ _ _ _ _ _).mpr
            refine ⟨declaration.arguments, ?_, argumentsFit⟩
            simpa [sortSame] using (Preterm.HasType.term headLookup :
              Preterm.HasType source.termSignature context (.term index)
                declaration.arguments declaration.resultSort)
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem preserves_arguments {source : Signature} {bound : List TypeExpr} {context : Context}
      {patterns : List Pattern} {expressions : List Preterm} {parameters : List TermParam}
      {formals : Context} (encoded : List.Forall₂ (Encodes source.names) patterns expressions)
      (contexts : ContextEncodes source.sorts bound context)
      (typing : ArgumentsHaveTypes source.language FreeTypeContext.empty bound patterns parameters)
      (compiled : parameters? source.sorts parameters = some formals) :
      List.Forall₂ (Preterm.FitsBinder source.termSignature context) expressions formals := by
    cases encoded with
    | nil =>
        cases typing
        simp only [parameters?, Option.some.injEq] at compiled
        subst formals
        exact .nil
    | @cons pattern expression patterns expressions first rest =>
        cases typing with
        | @cons _ _ _ parameter parameters expected representation parameterType firstTyped restTyped =>
            cases parameter with
            | simple name type =>
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst expected
                cases found : type? source.sorts type with
                | none => simp [parameters?, found] at compiled
                | some sort =>
                    cases remaining : parameters? source.sorts parameters with
                    | none => simp [parameters?, found, remaining] at compiled
                    | some targetParameters =>
                        have same : Binder.regular sort ∅ :: targetParameters = formals := by
                          simpa [parameters?, found, remaining] using compiled
                        subst formals
                        exact .cons (.regular (preserves_type first contexts firstTyped found))
                          (preserves_arguments rest contexts restTyped remaining)
            | _ => simp [parameters?] at compiled
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- Target typing cannot authorize a new sort or an ill-sorted source term. -/
  theorem reflects_type {source : Signature} {bound : List TypeExpr} {context : Context}
      {pattern : Pattern} {expression : Preterm} {type : TypeExpr} {sort : Nat}
      (encoded : Encodes source.names pattern expression)
      (contexts : ContextEncodes source.sorts bound context)
      (typing : Preterm.HasType source.termSignature context expression [] sort)
      (sortEncoding : type? source.sorts type = some sort) :
      HasType source.language FreeTypeContext.empty bound pattern type := by
    cases encoded with
    | boundVariable index =>
        cases typing with
        | var lookup =>
            obtain ⟨actualType, sourceLookup, actualSort, found, same⟩ :=
              contexts.lookup_source lookup
            subst_vars
            have typeSame : actualType = type := type?_injective found sortEncoding
            subst type
            exact .bvar sourceLookup
    | @constructor name index arguments expressions found encodedArguments =>
        obtain ⟨consumed, headTyped, fits⟩ :=
          (Preterm.HasType.applyArgs_iff _ _ _ _ _ _).mp typing
        simp only [List.append_nil] at headTyped
        cases headTyped with
        | @term _ declaration lookup =>
            cases ruleFound : source.language.terms[index]? with
            | none => simp [Signature.termSignature, ruleFound] at lookup
            | some rule =>
                have compiled : declaration? source.sorts rule = some declaration := by
                  simpa [Signature.termSignature, ruleFound] using lookup
                obtain ⟨parameters, result, _⟩ := declaration?_fields compiled
                have nameFound : source.names[index]? = some rule.label := by
                  simp [Signature.names, constructorNames, List.getElem?_map, ruleFound]
                have nameSame : name = rule.label := Option.some.inj
                  ((getElem?_index? found).symm.trans nameFound)
                subst name
                have typeSame : TypeExpr.base rule.category = type :=
                  type?_injective result sortEncoding
                subst type
                exact .constructor (List.mem_of_getElem? ruleFound)
                  (parameters?_no_bare_collection parameters)
                  (reflects_arguments encodedArguments contexts parameters fits)
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem reflects_arguments {source : Signature} {bound : List TypeExpr} {context : Context}
      {patterns : List Pattern} {expressions : List Preterm} {parameters : List TermParam}
      {formals : Context} (encoded : List.Forall₂ (Encodes source.names) patterns expressions)
      (contexts : ContextEncodes source.sorts bound context)
      (compiled : parameters? source.sorts parameters = some formals)
      (fits : List.Forall₂ (Preterm.FitsBinder source.termSignature context) expressions formals) :
      ArgumentsHaveTypes source.language FreeTypeContext.empty bound patterns parameters := by
    cases encoded with
    | nil =>
        cases fits
        have empty := (parameters?_eq_nil_iff _ _).mp compiled
        subst parameters
        exact .nil
    | @cons pattern expression patterns expressions first rest =>
        cases parameters with
        | nil =>
            simp only [parameters?, Option.some.injEq] at compiled
            subst formals
            cases fits
        | cons parameter parameters =>
            cases parameter with
            | simple name type =>
                cases found : type? source.sorts type with
                | none => simp [parameters?, found] at compiled
                | some sort =>
                    cases remaining : parameters? source.sorts parameters with
                    | none => simp [parameters?, found, remaining] at compiled
                    | some targetParameters =>
                        have same : Binder.regular sort ∅ :: targetParameters = formals := by
                          simpa [parameters?, found, remaining] using compiled
                        subst formals
                        cases fits with
                        | cons fitsFirst fitsRest =>
                            cases fitsFirst with
                            | regular firstTyped =>
                                exact .cons (by trivial) rfl
                                  (reflects_type first contexts firstTyped found)
                                  (reflects_arguments rest contexts remaining fitsRest)
            | _ => simp [parameters?] at compiled
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- On the encoded fragment, source and target typing agree in both directions.
This checks the context and every constructor argument, not just the result sort. -/
theorem typing_iff {source : Signature} {bound : List TypeExpr} {context : Context}
    {pattern : Pattern} {expression : Preterm} {type : TypeExpr} {sort : Nat}
    (encoded : Encodes source.names pattern expression)
    (contexts : ContextEncodes source.sorts bound context)
    (sortEncoding : type? source.sorts type = some sort) :
    HasType source.language FreeTypeContext.empty bound pattern type ↔
      Preterm.HasType source.termSignature context expression [] sort :=
  ⟨fun typing => preserves_type encoded contexts typing sortEncoding,
    fun typing => reflects_type encoded contexts typing sortEncoding⟩

/-- The same sort discipline governs rule instantiation: MM0 substitution
admission agrees exactly with authored positional argument typing. -/
theorem admissibility_iff {source : Signature} {bound : List TypeExpr} {context : Context}
    {patterns : List Pattern} {expressions : List Preterm} {parameters : List TermParam}
    {formals : Context} (encoded : List.Forall₂ (Encodes source.names) patterns expressions)
    (contexts : ContextEncodes source.sorts bound context)
    (compiled : parameters? source.sorts parameters = some formals) :
    ArgumentsHaveTypes source.language FreeTypeContext.empty bound patterns parameters ↔
      Substitution.Admissible source.termSignature formals context expressions := by
  have regular : ∀ binder ∈ formals, ∃ sort dependencies,
      binder = .regular sort dependencies := by
    intro binder member
    obtain ⟨sort, same⟩ := parameters?_ordinary compiled binder member
    exact ⟨sort, ∅, same⟩
  rw [Substitution.admissible_iff_typed_of_regular_formals _ _ _ _ regular]
  exact ⟨fun typing => preserves_arguments encoded contexts typing compiled,
    fun fits => reflects_arguments encoded contexts compiled fits⟩

/-- Compiled local contexts contain only ordinary, dependency-free variables. -/
theorem ContextEncodes.ordinary {sorts : List String} {types : List TypeExpr} {context : Context}
    (encoded : ContextEncodes sorts types context) :
    ∀ binder ∈ context, ∃ sort, binder = .regular sort ∅ := by
  induction encoded with
  | nil => simp
  | cons first rest ih =>
      intro binder member
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨sort, _, same⟩ := first
        exact ⟨sort, same⟩
      · exact ih binder member

/-- Positional rule vectors obey the same sort discipline as constructor arguments. -/
theorem typed_vector_iff {source : Signature} {bound types : List TypeExpr}
    {context formals : Context} {patterns : List Pattern} {expressions : List Preterm}
    (encoded : List.Forall₂ (Encodes source.names) patterns expressions)
    (contexts : ContextEncodes source.sorts bound context)
    (formalContexts : ContextEncodes source.sorts types formals) :
    List.Forall₂ (fun pattern type =>
      HasType source.language FreeTypeContext.empty bound pattern type) patterns types ↔
    List.Forall₂ (Preterm.FitsBinder source.termSignature context) expressions formals := by
  induction encoded generalizing types formals with
  | nil =>
      cases formalContexts with
      | nil => exact ⟨fun _ => .nil, fun _ => .nil⟩
      | cons first rest => constructor <;> intro impossible <;> cases impossible
  | @cons pattern expression patterns expressions first rest ih =>
      cases formalContexts with
      | nil => constructor <;> intro impossible <;> cases impossible
      | @cons type binder types formals head tail =>
          obtain ⟨sort, typeEncoding, rfl⟩ := head
          constructor
          · intro typed
            cases typed with
            | cons headTyped tailTyped =>
                exact .cons (.regular (preserves_type first contexts headTyped typeEncoding))
                  ((ih tail).mp tailTyped)
          · intro typed
            cases typed with
            | cons headTyped tailTyped =>
                cases headTyped with
                | regular headTyped =>
                    exact .cons (reflects_type first contexts headTyped typeEncoding)
                      ((ih tail).mpr tailTyped)

theorem vector_admissibility_iff {source : Signature} {bound types : List TypeExpr}
    {context formals : Context} {patterns : List Pattern} {expressions : List Preterm}
    (encoded : List.Forall₂ (Encodes source.names) patterns expressions)
    (contexts : ContextEncodes source.sorts bound context)
    (formalContexts : ContextEncodes source.sorts types formals) :
    List.Forall₂ (fun pattern type =>
      HasType source.language FreeTypeContext.empty bound pattern type) patterns types ↔
      Substitution.Admissible source.termSignature formals context expressions := by
  rw [Substitution.admissible_iff_typed_of_regular_formals _ _ _ _]
  · exact typed_vector_iff encoded contexts formalContexts
  · intro binder member
    obtain ⟨sort, same⟩ := formalContexts.ordinary binder member
    exact ⟨sort, ∅, same⟩

/-- Every typed MM0 expression over the compiled signature is a named source
spine. A residual function type always has a constructor head; context
variables are saturated and cannot acquire arguments. -/
theorem typed_encodable {source : Signature} {context remaining : Context}
    {expression : Preterm} {sort : Nat}
    (typing : Preterm.HasType source.termSignature context expression remaining sort) :
    (∀ binder ∈ remaining, ∃ sort, binder = .regular sort ∅) ∧
      ∃ pattern, Encodes source.names pattern expression ∧
        (remaining ≠ [] → ∃ name arguments, pattern = Pattern.apply name arguments) := by
  induction typing with
  | var lookup =>
      exact ⟨by simp, _, .boundVariable _, fun nonempty => False.elim (nonempty rfl)⟩
  | @term index declaration lookup =>
      obtain ⟨rule, found, compiled⟩ := source.lookup_source lookup
      obtain ⟨parameters, _, _⟩ := declaration?_fields compiled
      have nameFound : source.names[index]? = some rule.label := by
        simp [Signature.names, constructorNames, List.getElem?_map, found]
      refine ⟨parameters?_ordinary parameters, Pattern.apply rule.label [], ?_, ?_⟩
      · exact .constructor (index?_getElem? source.distinctConstructors nameFound) .nil
      · intro _
        exact ⟨rule.label, [], rfl⟩
  | bound _ _ ih =>
      obtain ⟨sort, impossible⟩ := ih.1 _ (List.mem_cons_self ..)
      cases impossible
  | @regular function argument expected result dependencies remaining _ _ ihFunction ihArgument =>
      obtain ⟨functionPattern, functionEncoded, functionShape⟩ := ihFunction.2
      obtain ⟨name, arguments, rfl⟩ := functionShape (by simp)
      obtain ⟨argumentPattern, argumentEncoded, _⟩ := ihArgument.2
      cases functionEncoded with
      | constructor found encodedArguments =>
          refine ⟨?_, Pattern.apply name (arguments ++ [argumentPattern]), ?_, ?_⟩
          · intro binder member
            exact ihFunction.1 binder (List.mem_cons_of_mem _ member)
          · simpa only [Preterm.applyArgs_append, Preterm.applyArgs] using
              (Encodes.constructor found
                (List.rel_append encodedArguments (.cons argumentEncoded .nil)))
          · intro _
            exact ⟨name, arguments ++ [argumentPattern], rfl⟩

/-- No typed target term lies outside the translated source typing fibre. -/
theorem typed_image {source : Signature} {bound : List TypeExpr} {context : Context}
    {expression : Preterm} {type : TypeExpr} {sort : Nat}
    (contexts : ContextEncodes source.sorts bound context)
    (sortEncoding : type? source.sorts type = some sort)
    (typing : Preterm.HasType source.termSignature context expression [] sort) :
    ∃ pattern, Encodes source.names pattern expression ∧
      HasType source.language FreeTypeContext.empty bound pattern type := by
  obtain ⟨_, pattern, encoded, _⟩ := typed_encodable typing
  exact ⟨pattern, encoded, reflects_type encoded contexts typing sortEncoding⟩

/-- All admitted target argument vectors have typed source representatives. -/
theorem typed_vector_image {source : Signature} {bound types : List TypeExpr}
    {context formals : Context} {expressions : List Preterm}
    (contexts : ContextEncodes source.sorts bound context)
    (formalContexts : ContextEncodes source.sorts types formals)
    (typed : List.Forall₂ (Preterm.FitsBinder source.termSignature context) expressions formals) :
    ∃ patterns, List.Forall₂ (Encodes source.names) patterns expressions ∧
      List.Forall₂ (fun pattern type =>
        HasType source.language FreeTypeContext.empty bound pattern type) patterns types := by
  induction formalContexts generalizing expressions with
  | nil => cases typed; exact ⟨[], .nil, .nil⟩
  | @cons type binder types formals first rest ih =>
      obtain ⟨sort, typeEncoding, rfl⟩ := first
      cases typed with
      | @cons expression _ _ _ head tail =>
          cases head with
          | regular typing =>
              obtain ⟨pattern, encoded, sourceTyped⟩ := typed_image contexts typeEncoding typing
              obtain ⟨patterns, encodedTail, typedTail⟩ := ih tail
              exact ⟨pattern :: patterns, .cons encoded encodedTail, .cons sourceTyped typedTail⟩

example : parameters? ["wff", "set"] [.simple "ph" (.base "wff")] =
    some [.regular 0 ∅] := by simp [parameters?, type?, index?]

example : parameters? ["wff", "set"] [.simple "ph" (.base "missing")] = none := by
  simp [parameters?, type?, index?]

example : parameters? ["wff", "set"]
    [.abstractionNamed (some "x") "ph" (.base "wff")] = none := rfl

/-! ## Encoding typed source terms -/

mutual
  /-- Every typed term in the existing first-order compiler fragment can be encoded. -/
  theorem typed_source_image {source : Signature} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr} {sort : Nat}
      (typing : HasType source.language FreeTypeContext.empty bound pattern type)
      (fragment : isMatchCorrectAux pattern = true)
      (sortEncoding : type? source.sorts type = some sort) :
      ∃ expression, Encodes source.names pattern expression := by
    cases pattern with
    | bvar index => exact ⟨.var index, .boundVariable index⟩
    | fvar name =>
        cases typing with
        | fvar impossible => simp [FreeTypeContext.empty] at impossible
    | apply name arguments =>
        cases typing with
        | @constructor _ rule _ member _ argumentsTyped =>
            obtain ⟨declaration, compiled⟩ := source.ordinaryConstructors rule member
            have parameters := (declaration?_fields compiled).1
            obtain ⟨expressions, encoded⟩ := typed_source_arguments argumentsTyped
              (by simpa [isMatchCorrectAux] using fragment) parameters
            have nameMember : rule.label ∈ source.names :=
              List.mem_map_of_mem member
            exact ⟨Preterm.applyArgs (.term (source.names.idxOf rule.label)) expressions,
              .constructor (index?_some _ _ nameMember) encoded⟩
    | _ => simp [isMatchCorrectAux] at fragment
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem typed_source_arguments {source : Signature} {bound : List TypeExpr}
      {patterns : List Pattern} {parameters : List TermParam} {formals : Context}
      (typing : ArgumentsHaveTypes source.language FreeTypeContext.empty bound patterns parameters)
      (fragment : isMatchCorrectListAux patterns = true)
      (compiled : parameters? source.sorts parameters = some formals) :
      ∃ expressions, List.Forall₂ (Encodes source.names) patterns expressions := by
    cases typing with
    | nil => exact ⟨[], .nil⟩
    | @cons _ pattern patterns parameter parameters expected _ parameterType first rest =>
        have fragments : isMatchCorrectAux pattern = true ∧
            isMatchCorrectListAux patterns = true := by
          simpa [isMatchCorrectListAux] using fragment
        cases parameter with
        | simple name type =>
            simp only [parameterType?, Option.some.injEq] at parameterType
            subst expected
            cases found : type? source.sorts type with
            | none => simp [parameters?, found] at compiled
            | some sort =>
                cases remaining : parameters? source.sorts parameters with
                | none => simp [parameters?, found, remaining] at compiled
                | some target =>
                    obtain ⟨expression, headEncoded⟩ := typed_source_image first fragments.1 found
                    obtain ⟨expressions, tailEncoded⟩ := typed_source_arguments rest fragments.2 remaining
                    exact ⟨expression :: expressions, .cons headEncoded tailEncoded⟩
        | _ => simp [parameters?] at compiled
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  theorem encoded_matchCorrect {names : List String} {pattern : Pattern} {expression : Preterm}
      (encoded : Encodes names pattern expression) : isMatchCorrectAux pattern = true := by
    cases encoded with
    | boundVariable index => rfl
    | constructor _ arguments => exact encodesList_matchCorrect arguments
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem encodesList_matchCorrect {names : List String} {patterns : List Pattern}
      {expressions : List Preterm} (encoded : List.Forall₂ (Encodes names) patterns expressions) :
      isMatchCorrectListAux patterns = true := by
    cases encoded with
    | nil => rfl
    | cons first rest =>
        simp only [isMatchCorrectListAux, Bool.and_eq_true]
        exact ⟨encoded_matchCorrect first, encodesList_matchCorrect rest⟩
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem typed_source_vector {source : Signature} {bound types : List TypeExpr}
    {formals : Context} {patterns : List Pattern}
    (typing : List.Forall₂ (fun pattern type =>
      HasType source.language FreeTypeContext.empty bound pattern type) patterns types)
    (formalContexts : ContextEncodes source.sorts types formals)
    (fragment : ∀ pattern ∈ patterns, isMatchCorrectAux pattern = true) :
    ∃ expressions, List.Forall₂ (Encodes source.names) patterns expressions := by
  induction typing generalizing formals with
  | nil => exact ⟨[], .nil⟩
  | @cons pattern type patterns types first rest ih =>
      cases formalContexts with
      | cons head tail =>
          obtain ⟨sort, typeEncoding, _⟩ := head
          obtain ⟨expression, encoded⟩ :=
            typed_source_image first (fragment pattern (by simp)) typeEncoding
          obtain ⟨expressions, encodedTail⟩ := ih tail
            (fun pattern member => fragment pattern (List.mem_cons_of_mem _ member))
          exact ⟨expression :: expressions, .cons encoded encodedTail⟩

theorem encoded_arguments_lookup {names : List String} {patterns : List Pattern}
    {expressions : List Preterm} (encoded : List.Forall₂ (Encodes names) patterns expressions)
    {index : Nat} {image : Preterm}
    (lookup : Substitution.ofList expressions index = some image) :
    Encodes names (argumentAt patterns index) image := by
  have found : ∃ pattern, patterns[index]? = some pattern ∧ Encodes names pattern image := by
    induction encoded generalizing index with
    | nil => simp [Substitution.ofList] at lookup
    | cons first rest ih =>
        cases index with
        | zero =>
            simp only [Substitution.ofList, List.getElem?_cons_zero, Option.some.injEq] at lookup
            subst image
            exact ⟨_, rfl, first⟩
        | succ index => exact ih lookup
  obtain ⟨pattern, found, encoding⟩ := found
  simpa only [argumentAt, found, Option.getD_some] using encoding

end Mettapedia.Languages.MM0.Translation.FirstOrderTyping
