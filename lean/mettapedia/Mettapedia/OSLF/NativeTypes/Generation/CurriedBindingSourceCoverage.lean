import Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingSource

/-!
# Coverage of independently typed source binder bodies

Canonical source inhabitants are decoded from the original authored typing
judgment. The proof uses the constructor declaration and binder representation
directly, and applies uniformly to every admitted language and base context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open BindingSemanticAdmission

variable {language : LanguageDef}

theorem arrow_source_lambda {context : List String} {pattern : Pattern}
    {domain : String} {codomain : TypeExpr}
    (typed : HasType language FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern (.arrow (.base domain) codomain))
    (object : isObjectPattern pattern = true) :
    ∃ binder body, pattern = .lambda binder body ∧
      HasType language FreeTypeContext.empty
        (.base domain :: Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) body codomain := by
  cases pattern with
  | bvar index =>
      cases typed with
      | bvar lookup =>
          simp only [Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.getElem?_map] at lookup
          cases found : context[index]? <;> simp [found] at lookup
  | fvar name => cases typed with | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | apply => cases typed
  | lambda binder body => cases typed with | lambda bodyTyped => exact ⟨binder, body, rfl, bodyTyped⟩
  | multiLambda => cases typed
  | subst => simp [isObjectPattern] at object
  | collection => cases typed

theorem unwrap_typed {type : TypeExpr} {domains : List String} {result : String}
    (spine : BinderSpine type domains result) (context : List String) (pattern : Pattern)
    (typed : HasType language FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern type)
    (object : isObjectPattern pattern = true)
    (canonical : pattern.hasCanonicalBinderMetadata = true) :
    ∃ body, pattern = wrap domains body ∧
      HasType language FreeTypeContext.empty
        (Mettapedia.GSLT.Poly.BindingLanguage.typeContext (domains.reverse ++ context)) body (.base result) ∧
      isObjectPattern body = true ∧ body.hasCanonicalBinderMetadata = true ∧ sizeOf body ≤ sizeOf pattern := by
  induction spine generalizing context pattern with
  | result sort => exact ⟨pattern, rfl, typed, object, canonical, Nat.le_refl _⟩
  | @binder type domains result domain spine ih =>
      obtain ⟨binder, body, rfl, bodyTyped⟩ := arrow_source_lambda typed object
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true,
        Option.isNone_iff_eq_none] at canonical
      obtain ⟨rfl, bodyCanonical⟩ := canonical
      obtain ⟨inside, printed, insideTyped, insideObject, insideCanonical, size⟩ :=
        ih (domain :: context) body bodyTyped object bodyCanonical
      refine ⟨inside, by rw [wrap, ← printed], ?_, insideObject, insideCanonical, ?_⟩
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using insideTyped
      · simp only [Pattern.lambda.sizeOf_spec]
        omega

theorem unprintArgument {parameter : TermParam} {scope : List String} {result : String}
    (meaning : ParameterMeaning parameter scope result) (context : List String)
    (argument : Pattern) {expected : TypeExpr}
    (expectedType : parameterType? parameter = some expected)
    (typed : HasType language FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) argument expected)
    (object : isObjectPattern argument = true)
    (canonical : argument.hasCanonicalBinderMetadata = true) :
    ∃ body, printArgument parameter body = argument ∧
      HasType language FreeTypeContext.empty
        (Mettapedia.GSLT.Poly.BindingLanguage.typeContext (scope ++ context)) body (.base result) ∧
      isObjectPattern body = true ∧ body.hasCanonicalBinderMetadata = true ∧ sizeOf body ≤ sizeOf argument := by
  cases meaning with
  | data name sort =>
      simp only [parameterType?, Option.some.injEq] at expectedType
      subst expected
      exact ⟨argument, rfl, typed, object, canonical, Nat.le_refl _⟩
  | shorthand binder bodyName sort =>
      simp only [parameterType?, Option.some.injEq] at expectedType
      subst expected
      obtain ⟨body, printed, bodyTyped, bodyObject, bodyCanonical, size⟩ :=
        unwrap_typed (BinderSpine.binder result (.result result)) context argument typed object canonical
      exact ⟨body, printed.symm, bodyTyped, bodyObject, bodyCanonical, size⟩
  | @binding binder bodyName domain bodyType domains result spine =>
      simp only [parameterType?, Option.some.injEq] at expectedType
      subst expected
      have full := BinderSpine.binder domain spine
      have decoded := (binderSpine?_exact _ _ _).mpr full
      obtain ⟨body, printed, bodyTyped, bodyObject, bodyCanonical, size⟩ :=
        unwrap_typed full context argument typed object canonical
      refine ⟨body, ?_, bodyTyped, bodyObject, bodyCanonical, size⟩
      simpa only [printArgument, decoded] using printed.symm

theorem exists_arguments {bound : Nat}
    (recurse : ∀ {context : List String} {sort : String} (pattern : Pattern),
      sizeOf pattern < bound →
      HasType language FreeTypeContext.empty
        (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern (.base sort) →
      isObjectPattern pattern = true → pattern.hasCanonicalBinderMetadata = true →
      ∃ term : Term (signature language) context sort, toPattern term = pattern) :
    (parameters : List TermParam) →
    (supported : ∀ parameter ∈ parameters, ∃ scope result, ParameterMeaning parameter scope result) →
    (context : List String) → (patterns : List Pattern) →
    ArgumentsHaveTypes language FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) patterns parameters →
    (∀ pattern ∈ patterns, sizeOf pattern < bound) →
    (∀ pattern ∈ patterns, isObjectPattern pattern = true) →
    (∀ pattern ∈ patterns, pattern.hasCanonicalBinderMetadata = true) →
    ∃ arguments : Args (signature language) (slots parameters) context,
      toPatterns parameters arguments = patterns
  | [], _, _, _, typed, _, _, _ => by cases typed; exact ⟨.nil, rfl⟩
  | parameter :: parameters, supported, context, patterns, typed, small, objects, canonicals => by
      cases patterns with
      | nil => cases typed
      | cons pattern patterns =>
          cases typed with
          | cons representation expectedType headTyped tailTyped =>
              obtain ⟨scope, result, meaning⟩ := supported parameter List.mem_cons_self
              obtain ⟨body, argumentPrinted, bodyTyped, bodyObject, bodyCanonical, bodySize⟩ :=
                unprintArgument meaning context pattern expectedType headTyped
                  (objects pattern List.mem_cons_self) (canonicals pattern List.mem_cons_self)
              have bodySmall : sizeOf body < bound :=
                lt_of_le_of_lt bodySize (small pattern List.mem_cons_self)
              obtain ⟨term, printed⟩ := recurse body bodySmall bodyTyped bodyObject bodyCanonical
              obtain ⟨rest, restPrinted⟩ := exists_arguments recurse parameters
                (fun next member => supported next (List.mem_cons_of_mem _ member))
                context patterns tailTyped
                (fun next member => small next (List.mem_cons_of_mem _ member))
                (fun next member => objects next (List.mem_cons_of_mem _ member))
                (fun next member => canonicals next (List.mem_cons_of_mem _ member))
              change ∃ arguments : Args (signature language) (slot parameter :: slots parameters) context,
                toPatterns (parameter :: parameters) arguments = pattern :: patterns
              rw [slot_meaning meaning]
              refine ⟨.cons term rest, ?_⟩
              change printArgument parameter (toPattern term) :: toPatterns parameters rest = pattern :: patterns
              rw [printed, argumentPrinted, restPrinted]

theorem exists_toPattern_of_size (admitted : Admitted language) :
    (bound : Nat) → (context : List String) → (pattern : Pattern) → sizeOf pattern < bound →
    (sort : String) →
    HasType language FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern (.base sort) →
    isObjectPattern pattern = true → pattern.hasCanonicalBinderMetadata = true →
    ∃ term : Term (signature language) context sort, toPattern term = pattern
  | 0, _, _, small, _, _, _, _ => absurd small (Nat.not_lt_zero _)
  | bound + 1, context, pattern, small, sort, typed, object, canonical => by
      cases pattern with
      | bvar index =>
          cases typed with
          | bvar lookup =>
              obtain ⟨position, printed⟩ := Mettapedia.GSLT.Poly.BindingLanguage.exists_var_of_get
                (Mettapedia.GSLT.Poly.BindingLanguage.lookup_base lookup)
              exact ⟨.var position, congrArg Pattern.bvar
                ((variableIndex_eq_varIndex position).trans printed)⟩
      | fvar name => cases typed with | fvar lookup => simp [FreeTypeContext.empty] at lookup
      | apply constructor patterns =>
          cases typed with
          | constructor member ordinary argumentsTyped =>
              rename_i declaration
              have smaller : ∀ pattern ∈ patterns, sizeOf pattern < bound := by
                intro pattern memberPattern
                have := List.sizeOf_lt_of_mem memberPattern
                simp only [Pattern.apply.sizeOf_spec] at small
                omega
              have objects : ∀ pattern ∈ patterns, isObjectPattern pattern = true := by
                simpa [isObjectPattern, Mettapedia.GSLT.Poly.BindingLanguage.isObjectPatternList_eq_true_iff] using object
              have canonicals : ∀ pattern ∈ patterns, pattern.hasCanonicalBinderMetadata = true :=
                (Pattern.hasCanonicalBinderMetadataList_eq_true_iff patterns).mp canonical
              obtain ⟨arguments, printed⟩ := exists_arguments
                (fun {context} {sort} pattern small typed object canonical =>
                  exists_toPattern_of_size admitted bound context pattern small sort typed object canonical)
                declaration.params (admitted declaration member) context patterns argumentsTyped
                smaller objects canonicals
              obtain ⟨index, valid, original⟩ := List.mem_iff_getElem.mp member
              subst declaration
              let origin : Origin language language.terms[index].category :=
                ⟨⟨index, valid⟩, rfl, admitted _ (List.getElem_mem valid)⟩
              refine ⟨.op origin arguments, ?_⟩
              exact congrArg (Pattern.apply language.terms[index].label) printed
      | lambda => cases typed
      | multiLambda => cases typed
      | subst => simp [isObjectPattern] at object
      | collection kind elements rest =>
          obtain ⟨declaration, member, _, name, element, shape⟩ :=
            declared_collection_constructor_of_hasSort typed
          obtain ⟨scope, result, impossible⟩ := admitted declaration member
            (.simple name (.collection kind element))
            (by rw [shape]; exact List.mem_singleton_self _)
          cases impossible

theorem exists_toPattern (admitted : Admitted language)
    {context : List String} {pattern : Pattern} {sort : String}
    (typed : HasType language FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern (.base sort))
    (object : isObjectPattern pattern = true)
    (canonical : pattern.hasCanonicalBinderMetadata = true) :
    ∃ term : Term (signature language) context sort, toPattern term = pattern :=
  exists_toPattern_of_size admitted (sizeOf pattern + 1) context pattern (Nat.lt_succ_self _)
    sort typed object canonical

abbrev Source (language : LanguageDef) (context : List String) (sort : String) :=
  {pattern : Pattern // HasType language FreeTypeContext.empty
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern (.base sort) ∧
    isObjectPattern pattern = true ∧ pattern.hasCanonicalBinderMetadata = true}

/-- Genuine independent adequacy: the original typed canonical source family
and the computed binding signature have exactly the same inhabitants. -/
noncomputable def sourceEquiv (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) (context : List String) (sort : String) :
    Term (signature language) context sort ≃ Source language context sort :=
  Equiv.ofBijective
    (fun term => ⟨toPattern term, toPattern_typed term, toPattern_object term, toPattern_canonical term⟩)
    ⟨fun _ _ equality => toPattern_injective labels (congrArg Subtype.val equality),
      fun source => by
        obtain ⟨term, printed⟩ := exists_toPattern admitted source.2.1 source.2.2.1 source.2.2.2
        exact ⟨term, Subtype.ext printed⟩⟩

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
