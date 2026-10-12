import Mettapedia.OSLF.NativeTypes.Generation.NativeSignature
import Mettapedia.GSLT.Poly.BindingLanguage
import Mettapedia.OSLF.Syntax.BindingFunctionArgumentComparison

/-!
# Authored binder arguments as contextual native function objects

The native function carrier is interpreted in the presheaf category of the
actual free binding clone. Its points are contextual natural transformations,
not arbitrary functions between sets of closed source terms. Source adequacy
uses the independently typed object-pattern fragment, the original grammar,
and its binding representation requirements. The checked profile below is
stricter than native declaration decoding; decoding alone does not establish
this adequacy for higher-order ordinary parameters.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingCarrierSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open Mettapedia.TypeTheory.Calculi.NativeDependent

open Mettapedia.GSLT.Poly.BindingLanguage

def supportedParameter : TermParam → Bool
  | .simple _ (.base _) => true
  | .abstractionNamed _ _ (.base _) => true
  | .abstractionNamed _ _ (.arrow (.base _) (.base _)) => true
  | _ => false

def checkProfile (language : LanguageDef) : Bool :=
  language.terms.all (fun declaration => declaration.params.all supportedParameter) &&
    decide (language.terms.map (·.label)).Nodup

theorem parameter_binding_fragment (parameter : TermParam)
    (supported : supportedParameter parameter = true) :
    (Mettapedia.GSLT.Poly.BindingLanguage.bindingDecl? parameter).isSome = true := by
  cases parameter with
  | simple name type => cases type <;> simp_all [supportedParameter, Mettapedia.GSLT.Poly.BindingLanguage.bindingDecl?]
  | abstractionNamed binder bodyName type =>
      cases type with
      | base sort => rfl
      | arrow domain codomain =>
          cases domain <;> cases codomain <;>
            simp_all [supportedParameter, Mettapedia.GSLT.Poly.BindingLanguage.bindingDecl?]
      | multiBinder domain => simp [supportedParameter] at supported
      | collection kind element => simp [supportedParameter] at supported
  | multiAbstractionNamed names bodyName type => simp [supportedParameter] at supported

theorem profile_sound (language : LanguageDef) (checked : checkProfile language = true) :
    (∀ declaration ∈ language.terms, Mettapedia.GSLT.Poly.BindingLanguage.BinderRule declaration) ∧
      (language.terms.map (·.label)).Nodup := by
  simp only [checkProfile, Bool.and_eq_true, decide_eq_true_eq] at checked
  refine ⟨?_, checked.2⟩
  intro declaration declared parameter member
  exact parameter_binding_fragment parameter
    (List.all_eq_true.mp (List.all_eq_true.mp checked.1 declaration declared) parameter member)

variable {language : LanguageDef}

abbrev algebra (language : LanguageDef) := BindingCloneAlgebra.terms (Mettapedia.GSLT.Poly.BindingLanguage.signature language)

abbrev TypedObject (language : LanguageDef) (context : List String) (sort : String) :=
  {pattern : Pattern // HasType language FreeTypeContext.empty (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context)
      pattern (.base sort) ∧ isObjectPattern pattern = true}

/-- Open source patterns have exactly the free binding terms, in every
finite base-sort context. The inverse comes from independent source typing. -/
noncomputable def sourceEquiv
    (fragment : ∀ declaration ∈ language.terms, Mettapedia.GSLT.Poly.BindingLanguage.BinderRule declaration)
    (labels : (language.terms.map (·.label)).Nodup) (context : List String) (sort : String) :
    Term (Mettapedia.GSLT.Poly.BindingLanguage.signature language) context sort ≃ TypedObject language context sort :=
  Equiv.ofBijective
    (fun term => ⟨Mettapedia.GSLT.Poly.BindingLanguage.toPattern term,
      Mettapedia.GSLT.Poly.BindingLanguage.toPattern_hasType term, Mettapedia.GSLT.Poly.BindingLanguage.toPattern_isObjectPattern term⟩)
    ⟨fun left right same => Mettapedia.GSLT.Poly.BindingLanguage.toPattern_injective labels left right (congrArg Subtype.val same),
      fun pattern => by
        obtain ⟨term, printed⟩ := Mettapedia.GSLT.Poly.BindingLanguage.exists_toPattern fragment pattern.1 sort pattern.2.1 pattern.2.2
        exact ⟨term, Subtype.ext printed⟩⟩

/-- Every carrier has its genuine presheaf meaning. Only the base-binder
profile receives the source adequacy theorem below. -/
noncomputable def meaning : NativeSignature.Carrier language → Base (algebra language) ⥤ Type
  | .sort position => programs (algebra language) language.types[position.val].name
  | .function domain codomain => (meaning domain).functorHom (meaning codomain)

/-- Independent interpretation of the nullary-sort and function part of the
native syntax. Unsupported dependent formers do not obtain a substitute. -/
noncomputable def nativeMeaning? {headers : List (NativeSignature.Header language)} :
    {n : Nat} → Refinement.TypeExpr (NativeSignature.symbols language headers) n →
      Option (Base (algebra language) ⥤ Type)
  | _, .family position _ => some (programs (algebra language) language.types[position.val].name)
  | _, .pi domain body => do
      let domain ← nativeMeaning? domain
      let body ← nativeMeaning? body
      pure (domain.functorHom body)
  | _, _ => none

theorem native_meaning (carrier : NativeSignature.Carrier language)
    (headers : List (NativeSignature.Header language)) (n : Nat) :
    nativeMeaning? (carrier.native (headers := headers) (n := n)) = some (meaning carrier) := by
  induction carrier generalizing n with
  | sort position => rfl
  | function domain codomain domainIH codomainIH =>
      simp only [NativeSignature.Carrier.native, nativeMeaning?, domainIH, codomainIH,
        meaning]
      rfl

/-- A decoded base-to-base native function is precisely an opened authored
body at its ambient context, through the earned Yoneda comparison. -/
noncomputable def functionBodyEquiv
    (fragment : ∀ declaration ∈ language.terms, Mettapedia.GSLT.Poly.BindingLanguage.BinderRule declaration)
    (labels : (language.terms.map (·.label)).Nodup)
    (context : List String) (domain codomain : Fin language.types.length) :
    (meaning (.function (.sort domain) (.sort codomain))).obj
        (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context)) ≃
      TypedObject language (language.types[domain.val].name :: context) language.types[codomain.val].name :=
  (scopedBodyEquiv (algebra language)
    (ContextObject.ofList (algebra language).substitution.toClone context)
    [language.types[domain.val].name] language.types[codomain.val].name).trans
    (sourceEquiv fragment labels _ _)

/-- Authored binder display metadata remains a parameter of the independent
source argument judgment; semantic patterns use its canonical unnamed form. -/
abbrev BindingArgument (language : LanguageDef) (context : List String)
    (binder : Option String) (bodyName domain codomain : String) :=
  {pattern : Pattern //
    MatchesParameterRepresentation (.abstractionNamed binder bodyName (.arrow (.base domain) (.base codomain)))
        pattern ∧
      HasType language FreeTypeContext.empty (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern
        (.arrow (.base domain) (.base codomain)) ∧
      isObjectPattern pattern = true}

noncomputable def openedArgumentEquiv (context : List String) (binder : Option String)
    (bodyName domain codomain : String) :
    TypedObject language (domain :: context) codomain ≃
      BindingArgument language context binder bodyName domain codomain :=
  Equiv.ofBijective
    (fun body => ⟨.lambda none body.1,
      ⟨trivial, HasType.lambda body.2.1, body.2.2⟩⟩)
    ⟨fun left right same => Subtype.ext (Pattern.lambda.inj (congrArg Subtype.val same)).2,
      fun argument => by
        obtain ⟨body, same⟩ :=
          (matchesParameterRepresentation_abstractionNamed_iff binder bodyName _ argument.1).mp argument.2.1
        have typed := same ▸ argument.2.2.1
        cases typed with
        | lambda bodyTyped =>
            exact ⟨⟨body, bodyTyped, by simpa only [same, isObjectPattern] using argument.2.2.2⟩, Subtype.ext same.symm⟩⟩

/-- The actual source binder argument is equivalent to a contextual point
of native Π; arbitrary closed-term functions are not identified with syntax. -/
noncomputable def bindingArgumentEquiv
    (fragment : ∀ declaration ∈ language.terms, Mettapedia.GSLT.Poly.BindingLanguage.BinderRule declaration)
    (labels : (language.terms.map (·.label)).Nodup)
    (context : List String) (binder : Option String) (bodyName : String)
    (domain codomain : Fin language.types.length) :
    (meaning (.function (.sort domain) (.sort codomain))).obj
        (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context)) ≃
      BindingArgument language context binder bodyName language.types[domain.val].name
        language.types[codomain.val].name :=
  (functionBodyEquiv fragment labels context domain codomain).trans
    (openedArgumentEquiv context binder bodyName _ _)

end Mettapedia.OSLF.NativeTypes.Generation.BindingCarrierSemantics
