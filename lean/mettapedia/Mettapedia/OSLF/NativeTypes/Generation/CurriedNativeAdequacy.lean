import Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingFunctions
import Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingSourceCoverage

/-!
# Native function meanings for semantically admitted authored parameters

The actual native carrier decoder is connected to independently admitted
binding spines, their genuine presheaf function objects, and the original
source typing judgment. Ordinary higher-order arrow data does not receive
this comparison merely because its native syntax has a formation derivation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open _root_.CategoryTheory
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open BindingSemanticAdmission
open Mettapedia.TypeTheory.Calculi.NativeDependent

variable {language : LanguageDef}

abbrev algebra (language : LanguageDef) := BindingCloneAlgebra.terms (signature language)

noncomputable def meaning : NativeSignature.Carrier language → Base (algebra language) ⥤ Type
  | .sort position => programs (algebra language) language.types[position.val].name
  | .function domain codomain => (meaning domain).functorHom (meaning codomain)

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
  | sort => rfl
  | function domain codomain domainIH codomainIH =>
      simp only [NativeSignature.Carrier.native, nativeMeaning?, domainIH, codomainIH, meaning]
      rfl

theorem meaning_spine (carrier : NativeSignature.Carrier language)
    {domains : List String} {result : String}
    (spine : BinderSpine carrier.source domains result) :
    meaning carrier = curried (algebra language) result domains := by
  induction carrier generalizing domains result with
  | sort position => cases spine; rfl
  | function domain codomain domainIH codomainIH =>
      cases domain with
      | sort position =>
          cases spine with
          | binder domain spine =>
              exact congrArg (fun body => (programs (algebra language)
                language.types[position.val].name).functorHom body) (codomainIH spine)
      | function first last => cases spine

theorem parameter_spine {parameter : TermParam} {scope : List String} {result : String}
    (admitted : ParameterMeaning parameter scope result) (carrier : NativeSignature.Carrier language)
    (represented : parameterType? parameter = some carrier.source) :
    ∃ domains, BinderSpine carrier.source domains result ∧ domains.reverse = scope := by
  cases admitted with
  | data name sort =>
      simp only [parameterType?, Option.some.injEq] at represented
      exact ⟨[], by rw [← represented]; exact .result result, rfl⟩
  | shorthand binder name sort =>
      simp only [parameterType?, Option.some.injEq] at represented
      exact ⟨[result], by rw [← represented]; exact .binder result (.result result), rfl⟩
  | binding binder name domain spine =>
      simp only [parameterType?, Option.some.injEq] at represented
      exact ⟨_, by rw [← represented]; exact .binder domain spine, rfl⟩

/-- The computed carrier meaning is naturally the function object of the
actual ordered source binder scope, at every ambient context. -/
noncomputable def nativeParameterFunctionSourceIso
    {parameter : TermParam} {scope : List String} {result : String}
    (admitted : ParameterMeaning parameter scope result)
    (carrier : NativeSignature.Carrier language)
    (represented : parameterType? parameter = some carrier.source) :
    meaning carrier ≅ (binders (algebra language) scope).functorHom
      (programs (algebra language) result) := by
  let domains := Classical.choose (parameter_spine admitted carrier represented)
  have info := Classical.choose_spec (parameter_spine admitted carrier represented)
  have spine : BinderSpine carrier.source domains result := info.1
  have ordered : domains.reverse = scope := info.2
  exact eqToIso (meaning_spine carrier spine) ≪≫
    curriedBinderIso (algebra language) result domains ≪≫
    eqToIso (congrArg (fun bindersScope =>
      (binders (algebra language) bindersScope).functorHom
        (programs (algebra language) result)) ordered)

noncomputable def nativeParameterFunctionIso
    {parameter : TermParam} {scope : List String} {result : String}
    (admitted : ParameterMeaning parameter scope result)
    (carrier : NativeSignature.Carrier language)
    (decoded : NativeSignature.decodeParameter? language parameter = some carrier) :
    meaning carrier ≅ (binders (algebra language) scope).functorHom
      (programs (algebra language) result) :=
  nativeParameterFunctionSourceIso admitted carrier
    (NativeSignature.decodeParameter?_sound decoded)

theorem nativeParameterFunctionIso_natural
    {parameter : TermParam} {scope : List String} {result : String}
    (admitted : ParameterMeaning parameter scope result)
    (carrier : NativeSignature.Carrier language)
    (decoded : NativeSignature.decodeParameter? language parameter = some carrier)
    {first last : Base (algebra language)} (substitution : first ⟶ last)
    (value : (meaning carrier).obj first) :
    (nativeParameterFunctionIso admitted carrier decoded).hom.app last
        ((meaning carrier).map substitution value) =
      ((binders (algebra language) scope).functorHom
        (programs (algebra language) result)).map substitution
          ((nativeParameterFunctionIso admitted carrier decoded).hom.app first value) :=
  (nativeParameterFunctionIso admitted carrier decoded).hom.naturality_apply substitution value

/-- Installed native function points have exactly the independently typed
source body inhabitants, under their computed ordered binder scope. -/
noncomputable def nativeParameterBodyEquiv (admittedLanguage : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    {parameter : TermParam} {scope : List String} {result : String}
    (admittedParameter : ParameterMeaning parameter scope result)
    (carrier : NativeSignature.Carrier language)
    (decoded : NativeSignature.decodeParameter? language parameter = some carrier)
    (context : List String) :
    (meaning carrier).obj
        (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context)) ≃
      Source language (scope ++ context) result := by
  let domains := Classical.choose (parameter_spine admittedParameter carrier
    (NativeSignature.decodeParameter?_sound decoded))
  have info := Classical.choose_spec (parameter_spine admittedParameter carrier
    (NativeSignature.decodeParameter?_sound decoded))
  have spine : BinderSpine carrier.source domains result := info.1
  have ordered : domains.reverse = scope := info.2
  rw [meaning_spine carrier spine, ← ordered]
  exact (curriedBodyEquiv (algebra language) context result domains).trans
    (sourceEquiv admittedLanguage labels (domains.reverse ++ context) result)

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
