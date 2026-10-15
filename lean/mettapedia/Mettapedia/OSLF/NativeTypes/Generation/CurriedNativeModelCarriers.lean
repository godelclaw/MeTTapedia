import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeAdequacy
import Mettapedia.TypeTheory.NativeNondependentFunctionComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementJudgmentInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementConstructorInterpretation

/-!
# Actual native model carriers for authored constructors

Sort families are independently represented by typed source terms in context.
Function parameters use the existing native local dependent product. Its
decoded displayed family is compared naturally to the actual presheaf
function object, including all future contexts and arguments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.NativeDependent
open NativeLocalTypeFormers ContextualLocalUniverses
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafParameterFamilies NativeNondependentFunctionComparison

variable {language : MeTTaIL.Syntax.LanguageDef}

abbrev Worlds (language : MeTTaIL.Syntax.LanguageDef) :=
  ContextObject (algebra language).substitution.toClone

abbrev emptyNativeScope (language : MeTTaIL.Syntax.LanguageDef) :=
  Refinement.Scope.nil (Worlds language)

noncomputable def sortFamily (position : Fin language.types.length) :
    DisplayedFamily (emptyNativeScope language).1 :=
  parameterFamily (emptyNativeScope language).1 (meaning (.sort position))

noncomputable def sortNativeType (position : Fin language.types.length) :
    NativeType (emptyNativeScope language).1 := LocalType.present (sortFamily position)

noncomputable def carrierNativeType (P : Base (algebra language) ⥤ Type) :
    NativeSignature.Carrier language → NativeType P
  | .sort position => (sortNativeType position).reindex
      ((Refinement.NativeModel (Worlds language)).toEmpty P)
  | .function domain body =>
      pi (carrierNativeType P domain)
        (carrierNativeType (totalSpace (carrierNativeType P domain).decoded) body)

noncomputable def carrierDecodedIso (P : Base (algebra language) ⥤ Type) :
    (carrier : NativeSignature.Carrier language) →
      (show DisplayedFamily P from (carrierNativeType P carrier).decoded) ≅
        constantFamily P (meaning carrier)
  | .sort position => by
      exact eqToIso (by
        change reindexDisplayed ((Refinement.NativeModel (Worlds language)).toEmpty P)
          (sortFamily position) = constantFamily P (meaning (.sort position))
        rfl)
  | .function domain body =>
      piFunctionIso (carrierNativeType P domain)
        (carrierNativeType (totalSpace (carrierNativeType P domain).decoded) body)
        (carrierDecodedIso P domain)
        (carrierDecodedIso (totalSpace (carrierNativeType P domain).decoded) body)

/-- A complete native carrier section is exactly a natural source-carrier
map. The function case uses the actual native product interpretation. -/
noncomputable def carrierSectionEquiv (P : Base (algebra language) ⥤ Type)
    (carrier : NativeSignature.Carrier language) :
    (carrierNativeType P carrier).decoded.sections ≃ (P ⟶ meaning carrier) :=
  ((Functor.sectionsFunctor P.Elements).mapIso (carrierDecodedIso P carrier)).toEquiv.trans
    (parameterSectionEquiv P (meaning carrier)).symm

noncomputable def carrierScope : (parameters : List (NativeSignature.Carrier language)) →
    Refinement.Scope (Worlds language) parameters.length
  | [] => emptyNativeScope language
  | parameter :: parameters =>
      (carrierScope parameters).snoc (carrierNativeType (carrierScope parameters).1 parameter)

noncomputable def carrierProduct : List (NativeSignature.Carrier language) →
    Base (algebra language) ⥤ Type
  | [] => 𝟙_ (Base (algebra language) ⥤ Type)
  | parameter :: parameters => meaning parameter ⊗ carrierProduct parameters

/-- The actual native mixed telescope is naturally the ordered product of
its decoded carriers. No argument is discarded by context assembly. -/
noncomputable def carrierScopeProductIso :
    (parameters : List (NativeSignature.Carrier language)) →
      (carrierScope parameters).1 ≅ carrierProduct parameters
  | [] => Iso.refl _
  | parameter :: parameters =>
      totalFamilyIso (carrierDecodedIso (carrierScope parameters).1 parameter) ≪≫
        (tensorLeft (meaning parameter)).mapIso (carrierScopeProductIso parameters)

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
