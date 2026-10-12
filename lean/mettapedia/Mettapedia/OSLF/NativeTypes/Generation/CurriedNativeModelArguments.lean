import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModelCarriers
import Mettapedia.OSLF.Syntax.BindingFunctionArgumentProducts

/-!
# Generated native telescopes and original constructor argument families

The mechanically decoded native carrier list is compared with every actual
authored parameter, in order. Native context comprehension and genuine
curried function meanings then yield the original whole-context argument
family, naturally under ambient substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open BindingFunctionArgumentComparison BindingSemanticAdmission

variable {language : LanguageDef}

theorem parameterSlotMeaning {parameter : TermParam}
    (admitted : ∃ scope result, ParameterMeaning parameter scope result) :
    ParameterMeaning parameter (slot parameter).1 (slot parameter).2 := by
  obtain ⟨scope, result, meaning⟩ := admitted
  simpa only [slot_meaning meaning] using meaning

noncomputable def parameterSlotIso {parameter : TermParam}
    (admitted : ∃ scope result, ParameterMeaning parameter scope result)
    (carrier : NativeSignature.Carrier language)
    (represented : parameterType? parameter = some carrier.source) :
    meaning carrier ≅ (binders (algebra language) (slot parameter).1).functorHom
      (programs (algebra language) (slot parameter).2) :=
  nativeParameterFunctionSourceIso (parameterSlotMeaning admitted) carrier represented

noncomputable def carrierArgumentsIso (parameters : List TermParam)
    (carriers : List (NativeSignature.Carrier language))
    (admitted : ∀ parameter ∈ parameters,
      ∃ scope result, ParameterMeaning parameter scope result)
    (represented : List.Forall₂ (fun parameter carrier =>
      parameterType? parameter = some carrier.source) parameters carriers) :
    carrierProduct carriers ≅ functionArguments (algebra language) (slots parameters) := by
  induction parameters generalizing carriers with
  | nil =>
      cases carriers with
      | nil => exact (nilIso (algebra language)).symm
      | cons carrier carriers => cases represented.length_eq
  | cons parameter parameters ih =>
      cases carriers with
      | nil => cases represented.length_eq
      | cons carrier carriers =>
          have info := List.forall₂_cons.mp represented
          let headIso := parameterSlotIso (admitted parameter List.mem_cons_self)
            carrier info.1
          let tailIso := ih carriers (fun next member =>
            admitted next (List.mem_cons_of_mem _ member)) info.2
          exact tensorIso headIso tailIso ≪≫
            (consIso (algebra language) (slot parameter).1 (slot parameter).2
              (slots parameters)).symm

noncomputable def constructorArgumentsIso (admitted : Admitted language)
    (header : NativeSignature.Header language) (correct : NativeSignature.HeaderCorrect header) :
    (carrierScope header.parameters).1 ≅
      functionArguments (algebra language)
        ((signature language).arity (originalOperator admitted header.origin)) :=
  carrierScopeProductIso header.parameters ≪≫
    carrierArgumentsIso language.terms[header.origin.val].params header.parameters
      (admitted _ (List.getElem_mem header.origin.isLt)) correct.1

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
