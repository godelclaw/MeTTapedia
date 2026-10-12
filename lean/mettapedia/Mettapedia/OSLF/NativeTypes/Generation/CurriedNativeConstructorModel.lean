import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModelArguments
import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarations

/-!
# Original authored constructors in the actual native dependent model

The independently constructed binding clone interprets each original
constructor on its complete ordered contextual arguments. Native telescope
comprehension and the earned carrier comparison construct genuine sections
for those operations. Raw header agreement is then proved by the existing
native evaluator; it is not an assumed whole-language model field.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf BindingFunctionArgumentComparison
open BindingSemanticAdmission
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.NativeDependent
open NativeLocalTypeFormers ContextualLocalUniverses

variable {language : LanguageDef}

theorem header_correct_member {origins : List (Fin language.terms.length)}
    {headers : List (NativeSignature.Header language)}
    (matched : List.Forall₂ (fun origin header =>
      header.origin = origin ∧ NativeSignature.HeaderCorrect header) origins headers) :
    ∀ header ∈ headers, NativeSignature.HeaderCorrect header := by
  induction matched with
  | nil => intro header member; cases member
  | cons head tail ih =>
      intro header member
      rcases List.mem_cons.mp member with equal | member
      · subst header; exact head.2
      · exact ih header member

theorem installed_header_correct (installed : NativeSignature.Installation language)
    (constructor : installed.Constructor) :
    NativeSignature.HeaderCorrect installed.headers[constructor] :=
  header_correct_member installed.constructor_correspondence _
    (List.getElem_mem constructor.isLt)

noncomputable def constructorMap (admitted : Admitted language)
    (header : NativeSignature.Header language) (correct : NativeSignature.HeaderCorrect header) :
    (carrierScope header.parameters).1 ⟶ meaning (.sort header.result) :=
  (constructorArgumentsIso admitted header correct).hom ≫
    functionOperation (algebra language) (originalOperator admitted header.origin) ≫
    (programsIso (algebra language) language.terms[header.origin.val].category).inv ≫
    (eqToIso (congrArg (programs (algebra language)) correct.2.symm)).hom

noncomputable def constructorSection (admitted : Admitted language)
    (header : NativeSignature.Header language) (correct : NativeSignature.HeaderCorrect header) :
    (carrierNativeType (carrierScope header.parameters).1 (.sort header.result)).decoded.sections :=
  (carrierSectionEquiv (carrierScope header.parameters).1 (.sort header.result)).symm
    (constructorMap admitted header correct)

/-- All primitive sections come from the original binding operations; type
families are the actual independently typed source representables. -/
noncomputable def constructorModel (installed : NativeSignature.Installation language)
    (admitted : Admitted language) : Refinement.ModelData installed.symbols (Worlds language) where
  typeParameters := fun _ => emptyNativeScope language
  typeFamily := sortNativeType
  termParameters := fun constructor => carrierScope installed.headers[constructor].parameters
  termType := fun constructor => carrierNativeType
    (carrierScope installed.headers[constructor].parameters).1
    (.sort installed.headers[constructor].result)
  termValue := fun constructor => constructorSection admitted installed.headers[constructor]
    (installed_header_correct installed constructor)
  predicateParameters := fun symbol => nomatch symbol
  predicateValue := fun symbol => nomatch symbol

theorem constructorModel_carrier_read (installed : NativeSignature.Installation language)
    (admitted : Admitted language) {n : Nat} (scope : Refinement.Scope (Worlds language) n)
    (carrier : NativeSignature.Carrier language) :
    (constructorModel installed admitted).evaluateType scope carrier.native =
      some (carrierNativeType scope.1 carrier) := by
  induction carrier generalizing n with
  | sort position =>
      exact (constructorModel installed admitted).evaluate_family scope position Fin.elim0
        ((Refinement.NativeModel (Worlds language)).toEmpty scope.1)
        (fun index => Fin.elim0 index)
  | function domain body domainIH bodyIH =>
      exact (constructorModel installed admitted).evaluate_pi scope domain.native body.native
        (carrierNativeType scope.1 domain)
        (carrierNativeType (scope.snoc (carrierNativeType scope.1 domain)).1 body)
        (domainIH scope) (bodyIH (scope.snoc (carrierNativeType scope.1 domain)))

theorem constructorModel_telescope_read (installed : NativeSignature.Installation language)
    (admitted : Admitted language) (parameters : List (NativeSignature.Carrier language)) :
    (constructorModel installed admitted).evaluateContext (NativeSignature.telescope parameters) =
      some (carrierScope parameters) := by
  induction parameters with
  | nil => rfl
  | cons parameter parameters ih =>
      exact (constructorModel installed admitted).evaluateContext_snoc
        (NativeSignature.telescope parameters) parameter.native (carrierScope parameters)
        (carrierNativeType (carrierScope parameters).1 parameter) ih
        (constructorModel_carrier_read installed admitted (carrierScope parameters) parameter)

/-- The existing evaluator validates every generated original declaration's
actual mixed parameter context and result family. -/
theorem constructorModel_realization (installed : NativeSignature.Installation language)
    (admitted : Admitted language) :
    Refinement.SignatureRealization (constructorModel installed admitted) installed.signature where
  typeHeader := fun _ => rfl
  termHeader := fun constructor => constructorModel_telescope_read installed admitted _
  predicateHeader := fun symbol => nomatch symbol
  termResult := fun constructor => constructorModel_carrier_read installed admitted
    (carrierScope installed.headers[constructor].parameters)
    (.sort installed.headers[constructor].result)

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
