import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeConstructorModel
import Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingOperations

/-!
# Native primitive evaluation and original constructor readouts

Evaluation of each installed primitive recovers the genuine native section
constructed from the original authored operation. The natural carrier
comparison reads that section back as the operation on its complete ordered
contextual arguments. Result-sort transport follows the checked original
header, and the original declaration index is retained.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf BindingFunctionArgumentComparison
open BindingSemanticAdmission Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.NativeDependent
open ContextualTypeOperations ContextualModelTelescopes
open Mettapedia.GSLT.LanguageDef.MultiSortedClone

variable {language : LanguageDef}

set_option backward.isDefEq.respectTransparency false in
theorem constructor_primitive_read (installed : NativeSignature.Installation language)
    (admitted : Admitted language) (constructor : installed.Constructor) :
    (constructorModel installed admitted).evaluateTerm
      ((constructorModel installed admitted).termParameters constructor)
      (.primitive constructor Refinement.TermExpr.var) =
      some (⟨(constructorModel installed admitted).termType constructor,
        (constructorModel installed admitted).termValue constructor⟩ :
        Refinement.NativeValue ((constructorModel installed admitted).termParameters constructor).1) := by
  let model := constructorModel installed admitted
  have evaluated := model.evaluate_primitive (model.termParameters constructor) constructor
    Refinement.TermExpr.var (𝟙 (model.termParameters constructor).1) (fun index => by
      change some ((model.termParameters constructor).2.lookup index) = _
      rw [Refinement.ScopeData.components]
      exact congrArg some (Value.substitute_identity
        (K := (Refinement.NativeModel (Worlds language)).toCwf)
        ((model.termParameters constructor).2.lookup index)).symm)
  exact evaluated.trans (congrArg some (Value.substitute_identity
    (⟨model.termType constructor, model.termValue constructor⟩ :
      Refinement.NativeValue (model.termParameters constructor).1)))

theorem constructor_section_readout (installed : NativeSignature.Installation language)
    (admitted : Admitted language) (constructor : installed.Constructor) :
    carrierSectionEquiv (carrierScope installed.headers[constructor].parameters).1
      (.sort installed.headers[constructor].result)
      ((constructorModel installed admitted).termValue constructor) =
      constructorMap admitted installed.headers[constructor]
        (installed_header_correct installed constructor) :=
  (carrierSectionEquiv _ _).apply_symm_apply _

noncomputable def constructorResultIso (header : NativeSignature.Header language)
    (correct : NativeSignature.HeaderCorrect header) :
    programs (algebra language) language.terms[header.origin.val].category ≅
      meaning (.sort header.result) :=
  eqToIso (congrArg (programs (algebra language)) correct.2.symm)

noncomputable def constructorTermReadout (admitted : Admitted language)
    (header : NativeSignature.Header language) (correct : NativeSignature.HeaderCorrect header)
    (context : List String) (arguments : (carrierScope header.parameters).1.obj
      (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context))) :
    Term (signature language) context language.terms[header.origin.val].category :=
  ((programsIso (algebra language) language.terms[header.origin.val].category).hom.app
    (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context)))
    (((constructorResultIso header correct).inv.app (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context)))
      (((carrierSectionEquiv (carrierScope header.parameters).1 (.sort header.result))
        (constructorSection admitted header correct)).app (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context)) arguments))

set_option backward.isDefEq.respectTransparency false in
theorem constructor_term_readout (admitted : Admitted language)
    (header : NativeSignature.Header language) (correct : NativeSignature.HeaderCorrect header)
    (context : List String) (arguments : (carrierScope header.parameters).1.obj
      (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context))) :
    constructorTermReadout admitted header correct context arguments =
      applyFunctionArgs (algebra language) (originalOperator admitted header.origin)
        (((constructorArgumentsIso admitted header correct).hom.app
          (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context))) arguments) := by
  simp only [constructorTermReadout, constructorSection,
    Equiv.apply_symm_apply, constructorMap]
  change (((programsIso (algebra language) language.terms[header.origin.val].category).hom.app _)
    (((constructorResultIso header correct).inv.app _)
      (((constructorResultIso header correct).hom.app _)
        (((programsIso (algebra language) language.terms[header.origin.val].category).inv.app _)
          (((functionOperation (algebra language) (originalOperator admitted header.origin)).app _)
            (((constructorArgumentsIso admitted header correct).hom.app _) arguments)))))) = _
  let X := Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context)
  let value := ((functionOperation (algebra language) (originalOperator admitted header.origin)).app X)
    (((constructorArgumentsIso admitted header correct).hom.app X) arguments)
  have resultCancel : ((constructorResultIso header correct).inv.app X)
      (((constructorResultIso header correct).hom.app X)
        (((programsIso (algebra language) language.terms[header.origin.val].category).inv.app X) value)) =
      ((programsIso (algebra language) language.terms[header.origin.val].category).inv.app X) value := by
    change ((constructorResultIso header correct).hom ≫
      (constructorResultIso header correct).inv).app X _ = _
    rw [Iso.hom_inv_id]
    rfl
  have programCancel : ((programsIso (algebra language) language.terms[header.origin.val].category).hom.app X)
      (((programsIso (algebra language) language.terms[header.origin.val].category).inv.app X) value) = value := by
    change ((programsIso (algebra language) language.terms[header.origin.val].category).inv ≫
      (programsIso (algebra language) language.terms[header.origin.val].category).hom).app X _ = _
    rw [Iso.inv_hom_id]
    rfl
  exact (congrArg (fun element =>
    ((programsIso (algebra language) language.terms[header.origin.val].category).hom.app X) element)
    resultCancel).trans (programCancel.trans
      (functionOperation_body (algebra language) (originalOperator admitted header.origin) _ _))

/-- The readout retains the original constructor and every argument body;
function arguments are converted through their earned complete-context
comparison rather than sampled on selected inputs. -/
theorem constructor_source_readout (admitted : Admitted language)
    (header : NativeSignature.Header language) (correct : NativeSignature.HeaderCorrect header)
    (context : List String) (arguments : (carrierScope header.parameters).1.obj
      (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context))) :
    toPattern (constructorTermReadout admitted header correct context arguments) =
      .apply language.terms[header.origin.val].label
        (toPatterns language.terms[header.origin.val].params
          (FreeBindingTerms.terms.familyToSyntax _
            (fromFunctions (algebra language)
              (((constructorArgumentsIso admitted header correct).hom.app
                (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context)))
                arguments)))) := by
  rw [constructor_term_readout]
  rfl

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
