import Mettapedia.TypeTheory.CwfYonedaProductFamilyComparison
import Mettapedia.TypeTheory.DisplayedPresheafPiSectionEvaluation

/-!
# The whole-family comparison preserves dependent function sections

The natural comparison obtained from original evaluation sends every source
function section to its independently constructed native abstraction.
Generic-future evaluation proves the comparison at every environment, not
only at a chosen present argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.CwfYoneda

open CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualProductSections DisplayedPresheafPi
open DisplayedPresheafIndexedCwfBridge CategoryIndexedFamilyGeneralPi

universe u w w'
variable (C : Cwf.{u, u, w, w'})

noncomputable section

theorem representedProductGenericIso_section {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ)
    (function : (representedProductFamily C A B).sections) :
    (representedProductGenericIso C A B σ).hom
        (function.val ⟨op (context C Δ), σ⟩) =
      ((piSectionEquiv (family C A) (dependentBodyFamily C A B)).symm function).val
        ((displayedToTotalElements (family C A)).obj (genericArgument C A σ).right) := by
  have read := RightKanInitialValue.comparison_evaluation
    (CategoryOfElements.π (family C A)) (indexedBodyFamily C A B)
    (⟨op (context C Δ), σ⟩ : (contextFace C Γ).Elements)
    (genericArgument C A σ) (genericArgumentInitial C A σ)
  have evaluated := ConcreteCategory.congr_hom read (function.val ⟨op (context C Δ), σ⟩)
  change (representedProductGenericIso C A B σ).hom
      (function.val ⟨op (context C Δ), σ⟩) =
    (generalPiEvaluation (context := Cat.of (contextFace C Γ).Elements)
      (family C A) (indexedBodyFamily C A B)).app (genericArgument C A σ).right
      ((representedProductFamily C A B).map (genericArgument C A σ).hom
        (function.val ⟨op (context C Δ), σ⟩)) at evaluated
  rw [function.property (genericArgument C A σ).hom] at evaluated
  exact evaluated.trans (inverse_indexed_value (family C A)
    (dependentBodyFamily C A B) function (genericArgument C A σ).right).symm

theorem sourceFunctionGenericEquiv_section (products : StableProducts C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ)
    (function : C.Tm Γ (products.operations.pi A B)) :
    sourceFunctionGenericEquiv C products A B σ
        ((interpretTerm C function).val ⟨op (context C Δ), σ⟩) =
      (bodyTermSectionEquiv C A B
        (ContextualPiEta.genericSection products.operations products.substitution.1 function)).val
        ((displayedToTotalElements (family C A)).obj (genericArgument C A σ).right) := by
  change encodeTerm C B (TypeOver.extensionSubstitution σ A)
      (ContextualPiEta.genericSection products.operations products.substitution.1
        (cast (congrArg (C.Tm Δ) (products.substitution.1 σ A B))
          (decodeTerm C (products.operations.pi A B) σ
            (encodeTerm C (products.operations.pi A B) σ (C.tmSub function σ))))) =
    encodeTerm C B (TypeOver.extensionSubstitution σ A)
      (C.tmSub (ContextualPiEta.genericSection products.operations products.substitution.1 function)
        (TypeOver.extensionSubstitution σ A))
  rw [decode_encode]
  exact congrArg (encodeTerm C B (TypeOver.extensionSubstitution σ A))
    (genericSection_reindex products σ function)

theorem productFamilyForward_section (products : StableProducts C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (function : C.Tm Γ (products.operations.pi A B)) :
    (Functor.sectionsFunctor _).map (productFamilyForward C products A B)
        (interpretTerm C function) = interpretFunction C products function := by
  apply (Functor.sections_ext_iff).2
  intro point
  apply (representedProductGenericIso C A B point.2).toEquiv.injective
  change (representedProductGenericIso C A B point.2).hom
      ((productFamilyForward C products A B).app point ((interpretTerm C function).val point)) =
    (representedProductGenericIso C A B point.2).hom
      ((interpretFunction C products function).val point)
  have right := representedProductGenericIso_section C A B point.2
    (interpretFunction C products function)
  rw [interpretFunction_body] at right
  exact (productFamilyForward_generic C products A B point.2
    ((interpretTerm C function).val point)).trans
      ((sourceFunctionGenericEquiv_section C products A B point.2 function).trans right.symm)

theorem productFamilyIso_section (products : StableProducts C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (function : C.Tm Γ (products.operations.pi A B)) :
    (Functor.sectionsFunctor _).map (productFamilyIso C products A B).hom
        (interpretTerm C function) = interpretFunction C products function := by
  rw [productFamilyIso_hom]
  exact productFamilyForward_section C products A B function

theorem productFamilyIso_abstraction (products : StableProducts C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (body : C.Tm (C.ext Γ A) B) :
    (Functor.sectionsFunctor _).map (productFamilyIso C products A B).hom
        (interpretTerm C (products.operations.lam body)) =
      lamDisplayed (representedBodySection C (A := A) (interpretTerm C body)) := by
  rw [productFamilyIso_section, interpretFunction_lam]

end

end Mettapedia.TypeTheory.CwfYoneda
