import Mettapedia.TypeTheory.CwfYonedaProductGenericEvaluation

/-!
# Natural comparison of original and native dependent products

The original evaluator's natural transpose is invertible on every full
function fibre. Generic-argument initiality and source beta/eta earn that
invertibility. The resulting comparison is natural on whole families;
it does not replace the chosen native product by a source-defined family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.CwfYoneda

open CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualProductSections CategoryIndexedFamilyGeneralPi
open DisplayedPresheafIndexedCwfBridge

universe u w w'
variable (C : Cwf.{u, u, w, w'})

noncomputable section

theorem productFamilyForward_generic (products : StableProducts C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ)
    (function : (family C (products.operations.pi A B)).obj ⟨op (context C Δ), σ⟩) :
    (representedProductGenericIso C A B σ).hom
        ((productFamilyForward C products A B).app ⟨op (context C Δ), σ⟩ function) =
      sourceFunctionGenericEquiv C products A B σ function := by
  have generic := RightKanInitialValue.comparison_evaluation
    (CategoryOfElements.π (family C A)) (indexedBodyFamily C A B)
    (⟨op (context C Δ), σ⟩ : (contextFace C Γ).Elements)
    (genericArgument C A σ) (genericArgumentInitial C A σ)
  have reading := ConcreteCategory.congr_hom generic
    ((productFamilyForward C products A B).app ⟨op (context C Δ), σ⟩ function)
  have natural := (productFamilyForward C products A B).naturality_apply
    (genericArgument C A σ).hom function
  have evaluated := ConcreteCategory.congr_hom
    (NatTrans.congr_app (productFamilyForward_evaluation C products A B)
      (genericArgument C A σ).right)
    ((family C (products.operations.pi A B)).map (genericArgument C A σ).hom function)
  change (representedProductGenericIso C A B σ).hom
      ((productFamilyForward C products A B).app ⟨op (context C Δ), σ⟩ function) =
    (generalPiEvaluation (context := Cat.of (contextFace C Γ).Elements)
      (family C A) (indexedBodyFamily C A B)).app (genericArgument C A σ).right
      ((representedProductFamily C A B).map (genericArgument C A σ).hom
        ((productFamilyForward C products A B).app ⟨op (context C Δ), σ⟩ function)) at reading
  rw [← natural] at reading
  exact reading.trans (evaluated.trans (sourceEvaluationBody_generic C products A B σ function))

/-- The independently earned whole-fibre inverse is the actual natural
transpose of source evaluation. -/
theorem productFamilyForward_fibre (products : StableProducts C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ)
    (function : (family C (products.operations.pi A B)).obj ⟨op (context C Δ), σ⟩) :
    (productFamilyForward C products A B).app ⟨op (context C Δ), σ⟩ function =
      productFibreEquiv C products A B σ function := by
  apply (representedProductGenericIso C A B σ).toEquiv.injective
  change (representedProductGenericIso C A B σ).hom
      ((productFamilyForward C products A B).app ⟨op (context C Δ), σ⟩ function) =
    (representedProductGenericIso C A B σ).hom (productFibreEquiv C products A B σ function)
  rw [productFamilyForward_generic]
  exact ((representedProductGenericIso C A B σ).toEquiv.apply_symm_apply _).symm

/-- The entire original source product family is naturally isomorphic to
the already chosen native right-Kan product, including every future map. -/
def productFamilyIso (products : StableProducts C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    family C (products.operations.pi A B) ≅ representedProductFamily C A B :=
  NatIso.ofComponents
    (fun point => (productFibreEquiv C products A B point.2).toIso)
    (by
      intro first second before
      apply ConcreteCategory.hom_ext
      intro function
      change productFibreEquiv C products A B second.2
        ((family C (products.operations.pi A B)).map before function) =
        (representedProductFamily C A B).map before
          (productFibreEquiv C products A B first.2 function)
      rw [← productFamilyForward_fibre, ← productFamilyForward_fibre]
      exact (productFamilyForward C products A B).naturality_apply before function)

theorem productFamilyIso_hom (products : StableProducts C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    (productFamilyIso C products A B).hom = productFamilyForward C products A B := by
  ext point function
  exact (productFamilyForward_fibre C products A B point.2 function).symm

end

end Mettapedia.TypeTheory.CwfYoneda
