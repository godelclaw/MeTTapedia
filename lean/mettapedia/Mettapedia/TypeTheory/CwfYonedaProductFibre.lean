import Mettapedia.TypeTheory.CwfYonedaProductSections
import Mettapedia.TypeTheory.CwfYonedaFutureArgumentInitial
import Mettapedia.TypeTheory.RightKanInitialValue

/-!
# Complete native dependent function fibres of an original CwF

Every native function at every original source environment is determined
by its value at the actual generic future argument. Source beta, eta and
substitution turn that complete generic body into an original function.
The two comparisons use the chosen native right-Kan product throughout.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfYoneda

open CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafIndexedCwfBridge
open ContextualProductSections ContextualTypeOperations

universe u w w'
variable (C : Cwf.{u, u, w, w'})

noncomputable section

def representedProductGenericIso {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ) :
    (representedProductFamily C A B).obj ⟨op (context C Δ), σ⟩ ≅
      (family C B).obj
        ⟨op (context C (C.ext Δ (C.tySub A σ))), TypeOver.extensionSubstitution σ A⟩ :=
  RightKanInitialValue.comparison (CategoryOfElements.π (family C A))
    (displayedToTotalElements (family C A) ⋙ dependentBodyFamily C A B)
    ⟨op (context C Δ), σ⟩ (genericArgument C A σ) (genericArgumentInitial C A σ)

def sourceFunctionGenericEquiv (products : StableProducts C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ) :
    (family C (products.operations.pi A B)).obj ⟨op (context C Δ), σ⟩ ≃
      (family C B).obj
        ⟨op (context C (C.ext Δ (C.tySub A σ))), TypeOver.extensionSubstitution σ A⟩ :=
  (termFibreEquiv C (products.operations.pi A B) σ).symm.trans
    ((Equiv.cast (congrArg (C.Tm Δ) (products.substitution.1 σ A B))).trans
      ((bodyEquiv products (C.tySub A σ)
        (C.tySub B (TypeOver.extensionSubstitution σ A))).trans
          (termFibreEquiv C B (TypeOver.extensionSubstitution σ A))))

/-- Whole native function fibres and original source function fibres are
in bijection at every environment, through the complete generic body. -/
def productFibreEquiv (products : StableProducts C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (σ : C.Sub Δ Γ) :
    (family C (products.operations.pi A B)).obj ⟨op (context C Δ), σ⟩ ≃
      (representedProductFamily C A B).obj ⟨op (context C Δ), σ⟩ :=
  (sourceFunctionGenericEquiv C products A B σ).trans
    (representedProductGenericIso C A B σ).toEquiv.symm

end

end Mettapedia.TypeTheory.CwfYoneda
