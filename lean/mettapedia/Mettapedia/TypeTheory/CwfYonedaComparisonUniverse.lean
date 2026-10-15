import Mettapedia.TypeTheory.CwfYonedaProductFamilyComparison
import Mettapedia.TypeTheory.ContextualCwfUniverseTypeLift

/-!
# Original dependent models with independent carrier sizes

Only context and substitution carriers are raised to a common level.
The original type and term carriers remain at their independent levels.
The actual source operations and their local laws earn the complete native
sum and product comparisons on those carriers. All original readouts are
retained; the lift adds no internal universe type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfYonedaComparisonUniverse

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualCwfUniverseLift ContextualProductSections ContextualSumComprehension

universe u v w w'

abbrev representedModel (C : Cwf.{u, v, w, w'}) :
    Cwf.{max u v, max u v, w, w'} :=
  lift.{u, v, w, w', max u v, max u v, 0, 0} C

def representedProducts {C : Cwf.{u, v, w, w'}} (products : StableProducts C) :
    StableProducts (representedModel C) where
  operations := liftProducts products.operations
  beta := lifted_products_beta products.operations products.beta
  substitution := lifted_products_substitution products.operations products.substitution
  eta := lifted_products_eta products.operations products.substitution.1 products.eta

def representedSums {C : Cwf.{u, v, w, w'}} (sums : StableSums C) :
    StableSums (representedModel C) := liftStableSums sums

noncomputable def sumComparison {C : Cwf.{u, v, w, w'}}
    (sums : StableSums C) {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    CwfYoneda.family (representedModel C)
        ((representedSums sums).operations.sigma ⟨A⟩ ⟨B⟩) ≅
      CwfYoneda.representedSumFamily (representedModel C) ⟨A⟩ ⟨B⟩ :=
  CwfYoneda.sumFamilyIso (representedModel C) (representedSums sums) ⟨A⟩ ⟨B⟩

noncomputable def productComparison {C : Cwf.{u, v, w, w'}}
    (products : StableProducts C) {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    CwfYoneda.family (representedModel C)
        ((representedProducts products).operations.pi ⟨A⟩ ⟨B⟩) ≅
      CwfYoneda.representedProductFamily (representedModel C) ⟨A⟩ ⟨B⟩ :=
  CwfYoneda.productFamilyIso (representedModel C) (representedProducts products) ⟨A⟩ ⟨B⟩

theorem original_function_body {C : Cwf.{u, v, w, w'}}
    (products : StableProducts C) {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (function : C.Tm Γ (products.operations.pi A B)) :
    (ContextualPiEta.genericSection (representedProducts products).operations
      (representedProducts products).substitution.1 (ULift.up function)).down =
      ContextualPiEta.genericSection products.operations products.substitution.1 function :=
  genericSection_readout products.operations products.substitution.1 (ULift.up function)

theorem original_argument_extension {C : Cwf.{u, v, w, w'}}
    {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : C.Ty Γ) :
    (TypeOver.extensionSubstitution (C := representedModel C) (ULift.up σ) (ULift.up A)).down =
      TypeOver.extensionSubstitution σ A :=
  extensionSubstitution_readout (C := C) (ULift.up σ) (ULift.up A)

theorem original_application {C : Cwf.{u, v, w, w'}}
    (products : StableProducts C) {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (function : C.Tm Γ (products.operations.pi A B)) (argument : C.Tm Γ A) :
    HEq ((representedProducts products).operations.app
      (ULift.up function) (ULift.up argument)).down (products.operations.app function argument) :=
  products_app_readout products.operations (ULift.up function) (ULift.up argument)

theorem original_sum_second {C : Cwf.{u, v, w, w'}}
    (sums : StableSums C) {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (value : C.Tm Γ (sums.operations.sigma A B)) :
    HEq ((representedSums sums).operations.snd (ULift.up value)).down
      (sums.operations.snd value) :=
  sums_snd_readout sums.operations (ULift.up value)

end Mettapedia.TypeTheory.CwfYonedaComparisonUniverse
