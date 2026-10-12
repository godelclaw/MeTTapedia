import Mettapedia.TypeTheory.DisplayedPresheafPi

/-!
# Whole function sections and indexed evaluation

The inverse of the actual displayed abstraction equivalence agrees with
the chosen right-Kan evaluation after regrouping total elements. This joins
the complete section operations to the same evaluator used on function
fibres; no equality of separately selected adjunctions is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafPi

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafIndexedCwfBridge CategoryIndexedFamilyGeneralPi

universe u
variable {C : Type u} [Category.{u} C] {P : Face.{u, u, u} C}

set_option backward.isDefEq.respectTransparency false in
theorem inverse_asIndexed (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A))
    (function : (piDisplayed A B).sections) :
    Functor.whiskerLeft (displayedToTotalElements A)
        (B.sectionsEquivHom PUnit ((piSectionEquiv A B).symm function)) =
      Functor.whiskerLeft (CategoryOfElements.π A)
          ((piDisplayed A B).sectionsEquivHom PUnit function) ≫
        generalPiEvaluation (context := Cat.of P.Elements) A
          (displayedToTotalElements A ⋙ B) := by
  have transposed := lamDisplayed_asIndexed ((piSectionEquiv A B).symm function)
  rw [pi_eta] at transposed
  rw [transposed]
  exact (generalPi_beta (context := Cat.of P.Elements) A
    (source := (Functor.const P.Elements).obj PUnit)
    (codomain := displayedToTotalElements A ⋙ B)
    (Functor.whiskerLeft (displayedToTotalElements A)
      (B.sectionsEquivHom PUnit ((piSectionEquiv A B).symm function)))).symm

theorem inverse_indexed_value (A : DisplayedFamily.{u, u, u, u} P)
    (B : DisplayedFamily.{u, u, u, u} (totalSpace A))
    (function : (piDisplayed A B).sections) (point : A.Elements) :
    ((piSectionEquiv A B).symm function).val ((displayedToTotalElements A).obj point) =
      (generalPiEvaluation (context := Cat.of P.Elements) A
          (displayedToTotalElements A ⋙ B)).app point
        (function.val point.1) := by
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (inverse_asIndexed A B function) point) PUnit.unit

end Mettapedia.TypeTheory.DisplayedPresheafPi
