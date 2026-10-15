import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryRepresentableConservativity
import Mettapedia.GSLT.Topos.YonedaPredicateReadout
import Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence

/-!
# Structural comparisons of the original theory's generated interpretation

The complete original-arrow readout is naturally isomorphic to Yoneda.
Actual finite-limit and canonical closed comparisons follow through that
isomorphism. Products and function objects are compared by isomorphisms;
no equality of independently chosen native type codes is postulated.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryRepresentables

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits (PreservesLimits preservesLimits_of_natIso)
open MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open RepresentableIndexedDeclarations
open TheoryEquations

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

def interpretedOriginal : C ⥤ Cᵒᵖ ⥤ Type u where
  obj object := (objectScope object).1
  map arrow := quotientReadout (originalFunctor.map arrow)
  map_id object := by rw [original_readout]; exact RepresentableDeclarations.originalPresheafArrow_identity object
  map_comp earlier later := by
    rw [original_readout, original_readout, original_readout]
    exact RepresentableDeclarations.originalPresheafArrow_composition earlier later

def originalYonedaComparison : interpretedOriginal (C := C) ≅ yoneda :=
  NatIso.ofComponents RepresentableDeclarations.objectScopeIso (by
    intro source target arrow
    change quotientReadout (originalFunctor.map arrow) ≫ objectName target =
      objectName source ≫ yoneda.map arrow
    rw [original_readout]
    change RepresentableDeclarations.originalPresheafArrow arrow ≫ objectName target = _
    rw [RepresentableDeclarations.originalPresheafArrow_name]
    have cancellation : objectNameInverse target ≫ objectName target = 𝟙 (yoneda.obj target) :=
      (RepresentableDeclarations.objectScopeIso target).inv_hom_id
    change objectName source ≫ yoneda.map arrow ≫ objectNameInverse target ≫ objectName target = _
    rw [cancellation, Category.comp_id])

instance interpretedOriginal_preservesLimits : PreservesLimits (interpretedOriginal (C := C)) :=
  preservesLimits_of_natIso originalYonedaComparison.symm

instance interpretedOriginal_faithful : (interpretedOriginal (C := C)).Faithful :=
  Functor.Faithful.of_iso originalYonedaComparison.symm

instance interpretedOriginal_full : (interpretedOriginal (C := C)).Full :=
  Functor.Full.of_iso originalYonedaComparison.symm

variable [CartesianMonoidalCategory C] [MonoidalClosed C]

instance interpretedOriginal_closed : MonoidalClosedFunctor (interpretedOriginal (C := C)) :=
  Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_of_naturalIso originalYonedaComparison

def productComparison (first second : C) :
    interpretedOriginal.obj (first ⊗ second) ≅ interpretedOriginal.obj first ⊗ interpretedOriginal.obj second :=
  asIso (prodComparison interpretedOriginal first second)

omit [MonoidalClosed C] in
theorem product_projection_first (first second : C) :
    (productComparison first second).hom ≫ fst _ _ = interpretedOriginal.map (fst first second) :=
  prodComparison_fst interpretedOriginal first second

omit [MonoidalClosed C] in
theorem product_projection_second (first second : C) :
    (productComparison first second).hom ≫ snd _ _ = interpretedOriginal.map (snd first second) :=
  prodComparison_snd interpretedOriginal first second

def functionComparison (argument result : C) :
    interpretedOriginal.obj ((ihom argument).obj result) ≅
      (ihom (interpretedOriginal.obj argument)).obj (interpretedOriginal.obj result) :=
  asIso ((expComparison interpretedOriginal argument).natTrans.app result)

theorem function_evaluation (argument result : C) :
    interpretedOriginal.obj argument ◁ (functionComparison argument result).hom ≫
        (ihom.ev (interpretedOriginal.obj argument)).app (interpretedOriginal.obj result) =
      inv (prodComparison interpretedOriginal argument ((ihom argument).obj result)) ≫
        interpretedOriginal.map ((ihom.ev argument).app result) :=
  expComparison_ev interpretedOriginal argument result

/-- The contravariant input comparison is part of the complete function
square; current-value agreement alone does not determine this arrow. -/
theorem function_comparison_calibration (argument result : C) :
    (functionComparison argument result).hom ≫
        (pre (originalYonedaComparison.inv.app argument)).app (interpretedOriginal.obj result) ≫
        (ihom (yoneda.obj argument)).map (originalYonedaComparison.hom.app result) =
      originalYonedaComparison.hom.app ((ihom argument).obj result) ≫
        (Mettapedia.GSLT.Topos.YonedaClosed.exponentialIso argument result).hom :=
  Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.exponential_naturalIso
    originalYonedaComparison argument result

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryRepresentables
