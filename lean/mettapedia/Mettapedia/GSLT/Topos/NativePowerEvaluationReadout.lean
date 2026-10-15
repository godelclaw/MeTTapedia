import Mettapedia.GSLT.Topos.NativePowerApplicationComparison
import Mettapedia.GSLT.Topos.NativePowerContextComparison

/-!
# Predicate application retains local power evaluation

A function section is read through its complete local function object.
The evaluation body is the existing dependent-product counit, and its
truth readout is exactly membership in that local predicate. This compares
independently constructed evaluators, including every generalized argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.Topos.NativePowerEvaluationReadout

open _root_.CategoryTheory Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafParameterFamilies DisplayedPresheafPi DisplayedPresheafSlicePi
open NativePowerPiComparison NativePowerPredicates
open PresheafPredicateGenericTruth PresheafNativePropositionReadout

universe u
variable {C : Type u} [Category.{u} C]
variable (P A : Cᵒᵖ ⥤ Type u)

noncomputable def predicateName
    (function : (dependent P A (omegaFunctor (C := C))).sections) : P ⟶ power A :=
  parameterName ((Functor.sectionsFunctor P.Elements).map
    (fromDependent P A (omegaFunctor (C := C))) function)

def argument : totalSpace (domain P A) ⟶ A where
  app _ := TypeCat.ofHom fun value => value.2
  naturality := by intros; rfl

def evaluationOfName (name : P ⟶ power A) :
    totalSpace (domain P A) ⟶ product A where
  app world := TypeCat.ofHom fun value => (value.2, name.app world value.1)
  naturality := by
    intro world future arrow
    apply ConcreteCategory.hom_ext
    intro value
    change (A.map arrow value.2, name.app future (P.map arrow value.1)) =
      (A.map arrow value.2, (power A).map arrow (name.app world value.1))
    exact Prod.ext rfl (name.naturality_apply arrow value.1)

noncomputable def evaluation
    (function : (dependent P A (omegaFunctor (C := C))).sections) :
    totalSpace (domain P A) ⟶ product A :=
  evaluationOfName P A (predicateName P A function)

theorem evaluation_body
    (function : (dependent P A (omegaFunctor (C := C))).sections) :
    evaluation P A function ≫ ConstructivePresheaf.evaluate A (omegaFunctor (C := C)) =
      parameterName ((piSectionEquiv (domain P A) (codomain P A
        (omegaFunctor (C := C)))).symm function) := by
  ext world value
  have evaluated := ConcreteCategory.congr_hom
    (NatTrans.congr_app (fromDependent_evaluation P A (omegaFunctor (C := C)))
      (show (totalSpace (domain P A)).Elements from ⟨world, value⟩))
    (function.val ⟨world, value.1⟩)
  change ((fromDependent P A (omegaFunctor (C := C))).app ⟨world, value.1⟩
      (function.val ⟨world, value.1⟩)).app world (𝟙 world) value.2 = _ at evaluated
  exact evaluated

/-- The actual dependent evaluation body has the same truth readout as
membership in the independently represented local power predicate. -/
theorem evaluation_membership
    (function : (dependent P A (omegaFunctor (C := C))).sections) :
    (membership A).preimage (evaluation P A function) =
      (truthPredicate C).preimage
        (parameterName ((piSectionEquiv (domain P A) (codomain P A
          (omegaFunctor (C := C)))).symm function)) := by
  rw [membership, ← Subfunctor.preimage_comp, evaluation_body]

end Mettapedia.GSLT.Topos.NativePowerEvaluationReadout
