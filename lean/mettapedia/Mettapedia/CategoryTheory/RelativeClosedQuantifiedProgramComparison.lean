import Mettapedia.CategoryTheory.RelativeClosedQuantifiedHomEquivalence
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorCellUniqueness

/-!
# The universal comparison agrees with the supplied complete base comparison

Every base object, including independently designated program and event
objects, retains the supplied comparison through the actual extension and
restriction constructions. The equation earns the needed program reading
of the universal map; preservation at the proposition object alone would
not provide it.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantified.ProgramComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory RelativeClosedGeneratedQuantifier Iteration

universe k
variable {source : ConjunctiveClosedTheory.{k}} {target : QuantifiedClosedTheory.{k}}
variable (mapping : ConjunctiveClosedTheory.Map source target.conjunctive)
variable (candidate : QuantifiedClosedTheory.Map (freeObject source) target)
variable (supplied : ConjunctiveClosedTheory.MapIso (Extension.restrictMap candidate) mapping)

set_option backward.isDefEq.respectTransparency false in
theorem complete_base_component (object : source.closed.Obj) :
    (Universal.completeComparison mapping candidate supplied).comparison.hom.app
        ((Extension.unitMap source).functor.obj object) ≫
      (HomEquivalence.extension_restriction source target mapping).comparison.hom.app object =
        supplied.comparison.hom.app object := by
  dsimp only [QuantifiedClosedTheory.conjunctive, freeObject, Closure.theory,
    Mettapedia.GSLT.Core.LambdaTheory.ofCategory] at *
  dsimp only [Universal.completeComparison, HomEquivalence.extension_restriction]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.rightUnitor_inv_app, eqToIso.hom, eqToHom_app]
  change ((Universal.comparison mapping candidate supplied).hom.app
      (baseObject (Closure.signature (stage source)) object) ≫ 𝟙 _) ≫
    eqToHom (Functor.congr_obj (Extension.complete_base_recovered mapping) object) = _
  rw [Category.comp_id, Universal.base_component, Universal.primitive_base_component]
  simp only [eqToHom_refl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem comparison_unique
    (other : candidate.functor ≅ (Extension.extendMap mapping).functor)
    (base : ∀ object : source.closed.Obj,
      other.hom.app ((Extension.unitMap source).functor.obj object) ≫
        (HomEquivalence.extension_restriction source target mapping).comparison.hom.app object =
          supplied.comparison.hom.app object) :
    other = (Universal.completeComparison mapping candidate supplied).comparison := by
  let : PreservesFiniteLimits candidate.functor := candidate.finite
  let : MonoidalClosedFunctor candidate.functor := candidate.closed
  apply Iso.ext
  apply FunctorCellUniqueness.cells_equal_of_generators
    (Universal.completeComparison mapping candidate supplied).comparison other.hom
  · intro object
    apply (cancel_mono
      ((HomEquivalence.extension_restriction source target mapping).comparison.hom.app object)).mp
    exact (base object).trans (complete_base_component mapping candidate supplied object).symm
  · intro origin
    exact origin.down.elim

end Mettapedia.CategoryTheory.RelativeClosedQuantified.ProgramComparison
