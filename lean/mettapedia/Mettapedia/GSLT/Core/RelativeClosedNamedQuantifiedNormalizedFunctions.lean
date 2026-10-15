import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedNormalization

/-!
# Whole function comparisons of the normalized logical map

The complete argument object is retained. The normalized exponential
comparison followed by the fresh proposition reading is precisely the
canonical equality transport to the independently chosen target function
object. Both directions of that comparison are proved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalClosed
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory FunctorNormalization
open ProgramReductionTheory RelativeClosedNamedQuantifiedPresentation
open InternalPredicateFunctionObjectMaps

universe k
variable {source : Theory.{k,k}} {Index Origins : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source}
variable {target : QuantifiedImplicativeProgramTheory.{k}}
variable (data : OriginComparison (source := source) (selected := selected) (constructors := constructors) target)

theorem normalized_function_object (value : (namedTheory source selected constructors).closed.Obj) :
    (normalized data).obj (InternalPredicateFunctionObject.power
        (predicates source selected constructors) value) =
      InternalPredicateFunctionObject.power target.quantified.operations.predicates
        ((normalized data).obj value) :=
  (normalized_exponential_object (atomicFunctor data) value
    (predicates source selected constructors).proposition).trans
    (congrArg (fun proposition : target.quantified.programTheory.closed.Obj =>
      (normalized data).obj value ⟶[target.quantified.programTheory.closed.Obj] proposition)
      (normalized_proposition_object data))

private theorem map_cast {C D : Type k} [Category.{k} C] [Category.{k} D]
    (mapping : C ⥤ D) {before after : C} (same : before = after) :
    mapping.map (eqToHom same) = eqToHom (congrArg mapping.obj same) := by
  cases same
  exact mapping.map_id _

theorem normalized_function_hom (value : (namedTheory source selected constructors).closed.Obj) :
    (powerComparison (normalizedPredicates data) value).hom =
      eqToHom (normalized_function_object data value) := by
  change (expComparison (normalized data) value).natTrans.app
      (predicates source selected constructors).proposition ≫
      (ihom ((normalized data).obj value)).map
        (normalizedPredicates data).proposition.hom = _
  rw [normalized_proposition_hom]
  have first := normalized_expComparison (atomicFunctor data) value
    (predicates source selected constructors).proposition
  have second := map_cast (ihom ((normalized data).obj value))
    (normalized_proposition_object data)
  exact (congrArg₂ (fun before after => before ≫ after) first second).trans
    (eqToHom_trans _ _)

theorem normalized_function_inv (value : (namedTheory source selected constructors).closed.Obj) :
    (powerComparison (normalizedPredicates data) value).inv =
      eqToHom (normalized_function_object data value).symm :=
  congrArg Iso.inv (Iso.ext (normalized_function_hom data value) :
    powerComparison (normalizedPredicates data) value =
      eqToIso (normalized_function_object data value))

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction
