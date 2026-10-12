import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedOriginComparison
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationBase

/-!
# Canonical native choices for a restricted logical interpretation

The supplied proposition comparison normalizes the fresh object to the
independent target carrier. Recursive finite-limit and function comparisons
then normalize the complete generated interpretation. The predicate map
is transported through these two actual natural isomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory FunctorNormalization
open ProgramReductionTheory RelativeClosedNamedQuantifiedPresentation

universe k
variable {source : Theory.{k,k}} {Index Origins : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source}
variable {target : QuantifiedImplicativeProgramTheory.{k}}
variable (data : OriginComparison (source := source) (selected := selected) (constructors := constructors) target)

def normalized := normalizedFunctor (atomicFunctor data)

instance normalized_finite : PreservesFiniteLimits (normalized data) :=
  normalized_preservesFiniteLimits (atomicFunctor data)

instance normalized_closed : MonoidalClosedFunctor (normalized data) :=
  FunctorNormalization.normalized_closed (atomicFunctor data)

def normalizedPredicates : InternalConjunctiveObject.Map (predicates source selected constructors)
    target.quantified.operations.predicates :=
  InternalConjunctiveObject.Map.ofFunctorIso (atomicPredicates data)
    (FunctorNormalization.comparison (atomicFunctor data))

instance normalizedPredicates_finite : PreservesFiniteLimits
    (normalizedPredicates data).functor := by
  change PreservesFiniteLimits (normalized data)
  infer_instance

instance normalizedPredicates_closed : MonoidalClosedFunctor
    (normalizedPredicates data).functor := by
  change MonoidalClosedFunctor (normalized data)
  infer_instance

theorem normalized_base_object (value : source.closed.Obj) :
    (normalized data).obj (baseObject
      (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) value) =
      data.original.closed.functor.obj value := by
  exact congrArg ObjectImage.value (objectImage_base (atomicFunctor data) value)

theorem normalized_proposition_object :
    (normalized data).obj (predicates source selected constructors).proposition =
      target.quantified.operations.predicates.proposition := by
  change (objectImage (atomicFunctor data)
    (namedObject (⟨⟨()⟩⟩ : ULift.{k} (ULift.{k} Unit)))).value = _
  rw [objectImage_named]
  rfl

theorem normalized_proposition_hom :
    (normalizedPredicates data).proposition.hom =
      eqToHom (normalized_proposition_object data) := by
  change (objectImage (atomicFunctor data)
      (namedObject (⟨⟨()⟩⟩ : ULift.{k} (ULift.{k} Unit)))).comparison.inv ≫
      (data.named.conjunctive.declarations.proposition.inv ≫
        data.named.conjunctive.declarations.proposition.hom) = _
  rw [Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (objectImage (atomicFunctor data)
    (namedObject (⟨⟨()⟩⟩ : ULift.{k} (ULift.{k} Unit)))).comparison.hom).mp
  rw [Iso.hom_inv_id]
  exact (comparison_transport (atomicFunctor data)
    (objectImage_named (atomicFunctor data)
      (⟨⟨()⟩⟩ : ULift.{k} (ULift.{k} Unit)))).symm

theorem atomic_base_arrow {before after : source.closed.Obj} (route : before ⟶ after) :
    (atomicFunctor data).map (baseArrow
      (signature := RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) route) =
      data.original.closed.functor.map route := by
  exact eq_of_heq (Interpretation.ArrowValue.arrows_heq
    (congrArg (fun functor : source.closed.Obj ⥤ target.quantified.programTheory.closed.Obj =>
      (⟨functor.obj before, functor.obj after, functor.map route⟩ :
        Interpretation.ArrowValue target.quantified.programTheory.closed.Obj))
      (entire_original_base data)))

theorem normalized_base_arrow {before after : source.closed.Obj} (route : before ⟶ after) :
    (normalized data).map (baseArrow
      (signature := RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) route) ≫
        eqToHom (normalized_base_object data after) =
      eqToHom (normalized_base_object data before) ≫
        data.original.closed.functor.map route :=
  (FunctorNormalization.base_arrow (atomicFunctor data) route).trans
    (congrArg (fun arrow => eqToHom (normalized_base_object data before) ≫ arrow)
      (atomic_base_arrow data route))

theorem entire_normalized_base :
    baseFunctor (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors) ⋙
        normalized data = data.original.closed.functor := by
  refine _root_.CategoryTheory.Functor.ext (normalized_base_object data) ?_
  intro before after route
  apply (cancel_mono (eqToHom (normalized_base_object data after))).mp
  change (normalized data).map (baseArrow route) ≫
      eqToHom (normalized_base_object data after) =
    (eqToHom (normalized_base_object data before) ≫
      data.original.closed.functor.map route ≫
        eqToHom (normalized_base_object data after).symm) ≫
      eqToHom (normalized_base_object data after)
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact normalized_base_arrow data route

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction
