import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedExpressionReadout

/-!
# Earned admission of every combined named primitive

The actual defining equations identify constructor and positioned-modal
names with their authored bodies. The independently interpreted complete
bodies are recovered by the earned predicate-expression comparison. This
supplies all old primitive readings required by coherent classification;
native inverse-arrow admission is then earned by the existing base theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory FunctorNormalization Interpretation
open ProgramReductionTheory RelativeClosedNamedQuantifiedPresentation

universe k
variable {source : Theory.{k,k}} {Index Origins : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source}
variable {target : QuantifiedImplicativeProgramTheory.{k}}
variable (data : OriginComparison (source := source) (selected := selected) (constructors := constructors) target)

theorem constructor_primitive_images (origin : Origins) :
    (extracted data).arrow (BaseExtension.originalArrows (Sum.inr origin)) =
      (model data).nativeModel.meanings.arrow (BaseExtension.originalArrows (Sum.inr origin)) := by
  have namedEqual :
      classOf (namedArrow (RelativeClosedStructuralImagePresentation.nativeHeaders source selected constructors)
        (BaseExtension.originalArrows (Sum.inr origin))) =
      classOf ((primitiveInclusion (source := source) (selected := selected) (constructors := constructors)).rawArrow
        (RelativeClosedPredicateLogic.existentialRaw (constructors origin).term)) :=
    congrArg (RelativeClosedStructuralImagePresentation.nativeInclusion source selected constructors).functor.map
      (RelativeClosedStructuralImagePresentation.named_operation_is_constructor_image source selected constructors origin)
  have body := complete_expression_value data
    (RelativeClosedPredicateLogic.existentialRaw (constructors origin).term)
    ((model data).constructorValues origin) (by rfl)
  exact (congrArg (fun arrow => (⟨_, _, (normalized data).map arrow⟩ :
      ArrowValue target.quantified.programTheory.closed.Obj)) namedEqual).trans body

theorem modal_primitive_images (origin : Option Index) :
    (extracted data).arrow (BaseExtension.originalArrows (Sum.inl (Sum.inr origin))) =
      (model data).nativeModel.meanings.arrow
        (BaseExtension.originalArrows (Sum.inl (Sum.inr origin))) := by
  cases origin with
  | none =>
    have namedEqual :
        classOf (namedArrow (RelativeClosedStructuralImagePresentation.nativeHeaders source selected constructors)
          (BaseExtension.originalArrows (Sum.inl (Sum.inr none)))) =
        classOf ((primitiveInclusion (source := source) (selected := selected) (constructors := constructors)).rawArrow
          (RelativeClosedPositionedModalPresentation.expression source selected none)) :=
      congrArg (modalInclusion source selected constructors).functor.map
        (RelativeClosedPositionedModalPresentation.named_operation_is_the_authored_expression source selected none)
    have body := complete_expression_value data
      (RelativeClosedPositionedModalPresentation.expression source selected none)
      ((model data).previous.modalValues none)
      (RelativeClosedPositionedModalRealization.expected_expression_read source selected
        data.original.closed.functor
        (RelativeClosedNamedQuantifiedMeaning.meaning source target.quantified
          data.original.closed.functor target.implication) none)
    exact (congrArg (fun arrow => (⟨_, _, (normalized data).map arrow⟩ :
        ArrowValue target.quantified.programTheory.closed.Obj)) namedEqual).trans body
  | some origin =>
    have namedEqual :
        classOf (namedArrow (RelativeClosedStructuralImagePresentation.nativeHeaders source selected constructors)
          (BaseExtension.originalArrows (Sum.inl (Sum.inr (some origin))))) =
        classOf ((primitiveInclusion (source := source) (selected := selected) (constructors := constructors)).rawArrow
          (RelativeClosedPositionedModalPresentation.expression source selected (some origin))) :=
      congrArg (modalInclusion source selected constructors).functor.map
        (RelativeClosedPositionedModalPresentation.named_operation_is_the_authored_expression source selected (some origin))
    have body := complete_expression_value data
      (RelativeClosedPositionedModalPresentation.expression source selected (some origin))
      ((model data).previous.modalValues (some origin))
      (RelativeClosedPositionedModalRealization.expected_expression_read source selected
        data.original.closed.functor
        (RelativeClosedNamedQuantifiedMeaning.meaning source target.quantified
          data.original.closed.functor target.implication) (some origin))
    exact (congrArg (fun arrow => (⟨_, _, (normalized data).map arrow⟩ :
        ArrowValue target.quantified.programTheory.closed.Obj)) namedEqual).trans body

theorem all_old_primitive_admission :
    @RelativeClosedStructuralImageCoherent.LocalArrowAdmission source Index Origins selected constructors
      target.quantified.programTheory.closed.Obj inferInstance inferInstance inferInstance inferInstance
      (model data) data.named.functor
      data.named.conjunctive.finite data.named.conjunctive.closed
      (primitiveImages data) := by
  let : PreservesFiniteLimits data.named.functor := data.named.conjunctive.finite
  let : MonoidalClosedFunctor data.named.functor := data.named.conjunctive.closed
  constructor
  intro origin
  cases origin with
  | inl original =>
    cases original with
    | inl operation => exact logical_primitive_images data operation
    | inr modality => exact modal_primitive_images data modality
  | inr constructor => exact constructor_primitive_images data constructor

def entire_named_comparison : data.named.functor ≅ (model data).nativeDiagram :=
  @RelativeClosedStructuralImageCoherent.comparison source Index Origins selected constructors
    target.quantified.programTheory.closed.Obj inferInstance inferInstance inferInstance inferInstance
    (model data) data.named.functor
    data.named.conjunctive.finite data.named.conjunctive.closed
    (primitiveImages data) (all_old_primitive_admission data)

theorem whole_named_arrow
    {before after : Object (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors)}
    (arrow : before ⟶ after) :
    data.named.functor.map arrow ≫ (entire_named_comparison data).hom.app after =
      (entire_named_comparison data).hom.app before ≫ (model data).nativeDiagram.map arrow :=
  (entire_named_comparison data).hom.naturality arrow

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction
