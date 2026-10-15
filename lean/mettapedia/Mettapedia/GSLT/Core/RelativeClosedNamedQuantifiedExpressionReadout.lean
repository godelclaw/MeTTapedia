import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedLogicalAdmission
import Mettapedia.CategoryTheory.RelativeClosedSyntaxAssignmentComparison

/-!
# Complete authored expression readings from earned primitive admission

The original predicate assignment is recovered from the candidate's actual
normalized declaration values. Structural evaluation then recovers every
authored predicate expression, with its whole function and independently
formed endpoint objects. Modal bodies and constructor images use this same
comparison rather than an extra whole-expression preservation hypothesis.
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

def extracted := assignment (atomicFunctor data)
  (RelativeClosedStructuralImagePresentation.nativeHeaders source selected constructors)

def primitiveMeanings := RelativeClosedPredicateLogic.Interpretation.assignment
  data.original.closed.functor
  (RelativeClosedNamedQuantifiedMeaning.meaning source target.quantified
    data.original.closed.functor target.implication)

def primitiveInclusion := RelativeClosedPredicateLogic.equationInclusion.compose
  (logicalInclusion source selected constructors)

theorem entire_primitive_assignment :
    (primitiveInclusion (source := source) (selected := selected) (constructors := constructors)).precompose
        (extracted data) = primitiveMeanings data := by
  apply Assignment.equal_of_components
  · exact (_root_.CategoryTheory.Functor.id_comp _).trans (entire_original_base data)
  · rfl
  · exact funext (logical_primitive_images data)

theorem entire_expression_evaluation
    {before after : Object (RelativeClosedPredicateLogic.signature (C := source.closed.Obj))}
    (raw : RawHom before after) :
    (extracted data).evaluateArrow
        ((primitiveInclusion (source := source) (selected := selected) (constructors := constructors)).rawArrow raw).code =
      (primitiveMeanings data).evaluateArrow raw.code :=
  ((primitiveInclusion (source := source) (selected := selected) (constructors := constructors)).evaluateArrow_precompose
    (extracted data) raw.code).trans
      (congrArg (fun supplied => supplied.evaluateArrow raw.code) (entire_primitive_assignment data))

theorem complete_expression_value
    {before after : Object (RelativeClosedPredicateLogic.signature (C := source.closed.Obj))}
    (raw : RawHom before after) (value : ArrowValue target.quantified.programTheory.closed.Obj)
    (reading : (primitiveMeanings data).evaluateArrow raw.code = some value) :
    (⟨(normalized data).obj
        ((primitiveInclusion (source := source) (selected := selected) (constructors := constructors)).object before),
      (normalized data).obj
        ((primitiveInclusion (source := source) (selected := selected) (constructors := constructors)).object after),
      (normalized data).map
        (classOf ((primitiveInclusion (source := source) (selected := selected) (constructors := constructors)).rawArrow raw))⟩ :
      ArrowValue target.quantified.programTheory.closed.Obj) = value :=
  Option.some.inj
    ((raw_arrow_reconstruction (atomicFunctor data)
      (RelativeClosedStructuralImagePresentation.nativeHeaders source selected constructors)
      ((primitiveInclusion (source := source) (selected := selected) (constructors := constructors)).rawArrow raw)).symm.trans
        ((entire_expression_evaluation data raw).trans reading))

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction
