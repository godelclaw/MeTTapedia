import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedNormalizedPredicates

/-!
# Logical primitive admission is earned from the candidate

For every original logical declaration, the candidate's normalized complete
arrow value is the independently supplied target meaning. The three
qualifier transport results identify the actual raw declaration spellings;
their finite diagrams and whole-operation uniqueness earn all five cases.
No logical primitive-admission hypothesis is required.
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

theorem logical_primitive_images (operation : RelativeClosedPredicateLogic.Operation source.closed.Obj) :
    (assignment (atomicFunctor data)
      (RelativeClosedStructuralImagePresentation.nativeHeaders source selected constructors)).arrow
        (BaseExtension.originalArrows (Sum.inl (Sum.inl operation))) =
      (model data).nativeModel.meanings.arrow
        (BaseExtension.originalArrows (Sum.inl (Sum.inl operation))) := by
  cases operation with
  | truth => exact normalized_truth_value data
  | conjunction => exact normalized_conjunction_value data
  | implication =>
      have primitive :
          classOf (namedArrow (RelativeClosedStructuralImagePresentation.nativeHeaders source selected constructors)
            (BaseExtension.originalArrows (Sum.inl (Sum.inl RelativeClosedPredicateLogic.Operation.implication)))) =
          (implication source selected constructors).operation := by
        exact (native_implication_operation source selected constructors).symm
      exact (congrArg (fun arrow => (⟨_, _, (normalized data).map arrow⟩ :
          ArrowValue target.quantified.programTheory.closed.Obj)) primitive).trans
        (normalized_implication_value data)
  | universal route =>
      have primitive :
          classOf (namedArrow (RelativeClosedStructuralImagePresentation.nativeHeaders source selected constructors)
            (BaseExtension.originalArrows (Sum.inl (Sum.inl (RelativeClosedPredicateLogic.Operation.universal route))))) =
          (nativeUniversal source selected constructors route).operation := by
        exact (native_universal_operation source selected constructors route).symm
      exact (congrArg (fun arrow => (⟨_, _, (normalized data).map arrow⟩ :
          ArrowValue target.quantified.programTheory.closed.Obj)) primitive).trans
        (normalized_universal_value data route)
  | existential route =>
      have primitive :
          classOf (namedArrow (RelativeClosedStructuralImagePresentation.nativeHeaders source selected constructors)
            (BaseExtension.originalArrows (Sum.inl (Sum.inl (RelativeClosedPredicateLogic.Operation.existential route))))) =
          (nativeExistential source selected constructors route).operation := by
        exact (native_existential_operation source selected constructors route).symm
      exact (congrArg (fun arrow => (⟨_, _, (normalized data).map arrow⟩ :
          ArrowValue target.quantified.programTheory.closed.Obj)) primitive).trans
        (normalized_existential_value data route)

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction
