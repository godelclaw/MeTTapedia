import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierModelReadout
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifiedObject

/-!
# Recovery of independently constructed classifier models

Only the five local initial-model readings are transferred to the general
locally quantified construction. Successor values agree by the actual
classifier quantifier definitions. Induction earns every finite-stage
comparison, and the tagged-origin assignment earns the final functor and
all raw evaluator comparisons, including failure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Iteration

universe k w z p
variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {doctrine : PredicateDoctrine.HigherOrder.{w,z,p} D} {stage : Stage C}

namespace Iteration

def NativeModel.toModel (initial : NativeModel doctrine stage) :
    Model (HigherOrderInternalPredicateQuantifiedObject.operations doctrine) stage where
  meanings := initial.meanings
  admitted := initial.admitted
  proposition := initial.proposition
  conjunction := initial.conjunction
  truth := initial.truth

theorem NativeModel.toModel_next (initial : NativeModel doctrine stage) :
    initial.next.toModel = initial.toModel.next := by
  rcases initial with ⟨meanings, admitted, proposition, conjunction, truth⟩
  rfl

theorem models_native (initial : NativeModel doctrine stage) (depth : Nat) :
    models initial.toModel depth = (nativeModels initial depth).toModel := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
    change (models initial.toModel depth).next = (nativeModels initial depth).next.toModel
    exact (congrArg Model.next previous).trans
      ((nativeModels initial depth).toModel_next).symm

end Iteration

namespace Closure

variable (initial : NativeModel doctrine stage)

private theorem functor_retype {names : Symbols.{k}}
    {presentation : Signature (C := C) (symbols := names)}
    {first second : RelativeClosedSyntax.Interpretation.Assignment C names D}
    (same : first = second)
    (firstAdmitted : RelativeClosedSyntax.Interpretation.Realization presentation first)
    (secondAdmitted : RelativeClosedSyntax.Interpretation.Realization presentation second) :
    RelativeClosedSyntax.Interpretation.functor first firstAdmitted =
      RelativeClosedSyntax.Interpretation.functor second secondAdmitted := by
  cases same
  rfl

theorem model_assignment_native : modelAssignment initial.toModel = nativeAssignment initial := by
  have arrowValues : (modelAssignment initial.toModel).arrow = (nativeAssignment initial).arrow := by
    funext origin
    cases origin with
    | inl origin => rfl
    | inr origin =>
      rcases origin with ⟨depth, name⟩
      exact congrArg
        (fun model : Model (HigherOrderInternalPredicateQuantifiedObject.operations doctrine)
            (stages stage (depth + 1)) => model.meanings.arrow (.inr name))
        (models_native initial (depth + 1))
  exact congrArg
    (fun arrows =>
      (⟨initial.meanings.base, initial.meanings.object, arrows⟩ :
        RelativeClosedSyntax.Interpretation.Assignment C (symbols stage) D)) arrowValues

theorem model_diagram_native : modelDiagram initial.toModel = nativeDiagram initial := by
  exact functor_retype (model_assignment_native initial)
    (modelRealization initial.toModel) (nativeRealization initial)

theorem model_object_native (code : ObjectCode C (symbols stage)) :
    (modelAssignment initial.toModel).evaluateObject code = (nativeAssignment initial).evaluateObject code :=
  congrArg (fun meanings => meanings.evaluateObject code) (model_assignment_native initial)

theorem model_arrow_native (code : ArrowCode C (symbols stage)) :
    (modelAssignment initial.toModel).evaluateArrow code = (nativeAssignment initial).evaluateArrow code :=
  congrArg (fun meanings => meanings.evaluateArrow code) (model_assignment_native initial)

theorem model_operator_native (route : Route (signature stage))
    (operation : InternalPredicateFunctionObject.power (operations stage) route.source ⟶
      InternalPredicateFunctionObject.power (operations stage) route.target) :
    modelOperatorValue initial.toModel route operation = nativeOperatorValue initial route operation :=
  congrArg (fun diagram : Object (signature stage) ⥤ D =>
    (⟨diagram.obj (InternalPredicateFunctionObject.power (operations stage) route.source),
      diagram.obj (InternalPredicateFunctionObject.power (operations stage) route.target),
      diagram.map operation⟩ : RelativeClosedSyntax.Interpretation.ArrowValue D))
      (model_diagram_native initial)

end Closure

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier
