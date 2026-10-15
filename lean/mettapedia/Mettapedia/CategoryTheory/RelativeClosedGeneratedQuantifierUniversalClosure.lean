import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierUniversalStage
import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierModelReadout

/-!
# The independently realized closure is determined at stage zero

Each finite restriction is a genuine locally realized model. Successor
uniqueness follows from its actual new headers and six equations, so
induction recovers every stage without assuming complete operator images.
Every authored origin then recovers its complete value at its birth stage.
The resulting assignment and model equalities retain the original raw
objects; coherent weak-functor comparisons are constructed separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.UniversalClosure

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Iteration Closure

universe k w z
variable {C : Type k} [Category.{k} C] {stage : Stage C}
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {quantifiers : InternalPredicateQuantifiedObject.Operations D}

private theorem model_ext {profile : Stage C} {first second : Model quantifiers profile}
    (meanings : first.meanings = second.meanings) : first = second := by
  cases first
  cases second
  cases meanings
  rfl

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem assignment_extensionality {symbols : Symbols.{k}}
    {first second : RelativeClosedSyntax.Interpretation.Assignment C symbols D}
    (bases : first.base = second.base)
    (objects : first.object = second.object)
    (arrows : first.arrow = second.arrow) : first = second := by
  cases first
  cases second
  cases bases
  cases objects
  cases arrows
  rfl

def restriction (supplied : Model quantifiers (completedStage stage)) (depth : Nat) :
    Model quantifiers (stages stage depth) where
  meanings := (stageMap stage depth).precompose supplied.meanings
  admitted := (stageMap stage depth).realization_precompose supplied.meanings supplied.admitted
  proposition :=
    ((stageMap stage depth).evaluateObject_precompose supplied.meanings
      (stages stage depth).language.proposition.code).symm.trans
        ((congrArg supplied.meanings.evaluateObject
          (congrArg Object.code (Closure.proposition_retained stage depth))).trans supplied.proposition)
  conjunction :=
    ((stageMap stage depth).evaluateArrow_precompose supplied.meanings
      (stages stage depth).language.conjunction.code).symm.trans
        ((congrArg supplied.meanings.evaluateArrow
          (Closure.conjunction_retained stage depth)).trans supplied.conjunction)
  truth :=
    ((stageMap stage depth).evaluateArrow_precompose supplied.meanings
      (stages stage depth).truth.code).symm.trans
        ((congrArg supplied.meanings.evaluateArrow
          (Closure.truth_retained stage depth)).trans supplied.truth)

theorem restriction_successor (supplied : Model quantifiers (completedStage stage)) (depth : Nat) :
    UniversalStage.restrict (restriction supplied (depth + 1)) = restriction supplied depth := by
  apply model_ext
  apply assignment_extensionality
  · change (𝟭 C ⋙ 𝟭 C) ⋙ (𝟭 C ⋙ supplied.meanings.base) = 𝟭 C ⋙ supplied.meanings.base
    rw [Functor.id_comp, Functor.id_comp]
  · rfl
  · funext origin
    rfl

theorem every_stage_recovered (supplied : Model quantifiers (completedStage stage)) :
    (depth : Nat) → restriction supplied depth = models (restriction supplied 0) depth
  | 0 => rfl
  | depth + 1 => by
      apply model_ext
      have previous := (restriction_successor supplied depth).trans (every_stage_recovered supplied depth)
      exact (UniversalStage.successor_unique (restriction supplied (depth + 1))).trans
        (congrArg (fun model : Model quantifiers (stages stage depth) => model.next.meanings) previous)

theorem assignment_recovered (supplied : Model quantifiers (completedStage stage)) :
    supplied.meanings = modelAssignment (restriction supplied 0) := by
  apply assignment_extensionality
  · change supplied.meanings.base = 𝟭 C ⋙ supplied.meanings.base
    exact (Functor.id_comp supplied.meanings.base).symm
  · rfl
  · funext origin
    cases origin with
    | inl origin => rfl
    | inr introduced =>
      rcases introduced with ⟨depth, origin⟩
      exact congrArg (fun model : Model quantifiers (stages stage (depth + 1)) =>
        model.meanings.arrow (.inr origin)) (every_stage_recovered supplied (depth + 1))

theorem complete_model_recovered (supplied : Model quantifiers (completedStage stage)) :
    supplied = completedModel (restriction supplied 0) := model_ext (assignment_recovered supplied)

theorem initial_restriction_recovered (initial : Model quantifiers stage) :
    restriction (completedModel initial) 0 = initial :=
  model_ext (model_assignment_restriction initial 0)

theorem extension_unique (initial : Model quantifiers stage)
    (supplied : Model quantifiers (completedStage stage))
    (old : (stageMap stage 0).precompose supplied.meanings = initial.meanings) :
    supplied = completedModel initial := by
  have initialSame : restriction supplied 0 = initial := model_ext old
  exact (complete_model_recovered supplied).trans (congrArg completedModel initialSame)

abbrev Extensions (initial : Model quantifiers stage) :=
  {supplied : Model quantifiers (completedStage stage) //
    (stageMap stage 0).precompose supplied.meanings = initial.meanings}

instance extensionUnique (initial : Model quantifiers stage) : Unique (Extensions initial) where
  default := ⟨completedModel initial, model_assignment_restriction initial 0⟩
  uniq supplied := Subtype.ext (extension_unique initial supplied.val supplied.property)

def modelEquiv : Model quantifiers stage ≃ Model quantifiers (completedStage stage) where
  toFun := completedModel
  invFun supplied := restriction supplied 0
  left_inv := initial_restriction_recovered
  right_inv supplied := (complete_model_recovered supplied).symm

theorem whole_diagram_recovered (supplied : Model quantifiers (completedStage stage)) :
    supplied.diagram = Closure.modelDiagram (restriction supplied 0) :=
  congrArg Model.diagram (complete_model_recovered supplied)

theorem all_raw_object_readings_recovered (supplied : Model quantifiers (completedStage stage))
    (code : ObjectCode C (symbols stage)) :
    supplied.meanings.evaluateObject code = (modelAssignment (restriction supplied 0)).evaluateObject code :=
  congrArg (fun meanings => meanings.evaluateObject code) (assignment_recovered supplied)

theorem all_raw_arrow_readings_recovered (supplied : Model quantifiers (completedStage stage))
    (code : ArrowCode C (symbols stage)) :
    supplied.meanings.evaluateArrow code = (modelAssignment (restriction supplied 0)).evaluateArrow code :=
  congrArg (fun meanings => meanings.evaluateArrow code) (assignment_recovered supplied)

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.UniversalClosure
