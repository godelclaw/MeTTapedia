import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierModelIteration
import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureNativeInterpretation

/-!
# Complete quantifier closure in arbitrary locally quantified targets

The complete assignment retains the independent initial primitive meanings.
A tagged new operator takes its complete value from the actual finite stage
where it is introduced. Recursion on origins earns assignment restriction;
the independent structural evaluator earns all raw readings and every local
closure declaration. The resulting quotient functor preserves finite limits
and, at the explicit common hom universe, the canonical exponential
comparison. No final realization or whole-expression law is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Iteration

universe k w z
variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {quantifiers : InternalPredicateQuantifiedObject.Operations D} {stage : Stage C}

def modelAssignment (initial : Model quantifiers stage) :
    RelativeClosedSyntax.Interpretation.Assignment C (symbols stage) D where
  base := initial.meanings.base
  object := initial.meanings.object
  arrow
    | .inl origin => initial.meanings.arrow origin
    | .inr ⟨depth, origin⟩ => (models initial (depth + 1)).meanings.arrow (.inr origin)

variable (initial : Model quantifiers stage)

theorem model_base_read : (depth : Nat) →
    (models initial depth).meanings.base = initial.meanings.base
  | 0 => rfl
  | depth + 1 => model_base_read depth

theorem model_object_read : (depth : Nat) → (origin : (stages stage depth).symbols.ObjectName) →
    (modelAssignment initial).object (objects stage depth origin) =
      (models initial depth).meanings.object origin
  | 0, _ => rfl
  | depth + 1, origin => model_object_read depth origin

theorem model_arrow_read : (depth : Nat) → (origin : (stages stage depth).symbols.ArrowName) →
    (modelAssignment initial).arrow (arrows stage depth origin) =
      (models initial depth).meanings.arrow origin
  | 0, _ => rfl
  | depth + 1, .inl origin => model_arrow_read depth origin
  | _ + 1, .inr _ => rfl

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem assignment_extensionality
    {names : Symbols.{k}}
    {first second : RelativeClosedSyntax.Interpretation.Assignment C names D}
    (bases : first.base = second.base)
    (objects : ∀ origin, first.object origin = second.object origin)
    (arrows : ∀ origin, first.arrow origin = second.arrow origin) : first = second := by
  rcases first with ⟨firstBase, firstObjects, firstArrows⟩
  rcases second with ⟨secondBase, secondObjects, secondArrows⟩
  dsimp only at bases objects arrows
  subst secondBase
  have sameObjects := funext objects
  have sameArrows := funext arrows
  subst secondObjects secondArrows
  rfl

theorem model_assignment_restriction (depth : Nat) :
    (stageMap stage depth).precompose (modelAssignment initial) =
      (models initial depth).meanings :=
  assignment_extensionality
    ((Functor.id_comp initial.meanings.base).trans (model_base_read initial depth).symm)
    (model_object_read initial depth) (model_arrow_read initial depth)

theorem model_object_readout (depth : Nat) (code : ObjectCode C (stages stage depth).symbols) :
    (modelAssignment initial).evaluateObject (objectCode stage depth code) =
      (models initial depth).meanings.evaluateObject code :=
  ((stageMap stage depth).evaluateObject_precompose (modelAssignment initial) code).trans
    (congrArg (fun assignment => assignment.evaluateObject code) (model_assignment_restriction initial depth))

theorem model_arrow_readout (depth : Nat) (code : ArrowCode C (stages stage depth).symbols) :
    (modelAssignment initial).evaluateArrow (arrowCode stage depth code) =
      (models initial depth).meanings.evaluateArrow code :=
  ((stageMap stage depth).evaluateArrow_precompose (modelAssignment initial) code).trans
    (congrArg (fun assignment => assignment.evaluateArrow code) (model_assignment_restriction initial depth))

theorem modelRealization :
    RelativeClosedSyntax.Interpretation.Realization (signature stage) (modelAssignment initial) where
  source
    | .inl origin =>
        (model_object_readout initial 0 (stage.presentation.source origin)).trans (initial.admitted.source origin)
    | .inr ⟨depth, origin⟩ =>
        (model_object_readout initial (depth + 1)
          ((stages stage (depth + 1)).presentation.source (.inr origin))).trans
            ((models initial (depth + 1)).admitted.source (.inr origin))
  target
    | .inl origin =>
        (model_object_readout initial 0 (stage.presentation.target origin)).trans (initial.admitted.target origin)
    | .inr ⟨depth, origin⟩ =>
        (model_object_readout initial (depth + 1)
          ((stages stage (depth + 1)).presentation.target (.inr origin))).trans
            ((models initial (depth + 1)).admitted.target (.inr origin))
  equation
    | .inl origin => by
        obtain ⟨value, first, last, before, after⟩ := initial.admitted.equation origin
        exact ⟨value,
          (model_object_readout initial 0 (stage.presentation.equationSource origin)).trans first,
          (model_object_readout initial 0 (stage.presentation.equationTarget origin)).trans last,
          (model_arrow_readout initial 0 (stage.presentation.left origin)).trans before,
          (model_arrow_readout initial 0 (stage.presentation.right origin)).trans after⟩
    | .inr ⟨depth, origin⟩ => by
        obtain ⟨value, first, last, before, after⟩ :=
          (models initial (depth + 1)).admitted.equation (.inr origin)
        exact ⟨value,
          (model_object_readout initial (depth + 1)
            ((stages stage (depth + 1)).presentation.equationSource (.inr origin))).trans first,
          (model_object_readout initial (depth + 1)
            ((stages stage (depth + 1)).presentation.equationTarget (.inr origin))).trans last,
          (model_arrow_readout initial (depth + 1)
            ((stages stage (depth + 1)).presentation.left (.inr origin))).trans before,
          (model_arrow_readout initial (depth + 1)
            ((stages stage (depth + 1)).presentation.right (.inr origin))).trans after⟩

def completedModel : Model quantifiers (completedStage stage) where
  meanings := modelAssignment initial
  admitted := modelRealization initial
  proposition := (model_object_readout initial 0 stage.language.proposition.code).trans initial.proposition
  conjunction := (model_arrow_readout initial 0 stage.language.conjunction.code).trans initial.conjunction
  truth := (model_arrow_readout initial 0 stage.truth.code).trans initial.truth

def modelDiagram : Object (signature stage) ⥤ D :=
  RelativeClosedSyntax.Interpretation.functor (modelAssignment initial) (modelRealization initial)

instance modelDiagram_preservesFiniteLimits : PreservesFiniteLimits (modelDiagram initial) :=
  RelativeClosedSyntax.Interpretation.functor_preservesFiniteLimits
    (modelAssignment initial) (modelRealization initial)

theorem model_whole_stage_restriction (depth : Nat) :
    (stageMap stage depth).functor ⋙ modelDiagram initial = Iteration.modelDiagram initial depth := by
  change (stageMap stage depth).functor ⋙
    RelativeClosedSyntax.Interpretation.functor (modelAssignment initial) (modelRealization initial) =
      RelativeClosedSyntax.Interpretation.functor (models initial depth).meanings (models initial depth).admitted
  have complete := (stageMap stage depth).functor_precompose
    (modelAssignment initial) (modelRealization initial)
  simpa only [model_assignment_restriction] using complete

theorem model_complete_readout {source target : Object (signature stage)} (arrow : RawHom source target) :
    (modelAssignment initial).evaluateArrow arrow.code =
      some ⟨(modelDiagram initial).obj source, (modelDiagram initial).obj target,
        (modelDiagram initial).map (classOf arrow)⟩ :=
  RelativeClosedSyntax.Interpretation.functor_complete_readout
    (modelAssignment initial) (modelRealization initial) arrow

def quantifiedOperations : InternalPredicateQuantifiedObject.Operations (Object (signature stage)) where
  predicates := SourceOperations.operations (language stage) (truth stage)
  laws := laws stage
  universal arrow := universal stage arrow
  existential arrow := existential stage arrow

section CommonHomUniverse

variable {H : Type w} [Category.{k} H]
variable [CartesianMonoidalCategory H] [MonoidalClosed H] [HasFiniteLimits H]
variable {quantification : InternalPredicateQuantifiedObject.Operations H}

def modelTheoryMap (model : Model quantification stage) :
    Mettapedia.GSLT.Core.LambdaTheoryMap (theory stage)
      (Mettapedia.GSLT.Core.LambdaTheory.ofCategory H) where
  functor := modelDiagram model
  preservesFiniteLimits := modelDiagram_preservesFiniteLimits model
  preservesExponentials := RelativeClosedSyntax.Interpretation.functor_closed
    (modelAssignment model) (modelRealization model)

end CommonHomUniverse

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure
