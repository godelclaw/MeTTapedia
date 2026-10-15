import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierIteration
import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierRealization
import Mettapedia.CategoryTheory.InternalPredicateQuantifiedObject

/-!
# Arbitrary locally quantified models at every generated stage

Independent initial primitive meanings carry only their local header and
equation realization. Each new operator uses the actual old arrow value
and the target's finite quantifier diagrams. Those diagrams earn the six
new equation readings and successor realization. Structural evaluation
then retains every old expression, including rejected reads, and the
complete old quotient functor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Iteration

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory

universe k w z
variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (quantifiers : InternalPredicateQuantifiedObject.Operations D)

structure Model (stage : Stage C) where
  meanings : RelativeClosedSyntax.Interpretation.Assignment C stage.symbols D
  admitted : RelativeClosedSyntax.Interpretation.Realization stage.presentation meanings
  proposition : RawInterpretation.ObjectReads meanings stage.language.proposition quantifiers.predicates.proposition
  conjunction : RawInterpretation.Reads meanings stage.language.conjunction quantifiers.predicates.conjunction
  truth : RawInterpretation.Reads meanings stage.truth quantifiers.predicates.truth

variable {quantifiers} {stage : Stage C}

def Model.meaning (previous : Model quantifiers stage) :
    Interpretation.Meaning stage.presentation previous.meanings previous.admitted quantifiers.predicates where
  universal route := (quantifiers.universal
    (Interpretation.routeValue stage.presentation previous.meanings previous.admitted route)).operation
  existential route := (quantifiers.existential
    (Interpretation.routeValue stage.presentation previous.meanings previous.admitted route)).operation

theorem Model.admission (previous : Model quantifiers stage) :
    Interpretation.Admission stage.presentation previous.meanings previous.admitted
      quantifiers.predicates previous.meaning where
  universalMonotonicity route := (quantifiers.universal
    (Interpretation.routeValue stage.presentation previous.meanings previous.admitted route)).monotonicity
  universalUnit route := (quantifiers.universal
    (Interpretation.routeValue stage.presentation previous.meanings previous.admitted route)).unit
  universalCounit route := (quantifiers.universal
    (Interpretation.routeValue stage.presentation previous.meanings previous.admitted route)).counit
  existentialMonotonicity route := (quantifiers.existential
    (Interpretation.routeValue stage.presentation previous.meanings previous.admitted route)).monotonicity
  existentialUnit route := (quantifiers.existential
    (Interpretation.routeValue stage.presentation previous.meanings previous.admitted route)).unit
  existentialCounit route := (quantifiers.existential
    (Interpretation.routeValue stage.presentation previous.meanings previous.admitted route)).counit

def Model.next (previous : Model quantifiers stage) : Model quantifiers stage.next where
  meanings := Interpretation.finalAssignment stage.presentation previous.meanings previous.admitted
    quantifiers.predicates previous.meaning
  admitted := Interpretation.realized stage.presentation stage.language previous.meanings previous.admitted
    quantifiers.predicates previous.meaning previous.proposition previous.conjunction previous.admission
  proposition :=
    (EquationExtension.evaluate_object_original (arrowSignature stage.presentation stage.language)
      (declaration stage.presentation stage.language)
      (Interpretation.assignment stage.presentation previous.meanings previous.admitted quantifiers.predicates previous.meaning)
      ((arrowInclusion stage.presentation stage.language).object stage.language.proposition).code).trans
      ((ArrowExtension.evaluate_object_original stage.presentation (arrowDeclaration stage.presentation stage.language)
        previous.meanings
        (Interpretation.added stage.presentation previous.meanings previous.admitted quantifiers.predicates previous.meaning)
        stage.language.proposition.code).trans previous.proposition)
  conjunction :=
    (EquationExtension.evaluate_arrow_original (arrowSignature stage.presentation stage.language)
      (declaration stage.presentation stage.language)
      (Interpretation.assignment stage.presentation previous.meanings previous.admitted quantifiers.predicates previous.meaning)
      ((arrowInclusion stage.presentation stage.language).rawArrow stage.language.conjunction).code).trans
      ((ArrowExtension.evaluate_arrow_original stage.presentation (arrowDeclaration stage.presentation stage.language)
        previous.meanings
        (Interpretation.added stage.presentation previous.meanings previous.admitted quantifiers.predicates previous.meaning)
        stage.language.conjunction.code).trans previous.conjunction)
  truth :=
    (EquationExtension.evaluate_arrow_original (arrowSignature stage.presentation stage.language)
      (declaration stage.presentation stage.language)
      (Interpretation.assignment stage.presentation previous.meanings previous.admitted quantifiers.predicates previous.meaning)
      ((arrowInclusion stage.presentation stage.language).rawArrow stage.truth).code).trans
      ((ArrowExtension.evaluate_arrow_original stage.presentation (arrowDeclaration stage.presentation stage.language)
        previous.meanings
        (Interpretation.added stage.presentation previous.meanings previous.admitted quantifiers.predicates previous.meaning)
        stage.truth.code).trans previous.truth)

theorem Model.restricted_assignment (previous : Model quantifiers stage) :
    stage.inclusion.precompose previous.next.meanings = previous.meanings := by
  rcases previous with ⟨⟨base, object, arrow⟩, admitted, proposition, conjunction, truth⟩
  rfl

theorem Model.old_object_readout (previous : Model quantifiers stage)
    (raw : ObjectCode C stage.symbols) :
    previous.next.meanings.evaluateObject
      (raw.map stage.inclusion.base stage.inclusion.objects stage.inclusion.arrows) =
      previous.meanings.evaluateObject raw :=
  (stage.inclusion.evaluateObject_precompose previous.next.meanings raw).trans
    (congrArg (fun meanings => meanings.evaluateObject raw) previous.restricted_assignment)

theorem Model.old_arrow_readout (previous : Model quantifiers stage)
    (raw : ArrowCode C stage.symbols) :
    previous.next.meanings.evaluateArrow
      (raw.map stage.inclusion.base stage.inclusion.objects stage.inclusion.arrows) =
      previous.meanings.evaluateArrow raw :=
  (stage.inclusion.evaluateArrow_precompose previous.next.meanings raw).trans
    (congrArg (fun meanings => meanings.evaluateArrow raw) previous.restricted_assignment)

def Model.diagram (previous : Model quantifiers stage) : Object stage.presentation ⥤ D :=
  RelativeClosedSyntax.Interpretation.functor previous.meanings previous.admitted

theorem Model.whole_restriction (previous : Model quantifiers stage) :
    stage.inclusion.functor ⋙ previous.next.diagram = previous.diagram := by
  change stage.inclusion.functor ⋙ RelativeClosedSyntax.Interpretation.functor
      previous.next.meanings previous.next.admitted =
    RelativeClosedSyntax.Interpretation.functor previous.meanings previous.admitted
  have complete := stage.inclusion.functor_precompose previous.next.meanings previous.next.admitted
  simpa only [previous.restricted_assignment] using complete

def quantifiedValue (operations : InternalPredicateQuantifiedObject.Operations D) (kind : Kind)
    (supplied : RelativeClosedSyntax.Interpretation.ArrowValue D) :
    RelativeClosedSyntax.Interpretation.ArrowValue D :=
  ⟨InternalPredicateFunctionObject.power operations.predicates supplied.source,
    InternalPredicateFunctionObject.power operations.predicates supplied.target,
    match kind with
    | .universal => (operations.universal supplied.arrow).operation
    | .existential => (operations.existential supplied.arrow).operation⟩

theorem Model.new_operator_readout (previous : Model quantifiers stage)
    (kind : Kind) (route : Route stage.presentation) {source target : D}
    (arrow : source ⟶ target) (reading : RawInterpretation.Reads previous.meanings route.arrow arrow) :
    previous.next.meanings.evaluateArrow (stage.quantifierRoute kind route).arrow.code =
      some (quantifiedValue quantifiers kind ⟨source, target, arrow⟩) := by
  have namedRead :=
    (EquationExtension.evaluate_arrow_original (arrowSignature stage.presentation stage.language)
      (declaration stage.presentation stage.language)
      (Interpretation.assignment stage.presentation previous.meanings previous.admitted
        quantifiers.predicates previous.meaning)
      (quantifier stage.presentation stage.language kind route).code).trans
        (Interpretation.operator_read stage.presentation stage.language previous.meanings previous.admitted
          quantifiers.predicates previous.meaning kind route)
  have oldImage := Option.some.inj
    ((RelativeClosedSyntax.Interpretation.rawArrowValue_readout previous.meanings previous.admitted
      route.arrow).symm.trans reading)
  exact namedRead.trans (congrArg (fun value : RelativeClosedSyntax.Interpretation.ArrowValue D =>
    some (quantifiedValue quantifiers kind value)) oldImage)

def models (initial : Model quantifiers stage) :
    (depth : Nat) → Model quantifiers (stages stage depth)
  | 0 => initial
  | depth + 1 => (models initial depth).next

def modelDiagram (initial : Model quantifiers stage) (depth : Nat) :
    Object (stages stage depth).presentation ⥤ D := (models initial depth).diagram

theorem every_successor_retains_the_old_model (initial : Model quantifiers stage) (depth : Nat) :
    (stages stage depth).inclusion.functor ⋙ modelDiagram initial (depth + 1) = modelDiagram initial depth :=
  (models initial depth).whole_restriction

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Iteration
