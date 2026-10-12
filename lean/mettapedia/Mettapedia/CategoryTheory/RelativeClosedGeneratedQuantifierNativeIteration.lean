import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierIteration
import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierNativeMeaning

/-!
# Earned classifier interpretation at every quantifier stage

The initial data supply independent primitive meanings and local header and
declared-equation admission. Each successor is constructed from the actual
old evaluator and classifier quantification; its six new diagrams are
proved. The same truth and conjunction readings are retained. Restriction
recovers every old raw expression, including rejected reads, and the whole
old quotient functor. No stage soundness or expression-compatibility callback
is supplied to the iteration.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Iteration

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory
open HigherOrderInternalPredicateObject

universe k w z p
variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (doctrine : PredicateDoctrine.HigherOrder.{w,z,p} D)

structure NativeModel (stage : Stage C) where
  meanings : RelativeClosedSyntax.Interpretation.Assignment C stage.symbols D
  admitted : RelativeClosedSyntax.Interpretation.Realization stage.presentation meanings
  proposition : RawInterpretation.ObjectReads meanings stage.language.proposition (operations doctrine).proposition
  conjunction : RawInterpretation.Reads meanings stage.language.conjunction (operations doctrine).conjunction
  truth : RawInterpretation.Reads meanings stage.truth (operations doctrine).truth

variable {doctrine} {stage : Stage C}

def NativeModel.next (previous : NativeModel doctrine stage) : NativeModel doctrine stage.next where
  meanings := Interpretation.finalAssignment stage.presentation previous.meanings previous.admitted
    (operations doctrine) (NativeMeaning.meaning stage.presentation previous.meanings previous.admitted doctrine)
  admitted := NativeMeaning.realized stage.presentation stage.language previous.meanings previous.admitted doctrine
    previous.proposition previous.conjunction
  proposition :=
    (EquationExtension.evaluate_object_original (arrowSignature stage.presentation stage.language)
      (declaration stage.presentation stage.language)
      (Interpretation.assignment stage.presentation previous.meanings previous.admitted (operations doctrine)
        (NativeMeaning.meaning stage.presentation previous.meanings previous.admitted doctrine))
      ((arrowInclusion stage.presentation stage.language).object stage.language.proposition).code).trans
      ((ArrowExtension.evaluate_object_original stage.presentation (arrowDeclaration stage.presentation stage.language)
        previous.meanings
        (Interpretation.added stage.presentation previous.meanings previous.admitted (operations doctrine)
          (NativeMeaning.meaning stage.presentation previous.meanings previous.admitted doctrine))
        stage.language.proposition.code).trans previous.proposition)
  conjunction :=
    (EquationExtension.evaluate_arrow_original (arrowSignature stage.presentation stage.language)
      (declaration stage.presentation stage.language)
      (Interpretation.assignment stage.presentation previous.meanings previous.admitted (operations doctrine)
        (NativeMeaning.meaning stage.presentation previous.meanings previous.admitted doctrine))
      ((arrowInclusion stage.presentation stage.language).rawArrow stage.language.conjunction).code).trans
      ((ArrowExtension.evaluate_arrow_original stage.presentation (arrowDeclaration stage.presentation stage.language)
        previous.meanings
        (Interpretation.added stage.presentation previous.meanings previous.admitted (operations doctrine)
          (NativeMeaning.meaning stage.presentation previous.meanings previous.admitted doctrine))
        stage.language.conjunction.code).trans previous.conjunction)
  truth :=
    (EquationExtension.evaluate_arrow_original (arrowSignature stage.presentation stage.language)
      (declaration stage.presentation stage.language)
      (Interpretation.assignment stage.presentation previous.meanings previous.admitted (operations doctrine)
        (NativeMeaning.meaning stage.presentation previous.meanings previous.admitted doctrine))
      ((arrowInclusion stage.presentation stage.language).rawArrow stage.truth).code).trans
      ((ArrowExtension.evaluate_arrow_original stage.presentation (arrowDeclaration stage.presentation stage.language)
        previous.meanings
        (Interpretation.added stage.presentation previous.meanings previous.admitted (operations doctrine)
          (NativeMeaning.meaning stage.presentation previous.meanings previous.admitted doctrine))
        stage.truth.code).trans previous.truth)

theorem NativeModel.restricted_assignment (previous : NativeModel doctrine stage) :
    stage.inclusion.precompose previous.next.meanings = previous.meanings := by
  rcases previous with ⟨⟨base, object, arrow⟩, admitted, proposition, conjunction, truth⟩
  rfl

theorem NativeModel.old_object_readout (previous : NativeModel doctrine stage)
    (raw : ObjectCode C stage.symbols) :
    previous.next.meanings.evaluateObject (raw.map stage.inclusion.base stage.inclusion.objects stage.inclusion.arrows) =
      previous.meanings.evaluateObject raw :=
  (stage.inclusion.evaluateObject_precompose previous.next.meanings raw).trans
    (congrArg (fun meanings => meanings.evaluateObject raw) previous.restricted_assignment)

theorem NativeModel.old_arrow_readout (previous : NativeModel doctrine stage)
    (raw : ArrowCode C stage.symbols) :
    previous.next.meanings.evaluateArrow (raw.map stage.inclusion.base stage.inclusion.objects stage.inclusion.arrows) =
      previous.meanings.evaluateArrow raw :=
  (stage.inclusion.evaluateArrow_precompose previous.next.meanings raw).trans
    (congrArg (fun meanings => meanings.evaluateArrow raw) previous.restricted_assignment)

def NativeModel.diagram (previous : NativeModel doctrine stage) : Object stage.presentation ⥤ D :=
  RelativeClosedSyntax.Interpretation.functor previous.meanings previous.admitted

theorem NativeModel.whole_restriction (previous : NativeModel doctrine stage) :
    stage.inclusion.functor ⋙ previous.next.diagram = previous.diagram := by
  change stage.inclusion.functor ⋙ RelativeClosedSyntax.Interpretation.functor
      previous.next.meanings previous.next.admitted =
    RelativeClosedSyntax.Interpretation.functor previous.meanings previous.admitted
  have complete := stage.inclusion.functor_precompose previous.next.meanings previous.next.admitted
  simpa only [previous.restricted_assignment] using complete

theorem NativeModel.new_operator_readout (previous : NativeModel doctrine stage)
    (kind : Kind) (route : Route stage.presentation) {source target : D}
    (arrow : source ⟶ target) (reading : RawInterpretation.Reads previous.meanings route.arrow arrow) :
    previous.next.meanings.evaluateArrow (stage.quantifierRoute kind route).arrow.code =
      some (NativeMeaning.operationValue doctrine kind ⟨source, target, arrow⟩) := by
  have complete := NativeMeaning.named_read stage.presentation stage.language previous.meanings previous.admitted
    doctrine kind route
  have oldImage := Option.some.inj
    ((RelativeClosedSyntax.Interpretation.rawArrowValue_readout previous.meanings previous.admitted route.arrow).symm.trans reading)
  exact complete.trans (congrArg (fun value : RelativeClosedSyntax.Interpretation.ArrowValue D =>
    some (NativeMeaning.operationValue doctrine kind value)) oldImage)

def nativeModels (initial : NativeModel doctrine stage) :
    (depth : Nat) → NativeModel doctrine (stages stage depth)
  | 0 => initial
  | depth + 1 => (nativeModels initial depth).next

def stageDiagram (initial : NativeModel doctrine stage) (depth : Nat) :
    Object (stages stage depth).presentation ⥤ D := (nativeModels initial depth).diagram

theorem every_successor_retains_the_whole_old_functor (initial : NativeModel doctrine stage) (depth : Nat) :
    (stages stage depth).inclusion.functor ⋙ stageDiagram initial (depth + 1) = stageDiagram initial depth :=
  (nativeModels initial depth).whole_restriction

theorem every_successor_retains_rejected_and_successful_arrows (initial : NativeModel doctrine stage) (depth : Nat)
    (raw : ArrowCode C (stages stage depth).symbols) :
    (nativeModels initial (depth + 1)).meanings.evaluateArrow
      (raw.map (stages stage depth).inclusion.base (stages stage depth).inclusion.objects
        (stages stage depth).inclusion.arrows) =
      (nativeModels initial depth).meanings.evaluateArrow raw :=
  (nativeModels initial depth).old_arrow_readout raw

theorem every_new_quantifier_has_its_complete_native_reading (initial : NativeModel doctrine stage) (depth : Nat)
    (kind : Kind) (route : Route (stages stage depth).presentation) :
    RawInterpretation.Reads (nativeModels initial (depth + 1)).meanings
      ((stages stage depth).quantifierRoute kind route).arrow
      (Interpretation.operator (stages stage depth).presentation
        (nativeModels initial depth).meanings (nativeModels initial depth).admitted (operations doctrine)
        (NativeMeaning.meaning (stages stage depth).presentation
          (nativeModels initial depth).meanings (nativeModels initial depth).admitted doctrine) kind route) :=
  NativeMeaning.named_read (stages stage depth).presentation (stages stage depth).language
    (nativeModels initial depth).meanings (nativeModels initial depth).admitted doctrine kind route

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Iteration
