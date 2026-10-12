import Mettapedia.GSLT.Core.PositionedRewritePredicateTransport
import Mettapedia.CategoryTheory.RelativeClosedProgramReductionExtension
import Mettapedia.CategoryTheory.RelativeClosedQuantifiedPositionedModal

/-!
# Actual authored frames in the quantified extension

The same completion unit installs the program relation and the entire rule
frame. Its event isomorphism retains the supplied firing evidence, separately
from the quantified predicate. The outgoing program product is compared
canonically with the mapped source product. Every independently supplied
weak map out of the completion preserves the actual frame operator with
this comparison and recovers every supplied event and future input.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedQuantifiedRuleFrames

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory
open InternalPredicateFunctionObject InternalPredicateFunctionObjectMaps
open InternalPredicatePositionedModalMaps PositionedModalOutgoingComparison
open RelativeClosedQuantified

universe k
variable (source : Theory.{k,k})
variable (predicates : InternalConjunctiveObject.Operations source.closed.Obj)
variable (laws : predicates.Laws)

def conjunctive : ConjunctiveClosedTheory.{k} where
  closed := source.closed
  operations := predicates
  laws := laws

abbrev inclusion := (Extension.unitMap (conjunctive source predicates laws)).underlying

def generatedTheory : Theory.{k,k} :=
  RelativeClosedProgramReductionExtension.mappedTheory source
    (freeObject (conjunctive source predicates laws)).closed (inclusion source predicates laws)

def generatedInclusion : Map source (generatedTheory source predicates laws) :=
  RelativeClosedProgramReductionExtension.mapping source
    (freeObject (conjunctive source predicates laws)).closed (inclusion source predicates laws)

def generatedRule (rule : Rule source) : Rule (generatedTheory source predicates laws) :=
  rule.transport (generatedInclusion source predicates laws)

def generatedFrame {rule : Rule source} (frame : PositionedRewriteModal.Frame rule) :
    PositionedRewriteModal.Frame (generatedRule source predicates laws rule) :=
  frame.transport (generatedInclusion source predicates laws)

theorem event_retained : IsIso (generatedInclusion source predicates laws).reduction :=
  RelativeClosedProgramReductionExtension.complete_reduction_retained source
    (freeObject (conjunctive source predicates laws)).closed (inclusion source predicates laws)

variable {source predicates laws}
variable (qualified : InternalPredicateImplication.Qualification predicates)
variable {rule : Rule source} (frame : PositionedRewriteModal.Frame rule)

def actualOperator :
    profiles (freeObject (conjunctive source predicates laws)).operations.predicates
        (generatedFrame source predicates laws frame).assay
        ((generatedFrame source predicates laws frame).assay ⨯ (generatedTheory source predicates laws).program) ⟶
      power (freeObject (conjunctive source predicates laws)).operations.predicates
        (generatedFrame source predicates laws frame).carrier :=
  modalityOperator (freeObject (conjunctive source predicates laws)).operations
    (Implication.freeQualification (conjunctive source predicates laws) qualified)
    (generatedFrame source predicates laws frame).forget (generatedFrame source predicates laws frame).focus
    (generatedFrame source predicates laws frame).instantiate (generatedFrame source predicates laws frame).outgoing

theorem actual_operator_reading :
    (profilesReindexIso
      (predicates := (freeObject (conjunctive source predicates laws)).operations.predicates)
      (frame.outgoingComparison (generatedInclusion source predicates laws))).hom ≫
        actualOperator qualified frame =
      RelativeClosedQuantified.PositionedModal.operator (conjunctive source predicates laws) qualified
        frame.forget frame.focus frame.instantiate frame.outgoing := by
  change _ ≫ modalityOperator _ _ _ _ _
    ((frame.transport (generatedInclusion source predicates laws)).outgoing) = _
  rw [← frame.outgoing_transport]
  exact modalityOperator_comparison
    (freeObject (conjunctive source predicates laws)).operations
    (Implication.freeQualification (conjunctive source predicates laws) qualified)
    ((inclusion source predicates laws).functor.map frame.forget)
    ((inclusion source predicates laws).functor.map frame.focus)
    ((inclusion source predicates laws).functor.map frame.instantiate)
    ((inclusion source predicates laws).functor.map frame.outgoing)
    (frame.outgoingComparison (generatedInclusion source predicates laws))

variable {target : QuantifiedClosedTheory.{k}}
variable (candidate : QuantifiedClosedTheory.Map (freeObject (conjunctive source predicates laws)) target)

abbrev candidateClosed := candidate.underlying

def candidateTheory : Theory.{k,k} :=
  RelativeClosedProgramReductionExtension.mappedTheory (generatedTheory source predicates laws)
    target.closed (candidateClosed candidate)

def candidateMap : Map (generatedTheory source predicates laws) (candidateTheory candidate) :=
  RelativeClosedProgramReductionExtension.mapping (generatedTheory source predicates laws)
    target.closed (candidateClosed candidate)

def candidateComparison : PositionedRewritePredicateTransport.PredicateComparison
    (candidateMap candidate) (freeObject (conjunctive source predicates laws)).operations target.operations where
  proposition := candidate.declarations.proposition
  truth := candidate.declarations.truth
  conjunction := candidate.declarations.conjunction

local instance candidate_predicates_finite :
    PreservesFiniteLimits (candidateComparison candidate).predicates.functor := candidate.finite

local instance candidate_predicates_closed :
    MonoidalClosedFunctor (candidateComparison candidate).predicates.functor := candidate.closed

variable (targetImplication : InternalPredicateImplication.Qualification target.operations.predicates)

theorem actual_candidate_square :
    candidate.functor.map (actualOperator qualified frame) ≫
        (powerComparison (candidateComparison candidate).predicates
          (generatedFrame source predicates laws frame).carrier).hom =
      (PositionedRewritePredicateTransport.inputsComparison (candidateComparison candidate)
        (generatedFrame source predicates laws frame)).hom ≫
        modalityOperator target.operations targetImplication
          ((generatedFrame source predicates laws frame).transport (candidateMap candidate)).forget
          ((generatedFrame source predicates laws frame).transport (candidateMap candidate)).focus
          ((generatedFrame source predicates laws frame).transport (candidateMap candidate)).instantiate
          ((generatedFrame source predicates laws frame).transport (candidateMap candidate)).outgoing :=
  PositionedRewritePredicateTransport.complete_operator_square (candidateComparison candidate)
    (Implication.freeQualification (conjunctive source predicates laws) qualified) targetImplication
    (generatedFrame source predicates laws frame)

end Mettapedia.GSLT.Core.RelativeClosedQuantifiedRuleFrames
