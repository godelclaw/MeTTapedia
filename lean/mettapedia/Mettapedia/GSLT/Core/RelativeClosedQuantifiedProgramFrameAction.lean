import Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMaps

/-!
# Actual frame operators in independently supplied extension targets

The universal program map supplies the local predicate comparison on the
same complete closed functor. Its event endpoints determine the operational
action, and finite-limit preservation transports the actual frame pullback.
The whole frame operator then commutes with this map, using its independent
program comparison and both complete predicate inputs.

The target relation is independently supplied; it is not defined as the
image relation of the source. Implication is locally qualified on both
sides, separately from the quantified completion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMaps.Supplied

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory
open RelativeClosedQuantified RelativeClosedQuantifiedRuleFrames
open InternalPredicateFunctionObject InternalPredicateFunctionObjectMaps
open InternalPredicatePositionedModalMaps

universe k
variable {source target : Theory.{k,k}}
variable {predicates : InternalConjunctiveObject.Operations source.closed.Obj} {laws : predicates.Laws}
variable {quantified : InternalPredicateQuantifiedObject.Operations target.closed.Obj}
variable (supplied : Supplied source target predicates laws quantified)

def predicateComparison : PositionedRewritePredicateTransport.PredicateComparison supplied.programMap
    (freeObject (conjunctive source predicates laws)).operations quantified where
  proposition := supplied.extension.declarations.proposition
  truth := supplied.extension.declarations.truth
  conjunction := supplied.extension.declarations.conjunction

variable (sourceImplication : InternalPredicateImplication.Qualification predicates)
variable (targetImplication : InternalPredicateImplication.Qualification quantified.predicates)
variable {rule : Rule source} (frame : PositionedRewriteModal.Frame rule)

theorem complete_frame_operator_square :
    supplied.extension.functor.map (actualOperator sourceImplication frame) ≫
        (powerComparison supplied.predicateComparison.predicates
          (generatedFrame source predicates laws frame).carrier).hom =
      (PositionedRewritePredicateTransport.inputsComparison supplied.predicateComparison
          (generatedFrame source predicates laws frame)).hom ≫
        modalityOperator quantified targetImplication
          ((generatedFrame source predicates laws frame).transport supplied.programMap).forget
          ((generatedFrame source predicates laws frame).transport supplied.programMap).focus
          ((generatedFrame source predicates laws frame).transport supplied.programMap).instantiate
          ((generatedFrame source predicates laws frame).transport supplied.programMap).outgoing :=
  PositionedRewritePredicateTransport.complete_operator_square supplied.predicateComparison
    (Implication.freeQualification (conjunctive source predicates laws) sourceImplication)
    targetImplication (generatedFrame source predicates laws frame)

theorem complete_frame_source :
    ((generatedFrame source predicates laws frame).transport supplied.programMap).instantiate ≫
        ((generatedFrame source predicates laws frame).transport supplied.programMap).plug =
      supplied.extension.functor.map (generatedRule source predicates laws rule).left ≫
        supplied.extendedProgram.hom :=
  ((generatedFrame source predicates laws frame).transport supplied.programMap).source

theorem complete_frame_outgoing :
    supplied.extension.functor.map (generatedFrame source predicates laws frame).outgoing ≫
        ((generatedFrame source predicates laws frame).outgoingComparison supplied.programMap).hom =
      ((generatedFrame source predicates laws frame).transport supplied.programMap).outgoing :=
  (generatedFrame source predicates laws frame).outgoing_transport supplied.programMap

end Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMaps.Supplied
