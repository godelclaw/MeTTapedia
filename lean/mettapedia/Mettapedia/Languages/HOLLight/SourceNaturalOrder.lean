import Mettapedia.Languages.HOLLight.NaturalModelCategoricity
import Mettapedia.Logic.HOL.SuccessorOrder

/-!
# Generated strict order in the received source model

The equivalence earned from the three exact cached Peano facts preserves the
interpreted successor. It identifies the successor-closure order program with
strict natural order in the same model constructed from accepted source replay.
The result introduces neither an order constant nor a new semantic premise.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.NaturalModelCategoricity
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open SourceProfileModels TypeFamilySemantics
universe w

variable (signature : Signature) (commands : List ProofExecution.Registered.Command)
  (after : ProofExecution.Registered.State)
  (accepted : ProofExecution.Registered.replayFrom policy
    (ProofExecution.Registered.empty SourceProfile.primitiveContext) commands = some after)
  (facts : CachedFacts signature after) (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

theorem replayNaturalEquivalence_successor (n : Nat) :
    replayNaturalEquivalence signature commands after accepted facts other assignment (n + 1) =
      signature.next ((sourceReplayFrame commands after accepted).frame.model other assignment)
        (replayNaturalEquivalence signature commands after accepted facts other assignment n) := rfl

theorem replay_order_iff
    (values : ((sourceReplayFrame commands after accepted).frame.model other assignment).Valuation [])
    (lower upper : signature.Carrier ((sourceReplayFrame commands after accepted).frame.model other assignment)) :
    (((sourceReplayFrame commands after accepted).frame.model other assignment).denote
      (HOL.SuccessorOrder.less signature.successor) values lower upper).down ↔
      (replayNaturalEquivalence signature commands after accepted facts other assignment).symm lower <
        (replayNaturalEquivalence signature commands after accepted facts other assignment).symm upper := by
  apply HOL.SuccessorOrder.less_iff
    ((sourceReplayFrame commands after accepted).frame.model other assignment)
    ((sourceReplayFrame commands after accepted).frame.model_fullDomains other assignment)
    signature.successor values
    (replayNaturalEquivalence signature commands after accepted facts other assignment)
  intro n
  rw [signature.denote_successor]
  exact (replayNaturalEquivalence_successor signature commands after accepted facts other assignment n).symm

/-- The same received Peano facts interpret segment offsets. No arithmetic
constant or extra source premise is introduced. -/
theorem replay_sum_iff
    (values : ((sourceReplayFrame commands after accepted).frame.model other assignment).Valuation [])
    (first second result : signature.Carrier ((sourceReplayFrame commands after accepted).frame.model other assignment)) :
    (((sourceReplayFrame commands after accepted).frame.model other assignment).denote
      (HOL.SuccessorOrder.sum signature.zero signature.successor) values first second result).down ↔
      (replayNaturalEquivalence signature commands after accepted facts other assignment).symm result =
        (replayNaturalEquivalence signature commands after accepted facts other assignment).symm first +
        (replayNaturalEquivalence signature commands after accepted facts other assignment).symm second := by
  apply HOL.SuccessorOrder.sum_iff
    ((sourceReplayFrame commands after accepted).frame.model other assignment)
    ((sourceReplayFrame commands after accepted).frame.model_fullDomains other assignment)
    signature.successor values signature.zero
    (replayNaturalEquivalence signature commands after accepted facts other assignment)
  · rw [signature.denote_zero]
    rfl
  · intro n
    rw [signature.denote_successor]
    exact (replayNaturalEquivalence_successor signature commands after accepted facts other assignment n).symm

#print axioms replay_sum_iff

#print axioms replayNaturalEquivalence_successor
#print axioms replay_order_iff
end Mettapedia.Languages.HOLLight.NaturalModelCategoricity
