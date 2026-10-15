import Mettapedia.GSLT.Causality.LocatedPermittedHistoryFunctor
import Mettapedia.GSLT.Causality.LocatedPermittedProjectionControls

/-!
# Dependent consumers of projected paid history receipts

Actual receipt continuation retains the source receive and its valuation.
Two orders with the same complete endpoint carry different certificates
about their first receive. No predicate on the endpoint alone represents
that dependent consumer on all original receipts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction.LocatedHistoryFunctorControls

open OccurrenceHistory Controls LocatedHistoryControls LocatedProjectionControls

def firstPaidOccurrence : Occurrence system.presentation start afterFirst :=
  ⟨(), ⟨pick 1 (Or.inl rfl) [true], by unfold System.Enables; decide,
    by change (afterFirst : Multiset (Res ⊕ (Nat × List Bool))) = _; decide⟩⟩

def secondPaidOccurrence : Occurrence system.presentation afterFirst finish :=
  ⟨(), ⟨pick 2 (Or.inr rfl) [], by unfold System.Enables; decide,
    by change (finish : Multiset (Res ⊕ (Nat × List Bool))) = _; decide⟩⟩

def paidFirstReceipt : Element system.presentation start :=
  (originElement system.presentation start).extend firstPaidOccurrence

def paidFinalReceipt : Element system.presentation start :=
  paidFirstReceipt.extend secondPaidOccurrence

def paidFinalContinuation : Element.Hom paidFirstReceipt paidFinalReceipt :=
  Element.extendHom paidFirstReceipt secondPaidOccurrence

def originalFirstReceipt : Element persistentReceiver.presentation (leftPart start) :=
  locatedHistoryReceipt persistentReceiver permitted (fun _ => 0) (fun _ => true)
    paidFirstReceipt

def originalFinalReceipt : Element persistentReceiver.presentation (leftPart start) :=
  locatedHistoryReceipt persistentReceiver permitted (fun _ => 0) (fun _ => true)
    paidFinalReceipt

def originalFinalContinuation : Element.Hom originalFirstReceipt originalFinalReceipt :=
  locatedHistoryContinuation persistentReceiver permitted (fun _ => 0) (fun _ => true)
    paidFinalContinuation

theorem actual_continuation_retains_the_second_original_receive :
    persistentReceiver.pathEntries originalFinalContinuation.rest = [⟨(), takeAgain 2⟩] :=
  rfl

theorem intermediate_and_final_receipts_have_different_values :
    (persistentReceiver.instanceValuation messageValue).onPath originalFirstReceipt.path = 20 ∧
      (persistentReceiver.instanceValuation messageValue).onPath originalFinalReceipt.path = 60 := by
  constructor
  · exact (persistentReceiver.instanceValuation_onPath messageValue originalFirstReceipt.path).trans
      (by rfl)
  · exact (persistentReceiver.instanceValuation_onPath messageValue originalFinalReceipt.path).trans
      (by rfl)

theorem actual_receipt_continuation_recovers_the_complete_original_path :
    originalFirstReceipt.path.append originalFinalContinuation.rest = originalFinalReceipt.path :=
  originalFinalContinuation.factor

def firstOrderReceipt : Element persistentReceiver.presentation (leftPart start) :=
  ⟨leftPart finish, firstOriginal⟩

def secondOrderReceipt : Element persistentReceiver.presentation (leftPart start) :=
  ⟨leftPart finish, secondOriginal⟩

def firstMessageIsOne
    (receipt : Element persistentReceiver.presentation (leftPart start)) : Prop :=
  ∃ rest, persistentReceiver.pathEntries receipt.path = ⟨(), takeAgain 1⟩ :: rest

theorem first_order_supplies_the_history_dependent_certificate :
    firstMessageIsOne firstOrderReceipt := by
  exact ⟨[⟨(), takeAgain 2⟩], first_projection_retains_the_complete_order⟩

theorem second_order_rejects_the_history_dependent_certificate :
    ¬ firstMessageIsOne secondOrderReceipt := by
  rintro ⟨rest, reading⟩
  change persistentReceiver.pathEntries secondOriginal = _ at reading
  rw [second_projection_retains_the_complete_order] at reading
  have impossible : (2 : Nat) = 1 :=
    congrArg (fun entry : persistentReceiver.Entry => (entry.2 : Nat))
      (List.cons.inj reading).1
  cases impossible

theorem equal_current_states_can_retain_distinct_receipts :
    firstOrderReceipt.target = secondOrderReceipt.target ∧
      firstOrderReceipt ≠ secondOrderReceipt := by
  refine ⟨rfl, ?_⟩
  intro same
  exact second_order_rejects_the_history_dependent_certificate
    (same ▸ first_order_supplies_the_history_dependent_certificate)

theorem history_dependent_certificate_cannot_descend_to_current_state :
    ¬ ∃ predicate : Multiset Res → Prop,
      ∀ receipt : Element persistentReceiver.presentation (leftPart start),
        firstMessageIsOne receipt ↔ predicate receipt.target := by
  rintro ⟨predicate, descends⟩
  have accepted := (descends firstOrderReceipt).mp
    first_order_supplies_the_history_dependent_certificate
  exact second_order_rejects_the_history_dependent_certificate
    ((descends secondOrderReceipt).mpr accepted)

end Mettapedia.GSLT.Causality.ResourceInteraction.LocatedHistoryFunctorControls
