import Mettapedia.GSLT.Causality.ResourceHistoryReservations
import Mettapedia.GSLT.Causality.LocatedPermittedProjectionControls

/-!
# Actual two-receive histories reserve five and spend three

Five units are reserved from ten. The independently supplied history charges
one and two, refunds two, leaves seven live units and retains three spent
units. Reserving two produces the same algebraic final account, but its
intermediate spending is inadmissible. A final balance cannot license that
protocol retrospectively.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction.ResourceReservationControls

open OccurrenceHistory Controls LocatedProjectionControls
open Mettapedia.GSLT.Dynamics.ParallelFuelLease

noncomputable section

inductive Owner where
  | parent
  | child
  deriving DecidableEq

theorem child_ne_parent : Owner.child ≠ Owner.parent := by
  intro same
  cases same

def initial : Ledger Owner := ⟨Finsupp.single .parent 10, 0⟩

theorem initial_valid : initial.Nonnegative := by
  constructor
  · exact le_rfl
  · intro owner
    cases owner <;> simp [initial, child_ne_parent]

def receiveCharge : ∀ {site : persistentReceiver.Site}, persistentReceiver.Instance site → Nat :=
  fun {_site} => fun value : Nat => value

theorem actual_history_charges :
    wordCharges persistentReceiver @receiveCharge (persistentReceiver.pathEntries firstOriginal) =
      [1, 2] := by
  unfold wordCharges
  rw [first_projection_retains_the_complete_order]
  rfl

def final (upper : Nat) : Ledger Owner :=
  finishReservation .parent .child child_ne_parent initial upper [1, 2]

theorem accepted_history_and_refund :
    (∃ paid : OccurrencePath (funded persistentReceiver (unitPrice persistentReceiver @receiveCharge)).presentation
      (marking (leftPart LocatedHistoryControls.start) (Multiset.replicate 5 ()))
      (marking (leftPart LocatedHistoryControls.finish)
        (Multiset.replicate 5 () - Multiset.replicate 3 ())),
      (funded persistentReceiver (unitPrice persistentReceiver @receiveCharge)).pathEntries paid =
        persistentReceiver.pathEntries firstOriginal) ∧ Execution initial (final 5) := by
  have joined := reserved_history persistentReceiver @receiveCharge firstOriginal initial
    Owner.parent Owner.child child_ne_parent 5 initial_valid
      (by simp [initial, child_ne_parent]) (by norm_num [initial])
      (by rw [actual_history_charges]; decide)
  rw [actual_history_charges] at joined
  exact ⟨joined.1, joined.2.1⟩

theorem exact_overcharge_refund :
    (refundTransfer (spendWord Owner.child [1, 2]
      (reserved Owner.parent Owner.child child_ne_parent initial 5))
        Owner.child Owner.parent child_ne_parent).amount = 2 ∧
      (final 5).balances .parent = 7 ∧ (final 5).balances .child = 0 ∧ (final 5).spent = 3 := by
  have empty : initial.balances .child = 0 := by simp [initial, child_ne_parent]
  constructor
  · rw [reservation_refund_amount _ _ _ _ _ _ empty]
    norm_num
  · constructor
    · rw [final, reservation_final_parent _ _ _ _ _ _ empty]
      norm_num [initial]
    · exact ⟨reservation_final_child _ _ _ _ _ _, by rw [final, reservation_spent]; norm_num [initial]⟩

theorem final_account_independent_of_the_reservation_bound :
    (final 2).balances .parent = (final 5).balances .parent ∧
      (final 2).spent = (final 5).spent := by
  have empty : initial.balances .child = 0 := by simp [initial, child_ne_parent]
  rw [final, final, reservation_final_parent _ _ _ _ _ _ empty,
    reservation_final_parent _ _ _ _ _ _ empty, reservation_spent, reservation_spent]
  exact ⟨rfl, rfl⟩

theorem undersized_reservation_cannot_execute_the_charges :
    ¬ Execution (reserved Owner.parent Owner.child child_ne_parent initial 2)
      (spendWord Owner.child [1, 2] (reserved Owner.parent Owner.child child_ne_parent initial 2)) := by
  let grant : Transfer.Receipt (reserveMovement Owner.parent Owner.child child_ne_parent 2) initial :=
    ⟨⟨by norm_num [reserveMovement], by norm_num [reserveMovement, initial]⟩⟩
  have valid : (reserved Owner.parent Owner.child child_ne_parent initial 2).Nonnegative :=
    grant.nonnegative_after initial_valid
  intro execution
  have affordability := (spendWord_execution_iff Owner.child [1, 2] _ valid).mp execution
  rw [reserved_child _ _ _ _ _ (by simp [initial, child_ne_parent])] at affordability
  norm_num at affordability

theorem actual_prepaid_word_rejects_the_undersized_bound :
    ¬ ∃ paid : OccurrencePath (funded persistentReceiver (unitPrice persistentReceiver @receiveCharge)).presentation
      (marking (leftPart LocatedHistoryControls.start) (Multiset.replicate 2 ()))
      (marking (leftPart LocatedHistoryControls.finish)
        (Multiset.replicate 2 () - Multiset.replicate 3 ())),
      (funded persistentReceiver (unitPrice persistentReceiver @receiveCharge)).pathEntries paid =
        persistentReceiver.pathEntries firstOriginal := by
  have comparison := natural_price_history_iff persistentReceiver @receiveCharge firstOriginal 2
  rw [actual_history_charges] at comparison
  exact fun paid => (by decide : ¬ (3 ≤ 2)) (comparison.mp paid)

end

end Mettapedia.GSLT.Causality.ResourceInteraction.ResourceReservationControls
