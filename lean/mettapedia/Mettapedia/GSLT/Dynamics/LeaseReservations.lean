import Mettapedia.GSLT.Dynamics.LeaseSpendWords

/-!
# Reserve an upper bound and refund only unused fuel

The parent grants a declared upper bound to an empty child lease. Each
actual charge is executed separately. The child's remaining balance is then
transferred back. The complete admitted execution leaves the parent debited
by exactly the actual sum and retains that sum in the spent account.

This is a conservative reservation policy. It needs the declared upper bound
to cover the supplied charges and to be present before execution starts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ParallelFuelLease

universe uOwner

noncomputable section

variable {Owner : Type uOwner} (parent child : Owner) (distinct : child ≠ parent)

def reserveMovement (upper : Nat) : Transfer Owner :=
  ⟨parent, child, distinct.symm, upper⟩

def reserved (ledger : Ledger Owner) (upper : Nat) : Ledger Owner :=
  (reserveMovement parent child distinct upper).apply ledger

theorem reserved_child (ledger : Ledger Owner) (upper : Nat)
    (empty : ledger.balances child = 0) :
    (reserved parent child distinct ledger upper).balances child = upper := by
  have balance := Transfer.balance_at_target (reserveMovement parent child distinct upper) ledger
  simpa only [reserved, reserveMovement, empty, zero_add] using balance

theorem reserved_parent (ledger : Ledger Owner) (upper : Nat) :
    (reserved parent child distinct ledger upper).balances parent =
      ledger.balances parent - (upper : ℤ) :=
  Transfer.balance_at_source (reserveMovement parent child distinct upper) ledger

def finishReservation (ledger : Ledger Owner) (upper : Nat) (charges : List Nat) : Ledger Owner :=
  let used := spendWord child charges (reserved parent child distinct ledger upper)
  (refundTransfer used child parent distinct).apply used

theorem reservation_execution (ledger : Ledger Owner) (upper : Nat) (charges : List Nat)
    (valid : ledger.Nonnegative) (empty : ledger.balances child = 0)
    (available : (upper : ℤ) ≤ ledger.balances parent) (bounded : charges.sum ≤ upper) :
    Execution ledger (finishReservation parent child distinct ledger upper charges) := by
  let grant : Transfer.Receipt (reserveMovement parent child distinct upper) ledger :=
    ⟨⟨Nat.cast_nonneg _, available⟩⟩
  have grantedValid := grant.nonnegative_after valid
  have childBalance : grant.after.balances child = upper :=
    reserved_child parent child distinct ledger upper empty
  have chargeBound : (charges.sum : ℤ) ≤ grant.after.balances child := by
    rw [childBalance]
    exact Nat.cast_le.mpr bounded
  have spending := spendWord_execution child charges grant.after chargeBound
  let used := spendWord child charges grant.after
  let refund := refundReceipt used (spending.nonnegative_preserved grantedValid) child parent distinct
  exact (Execution.cons (.transfer _ grant) spending).append
    (.cons (.transfer _ refund) (.refl _))

theorem reservation_prefix_valid (ledger : Ledger Owner) (upper : Nat) (charges : List Nat)
    (valid : ledger.Nonnegative) (empty : ledger.balances child = 0)
    (available : (upper : ℤ) ≤ ledger.balances parent) (bounded : charges.sum ≤ upper)
    (count : Nat) :
    (spendWord child (charges.take count) (reserved parent child distinct ledger upper)).Nonnegative := by
  let grant : Transfer.Receipt (reserveMovement parent child distinct upper) ledger :=
    ⟨⟨Nat.cast_nonneg _, available⟩⟩
  apply spendWord_prefix_valid child charges grant.after (grant.nonnegative_after valid)
  rw [show grant.after.balances child = upper from reserved_child parent child distinct ledger upper empty]
  exact Nat.cast_le.mpr bounded

theorem reservation_refund_amount (ledger : Ledger Owner) (upper : Nat) (charges : List Nat)
    (empty : ledger.balances child = 0) :
    (refundTransfer (spendWord child charges (reserved parent child distinct ledger upper))
      child parent distinct).amount = (upper : ℤ) - (charges.sum : ℤ) := by
  change (spendWord child charges (reserved parent child distinct ledger upper)).balances child = _
  rw [spendWord_at_owner, reserved_child parent child distinct ledger upper empty]

theorem reservation_final_parent (ledger : Ledger Owner) (upper : Nat) (charges : List Nat)
    (empty : ledger.balances child = 0) :
    (finishReservation parent child distinct ledger upper charges).balances parent =
      ledger.balances parent - (charges.sum : ℤ) := by
  let used := spendWord child charges (reserved parent child distinct ledger upper)
  have refunded : (finishReservation parent child distinct ledger upper charges).balances parent =
      used.balances parent + used.balances child :=
    Transfer.balance_at_target (refundTransfer used child parent distinct) used
  rw [refunded]
  change (spendWord child charges (reserved parent child distinct ledger upper)).balances parent +
    (spendWord child charges (reserved parent child distinct ledger upper)).balances child = _
  rw [spendWord_at_other child charges _ distinct.symm, spendWord_at_owner,
    reserved_parent, reserved_child parent child distinct ledger upper empty]
  ring

theorem reservation_final_child (ledger : Ledger Owner) (upper : Nat) (charges : List Nat) :
    (finishReservation parent child distinct ledger upper charges).balances child = 0 := by
  let used := spendWord child charges (reserved parent child distinct ledger upper)
  have refunded : (finishReservation parent child distinct ledger upper charges).balances child =
      used.balances child - used.balances child :=
    Transfer.balance_at_source (refundTransfer used child parent distinct) used
  exact refunded.trans (sub_self _)

theorem reservation_spent (ledger : Ledger Owner) (upper : Nat) (charges : List Nat) :
    (finishReservation parent child distinct ledger upper charges).spent =
      ledger.spent + (charges.sum : ℤ) := by
  change (spendWord child charges (reserved parent child distinct ledger upper)).spent = _
  rw [spendWord_spent]
  rfl

end

end Mettapedia.GSLT.Dynamics.ParallelFuelLease
