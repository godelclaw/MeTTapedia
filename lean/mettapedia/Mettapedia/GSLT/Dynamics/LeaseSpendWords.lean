import Mettapedia.GSLT.Dynamics.ParallelFuelLease

/-!
# Complete nonnegative charge words in an existing fuel lease

Every charge is executed as its own admitted spend. An independently formed
sum gives the same final balances and irreversibly spent work. The sum fits
exactly when this word has an admitted execution from a valid ledger, and
every prefix remains valid. Refunding a reservation returns live fuel only.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ParallelFuelLease

universe uOwner

noncomputable section

variable {Owner : Type uOwner}

theorem Execution.append {source middle target : Ledger Owner}
    (first : Execution source middle) (second : Execution middle target) :
    Execution source target := by
  induction first with
  | refl => exact second
  | cons head rest ih => exact .cons head (ih second)

def spendWord (owner : Owner) : List Nat → Ledger Owner → Ledger Owner
  | [], ledger => ledger
  | charge :: rest, ledger => spendWord owner rest ((Spend.mk owner charge).apply ledger)

theorem spendWord_balances (owner : Owner) (charges : List Nat) (ledger : Ledger Owner) :
    (spendWord owner charges ledger).balances =
      ledger.balances - Finsupp.single owner (charges.sum : ℤ) := by
  induction charges generalizing ledger with
  | nil => simp [spendWord]
  | cons charge rest ih =>
      simp only [spendWord, ih, Spend.apply, List.sum_cons, Nat.cast_add,
        Finsupp.single_add, sub_sub]

theorem spendWord_spent (owner : Owner) (charges : List Nat) (ledger : Ledger Owner) :
    (spendWord owner charges ledger).spent = ledger.spent + (charges.sum : ℤ) := by
  induction charges generalizing ledger with
  | nil => simp [spendWord]
  | cons charge rest ih =>
      simp only [spendWord, ih, Spend.apply, List.sum_cons, Nat.cast_add, add_assoc]

theorem spendWord_at_owner (owner : Owner) (charges : List Nat) (ledger : Ledger Owner) :
    (spendWord owner charges ledger).balances owner =
      ledger.balances owner - (charges.sum : ℤ) := by
  rw [spendWord_balances]
  simp

theorem spendWord_at_other (owner : Owner) (charges : List Nat) (ledger : Ledger Owner)
    {other : Owner} (distinct : other ≠ owner) :
    (spendWord owner charges ledger).balances other = ledger.balances other := by
  rw [spendWord_balances]
  simp [distinct]

theorem spendWord_execution (owner : Owner) (charges : List Nat) (ledger : Ledger Owner)
    (affordable : (charges.sum : ℤ) ≤ ledger.balances owner) :
    Execution ledger (spendWord owner charges ledger) := by
  induction charges generalizing ledger with
  | nil => exact .refl _
  | cons charge rest ih =>
      have sumBound : (charge : ℤ) + (rest.sum : ℤ) ≤ ledger.balances owner := by
        simpa only [List.sum_cons, Nat.cast_add] using affordable
      have positive : 0 ≤ (rest.sum : ℤ) := Nat.cast_nonneg _
      have headBound : (charge : ℤ) ≤ ledger.balances owner := by omega
      let debit : Spend Owner := ⟨owner, charge⟩
      let receipt : Spend.Receipt debit ledger := ⟨⟨Nat.cast_nonneg _, headBound⟩⟩
      refine .cons (.spend debit receipt) (ih receipt.after ?_)
      change (rest.sum : ℤ) ≤ (debit.apply ledger).balances owner
      rw [Spend.balance_at_owner]
      change (rest.sum : ℤ) ≤ ledger.balances owner - (charge : ℤ)
      omega

theorem spendWord_execution_iff (owner : Owner) (charges : List Nat) (ledger : Ledger Owner)
    (valid : ledger.Nonnegative) :
    Execution ledger (spendWord owner charges ledger) ↔
      (charges.sum : ℤ) ≤ ledger.balances owner := by
  constructor
  · intro execution
    have nonnegative := (execution.nonnegative_preserved valid).2 owner
    rw [spendWord_at_owner] at nonnegative
    exact sub_nonneg.mp nonnegative
  · exact spendWord_execution owner charges ledger

theorem spendWord_prefix_valid (owner : Owner) (charges : List Nat) (ledger : Ledger Owner)
    (valid : ledger.Nonnegative) (affordable : (charges.sum : ℤ) ≤ ledger.balances owner)
    (count : Nat) : (spendWord owner (charges.take count) ledger).Nonnegative := by
  have prefixBound : (charges.take count).sum ≤ charges.sum :=
    (List.take_sublist count charges).sum_le_sum (fun _ _ => Nat.zero_le _)
  have castBound : ((charges.take count).sum : ℤ) ≤ (charges.sum : ℤ) :=
    Nat.cast_le.mpr prefixBound
  exact (spendWord_execution owner _ ledger (castBound.trans affordable)).nonnegative_preserved valid

end

end Mettapedia.GSLT.Dynamics.ParallelFuelLease
