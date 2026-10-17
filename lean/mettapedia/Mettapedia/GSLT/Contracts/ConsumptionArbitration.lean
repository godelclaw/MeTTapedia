import Mettapedia.GSLT.Contracts.CoordinationFreedom
import Mettapedia.GSLT.Contracts.AuthorityControls

/-!
# Consumption needs arbitration

Two consumers of one token are not confluent: whichever fires first takes it
(`Coordination.Controls.consumption_not_confluent`).  Consumption is not
monotone, so no coordination-free execution computes it.  What it needs is
arbitration: a decision, made at one point, of which consumer takes the token.
This module proves two forms of arbitration correct on that control and relates
them to the existing contract layer.

* **The commit order decides** (`first_committer_wins`): in every schedule the
  consumer that fires first takes the token, and later consumers change
  nothing.  Optimistic transactions arbitrate this way: the first commit wins,
  and a later commit's dependency on the taken occurrence fails validation
  (`Contracts.Dependencies.printed_value_does_not_rescue`).
* **Exclusive authority decides before the race** (`gated_confluent`,
  `gated_winner`): if each consumer may fire only while it holds the consume
  right of the token, and the two rights can be held side by side, then at most
  one consumer holds the consume right (`Contracts.Access.consume_exclusive`),
  the gated program is confluent, and its outcome is the holder's, whatever the
  schedule.  Locks arbitrate this way, moving the choice from the schedule to
  the assignment of authority.

Either way the outcome is decided by an order or an assignment chosen once; no
schedule-independent outcome exists without one.  A program in which every rule
is the identity or one idempotent rule is confluent
(`confluent_of_single_rule`), which is the shape arbitration produces.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Arbitration

open Mettapedia.GSLT.Contracts.Coordination
open Mettapedia.GSLT.Contracts.Coordination.Controls
open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v

/-- Runs of a program whose rules are the identity or one idempotent rule stay
at the start or at its image. -/
theorem run_single_rule {α : Type u} {ι : Type v} {rules : ι → α → α} {f : α → α}
    (idem : ∀ s, f (f s) = f s) (only : ∀ i, rules i = f ∨ rules i = id) (s : α) (schedule : List ι) :
    run rules s schedule = s ∨ run rules s schedule = f s := by
  induction schedule generalizing s with
  | nil => exact Or.inl rfl
  | cons i rest ih =>
      rw [run_cons]
      rcases only i with hf | hid
      · rw [hf]
        rcases ih (f s) with h | h
        · exact Or.inr h
        · rw [idem] at h
          exact Or.inr h
      · rw [hid]
        exact ih s

/-- **A program whose rules are the identity or one idempotent rule is confluent.** -/
theorem confluent_of_single_rule {α : Type u} {ι : Type v} {rules : ι → α → α} {f : α → α}
    (idem : ∀ s, f (f s) = f s) (only : ∀ i, rules i = f ∨ rules i = id) : Confluent rules := by
  intro s first second quietFirst quietSecond
  by_cases some : ∃ i, rules i = f
  · obtain ⟨i, hi⟩ := some
    have fixed : ∀ r, Quiescent rules r → f r = r := fun r quiet => hi ▸ quiet i
    have toImage : ∀ schedule, Quiescent rules (run rules s schedule) →
        run rules s schedule = f s := by
      intro schedule quiet
      rcases run_single_rule idem only s schedule with h | h
      · have := fixed _ quiet
        rw [h] at this ⊢
        exact this.symm
      · exact h
    rw [toImage first quietFirst, toImage second quietSecond]
  · push Not at some
    have identity : ∀ i, rules i = id := fun i => (only i).resolve_left (some i)
    have stays : ∀ t schedule, run rules t schedule = t := by
      intro t schedule
      induction schedule generalizing t with
      | nil => rfl
      | cons i rest ih => rw [run_cons, identity i]; exact ih t
    rw [stays s first, stays s second]

/-! ## The consumption control -/

theorem consumers_without_token (i : Bool) {store : Set Token} (absent : Token.token ∉ store) :
    consumers i store = store := by
  ext fact
  cases i <;> simp only [consumers, Set.mem_union, Set.mem_ofPred_eq] <;> tauto

theorem consumers_idem (i : Bool) (store : Set Token) :
    consumers i (consumers i store) = consumers i store := by
  apply consumers_without_token
  cases i <;> simp [consumers]

/-- **The commit order decides**: the consumer that fires first takes the token,
and later firings change nothing. -/
theorem first_committer_wins (first : Bool) (rest : List Bool) :
    run consumers {Token.token} (first :: rest) = consumers first {Token.token} := by
  rw [run_cons]
  have absent : Token.token ∉ consumers first {Token.token} := by
    cases first <;> simp [consumers]
  generalize consumers first {Token.token} = store at absent ⊢
  induction rest with
  | nil => rfl
  | cons i rest ih => rw [run_cons, consumers_without_token i absent, ih]

/-- Each consumer may fire only while it holds the consume right. -/
def gated (authority : Bool → Contracts.Access) : Bool → Set Token → Set Token :=
  fun i store => if authority i = .consume then consumers i store else store

/-- **Separate rights leave at most one consumer.** -/
theorem not_both_consume {authority : Bool → Contracts.Access}
    (separate : authority true ## authority false) :
    ¬ (authority true = .consume ∧ authority false = .consume) := by
  rintro ⟨first, second⟩
  have := Contracts.Access.consume_exclusive.2 (authority false) (first ▸ separate)
  rw [second] at this
  exact absurd this (by decide)

/-- **Exclusive authority restores confluence.** -/
theorem gated_confluent (authority : Bool → Contracts.Access)
    (separate : authority true ## authority false) : Confluent (gated authority) := by
  by_cases holder : ∃ i, authority i = .consume
  · obtain ⟨i, hi⟩ := holder
    refine confluent_of_single_rule (consumers_idem i) fun j => ?_
    by_cases same : j = i
    · subst same
      left
      funext store
      simp [gated, hi]
    · right
      funext store
      have other : authority j ≠ .consume := by
        intro hj
        apply not_both_consume separate
        cases i <;> cases j <;> simp_all
      simp [gated, other]
  · push Not at holder
    refine confluent_of_single_rule (f := id) (fun _ => rfl) fun j => Or.inl ?_
    funext store
    simp [gated, holder j]

/-- **The holder of the consume right wins, whatever the schedule.** -/
theorem gated_winner {authority : Bool → Contracts.Access} {i : Bool}
    (holds : authority i = .consume) (schedule : List Bool) :
    run (gated authority) {Token.token} (i :: schedule) = consumers i {Token.token} := by
  rw [run_cons]
  have first : gated authority i {Token.token} = consumers i {Token.token} := by simp [gated, holds]
  rw [first]
  have absent : Token.token ∉ consumers i {Token.token} := by cases i <;> simp [consumers]
  generalize consumers i {Token.token} = store at absent ⊢
  induction schedule with
  | nil => rfl
  | cons j rest ih =>
      rw [run_cons]
      have : gated authority j store = store := by
        unfold gated
        split_ifs
        · exact consumers_without_token j absent
        · rfl
      rw [this, ih]

end Mettapedia.GSLT.Contracts.Arbitration
