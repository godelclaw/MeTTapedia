import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ChannelAddressing
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ValidationPolicies
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Basis

/-!
# Acceptance obligations as theorems: the parallelism ladder and Alice and Bob

## The ladder of validation

Each tier says which validation suffices for a class of commits.

* **Tier 0, monotone commits** (keep and make only): no validation; every mode admits the same
  rounds (`ValidationPolicies.round_monotone_of_sublist`).
* **Tier 1, disjoint scopes**: commits scoped to disjoint sets of names are independent
  (`independent_of_disjoint_scopes`), so they run in every order, and an unchecked round of them
  is a serializable round (`ValidationPolicies.unchecked_round_serializable_of_independent`).
  Work on different channels never conflicts.
* **Tier 2, one region, disjoint occurrences**: independence is exactly disjoint occurrence
  footprints with no writes into each other's queried regions (`Exactness`); for commits
  without keeps or predicate queries the per-occurrence claim (`snapshot`) is serializable
  (`ValidationPolicies.permits_snapshot_iff_of_readFree`).
* **Tier 3, real conflicts**: waves with acyclic precedence (`Waves`), or worlds up to traces
  (`Traces`).

## Alice and Bob

Alice and Bob each receive a transfer request on their own channel, update a shared bank space,
and reply on their own reply channel, all in one commit (`Controls`):

* their transfers touch different accounts and are independent: they run in parallel, in either
  order, to one store (`alice_bob_independent`, `alice_bob_one_store`);
* two receivers competing for Alice's request clash: the request is consumed once
  (`competing_receivers_clash`);
* a persistent read of an account leaves it: two auditors are independent
  (`auditors_independent`);
* a transfer that pays from Alice's account again clashes with Alice's: no double spend
  (`double_spend_clash`);
* cancelling Alice's parked handler and waking it clash: one happens (`alice_cancel_or_wake`);
* rights: Bob's transfer is scoped to Bob's names and the bank, and leaves Alice's request
  channel as it was (`bob_leaves_alice_channel`);
* naming is not authenticating: a message whose payload claims Bob as sender can be made by
  anyone who holds the channel name (`claimed_sender_is_content`); authentication needs a seal
  or a key, not a name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v} {N : Type w}

/-- **Tier 1: commits scoped to disjoint names are independent.** -/
theorem independent_of_disjoint_scopes {label : O → R} {loc : R → N} {first second : N → Bool}
    (apart : ∀ n, first n = true → second n = true → False) {c d : Commit O R}
    (scopedC : Scoped label loc first c) (scopedD : Scoped label loc second d) :
    Independent label c d := by
  have separate : ∀ {X Y : Finset O}, (∀ o ∈ X, first (loc (label o)) = true) →
      (∀ o ∈ Y, second (loc (label o)) = true) → Disjoint X Y := by
    intro X Y inX inY
    exact Finset.disjoint_left.mpr fun o x y => apart _ (inX o x) (inY o y)
  have noWrite : ∀ {e f : Commit O R} {held held' : N → Bool},
      (∀ n, held n = true → held' n = true → False) → Scoped label loc held e →
      Scoped label loc held' f → ¬ WritesInto label e f := by
    rintro e f held held' apartHeld scopedE scopedF ⟨read, member, o, written, inRegion⟩
    have inF := scopedF.queries read member _ inRegion
    rcases Finset.mem_union.mp written with taken | made
    · exact apartHeld _ (scopedE.taken o taken) inF
    · exact apartHeld _ (scopedE.made o made) inF
  refine ⟨?_, ?_, ?_⟩
  · rintro (taken | made)
    · exact taken (separate scopedC.taken scopedD.taken)
    · exact made (separate scopedC.made scopedD.made)
  · rintro (kept | writes)
    · exact kept (separate scopedC.taken scopedD.kept)
    · exact noWrite apart scopedC scopedD writes
  · rintro (kept | writes)
    · exact kept (Finset.disjoint_left.mpr fun o taken keptC =>
        apart _ (scopedC.kept o keptC) (scopedD.taken o taken))
    · exact noWrite (fun n h h' => apart n h' h) scopedD scopedC writes

/-! ## Alice and Bob -/

namespace Controls

open Atom

/-- Names: Alice's channel `0`, Bob's `1`, the bank `2`, Alice's reply channel `3`, Bob's `4`. -/
def bankLoc : ℕ → ℕ
  | 100 => 0 | 120 => 0
  | 101 => 1 | 121 => 1
  | 110 => 2 | 111 => 2 | 112 => 2 | 130 => 2 | 132 => 2
  | 131 => 3
  | 133 => 4
  | _ => 5

/-- Labels: a name with an atom (the atom does not matter for these controls). -/
def bankLabel (o : ℕ) : ℕ × Atom := (bankLoc o, out)

/-- Alice's transfer: take her request `100`, keep her handler `120`, take her account `110`,
make the new balance `130` and the reply `131`. -/
def aliceTx : Commit ℕ (ℕ × Atom) := ⟨{100, 110}, {120}, {130, 131}, []⟩

/-- Bob's transfer: take his request `101`, keep his handler `121`, take his account `111`,
make the new balance `132` and the reply `133`. -/
def bobTx : Commit ℕ (ℕ × Atom) := ⟨{101, 111}, {121}, {132, 133}, []⟩

/-- The initial store. -/
def bankStore : Finset ℕ := {100, 101, 110, 111, 112, 120, 121}

theorem aliceTx_enabled : Enabled bankLabel bankStore aliceTx :=
  ⟨by decide, by decide, by decide, by decide, by simp [aliceTx]⟩

theorem bobTx_enabled : Enabled bankLabel bankStore bobTx :=
  ⟨by decide, by decide, by decide, by decide, by simp [bobTx]⟩

/-- **Alice and Bob are independent.** -/
theorem alice_bob_independent : Independent bankLabel aliceTx bobTx :=
  ⟨by unfold Clash; simp [aliceTx, bobTx], by unfold Spoils WritesInto; simp [aliceTx, bobTx],
    by unfold Spoils WritesInto; simp [aliceTx, bobTx]⟩

/-- **Both orders run, to one store.** -/
theorem alice_bob_one_store :
    Enabled bankLabel (fire bankStore aliceTx) bobTx ∧
      Enabled bankLabel (fire bankStore bobTx) aliceTx ∧
      fire (fire bankStore aliceTx) bobTx = fire (fire bankStore bobTx) aliceTx :=
  let both := (independent_iff_both_orders aliceTx_enabled bobTx_enabled).mp alice_bob_independent
  ⟨both.1, both.2, fire_comm aliceTx_enabled bobTx_enabled⟩

/-- A second receiver of Alice's request. -/
def rivalReceiver : Commit ℕ (ℕ × Atom) := ⟨{100}, ∅, {140}, []⟩

/-- **Competing receivers consume Alice's request once.** -/
theorem competing_receivers_clash : Clash aliceTx rivalReceiver :=
  Or.inl (by simp [aliceTx, rivalReceiver])

/-- Two auditors read the third account. -/
def auditor₁ : Commit ℕ (ℕ × Atom) := ⟨∅, {112}, {141}, []⟩

/-- The other auditor. -/
def auditor₂ : Commit ℕ (ℕ × Atom) := ⟨∅, {112}, {142}, []⟩

/-- **Persistent reads leave the account in place**: the auditors are independent. -/
theorem auditors_independent : Independent bankLabel auditor₁ auditor₂ :=
  ⟨by unfold Clash; simp [auditor₁, auditor₂], by unfold Spoils WritesInto; simp [auditor₁, auditor₂],
    by unfold Spoils WritesInto; simp [auditor₁, auditor₂]⟩

/-- Another transfer paying from Alice's account. -/
def secondPayment : Commit ℕ (ℕ × Atom) := ⟨{101, 110}, {121}, {143, 144}, []⟩

/-- **No double spend**: two transfers from Alice's account clash. -/
theorem double_spend_clash : Clash aliceTx secondPayment :=
  Or.inl (by simp [aliceTx, secondPayment])

/-- Alice's once-handler `120` woken by her request. -/
def aliceWake : Commit ℕ (ℕ × Atom) := ⟨{100, 120}, ∅, {145}, []⟩

/-- Cancel Alice's once-handler. -/
def aliceCancel : Commit ℕ (ℕ × Atom) := ⟨{120}, ∅, {146}, []⟩

/-- **Cancel or wake, exactly one.** -/
theorem alice_cancel_or_wake : Clash aliceWake aliceCancel := Or.inl (by simp [aliceWake, aliceCancel])

/-- Bob's rights: his channel, the bank, his reply channel. -/
def bobRights : ℕ → Bool := fun n => n == 1 || n == 2 || n == 4

/-- **Bob's transfer leaves Alice's request channel as it was.** -/
theorem bob_leaves_alice_channel :
    Scoped bankLabel Prod.fst bobRights bobTx ∧
      restrict bankLabel Prod.fst (fun n => n == 0) (fire bankStore bobTx) =
        restrict bankLabel Prod.fst (fun n => n == 0) bankStore := by
  refine ⟨⟨by decide, by decide, by decide, by simp [bobTx]⟩, by decide⟩

/-- Two messages on Bob's channel `1`: occurrence `150` claims sender Alice, `151` claims Bob.
The claim is part of the label, not of the rights of whoever made it. -/
def claimLabel : ℕ → ℕ × Atom
  | 150 => (1, tok)
  | 151 => (1, lock)
  | _ => (5, out)

/-- **Naming is not authenticating.** Any holder of Bob's channel name may make a message whose
content claims either sender: both commits are scoped to the same rights. -/
theorem claimed_sender_is_content :
    Scoped claimLabel Prod.fst (fun n => n == 1) ⟨∅, ∅, {150}, []⟩ ∧
      Scoped claimLabel Prod.fst (fun n => n == 1) ⟨∅, ∅, {151}, []⟩ :=
  ⟨⟨by simp, by simp, by decide, by simp⟩, ⟨by simp, by simp, by decide, by simp⟩⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
