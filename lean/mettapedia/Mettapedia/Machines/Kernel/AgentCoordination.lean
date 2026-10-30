import Mettapedia.Machines.Kernel.Delegation

/-!
# Agents coordinating through delegated authority

A small society of agents shares a resource (a mailbox) by passing capabilities to it. This is the
`Delegation` core read as a coordination layer rather than as a kernel: the subjects are agents, the
objects are the tools, mailboxes and stores they share, the grant flag permits passing grant authority
onward, and revocation withdraws a resource along the chain it was handed down. An allowed subject edge
can still authorize a use-only copy after the resource's grant flag has been dropped.

The society: the `lead` holds the mailbox with the right to pass it on and may delegate to `helperA`,
who in turn may delegate to `helperB`. No one may delegate to `stranger`.

Results:
- `helperA_canHold_mailbox`, `helperB_canHold_mailbox`: delegation reaches the helpers;
- `helperB_holds_after_delegation`: a concrete run hands the mailbox down the chain;
- `helperB_loses_mailbox_after_revoke`: the `lead` revoking its grant withdraws the mailbox from the
  whole chain at once (revocation along derivation);
- `helperB_denied_without_grant`: copying cannot restore a dropped grant flag;
- `helperB_holds_use_only_copy`: a use-only capability can still be copied along an allowed edge;
- `stranger_never_holds`: under any sequence of delegations and revocations, the `stranger` never holds
  any resource. Authority is confined to the agents reachable from the genesis grants.

The last is the safety guarantee a coordination substrate owes its participants: an agent outside the
delegation graph cannot acquire a shared capability, however the others pass and revoke among themselves.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.AgentCoordination

open Mettapedia.Machines.Kernel.Delegation

/-- The agents. `stranger` is outside the delegation graph. -/
inductive Agent where
  | lead | helperA | helperB | stranger
  deriving DecidableEq, Repr

/-- The shared resources. -/
inductive Resource where
  | mailbox
  deriving DecidableEq, Repr

open Agent Resource

/-- The genesis authority: the `lead` holds the mailbox with the right to pass it on; the `lead` may
grant to `helperA`, and `helperA` may grant to `helperB`. No capability targets `stranger`. -/
def genesis : State Agent Resource where
  caps :=
    [ ⟨0, lead, .obj mailbox, true, []⟩,
      ⟨1, lead, .subj helperA, true, []⟩,
      ⟨2, helperA, .subj helperB, true, []⟩ ]
  next := 3

/-! ## Delegation reaches the helpers -/

/-- `helperA` can obtain the mailbox: the `lead` holds it with grant and may grant to `helperA`. -/
theorem helperA_canHold_mailbox : CanHold genesis helperA (.obj mailbox) true :=
  .pass (.base ⟨⟨0, lead, .obj mailbox, true, []⟩, by decide, rfl, rfl, fun _ => rfl⟩)
        (.base ⟨⟨1, lead, .subj helperA, true, []⟩, by decide, rfl, rfl, fun _ => rfl⟩)

/-- `helperB` can obtain the mailbox, one delegation further down the chain. -/
theorem helperB_canHold_mailbox : CanHold genesis helperB (.obj mailbox) true :=
  .pass helperA_canHold_mailbox
        (.base ⟨⟨2, helperA, .subj helperB, true, []⟩, by decide, rfl, rfl, fun _ => rfl⟩)

/-- The concrete run that hands the mailbox from the `lead` down to `helperB`. -/
def delegateChain : List (Op Agent Resource) :=
  [ .pass lead (.obj mailbox) true helperA,
    .pass helperA (.obj mailbox) true helperB ]

/-- After the run, `helperB` really holds the mailbox with grant. -/
theorem helperB_holds_after_delegation :
    Holds (run genesis delegateChain) helperB (.obj mailbox) true := by
  have h0m : Holds genesis lead (.obj mailbox) true :=
    ⟨⟨0, lead, .obj mailbox, true, []⟩, by decide, rfl, rfl, fun _ => rfl⟩
  have h0a : Holds genesis lead (.subj helperA) true :=
    ⟨⟨1, lead, .subj helperA, true, []⟩, by decide, rfl, rfl, fun _ => rfl⟩
  have hAB : Holds genesis helperA (.subj helperB) true :=
    ⟨⟨2, helperA, .subj helperB, true, []⟩, by decide, rfl, rfl, fun _ => rfl⟩
  have s1A := holds_new_pass h0m h0a
  have s1AB := holds_step_pass (a := lead) (x := .obj mailbox) (g := true) (b := helperA) hAB
  have := holds_new_pass s1A s1AB
  simpa [delegateChain, run] using this

/-! ## Revocation withdraws the whole chain -/

/-- When the `lead` revokes its grant of the mailbox, `helperB`'s delegated copy disappears with it:
revocation removes every capability derived from the revoked one. -/
theorem helperB_loses_mailbox_after_revoke :
    ¬ Holds (step (run genesis delegateChain) (.revoke lead 0)) helperB (.obj mailbox) true := by
  unfold Holds; decide

/-! ## Use-only copying cannot restore grant authority -/

/-- The `lead` hands `helperA` a use-only mailbox capability, then `helperA` attempts to restore
its grant flag while passing it to `helperB`. -/
def noGrantChain : List (Op Agent Resource) :=
  [ .pass lead (.obj mailbox) false helperA,
    .pass helperA (.obj mailbox) true helperB ]

/-- This run asks `helperA` to restore the dropped grant flag. That request is refused,
so `helperB` receives neither kind of capability in this particular run. -/
theorem helperB_denied_without_grant :
    ∀ g, ¬ Holds (run genesis noGrantChain) helperB (.obj mailbox) g := by
  intro g; cases g <;> (unfold Holds; decide)

/-- Dropping the grant flag does not make a capability noncopyable. A holder with an
allowed subject edge may still pass a use-only copy, as the delegation core specifies. -/
theorem helperB_holds_use_only_copy :
    Holds (run genesis [.pass lead (.obj mailbox) false helperA,
                        .pass helperA (.obj mailbox) false helperB])
      helperB (.obj mailbox) false := by
  unfold Holds
  decide

/-- A use-only copy does not gain the grant flag. -/
theorem helperB_use_only_copy_has_no_grant :
    ¬ Holds (run genesis [.pass lead (.obj mailbox) false helperA,
                          .pass helperA (.obj mailbox) false helperB])
        helperB (.obj mailbox) true := by
  unfold Holds
  decide

/-! ## The stranger is confined out -/

/-- No genesis capability is held by `stranger`. -/
theorem no_cap_held_by_stranger : ∀ c ∈ genesis.caps, c.holder ≠ stranger := by decide

/-- No genesis capability targets `stranger`. -/
theorem no_subj_stranger_cap : ∀ c ∈ genesis.caps, c.target ≠ .subj stranger := by decide

/-- `stranger` holds nothing at the genesis. -/
theorem stranger_holds_nothing {x : Target Agent Resource} {g : Bool} :
    ¬ Holds genesis stranger x g := by
  rintro ⟨c, hc, h1, -, -⟩
  exact no_cap_held_by_stranger c hc h1

/-- No one holds a genesis capability that targets `stranger`. -/
theorem genesis_no_subj_stranger {a : Agent} {g : Bool} :
    ¬ Holds genesis a (.subj stranger) g := by
  rintro ⟨c, hc, -, h2, -⟩
  exact no_subj_stranger_cap c hc h2

/-- No reachable authority targets `stranger`: a grant capability naming `stranger` can never arise,
because none exists at the genesis and passing only copies existing targets. -/
theorem canHold_target_ne_subj_stranger {a : Agent} {x : Target Agent Resource} {g : Bool}
    (h : CanHold genesis a x g) : x ≠ .subj stranger := by
  induction h with
  | base hh => intro hx; exact genesis_no_subj_stranger (hx ▸ hh)
  | pass _ _ ih1 _ => exact ih1

/-- No reachable authority is held by `stranger`. -/
theorem canHold_holder_ne_stranger {a : Agent} {x : Target Agent Resource} {g : Bool}
    (h : CanHold genesis a x g) : a ≠ stranger := by
  induction h with
  | base hh => intro ha; exact stranger_holds_nothing (ha ▸ hh)
  | @pass a b x g _ hcb _ _ =>
      intro hb
      exact canHold_target_ne_subj_stranger hcb (by rw [hb])

/-- The coordination safety guarantee: under any sequence of delegations and revocations from the
genesis, the `stranger` never holds any resource. -/
theorem stranger_never_holds (ops : List (Op Agent Resource)) {x : Target Agent Resource} {g : Bool} :
    ¬ Holds (run genesis ops) stranger x g := by
  intro h
  exact canHold_holder_ne_stranger (holds_confined genesis ops h) rfl

end Mettapedia.Machines.Kernel.AgentCoordination
