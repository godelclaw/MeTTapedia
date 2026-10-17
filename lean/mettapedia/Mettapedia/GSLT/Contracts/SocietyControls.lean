import Mettapedia.GSLT.Contracts.ContractDimensions
import Mettapedia.GSLT.Contracts.ReifiedActions
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

/-!
# Controls for contracts among several agents

The six contract dimensions of `Mettapedia.GSLT.Contracts.Dimensions` are
read by one observer, for one set of components that all keep their
contracts.  Each dimension there is behaviour read under a declared family of
environments: in isolation, under an inserting environment, on infinite runs.
A society of agents needs three further families:

* **observers**: which agent may learn what, and which agent can tell that a
  promise was broken;
* **compliance**: which parties may break their contracts, and what the whole
  still guarantees when they do;
* **change**: who may change the world or the rules (not built here).

This module gives separating controls for the first two, a positive theorem
showing that agreement among parties who keep their contracts already follows
from the update order of authority, and a control for validating a trustee's
guarantee after publication.

## Observers: may know is not may do

`revealsSecret` branches on an item of the store that it does not own and
reports which branch it took; `ignoresSecret` does the same work without
looking.  All six readouts agree (`secret_pair_readouts`): both export no
authority and write nothing.  From a store holding the item, their traces
differ (`secret_pair_traces`).  Authority, as frame preservation, bounds what
a party may do to others' holdings, not what it may learn from them: the owner
of one cell may copy a cell another party owns into its own, preserving every
frame (`copySecond_preserves`, `copySecond_reveals`).  The
difference is a function of behaviour as the store varies; what the contract
needs in addition is the index saying which items are secret from which
observer (noninterference, Goguen and Meseguer 1982).

## Local views and joint views

A party promises to send one value to two peers.  An equivocating run sends
different values; an agreeing run sends the same.  Each peer, alone, sees
exactly the same values under the always-equivocating and the always-agreeing
party (`local_views_agree`), and no single peer can detect an equivocation
(`equivocation_not_detectable_alone`), although the pooled view detects it
(`equivocation_detectable_jointly`).  Agreement is a joint observation.  When
the first peer forwards what it received, an unsigned forward leaves the blame
open between the sender and the forwarder
(`unsigned_mismatch_blame_open`); a forward that can only repeat the sender's
actual message blames the sender (`signed_mismatch_blames_sender`).  This is
the accountability that signed, causally linked messages give in the
blocklace of Cordial Miners (Keidar, Naor, Poupko and Shapiro, DISC 2023).

## Compliance: what the whole depends on

Three parties report a fact.  Following the first party (`leader`) and taking
the majority (`majority`) agree whenever every party complies
(`agree_under_compliance`).  The sets of parties that may deviate while the
decision stays correct differ, and neither family contains the other:

* the leader rule tolerates exactly the sets that omit the first party
  (`leader_tolerates_iff`);
* the majority rule tolerates exactly the sets of at most one party
  (`majority_tolerates_iff`).

So a composite's dependence on its parties is a family of tolerated sets (a
fail-prone system in the sense of Malkhi and Reiter, *Byzantine quorum
systems*, 1998), not one set of assumptions.  Blame follows the shape: every
wrong leader decision implicates the first party (`leader_wrong_blames_first`),
while for every party there is a wrong majority decision in which that party
complied (`majority_wrong_names_nobody`).

## Coalitions that keep their contracts

Two separate holders of authority can never update to authority that cannot be
held side by side (`separate_holders_reach_separate`).  So two coalitions that
reach conflicting rights must share a holding (`conflict_needs_overlap`):
for parties that keep their contracts, quorum intersection is a consequence of
the update order.  What a deviating party does is use one exclusive share in
both coalitions, and an exclusive share is not separate from itself
(`exclusive_share_not_separate`).

## Validating a guarantee after publication

`validateThenPublish` checks the probed item before it publishes;
`publishThenValidate` publishes and checks afterwards.  Their commit and abort
decisions agree (`late_validation_same_verdicts`).  When the check fails, the
early validator has published nothing and the late one has already published
(`late_validation_keeps_publication`).  A refusal after publication is not a
rollback: what remains is a compensating obligation, which the update order of
authority, being affine, does not force.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Society

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Contracts.Dimensions

/-! ## Observers: may know is not may do -/

/-- Branches on the scratch item, which it does not own, and reports the
branch it took. -/
def revealsSecret : Prog := .ifPresent .scratch (.emit .fault .done) (.emit .served .done)

/-- The same work without looking. -/
def ignoresSecret : Prog := .tick (.emit .served .done)

/-- A store that holds the secret item. -/
def secretStore : Store := [.base, .scratch]

/-- The visible traces of every run from a store, in isolation. -/
def tracesFrom (p : Prog) (s : Store) : Finset (List Event) :=
  ((runs isolated p s).map Outcome.trace).toFinset

/-- **All six readouts agree.** -/
theorem secret_pair_readouts : readouts revealsSecret = readouts ignoresSecret := by
  decide

/-- **The traces differ once the secret is present.** -/
theorem secret_pair_traces :
    tracesFrom revealsSecret secretStore = {[.fault]} ∧
      tracesFrom ignoresSecret secretStore = {[.served]} := by
  decide

/-- Neither program exports authority. -/
theorem secret_pair_no_authority :
    (readouts revealsSecret).authority = {0} ∧ (readouts ignoresSecret).authority = {0} := by
  decide

/-- Copy the second cell into the first. -/
def copySecond : TwoCells.State → TwoCells.State → Prop := fun s s' => s' = (s.2, s.2)

/-- **Learning preserves every frame.**  The owner of the first cell copies the
second cell, which another party owns, into its own cell.  Its authority after
the step pins no value, since the value it learns is not known in advance; no
holder of any frame is broken. -/
theorem copySecond_preserves :
    ActionPreserves TwoCells.reify copySecond
      ((.own false, .empty) : TwoCells.Authority) (.empty, .empty) := by
  rintro ⟨r₁, r₂⟩ ⟨separate₁, -⟩ s ⟨-, own₂⟩ s' rfl
  have r₁empty : r₁ = .empty := by
    rcases separate₁ with owned | empty
    · cases owned
    · exact empty
  subst r₁empty
  refine ⟨⟨Or.inl rfl, Or.inl rfl⟩, ?_, ?_⟩
  · intro v owned
    cases owned
  · intro v owned
    exact own₂ v owned

/-- **The copy reveals the other party's cell**: from states that differ only
in the second cell, the first cell ends different. -/
theorem copySecond_reveals :
    copySecond (false, false) (false, false) ∧ copySecond (false, true) (true, true) :=
  ⟨rfl, rfl⟩

/-! ## Local views and joint views -/

/-- What a party sends to the first and to the second peer. -/
abbrev Sent := Bool × Bool

/-- A run that keeps the promise to send one value to both peers. -/
def Consistent (m : Sent) : Prop := m.1 = m.2

instance (m : Sent) : Decidable (Consistent m) := inferInstanceAs (Decidable (m.1 = m.2))

/-- The runs of a party that always equivocates. -/
def alwaysEquivocates : Finset Sent := {(true, false), (false, true)}

/-- The runs of a party that always agrees. -/
def alwaysAgrees : Finset Sent := {(true, true), (false, false)}

/-- **Each peer's view is the same under both parties; the joint runs
differ.** -/
theorem local_views_agree :
    alwaysEquivocates.image Prod.fst = alwaysAgrees.image Prod.fst ∧
      alwaysEquivocates.image Prod.snd = alwaysAgrees.image Prod.snd ∧
      alwaysEquivocates ≠ alwaysAgrees ∧
      (∀ m ∈ alwaysEquivocates, ¬ Consistent m) ∧ (∀ m ∈ alwaysAgrees, Consistent m) := by
  decide

/-- A breach at run `m` is detectable through a view when no run that keeps the
promise looks the same through it. -/
def DetectableBy {V : Type} (view : Sent → V) (m : Sent) : Prop :=
  ∀ m', Consistent m' → view m' ≠ view m

/-- **No single peer can detect an equivocation.** -/
theorem equivocation_not_detectable_alone (m : Sent) :
    ¬ DetectableBy Prod.fst m ∧ ¬ DetectableBy Prod.snd m :=
  ⟨fun detects => detects (m.1, m.1) rfl rfl, fun detects => detects (m.2, m.2) rfl rfl⟩

/-- **The pooled view detects every equivocation.** -/
theorem equivocation_detectable_jointly {m : Sent} (breach : ¬ Consistent m) :
    DetectableBy id m := by
  intro m' keeps same
  have equal : m' = m := same
  exact breach (equal ▸ keeps)

/-- A forwarding exchange: what the sender sent to each peer, and what the
first peer forwarded to the second. -/
structure Exchange where
  sent : Sent
  forwarded : Bool
  deriving DecidableEq

/-- The second peer's evidence: the forwarded value and its own. -/
def Exchange.evidence (e : Exchange) : Bool × Bool := (e.forwarded, e.sent.2)

/-- The sender broke its promise. -/
def Exchange.senderDeviates (e : Exchange) : Prop := ¬ Consistent e.sent

/-- The forwarder misreported what it received. -/
def Exchange.forwarderDeviates (e : Exchange) : Prop := e.forwarded ≠ e.sent.1

/-- A forward that can only repeat the sender's actual message, as a signed
message can. -/
def Exchange.Authentic (e : Exchange) : Prop := e.forwarded = e.sent.1

/-- **An unsigned forward leaves the blame open**: the same mismatched evidence
arises when only the sender deviated and when only the forwarder did. -/
theorem unsigned_mismatch_blame_open :
    ∃ e e' : Exchange, e.evidence = (true, false) ∧ e'.evidence = (true, false) ∧
      e.senderDeviates ∧ ¬ e.forwarderDeviates ∧
      e'.forwarderDeviates ∧ ¬ e'.senderDeviates := by
  refine ⟨⟨(true, false), true⟩, ⟨(false, false), true⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp [Exchange.senderDeviates, Exchange.forwarderDeviates, Consistent]

/-- **An authentic forward blames the sender**: mismatched evidence implies the
sender broke its promise. -/
theorem signed_mismatch_blames_sender (e : Exchange) (authentic : e.Authentic)
    (mismatch : e.evidence.1 ≠ e.evidence.2) : e.senderDeviates := by
  intro keeps
  apply mismatch
  change e.forwarded = e.sent.2
  rw [authentic]
  exact keeps

/-! ## Compliance: what the whole depends on -/

/-- The reports of three parties. -/
abbrev Reports := Fin 3 → Bool

/-- Every party reports the fact. -/
def compliant (v : Bool) : Reports := fun _ => v

/-- Only the parties in `faulty` may report something else. -/
def DeviatesWithin (faulty : Finset (Fin 3)) (v : Bool) (r : Reports) : Prop :=
  ∀ i, i ∉ faulty → r i = v

instance (faulty : Finset (Fin 3)) (v : Bool) (r : Reports) :
    Decidable (DeviatesWithin faulty v r) :=
  inferInstanceAs (Decidable (∀ i, i ∉ faulty → r i = v))

/-- Follow the first party. -/
def leader (r : Reports) : Bool := r 0

/-- Take the majority. -/
def majority (r : Reports) : Bool := (r 0 && r 1) || (r 0 && r 2) || (r 1 && r 2)

/-- A decision rule tolerates a set of parties when the decision is correct
whatever those parties report. -/
def Tolerates (rule : Reports → Bool) (faulty : Finset (Fin 3)) : Prop :=
  ∀ v r, DeviatesWithin faulty v r → rule r = v

instance (rule : Reports → Bool) (faulty : Finset (Fin 3)) : Decidable (Tolerates rule faulty) :=
  inferInstanceAs (Decidable (∀ v r, DeviatesWithin faulty v r → rule r = v))

/-- **Under compliance the two rules decide alike.** -/
theorem agree_under_compliance (v : Bool) :
    leader (compliant v) = v ∧ majority (compliant v) = v := by
  cases v <;> decide

/-- **The leader rule tolerates exactly the sets that omit the first party.** -/
theorem leader_tolerates_iff (faulty : Finset (Fin 3)) :
    Tolerates leader faulty ↔ (0 : Fin 3) ∉ faulty := by
  revert faulty
  decide

/-- **The majority rule tolerates exactly the sets of at most one party.** -/
theorem majority_tolerates_iff (faulty : Finset (Fin 3)) :
    Tolerates majority faulty ↔ faulty.card ≤ 1 := by
  revert faulty
  decide

/-- **Neither family of tolerated sets contains the other.** -/
theorem tolerated_families_incomparable :
    (Tolerates leader {1, 2} ∧ ¬ Tolerates majority {1, 2}) ∧
      (Tolerates majority {0} ∧ ¬ Tolerates leader {0}) := by
  decide

/-- The parties whose report is not the fact. -/
def deviators (v : Bool) (r : Reports) : Finset (Fin 3) :=
  Finset.univ.filter fun i => r i ≠ v

/-- **Every wrong leader decision implicates the first party.** -/
theorem leader_wrong_blames_first (v : Bool) (r : Reports) (wrong : leader r ≠ v) :
    (0 : Fin 3) ∈ deviators v r := by
  simpa [deviators, leader] using wrong

/-- **A wrong majority decision needs two deviators**, and for every party
there is a wrong majority decision in which that party complied: the decision
alone names nobody. -/
theorem majority_wrong_names_nobody :
    (∀ v r, majority r ≠ v → 2 ≤ (deviators v r).card) ∧
      ∀ v (i : Fin 3), ∃ r, majority r ≠ v ∧ r i = v := by
  decide

/-! ## Coalitions that keep their contracts -/

section Coalitions

universe u

variable {α : Type u} [Zero α] [Add α] [SepAlgebra α]

/-- **Separate holders reach separate authority.** -/
theorem separate_holders_reach_separate {a b r₁ r₂ : α} (separate : a ## b)
    (first : FrameUpdate a r₁) (second : FrameUpdate b r₂) : r₁ ## r₂ :=
  (first.add second separate).1

/-- **Conflicting rights need overlapping coalitions.** -/
theorem conflict_needs_overlap {a b r₁ r₂ : α} (conflict : ¬ r₁ ## r₂)
    (first : FrameUpdate a r₁) (second : FrameUpdate b r₂) : ¬ a ## b :=
  fun separate => conflict (separate_holders_reach_separate separate first second)

end Coalitions

/-- **An exclusive share is not separate from itself**: using it in two
coalitions is not a holding of the update order. -/
theorem exclusive_share_not_separate : ¬ Access.consume ## Access.consume := by
  intro self
  exact Access.consume_exclusive.1 (Access.consume_exclusive.2 _ self)

/-- **Two holdings that both update to the consume right are never separate.** -/
theorem consumers_overlap {a b : Access} (first : FrameUpdate a Access.consume)
    (second : FrameUpdate b Access.consume) : ¬ a ## b :=
  conflict_needs_overlap exclusive_share_not_separate first second

/-- Positive control: separate read holders both reach the read right. -/
theorem readers_separate :
    Access.read ## Access.read ∧ FrameUpdate Access.read Access.read :=
  ⟨Access.read_selfSeparate, FrameUpdate.refl _⟩

/-! ## Validating a guarantee after publication -/

/-- Check that the probed item is absent, then publish. -/
def validateThenPublish : Prog :=
  .ifPresent .probe (.emit .abort .done) (.emit .commit (.emit .served .done))

/-- Publish, then check that the probed item is absent. -/
def publishThenValidate : Prog :=
  .emit .served (.ifPresent .probe (.emit .abort .done) (.emit .commit .done))

/-- **The commit and abort decisions agree.** -/
theorem late_validation_same_verdicts :
    (readouts validateThenPublish).transaction = (readouts publishThenValidate).transaction := by
  decide

/-- **A failed late validation leaves the publication in place.** -/
theorem late_validation_keeps_publication :
    (completed isolated validateThenPublish).map Outcome.trace = [[.commit, .served]] ∧
      (completed isolated publishThenValidate).map Outcome.trace = [[.served, .commit]] ∧
      (completed insertProbe validateThenPublish).map Outcome.trace = [[.abort]] ∧
      (completed insertProbe publishThenValidate).map Outcome.trace = [[.served, .abort]] := by
  decide

/-! ## Axiom audit -/

#print axioms secret_pair_readouts
#print axioms secret_pair_traces
#print axioms copySecond_preserves
#print axioms local_views_agree
#print axioms equivocation_not_detectable_alone
#print axioms equivocation_detectable_jointly
#print axioms unsigned_mismatch_blame_open
#print axioms signed_mismatch_blames_sender
#print axioms leader_tolerates_iff
#print axioms majority_tolerates_iff
#print axioms tolerated_families_incomparable
#print axioms leader_wrong_blames_first
#print axioms majority_wrong_names_nobody
#print axioms conflict_needs_overlap
#print axioms exclusive_share_not_separate
#print axioms consumers_overlap
#print axioms late_validation_same_verdicts
#print axioms late_validation_keeps_publication

end Mettapedia.GSLT.Contracts.Society
