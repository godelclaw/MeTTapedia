import Mettapedia.GSLT.Contracts.Quorums
import Mettapedia.GSLT.Contracts.ContractDimensions
import Mettapedia.GSLT.Contracts.ReifiedActions
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.EvidenceBridge
import Mettapedia.PLN.Evidence.SourceReliability
import Mathlib.Data.Finset.Sort
import Mettapedia.TypeTheory.Authority

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

/-! ## Provenance-aware consumers of the raw additive ledger -/

namespace Provenance

open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Evidence.EvidentialLedger
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

variable {Source Scope Trial : Type} [DecidableEq Scope] [LinearOrder Trial]

/-- Registry entries are the authenticated atomic observations of the service
profile. `none` is unfinished/under-observed, never a negative observation. -/
structure Registry (Scope Trial : Type) where
  scopeOf : Trial → Scope
  outcome : Trial → Option Bool

structure Packet (Source Scope Trial : Type) where
  reporter : Source
  scope : Scope
  roots : Finset Trial
  route : List Source

/-- A forwarded packet names its original atomic roots. Reporter labels and
routes cannot manufacture additional trials or change their registry scope. -/
def roots (registry : Registry Scope Trial) (scope : Scope) : List (Packet Source Scope Trial) → Finset Trial
  | [] => ∅
  | packet :: rest =>
      if packet.scope = scope then
        packet.roots.filter (fun trial => registry.scopeOf trial = scope) ∪ roots registry scope rest
      else roots registry scope rest

theorem roots_append (registry : Registry Scope Trial) (scope : Scope)
    (first second : List (Packet Source Scope Trial)) :
    roots registry scope (first ++ second) = roots registry scope first ∪ roots registry scope second := by
  induction first with
  | nil => simp [roots]
  | cons packet rest ih =>
      by_cases same : packet.scope = scope <;> simp [roots, same, ih, Finset.union_assoc]

def sample (registry : Registry Scope Trial) (trials : Finset Trial) : FiniteBinarySample Trial where
  trials := trials.filter (fun trial => (registry.outcome trial).isSome)
  successes := trials.filter (fun trial => registry.outcome trial = some true)
  successes_subset := by
    intro trial member
    obtain ⟨included, positive⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨included, by simp [positive]⟩

def pending (registry : Registry Scope Trial) (trials : Finset Trial) : Finset Trial :=
  trials.filter (fun trial => registry.outcome trial = none)

/-- The raw additive owner is called once per distinct registered root. Its
own list fold and source-forgetting policy are unchanged. -/
def atom (registry : Registry Scope Trial) (trial : Trial) : SourceItem Trial Unit where
  source := trial
  kind := .empirical
  support _ := match registry.outcome trial with
    | none => 0
    | some true => ⟨1, 0⟩
    | some false => ⟨0, 1⟩
  note := "registered atomic observation"

def aggregateRoots (registry : Registry Scope Trial) (trials : Finset Trial) : BinEvNat :=
  aggregate ((trials.sort (· ≤ ·)).map (atom registry)) ()

def aggregateView (registry : Registry Scope Trial) (scope : Scope)
    (packets : List (Packet Source Scope Trial)) : BinEvNat × Finset Trial :=
  let selected := roots registry scope packets
  (aggregateRoots registry selected, pending registry selected)

omit [LinearOrder Trial] in
private theorem raw_aggregate_eq_sum (items : List (SourceItem Trial Unit)) :
    aggregate items () = (items.map (fun item => item.support ())).sum := by
  induction items with
  | nil => rfl
  | cons item rest ih => rw [aggregate_cons, List.map_cons, List.sum_cons, ih]

omit [DecidableEq Scope] in
theorem aggregateRoots_eq_sum (registry : Registry Scope Trial) (trials : Finset Trial) :
    aggregateRoots registry trials = trials.sum (fun trial => (atom registry trial).support ()) := by
  rw [aggregateRoots, raw_aggregate_eq_sum, List.map_map]
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
  rfl

theorem replay_is_idempotent (registry : Registry Scope Trial) (scope : Scope)
    (packets : List (Packet Source Scope Trial)) :
    aggregateView registry scope (packets ++ packets) = aggregateView registry scope packets := by
  simp only [aggregateView, roots_append, Finset.union_self]

omit [DecidableEq Scope] in
theorem sample_union (registry : Registry Scope Trial) (first second : Finset Trial) :
    sample registry (first ∪ second) = (sample registry first).merge (sample registry second) := by
  simp only [sample, FiniteBinarySample.merge, Finset.filter_union]

omit [DecidableEq Scope] in
theorem disjoint_roots_add (registry : Registry Scope Trial) (first second : Finset Trial)
    (independent : Disjoint first second) :
    aggregateRoots registry (first ∪ second) = aggregateRoots registry first + aggregateRoots registry second ∧
      (sample registry (first ∪ second)).observations =
        Mettapedia.PLN.Evidence.Convergence.BernoulliObservations.combine
          (sample registry first).observations (sample registry second).observations := by
  refine ⟨?_, ?_⟩
  · simp only [aggregateRoots_eq_sum]
    exact Finset.sum_union independent
  · rw [sample_union]
    apply FiniteBinarySample.observations_merge_of_disjoint
    exact independent.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- Root disjointness licenses count addition; it asserts no probabilistic IID property. -/
theorem independent_packet_groups_add (registry : Registry Scope Trial) (scope : Scope)
    (first second : List (Packet Source Scope Trial))
    (independent : Disjoint (roots registry scope first) (roots registry scope second)) :
    (aggregateView registry scope (first ++ second)).1 =
      (aggregateView registry scope first).1 + (aggregateView registry scope second).1 := by
  simp only [aggregateView, roots_append]
  exact (disjoint_roots_add registry _ _ independent).1

structure Assessment (Scope Dependency : Type) where
  scope : Scope
  profile : Mettapedia.PLN.Evidence.SourceReliability.ReliabilityProfile
  dependencies : Finset Dependency
  kind : Mettapedia.PLN.Evidence.EvidenceKind

/-- Calibration is selected at the complete identity/task/context/epoch key.
An installed prior or justified indirect profile is allowed; no learner is
claimed, and selecting it does not establish any report's truth. -/
def calibrationAt {Dependency : Type} (scope : Scope) (assessment : Assessment Scope Dependency) :
    Option Mettapedia.PLN.Evidence.SourceReliability.ReliabilityProfile :=
  if assessment.scope = scope then some assessment.profile else none

def adjustedAt {Dependency : Type}
    (registry : Registry Scope Trial) (scope : Scope) (assessment : Assessment Scope Dependency)
    (packets : List (Packet Source Scope Trial)) : Option (BinEvNat × Finset Trial) :=
  (calibrationAt scope assessment).map fun profile =>
    (Mettapedia.PLN.Evidence.SourceReliability.reliabilityAdjust profile (aggregateView registry scope packets).1,
      (aggregateView registry scope packets).2)

theorem wrong_scope_does_not_transfer_calibration {Dependency : Type}
    (scope : Scope) (assessment : Assessment Scope Dependency) (different : assessment.scope ≠ scope) :
    calibrationAt scope assessment = none := by simp only [calibrationAt, if_neg different]

namespace Adoption

open Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation.Reliance
open Mettapedia.TypeTheory.AuthorityTheory
open Mettapedia.GSLT.LanguageDef.OperationCostProtocol.Indexed

variable {Dependency : Type} [DecidableEq Dependency]
variable (meaning : Dependency → Prop) {target : Mettapedia.GSLT.LanguageDef.SemanticEvidence.AdmissionObject.{0}}

structure Policy where
  requiredPositive : Nat

/-- The positive constructor means policy eligibility of conditional data,
not an inhabitant of `TypeTheory.Authority.Evidence`. An unfinished check
retains its pending trials in the incomplete constructor. -/
abbrev Choice := Mettapedia.TypeTheory.AuthorityTheory.Outcome
  (Conditional meaning target × (BinEvNat × Finset Trial)) PEmpty.{1}
  (Conditional meaning target) (Conditional meaning target × (BinEvNat × Finset Trial))

def consider (registry : Registry Scope Trial) (scope : Scope)
    (assessment : Assessment Scope Dependency) (factOf : Trial ↪ Dependency)
    (packets : List (Packet Source Scope Trial)) (policy : Policy) (result : Conditional meaning target) :
    Choice (Trial := Trial) (target := target) meaning :=
  if assessment.scope = scope then
    let observations := aggregateView registry scope packets
    let weighted := (Mettapedia.PLN.Evidence.SourceReliability.reliabilityAdjust assessment.profile observations.1,
      observations.2)
    let retained := result.require (assessment.dependencies ∪ (roots registry scope packets).image factOf)
    if policy.requiredPositive ≤ weighted.1.pos ∧ weighted.2 = ∅ then
      .established (retained, weighted)
    else .incomplete (retained, weighted)
  else .outsideFragment result

theorem eligible_retains_all_relied_on_dependencies (registry : Registry Scope Trial) (scope : Scope)
    (assessment : Assessment Scope Dependency) (factOf : Trial ↪ Dependency)
    (packets : List (Packet Source Scope Trial)) (policy : Policy) (result retained : Conditional meaning target)
    (evidence : BinEvNat × Finset Trial)
    (eligible : consider meaning registry scope assessment factOf packets policy result = .established (retained, evidence)) :
    assessment.scope = scope ∧ result.dependencies ⊆ retained.dependencies ∧
      assessment.dependencies ⊆ retained.dependencies ∧
      ∀ trial ∈ roots registry scope packets, factOf trial ∈ retained.dependencies := by
  unfold consider at eligible
  split at eligible
  · rename_i sameScope
    dsimp only at eligible
    split at eligible
    · have fields := Prod.mk.inj (Mettapedia.TypeTheory.AuthorityTheory.Outcome.established.inj eligible)
      cases fields.1
      refine ⟨sameScope, Finset.subset_union_right, ?_, ?_⟩
      · exact Finset.subset_union_left.trans Finset.subset_union_left
      · intro trial member
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨trial, member, rfl⟩))
    · cases eligible
  · cases eligible

variable {Provider Resource Authority : Type} [DecidableEq Provider] [DecidableEq Resource]
variable [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]

/-- Reputation selects a reliance candidate; the existing current-grant
adoption remains the final boundary. Every unsuccessful branch retains its
original policy outcome, including incompleteness and its exact premises. -/
def adoptChoice (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available requirement.required)]
    (active : Dependency → Bool) (choice : Choice (Trial := Trial) (target := target) meaning) :
    Except (Choice (Trial := Trial) (target := target) meaning) (Conditional meaning target × (BinEvNat × Finset Trial)) :=
  match choice with
  | .established (result, evidence) =>
      match Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation.Reliance.adopt meaning requirement current active result with
      | .ok adopted => .ok (adopted, evidence)
      | .error _ => .error choice
  | .refuted impossible => nomatch impossible
  | .outsideFragment _ | .incomplete _ => .error choice

omit [LinearOrder Trial] [DecidableEq Dependency] in
theorem adopted_choice_has_current_permission (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available requirement.required)]
    (active : Dependency → Bool) (choice : Choice (Trial := Trial) (target := target) meaning)
    (result : Conditional meaning target) (evidence : BinEvNat × Finset Trial)
    (accepted : adoptChoice meaning requirement current active choice = .ok (result, evidence)) :
    requirement.Current current ∧ ∀ dependency ∈ result.dependencies, active dependency = true := by
  cases choice with
  | established payload =>
      rcases payload with ⟨original, recorded⟩
      change (match Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation.Reliance.adopt
          meaning requirement current active original with
        | .ok adopted => (Except.ok (adopted, recorded) : Except (Choice (Trial := Trial) (target := target) meaning) _)
        | .error _ => Except.error (.established (original, recorded))) = Except.ok (result, evidence) at accepted
      cases issued : Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation.Reliance.adopt
          meaning requirement current active original with
      | error _ => simp only [issued] at accepted; cases accepted
      | ok candidate =>
          rw [issued] at accepted
          have same := Prod.mk.inj (Except.ok.inj accepted)
          obtain ⟨grant, live, rfl⟩ := adopt_admitted meaning requirement current active original candidate issued
          exact ⟨grant, by simpa only [← same.1] using live⟩
  | refuted impossible => cases impossible
  | outsideFragment _ => cases accepted
  | incomplete _ => cases accepted

def profileTarget : Mettapedia.GSLT.LanguageDef.SemanticEvidence.AdmissionObject.{0} :=
  ⟨Mettapedia.PLN.Evidence.SourceReliability.ReliabilityProfile,
    fun profile => profile.tpRate ≤ 1000 ∧ profile.tnRate ≤ 1000⟩

abbrev CalibrationStore := Mettapedia.Machines.BindingPublication.Environment Scope (Assessment Scope Dependency) Unit

/-- A profile is installed through current adoption, at the server-selected
scope requirement. Its prior/indirect provenance remains a named dependency
set. This is an installation policy, not a statistical learning algorithm. -/
def install (requiredAt : Scope → CheckedGrant.Requirement Provider Resource Authority)
    (scope : Scope) (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available (requiredAt scope).required)]
    (active : Dependency → Bool) (store : CalibrationStore (Scope := Scope) (Dependency := Dependency))
    (profile : Conditional meaning profileTarget) (kind : Mettapedia.PLN.Evidence.EvidenceKind) :
    Except (Conditional meaning profileTarget × CalibrationStore (Scope := Scope) (Dependency := Dependency))
      (CalibrationStore (Scope := Scope) (Dependency := Dependency)) :=
  match Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation.Reliance.adopt meaning (requiredAt scope) current active profile with
  | .error retained => .error (retained, store)
  | .ok admitted =>
      .ok (Mettapedia.Machines.BindingPublication.applyPatch store
        ⟨[(scope, ⟨scope, admitted.value, admitted.dependencies, kind⟩)], ()⟩)

omit [DecidableEq Dependency] in
theorem installed_profile_has_current_authority
    (requiredAt : Scope → CheckedGrant.Requirement Provider Resource Authority)
    (scope : Scope) (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available (requiredAt scope).required)]
    (active : Dependency → Bool) (store next : CalibrationStore (Scope := Scope) (Dependency := Dependency))
    (profile : Conditional meaning profileTarget) (kind : Mettapedia.PLN.Evidence.EvidenceKind)
    (accepted : install meaning requiredAt scope current active store profile kind = .ok next) :
    (requiredAt scope).Current current ∧
      next.get scope = some ⟨scope, profile.value, profile.dependencies, kind⟩ ∧
      ∀ other, other ≠ scope → next.get other = store.get other := by
  unfold install at accepted
  split at accepted
  · cases accepted
  · rename_i admitted adopted
    obtain ⟨authority, _, rfl⟩ := adopt_admitted meaning (requiredAt scope) current active profile admitted adopted
    cases Except.ok.inj accepted
    refine ⟨authority, ?_, ?_⟩
    · simp [Mettapedia.Machines.BindingPublication.applyPatch, Mettapedia.Machines.BindingPublication.applyWrites]
    · intro other different
      simp [Mettapedia.Machines.BindingPublication.applyPatch, Mettapedia.Machines.BindingPublication.applyWrites,
        Function.update_of_ne different]

def considerInstalled (registry : Registry Scope Trial) (scope : Scope)
    (store : CalibrationStore (Scope := Scope) (Dependency := Dependency)) (factOf : Trial ↪ Dependency)
    (packets : List (Packet Source Scope Trial)) (policy : Policy) (result : Conditional meaning target) :
    Choice (Trial := Trial) (target := target) meaning :=
  match store.get scope with
  | none => .incomplete (result, aggregateView registry scope packets)
  | some assessment => consider meaning registry scope assessment factOf packets policy result

end Adoption

namespace Controls

open Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation.Reliance
open Mettapedia.GSLT.LanguageDef.SemanticEvidence
open Mettapedia.GSLT.LanguageDef.OperationCostProtocol.Indexed
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.PLN.Evidence.SourceReliability

abbrev ScopeKey := Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation.Reliance.Scope Nat Nat Nat Nat

def scope : ScopeKey := ⟨7, 9, 11, 3⟩
def registry : Registry ScopeKey Nat :=
  ⟨fun trial => if trial = 3 then {scope with task := 10} else scope,
    fun trial => if trial = 2 then none else if trial = 4 then some false else some true⟩
def original : Packet Nat ScopeKey Nat := ⟨7, scope, {0}, [7]⟩
def forwarded : Packet Nat ScopeKey Nat := ⟨8, scope, {0}, [7, 8]⟩
def independent : Packet Nat ScopeKey Nat := ⟨7, scope, {1}, [7]⟩
def unfinished : Packet Nat ScopeKey Nat := ⟨7, scope, {2}, [7]⟩
def misScoped : Packet Nat ScopeKey Nat := ⟨7, {scope with task := 10}, {0}, [7]⟩

theorem correlated_forwarding_does_not_create_an_independent_trial :
    aggregate [atom registry 0, atom registry 0] () = ⟨2, 0⟩ ∧
      aggregateView registry scope [original, forwarded] = (⟨1, 0⟩, ∅) ∧
      ¬ Disjoint (roots registry scope [original]) (roots registry scope [forwarded]) := by
  simp only [aggregateView, aggregateRoots_eq_sum]
  decide

theorem independent_trials_by_one_source_remain_distinct :
    original.reporter = independent.reporter ∧
      Disjoint (roots registry scope [original]) (roots registry scope [independent]) ∧
      aggregateView registry scope [original, independent] = (⟨2, 0⟩, ∅) ∧
      (sample registry (roots registry scope [original, independent])).observations.successes = 2 := by
  simp only [aggregateView, aggregateRoots_eq_sum]
  decide

theorem unfinished_and_wrong_scope_do_not_become_negative_or_new_counts :
    aggregateView registry scope [unfinished] = (⟨0, 0⟩, {2}) ∧
      aggregateView registry scope [misScoped] = (⟨0, 0⟩, ∅) ∧
      aggregateView registry scope [⟨7, scope, {3}, [7]⟩] = (⟨0, 0⟩, ∅) ∧
      aggregateView registry scope [⟨7, scope, {4}, [7]⟩] = (⟨0, 1⟩, ∅) := by
  simp only [aggregateView, aggregateRoots_eq_sum]
  decide

/-- A model's competence is an external predicate, not a consequence of its
label, its bounded parameter fields, or the local policy's acceptance. -/
inductive Fact where
  | report (occurrence claim : Nat)
  | calibration (scope : ScopeKey) (profile : ReliabilityProfile)
  deriving DecidableEq

def meaning (calibrated : ScopeKey → ReliabilityProfile → Prop) : Fact → Prop
  | .report _ claim => claim ≠ 0
  | .calibration key profile => calibrated key profile

def factOf : Nat ↪ Fact where
  toFun trial := .report (100 + trial) 2
  inj' := by intro first second same; have equal := (Fact.report.inj same).1; omega

variable (calibrated : ScopeKey → ReliabilityProfile → Prop)

def result (claim : Nat) : Conditional (meaning calibrated) AdmissionCanary.positiveNaturals :=
  ⟨claim, {.report 50 claim}, fun supplied =>
    show claim ≠ 0 from supplied (.report 50 claim) (Finset.mem_singleton_self _)⟩

def priorProfile : Conditional (meaning calibrated) Adoption.profileTarget :=
  ⟨perfectProfile, {.calibration scope perfectProfile}, fun _ => show perfectProfile.tpRate ≤ 1000 ∧ perfectProfile.tnRate ≤ 1000 from by decide⟩

def prior : Assessment ScopeKey Fact :=
  ⟨scope, perfectProfile, {.calibration scope perfectProfile}, .expertElicited⟩
def indirect : Assessment ScopeKey Fact :=
  ⟨scope, uninformativeProfile, {.calibration scope uninformativeProfile}, .modelDerived⟩

def choice := Adoption.consider (meaning calibrated) registry scope prior factOf [original, independent]
  ⟨2⟩ (result calibrated 6)
def pendingChoice := Adoption.consider (meaning calibrated) registry scope prior factOf [original, unfinished]
  ⟨1⟩ (result calibrated 6)
def falseChoice := Adoption.consider (meaning calibrated) registry scope prior factOf [original, independent]
  ⟨2⟩ (result calibrated 0)

def choiceView {target : AdmissionObject.{0}} (value : Adoption.Choice (Trial := Nat) (meaning calibrated) (target := target)) :
    Nat × Finset Fact × BinEvNat × Finset Nat :=
  match value with
  | .established (retained, counts, pending) => (0, retained.dependencies, counts, pending)
  | .refuted impossible => nomatch impossible
  | .outsideFragment retained => (1, retained.dependencies, 0, ∅)
  | .incomplete (retained, counts, pending) => (2, retained.dependencies, counts, pending)

private theorem two_counts : aggregateView registry scope [original, independent] = (⟨2, 0⟩, ∅) :=
  independent_trials_by_one_source_remain_distinct.2.2.1

private theorem pending_counts : aggregateView registry scope [original, unfinished] = (⟨1, 0⟩, {2}) := by
  simp only [aggregateView, aggregateRoots_eq_sum]
  decide

def eligibleResult (claim : Nat) := (result calibrated claim).require
  (prior.dependencies ∪ (roots registry scope [original, independent]).image factOf)

private theorem consider_data (claim : Nat) :
    Adoption.consider (meaning calibrated) registry scope prior factOf [original, independent]
      ⟨2⟩ (result calibrated claim) = .established (eligibleResult calibrated claim, ⟨2, 0⟩, ∅) := by
  simp only [Adoption.consider]
  rw [if_pos (show prior.scope = scope from rfl)]
  rw [two_counts, show prior.profile = perfectProfile from rfl, perfect_preserves]
  rfl

theorem actual_eligible_policy_retains_report_calibration_and_trial_premises :
    choiceView calibrated (choice calibrated) =
      (0, {.report 50 6, .calibration scope perfectProfile, factOf 0, factOf 1}, ⟨2, 0⟩, ∅) := by
  rw [choice, consider_data]
  dsimp only [choiceView, eligibleResult, Conditional.require, result]
  decide

theorem perfect_prior_cannot_complete_an_unfinished_observation :
    (choiceView calibrated (pendingChoice calibrated)).1 = 2 ∧
      (choiceView calibrated (pendingChoice calibrated)).2.2.2 = {2} := by
  simp only [pendingChoice, Adoption.consider]
  rw [if_pos (show prior.scope = scope from rfl)]
  rw [pending_counts, show prior.profile = perfectProfile from rfl, perfect_preserves]
  exact ⟨rfl, rfl⟩

theorem identity_task_context_epoch_all_scope_calibration :
    calibrationAt {scope with principal := 8} prior = none ∧
      calibrationAt {scope with task := 10} prior = none ∧
      calibrationAt {scope with context := 12} prior = none ∧
      calibrationAt {scope with epoch := 4} prior = none := by decide

theorem indirect_and_prior_models_change_weights_without_forging_direct_trials :
    (adjustedAt registry scope prior [original, independent]).map Prod.fst = some ⟨2, 0⟩ ∧
      (adjustedAt registry scope indirect [original, independent]).map Prod.fst = some ⟨0, 0⟩ ∧
      roots registry scope [original, independent] = {0, 1} := by
  simp only [adjustedAt, two_counts]
  exact ⟨rfl, rfl, by decide⟩

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

def requiredAt (key : ScopeKey) : CheckedGrant.Requirement Nat ScopeKey Access := ⟨⟨0, key, 3⟩, .consume⟩
def current : CheckedGrant.View Nat ScopeKey Access := ⟨⟨0, scope, 3⟩, .consume⟩
def revoked : CheckedGrant.View Nat ScopeKey Access := ⟨⟨0, scope, 3⟩, .none⟩
def regranted : CheckedGrant.View Nat ScopeKey Access := ⟨⟨0, scope, 4⟩, .consume⟩
local instance (grant : CheckedGrant.View Nat ScopeKey Access) :
    Decidable (FrameUpdate grant.available (requiredAt scope).required) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate grant.available frame = true → Access.separate Access.consume frame = true))

def store : Adoption.CalibrationStore (Scope := ScopeKey) (Dependency := Fact) := ⟨fun _ => none, ()⟩
def installed := Adoption.install (meaning calibrated) requiredAt scope current (fun _ => true) store
  (priorProfile calibrated) .expertElicited
def installedStore : Adoption.CalibrationStore (Scope := ScopeKey) (Dependency := Fact) :=
  match installed calibrated with
  | .ok committed => committed
  | .error (_, old) => old

def installedChoice := Adoption.considerInstalled (meaning calibrated) registry scope (installedStore calibrated)
  factOf [original, independent] ⟨2⟩ (result calibrated 6)

def acceptedView {target : AdmissionObject.{0}}
    (value : Except (Adoption.Choice (Trial := Nat) (meaning calibrated) (target := target))
      (Conditional (meaning calibrated) target × (BinEvNat × Finset Nat))) : Bool × Finset Fact :=
  match value with
  | .ok (retained, _) => (true, retained.dependencies)
  | .error original => (false, (choiceView calibrated original).2.1)

theorem actual_profile_installation_changes_only_the_scoped_record :
    ((installedStore calibrated).get scope).map Assessment.dependencies = some (priorProfile calibrated).dependencies ∧
      ((installedStore calibrated).get scope).map Assessment.kind = some .expertElicited ∧
      (installedStore calibrated).get {scope with task := 10} = none ∧
      choiceView calibrated (installedChoice calibrated) = choiceView calibrated (choice calibrated) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  unfold installedChoice
  rw [Adoption.considerInstalled, show (installedStore calibrated).get scope = some prior from rfl]
  rfl

private theorem installedChoice_eq : installedChoice calibrated = choice calibrated := by
  unfold installedChoice
  rw [Adoption.considerInstalled, show (installedStore calibrated).get scope = some prior from rfl]
  rfl

theorem installed_policy_adoption_rechecks_revocation_and_generation :
    (acceptedView calibrated (Adoption.adoptChoice (meaning calibrated) (requiredAt scope) current
      (fun _ => true) (installedChoice calibrated))).1 = true ∧
      (acceptedView calibrated (Adoption.adoptChoice (meaning calibrated) (requiredAt scope) revoked
        (fun _ => true) (installedChoice calibrated))).1 = false ∧
      (acceptedView calibrated (Adoption.adoptChoice (meaning calibrated) (requiredAt scope) regranted
        (fun _ => true) (installedChoice calibrated))).1 = false ∧
      (acceptedView calibrated (Adoption.adoptChoice (meaning calibrated) (requiredAt scope) current
        (fun _ => false) (installedChoice calibrated))).1 = false := by
  simp only [installedChoice_eq, choice, consider_data, Adoption.adoptChoice, acceptedView]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem admitted_reputation_still_does_not_prove_the_report :
    (acceptedView calibrated (Adoption.adoptChoice (meaning calibrated) (requiredAt scope) current
      (fun _ => true) (falseChoice calibrated))).1 = true ∧
      ¬ AdmissionCanary.positiveNaturals.Meaning (result calibrated 0).value := by
  constructor
  · rw [falseChoice, consider_data]
    rfl
  · exact fun purported => purported rfl

end Controls

end Provenance

/-! ## Epoch-scoped peer votes and decisions from available local evidence -/

namespace Peer

open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone

variable {size : Nat}

abbrev VoteKey := Nat × Nat × Nat
abbrev GrantResource := Nat × Nat × Nat

structure Message (size : Nat) where
  sender : Fin size
  recipient : Fin size
  epoch : Nat
  task : Nat
  context : Nat
  value : Bool
  deriving DecidableEq

def Message.key (message : Message size) : VoteKey :=
  (message.epoch, message.task, message.context)

structure State (size : Nat) where
  service : Nat
  epoch : Nat
  members : Finset (Fin size)
  commitments : Fin size × VoteKey → Option Bool
  sent : List (Message size)

def initial (size service epoch : Nat) : State size :=
  ⟨service, epoch, Finset.univ, fun _ => none, []⟩

structure Request (size : Nat) where
  epoch : Nat
  task : Nat
  context : Nat
  recipient : Fin size
  value : Bool
  deriving DecidableEq

def sendHandle (state : State size) (principal : Fin size) (task context : Nat) : Handle Nat GrantResource :=
  ⟨state.service, (principal.val, task, context), state.epoch⟩

/-- The caller identity is a separately supplied service principal. The
request has no sender field. Honest senders commit to one value per epoch/
task/context; a tolerated faulty sender may equivocate under its own identity. -/
def send (faulty : Finset (Fin size)) (frontier : Frontier Nat GrantResource (Fin size))
    (state : State size) (principal : Fin size) (request : Request size) : Option (State size) :=
  if request.epoch = state.epoch ∧ principal ∈ state.members ∧ request.recipient ∈ state.members ∧
      authorizedB frontier principal (sendHandle state principal request.task request.context) = true then
    let key : VoteKey := (state.epoch, request.task, request.context)
    if principal ∈ faulty ∨ state.commitments (principal, key) = none ∨
        state.commitments (principal, key) = some request.value then
      some {state with
        commitments := Function.update state.commitments (principal, key) (some request.value)
        sent := state.sent ++ [⟨principal, request.recipient, state.epoch, request.task, request.context, request.value⟩]}
    else none
  else none

theorem send_admitted (faulty : Finset (Fin size)) (frontier : Frontier Nat GrantResource (Fin size))
    (state next : State size) (principal : Fin size) (request : Request size)
    (accepted : send faulty frontier state principal request = some next) :
    request.epoch = state.epoch ∧ principal ∈ state.members ∧ request.recipient ∈ state.members ∧
      Authorized frontier principal (sendHandle state principal request.task request.context) ∧
      (principal ∈ faulty ∨ state.commitments (principal, (state.epoch, request.task, request.context)) = none ∨
        state.commitments (principal, (state.epoch, request.task, request.context)) = some request.value) ∧
      next = {state with
        commitments := Function.update state.commitments (principal, (state.epoch, request.task, request.context)) (some request.value)
        sent := state.sent ++ [⟨principal, request.recipient, state.epoch, request.task, request.context, request.value⟩]} := by
  unfold send at accepted
  split at accepted
  · rename_i admitted
    dsimp only at accepted
    split at accepted
    · exact ⟨admitted.1, admitted.2.1, admitted.2.2.1, admitted.2.2.2, by assumption,
        (Option.some.inj accepted).symm⟩
    · cases accepted
  · cases accepted

/-- The historical log agrees with each nonfaulty sender's actual committed
value. This invariant is derived from the concrete guarded send transition. -/
def HonestLog (faulty : Finset (Fin size)) (state : State size) : Prop :=
  ∀ message ∈ state.sent, message.sender ∉ faulty →
    state.commitments (message.sender, message.key) = some message.value

theorem initial_honest (faulty : Finset (Fin size)) (service epoch : Nat) :
    HonestLog faulty (initial size service epoch) := by
  intro message member
  cases member

theorem send_honest (faulty : Finset (Fin size)) (frontier : Frontier Nat GrantResource (Fin size))
    (state next : State size) (principal : Fin size) (request : Request size)
    (before : HonestLog faulty state)
    (accepted : send faulty frontier state principal request = some next) : HonestLog faulty next := by
  obtain ⟨_, _, _, _, licensed, rfl⟩ := send_admitted faulty frontier state next principal request accepted
  intro message member honest
  rcases List.mem_append.mp member with old | fresh
  · have committed := before message old honest
    by_cases same : (message.sender, message.key) = (principal, (state.epoch, request.task, request.context))
    · have principalHonest : principal ∉ faulty := by
        have senderEqual : message.sender = principal := congrArg Prod.fst same
        simpa only [← senderEqual] using honest
      have previous := committed
      rw [same] at previous
      have value : message.value = request.value := by
        rcases licensed with bad | absent | agreed
        · exact False.elim (principalHonest bad)
        · rw [previous] at absent
          cases absent
        · exact Option.some.inj (previous.symm.trans agreed)
      change Function.update state.commitments (principal, (state.epoch, request.task, request.context))
        (some request.value) (message.sender, message.key) = some message.value
      rw [same, Function.update_self, value]
    · simpa only [Function.update_of_ne same] using committed
  · simp only [List.mem_singleton] at fresh
    subst message
    simp [Message.key]

def Step (faulty : Finset (Fin size)) (frontier : Frontier Nat GrantResource (Fin size))
    (before after : State size) : Prop :=
  ∃ principal request, send faulty frontier before principal request = some after

theorem reached_honest (faulty : Finset (Fin size)) (frontier : Frontier Nat GrantResource (Fin size))
    (start finish : State size) (initially : HonestLog faulty start)
    (trace : Relation.ReflTransGen (Step faulty frontier) start finish) : HonestLog faulty finish := by
  induction trace with
  | refl => exact initially
  | tail _ move ih =>
      obtain ⟨principal, request, accepted⟩ := move
      exact send_honest faulty frontier _ _ principal request ih accepted

theorem honest_sender_does_not_equivocate (faulty : Finset (Fin size)) (state : State size)
    (lawful : HonestLog faulty state) (first second : Message size)
    (firstSent : first ∈ state.sent) (secondSent : second ∈ state.sent)
    (samePrincipal : first.sender = second.sender) (sameKey : first.key = second.key)
    (honest : first.sender ∉ faulty) : first.value = second.value := by
  have a := lawful first firstSent honest
  have b := lawful second secondSent (by simpa only [← samePrincipal] using honest)
  rw [← samePrincipal, ← sameKey] at b
  exact Option.some.inj (a.symm.trans b)

/-- Available authenticated evidence is selected by actual log positions.
Missing positions yield no message; repeated positions do not create voters. -/
def localView (state : State size) (recipient : Fin size) (task context : Nat) (positions : List Nat) :
    List (Message size) :=
  (positions.filterMap fun index => state.sent[index]?).filter fun message =>
    message.recipient = recipient ∧ message.epoch = state.epoch ∧ message.task = task ∧ message.context = context

def voters (value : Bool) (view : List (Message size)) : Finset (Fin size) :=
  ((view.filter (fun message => message.value = value)).map Message.sender).toFinset

/-- This decision function reads only the supplied local messages. It does
not consult truth, faults, remote inboxes or a global consensus witness. -/
def decideLocal (threshold : Nat) (view : List (Message size)) : Option Bool :=
  if threshold ≤ (voters true view).card then some true
  else if threshold ≤ (voters false view).card then some false else none

theorem decided_has_quorum (threshold : Nat) (view : List (Message size)) (value : Bool)
    (decided : decideLocal threshold view = some value) : threshold ≤ (voters value view).card := by
  unfold decideLocal at decided
  split at decided
  · cases Option.some.inj decided
    assumption
  · split at decided
    · cases Option.some.inj decided
      assumption
    · cases decided

theorem voter_has_local_message (value : Bool) (view : List (Message size)) (principal : Fin size)
    (present : principal ∈ voters value view) :
    ∃ message ∈ view, message.sender = principal ∧ message.value = value := by
  obtain ⟨message, member, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
  obtain ⟨inView, agrees⟩ := List.mem_filter.mp member
  exact ⟨message, inView, equal, of_decide_eq_true agrees⟩

theorem local_message_is_authentic (state : State size) (recipient : Fin size) (task context : Nat)
    (positions : List Nat) (message : Message size) (present : message ∈ localView state recipient task context positions) :
    message ∈ state.sent ∧ message.recipient = recipient ∧ message.key = (state.epoch, task, context) := by
  obtain ⟨selected, fieldCheck⟩ := List.mem_filter.mp present
  obtain ⟨index, _, found⟩ := List.mem_filterMap.mp selected
  have fields := of_decide_eq_true fieldCheck
  exact ⟨List.mem_of_getElem? found, fields.1,
    by simp only [Message.key, fields.2.1, fields.2.2.1, fields.2.2.2]⟩

theorem honest_quorum_overlap (faulty first second : Finset (Fin 4))
    (faultBound : faulty.card ≤ 1) (firstSize : 3 ≤ first.card) (secondSize : 3 ≤ second.card) :
    ∃ principal, principal ∈ first ∧ principal ∈ second ∧ principal ∉ faulty :=
  Quorums.four_one faulty first second faultBound firstSize secondSize

theorem complement_supplies_quorum (faulty : Finset (Fin 4)) (faultBound : faulty.card ≤ 1) :
    3 ≤ (Finset.univ \ faulty).card ∧ Disjoint (Finset.univ \ faulty) faulty := by
  constructor
  · rw [Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  · exact Finset.sdiff_disjoint

theorem decisions_agree_from_available_local_views (faulty : Finset (Fin 4)) (state : State 4)
    (faultBound : faulty.card ≤ 1) (lawful : HonestLog faulty state)
    (firstRecipient secondRecipient : Fin 4) (task context : Nat) (firstPositions secondPositions : List Nat)
    (first second : Bool)
    (firstDecision : decideLocal 3 (localView state firstRecipient task context firstPositions) = some first)
    (secondDecision : decideLocal 3 (localView state secondRecipient task context secondPositions) = some second) :
    first = second := by
  obtain ⟨principal, inFirst, inSecond, honest⟩ := honest_quorum_overlap faulty _ _ faultBound
    (decided_has_quorum 3 _ first firstDecision) (decided_has_quorum 3 _ second secondDecision)
  obtain ⟨message, received, sender, value⟩ := voter_has_local_message first _ principal inFirst
  obtain ⟨message', received', sender', value'⟩ := voter_has_local_message second _ principal inSecond
  have actual := local_message_is_authentic state firstRecipient task context firstPositions message received
  have actual' := local_message_is_authentic state secondRecipient task context secondPositions message' received'
  have equal := honest_sender_does_not_equivocate faulty state lawful message message' actual.1 actual'.1
    (sender.trans sender'.symm) (actual.2.2.trans actual'.2.2.symm) (by simpa only [sender] using honest)
  exact value.symm.trans (equal.trans value')

abbrev Holdings (size : Nat) := Fin size → Excl VoteKey

def coalition (key : VoteKey) (principals : Finset (Fin size)) : Holdings size :=
  fun principal => if principal ∈ principals then .own key else .empty

theorem quorums_overlap_at_realized_honest_resource (faulty first second : Finset (Fin 4))
    (key : VoteKey) (faultBound : faulty.card ≤ 1) (firstSize : 3 ≤ first.card) (secondSize : 3 ≤ second.card) :
    ∃ principal, principal ∉ faulty ∧ coalition key first principal = .own key ∧
      coalition key second principal = .own key ∧ ¬ coalition key first ## coalition key second := by
  obtain ⟨principal, left, right, honest⟩ := honest_quorum_overlap faulty first second faultBound firstSize secondSize
  refine ⟨principal, honest, by simp [coalition, left], by simp [coalition, right], ?_⟩
  intro separate
  exact Excl.not_separate_own key key (by simpa only [coalition, if_pos left, if_pos right] using separate principal)

/-- An ordinary request word uses the same guarded handler. The fault family
is a specification parameter; the local decision procedure never receives it. -/
def issueWord (faulty : Finset (Fin size)) (frontier : Frontier Nat GrantResource (Fin size))
    (state : State size) (requests : List (Fin size × Request size)) : Option (State size) :=
  requests.foldlM (fun current request => send faulty frontier current request.1 request.2) state

theorem issued_word_honest (faulty : Finset (Fin size)) (frontier : Frontier Nat GrantResource (Fin size))
    (requests : List (Fin size × Request size)) (state finish : State size)
    (before : HonestLog faulty state) (accepted : issueWord faulty frontier state requests = some finish) :
    HonestLog faulty finish := by
  induction requests generalizing state with
  | nil => cases Option.some.inj accepted; exact before
  | cons request rest ih =>
      obtain ⟨next, issued, remaining⟩ := Option.bind_eq_some_iff.mp accepted
      exact ih next (send_honest faulty frontier state next request.1 request.2 before issued) remaining

namespace Controls

def frontier (size : Nat) : Frontier Nat GrantResource (Fin size) :=
  ((List.finRange size).map fun principal =>
    (⟨⟨17, (principal.val, 9, 11), 3⟩, principal, .owned⟩ : Lease Nat GrantResource (Fin size)))

def request {size : Nat} (recipient : Fin size) (value : Bool) : Request size := ⟨3, 9, 11, recipient, value⟩
def goodRequests : List (Fin 4 × Request 4) :=
  [(0, request 0 true), (1, request 0 true), (2, request 0 true),
   (1, request 1 true), (2, request 1 true), (3, request 1 true)]
def goodWord := issueWord {3} (frontier 4) (initial 4 17 3) goodRequests
def good : State 4 := goodWord.get (by decide)

theorem real_peer_word_has_honest_commitments : HonestLog {3} good :=
  issued_word_honest {3} (frontier 4) goodRequests (initial 4 17 3) good
    (initial_honest {3} 17 3) (by rfl)

theorem nontrivial_local_quorums_decide_with_available_authentic_messages :
    voters true (localView good 0 9 11 [0, 1, 2]) = {0, 1, 2} ∧
      voters true (localView good 1 9 11 [3, 4, 5]) = {1, 2, 3} ∧
      decideLocal 3 (localView good 0 9 11 [0, 1, 2]) = some true ∧
      decideLocal 3 (localView good 1 9 11 [3, 4, 5]) = some true := by decide

theorem any_two_actual_decisions_agree (first second : Bool)
    (firstDecision : decideLocal 3 (localView good 0 9 11 [0, 1, 2]) = some first)
    (secondDecision : decideLocal 3 (localView good 1 9 11 [3, 4, 5]) = some second) : first = second :=
  decisions_agree_from_available_local_views {3} good (by decide) real_peer_word_has_honest_commitments
    0 1 9 11 [0, 1, 2] [3, 4, 5] first second firstDecision secondDecision

theorem unseen_replayed_and_foreign_context_messages_do_not_decide :
    decideLocal 3 (localView good 0 9 11 []) = none ∧
      decideLocal 3 (localView good 0 9 11 [0, 0, 1, 999]) = none ∧
      decideLocal 3 (localView good 0 10 11 [0, 1, 2, 3, 4, 5]) = none ∧
      (⟨3, 0, 3, 9, 11, true⟩ : Message 4) ∉ localView good 0 9 11 [0, 1, 2, 3, 4, 5] := by decide

theorem wrong_epoch_missing_grant_and_honest_equivocation_are_refused :
    (send {3} (frontier 4) good 0 {request 1 false with epoch := 2}).isNone = true ∧
      (send {3} 0 good 0 (request 1 true)).isNone = true ∧
      (send {3} (frontier 4) good 0 (request 1 false)).isNone = true := by decide

def badRequests : List (Fin 3 × Request 3) :=
  [(0, request 0 true), (1, request 0 true), (1, request 2 false), (2, request 2 false)]
def badWord := issueWord {1} (frontier 3) (initial 3 17 3) badRequests
def bad : State 3 := badWord.get (by decide)

theorem faulty_overlap_has_authentic_conflicting_local_decisions :
    HonestLog {1} bad ∧
      ({0, 1} ∩ {1, 2} : Finset (Fin 3)) ⊆ {1} ∧
      decideLocal 2 (localView bad 0 9 11 [0, 1]) = some true ∧
      decideLocal 2 (localView bad 2 9 11 [2, 3]) = some false := by
  refine ⟨issued_word_honest {1} (frontier 3) badRequests (initial 3 17 3) bad
    (initial_honest {1} 17 3) (by rfl), by decide, by decide, by decide⟩

end Controls

end Peer

end Mettapedia.GSLT.Contracts.Society
