import Mettapedia.GSLT.Contracts.CoordinationFreedom

/-!
# Exactly-once take cannot be coordination free

A linear take hands one occurrence to one taker. Across locations, two results decide what any
implementation can do.

## Replicas that only merge (the CALM converse)

Fault model: replicas fire rules on their own copies and merge the copies they receive, with any
delay, reordering or duplication of deliveries (`Contracts.Coordination.CoordinationFree`). No
replica ever waits for another.

A replica's grant must be **stable**: once a replica sees that a requester holds the token, it
never learns something that withdraws the grant (`Stable`). Otherwise the requester could act on a
grant that is later handed to someone else.

* **Exactly-once allocation is not monotone** (`ExactlyOnce.not_monotone`): a lone requester is
  served and of two requesters at most one is; with stable grants, a monotone outcome would serve
  both.
* **Hence it is not coordination free** (`ExactlyOnce.not_coordinationFree`): by the converse of
  CALM, every inflationary terminating program that computes an outcome without coordination
  computes a monotone one. This holds for every representation of the replicas' state, tombstones
  included, as long as replicas only grow and merge.

The stability hypothesis is necessary. The deterministic winner rule "the least requester holds the
token" is computed without coordination and allocates exactly once, but its grants are provisional:
a replica that has seen requester `1` alone grants `1`, and withdraws the grant when it later hears
of requester `0` (`Controls.winnerRule_exactlyOnce`, `Controls.winnerRule_unstable`). Making such a
grant final needs to know that no smaller request exists: a predicate query, sound only once the
world of requests is closed, which needs a bound on delays or a coordinator.

## Partitions with availability

Fault model: the replicas are partitioned, so each answers the requests it receives from its own
view (`PartitionAnswer`). Required: a request that is the only one in the whole system is granted
(availability), and no run grants twice (exactly once).

* **No partition-tolerant, available, exactly-once take exists** (`no_available_exactlyOnce`): two
  replicas that each receive one request cannot tell that the other did, so each grants, and the
  token is taken twice. One requester asking at both replicas is enough.
* **An owner keeps exactly once and gives up availability elsewhere** (`owner_exactlyOnce`,
  `owner_unavailable`): when only the token's home replica grants, no run grants twice, and a lone
  request at another replica is refused while it is cut off.

## Monotone sends are free

A send adds a message and reads nothing; it is presence-only, so it computes its closure without
coordination (`Controls.send_coordinationFree`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ExactlyOnceTake

open Mettapedia.GSLT.Contracts.Coordination

universe u v w

/-! ## Replicas that only merge -/

section Allocation

variable {α : Type u} [CompleteLattice α] {W : Type v}

/-- A readout of grants is **stable** when a grant seen at a store is seen at every larger store. -/
def Stable (granted : α → W → Prop) : Prop :=
  ∀ {small large : α}, small ≤ large → ∀ who, granted small who → granted large who

/-- **Exactly-once allocation of one token.** `request who` is the input holding the token and the
request of `who`. A lone requester is served; of two requesters, at most one is. -/
structure ExactlyOnce (outcome : α → α) (granted : α → W → Prop) (request : W → α) : Prop where
  serves : ∀ who, granted (outcome (request who)) who
  atMostOne : ∀ first second, granted (outcome (request first ⊔ request second)) first →
    granted (outcome (request first ⊔ request second)) second → first = second

/-- **Exactly-once allocation with stable grants is not monotone.** -/
theorem ExactlyOnce.not_monotone {outcome : α → α} {granted : α → W → Prop} {request : W → α}
    (spec : ExactlyOnce outcome granted request) (stable : Stable granted) {first second : W}
    (distinct : first ≠ second) : ¬ Monotone outcome := by
  intro monotone
  apply distinct
  apply spec.atMostOne
  · exact stable (monotone le_sup_left) first (spec.serves first)
  · exact stable (monotone le_sup_right) second (spec.serves second)

/-- **Exactly-once take is not coordination free.** No inflationary program that runs every store
to quiescence computes an exactly-once allocation with stable grants by replicas that only fire
and merge. -/
theorem ExactlyOnce.not_coordinationFree {ι : Type w} {rules : ι → α → α}
    (inflationary : ∀ rule store, store ≤ rules rule store)
    (terminates : ∀ store, ∃ schedule, Quiescent rules (run rules store schedule))
    {outcome : α → α} {granted : α → W → Prop} {request : W → α}
    (spec : ExactlyOnce outcome granted request) (stable : Stable granted) {first second : W}
    (distinct : first ≠ second) : ¬ CoordinationFree rules outcome := fun free =>
  spec.not_monotone stable distinct (monotone_of_coordinationFree inflationary terminates free)

end Allocation

/-! ## Partitions with availability -/

section Partition

variable {Replica : Type u} {W : Type v}

/-- Under a partition each replica answers a request from its own view: whether replica `site`
grants the token to `who` depends only on `site` and `who`. -/
abbrev PartitionAnswer (Replica : Type u) (W : Type v) := Replica → W → Bool

/-- A run of a partitioned system: each replica receives at most one request. -/
abbrev Requests (Replica : Type u) (W : Type v) := Replica → Option W

/-- The grants of a run: the replicas whose request is granted. -/
def Grants (answer : PartitionAnswer Replica W) (requests : Requests Replica W) (site : Replica) :
    Prop :=
  ∃ who, requests site = some who ∧ answer site who = true

/-- The run in which `who` asks at `site` and nobody else asks anywhere. -/
def lone [DecidableEq Replica] (site : Replica) (who : W) : Requests Replica W :=
  fun other => if other = site then some who else none

/-- Availability: a request that is the only one in the system is granted. -/
def Available [DecidableEq Replica] (answer : PartitionAnswer Replica W) : Prop :=
  ∀ site who, answer site who = true

/-- Exactly once: no run grants the token at two replicas. -/
def AtMostOnce (answer : PartitionAnswer Replica W) : Prop :=
  ∀ requests first second, Grants answer requests first → Grants answer requests second →
    first = second

/-- The lone request is the only request of its run. -/
theorem lone_only [DecidableEq Replica] (site : Replica) (who : W) {other : Replica} {who' : W}
    (asked : lone site who other = some who') : other = site ∧ who' = who := by
  unfold lone at asked
  split_ifs at asked with same
  · exact ⟨same, (Option.some.inj asked).symm⟩

/-- **No partitioned system takes exactly once and stays available.** Two replicas that each
receive a request from their own side both grant. -/
theorem no_available_exactlyOnce [DecidableEq Replica] {answer : PartitionAnswer Replica W}
    (available : Available answer) (once : AtMostOnce answer) {first second : Replica}
    (apart : first ≠ second) (who : W) : False := by
  let both : Requests Replica W := fun other =>
    if other = first then some who else if other = second then some who else none
  have grantsFirst : Grants answer both first := ⟨who, by simp [both], available first who⟩
  have grantsSecond : Grants answer both second :=
    ⟨who, by simp [both, Ne.symm apart], available second who⟩
  exact apart (once both first second grantsFirst grantsSecond)

/-- The answer of an owner: only the token's home replica grants. -/
def ownerAnswer [DecidableEq Replica] (home : Replica) : PartitionAnswer Replica W :=
  fun site _ => decide (site = home)

/-- **An owner takes exactly once.** -/
theorem owner_exactlyOnce [DecidableEq Replica] (home : Replica) :
    AtMostOnce (ownerAnswer (W := W) home) := by
  rintro requests first second ⟨_, _, grantFirst⟩ ⟨_, _, grantSecond⟩
  simp only [ownerAnswer, decide_eq_true_eq] at grantFirst grantSecond
  rw [grantFirst, grantSecond]

/-- **An owner is unavailable across the partition**: a lone request at another replica is
refused. -/
theorem owner_unavailable [DecidableEq Replica] {home other : Replica} (apart : other ≠ home)
    (who : W) : ¬ Grants (ownerAnswer home) (lone other who) other := by
  rintro ⟨_, _, granted⟩
  simp [ownerAnswer, apart] at granted

/-- The owner serves every request on its own side. -/
theorem owner_serves_home [DecidableEq Replica] (home : Replica) (who : W) :
    Grants (ownerAnswer home) (lone home who) home :=
  ⟨who, by simp [lone], by simp [ownerAnswer]⟩

end Partition

/-! ## Controls -/

namespace Controls

/-- Facts of the allocation control: the token, a request, a grant, and a message. -/
inductive Fact where
  | token
  | request (who : ℕ)
  | grant (who : ℕ)
  | message (id : ℕ)
  deriving DecidableEq

/-- The input in which `who` requests the token. -/
def request (who : ℕ) : Set Fact := {Fact.token, Fact.request who}

/-- A grant fact is a stable readout. -/
def granted (store : Set Fact) (who : ℕ) : Prop := Fact.grant who ∈ store

theorem granted_stable : Stable granted := fun le _ held => le held

/-- `who` is the least requester present with the token. -/
def leastRequester (store : Set Fact) (who : ℕ) : Prop :=
  Fact.token ∈ store ∧ Fact.request who ∈ store ∧ ∀ other < who, Fact.request other ∉ store

/-- Grant the token to the least requester. -/
def grantLeast (store : Set Fact) : Set Fact :=
  store ∪ {fact | ∃ who, fact = Fact.grant who ∧ leastRequester store who}

theorem leastRequester_request (who : ℕ) : leastRequester (request who) who := by
  refine ⟨by simp [request], by simp [request], fun other below member => ?_⟩
  simp only [request, Set.mem_insert_iff, Set.mem_singleton_iff, reduceCtorEq, Fact.request.injEq,
    false_or] at member
  omega

theorem leastRequester_pair {first second who : ℕ}
    (least : leastRequester (request first ∪ request second) who) : who = first ∨ who = second := by
  have := least.2.1
  simp only [request, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, reduceCtorEq,
    Fact.request.injEq, false_or] at this
  exact this

theorem leastRequester_unique {store : Set Fact} {first second : ℕ}
    (leastFirst : leastRequester store first) (leastSecond : leastRequester store second) :
    first = second := by
  by_contra distinct
  rcases Nat.lt_or_gt_of_ne distinct with below | above
  · exact leastSecond.2.2 first below leastFirst.2.1
  · exact leastFirst.2.2 second above leastSecond.2.1

theorem grant_mem_grantLeast_request {first second who : ℕ}
    (member : Fact.grant who ∈ grantLeast (request first ∪ request second)) :
    leastRequester (request first ∪ request second) who := by
  rcases member with inStore | ⟨who', same, least⟩
  · simp [request] at inStore
  · rw [Fact.grant.injEq] at same
    exact same ▸ least

/-- **The specification is satisfiable**: granting to the least requester allocates exactly once. -/
theorem grantLeast_exactlyOnce : ExactlyOnce grantLeast granted request where
  serves who := Or.inr ⟨who, rfl, leastRequester_request who⟩
  atMostOne _ _ grantFirst grantSecond :=
    leastRequester_unique (grant_mem_grantLeast_request grantFirst)
      (grant_mem_grantLeast_request grantSecond)

/-- So it is not monotone, and no replicas that only merge compute it. -/
theorem grantLeast_not_monotone : ¬ Monotone grantLeast :=
  grantLeast_exactlyOnce.not_monotone granted_stable (by decide : (0 : ℕ) ≠ 1)

/-- **The deterministic winner rule** reads "least requester" off the store itself, with no rule
fired: it allocates exactly once and is monotone, hence computed without coordination. -/
theorem winnerRule_exactlyOnce : ExactlyOnce id leastRequester request where
  serves := leastRequester_request
  atMostOne _ _ first second := leastRequester_unique first second

theorem winnerRule_monotone : Monotone (id : Set Fact → Set Fact) := monotone_id

/-- **Its grants are provisional**: requester `1` alone is granted, and the grant is withdrawn when
requester `0` is heard of. -/
theorem winnerRule_unstable :
    leastRequester (request 1) 1 ∧ ¬ leastRequester (request 0 ∪ request 1) 1 ∧
      ¬ Stable leastRequester := by
  have withdrawn : ¬ leastRequester (request 0 ∪ request 1) 1 := fun least =>
    least.2.2 0 (by decide) (by simp [request])
  refine ⟨leastRequester_request 1, withdrawn, fun stable => ?_⟩
  exact withdrawn (stable Set.subset_union_right 1 (leastRequester_request 1))

/-- Sending message `id` adds it and reads nothing. -/
def send (id : ℕ) (store : Set Fact) : Set Fact := insert (Fact.message id) store

theorem send_presenceOnly : PresenceOnly send where
  monotone _ _ _ le := Set.insert_subset_insert le
  inflationary _ _ := Set.subset_insert _ _

/-- **Sends need no coordination.** -/
theorem send_coordinationFree : CoordinationFree send (closure send) :=
  coordinationFree_of_presenceOnly send_presenceOnly

/-- The partition result needs two replicas: with one replica, granting every request is
available and exactly once. -/
theorem single_replica_available :
    Available (fun (_ : Unit) (_ : ℕ) => true) ∧ AtMostOnce (fun (_ : Unit) (_ : ℕ) => true) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- Two replicas: availability and exactly once exclude each other. -/
theorem two_replicas_exclude (answer : PartitionAnswer Bool ℕ) :
    ¬ (Available answer ∧ AtMostOnce answer) := fun ⟨available, once⟩ =>
  no_available_exactlyOnce available once (by decide : true ≠ false) 0

/-- **Exactly once, negative**: counting every requester as granted serves a lone requester, and
serves both of two. (`grantLeast_exactlyOnce` is the positive control.) -/
theorem everyRequester_not_exactlyOnce :
    ¬ ExactlyOnce id (fun store who => Fact.request who ∈ store) request := fun once =>
  absurd (once.atMostOne 0 1 (by simp [request]) (by simp [request])) (by decide)

end Controls

end Mettapedia.GSLT.Coordination.ExactlyOnceTake
