import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Basic

/-!
# Exactly when coordination is needed: invariant confluence

A replica state is an element of a join semilattice; replicas merge by join, so merging is
idempotent, commutative and associative. A **transaction** maps a replica's state to a larger one.
An **invariant** is a predicate on states.

## Coordination-free execution

Any number of replicas (indexed by `ℕ`) start in one state. Two kinds of events, in any order:

* `commit replica transaction`: the replica runs the transaction on its own state and keeps the
  result exactly when the result satisfies the invariant. This is the whole of local validation:
  no replica consults another before committing.
* `merge source target`: the target joins the source's state into its own. A merge is never
  refused, so replicas that have heard the same transactions converge.

The system is **globally valid** when every replica satisfies the invariant after every execution
(`GloballyValid`).

## The criterion

A state is **reachable** when it is the start, or a transaction applied to a reachable state with a
valid result, or a valid join of two reachable states (`Reachable`). The transactions are
**invariant confluent** when the join of any two reachable states satisfies the invariant
(`IConfluent`), the condition of Bailis, Fekete, Franklin, Ghodsi, Hellerstein and Stoica,
*Coordination avoidance in database systems*, Proceedings of the VLDB Endowment 8(3), 2014.

* **Coordination-free execution is globally valid exactly when the transactions are invariant
  confluent** (`globallyValid_iff_iConfluent`). The forward direction builds, from any two
  reachable states, an execution that produces them on disjoint sets of replicas and merges them
  (`realize`, `realize_merge`): executions can be relocated to fresh replicas (`exec_shift`)
  and leave untouched replicas alone (`exec_of_target_ne`).
* **Merge-closed invariants are confluent** (`iConfluent_of_mergeClosed`): a constraint on each
  element, such as "every message has a valid sender", needs no coordination.

## Owned scope

When every transaction is run only by the owner of the component it writes, and the invariant is
a conjunction of one condition per owner's component, coordination-free execution is globally
valid whatever the components' conditions are (`owned_valid`). The reason: every copy of an
owner's component is one of the owner's own past values, and those form a chain, so a merge of
two copies is one of them. This is the escrow principle and the reason absence and uniqueness
are safe inside an owned scope.

## Controls

* **Mail with keyed identities is free; with per-delivery identities it duplicates**
  (`Controls.keyedMail_confluent`, `Controls.noncedMail_not_confluent`).
* **One task claimed once needs coordination** (`Controls.claims_not_confluent`,
  `Controls.claims_violated`).
* **A budget needs coordination naively** (`Controls.budget_not_confluent`), **and none when it is
  split into owned shares** (`Controls.escrow_valid`).
* **Evidence held as a set of identified observations is merged idempotently**
  (`Controls.evidence_merge_idempotent`), **while summing counts double counts a repeated
  delivery** (`Controls.summed_counts_double`).
* **Uniqueness needs coordination** (`Controls.names_not_confluent`), **except in an owned scope**
  (`Controls.ownedNames_valid`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.InvariantConfluence

universe u v w

/-! ## Coordination-free execution -/

/-- An event of a replicated system. -/
inductive Event (ι : Type v) where
  | commit (replica : ℕ) (transaction : ι)
  | merge (source target : ℕ)

namespace Event

variable {ι : Type v}

/-- The replica an event changes. -/
def target : Event ι → ℕ
  | commit replica _ => replica
  | merge _ target => target

/-- Relocate an event by `k` replicas. -/
def shift (k : ℕ) : Event ι → Event ι
  | commit replica i => commit (replica + k) i
  | merge source target => merge (source + k) (target + k)

theorem target_shift (k : ℕ) (e : Event ι) : (e.shift k).target = e.target + k := by
  cases e <;> rfl

end Event

variable {α : Type u} [SemilatticeSup α] {ι : Type v}
variable (T : ι → α → α) (I : α → Prop) [DecidablePred I]

/-- One event: a commit is kept only when its result satisfies the invariant; a merge joins. -/
def Event.apply (net : ℕ → α) : Event ι → ℕ → α
  | .commit replica i =>
      if I (T i (net replica)) then Function.update net replica (T i (net replica)) else net
  | .merge source target => Function.update net target (net target ⊔ net source)

/-- An execution. -/
def exec : (ℕ → α) → List (Event ι) → ℕ → α
  | net, [] => net
  | net, e :: es => exec (Event.apply T I net e) es

/-- **Global validity**: every replica satisfies the invariant after every execution from the
start. -/
def GloballyValid (start : α) : Prop :=
  ∀ (events : List (Event ι)) (replica : ℕ), I (exec T I (fun _ => start) events replica)

/-- **Reachable states**: the start, valid transactions of reachable states, and valid joins of
reachable states. -/
inductive Reachable (start : α) : α → Prop
  | base : Reachable start start
  | commit {state : α} (i : ι) : Reachable start state → I (T i state) →
      Reachable start (T i state)
  | merge {first second : α} : Reachable start first → Reachable start second →
      I (first ⊔ second) → Reachable start (first ⊔ second)

/-- **Invariant confluence**: the join of two reachable states is valid. -/
def IConfluent (start : α) : Prop :=
  ∀ first second, Reachable T I start first → Reachable T I start second → I (first ⊔ second)

variable {T I}

omit [DecidablePred I] in
theorem Reachable.valid {start state : α} (valid : I start) (reach : Reachable T I start state) :
    I state := by
  induction reach with
  | base => exact valid
  | commit _ _ ok _ => exact ok
  | merge _ _ ok _ _ => exact ok

theorem exec_append (net : ℕ → α) (first second : List (Event ι)) :
    exec T I net (first ++ second) = exec T I (exec T I net first) second := by
  induction first generalizing net with
  | nil => rfl
  | cons e rest ih => exact ih _

/-- An event leaves every other replica alone. -/
theorem apply_of_target_ne (net : ℕ → α) (e : Event ι) {replica : ℕ} (other : e.target ≠ replica) :
    Event.apply T I net e replica = net replica := by
  cases e with
  | commit target i =>
      simp only [Event.apply]
      split_ifs
      · exact Function.update_of_ne (Ne.symm other) _ _
      · rfl
  | merge source target => exact Function.update_of_ne (Ne.symm other) _ _

/-- **An execution leaves the replicas it never targets alone.** -/
theorem exec_of_target_ne (net : ℕ → α) (events : List (Event ι)) {replica : ℕ}
    (avoids : ∀ e ∈ events, e.target ≠ replica) : exec T I net events replica = net replica := by
  induction events generalizing net with
  | nil => rfl
  | cons e rest ih =>
      simp only [exec]
      rw [ih _ fun e' member => avoids e' (List.mem_cons_of_mem _ member)]
      exact apply_of_target_ne net e (avoids e (List.mem_cons_self ..))

theorem apply_shift (net : ℕ → α) (k : ℕ) (e : Event ι) :
    (fun j => Event.apply T I net (e.shift k) (j + k)) = Event.apply T I (fun j => net (j + k)) e := by
  funext j
  cases e with
  | commit replica i =>
      simp only [Event.shift, Event.apply]
      split_ifs
      · simp only [Function.update_apply, Nat.add_right_cancel_iff]
      · rfl
  | merge source target =>
      simp only [Event.shift, Event.apply, Function.update_apply, Nat.add_right_cancel_iff]

/-- **Executions relocate**: shifting every replica by `k` runs the same execution on the replicas
from `k` on. -/
theorem exec_shift (k : ℕ) (events : List (Event ι)) : ∀ net : ℕ → α,
    (fun j => exec T I net (events.map (Event.shift k)) (j + k)) =
      exec T I (fun j => net (j + k)) events := by
  induction events with
  | nil => intro net; rfl
  | cons e rest ih =>
      intro net
      simp only [List.map_cons, exec]
      rw [ih, apply_shift]

/-- A state produced at replica `0` by an execution that changes only replicas below `bound`. -/
def Realized (start state : α) : Prop :=
  ∃ (events : List (Event ι)) (bound : ℕ), 0 < bound ∧ (∀ e ∈ events, e.target < bound) ∧
    exec T I (fun _ => start) events 0 = state

/-- **Merging two produced states is produced**: run the first, run the second relocated past the
first's replicas, and merge. -/
theorem realize_merge {start first second : α} (realizedFirst : Realized (T := T) (I := I) start first)
    (realizedSecond : Realized (T := T) (I := I) start second) :
    Realized (T := T) (I := I) start (first ⊔ second) := by
  obtain ⟨events₁, bound₁, pos₁, below₁, eq₁⟩ := realizedFirst
  obtain ⟨events₂, bound₂, pos₂, below₂, eq₂⟩ := realizedSecond
  refine ⟨events₁ ++ events₂.map (Event.shift bound₁) ++ [.merge bound₁ 0], bound₁ + bound₂,
    by omega, ?_, ?_⟩
  · intro e member
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at member
    rcases member with (inFirst | ⟨e', inSecond, rfl⟩) | rfl
    · have := below₁ e inFirst; omega
    · rw [Event.target_shift]; have := below₂ e' inSecond; omega
    · show 0 < bound₁ + bound₂; omega
  · set net₁ := exec T I (fun _ => start) events₁
    have untouched : (fun j => net₁ (j + bound₁)) = fun _ => start := by
      funext j
      exact exec_of_target_ne _ events₁ fun e member same => by
        have := below₁ e member; omega
    have secondThere : exec T I net₁ (events₂.map (Event.shift bound₁)) bound₁ = second := by
      have := congrFun (exec_shift (T := T) (I := I) bound₁ events₂ net₁) 0
      simp only [Nat.zero_add] at this
      rw [this, untouched, eq₂]
    have firstThere : exec T I net₁ (events₂.map (Event.shift bound₁)) 0 = first := by
      rw [exec_of_target_ne _ _ fun e member same => ?_]
      · exact eq₁
      · obtain ⟨e', _, rfl⟩ := List.mem_map.mp member
        rw [Event.target_shift] at same
        omega
    rw [exec_append, exec_append]
    simp only [exec, Event.apply, Function.update_self]
    rw [firstThere, secondThere]

/-- **Every reachable state is produced by some execution.** -/
theorem realize {start state : α} (reach : Reachable T I start state) :
    Realized (T := T) (I := I) start state := by
  induction reach with
  | base => exact ⟨[], 1, by decide, by simp, rfl⟩
  | commit i _ ok ih =>
      obtain ⟨events, bound, pos, below, eq⟩ := ih
      refine ⟨events ++ [.commit 0 i], bound, pos, ?_, ?_⟩
      · intro e member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with inEvents | rfl
        · exact below e inEvents
        · exact pos
      · rw [exec_append]
        simp only [exec, Event.apply, eq, ok, if_true, Function.update_self]
  | merge _ _ _ ihFirst ihSecond => exact realize_merge ihFirst ihSecond

/-- **The criterion**: coordination-free execution is globally valid exactly when the transactions
are invariant confluent. -/
theorem globallyValid_iff_iConfluent {start : α} (valid : I start) :
    GloballyValid T I start ↔ IConfluent T I start := by
  constructor
  · intro globallyValid first second reachFirst reachSecond
    obtain ⟨events, _, _, _, eq⟩ := realize_merge (realize reachFirst) (realize reachSecond)
    rw [← eq]
    exact globallyValid events 0
  · intro confluent events replica
    suffices ∀ (net : ℕ → α), (∀ j, Reachable T I start (net j)) →
        ∀ j, Reachable T I start (exec T I net events j) from
      (this _ (fun _ => Reachable.base) replica).valid valid
    induction events with
    | nil => exact fun net reach => reach
    | cons e rest ih =>
        intro net reach
        apply ih
        intro j
        cases e with
        | commit target i =>
            simp only [Event.apply]
            split_ifs with ok
            · rw [Function.update_apply]
              split_ifs with same
              · exact Reachable.commit i (reach target) ok
              · exact reach j
            · exact reach j
        | merge source target =>
            simp only [Event.apply, Function.update_apply]
            split_ifs with same
            · exact Reachable.merge (reach target) (reach source)
                (confluent _ _ (reach target) (reach source))
            · exact reach j

omit [DecidablePred I] in
/-- **Merge-closed invariants are confluent.** -/
theorem iConfluent_of_mergeClosed {start : α} (valid : I start)
    (closed : ∀ first second, I first → I second → I (first ⊔ second)) : IConfluent T I start :=
  fun _ _ reachFirst reachSecond => closed _ _ (reachFirst.valid valid) (reachSecond.valid valid)

/-- A witness against confluence is a violating execution. -/
theorem not_globallyValid_of_witness {start first second : α} (valid : I start)
    (reachFirst : Reachable T I start first) (reachSecond : Reachable T I start second)
    (violated : ¬ I (first ⊔ second)) : ¬ GloballyValid T I start := fun globallyValid =>
  violated ((globallyValid_iff_iConfluent valid).mp globallyValid _ _ reachFirst reachSecond)

/-! ## Owned scope -/

section OwnedScope

variable {L : Type u} [DecidableEq L] {β : Type v} [SemilatticeSup β] {κ : Type w}

/-- Transactions placed at owners: transaction `k` is run by `owner k` and writes only that owner's
component, to a larger value. It may read every component of its replica. -/
structure Placed (L : Type u) (β : Type v) [SemilatticeSup β] (κ : Type w) where
  owner : κ → L
  write : κ → (L → β) → β
  grows : ∀ k state, state (owner k) ≤ write k state

/-- An event of an owned system: run a transaction at its owner, or merge two replicas. -/
inductive OwnedEvent (κ : Type w) (L : Type u) where
  | commit (k : κ)
  | merge (source target : L)

variable (P : Placed L β κ) (J : L → β → Prop) [∀ l, DecidablePred (J l)]

/-- One event of an owned system. Each location is a replica holding every component. -/
def OwnedEvent.apply (net : L → L → β) : OwnedEvent κ L → L → L → β
  | .commit k =>
      if J (P.owner k) (P.write k (net (P.owner k))) then
        Function.update net (P.owner k)
          (Function.update (net (P.owner k)) (P.owner k) (P.write k (net (P.owner k))))
      else net
  | .merge source target => Function.update net target (net target ⊔ net source)

/-- An execution of an owned system. -/
def execOwned : (L → L → β) → List (OwnedEvent κ L) → L → L → β
  | net, [] => net
  | net, e :: es => execOwned (OwnedEvent.apply P J net e) es

variable {P J}

/-- The invariant of an owned system: every copy of a component lies below the owner's own copy,
copies of one component are comparable, and every copy satisfies the component's condition. -/
structure OwnedInv (net : L → L → β) : Prop where
  below : ∀ replica l, net replica l ≤ net l l
  comparable : ∀ first second l, net first l ≤ net second l ∨ net second l ≤ net first l
  valid : ∀ replica l, J l (net replica l)

theorem ownedInv_apply {net : L → L → β} (inv : OwnedInv (J := J) net) (e : OwnedEvent κ L) :
    OwnedInv (J := J) (OwnedEvent.apply P J net e) := by
  cases e with
  | commit k =>
      simp only [OwnedEvent.apply]
      split_ifs with ok
      · have grows : net (P.owner k) (P.owner k) ≤ P.write k (net (P.owner k)) := P.grows k _
        -- the new table: only the owner's own component at the owner changes
        have entry : ∀ r l, Function.update net (P.owner k)
            (Function.update (net (P.owner k)) (P.owner k) (P.write k (net (P.owner k)))) r l =
              if r = P.owner k ∧ l = P.owner k then P.write k (net (P.owner k)) else net r l := by
          intro r l
          by_cases h₁ : r = P.owner k <;> by_cases h₂ : l = P.owner k <;>
            simp [h₁, h₂]
        refine ⟨fun r l => ?_, fun r r' l => ?_, fun r l => ?_⟩
        · rw [entry, entry]
          by_cases h : l = P.owner k
          · rw [if_pos (show l = P.owner k ∧ l = P.owner k from ⟨h, h⟩)]
            split_ifs
            · exact le_rfl
            · subst h; exact (inv.below r _).trans grows
          · rw [if_neg fun h' => h h'.2, if_neg fun h' => h h'.2]
            exact inv.below r l
        · rw [entry, entry]
          by_cases h : l = P.owner k
          · subst h
            split_ifs
            · exact Or.inl le_rfl
            · exact Or.inr ((inv.below r' _).trans grows)
            · exact Or.inl ((inv.below r _).trans grows)
            · exact inv.comparable r r' _
          · rw [if_neg fun h' => h h'.2, if_neg fun h' => h h'.2]
            exact inv.comparable r r' l
        · rw [entry]
          split_ifs with h
          · rw [h.2]; exact ok
          · exact inv.valid r l
      · exact inv
  | merge source target =>
      simp only [OwnedEvent.apply]
      -- the merged copy of each component is one of the two old copies
      have joined : ∀ l, (net target ⊔ net source) l = net target l ∨
          (net target ⊔ net source) l = net source l := by
        intro l
        rcases inv.comparable target source l with le | le
        · exact Or.inr (sup_eq_right.mpr le)
        · exact Or.inl (sup_eq_left.mpr le)
      have ownerSame : ∀ l, Function.update net target (net target ⊔ net source) l l = net l l := by
        intro l
        rw [Function.update_apply]
        split_ifs with same
        · subst same
          exact sup_eq_left.mpr (inv.below source _)
        · rfl
      have isOld : ∀ replica l, ∃ old, Function.update net target (net target ⊔ net source) replica l =
          net old l := by
        intro replica l
        rw [Function.update_apply]
        split_ifs
        · rcases joined l with h | h
          · exact ⟨target, h⟩
          · exact ⟨source, h⟩
        · exact ⟨replica, rfl⟩
      refine ⟨fun replica l => ?_, fun first second l => ?_, fun replica l => ?_⟩
      · obtain ⟨old, h⟩ := isOld replica l
        rw [h, ownerSame]
        exact inv.below old l
      · obtain ⟨old₁, h₁⟩ := isOld first l
        obtain ⟨old₂, h₂⟩ := isOld second l
        rw [h₁, h₂]
        exact inv.comparable old₁ old₂ l
      · obtain ⟨old, h⟩ := isOld replica l
        rw [h]
        exact inv.valid old l

/-- **Owned scope needs no coordination**: when every transaction runs at the owner of the one
component it writes, every replica satisfies every component's condition after every execution. -/
theorem owned_valid {start : L → β} (valid : ∀ l, J l (start l)) (events : List (OwnedEvent κ L))
    (replica l : L) : J l (execOwned P J (fun _ => start) events replica l) := by
  suffices ∀ net : L → L → β, OwnedInv (J := J) net → OwnedInv (J := J) (execOwned P J net events) from
    (this _ ⟨fun _ _ => le_rfl, fun _ _ _ => Or.inl le_rfl, fun _ l => valid l⟩).valid replica l
  induction events with
  | nil => exact fun _ inv => inv
  | cons e rest ih => exact fun net inv => ih _ (ownedInv_apply inv e)

end OwnedScope

/-! ## Controls -/

namespace Controls

/-! ### Mail -/

/-- Deliver the message whose identity is the event identifier `id`. -/
def deliverKeyed (id : ℕ) (inbox : Finset ℕ) : Finset ℕ := insert id inbox

/-- Every message in the inbox was sent: the sent events are those below `100`. -/
def onlySent (inbox : Finset ℕ) : Prop := ∀ id ∈ inbox, id < 100

instance : DecidablePred onlySent := fun inbox => by unfold onlySent; infer_instance

/-- **Mail with keyed identities is free**: "every message was sent" is merge-closed. -/
theorem keyedMail_confluent : IConfluent deliverKeyed onlySent ∅ :=
  iConfluent_of_mergeClosed (by simp [onlySent]) fun _ _ validFirst validSecond id member => by
    rcases Finset.mem_union.mp member with inFirst | inSecond
    · exact validFirst id inFirst
    · exact validSecond id inSecond

/-- Deliver an event as a fresh occurrence: the pair of the event identifier and a delivery
number. -/
def deliverNonced (delivery : ℕ × ℕ) (inbox : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  insert delivery inbox

/-- At most one entry per first component: one occurrence per event, one claim per task, one
holder per name. -/
def onePerKey (entries : Finset (ℕ × ℕ)) : Prop := ∀ x ∈ entries, ∀ y ∈ entries, x.1 = y.1 → x = y

instance : DecidablePred onePerKey := fun entries => by unfold onePerKey; infer_instance

/-- **Mail with per-delivery identities duplicates**: two gateways each deliver event `7` under
their own delivery number, and the merged inbox holds it twice. -/
theorem noncedMail_not_confluent : ¬ IConfluent deliverNonced onePerKey ∅ := by
  intro confluent
  have := confluent _ _ (Reachable.commit (7, 1) Reachable.base (by decide))
    (Reachable.commit (7, 2) Reachable.base (by decide))
  exact absurd this (by decide)

/-! ### Claims -/

/-- Worker `who` claims task `0`. -/
def claim (who : ℕ) (claims : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := insert (0, who) claims

/-- **One task claimed once needs coordination.** -/
theorem claims_not_confluent : ¬ IConfluent claim onePerKey ∅ := by
  intro confluent
  have := confluent _ _ (Reachable.commit 1 Reachable.base (by decide))
    (Reachable.commit 2 Reachable.base (by decide))
  exact absurd this (by decide)

/-- **The violating execution**: replica `0` claims for worker `1`, replica `1` for worker `2`,
then replica `0` hears of replica `1`. Each replica validated its own claim. -/
theorem claims_violated :
    exec claim onePerKey (fun _ => ∅) [.commit 0 1, .commit 1 2, .merge 1 0] 0 =
        {(0, 1), (0, 2)} ∧ ¬ onePerKey {(0, 1), (0, 2)} := by
  decide

/-- A second claim at the same replica is refused by local validation. -/
theorem claims_refused_locally :
    exec claim onePerKey (fun _ => ∅) [.commit 0 1, .commit 0 2] 0 = {(0, 1)} := by
  decide

/-! ### Budgets -/

/-- Spend one unit, recorded under the spend's identifier. -/
def spend (id : ℕ) (spent : Finset ℕ) : Finset ℕ := insert id spent

/-- At most two units are spent. -/
def withinTwo (spent : Finset ℕ) : Prop := spent.card ≤ 2

instance : DecidablePred withinTwo := fun spent => by unfold withinTwo; infer_instance

/-- **A budget needs coordination naively**: two replicas each spend the whole budget. -/
theorem budget_not_confluent : ¬ IConfluent spend withinTwo ∅ := by
  intro confluent
  have first : Reachable spend withinTwo ∅ (spend 2 (spend 1 ∅)) :=
    Reachable.commit 2 (Reachable.commit 1 Reachable.base (by decide)) (by decide)
  have second : Reachable spend withinTwo ∅ (spend 4 (spend 3 ∅)) :=
    Reachable.commit 4 (Reachable.commit 3 Reachable.base (by decide)) (by decide)
  exact absurd (confluent _ _ first second) (by decide)

/-- Escrow: share `l` spends unit `id` in its own component. -/
def escrow : Placed Bool (Finset ℕ) (Bool × ℕ) where
  owner k := k.1
  write k state := insert k.2 (state k.1)
  grows _ _ := Finset.subset_insert _ _

/-- Each of the two shares holds one unit. -/
def shareOfOne (_ : Bool) (spent : Finset ℕ) : Prop := spent.card ≤ 1

instance (l : Bool) : DecidablePred (shareOfOne l) := fun spent => by unfold shareOfOne; infer_instance

/-- **Split into owned shares, the budget needs no coordination**: whatever the interleaving of
spends at the two owners and merges, every replica sees at most two units spent. -/
theorem escrow_valid (events : List (OwnedEvent (Bool × ℕ) Bool)) (replica : Bool) :
    (execOwned escrow shareOfOne (fun _ => (fun _ => ∅)) events replica true).card +
        (execOwned escrow shareOfOne (fun _ => (fun _ => ∅)) events replica false).card ≤ 2 := by
  have own := owned_valid (P := escrow) (J := shareOfOne) (start := fun _ => ∅)
    (fun _ => by simp [shareOfOne]) events replica
  have := own true
  have := own false
  unfold shareOfOne at *
  omega

/-- The same spends without ownership: both replicas spend from share `true`, and the merged
share holds two units. -/
theorem escrow_needs_owner :
    exec (fun (id : ℕ) (spent : Finset ℕ) => insert id spent) (fun spent : Finset ℕ => spent.card ≤ 1)
        (fun _ => ∅) [.commit 0 1, .commit 1 2, .merge 1 0] 0 = {1, 2} := by
  decide

/-! ### Evidence -/

/-- Evidence held as a set of identified observations, each positive or negative. -/
abbrev Evidence := Finset (ℕ × Bool)

/-- The positive count read from a set of observations. -/
def positiveCount (evidence : Evidence) : ℕ := (evidence.filter fun x => x.2 = true).card

/-- **Evidence held as a set merges idempotently**: hearing the same observations again does not
change the count. -/
theorem evidence_merge_idempotent (evidence : Evidence) :
    positiveCount (evidence ⊔ evidence) = positiveCount evidence := by
  rw [sup_idem]

/-- Evidence held as summed counts, merged by addition. -/
def mergeCounts (first second : ℕ × ℕ) : ℕ × ℕ := (first.1 + second.1, first.2 + second.2)

/-- **Summed counts double count a repeated delivery.** -/
theorem summed_counts_double : mergeCounts (3, 1) (3, 1) = (6, 2) ∧ (6, 2) ≠ ((3, 1) : ℕ × ℕ) := by
  decide

/-! ### Uniqueness -/

/-- Register name `n` for holder `w`. -/
def register (entry : ℕ × ℕ) (names : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := insert entry names

/-- **Uniqueness needs coordination**: two replicas register one name for two holders. -/
theorem names_not_confluent : ¬ IConfluent register onePerKey ∅ := by
  intro confluent
  have := confluent _ _ (Reachable.commit (5, 1) Reachable.base (by decide))
    (Reachable.commit (5, 2) Reachable.base (by decide))
  exact absurd this (by decide)

/-- The home of a name: even names at `true`, odd names at `false`. -/
def nameHome (n : ℕ) : Bool := decide (n % 2 = 0)

/-- Registrations placed at the name's home. -/
def ownedNames : Placed Bool (Finset (ℕ × ℕ)) (ℕ × ℕ) where
  owner entry := nameHome entry.1
  write entry state := insert entry (state (nameHome entry.1))
  grows _ _ := Finset.subset_insert _ _

/-- A home's component: one holder per name, and only names homed there. -/
def homeNames (l : Bool) (names : Finset (ℕ × ℕ)) : Prop :=
  onePerKey names ∧ ∀ x ∈ names, nameHome x.1 = l

instance (l : Bool) : DecidablePred (homeNames l) := fun names => by unfold homeNames; infer_instance

/-- **Uniqueness in an owned scope needs no coordination**: on every replica, after every
execution, the registrations of both homes together hold one holder per name. -/
theorem ownedNames_valid (events : List (OwnedEvent (ℕ × ℕ) Bool)) (replica : Bool) :
    onePerKey (execOwned ownedNames homeNames (fun _ => (fun _ => ∅)) events replica true ∪
      execOwned ownedNames homeNames (fun _ => (fun _ => ∅)) events replica false) := by
  have own := owned_valid (P := ownedNames) (J := homeNames) (start := fun _ => ∅)
    (fun _ => by simp [homeNames, onePerKey]) events replica
  obtain ⟨uniqueTrue, homedTrue⟩ := own true
  obtain ⟨uniqueFalse, homedFalse⟩ := own false
  intro x inX y inY same
  rcases Finset.mem_union.mp inX with xTrue | xFalse <;>
    rcases Finset.mem_union.mp inY with yTrue | yFalse
  · exact uniqueTrue x xTrue y yTrue same
  · have := (homedTrue x xTrue).symm.trans (same ▸ homedFalse y yFalse)
    exact absurd this (by decide)
  · have := (homedFalse x xFalse).symm.trans (same ▸ homedTrue y yTrue)
    exact absurd this (by decide)
  · exact uniqueFalse x xFalse y yFalse same

/-! ### Validity, reachability, production and ownership -/

/-- **Global validity**: keyed mail is globally valid; nonced mail is not. -/
theorem globallyValid_controls :
    GloballyValid deliverKeyed onlySent ∅ ∧ ¬ GloballyValid deliverNonced onePerKey ∅ :=
  ⟨(globallyValid_iff_iConfluent (by decide)).mpr keyedMail_confluent,
    fun valid => noncedMail_not_confluent ((globallyValid_iff_iConfluent (by decide)).mp valid)⟩

/-- **Reachable states**: delivering message `1` is reachable; two claims of one key are not,
because reachable states are valid. -/
theorem reachable_controls :
    Reachable deliverKeyed onlySent ∅ (deliverKeyed 1 ∅) ∧
      ¬ Reachable claim onePerKey ∅ ({(0, 1), (0, 2)} : Finset (ℕ × ℕ)) := by
  refine ⟨.commit 1 .base (by decide), fun reach => ?_⟩
  have := Reachable.valid (by decide) reach
  revert this
  decide

/-- **Produced states**: one replica delivering message `1` produces `{1}`; no execution produces
`{100}`, which the invariant forbids. -/
theorem realized_controls :
    Realized (T := deliverKeyed) (I := onlySent) ∅ {1} ∧
      ¬ Realized (T := deliverKeyed) (I := onlySent) ∅ {100} := by
  refine ⟨⟨[.commit 0 1], 1, by decide, by simp [Event.target], ?_⟩, ?_⟩
  · simp [exec, Event.apply, deliverKeyed, onlySent]
  · rintro ⟨events, bound, -, -, produced⟩
    have valid := (globallyValid_controls.1) events 0
    rw [produced] at valid
    exact absurd (valid 100 (by simp)) (by decide)

/-- **The owned invariant**: the empty start of the escrow holds it; a replica holding two units
of share `true` that its owner has not seen does not. -/
theorem ownedInv_controls :
    OwnedInv (J := shareOfOne) (fun (_ : Bool) (_ : Bool) => (∅ : Finset ℕ)) ∧
      ¬ OwnedInv (J := shareOfOne)
        (fun (r l : Bool) => if r = false ∧ l = true then ({1, 2} : Finset ℕ) else ∅) := by
  refine ⟨⟨fun _ _ => le_rfl, fun _ _ _ => Or.inl le_rfl, fun _ _ => by simp [shareOfOne]⟩,
    fun inv => ?_⟩
  have := inv.valid false true
  revert this
  decide

end Controls

end Mettapedia.GSLT.Coordination.InvariantConfluence
