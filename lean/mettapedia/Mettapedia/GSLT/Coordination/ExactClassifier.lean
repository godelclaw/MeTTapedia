import Mettapedia.GSLT.Coordination.Declarations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The coordination classifier, exact, with every verdict proved sufficient

`Declarations.required` maps a declared invariant class and the direction of a region's commits
to a mechanism. Its `free` verdicts are sound, but two things were missing: at bound `0` the count
cells it sends to coordination are invariant confluent (it is conservative there), and its `owner`
and `escrow` verdicts had no sufficiency theorem. This module closes both, and adds the column the
count table cannot see: takes that consume an occurrence for an effect.

## Exact for every bound

`requiredExact` sends the bound-`0` cells to `free`: "at most `0` live" is merge-closed (the live
set is empty exactly when everything seen is gone), and "at least `0` live" always holds.

* **Exactness** (`requiredExact_free_iff`): a cell's verdict is `free` exactly when every region of
  that class and direction, from every valid start, is invariant confluent. Where the verdict is
  not `free`, a region of the cell violates the invariant under coordination-free execution, for
  every bound (`atMost_succ_make_needs`, `atLeast_succ_take_needs`).
* **Agreement with `required`** (`required_eq_requiredExact`): the two classifiers agree on every
  cell with a positive bound, and on the merge-closed and general rows. At bound `0`
  (`required_conservative_at_zero`) the older one says coordination where none is needed.

## The verdicts are sufficient

* **Owner** (`owner_sufficient`): if every transaction of a region runs at one home and other
  replicas only merge, every replica satisfies the region's invariant after every execution,
  whatever the invariant is. This is the owned scope of `InvariantConfluence.owned_valid` with one
  owner. At the level of commits it is `HomeLocation.run_refines`.
* **Escrow of a surplus** (`escrow_atLeast_sufficient`): for "at least `k` live", give each
  location a share of the surplus and let it take at most its share. Then every replica sees at
  least `k` live, under any interleaving of takes, makes and merges.
* **Escrow of a capacity** (`escrow_atMost_sufficient`): for "at most `k` live", give each location
  a share of the free capacity and let it make at most its share. Then every replica sees at most
  `k` live.

## Consuming takes

The count table treats a take as the removal of an occurrence; two replicas removing one
occurrence remove it once. A take that **consumes** the occurrence for an effect is different: two
replicas consuming one occurrence produce two effects.

* **Consumption with differing effects needs coordination** (`consume_needs`): two replicas each
  consume occurrence `0`, one recording effect `1` and the other effect `2`; the merge records two
  effects of one consumption. This is the exactly-once take of `ExactlyOnceTake` in the replica
  model.
* **Consumption whose effect is a function of the consumed occurrence is free**
  (`consume_deterministic_free`): repeated consumption records the same effect, so the merge is
  valid. Deterministic, idempotent effects make double consumption harmless.

`classify` adds this column: a region with consuming takes whose effects are not determined by the
occurrence needs an owner (or a lease at the owner, when takers may crash), whatever its count
class.

## Controls

* `Controls.escrow_oversubscribed`: shares that add up to more than the surplus let two locations
  take the minimum away.
* `Controls.owner_routing_needed`: the same claims run at two replicas violate the invariant that
  the owner keeps.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ExactClassifier

open Mettapedia.GSLT.Coordination.InvariantConfluence
open Mettapedia.GSLT.Coordination.ReplicaMerge
open Mettapedia.GSLT.Coordination.Declarations

universe u v w

/-! ## Operations on a region -/

theorem op_le (op : Op) (s : Region) : s ≤ op.apply s := by
  cases op with
  | make id => exact ⟨Finset.subset_insert _ _, le_rfl⟩
  | take id => exact ⟨le_rfl, Finset.subset_insert _ _⟩

theorem live_sup (s t : Region) : Replica.live (s ⊔ t) ⊆ Replica.live s ∪ Replica.live t := by
  intro o member
  have fst : (s ⊔ t).1 = s.1 ∪ t.1 := rfl
  have snd : (s ⊔ t).2 = s.2 ∪ t.2 := rfl
  simp only [Replica.live, Replica.seen, Replica.gone, Finset.mem_sdiff, fst, snd, Finset.mem_union,
    not_or] at member ⊢
  obtain ⟨inSeen, notS, notT⟩ := member
  rcases inSeen with h | h
  · exact Or.inl ⟨h, notS⟩
  · exact Or.inr ⟨h, notT⟩

/-- "At most `0` live" is merge-closed. -/
theorem atMost_zero_mergeClosed (s t : Region) (validS : AtMost 0 s) (validT : AtMost 0 t) :
    AtMost 0 (s ⊔ t) := by
  unfold AtMost at *
  rw [Nat.le_zero, Finset.card_eq_zero] at *
  exact Finset.subset_empty.mp ((live_sup s t).trans (by rw [validS, validT]; simp))

/-! ## The exact classifier -/

/-- **The exact classifier**: bound `0` goes to `free`. -/
def requiredExact : InvariantClass → Direction → Mechanism
  | .mergeClosed, _ => .free
  | .atMost 0, _ => .free
  | .atMost (_ + 1), .removing => .free
  | .atMost (_ + 1), _ => .escrowOrOwner
  | .atLeast 0, _ => .free
  | .atLeast (_ + 1), .adding => .free
  | .atLeast (_ + 1), _ => .escrowOrOwner
  | .general, _ => .owner

/-- Every region of the cell, from every valid start, is invariant confluent. -/
def CellFree (cls : InvariantClass) (dir : Direction) : Prop :=
  ∀ (ι : Type) (ops : ι → Op) (I : Region → Prop) [DecidablePred I], Denotes I cls → Matches ops dir →
    ∀ start, I start → IConfluent (fun i => (ops i).apply) I start

/-- Make any occurrence. -/
def makeAny : ℕ → Op := Op.make

/-- Take any occurrence. -/
def takeAny : ℕ → Op := Op.take

theorem makeAny_reachable (k : ℕ) :
    ∀ j ≤ k, Reachable (fun i => (makeAny i).apply) (AtMost k) (∅, ∅) (Finset.range j, ∅) := by
  intro j
  induction j with
  | zero => intro _; simpa using (Reachable.base : Reachable (fun i => (makeAny i).apply) (AtMost k) (∅, ∅) (∅, ∅))
  | succ j ih =>
      intro le
      have step := Reachable.commit (T := fun i => (makeAny i).apply) (I := AtMost k) j (ih (by omega))
        (by simp [makeAny, Op.apply, AtMost, Replica.live, Replica.seen, Replica.gone]; omega)
      rw [Finset.range_add_one]
      simpa [makeAny, Op.apply] using step

/-- **At most `k + 1` live under makes needs coordination**, for every bound: one replica makes
`k + 1` occurrences, another makes one more. -/
theorem atMost_succ_make_needs (k : ℕ) :
    ¬ IConfluent (fun i => (makeAny i).apply) (AtMost (k + 1)) (∅, ∅) := by
  intro confluent
  have first := makeAny_reachable (k + 1) (k + 1) le_rfl
  have second : Reachable (fun i => (makeAny i).apply) (AtMost (k + 1)) (∅, ∅) ({k + 1}, ∅) := by
    have atStart : Reachable (fun i => (makeAny i).apply) (AtMost (k + 1)) ((∅ : Finset ℕ), (∅ : Finset ℕ))
        (∅, ∅) := Reachable.base
    have := Reachable.commit (k + 1) atStart
      (by simp [makeAny, Op.apply, AtMost, Replica.live, Replica.seen, Replica.gone])
    simpa [makeAny, Op.apply] using this
  have bound := confluent _ _ first second
  have fst : ((Finset.range (k + 1), (∅ : Finset ℕ)) ⊔ ({k + 1}, ∅) : Region).1 =
      Finset.range (k + 1) ∪ {k + 1} := rfl
  have snd : ((Finset.range (k + 1), (∅ : Finset ℕ)) ⊔ ({k + 1}, ∅) : Region).2 = ∅ := by
    show (∅ : Finset ℕ) ∪ ∅ = ∅; simp
  unfold AtMost Replica.live Replica.seen Replica.gone at bound
  have union : Finset.range (k + 1) ∪ {k + 1} = Finset.range (k + 2) := by
    ext x; simp; omega
  rw [fst, snd, Finset.sdiff_empty, union, Finset.card_range] at bound
  omega

/-- **At least `k + 1` live under takes needs coordination**, for every bound: `k + 2` live, two
replicas take one each. -/
theorem atLeast_succ_take_needs (k : ℕ) :
    ¬ IConfluent (fun i => (takeAny i).apply) (AtLeast (k + 1)) (Finset.range (k + 2), ∅) := by
  intro confluent
  have liveAfter : ∀ id < k + 2, (Finset.range (k + 2) \ {id}).card = k + 1 := by
    intro id lt
    rw [Finset.card_sdiff_of_subset (by simpa using lt)]
    simp
  have reach : ∀ id < k + 2, Reachable (fun i => (takeAny i).apply) (AtLeast (k + 1))
      (Finset.range (k + 2), ∅) (Finset.range (k + 2), {id}) := by
    intro id lt
    have atStart : Reachable (fun i => (takeAny i).apply) (AtLeast (k + 1))
        ((Finset.range (k + 2), (∅ : Finset ℕ)) : Region) (Finset.range (k + 2), ∅) := Reachable.base
    have := Reachable.commit id atStart
      (by
        simp only [takeAny, Op.apply, AtLeast, Replica.live, Replica.seen, Replica.gone]
        rw [show insert id (∅ : Finset ℕ) = {id} from rfl, liveAfter id lt])
    simpa [takeAny, Op.apply] using this
  have bound := confluent _ _ (reach 0 (by omega)) (reach 1 (by omega))
  have fst : ((Finset.range (k + 2), ({0} : Finset ℕ)) ⊔ (Finset.range (k + 2), {1}) : Region).1 =
      Finset.range (k + 2) := by show Finset.range (k + 2) ∪ Finset.range (k + 2) = _; simp
  have snd : ((Finset.range (k + 2), ({0} : Finset ℕ)) ⊔ (Finset.range (k + 2), {1}) : Region).2 =
      {0, 1} := rfl
  unfold AtLeast Replica.live Replica.seen Replica.gone at bound
  rw [fst, snd, Finset.card_sdiff_of_subset (by intro x; simp; omega)] at bound
  have : ({0, 1} : Finset ℕ).card = 2 := by decide
  rw [this, Finset.card_range] at bound
  omega

theorem atMost_empty (k : ℕ) : AtMost k ((∅, ∅) : Region) := by
  simp [AtMost, Replica.live, Replica.seen, Replica.gone]

theorem matches_mixed {ι : Type u} (ops : ι → Op) : Matches ops .mixed := trivial

/-- **The classifier is exact**: a cell's verdict is `free` exactly when every region of the cell
is invariant confluent from every valid start. -/
theorem requiredExact_free_iff (cls : InvariantClass) (dir : Direction) :
    requiredExact cls dir = .free ↔ CellFree cls dir := by
  constructor
  · intro free ι ops I _ denotes fits start valid
    cases cls with
    | mergeClosed => exact iConfluent_of_mergeClosed valid denotes
    | atMost k =>
        simp only [Denotes] at denotes
        subst denotes
        cases k with
        | zero => exact iConfluent_of_mergeClosed valid atMost_zero_mergeClosed
        | succ k =>
            cases dir with
            | removing => exact atMost_take_free fits _ valid
            | adding => simp [requiredExact] at free
            | mixed => simp [requiredExact] at free
    | atLeast k =>
        simp only [Denotes] at denotes
        subst denotes
        cases k with
        | zero => exact fun _ _ _ _ => Nat.zero_le _
        | succ k =>
            cases dir with
            | adding => exact atLeast_make_free fits _ valid
            | removing => simp [requiredExact] at free
            | mixed => simp [requiredExact] at free
    | general => simp [requiredExact] at free
  · intro cellFree
    -- every cell whose verdict is not `free` contains a witness
    have makes : Matches makeAny .adding := fun i => ⟨i, rfl⟩
    have takes : Matches takeAny .removing := fun i => ⟨i, rfl⟩
    have makeWitness : ∀ k, ¬ CellFree (.atMost (k + 1)) .adding := fun k cell =>
      atMost_succ_make_needs k (cell ℕ makeAny _ rfl makes _ (atMost_empty _))
    have makeWitnessMixed : ∀ k, ¬ CellFree (.atMost (k + 1)) .mixed := fun k cell =>
      atMost_succ_make_needs k (cell ℕ makeAny _ rfl (matches_mixed _) _ (atMost_empty _))
    have takeValid : ∀ k, AtLeast (k + 1) ((Finset.range (k + 2), ∅) : Region) := by
      intro k
      simp [AtLeast, Replica.live, Replica.seen, Replica.gone]
    have takeWitness : ∀ k, ¬ CellFree (.atLeast (k + 1)) .removing := fun k cell =>
      atLeast_succ_take_needs k (cell ℕ takeAny _ rfl takes _ (takeValid k))
    have takeWitnessMixed : ∀ k, ¬ CellFree (.atLeast (k + 1)) .mixed := fun k cell =>
      atLeast_succ_take_needs k (cell ℕ takeAny _ rfl (matches_mixed _) _ (takeValid k))
    cases cls with
    | mergeClosed => rfl
    | atMost k =>
        cases k with
        | zero => rfl
        | succ k =>
            cases dir with
            | removing => rfl
            | adding => exact absurd cellFree (makeWitness k)
            | mixed => exact absurd cellFree (makeWitnessMixed k)
    | atLeast k =>
        cases k with
        | zero => rfl
        | succ k =>
            cases dir with
            | adding => rfl
            | removing => exact absurd cellFree (takeWitness k)
            | mixed => exact absurd cellFree (takeWitnessMixed k)
    | general =>
        exfalso
        cases dir with
        | adding =>
            exact atMost_succ_make_needs 0 (cellFree ℕ makeAny (AtMost 1) trivial makes _ (by decide))
        | mixed =>
            exact atMost_succ_make_needs 0
              (cellFree ℕ makeAny (AtMost 1) trivial (matches_mixed _) _ (by decide))
        | removing =>
            exact atLeast_succ_take_needs 0 (cellFree ℕ takeAny (AtLeast 1) trivial takes _ (takeValid 0))

/-- **The two classifiers agree away from bound `0`.** -/
theorem required_eq_requiredExact (cls : InvariantClass) (dir : Direction)
    (notZeroAtMost : cls ≠ .atMost 0) (notZeroAtLeast : cls ≠ .atLeast 0) :
    required cls dir = requiredExact cls dir := by
  cases cls with
  | mergeClosed => rfl
  | atMost k =>
      cases k with
      | zero => exact absurd rfl notZeroAtMost
      | succ k => cases dir <;> rfl
  | atLeast k =>
      cases k with
      | zero => exact absurd rfl notZeroAtLeast
      | succ k => cases dir <;> rfl
  | general => cases dir <;> rfl

/-- **At bound `0` the older classifier is conservative**: it asks for coordination in cells that
are free. -/
theorem required_conservative_at_zero :
    required (.atMost 0) .adding = .escrowOrOwner ∧ CellFree (.atMost 0) .adding ∧
      required (.atLeast 0) .removing = .escrowOrOwner ∧ CellFree (.atLeast 0) .removing :=
  ⟨rfl, (requiredExact_free_iff _ _).mp rfl, rfl, (requiredExact_free_iff _ _).mp rfl⟩

/-! ## The owner verdict is sufficient -/

section Owner

variable {L : Type u} [DecidableEq L] {α : Type v} [SemilatticeSup α] {ι : Type w}

/-- All transactions of a region run at its home `h`. -/
def atHome (h : L) (T : ι → α → α) (grows : ∀ i s, s ≤ T i s) :
    InvariantConfluence.Placed L α ι where
  owner _ := h
  write i state := T i (state h)
  grows i state := grows i (state h)

/-- The home keeps the region's invariant; the other components are not the region's. -/
def homeCondition (h : L) (I : α → Prop) (l : L) (s : α) : Prop := l = h → I s

instance (h : L) (I : α → Prop) [DecidablePred I] (l : L) : DecidablePred (homeCondition h I l) :=
  fun _ => by unfold homeCondition; infer_instance

/-- **The owner verdict is sufficient, for every invariant**: when every transaction of a region
runs at its home with local validation, and every other replica only merges, every replica's copy
of the region satisfies the invariant after every execution. -/
theorem owner_sufficient (h : L) (T : ι → α → α) (grows : ∀ i s, s ≤ T i s) (I : α → Prop)
    [DecidablePred I] {start : α} (valid : I start) (events : List (OwnedEvent ι L)) (replica : L) :
    I (execOwned (atHome h T grows) (homeCondition h I) (fun _ _ => start) events replica h) :=
  owned_valid (P := atHome h T grows) (J := homeCondition h I) (start := fun _ => start)
    (fun _ _ => valid) events replica h rfl

/-- The owner verdict on a region of occurrences. -/
theorem owner_sufficient_region (h : L) (ops : ι → Op) (I : Region → Prop) [DecidablePred I]
    {start : Region} (valid : I start) (events : List (OwnedEvent ι L)) (replica : L) :
    I (execOwned (atHome h (fun i => (ops i).apply) (fun i s => op_le (ops i) s)) (homeCondition h I)
      (fun _ _ => start) events replica h) :=
  owner_sufficient h _ _ I valid events replica

end Owner

/-! ## The escrow verdicts are sufficient -/

section Escrow

variable {L : Type u} [Fintype L] [DecidableEq L]

/-- An operation placed at a location. -/
structure LocatedOp (L : Type u) where
  site : L
  op : Op

/-- Escrow: each location's component records what it made and what it took. -/
def escrow : InvariantConfluence.Placed L Region (LocatedOp L) where
  owner k := k.site
  write k state := k.op.apply (state k.site)
  grows k state := op_le k.op (state k.site)

/-- The region a replica sees: the start, plus what every location made and took. -/
def globalRegion (start : Region) (copy : L → Region) : Region :=
  (start.1 ∪ Finset.univ.biUnion fun l => (copy l).1, start.2 ∪ Finset.univ.biUnion fun l => (copy l).2)

/-- A location takes at most its share. -/
def takesWithin (share : L → ℕ) (l : L) (s : Region) : Prop := s.2.card ≤ share l

/-- A location makes at most its share. -/
def makesWithin (share : L → ℕ) (l : L) (s : Region) : Prop := s.1.card ≤ share l

instance (share : L → ℕ) (l : L) : DecidablePred (takesWithin share l) :=
  fun _ => inferInstanceAs (Decidable (_ ≤ _))

instance (share : L → ℕ) (l : L) : DecidablePred (makesWithin share l) :=
  fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- **Escrow of a surplus is sufficient for "at least `k` live"**: if the shares add up to at most
the surplus of the start over `k`, and each location takes at most its share, every replica sees
at least `k` live occurrences after every execution of takes, makes and merges. -/
theorem escrow_atLeast_sufficient (share : L → ℕ) (k : ℕ) {start : Region}
    (slack : k + ∑ l, share l ≤ (Replica.live start).card) (events : List (OwnedEvent (LocatedOp L) L))
    (replica : L) :
    AtLeast k (globalRegion start
      (execOwned escrow (takesWithin share) (fun _ _ => (∅, ∅)) events replica)) := by
  set copy := execOwned escrow (takesWithin share) (fun _ _ => (∅, ∅)) events replica
  have within : ∀ l, (copy l).2.card ≤ share l := fun l =>
    owned_valid (P := escrow) (J := takesWithin share) (start := fun _ => (∅, ∅))
      (fun l => by simp [takesWithin]) events replica l
  set taken := Finset.univ.biUnion fun l => (copy l).2
  have takenBound : taken.card ≤ ∑ l, share l :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun l _ => within l)
  have sub : Replica.live start \ taken ⊆ Replica.live (globalRegion start copy) := by
    intro o member
    simp only [Replica.live, Replica.seen, Replica.gone, globalRegion, Finset.mem_sdiff,
      Finset.mem_union, not_or] at member ⊢
    exact ⟨Or.inl member.1.1, member.1.2, member.2⟩
  unfold AtLeast
  have := Finset.le_card_sdiff taken (Replica.live start)
  have := Finset.card_le_card sub
  omega

/-- **Escrow of a capacity is sufficient for "at most `k` live"**: if the start's live occurrences
and the shares add up to at most `k`, and each location makes at most its share, every replica
sees at most `k` live occurrences after every execution. -/
theorem escrow_atMost_sufficient (share : L → ℕ) (k : ℕ) {start : Region}
    (slack : (Replica.live start).card + ∑ l, share l ≤ k) (events : List (OwnedEvent (LocatedOp L) L))
    (replica : L) :
    AtMost k (globalRegion start
      (execOwned escrow (makesWithin share) (fun _ _ => (∅, ∅)) events replica)) := by
  set copy := execOwned escrow (makesWithin share) (fun _ _ => (∅, ∅)) events replica
  have within : ∀ l, (copy l).1.card ≤ share l := fun l =>
    owned_valid (P := escrow) (J := makesWithin share) (start := fun _ => (∅, ∅))
      (fun l => by simp [makesWithin]) events replica l
  set made := Finset.univ.biUnion fun l => (copy l).1
  have madeBound : made.card ≤ ∑ l, share l :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun l _ => within l)
  have sub : Replica.live (globalRegion start copy) ⊆ Replica.live start ∪ made := by
    intro o member
    simp only [Replica.live, Replica.seen, Replica.gone, globalRegion, Finset.mem_sdiff,
      Finset.mem_union, not_or] at member ⊢
    obtain ⟨inSeen, notGone, _⟩ := member
    rcases inSeen with h | h
    · exact Or.inl ⟨h, notGone⟩
    · exact Or.inr h
  unfold AtMost
  have := Finset.card_le_card sub
  have := Finset.card_union_le (Replica.live start) made
  omega

end Escrow

/-! ## Consuming takes -/

section Consume

/-- A region with the effects of its consumptions: `(consumed occurrence, effect)`. -/
abbrev WithEffects := Region × Finset (ℕ × ℕ)

/-- Consume occurrence `id` and record the effect `out`. -/
def consume (id out : ℕ) (s : WithEffects) : WithEffects := ((s.1.1, insert id s.1.2), insert (id, out) s.2)

/-- **Exactly-once consumption**: one effect per consumed occurrence. -/
def OncePerTaken (s : WithEffects) : Prop := ∀ x ∈ s.2, ∀ y ∈ s.2, x.1 = y.1 → x = y

instance : DecidablePred OncePerTaken := fun s => by unfold OncePerTaken; infer_instance

/-- Two replicas consume occurrence `0`, with effects `1` and `2`. -/
def consumeTwice (b : Bool) : WithEffects → WithEffects := consume 0 (if b then 1 else 2)

/-- **Consumption with differing effects needs coordination.** -/
theorem consume_needs : ¬ IConfluent consumeTwice OncePerTaken (({0}, ∅), ∅) := by
  intro confluent
  have := confluent _ _ (Reachable.commit true Reachable.base (by decide))
    (Reachable.commit false Reachable.base (by decide))
  exact absurd this (by decide)

/-- Every recorded effect is the one the function gives. -/
def EffectsOf (f : ℕ → ℕ) (s : WithEffects) : Prop := ∀ x ∈ s.2, x.2 = f x.1

/-- **Consumption whose effect is a function of the consumed occurrence is free.** -/
theorem consume_deterministic_free {ι : Type u} (target : ι → ℕ) (f : ℕ → ℕ) {start : WithEffects}
    (startEffects : EffectsOf f start) :
    IConfluent (fun i => consume (target i) (f (target i))) OncePerTaken start := by
  have reachEffects : ∀ s, Reachable (fun i => consume (target i) (f (target i))) OncePerTaken start s →
      EffectsOf f s := by
    intro s reach
    induction reach with
    | base => exact startEffects
    | commit i _ _ ih =>
        intro x member
        rcases Finset.mem_insert.mp member with rfl | old
        · rfl
        · exact ih x old
    | merge _ _ _ ih₁ ih₂ =>
        intro x member
        rcases Finset.mem_union.mp member with h | h
        · exact ih₁ x h
        · exact ih₂ x h
  intro first second reachFirst reachSecond x inX y inY same
  have joined : EffectsOf f (first ⊔ second) := by
    intro z member
    rcases Finset.mem_union.mp member with h | h
    · exact reachEffects _ reachFirst z h
    · exact reachEffects _ reachSecond z h
  have hx := joined x inX
  have hy := joined y inY
  exact Prod.ext same (by rw [hx, hy, same])

end Consume

/-! ## The full classifier -/

/-- **The classifier with the consumption column**: consuming takes whose effects are not
determined by the consumed occurrence need the owner, whatever the count class. -/
def classify (cls : InvariantClass) (dir : Direction) (consumesWithEffect : Bool) : Mechanism :=
  if consumesWithEffect then .owner else requiredExact cls dir

/-! ## Controls -/

namespace Controls

/-- Two locations, each with a share of one, while the surplus over the bound is only one. -/
def oneEach : Bool → ℕ := fun _ => 1

/-- Location `true` takes `0`, location `false` takes `1`, then `true` hears of `false`. -/
def twoTakes : List (OwnedEvent (LocatedOp Bool) Bool) :=
  [.commit ⟨true, .take 0⟩, .commit ⟨false, .take 1⟩, .merge false true]

/-- **Oversubscribed shares break the minimum**: start with two live, require at least one; the
shares add up to two, more than the surplus of one, and two takes leave nothing live. -/
theorem escrow_oversubscribed :
    ¬ AtLeast 1 (globalRegion ({0, 1}, ∅)
      (execOwned escrow (takesWithin oneEach) (fun _ _ => (∅, ∅)) twoTakes true)) := by
  decide

/-- The same takes with shares adding up to the surplus: one location may take, the other may
not, and the minimum holds (an instance of `escrow_atLeast_sufficient`). -/
theorem escrow_within_surplus :
    AtLeast 1 (globalRegion ({0, 1}, ∅)
      (execOwned escrow (takesWithin fun b => if b then 1 else 0) (fun _ _ => (∅, ∅)) twoTakes true)) :=
  escrow_atLeast_sufficient _ 1 (by decide) twoTakes true

/-- **Routing to the owner is needed**: the claims of `InvariantConfluence.Controls` run at two
replicas break "one claim per task"; run at the home, every replica keeps it. -/
theorem owner_routing_needed :
    ¬ IConfluent InvariantConfluence.Controls.claim InvariantConfluence.Controls.onePerKey ∅ ∧
      ∀ (events : List (OwnedEvent ℕ Bool)) (replica : Bool),
        InvariantConfluence.Controls.onePerKey
          (execOwned (atHome true InvariantConfluence.Controls.claim fun _ _ => Finset.subset_insert _ _)
            (homeCondition true InvariantConfluence.Controls.onePerKey) (fun _ _ => ∅) events replica true) :=
  ⟨InvariantConfluence.Controls.claims_not_confluent, fun events replica =>
    owner_sufficient true _ _ _ (by decide) events replica⟩

end Controls

end Mettapedia.GSLT.Coordination.ExactClassifier
