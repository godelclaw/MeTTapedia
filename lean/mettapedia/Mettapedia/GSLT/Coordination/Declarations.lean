import Mettapedia.GSLT.Coordination.InvariantConfluence
import Mettapedia.GSLT.Coordination.HomeLocation

/-!
# Coordination as a region policy: what can be chosen, what must be declared

Each region chooses its coordination the way it chooses its concurrency mode: from what its
commits do and from the invariant it must keep. The exact criterion is invariant confluence
(`InvariantConfluence.globallyValid_iff_iConfluent`). This module states how far a checker can
choose the cheapest sufficient mechanism by itself.

## The verdict needs the invariant and the labels, not only the footprint

Two regions whose commits have the same shape (take nothing, keep nothing, query nothing,
make one fresh occurrence) can differ: with "at most one leader", making two leaders needs
coordination and making one leader and one follower does not (`Controls.shape_does_not_decide`).
So a checker that sees only footprints must be conservative, and the invariant has to be declared.

## A decidable table: count bounds

For a region held as replicas of seen and taken occurrences (`ReplicaMerge.Replica`), with commits
that only make or only take:

| invariant | commits that make | commits that take |
|---|---|---|
| at most `k` live (capacity, uniqueness) | coordination (`atMost_make_needs`) | free (`atMost_take_free`) |
| at least `k` live (minimum balance) | free (`atLeast_make_free`) | coordination (`atLeast_take_needs`) |

A merge-closed invariant (a condition on each element) is free whatever the commits do
(`InvariantConfluence.iConfluent_of_mergeClosed`). Where the table says coordination, escrow
splits the capacity or the surplus into owned shares and turns the cell into an owned scope
(`InvariantConfluence.owned_valid`, `Escrow.no_overspend`).

## The classifier and its soundness

`required` maps a declared invariant class and the direction of a region's commits to the
cheapest mechanism the table justifies; `required_free_sound` proves that every `free` verdict is
invariant confluent. Undeclared or general invariants get the owner, which is always sufficient
for commits homed at one location (`HomeLocation.run_refines`).

## Commits that span owners

A commit that takes occurrences of two homes is homed at neither (`crossOwner_not_homed`), so it
needs atomic commit across owners (`AtomicCommitBlocking`), co-location under one owner, or a saga
with declared compensation.

## Monotone footprints are free

Commits that take nothing and query nothing need no coordination at all, under any
invariant they keep one at a time that is merge-closed, and their replicas always merge to a legal
serial run (`monotone_free`, from `ReplicaMerge.monotone_merge_legal`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.Declarations

open Mettapedia.GSLT.Coordination.InvariantConfluence
open Mettapedia.GSLT.Coordination.ReplicaMerge
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

/-! ## Count bounds on a region -/

/-- A region's replica state: occurrences seen and occurrences taken. -/
abbrev Region := Replica ℕ

/-- An operation on a region. -/
inductive Op where
  | make (id : ℕ)
  | take (id : ℕ)
  deriving DecidableEq

/-- Apply an operation to a replica. -/
def Op.apply : Op → Region → Region
  | .make id, state => (insert id state.1, state.2)
  | .take id, state => (state.1, insert id state.2)

/-- At most `k` live occurrences. -/
def AtMost (k : ℕ) (s : Region) : Prop := (Replica.live s).card ≤ k

/-- At least `k` live occurrences. -/
def AtLeast (k : ℕ) (s : Region) : Prop := k ≤ (Replica.live s).card

instance (k : ℕ) : DecidablePred (AtMost k) := fun _ => inferInstanceAs (Decidable (_ ≤ _))

instance (k : ℕ) : DecidablePred (AtLeast k) := fun _ => inferInstanceAs (Decidable (_ ≤ _))

variable {ι : Type u}

/-- With only takes, states keep the seen occurrences and grow the taken ones. -/
theorem reachable_of_takes {ops : ι → Op} (takes : ∀ i, ∃ id, ops i = .take id) {I : Region → Prop}
    [DecidablePred I] {start s : Region} (reach : Reachable (fun i => (ops i).apply) I start s) :
    s.1 = start.1 ∧ start.2 ⊆ s.2 := by
  induction reach with
  | base => exact ⟨rfl, le_rfl⟩
  | commit i _ _ ih =>
      obtain ⟨id, isTake⟩ := takes i
      rw [isTake]
      exact ⟨ih.1, ih.2.trans (Finset.subset_insert _ _)⟩
  | merge _ _ _ ih₁ ih₂ =>
      exact ⟨by simp [ih₁.1, ih₂.1], ih₁.2.trans Finset.subset_union_left⟩

/-- With only makes, states keep the taken occurrences and grow the seen ones. -/
theorem reachable_of_makes {ops : ι → Op} (makes : ∀ i, ∃ id, ops i = .make id) {I : Region → Prop}
    [DecidablePred I] {start s : Region} (reach : Reachable (fun i => (ops i).apply) I start s) :
    s.2 = start.2 ∧ start.1 ⊆ s.1 := by
  induction reach with
  | base => exact ⟨rfl, le_rfl⟩
  | commit i _ _ ih =>
      obtain ⟨id, isMake⟩ := makes i
      rw [isMake]
      exact ⟨ih.1, ih.2.trans (Finset.subset_insert _ _)⟩
  | merge _ _ _ ih₁ ih₂ =>
      exact ⟨by simp [ih₁.1, ih₂.1], ih₁.2.trans Finset.subset_union_left⟩

/-- **An upper bound under takes is free.** -/
theorem atMost_take_free {ops : ι → Op} (takes : ∀ i, ∃ id, ops i = .take id) (k : ℕ) {start : Region}
    (valid : AtMost k start) : IConfluent (fun i => (ops i).apply) (AtMost k) start := by
  intro first second reachFirst reachSecond
  have bound := reachFirst.valid valid
  obtain ⟨seenFirst, _⟩ := reachable_of_takes takes reachFirst
  obtain ⟨seenSecond, _⟩ := reachable_of_takes takes reachSecond
  refine le_trans (Finset.card_le_card fun o member => ?_) bound
  have fst : (first ⊔ second).1 = first.1 ∪ second.1 := rfl
  have snd : (first ⊔ second).2 = first.2 ∪ second.2 := rfl
  simp only [Replica.live, Replica.seen, Replica.gone, Finset.mem_sdiff, fst, snd,
    Finset.mem_union, not_or] at member ⊢
  obtain ⟨inSeen, notFirst, _⟩ := member
  refine ⟨?_, notFirst⟩
  rcases inSeen with h | h
  · exact h
  · rw [seenSecond, ← seenFirst] at h; exact h

/-- **A lower bound under makes is free.** -/
theorem atLeast_make_free {ops : ι → Op} (makes : ∀ i, ∃ id, ops i = .make id) (k : ℕ) {start : Region}
    (valid : AtLeast k start) : IConfluent (fun i => (ops i).apply) (AtLeast k) start := by
  intro first second reachFirst reachSecond
  have bound := reachFirst.valid valid
  obtain ⟨goneFirst, _⟩ := reachable_of_makes makes reachFirst
  obtain ⟨goneSecond, _⟩ := reachable_of_makes makes reachSecond
  refine le_trans bound (Finset.card_le_card fun o member => ?_)
  have fst : (first ⊔ second).1 = first.1 ∪ second.1 := rfl
  have snd : (first ⊔ second).2 = first.2 ∪ second.2 := rfl
  simp only [Replica.live, Replica.seen, Replica.gone, Finset.mem_sdiff, fst, snd,
    Finset.mem_union, not_or] at member ⊢
  obtain ⟨inSeen, notGone⟩ := member
  refine ⟨Or.inl inSeen, notGone, ?_⟩
  rw [goneSecond, ← goneFirst]; exact notGone

/-- Make occurrences `1` or `2`. -/
def twoMakes : Bool → Op := fun b => if b then .make 1 else .make 2

/-- Take occurrences `1` or `2`. -/
def twoTakes : Bool → Op := fun b => if b then .take 1 else .take 2

/-- **An upper bound under makes needs coordination**: capacity one, two replicas each make one. -/
theorem atMost_make_needs : ¬ IConfluent (fun i => (twoMakes i).apply) (AtMost 1) (∅, ∅) := by
  intro confluent
  have := confluent _ _ (Reachable.commit true Reachable.base (by decide))
    (Reachable.commit false Reachable.base (by decide))
  exact absurd this (by decide)

/-- **A lower bound under takes needs coordination**: two live, at least one must stay, two
replicas each take one. -/
theorem atLeast_take_needs : ¬ IConfluent (fun i => (twoTakes i).apply) (AtLeast 1) ({1, 2}, ∅) := by
  intro confluent
  have := confluent _ _ (Reachable.commit true Reachable.base (by decide))
    (Reachable.commit false Reachable.base (by decide))
  exact absurd this (by decide)

/-! ## The classifier -/

/-- What a region declares about its invariant. -/
inductive InvariantClass where
  | mergeClosed
  | atMost (k : ℕ)
  | atLeast (k : ℕ)
  | general
  deriving DecidableEq

/-- What a region's commits do to it. -/
inductive Direction where
  | adding
  | removing
  | mixed
  deriving DecidableEq

/-- The cheapest mechanism the table justifies. -/
inductive Mechanism where
  | free
  | escrowOrOwner
  | owner
  deriving DecidableEq, Repr

/-- **The classifier.** -/
def required : InvariantClass → Direction → Mechanism
  | .mergeClosed, _ => .free
  | .atMost _, .removing => .free
  | .atMost _, _ => .escrowOrOwner
  | .atLeast _, .adding => .free
  | .atLeast _, _ => .escrowOrOwner
  | .general, _ => .owner

/-- What a declared class means for an invariant. -/
def Denotes (I : Region → Prop) : InvariantClass → Prop
  | .mergeClosed => ∀ first second, I first → I second → I (first ⊔ second)
  | .atMost k => I = AtMost k
  | .atLeast k => I = AtLeast k
  | .general => True

/-- What a direction means for a region's operations. -/
def Matches (ops : ι → Op) : Direction → Prop
  | .adding => ∀ i, ∃ id, ops i = .make id
  | .removing => ∀ i, ∃ id, ops i = .take id
  | .mixed => True

/-- **Every `free` verdict is invariant confluent.** -/
theorem required_free_sound {ops : ι → Op} {I : Region → Prop} [DecidablePred I] {cls : InvariantClass}
    {dir : Direction} (free : required cls dir = .free) (denotes : Denotes I cls)
    (fits : Matches ops dir) {start : Region} (valid : I start) :
    IConfluent (fun i => (ops i).apply) I start := by
  cases cls with
  | mergeClosed => exact iConfluent_of_mergeClosed valid denotes
  | atMost k =>
      cases dir with
      | removing =>
          simp only [Denotes] at denotes
          subst denotes
          exact atMost_take_free fits k valid
      | adding => simp [required] at free
      | mixed => simp [required] at free
  | atLeast k =>
      cases dir with
      | adding =>
          simp only [Denotes] at denotes
          subst denotes
          exact atLeast_make_free fits k valid
      | removing => simp [required] at free
      | mixed => simp [required] at free
  | general => simp [required] at free

/-- The classifier is exact on the count cells: where it does not say `free`, a region of that
class and direction exists that is not invariant confluent. -/
theorem required_needs_witness :
    required (.atMost 1) .adding = .escrowOrOwner ∧
      ¬ IConfluent (fun i => (twoMakes i).apply) (AtMost 1) (∅, ∅) ∧
    required (.atLeast 1) .removing = .escrowOrOwner ∧
      ¬ IConfluent (fun i => (twoTakes i).apply) (AtLeast 1) ({1, 2}, ∅) :=
  ⟨rfl, atMost_make_needs, rfl, atLeast_take_needs⟩

/-! ## Commits that span owners -/

section CrossOwner

open Mettapedia.GSLT.Coordination.HomeLocation

variable {O : Type u} [DecidableEq O] {R : Type v} {L : Type u}

/-- **A commit that takes at two homes is homed at neither.** -/
theorem crossOwner_not_homed (label : O → R) (home : R → L) (p : Placed O R L) {first second : O}
    (takesFirst : first ∈ p.commit.taken) (takesSecond : second ∈ p.commit.taken)
    (apart : home (label first) ≠ home (label second)) : ¬ HomedAt label home p := by
  intro homed
  exact apart ((homed.1 first (Finset.mem_union_left _ takesFirst)).trans
    (homed.1 second (Finset.mem_union_left _ takesSecond)).symm)

end CrossOwner

/-! ## Monotone footprints -/

section Monotone

variable {O : Type u} [DecidableEq O] {R : Type v}

/-- The footprint check: every commit takes nothing and queries nothing. -/
def monotoneFootprint (cs : List (Commit O R)) : Bool :=
  cs.all fun c => c.taken.card == 0 && c.queries.isEmpty

omit [DecidableEq O] in
theorem monotone_of_footprint {cs : List (Commit O R)} (check : monotoneFootprint cs = true) :
    ∀ c ∈ cs, c.Monotone := by
  intro c member
  have := List.all_eq_true.mp check c member
  simp only [Bool.and_eq_true, beq_iff_eq, Finset.card_eq_zero, List.isEmpty_iff] at this
  exact this

/-- **Monotone footprints are free**: the footprint check is decidable, and when it passes, replicas
that each apply one commit merge to a legal serial run. -/
theorem monotone_free {label : O → R} {r : Replica O} (wf : r.WellFormed) {cs : List (Commit O R)}
    (check : monotoneFootprint cs = true) (enabled : ∀ c ∈ cs, Enabled label r.live c)
    (fresh : GloballyFresh r.seen cs) :
    (mergeAll r cs).live = fireList r.live cs ∧ Executable label r.live cs :=
  monotone_merge_legal wf cs (monotone_of_footprint check) enabled fresh

end Monotone

/-! ## Controls -/

namespace Controls

/-- Occurrence `40` and `41` are leaders, `42` a follower. -/
def isLeader (id : ℕ) : Bool := id == 40 || id == 41

/-- At most one leader. -/
def oneLeader (s : Finset ℕ) : Prop := (s.filter fun id => isLeader id = true).card ≤ 1

instance : DecidablePred oneLeader := fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- Two regions whose transactions have the same shape: each makes one fresh occurrence. -/
def makeLeaders : Bool → Finset ℕ → Finset ℕ := fun b s => insert (if b then 40 else 41) s

def makeLeaderAndFollower : Bool → Finset ℕ → Finset ℕ := fun b s => insert (if b then 40 else 42) s

theorem leaderFollower_reachable {s : Finset ℕ}
    (reach : Reachable makeLeaderAndFollower oneLeader ∅ s) : s ⊆ {40, 42} := by
  induction reach with
  | base => exact Finset.empty_subset _
  | commit b _ _ ih =>
      intro x member
      rcases Finset.mem_insert.mp member with rfl | old
      · cases b <;> simp
      · exact ih old
  | merge _ _ _ ih₁ ih₂ => exact Finset.union_subset ih₁ ih₂

/-- **The shape does not decide**: making two leaders needs coordination; making a leader and a
follower does not, though every transaction of both makes one fresh occurrence and reads nothing. -/
theorem shape_does_not_decide :
    ¬ IConfluent makeLeaders oneLeader ∅ ∧ IConfluent makeLeaderAndFollower oneLeader ∅ := by
  refine ⟨fun confluent => ?_, fun first second reachFirst reachSecond => ?_⟩
  · have := confluent _ _ (Reachable.commit true Reachable.base (by decide))
      (Reachable.commit false Reachable.base (by decide))
    exact absurd this (by decide)
  · have within : first ⊔ second ⊆ {40, 42} :=
      Finset.union_subset (leaderFollower_reachable reachFirst) (leaderFollower_reachable reachSecond)
    unfold oneLeader
    calc (Finset.filter (fun id => isLeader id = true) (first ⊔ second)).card
        ≤ (Finset.filter (fun id => isLeader id = true) ({40, 42} : Finset ℕ)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ within)
      _ = 1 := by decide

/-! ### Count bounds, directions and classes -/

/-- **At most one, positive**: a region with one live occurrence. (`atMost_make_needs` is about
the merge, the negative side.) -/
theorem atMost_controls : AtMost 1 (({1}, ∅) : Region) ∧ ¬ AtMost 1 (({1, 2}, ∅) : Region) := by
  decide

/-- **Directions**: two makes are adding and not removing; two takes are removing. -/
theorem matches_controls :
    Matches twoMakes .adding ∧ ¬ Matches twoMakes .removing ∧ Matches twoTakes .removing := by
  refine ⟨fun b => ?_, fun removing => ?_, fun b => ?_⟩
  · cases b
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
  · obtain ⟨id, h⟩ := removing true
    simp [twoMakes] at h
  · cases b
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩

/-- **Classes**: `AtMost 1` is the bound it names and `AtLeast 1` is not; that an occurrence is
gone is closed under merge, and `AtMost 1` is not. -/
theorem denotes_controls :
    Denotes (AtMost 1) (.atMost 1) ∧ ¬ Denotes (AtLeast 1) (.atMost 1) ∧
      Denotes (fun s : Region => 7 ∈ s.2) .mergeClosed ∧ ¬ Denotes (AtMost 1) .mergeClosed := by
  refine ⟨rfl, fun same => ?_, fun first second h h' => ?_, fun closed => ?_⟩
  · have holds : AtMost 1 ((∅, ∅) : Region) := by decide
    rw [← congrFun same ((∅, ∅) : Region)] at holds
    revert holds
    decide
  · show 7 ∈ (first ⊔ second).2
    exact Finset.mem_union_left _ h
  · have := closed (({1}, ∅) : Region) (({2}, ∅) : Region) (by decide) (by decide)
    revert this
    decide

end Controls

end Mettapedia.GSLT.Coordination.Declarations
