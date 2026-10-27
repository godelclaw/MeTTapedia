import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Owners replaced by majorities, and winner rules

When an owner may fail and its resource must stay available, a new owner has to be chosen, and
two locations must never both believe they own it. This is consensus. Its safety rests on one
counting fact, and its liveness on a bound on failures and on timing.

## Majorities (crash faults)

**Fault model.** Acceptors may crash; a crashed acceptor sends nothing more. Each acceptor votes
for at most one candidate per epoch, and never forgets what it stored.

* **Two majorities meet** (`quorums_intersect`).
* **The correct acceptors are a majority** when `n ≥ 2f + 1` and at most `f` crash
  (`correct_quorum`); with more crashes no majority answers (`Controls.too_many_crashes`).
* **One owner per epoch** (`one_owner_per_epoch`): two candidates elected by majorities in one
  epoch are the same.
* **A new owner learns every committed decision** (`committed_seen`): a decision stored by a
  majority is seen by every owner that reads from a majority. Owner failover therefore needs no
  more than majorities; what it cannot do without timing assumptions is terminate, by the theorem
  of Fischer, Lynch and Paterson.
* **Halves are not enough** (`Controls.halves_two_owners`): with four acceptors and two votes,
  disjoint halves elect two owners in one epoch.

## Deterministic winner rules (timing faults)

Each claimant broadcasts its claim and, after waiting `wait`, proceeds unless it has seen an
earlier claim (`Proceeds`).

* **With a bound on delays it is safe** (`winner_unique`): when every claim reaches every claimant
  within `wait`, at most one claimant proceeds.
* **The earliest claimant always proceeds** (`earliest_proceeds`), whatever the delays.
* **Without the bound it is not** (`Controls.late_claim_two_winners`): a claim delayed past the
  wait lets two claimants proceed. A winner rule is therefore safe only under synchrony, or when
  the effect it licenses is fenced at an owner (`FencedLeases`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.MajorityEpochs

universe u v

/-! ## Majorities -/

section Majorities

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A majority of the acceptors. -/
def IsMajority (quorum : Finset V) : Prop := Fintype.card V < 2 * quorum.card

instance (quorum : Finset V) : Decidable (IsMajority quorum) := inferInstanceAs (Decidable (_ < _))

/-- **Two majorities meet.** -/
theorem quorums_intersect {first second : Finset V} (majorFirst : IsMajority first)
    (majorSecond : IsMajority second) : ∃ v, v ∈ first ∧ v ∈ second := by
  have unionBound := Finset.card_le_univ (first ∪ second)
  have count := Finset.card_union_add_card_inter first second
  unfold IsMajority at majorFirst majorSecond
  have : 0 < (first ∩ second).card := by omega
  obtain ⟨v, member⟩ := Finset.card_pos.mp this
  exact ⟨v, (Finset.mem_inter.mp member).1, (Finset.mem_inter.mp member).2⟩

/-- **With `n ≥ 2f + 1`, the correct acceptors are a majority.** -/
theorem correct_quorum (faulty : Finset V) (f : ℕ) (resilience : 2 * f + 1 ≤ Fintype.card V)
    (bound : faulty.card ≤ f) : IsMajority (Finset.univ \ faulty) := by
  unfold IsMajority
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ faulty), Finset.card_univ]
  omega

variable {C : Type v}

/-- Candidate `c` is elected in an epoch when a majority voted for it there. -/
def Elected (vote : ℕ → V → Option C) (epoch : ℕ) (c : C) : Prop :=
  ∃ quorum, IsMajority quorum ∧ ∀ v ∈ quorum, vote epoch v = some c

/-- **One owner per epoch.** -/
theorem one_owner_per_epoch {vote : ℕ → V → Option C} {epoch : ℕ} {first second : C}
    (electedFirst : Elected vote epoch first) (electedSecond : Elected vote epoch second) :
    first = second := by
  obtain ⟨q₁, major₁, votes₁⟩ := electedFirst
  obtain ⟨q₂, major₂, votes₂⟩ := electedSecond
  obtain ⟨v, in₁, in₂⟩ := quorums_intersect major₁ major₂
  have := (votes₁ v in₁).symm.trans (votes₂ v in₂)
  exact Option.some.inj this

/-- **A new owner learns every committed decision**: a decision stored by a majority is seen by
whoever reads from a majority. -/
theorem committed_seen {D : Type v} {stored : V → Set D} {decision : D} {committed readers : Finset V}
    (majorCommitted : IsMajority committed) (storedThere : ∀ v ∈ committed, decision ∈ stored v)
    (majorReaders : IsMajority readers) : ∃ v ∈ readers, decision ∈ stored v := by
  obtain ⟨v, inCommitted, inReaders⟩ := quorums_intersect majorCommitted majorReaders
  exact ⟨v, inReaders, storedThere v inCommitted⟩

end Majorities

/-! ## Deterministic winner rules -/

section Winner

variable {W : Type u}

/-- Claim `v` comes before claim `w`: earlier, or at the same time with a smaller rank. -/
def Before (time : W → ℕ) (rank : W → ℕ) (v w : W) : Prop :=
  time v < time w ∨ (time v = time w ∧ rank v < rank w)

/-- Claimant `w` has seen `v`'s claim when it decides, `wait` after its own claim. -/
def Sees (time : W → ℕ) (delay : W → W → ℕ) (wait : ℕ) (v w : W) : Prop :=
  time v + delay v w ≤ time w + wait

/-- Claimant `w` proceeds when it has seen no earlier claim. -/
def Proceeds (time rank : W → ℕ) (delay : W → W → ℕ) (wait : ℕ) (w : W) : Prop :=
  ∀ v, v ≠ w → Sees time delay wait v w → ¬ Before time rank v w

/-- **With delays bounded by the wait, at most one claimant proceeds.** -/
theorem winner_unique {time rank : W → ℕ} (distinct : Function.Injective rank) {delay : W → W → ℕ}
    {wait : ℕ} (bounded : ∀ v w, delay v w ≤ wait) {first second : W}
    (proceedsFirst : Proceeds time rank delay wait first)
    (proceedsSecond : Proceeds time rank delay wait second) : first = second := by
  by_contra apart
  -- one of the two claims comes before the other, and the later claimant has seen it
  have ordered : Before time rank first second ∨ Before time rank second first := by
    unfold Before
    rcases lt_trichotomy (time first) (time second) with lt | eq | gt
    · exact Or.inl (Or.inl lt)
    · rcases lt_trichotomy (rank first) (rank second) with lt' | eq' | gt'
      · exact Or.inl (Or.inr ⟨eq, lt'⟩)
      · exact absurd (distinct eq') apart
      · exact Or.inr (Or.inr ⟨eq.symm, gt'⟩)
    · exact Or.inr (Or.inl gt)
  rcases ordered with before | before
  · have seen : Sees time delay wait first second := by
      have := bounded first second
      unfold Sees
      rcases before with lt | ⟨eq, _⟩ <;> omega
    exact proceedsSecond first apart seen before
  · have seen : Sees time delay wait second first := by
      have := bounded second first
      unfold Sees
      rcases before with lt | ⟨eq, _⟩ <;> omega
    exact proceedsFirst second (Ne.symm apart) seen before

/-- **The earliest claimant always proceeds**, whatever the delays. -/
theorem earliest_proceeds {time rank : W → ℕ} {delay : W → W → ℕ} {wait : ℕ} {earliest : W}
    (isEarliest : ∀ v, v ≠ earliest → Before time rank earliest v)
    (strict : ∀ v w, Before time rank v w → ¬ Before time rank w v) :
    Proceeds time rank delay wait earliest :=
  fun v apart _ before => strict earliest v (isEarliest v apart) before

theorem before_asymm {time rank : W → ℕ} (v w : W) (before : Before time rank v w) :
    ¬ Before time rank w v := by
  unfold Before at *
  omega

end Winner

/-! ## Controls -/

namespace Controls

/-- **Halves are not enough**: with four acceptors, `{0, 1}` vote for `a` and `{2, 3}` for `b`;
each pair is half, not a majority, and taking halves as quorums elects two owners. -/
theorem halves_two_owners :
    let vote : ℕ → Fin 4 → Option Bool := fun _ v => some (decide (v.val < 2))
    (∀ v ∈ ({0, 1} : Finset (Fin 4)), vote 0 v = some true) ∧
      (∀ v ∈ ({2, 3} : Finset (Fin 4)), vote 0 v = some false) ∧
      ¬ IsMajority ({0, 1} : Finset (Fin 4)) := by
  decide

/-- **With more than `f` crashes no majority answers**: of three acceptors, two crash. -/
theorem too_many_crashes : ¬ IsMajority (Finset.univ \ ({0, 1} : Finset (Fin 3))) := by
  decide

/-- **A late claim lets two claimants proceed**: both claim at time `0`; the claim of the
earlier-ranked one reaches the other after `5` while the wait is `1`. -/
theorem late_claim_two_winners :
    let time : Bool → ℕ := fun _ => 0
    let rank : Bool → ℕ := fun w => if w then 1 else 0
    let delay : Bool → Bool → ℕ := fun v _ => if v then 0 else 5
    Proceeds time rank delay 1 false ∧ Proceeds time rank delay 1 true := by
  refine ⟨?_, ?_⟩
  · intro v apart _ before
    cases v
    · exact apart rfl
    · simp [Before] at before
  · intro v apart seen _
    cases v
    · simp [Sees] at seen
    · exact apart rfl

/-- **Elected, positive**: when all three acceptors vote for `true`, the majority of all of them
elects it. -/
theorem unanimous_elected : Elected (fun _ (_ : Fin 3) => some true) 0 true :=
  ⟨Finset.univ, by decide, fun _ _ => rfl⟩

/-- **Elected, negative**: one vote for `true`, one for `false` and one abstention elect neither:
every majority of three contains a voter that did not vote `true`. -/
theorem split_vote_not_elected :
    ¬ Elected (fun _ (v : Fin 3) => if v = 0 then some true else if v = 1 then some false else none)
      0 true := by
  rintro ⟨quorum, major, votes⟩
  have two : 1 < quorum.card := by
    unfold IsMajority at major
    simp only [Fintype.card_fin] at major
    omega
  obtain ⟨v, member, notZero⟩ := Finset.exists_mem_ne two 0
  have vote := votes v member
  clear member votes major two
  revert v
  decide

/-- **Proceeds, negative**: both claim at time `0`, every claim arrives at once and the wait is
`1`; the claimant of rank `1` sees the earlier-ranked claim and does not proceed.
(`late_claim_two_winners` contains positive controls.) -/
theorem later_rank_not_proceeds :
    ¬ Proceeds (fun _ : Bool => 0) (fun w => if w then 1 else 0) (fun _ _ => 0) 1 true := by
  intro proceeds
  exact proceeds false (by decide) (by simp [Sees]) (by simp [Before])

end Controls

end Mettapedia.GSLT.Coordination.MajorityEpochs
