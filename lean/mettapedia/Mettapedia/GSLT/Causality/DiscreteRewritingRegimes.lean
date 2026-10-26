import Mettapedia.GSLT.Causality.DiscreteDoublePushout

/-!
# Double-pushout, single-pushout and sesqui-pushout rewriting of a space, side by side

`DiscreteDoublePushout` reads a rule instance on a space of atom occurrences as a double-pushout
derivation. The other two algebraic regimes differ only in what a match may identify, because a space
has no edges and the dangling condition is empty.

## Single pushout: deletion wins

A single-pushout match (`SPOMatch`) may use one occurrence both as consumed and as kept. Its result has
the double-pushout formula, the state without the consumed occurrences plus the production.

* **Every double-pushout match is one** (`Match.toSPO`), with the same result.
* **It exists exactly when the consumption and the reads are each present** (`exists_spoMatch_iff`),
  not side by side.
* **Counted, it is still one firing** (`SPOMatch.labels_result`).
* **The kept part survives exactly when the match respects identification**
  (`SPOMatch.kept_sub_result_iff`): with one occurrence read and consumed, the read is gone after the
  derivation (`RegimeControls.spo_read_vanishes`).
* **Local Church–Rosser holds for independent single-pushout matches** (`SPOMatch.local_church_rosser`),
  but the counting model's concurrency is the double-pushout one: a single-pushout match independent of
  another can exist where the counting model reports no concurrency
  (`RegimeControls.spo_independent_not_concurrent`).

## Three enabling conditions, one firing

Counted, the three readings of identification are three enabling conditions for the same firing
`M - consume + produce`:
* injective double pushout (`Enables`): consumption and reads side by side, a read occurrence per read;
* double pushout with shared reads (`EnablesSharedReads`): every read atom present beside the
  consumption, reads sharing occurrences;
* single pushout (`EnablesSPO`): consumption present, every read atom present.

Each implies the next (`enablesSharedReads_of_enables`, `enablesSPO_of_enablesSharedReads`), and
neither converse holds (`RegimeControls.two_reads_one_token`, `RegimeControls.read_take_one_token`).
Reads are preserved by the first two (`read_present_after_of_enablesSharedReads`); the third can
consume what it read.

## Sesqui-pushout

Sesqui-pushout rewriting replaces the left pushout by a final pullback complement.
* **On an identification-respecting match the double-pushout context is the final pullback complement**
  in the lattice of occurrence sets: it meets the left side in the kept part (`Match.context_meets`)
  and contains every set that does (`Match.subset_context`).
* **On a match identifying a consumed with a kept item no pullback complement exists**
  (`no_pullback_complement_of_identified`), whatever the complement and its maps.

So on spaces the three regimes agree on identification-respecting matches; on a match that reads and
consumes one occurrence, the single pushout fires and deletes it, the double pushout refuses it, and the
sesqui-pushout has no derivation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

universe uRes uRule uOcc

namespace System

variable {R : Type uRes} [DecidableEq R] (S : System.{uRes, uRule} R)
variable {O : Type uOcc} [DecidableEq O] (label : O → R)

/-! ## Single-pushout matches -/

/-- **A single-pushout match**: the consumed and the kept occurrences, with the instance's labels,
inside the state; they may overlap. -/
structure SPOMatch (state : Finset O) {site : S.Site} (i : S.Instance site) where
  taken : Finset O
  kept : Finset O
  taken_sub : taken ⊆ state
  kept_sub : kept ⊆ state
  taken_labels : labels label taken = S.consume i
  kept_labels : labels label kept = S.read i

variable {S label}

/-- Every double-pushout match is a single-pushout match. -/
def Match.toSPO {state : Finset O} {site : S.Site} {i : S.Instance site} (m : S.Match label state i) :
    S.SPOMatch label state i :=
  ⟨m.taken, m.kept, m.taken_sub, m.kept_sub, m.taken_labels, m.kept_labels⟩

namespace SPOMatch

variable {state : Finset O} {site : S.Site} {i : S.Instance site}

/-- The result: the state without the consumed occurrences, with fresh occurrences `made`. -/
def result (m : S.SPOMatch label state i) (made : Finset O) : Finset O := (state \ m.taken) ∪ made

omit [DecidableEq R] in
/-- A double-pushout match has the same result read as a single-pushout match. -/
theorem toSPO_result (m : S.Match label state i) (made : Finset O) :
    m.toSPO.result made = m.result made := rfl

/-- **Counted, a single-pushout derivation is one firing.** -/
theorem labels_result (m : S.SPOMatch label state i) {made : Finset O} (fresh : Disjoint made state)
    (madeLabels : labels label made = S.produce i) :
    labels label (m.result made) = S.fire (labels label state) i := by
  have apart : Disjoint (state \ m.taken) made :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset fresh.symm
  rw [result, labels_union_of_disjoint apart, labels_sdiff m.taken_sub, m.taken_labels, madeLabels]
  rfl

omit [DecidableEq R] in
/-- **The kept part survives exactly when the match respects identification.** -/
theorem kept_sub_result_iff (m : S.SPOMatch label state i) {made : Finset O}
    (fresh : Disjoint made state) : m.kept ⊆ m.result made ↔ Disjoint m.taken m.kept := by
  constructor
  · intro survives
    refine Finset.disjoint_left.mpr fun o inTaken inKept => ?_
    rcases Finset.mem_union.mp (survives inKept) with inContext | inMade
    · exact (Finset.mem_sdiff.mp inContext).2 inTaken
    · exact Finset.disjoint_left.mp fresh inMade (m.kept_sub inKept)
  · intro apart o inKept
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨m.kept_sub inKept, fun inTaken => Finset.disjoint_left.mp apart inTaken inKept⟩)

/-- Single-pushout independence: neither consumes what the other uses. -/
def Independent {site₂ : S.Site} {j : S.Instance site₂} (m₁ : S.SPOMatch label state i)
    (m₂ : S.SPOMatch label state j) : Prop :=
  Disjoint m₁.taken (m₂.taken ∪ m₂.kept) ∧ Disjoint m₂.taken (m₁.taken ∪ m₁.kept)

omit [DecidableEq R] in
/-- **Local Church–Rosser for independent single-pushout matches.** Each match's occurrences survive
the other's derivation, and the two orders reach one space. -/
theorem local_church_rosser {site₂ : S.Site} {j : S.Instance site₂} (m₁ : S.SPOMatch label state i)
    (m₂ : S.SPOMatch label state j) (indep : Independent m₁ m₂) {made₁ made₂ : Finset O}
    (fresh₁ : Disjoint made₁ state) (fresh₂ : Disjoint made₂ state) :
    (m₂.taken ∪ m₂.kept ⊆ m₁.result made₁) ∧ (m₁.taken ∪ m₁.kept ⊆ m₂.result made₂) ∧
      ((state \ m₁.taken ∪ made₁) \ m₂.taken ∪ made₂ = (state \ m₂.taken ∪ made₂) \ m₁.taken ∪ made₁) := by
  obtain ⟨one, two⟩ := indep
  refine ⟨fun o inUse => ?_, fun o inUse => ?_, ?_⟩
  · have inState : o ∈ state := by
      rcases Finset.mem_union.mp inUse with h | h
      · exact m₂.taken_sub h
      · exact m₂.kept_sub h
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨inState, fun inTaken =>
      Finset.disjoint_left.mp one inTaken inUse⟩)
  · have inState : o ∈ state := by
      rcases Finset.mem_union.mp inUse with h | h
      · exact m₁.taken_sub h
      · exact m₁.kept_sub h
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨inState, fun inTaken =>
      Finset.disjoint_left.mp two inTaken inUse⟩)
  · ext o
    simp only [Finset.mem_union, Finset.mem_sdiff]
    have notTaken₂ : o ∈ made₁ → o ∉ m₂.taken := fun inMade inTaken =>
      Finset.disjoint_left.mp fresh₁ inMade (m₂.taken_sub inTaken)
    have notTaken₁ : o ∈ made₂ → o ∉ m₁.taken := fun inMade inTaken =>
      Finset.disjoint_left.mp fresh₂ inMade (m₁.taken_sub inTaken)
    constructor
    · rintro (⟨⟨inState, notT₁⟩ | inMade₁, notT₂⟩ | inMade₂)
      · exact Or.inl ⟨Or.inl ⟨inState, notT₂⟩, notT₁⟩
      · exact Or.inr inMade₁
      · exact Or.inl ⟨Or.inr inMade₂, notTaken₁ inMade₂⟩
    · rintro (⟨⟨inState, notT₂⟩ | inMade₂, notT₁⟩ | inMade₁)
      · exact Or.inl ⟨Or.inl ⟨inState, notT₁⟩, notT₂⟩
      · exact Or.inr inMade₂
      · exact Or.inl ⟨Or.inr inMade₁, notTaken₂ inMade₁⟩

end SPOMatch

/-! ## Three enabling conditions -/

variable (S)

/-- Double pushout with shared reads: the consumption is present, and every read atom is present beside
it. -/
def EnablesSharedReads (M : Multiset R) {site : S.Site} (i : S.Instance site) : Prop :=
  S.consume i ≤ M ∧ ∀ a ∈ S.read i, a ∈ M - S.consume i

/-- Single pushout: the consumption is present, and every read atom is present. -/
def EnablesSPO (M : Multiset R) {site : S.Site} (i : S.Instance site) : Prop :=
  S.consume i ≤ M ∧ ∀ a ∈ S.read i, a ∈ M

variable {S}

theorem enablesSharedReads_of_enables {M : Multiset R} {site : S.Site} {i : S.Instance site}
    (enabled : S.Enables M i) : S.EnablesSharedReads M i := by
  refine ⟨le_trans (Multiset.le_add_right _ _) enabled, fun a inRead => ?_⟩
  exact Multiset.mem_of_le (le_tsub_of_add_le_left enabled) inRead

theorem enablesSPO_of_enablesSharedReads {M : Multiset R} {site : S.Site} {i : S.Instance site}
    (enabled : S.EnablesSharedReads M i) : S.EnablesSPO M i :=
  ⟨enabled.1, fun a inRead => Multiset.mem_of_le (Multiset.sub_le_self _ _) (enabled.2 a inRead)⟩

/-- **Reads are preserved under shared-read enabling**: every read atom is present after the firing. -/
theorem read_present_after_of_enablesSharedReads {M : Multiset R} {site : S.Site} {i : S.Instance site}
    (enabled : S.EnablesSharedReads M i) : ∀ a ∈ S.read i, a ∈ S.fire M i :=
  fun a inRead => Multiset.mem_add.mpr (Or.inl (enabled.2 a inRead))

/-- **A single-pushout match exists exactly when the consumption and the reads are each present.** -/
theorem exists_spoMatch_iff (state : Finset O) {site : S.Site} (i : S.Instance site) :
    Nonempty (S.SPOMatch label state i) ↔
      S.consume i ≤ labels label state ∧ S.read i ≤ labels label state := by
  constructor
  · rintro ⟨m⟩
    exact ⟨m.taken_labels ▸ labels_mono m.taken_sub, m.kept_labels ▸ labels_mono m.kept_sub⟩
  · rintro ⟨consumed, read⟩
    obtain ⟨T, subT, labelsT⟩ := exists_sub_labels _ consumed
    obtain ⟨K, subK, labelsK⟩ := exists_sub_labels _ read
    exact ⟨⟨T, K, subT, subK, labelsT, labelsK⟩⟩

/-! ## Sesqui-pushout -/

namespace Match

variable {state : Finset O} {site : S.Site} {i : S.Instance site}

omit [DecidableEq R] in
/-- The context meets the left side exactly in the kept part: the left square is a pullback of
inclusions. -/
theorem context_meets (m : S.Match label state i) :
    m.context ∩ (m.taken ∪ m.kept) = m.kept :=
  (m.left_square).2

omit [DecidableEq R] in
/-- **The context is the final pullback complement**: every set of occurrences of the state that meets
the left side only in the kept part lies inside it. -/
theorem subset_context (m : S.Match label state i) {D : Finset O} (inside : D ⊆ state)
    (meets : D ∩ (m.taken ∪ m.kept) ⊆ m.kept) : D ⊆ m.context := by
  intro o inD
  refine Finset.mem_sdiff.mpr ⟨inside inD, fun inTaken => ?_⟩
  have inKept := meets (Finset.mem_inter.mpr ⟨inD, Finset.mem_union_left _ inTaken⟩)
  exact Finset.disjoint_left.mp m.identification inTaken inKept

end Match

end System

/-- A commuting square of maps of sets is a pullback when every pair agreeing in the corner comes from
exactly one element of the interface. -/
def IsSetPullback {K L D G : Type*} (l : K → L) (k : K → D) (m : L → G) (n : D → G) : Prop :=
  (∀ c, m (l c) = n (k c)) ∧ ∀ x d, m x = n d → ∃! c, l c = x ∧ k c = d

/-- **No pullback complement exists for a match identifying a consumed with a kept item.** The left
side has a consumed item `0` and a kept item `1`, the interface is the kept item, and the match sends
both to one occurrence. -/
theorem no_pullback_complement_of_identified {G D : Type*} (m : Fin 2 → G) (identify : m 0 = m 1)
    (k : Unit → D) (n : D → G) :
    ¬ IsSetPullback (fun _ : Unit => (1 : Fin 2)) k m n := by
  rintro ⟨commutes, unique⟩
  obtain ⟨c, ⟨hc, -⟩, -⟩ := unique 0 (k ()) (by rw [identify, commutes ()])
  simp at hc

/-! ## Controls -/

namespace RegimeControls

open _root_.Mettapedia.GSLT.Causality.ResourceInteraction.System DoublePushoutControls

/-- **Single pushout lets one occurrence be read and consumed, and the read is gone after.** -/
theorem spo_read_vanishes :
    ∃ m : readTake.SPOMatch (fun _ : Fin 1 => Atom.tok) Finset.univ (site := ()) (),
      ¬ m.kept ⊆ m.result ∅ := by
  refine ⟨⟨{0}, {0}, Finset.subset_univ _, Finset.subset_univ _, rfl, rfl⟩, fun survives => ?_⟩
  have apart := (SPOMatch.kept_sub_result_iff _ (Finset.disjoint_empty_left _)).mp survives
  exact absurd apart (by decide)

/-- A reader of two copies of one token. -/
def twoReads : System Atom where
  Site := Unit
  Instance := fun _ => Unit
  consume := fun _ => 0
  read := fun _ => {Atom.tok, Atom.tok}
  produce := fun _ => {Atom.seen}

/-- **Shared reads do not imply injective enabling**: one token serves two reads that share it, while
the counting model needs two. -/
theorem two_reads_one_token :
    twoReads.EnablesSharedReads ({Atom.tok} : Multiset Atom) (site := ()) () ∧
      ¬ twoReads.Enables ({Atom.tok} : Multiset Atom) (site := ()) () := by
  refine ⟨⟨by simp [twoReads], fun x inRead => ?_⟩, by unfold System.Enables; decide⟩
  simp [twoReads] at inRead
  simp [twoReads, inRead]

/-- **Single-pushout enabling does not imply shared-read enabling**: with one token, reading and
consuming it is single-pushout enabled only. -/
theorem read_take_one_token :
    readTake.EnablesSPO ({Atom.tok} : Multiset Atom) (site := ()) () ∧
      ¬ readTake.EnablesSharedReads ({Atom.tok} : Multiset Atom) (site := ()) () := by
  refine ⟨⟨by simp [readTake], fun x inRead => by simp [readTake] at inRead ⊢; exact inRead⟩, ?_⟩
  rintro ⟨-, reads⟩
  have := reads Atom.tok (by simp [readTake])
  simp [readTake] at this

/-- A token read and consumed, and a third atom read. -/
def readTakeAndReader : System Atom where
  Site := Unit
  Instance := fun _ => Bool
  consume := fun (b : Bool) => if b then {Atom.tok} else 0
  read := fun (b : Bool) => if b then {Atom.tok} else {Atom.c}
  produce := fun (b : Bool) => if b then {Atom.seen} else {Atom.sawC}

/-- **Single-pushout independence is not the counting model's concurrency**: one occurrence of `tok`
read and consumed, independent of a reader of `c`, while the counting model needs a second `tok`. -/
theorem spo_independent_not_concurrent :
    ∃ (m₁ : readTakeAndReader.SPOMatch ![Atom.tok, Atom.c] Finset.univ (site := ()) true)
      (m₂ : readTakeAndReader.SPOMatch ![Atom.tok, Atom.c] Finset.univ (site := ()) false),
      SPOMatch.Independent m₁ m₂ ∧
        ¬ readTakeAndReader.Concurrent (labels ![Atom.tok, Atom.c] Finset.univ)
          (site₁ := ()) (site₂ := ()) true false := by
  refine ⟨⟨{0}, {0}, Finset.subset_univ _, Finset.subset_univ _, by decide, by decide⟩,
    ⟨∅, {1}, Finset.empty_subset _, Finset.subset_univ _, by decide, by decide⟩, ?_, ?_⟩
  · exact ⟨by decide, by decide⟩
  · unfold System.Concurrent
    decide

end RegimeControls

end Mettapedia.GSLT.Causality.ResourceInteraction
