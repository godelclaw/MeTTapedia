import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Isolation

/-!
# Validation of a proposal, and serializability

A proposal was explored from a snapshot.  When it is to be published the live
state may have moved.  Two notions say that the proposal is still good.

* **The reads are kept** (`Proposal.ReadsKept`): the live state agrees with the
  snapshot on every location the proposal read or wrote.
* **The region still has the outcome** (`Region.StillHas`): replayed on the live
  state, the region has the same answer with the same proposal.

Results.

* `Region.stillHas_of_readsKept`: **validation is sound.**  If the reads are
  kept, the region replayed on the live state has that outcome.
* The inclusion is strict.  With two tokens in a space and two regions that each
  take one, publishing the first changes what the second read, and the second
  still has its outcome (`Controls.second_copy_stillHas`,
  `Controls.second_copy_reads_not_kept`).  The same holds of two regions that
  each add an atom to one space (`Controls.second_add_stillHas`,
  `Controls.second_add_reads_not_kept`).  With one token the second region has
  lost its outcome under both notions (`Controls.last_copy_not_stillHas`).
* `Proposal.publish_eq_piecewise`: if the reads are kept, publication on the live
  state installs the private view on the written locations and leaves every other
  location of the live state as it is.  The private view itself is the snapshot
  with the written locations overlaid (`Proposal.view_eq_piecewise`).
* `publishInOrder_serializable`: **serializability.**  A sequence of
  publications, each made when the region of its proposal still had the outcome,
  is the committed run of the published alternatives in the order of
  publication: the same answers, the same final state.
  `publishWithKeptReads_serializable` is the same with every publication
  validated by kept reads against the snapshot its proposal was explored from.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra

universe u v w

variable {Location : Type u} {Value : Type v} {Answer : Type w}

section Validation

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-- **The first validation**: the live state agrees with the snapshot on every
location the proposal read or wrote. -/
def Proposal.ReadsKept (proposal : Proposal Location Value Answer)
    (snapshot live : Location → Value) : Prop :=
  AgreesOn (proposal.reads ∪ proposal.writes) snapshot live

instance Proposal.decidableReadsKept [DecidableEq Value]
    (proposal : Proposal Location Value Answer) (snapshot live : Location → Value) :
    Decidable (proposal.ReadsKept snapshot live) :=
  inferInstanceAs (Decidable (AgreesOn (proposal.reads ∪ proposal.writes) snapshot live))

/-- **The second validation**: the region, replayed on the live state, still has
the outcome. -/
def Region.StillHas (region : Region Location Value Answer) (live : Location → Value)
    (outcome : Answer × Proposal Location Value Answer) : Prop :=
  outcome ∈ region.branchLocal live

/-- The region still has an outcome exactly when the proposal is one of its
alternatives, its steps can be published on the live state, and the answer read
from the result is the answer of the outcome. -/
theorem Region.stillHas_iff {region : Region Location Value Answer} {live : Location → Value}
    {outcome : Answer × Proposal Location Value Answer} :
    region.StillHas live outcome ↔
      outcome.2 ∈ region.proposals ∧
        ∃ view, publish outcome.2.steps live = some view ∧
          outcome.2.readout.value view = outcome.1 := by
  rw [Region.StillHas, Region.mem_branchLocal_iff, Proposal.outcome?_eq_some_iff]
  constructor
  · rintro ⟨member, view, published, same⟩
    exact ⟨member, view, published, congrArg Prod.fst same⟩
  · rintro ⟨member, view, published, same⟩
    exact ⟨member, view, published, Prod.ext same rfl⟩

/-- **Validation is sound.**  If the live state agrees with the snapshot on what
a proposal read and wrote, the region replayed on the live state has that
outcome. -/
theorem Region.stillHas_of_readsKept {region : Region Location Value Answer}
    {snapshot live : Location → Value} {outcome : Answer × Proposal Location Value Answer}
    (explored : outcome ∈ region.branchLocal snapshot)
    (kept : outcome.2.ReadsKept snapshot live) : region.StillHas live outcome := by
  obtain ⟨member, has⟩ := Region.mem_branchLocal_iff.mp explored
  exact Region.mem_branchLocal_iff.mpr ⟨member, (outcome.2.outcome?_congr kept) ▸ has⟩

/-- **Under the first validation, publication installs the private view**: the
published state is the view the proposal reached from its snapshot on the
locations it wrote, and the live state on every other location. -/
theorem Proposal.publish_eq_piecewise (proposal : Proposal Location Value Answer)
    {snapshot view live : Location → Value}
    (published : publish proposal.steps snapshot = some view)
    (kept : proposal.ReadsKept snapshot live) :
    publish proposal.steps live = some (proposal.writes.piecewise view live) := by
  obtain ⟨liveView, livePublished, written, outside⟩ :=
    (publish_effectFootprinted proposal.steps).frame published live
      (agreesOn_mono
        (Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _)) kept)
  rw [livePublished]
  congr 1
  funext location
  by_cases isWritten : location ∈ proposal.writes
  · rw [Finset.piecewise_eq_of_mem _ _ _ isWritten]
    exact (written location isWritten).symm
  · rw [Finset.piecewise_eq_of_notMem _ _ _ isWritten]
    exact outside location isWritten

/-- **The private view is an overlay over the snapshot**: it is the snapshot on
every location the proposal did not write. -/
theorem Proposal.view_eq_piecewise (proposal : Proposal Location Value Answer)
    {snapshot view : Location → Value}
    (published : publish proposal.steps snapshot = some view) :
    view = proposal.writes.piecewise view snapshot :=
  Option.some.inj
    (published.symm.trans (proposal.publish_eq_piecewise published (agreesOn_refl _ _)))

/-! ## Serializability -/

/-- **Publication in order, validated by replay.**  The outcomes are published
one after another.  Each is checked when its turn comes: its steps must fire on
the state reached, and the answer read from the result must be the answer of the
outcome.  Otherwise the sequence is refused. -/
def publishInOrder [DecidableEq Answer] :
    List (Answer × Proposal Location Value Answer) → (Location → Value) →
      Option (Location → Value)
  | [], world => some world
  | outcome :: rest, world =>
      (publish outcome.2.steps world).bind fun next =>
        if outcome.2.readout.value next = outcome.1 then publishInOrder rest next else none

/-- **Publication in order, validated by kept reads.**  Each entry is an outcome
with the snapshot it was explored from.  When its turn comes its reads must be
kept on the state reached; then its steps are published there. -/
def publishWithKeptReads [DecidableEq Value] :
    List ((Location → Value) × (Answer × Proposal Location Value Answer)) →
      (Location → Value) → Option (Location → Value)
  | [], world => some world
  | entry :: rest, world =>
      if entry.2.2.ReadsKept entry.1 world then
        (publish entry.2.2.steps world).bind (publishWithKeptReads rest)
      else none

/-- **Serializability.**  A sequence of publications, each valid when it was
made, is the committed run of the published alternatives in the order of
publication: the answers returned are the answers of that run, and the final
state is its state. -/
theorem publishInOrder_serializable [DecidableEq Answer]
    {outcomes : List (Answer × Proposal Location Value Answer)} {world final : Location → Value}
    (published : publishInOrder outcomes world = some final) :
    (Region.alternatives (outcomes.map fun outcome => outcome.2.region)).committed world =
      (outcomes.map Prod.fst, final) := by
  induction outcomes generalizing world with
  | nil =>
      cases published
      rfl
  | cons outcome rest ih =>
      rw [publishInOrder, Option.bind_eq_some_iff] at published
      obtain ⟨next, headPublished, tail⟩ := published
      split at tail
      · next sameAnswer =>
        have head := outcome.2.region_committed headPublished
        show ((outcome.2.region.committed world).1 ++
            ((Region.alternatives (rest.map fun outcome => outcome.2.region)).committed
              (outcome.2.region.committed world).2).1,
          ((Region.alternatives (rest.map fun outcome => outcome.2.region)).committed
            (outcome.2.region.committed world).2).2) = _
        rw [head, ih tail, sameAnswer]
        rfl
      · cases tail

/-- Validation by kept reads implies validation by replay, along a whole sequence:
if every entry was explored from its snapshot, a sequence published with kept
reads is published in order. -/
theorem publishInOrder_of_keptReads [DecidableEq Value] [DecidableEq Answer]
    {entries : List ((Location → Value) × (Answer × Proposal Location Value Answer))}
    {world final : Location → Value}
    (explored : ∀ entry ∈ entries, entry.2.2.outcome? entry.1 = some entry.2)
    (published : publishWithKeptReads entries world = some final) :
    publishInOrder (entries.map Prod.snd) world = some final := by
  induction entries generalizing world with
  | nil => exact published
  | cons entry rest ih =>
      rw [publishWithKeptReads] at published
      split at published
      · next kept =>
        rw [Option.bind_eq_some_iff] at published
        obtain ⟨next, headPublished, tail⟩ := published
        have replayed : entry.2.2.outcome? world = some entry.2 :=
          (entry.2.2.outcome?_congr kept) ▸ explored entry List.mem_cons_self
        obtain ⟨view, viewPublished, same⟩ := Proposal.outcome?_eq_some_iff.mp replayed
        have sameView : view = next := Option.some.inj (viewPublished.symm.trans headPublished)
        have sameAnswer : entry.2.2.readout.value next = entry.2.1 := by
          rw [← sameView]
          exact congrArg Prod.fst same
        show publishInOrder (entry.2 :: rest.map Prod.snd) world = some final
        rw [publishInOrder, headPublished, Option.bind_some, if_pos sameAnswer]
        exact ih (fun other member => explored other (List.mem_cons_of_mem entry member)) tail
      · cases published

/-- **Serializability, with the first validation.**  If every proposal was
explored from its snapshot and published while its reads were kept, the answers
that were computed from the snapshots are the answers of the committed run of
the published alternatives in the order of publication, and the final state is
its state. -/
theorem publishWithKeptReads_serializable [DecidableEq Value] [DecidableEq Answer]
    {entries : List ((Location → Value) × (Answer × Proposal Location Value Answer))}
    {world final : Location → Value}
    (explored : ∀ entry ∈ entries, entry.2.2.outcome? entry.1 = some entry.2)
    (published : publishWithKeptReads entries world = some final) :
    (Region.alternatives (entries.map fun entry => entry.2.2.region)).committed world =
      (entries.map fun entry => entry.2.1, final) := by
  have serial := publishInOrder_serializable (publishInOrder_of_keptReads explored published)
  simpa [List.map_map, Function.comp_def] using serial

end Validation

/-! ## Controls -/

namespace Controls

/-- Take one `0` from the space. -/
def takeToken : Proposal Store (Multiset ℕ) Unit :=
  ⟨[Step.removeAtom .space 0], Readout.const ()⟩

/-- Add one `1` to the space. -/
def addOne : Proposal Store (Multiset ℕ) Unit :=
  ⟨[Step.addAtom .space 1], Readout.const ()⟩

/-- The space holds two tokens. -/
def twoTokens : Network Store ℕ := Pi.single .space {0, 0}

/-- The space holds one token. -/
def oneToken : Network Store ℕ := Pi.single .space {0}

theorem takeToken_publishable_twice : (publish takeToken.steps twoTokens).isSome := by
  decide

/-- The state after one of two tokens was taken. -/
def afterFirstOfTwo : Network Store ℕ :=
  (publish takeToken.steps twoTokens).get takeToken_publishable_twice

theorem takeToken_publishable_once : (publish takeToken.steps oneToken).isSome := by
  decide

/-- The state after the only token was taken. -/
def afterLast : Network Store ℕ :=
  (publish takeToken.steps oneToken).get takeToken_publishable_once

theorem addOne_publishable : (publish addOne.steps empty).isSome := by
  decide

/-- The state after one atom was added to the empty space. -/
def afterFirstAdd : Network Store ℕ :=
  (publish addOne.steps empty).get addOne_publishable

/-- With two tokens, the region that takes one has its outcome. -/
theorem takeToken_explored : ((), takeToken) ∈ takeToken.region.branchLocal twoTokens :=
  Region.stillHas_iff.mpr
    ⟨by simp [Proposal.region_proposals], _,
      (Option.some_get takeToken_publishable_twice).symm, rfl⟩

/-- **Positive, first validation**: a change in another store keeps the reads. -/
theorem takeToken_reads_kept_elsewhere :
    takeToken.ReadsKept twoTokens (twoTokens + Pi.single .cell {5}) := by
  decide

/-- **Strictness.**  After the first of two tokens was taken, the reads of the
second taker are not kept: the space it read has changed. -/
theorem second_copy_reads_not_kept : ¬ takeToken.ReadsKept twoTokens afterFirstOfTwo := by
  decide

/-- And its region still has the outcome: there is a token left to take. -/
theorem second_copy_stillHas : takeToken.region.StillHas afterFirstOfTwo ((), takeToken) :=
  Region.stillHas_iff.mpr
    ⟨by simp [Proposal.region_proposals],
      Option.isSome_iff_exists.mp (by decide : (publish takeToken.steps afterFirstOfTwo).isSome)
        |>.elim fun view published => ⟨view, published, rfl⟩⟩

/-- **Negative, both validations**: after the only token was taken the second
taker has lost its outcome. -/
theorem last_copy_not_stillHas : ¬ takeToken.region.StillHas afterLast ((), takeToken) := by
  intro still
  obtain ⟨-, view, published, -⟩ := Region.stillHas_iff.mp still
  have refused : (publish takeToken.steps afterLast).isSome = false := by decide
  rw [published] at refused
  cases refused

theorem last_copy_reads_not_kept : ¬ takeToken.ReadsKept oneToken afterLast := by
  decide

/-- **Strictness, for additions.**  After one atom was added, the reads of a
second region that adds an atom to the same space are not kept. -/
theorem second_add_reads_not_kept : ¬ addOne.ReadsKept empty afterFirstAdd := by
  decide

/-- And its region still has the outcome: an addition fires on every state. -/
theorem second_add_stillHas : addOne.region.StillHas afterFirstAdd ((), addOne) :=
  Region.stillHas_iff.mpr
    ⟨by simp [Proposal.region_proposals],
      Option.isSome_iff_exists.mp (by decide : (publish addOne.steps afterFirstAdd).isSome)
        |>.elim fun view published => ⟨view, published, rfl⟩⟩

/-- **Positive, publication in order**: two takers of two tokens are published
one after the other, and leave the space empty. -/
theorem two_takers_published_in_order :
    (publishInOrder [((), takeToken), ((), takeToken)] twoTokens).map (fun world => world .space) =
      some 0 := by
  decide

/-- **Negative, publication in order**: two takers of one token are refused. -/
theorem two_takers_of_one_token_refused :
    (publishInOrder [((), takeToken), ((), takeToken)] oneToken).isSome = false := by
  decide

/-- **Positive, kept reads**: one taker explored from the state it is published
on. -/
theorem one_taker_published_with_kept_reads :
    (publishWithKeptReads [(twoTokens, ((), takeToken))] twoTokens).map
        (fun world => world .space) = some {0} := by
  decide

/-- **Negative, kept reads**: of two takers explored from one snapshot the second
is refused by the first validation, although publication in order admits it. -/
theorem second_taker_refused_by_kept_reads :
    (publishWithKeptReads [(twoTokens, ((), takeToken)), (twoTokens, ((), takeToken))]
      twoTokens).isSome = false := by
  decide

end Controls

#print axioms Region.stillHas_iff
#print axioms Region.stillHas_of_readsKept
#print axioms Proposal.publish_eq_piecewise
#print axioms Proposal.view_eq_piecewise
#print axioms publishInOrder_serializable
#print axioms publishInOrder_of_keptReads
#print axioms publishWithKeptReads_serializable
#print axioms Controls.takeToken_explored
#print axioms Controls.takeToken_reads_kept_elsewhere
#print axioms Controls.second_copy_reads_not_kept
#print axioms Controls.second_copy_stillHas
#print axioms Controls.last_copy_not_stillHas
#print axioms Controls.last_copy_reads_not_kept
#print axioms Controls.second_add_reads_not_kept
#print axioms Controls.second_add_stillHas
#print axioms Controls.two_takers_published_in_order
#print axioms Controls.two_takers_of_one_token_refused
#print axioms Controls.one_taker_published_with_kept_reads
#print axioms Controls.second_taker_refused_by_kept_reads

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
