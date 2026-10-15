import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Waves
import Mettapedia.GSLT.Core.AtomicSnapshotTransaction

/-!
# The commit border over the atomic snapshot transaction

`GSLT.Core.AtomicSnapshotTransaction` is the transaction boundary with the
coarsest validation: a proposal is committed only when the live revision and the
whole live state are those it was captured from, and after one commit every
proposal captured from that revision is refused, its work kept as pending.  This
module reads the outcomes of regions through that boundary and adds no second
boundary.

* `Explored` is an outcome of a region waiting at the border: the region, the
  snapshot it was explored from, the outcome with the evidence that the region
  has it from that snapshot, and the work paid for it.  `commitBorder` is the
  `Spec` that tells the boundary how to read it: the captured snapshot, the state
  that publishing the proposal on that snapshot gives, the work.
* `Explored.readsKept_of_matches`: the validation of the boundary implies the
  first validation.  The converse fails (`Controls.reads_kept_without_match`).
* `Explored.refresh` captures the same outcome again over a live snapshot on
  which the region still has it.  The new capture matches the live snapshot
  (`Explored.refresh_matches`), so the boundary commits it
  (`Explored.refreshReceipt`), and what it commits is the publication of the
  proposal on the live state (`Explored.refresh_publish`).  The old capture is
  not revived: it stays refused.  A refresh is a new proposal tied to the whole
  current snapshot, as in `GSLT.Core.AtomicDeferredDisposition`; here it exists
  only when the region still has the outcome whose answer was returned.
* `Explored.independent_sibling_survives_commit`: **the frame law refines the
  boundary.**  After one commit the boundary refuses a sibling captured from the
  same snapshot.  If the committed proposal is independent of the sibling's, the
  sibling's reads are kept on the committed state, its region still has its
  outcome there, and captured again it matches.
* `Explored.publication` is publication validated by kept reads, as a decision of
  the boundary: commit of the new capture, or deferral of the old one.
  `Explored.publication_of_readsKept` and
  `Explored.publication_of_reads_not_kept` say what each does to the state and to
  the work: **a refused proposal changes nothing and keeps its work**; no work
  vanishes in either case (`Explored.publication_ledger`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Core.AtomicSnapshotTransaction

universe u v w x y

/-- **An outcome of a region at the commit border.** -/
structure Explored (Location : Type u) (Value : Type v) (Answer : Type w) (Revision : Type x)
    (Work : Type y) [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value] where
  /-- The region that was run in the branch-local mode. -/
  region : Region Location Value Answer
  /-- The snapshot it was run from. -/
  snapshot : Snapshot Revision (Location → Value)
  /-- One of its outcomes: an answer and a proposal. -/
  outcome : Answer × Proposal Location Value Answer
  /-- The work paid for the outcome. -/
  work : List Work
  /-- The region has the outcome from the snapshot. -/
  explored : outcome ∈ region.branchLocal snapshot.state

variable {Location : Type u} {Value : Type v} {Answer : Type w} {Revision : Type x}
  {Work : Type y}

section Border

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

namespace Explored

/-- The proposal of an explored outcome can be published on its own snapshot. -/
theorem publishable (entry : Explored Location Value Answer Revision Work) :
    (publish entry.outcome.2.steps entry.snapshot.state).isSome := by
  obtain ⟨view, published, -⟩ := Region.committed_of_mem_branchLocal entry.explored
  rw [published]
  rfl

/-- The state that publishing the proposal on its own snapshot gives. -/
def target (entry : Explored Location Value Answer Revision Work) : Location → Value :=
  (publish entry.outcome.2.steps entry.snapshot.state).get entry.publishable

theorem publish_snapshot (entry : Explored Location Value Answer Revision Work) :
    publish entry.outcome.2.steps entry.snapshot.state = some entry.target :=
  (Option.some_get entry.publishable).symm

end Explored

/-- **The commit border, as the atomic boundary reads it**: the captured
snapshot, the published state, the work. -/
def commitBorder :
    Spec Revision (Location → Value) Work (Explored Location Value Answer Revision Work) where
  capturedRevision entry := entry.snapshot.revision
  capturedState entry := entry.snapshot.state
  targetState entry := entry.target
  pendingWork entry := entry.work

namespace Explored

/-- **The validation of the boundary implies the first validation**: a live
snapshot that equals the captured one keeps every read. -/
theorem readsKept_of_matches {entry : Explored Location Value Answer Revision Work}
    {live : Snapshot Revision (Location → Value)} (current : Matches commitBorder entry live) :
    entry.outcome.2.ReadsKept entry.snapshot.state live.state := by
  have same : live.state = entry.snapshot.state := current.state_eq
  rw [same]
  exact agreesOn_refl _ _

/-- **Refresh**: a new capture of the same region, outcome and work, over a live
snapshot on which the region still has the outcome.  The evidence that it still
has it is what makes the new capture one. -/
def refresh (entry : Explored Location Value Answer Revision Work)
    (live : Snapshot Revision (Location → Value))
    (still : entry.region.StillHas live.state entry.outcome) :
    Explored Location Value Answer Revision Work :=
  { entry with snapshot := live, explored := still }

/-- The new capture matches the live snapshot. -/
theorem refresh_matches (entry : Explored Location Value Answer Revision Work)
    (live : Snapshot Revision (Location → Value))
    (still : entry.region.StillHas live.state entry.outcome) :
    Matches commitBorder (entry.refresh live still) live :=
  ⟨rfl, rfl⟩

/-- So the boundary commits it, with any fresh revision. -/
def refreshReceipt (entry : Explored Location Value Answer Revision Work)
    (live : Snapshot Revision (Location → Value))
    (still : entry.region.StillHas live.state entry.outcome) (next : Revision)
    (advanced : next ≠ live.revision) :
    CommitReceipt commitBorder (entry.refresh live still) live where
  current := entry.refresh_matches live still
  nextRevision := next
  advanced := advanced

/-- What it commits is the publication of the proposal on the live state. -/
theorem refresh_publish (entry : Explored Location Value Answer Revision Work)
    (live : Snapshot Revision (Location → Value))
    (still : entry.region.StillHas live.state entry.outcome) :
    publish entry.outcome.2.steps live.state = some (entry.refresh live still).target :=
  (entry.refresh live still).publish_snapshot

/-- **The frame law refines the boundary.**  After the commit of one proposal the
boundary refuses a sibling captured from the same snapshot.  If the committed
proposal is independent of the sibling's, the sibling's reads are kept on the
committed state, its region still has its outcome there, and captured again it
matches. -/
theorem independent_sibling_survives_commit
    {first second : Explored Location Value Answer Revision Work}
    {live : Snapshot Revision (Location → Value)}
    (receipt : CommitReceipt commitBorder first live)
    (sameSnapshot : second.snapshot = first.snapshot)
    (independent : first.outcome.2.Independent second.outcome.2) :
    ¬ Matches commitBorder second receipt.after ∧
      second.outcome.2.ReadsKept second.snapshot.state receipt.after.state ∧
      ∃ still : second.region.StillHas receipt.after.state second.outcome,
        Matches commitBorder (second.refresh receipt.after still) receipt.after := by
  have kept : second.outcome.2.ReadsKept second.snapshot.state receipt.after.state := by
    rw [sameSnapshot]
    exact Proposal.readsKept_of_independent independent first.publish_snapshot
  exact ⟨receipt.after_rejects_same_revision_sibling (congrArg Snapshot.revision sameSnapshot),
    kept, Region.stillHas_of_readsKept second.explored kept, second.refresh_matches _ _⟩

/-- **Publication at the border, validated by kept reads.**  If the live state
agrees with the snapshot on what the proposal read and wrote, the outcome is
captured again over the live snapshot and the boundary commits it.  Otherwise the
boundary defers the old capture. -/
def publication [DecidableEq Value] (entry : Explored Location Value Answer Revision Work)
    (live : Snapshot Revision (Location → Value)) (next : Revision)
    (advanced : next ≠ live.revision) :
    (captured : Explored Location Value Answer Revision Work) ×
      Decision commitBorder captured live :=
  if kept : entry.outcome.2.ReadsKept entry.snapshot.state live.state then
    ⟨entry.refresh live (Region.stillHas_of_readsKept entry.explored kept),
      .committed (entry.refreshReceipt live _ next advanced)⟩
  else ⟨entry, .deferred fun current => kept (entry.readsKept_of_matches current)⟩

/-- **A proposal whose reads are kept is published**: the state becomes the
publication of the proposal on the live state, at the fresh revision, and the
work is executed. -/
theorem publication_of_readsKept [DecidableEq Value]
    (entry : Explored Location Value Answer Revision Work)
    (live : Snapshot Revision (Location → Value)) (next : Revision)
    (advanced : next ≠ live.revision)
    (kept : entry.outcome.2.ReadsKept entry.snapshot.state live.state)
    {published : Location → Value}
    (publishes : publish entry.outcome.2.steps live.state = some published) :
    (entry.publication live next advanced).2.physicalSnapshot = ⟨next, published⟩ ∧
      (entry.publication live next advanced).2.ledger.executed = (entry.work : Multiset Work) ∧
      (entry.publication live next advanced).2.ledger.pending = 0 := by
  have unfolded : entry.publication live next advanced =
      ⟨entry.refresh live (Region.stillHas_of_readsKept entry.explored kept),
        .committed (entry.refreshReceipt live _ next advanced)⟩ := by
    unfold publication
    exact dif_pos kept
  rw [unfolded]
  refine ⟨?_, rfl, rfl⟩
  have same : (entry.refresh live (Region.stillHas_of_readsKept entry.explored kept)).target =
      published :=
    Option.some.inj ((entry.refresh_publish live _).symm.trans publishes)
  show (⟨next, (entry.refresh live _).target⟩ : Snapshot Revision (Location → Value)) = _
  rw [same]

/-- **A refused proposal changes nothing and keeps its work**: the live snapshot
is returned as it is, nothing is executed, and the whole work is pending. -/
theorem publication_of_reads_not_kept [DecidableEq Value]
    (entry : Explored Location Value Answer Revision Work)
    (live : Snapshot Revision (Location → Value)) (next : Revision)
    (advanced : next ≠ live.revision)
    (changed : ¬ entry.outcome.2.ReadsKept entry.snapshot.state live.state) :
    (entry.publication live next advanced).2.physicalSnapshot = live ∧
      (entry.publication live next advanced).2.ledger.executed = 0 ∧
      (entry.publication live next advanced).2.ledger.pending = (entry.work : Multiset Work) := by
  have unfolded : entry.publication live next advanced =
      ⟨entry, .deferred fun current => changed (entry.readsKept_of_matches current)⟩ := by
    unfold publication
    exact dif_neg changed
  rw [unfolded]
  exact ⟨rfl, rfl, rfl⟩

/-- **No work vanishes at the border**: executed and pending together are the
work of the proposal, whether it was published or refused. -/
theorem publication_ledger [DecidableEq Value]
    (entry : Explored Location Value Answer Revision Work)
    (live : Snapshot Revision (Location → Value)) (next : Revision)
    (advanced : next ≠ live.revision) :
    (entry.publication live next advanced).2.ledger.executed +
        (entry.publication live next advanced).2.ledger.pending =
      (entry.work : Multiset Work) := by
  have accounts := (entry.publication live next advanced).2.ledger_accounts
  rw [accounts]
  unfold publication
  split <;> rfl

end Explored

end Border

/-! ## Controls -/

namespace Controls

/-- The snapshot with one token, at revision `0`. -/
def start : Snapshot ℕ (Network Store ℕ) := ⟨0, oneToken⟩

theorem taker_explored : ((), takeToken) ∈ takeToken.region.branchLocal oneToken :=
  Region.stillHas_iff.mpr
    ⟨by simp [Proposal.region_proposals], _, (Option.some_get takeToken_publishable_once).symm, rfl⟩

/-- A taker of the only token, captured from the start, with one labelled unit
of work. -/
def taker (label : ℕ) : Explored Store (Multiset ℕ) Unit ℕ ℕ where
  region := takeToken.region
  snapshot := start
  outcome := ((), takeToken)
  work := [label]
  explored := taker_explored

/-- **Negative**: there is no explored outcome of the taker from a snapshot with
no token: the evidence that the region has an outcome cannot be given. -/
theorem no_taker_without_token :
    ¬ ∃ entry : Explored Store (Multiset ℕ) Unit ℕ ℕ,
      entry.region = takeToken.region ∧ entry.snapshot.state = empty := by
  rintro ⟨entry, sameRegion, sameState⟩
  have explored := entry.explored
  rw [sameRegion, sameState] at explored
  have noOutcome : takeToken.region.branchLocal empty = [] := by decide
  rw [noOutcome] at explored
  cases explored

/-- The snapshot after the first taker was published. -/
def afterFirstTaker : Snapshot ℕ (Network Store ℕ) := ⟨1, afterLast⟩

/-- **Positive**: the first taker is published: the token is gone at the fresh
revision and its work is executed. -/
theorem first_taker_published :
    ((taker 1).publication start 1 (by decide)).2.physicalSnapshot = afterFirstTaker ∧
      ((taker 1).publication start 1 (by decide)).2.ledger.executed = {1} ∧
      ((taker 1).publication start 1 (by decide)).2.ledger.pending = 0 :=
  (taker 1).publication_of_readsKept start 1 (by decide) (agreesOn_refl _ _)
    (Option.some_get takeToken_publishable_once).symm

/-- **A race, reported**: publishing the first taker refuses the second.  The
refused one changes nothing and keeps its work. -/
theorem second_taker_refused :
    ((taker 2).publication afterFirstTaker 2 (by decide)).2.physicalSnapshot = afterFirstTaker ∧
      ((taker 2).publication afterFirstTaker 2 (by decide)).2.ledger.executed = 0 ∧
      ((taker 2).publication afterFirstTaker 2 (by decide)).2.ledger.pending = {2} :=
  (taker 2).publication_of_reads_not_kept afterFirstTaker 2 (by decide) last_copy_reads_not_kept

/-- And it could not have been captured again: its region no longer has the
outcome. -/
theorem second_taker_cannot_refresh :
    ¬ (taker 2).region.StillHas afterFirstTaker.state (taker 2).outcome :=
  last_copy_not_stillHas

theorem mark_explored : ((), mark) ∈ mark.region.branchLocal oneToken :=
  Region.stillHas_iff.mpr
    ⟨by simp [Proposal.region_proposals],
      Option.isSome_iff_exists.mp (by decide : (publish mark.steps oneToken).isSome)
        |>.elim fun view published => ⟨view, published, rfl⟩⟩

/-- A sibling of the takers that marks the cell, captured from the same start. -/
def marker : Explored Store (Multiset ℕ) Unit ℕ ℕ where
  region := mark.region
  snapshot := start
  outcome := ((), mark)
  work := [3]
  explored := mark_explored

/-- The receipt of the first taker at the start. -/
def firstTakerReceipt : CommitReceipt commitBorder (taker 1) start where
  current := ⟨rfl, rfl⟩
  nextRevision := 1
  advanced := by decide

/-- **Positive, refinement**: after the first taker commits, the boundary refuses
the marker, which was captured from the same snapshot; its reads are kept, and
captured again it matches. -/
theorem marker_survives_commit :
    ¬ Matches commitBorder marker firstTakerReceipt.after ∧
      marker.outcome.2.ReadsKept marker.snapshot.state firstTakerReceipt.after.state ∧
      ∃ still : marker.region.StillHas firstTakerReceipt.after.state marker.outcome,
        Matches commitBorder (marker.refresh firstTakerReceipt.after still)
          firstTakerReceipt.after :=
  Explored.independent_sibling_survives_commit firstTakerReceipt rfl (by decide)

/-- One token in the space and a note in the cell. -/
def oneTokenAndNote : Network Store ℕ := oneToken + Pi.single .cell {5}

/-- **The first validation is strictly weaker than the validation of the
boundary**: with a change in another store the reads of a taker are kept, and
the captured snapshot does not match. -/
theorem reads_kept_without_match :
    takeToken.ReadsKept oneToken oneTokenAndNote ∧
      ¬ Matches commitBorder (taker 1) ⟨0, oneTokenAndNote⟩ := by
  refine ⟨by decide, fun current => ?_⟩
  have same : oneTokenAndNote Store.cell = oneToken Store.cell :=
    congrFun current.state_eq Store.cell
  exact absurd same (by decide)

end Controls

#print axioms Explored.readsKept_of_matches
#print axioms Explored.refresh_matches
#print axioms Explored.refresh_publish
#print axioms Explored.independent_sibling_survives_commit
#print axioms Explored.publication_of_readsKept
#print axioms Explored.publication_of_reads_not_kept
#print axioms Explored.publication_ledger
#print axioms Controls.no_taker_without_token
#print axioms Controls.first_taker_published
#print axioms Controls.second_taker_refused
#print axioms Controls.second_taker_cannot_refresh
#print axioms Controls.marker_survives_commit
#print axioms Controls.reads_kept_without_match

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
