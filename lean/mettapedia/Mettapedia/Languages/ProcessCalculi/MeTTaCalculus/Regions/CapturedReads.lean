import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Waves
import Mettapedia.Machines.RevisionDependencySet

/-!
# The first validation is the publication contract of a captured read view

`Machines.RevisionDependencySet` has captured read views: a computation is
admitted against a whole environment, records the names it consults, and may
publish when no consulted name has changed (`CapturedReadView.CanPublish`).  A
finite delta outside the consulted names keeps the view publishable
(`CapturedReadView.canPublish_applyWrites_iff`).

A located state is such an environment, with the value at a location as its
revision.  The read view of a proposal (`Proposal.readView`) is admitted against
the snapshot and has consulted the locations the proposal read or wrote.

* `Proposal.readsKept_iff_canPublish`: the reads of a proposal are kept on a live
  state exactly when its read view can publish there.
* `Proposal.canPublish_of_independent`: after an independent proposal has been
  published, the read view of the other can still publish.

So the first validation of `Regions.Validation` is that contract, and what this
development adds to it is the consequence: when the view can publish, the region
replayed on the live state has the outcome (`Region.stillHas_of_readsKept`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines

universe w

variable {Location Value : Type} {Answer : Type w} [DecidableEq Location] [DecidableEq Value]
  [Zero Value] [Add Value] [SepAlgebra Value]

/-- **The read view of a proposal**: admitted against the snapshot it was explored
from, complete, with no mismatch seen, and having consulted the locations the
proposal read or wrote. -/
noncomputable def Proposal.readView (proposal : Proposal Location Value Answer)
    (snapshot : Location → Value) : CapturedReadView Location Value where
  captured := ⟨snapshot⟩
  consulted := (proposal.reads ∪ proposal.writes).toList
  firstMismatch := none
  captureComplete := true

/-- **The reads of a proposal are kept exactly when its read view can publish.** -/
theorem Proposal.readsKept_iff_canPublish (proposal : Proposal Location Value Answer)
    (snapshot live : Location → Value) :
    proposal.ReadsKept snapshot live ↔ (proposal.readView snapshot).CanPublish ⟨live⟩ := by
  unfold CapturedReadView.CanPublish
  rw [CapturedReadView.valid_dependencies_iff]
  have consulted : (proposal.readView snapshot).consulted.toFinset =
      proposal.reads ∪ proposal.writes :=
    Finset.toList_toFinset _
  rw [consulted]
  constructor
  · intro kept
    exact ⟨rfl, rfl, fun location inside => (kept location inside).symm⟩
  · rintro ⟨-, -, agrees⟩
    exact fun location inside => (agrees location inside).symm

/-- **After an independent publication the read view can still publish.** -/
theorem Proposal.canPublish_of_independent {first second : Proposal Location Value Answer}
    (independent : first.Independent second) {world next : Location → Value}
    (published : publish first.steps world = some next) :
    (second.readView world).CanPublish ⟨next⟩ :=
  (second.readsKept_iff_canPublish world next).mp
    (Proposal.readsKept_of_independent independent published)

/-! ## Controls -/

namespace Controls

/-- **Positive**: a change in another store leaves the read view of a taker
publishable. -/
theorem taker_view_can_publish_elsewhere :
    (takeToken.readView twoTokens).CanPublish ⟨twoTokens + Pi.single .cell {5}⟩ :=
  (takeToken.readsKept_iff_canPublish _ _).mp takeToken_reads_kept_elsewhere

/-- **Negative**: after the first of two tokens was taken, the read view of the
second taker cannot publish. -/
theorem second_taker_view_cannot_publish :
    ¬ (takeToken.readView twoTokens).CanPublish ⟨afterFirstOfTwo⟩ := fun allowed =>
  second_copy_reads_not_kept ((takeToken.readsKept_iff_canPublish _ _).mpr allowed)

end Controls

#print axioms Proposal.readsKept_iff_canPublish
#print axioms Proposal.canPublish_of_independent
#print axioms Controls.taker_view_can_publish_elsewhere
#print axioms Controls.second_taker_view_cannot_publish

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
