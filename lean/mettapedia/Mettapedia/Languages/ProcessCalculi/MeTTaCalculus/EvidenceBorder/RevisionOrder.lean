import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder.BranchLocalCount
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Granularity

/-!
# Commuting revisions and a read/write conflict

Revisions of one count commute, so evidence publications that write that one
location have one result in every order. Independence by read and write sets
(`wave_every_order`) calls two proposals that write one location a conflict:
`Policy.publishWave` returns none, and the independence premise of
`wave_every_order` is false. The two readings disagree on that pair.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Controls
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.AddOnly
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Logic.EvidenceStateInsufficiency

/-- Revisions of one count commute, and so the two orders of two evidence
publications into that count are one state. -/
theorem revisions_publish_in_every_order (counts : Counts) (left right : Bool) :
    (counts.revise left).revise right = (counts.revise right).revise left ∧
      [left, right].foldl Counts.revise counts = [right, left].foldl Counts.revise counts := by
  refine ⟨?commute, ?orders⟩
  · cases counts
    cases left <;> cases right <;> rfl
  · cases counts
    cases left <;> cases right <;> rfl

/-- **Positive, where the premise holds.** Two pure observations write nothing,
so `wave_every_order` publishes them in both orders with one final state. -/
theorem independent_observations_every_order :
    let outcomes := purePair.branchLocal emptyFlag
    let swapped :=
      (Region.alternatives [pureObservation false, pureObservation true]).branchLocal emptyFlag
    ∃ final,
      publishWithKeptReads (outcomes.map fun outcome => (emptyFlag, outcome)) emptyFlag =
        some final ∧
      publishWithKeptReads (swapped.map fun outcome => (emptyFlag, outcome)) emptyFlag =
        some final := by
  refine wave_every_order ?explored ?independent ?perm
  · intro outcome member
    exact (Region.mem_branchLocal_iff.mp member).2
  · decide
  · exact (Region.branchLocal_alternatives_perm
      (List.Perm.swap (pureObservation true) (pureObservation false) []) emptyFlag).symm

/-- One sibling writes the space, the one location, and returns a Boolean
observation. -/
def writingOneLocation (observation : Bool) (atom : Kind) :
    Region Store (Multiset Kind) Bool :=
  .step (Step.addAtom .space atom) (.answer (Readout.const observation))

theorem writingOneLocation_returns (observation : Bool) (atom : Kind) :
    ((writingOneLocation observation atom).branchLocal noAtoms).map Prod.fst = [observation] := by
  cases observation <;> cases atom <;> decide

theorem writingOneLocation_writes_space (observation : Bool) (atom : Kind) :
    ((writingOneLocation observation atom).branchLocal noAtoms).map
        (fun outcome => outcome.2.writes) = [{Store.space}] ∧
      writingOneLocation observation atom ≠ (Region.fail : Region Store (Multiset Kind) Bool) := by
  refine ⟨?writes, ?notFail⟩
  · cases observation <;> cases atom <;> decide
  · intro same
    cases same

/-- The two publications: `true` then `false`, both writing `Store.space`. -/
def oneLocationPair : Region Store (Multiset Kind) Bool :=
  Region.alternatives [writingOneLocation true .a, writingOneLocation false .b]

theorem oneLocationPair_answers :
    ((oneLocationPair.branchLocal noAtoms).map Prod.fst) = [true, false] := by
  decide

theorem oneLocationPair_not_swapped :
    ((oneLocationPair.branchLocal noAtoms).map Prod.fst) ≠ [false, true] := by
  decide

/-- The same two publications, false and then true. -/
def oneLocationPairSwapped : Region Store (Multiset Kind) Bool :=
  Region.alternatives [writingOneLocation false .b, writingOneLocation true .a]

theorem oneLocationPairSwapped_answers :
    ((oneLocationPairSwapped.branchLocal noAtoms).map Prod.fst) = [false, true] := by
  decide

theorem oneLocationPairSwapped_not_original :
    ((oneLocationPairSwapped.branchLocal noAtoms).map Prod.fst) ≠ [true, false] := by
  decide

/-- **Both readings of one pair.** The two publications write `Store.space`.
`revisions_publish_in_every_order` says their observations revise one count in
either order. `wave_every_order` asks for pairwise `Proposal.Independent`, and
that premise is false; `Policy.publishWave` returns none. -/
theorem one_location_publications_conflict :
    ((oneLocationPair.branchLocal noAtoms).map Prod.fst) = [true, false] ∧
      ((oneLocationPairSwapped.branchLocal noAtoms).map Prod.fst) = [false, true] ∧
      ((oneLocationPair.branchLocal noAtoms).map fun outcome => outcome.2.writes) =
        [{Store.space}, {Store.space}] ∧
      ((oneLocationPairSwapped.branchLocal noAtoms).map fun outcome => outcome.2.writes) =
        [{Store.space}, {Store.space}] ∧
      countObservations ((oneLocationPair.branchLocal noAtoms).map Prod.fst) =
        countObservations ((oneLocationPairSwapped.branchLocal noAtoms).map Prod.fst) ∧
      ((⟨0, 0⟩ : Counts).revise true).revise false =
        ((⟨0, 0⟩ : Counts).revise false).revise true ∧
      ¬ (oneLocationPair.branchLocal noAtoms).Pairwise
        (fun first second => first.2.Independent second.2) ∧
      (oneLocationPair.observe Policy.publishWave noAtoms).2 = none := by
  have answers := oneLocationPair_answers
  have swapped := oneLocationPairSwapped_answers
  have comm := revisions_publish_in_every_order ⟨0, 0⟩ true false
  refine ⟨answers, swapped, ?writes, ?writesSwapped, ?counts, comm.1, ?premise, ?refused⟩
  · decide
  · decide
  · rw [answers, swapped]
    unfold countObservations
    exact comm.2
  · decide
  · have isNone :
        (oneLocationPair.observe Policy.publishWave noAtoms).2.isNone = true := by
      decide
    cases result : (oneLocationPair.observe Policy.publishWave noAtoms).2 with
    | none => rfl
    | some _ => simp [result] at isNone

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder
