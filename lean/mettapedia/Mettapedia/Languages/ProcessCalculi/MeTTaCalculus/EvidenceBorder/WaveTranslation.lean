import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder.BranchLocalCount
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Policies
import Mettapedia.Logic.HostingStyles.Weighted.CountEvidence
import Mettapedia.Logic.HostingStyles.Weighted.Division
import Mettapedia.Logic.HostingStyles.Weighted.KernelPreservation

/-!
# One observation, once; counts through a translation

Two siblings that explored one observation and both publish it revise a count
twice. A wave counts each observation once when its proposals are independent
and its answers do not repeat an observation. The repeated publication is the
doubling in `revise_scale_ne_scale_revise`.

Counts read back through a weight-preserving map are the source counts. Through
a map that is hosting and not weight-preserving they are multiplied.
`KernelPreserving` is that hosting side: it holds of the listed read-back
exactly when the map is weight-preserving. The corrected count is a `Splits`
quotient.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Controls
open Mettapedia.Logic.EvidenceStateInsufficiency
open Mettapedia.Logic.HostingStyles.Weighted
open Mettapedia.GSLT.Dynamics.JoinAggregation

/-- The answers of a wave name each Boolean observation at most once. -/
def countsEachOnce (observations : List Bool) : Prop :=
  observations.Nodup

theorem countsEachOnce_distinct : countsEachOnce [true, false] := by
  unfold countsEachOnce
  decide

theorem not_countsEachOnce_repeat : ¬ countsEachOnce [true, true] := by
  unfold countsEachOnce
  decide

/-- A wave of evidence publications counts each observation once when the
proposals are independent and the answers do not repeat an observation. -/
def waveCountsOnce (outcomes : List (Bool × Proposal Unit Flag Bool)) : Prop :=
  (outcomes.map Prod.snd).Pairwise Proposal.Independent ∧
  countsEachOnce (outcomes.map Prod.fst)

theorem waveCountsOnce_pure : waveCountsOnce (purePair.branchLocal emptyFlag) := by
  unfold waveCountsOnce countsEachOnce
  decide

theorem not_waveCountsOnce_repeat :
    ¬ waveCountsOnce
      ((Region.alternatives [pureObservation true, pureObservation true]).branchLocal emptyFlag) := by
  unfold waveCountsOnce countsEachOnce
  decide

/-- Under that condition the positive count is the number of true answers, and
that number is at most one. The same holds for false. -/
theorem wave_counts_each_once (observations : List Bool) (once : countsEachOnce observations) :
    (countObservations observations).pos = observations.count true ∧
      observations.count true ≤ 1 ∧
      (countObservations observations).neg = observations.count false ∧
      observations.count false ≤ 1 := by
  refine ⟨countObservations_pos observations,
    (List.nodup_iff_count_le_one.mp once) true,
    countObservations_neg observations,
    (List.nodup_iff_count_le_one.mp once) false⟩

/-- **Negative.** Two siblings explored `true` and both publish it: the wave
policy returns two copies, and the count is two revisions of one observation. -/
theorem repeated_siblings_publish_twice :
    let region := Region.alternatives [pureObservation true, pureObservation true]
    (region.observe Policy.publishWave emptyFlag).1 = [true, true] ∧
      countObservations (observationBag region emptyFlag) = ⟨2, 0⟩ ∧
      ¬ waveCountsOnce (region.branchLocal emptyFlag) := by
  unfold waveCountsOnce countsEachOnce
  decide

/-- The two revisions equal `scaleCounts` of one revision, and scaling does not
commute with one further revision (`revise_scale_ne_scale_revise`). -/
theorem repeated_publication_matches_scale :
    countObservations [true, true] = scaleCounts (countObservations [true]) ∧
      (scaleCounts (countObservations [])).revise true ≠
        scaleCounts ((countObservations []).revise true) := by
  refine ⟨rfl, revise_scale_ne_scale_revise (countObservations [])⟩

/-- Counts read back as the two fibre sums of a Boolean translation. -/
def readBackCounts {Copy : Type} (key : Copy → Bool) (weight : Copy → ℕ)
    (copies : List Copy) : Counts where
  pos := groupSum key weight copies true
  neg := groupSum key weight copies false

theorem readBackCounts_one :
    readBackCounts (fun p : Bool × Fin 1 => p.1) (fun _ => (1 : ℕ)) (bothCopies 1) = ⟨1, 1⟩ := by
  have each (b : Bool) :
      groupSum (fun p : Bool × Fin 1 => p.1) (fun _ => (1 : ℕ)) (bothCopies 1) b = 1 := by
    rw [fibre_sum_mul]
    rfl
  simp [readBackCounts, each true, each false]

theorem readBackCounts_two_ne :
    readBackCounts (fun p : Bool × Fin 2 => p.1) (fun _ => (1 : ℕ)) (bothCopies 2) ≠ ⟨1, 1⟩ := by
  have each (b : Bool) :
      groupSum (fun p : Bool × Fin 2 => p.1) (fun _ => (1 : ℕ)) (bothCopies 2) b = 2 := by
    rw [fibre_sum_mul]
    rfl
  simp [readBackCounts, each true, each false]

/-- **Three cases.** A weight-preserving read-back is the source count. A
hosting map that is not weight-preserving multiplies it. `KernelPreserving` is
the hosting side of the same read-back. A `Splits` quotient restores the source
weight. -/
theorem evidence_read_back (w : ℚ) :
    (readBackCounts (fun p : Bool × Fin 1 => p.1) (fun _ => (1 : ℕ)) (bothCopies 1) = ⟨1, 1⟩ ∧
      weightPreserving (fun _ : Bool => (1 : ℕ)) (fun p : Bool × Fin 1 => p.1)
        (fun _ => (1 : ℕ)) (bothCopies 1)) ∧
    ((matchIdentity 2).Hosting ∧
      ¬ weightPreserving (fun _ : Bool => (1 : ℕ)) (matchEvent 2) (fun _ => (1 : ℕ))
          (matchFibre 2) ∧
      readBackCounts (matchEvent 2) (fun _ => (1 : ℕ)) (matchFibre 2) =
        scaleCounts ⟨1, 1⟩) ∧
    ((weightPreserving (fun _ : Bool => (1 : ℕ)) (fun p : Bool × Fin 1 => p.1)
        (fun _ => (1 : ℕ)) (bothCopies 1) ↔
      KernelPreserving (listedMap (fun _ : Bool => (1 : ℕ)) (fun p : Bool × Fin 1 => p.1)
        (fun _ => (1 : ℕ)) (bothCopies 1))) ∧
      ¬ KernelPreserving (listedMap (fun _ : Bool => (1 : ℕ)) (fun p : Bool × Fin 2 => p.1)
        (fun _ => (1 : ℕ)) (bothCopies 2))) ∧
    (∀ split : Splits ℚ 2 w,
      weightPreserving (fun _ : Bool => w) (fun p : Bool × Fin 2 => p.1)
        (fun _ => split.quotient) (bothCopies 2)) := by
  have hosted := hosting_fibre_multiplies_weight 2 (by decide)
  refine ⟨⟨readBackCounts_one, ?preserves⟩, ⟨hosted.1, hosted.2.2.2.2.2.2.2, ?multiplied⟩,
    ⟨?kernelSide, listed_two_not_preserving⟩, ?splits⟩
  · intro b
    rw [fibre_sum_mul]
    rfl
  · have multiplied := hosted.2.2.2.2.2.2.1
    have pos : groupSum (matchEvent 2) (fun _ => (1 : ℕ)) (matchFibre 2) true = 2 := by
      simpa using multiplied true
    have neg : groupSum (matchEvent 2) (fun _ => (1 : ℕ)) (matchFibre 2) false = 2 := by
      simpa using multiplied false
    simp [readBackCounts, scaleCounts, pos, neg]
  · exact listed_weightPreserving_iff (fun _ : Bool => (1 : ℕ))
      (fun p : Bool × Fin 1 => p.1) (fun _ => (1 : ℕ)) (bothCopies 1)
  · intro split
    exact splits_restore 2 w split

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder
