import Mettapedia.Combinatorics.Matching.Noncrossing
import Mettapedia.ProbabilityTheory.FreeProbability.NoncrossingPartitions

/-!
# Noncrossing pairings are noncrossing partitions

An involution `f` of `Fin n` partitions the points into its orbits `{x, f x}`: two points
share a block when their orbits have the same least point.  This partition is noncrossing
in the sense of `Partition.isNoncrossing` exactly when the chords `{x, f x}` do not
interleave, `NoncrossingMatching.IsNoncrossing f` (`orbitPartition_isNoncrossing_iff`).  So
the noncrossing perfect matchings counted by `NoncrossingMatching.card_noncrossing_pairing`
are the noncrossing partitions all of whose blocks have two elements, the pairings
indexing the moments of a free semicircular element.
-/

namespace Mettapedia.ProbabilityTheory.FreeProbability

open NoncrossingMatching Function Finset

variable {n : ℕ}

/-- The partition of `Fin n` into the orbits `{x, f x}` of an involution: points whose
orbits have the same least point share a block. -/
def orbitPartition (f : Fin n → Fin n) : Partition n :=
  partitionOfLabels fun x => min x (f x)

theorem orbitPartition_part_eq_iff (f : Fin n → Fin n) (a c : Fin n) :
    (orbitPartition f).part a = (orbitPartition f).part c ↔ min a (f a) = min c (f c) := by
  rw [← (orbitPartition f).mem_part_iff_part_eq_part (mem_univ a) (mem_univ c), orbitPartition,
    mem_part_labels, eq_comm]

/-- Two points of one orbit, the smaller first, are partners. -/
private theorem partner_of_least_eq {f : Fin n → Fin n} (hf : Involutive f) {a c : Fin n}
    (hac : a < c) (h : min a (f a) = min c (f c)) : c = f a := by
  rcases le_total a (f a) with ha | ha <;> rcases le_total c (f c) with hc | hc
  · rw [min_eq_left ha, min_eq_left hc] at h
    exact absurd h hac.ne
  · rw [min_eq_left ha, min_eq_right hc] at h
    rw [h, hf c]
  · rw [min_eq_right ha, min_eq_left hc] at h
    rw [h] at ha
    exact absurd (ha.trans_lt hac) (lt_irrefl c)
  · rw [min_eq_right ha, min_eq_right hc] at h
    exact absurd (hf.injective h) hac.ne

/-- **The orbit partition of an involution is noncrossing exactly when its chords do not
interleave.** -/
theorem orbitPartition_isNoncrossing_iff {f : Fin n → Fin n} (hf : Involutive f) :
    (orbitPartition f).isNoncrossing ↔ IsNoncrossing f := by
  have least : ∀ {x}, x < f x → min x (f x) = x ∧ min (f x) (f (f x)) = x := fun hx =>
    ⟨min_eq_left hx.le, by rw [hf, min_eq_right hx.le]⟩
  constructor
  · intro hnc a b hab hbfa hfafb
    have hafa : a < f a := hab.trans hbfa
    have hbfb : b < f b := hbfa.trans hfafb
    have key := hnc a b (f a) (f b) hab hbfa hfafb
      ((orbitPartition_part_eq_iff f a (f a)).mpr (by rw [(least hafa).1, (least hafa).2]))
      ((orbitPartition_part_eq_iff f b (f b)).mpr (by rw [(least hbfb).1, (least hbfb).2]))
    rw [orbitPartition_part_eq_iff, (least hafa).1, (least hbfb).1] at key
    exact hab.ne key
  · intro hnc a b c d hab hbc hcd hac hbd
    rw [orbitPartition_part_eq_iff] at hac hbd
    have hca := partner_of_least_eq hf (hab.trans hbc) hac
    have hdb := partner_of_least_eq hf (hbc.trans hcd) hbd
    subst hca hdb
    exact (hnc a b hab hbc hcd).elim

end Mettapedia.ProbabilityTheory.FreeProbability
