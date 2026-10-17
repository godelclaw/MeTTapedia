import Mettapedia.Combinatorics.Matching.Noncrossing
import Mettapedia.ProbabilityTheory.FreeProbability.NoncrossingPartitions

/-!
# Noncrossing pairings are noncrossing partitions

An involution `f` of `Fin n` partitions the points into its orbits `{x, f x}`.  This
partition is noncrossing in the sense of `SetPartition.isNoncrossing` exactly when the
chords `{x, f x}` do not interleave, `NoncrossingMatching.IsNoncrossing f`
(`orbitPartition_isNoncrossing_iff`).  So the noncrossing perfect matchings counted by
`NoncrossingMatching.card_noncrossing_pairing` are the noncrossing partitions all of whose
blocks have two elements, the pairings indexing the moments of a free semicircular
element.
-/

namespace Mettapedia.ProbabilityTheory.FreeProbability

open NoncrossingMatching Function

variable {n : ℕ}

private theorem mem_foldl_union {l : List (Finset (Fin n))} {s : Finset (Fin n)} {x : Fin n} :
    x ∈ l.foldl (· ∪ ·) s ↔ x ∈ s ∨ ∃ B ∈ l, x ∈ B := by
  induction l generalizing s with
  | nil => simp
  | cons B l ih =>
      rw [List.foldl_cons, ih, Finset.mem_union]
      simp only [List.mem_cons, exists_eq_or_imp]
      tauto

/-- The partition of `Fin n` into the orbits `{x, f x}` of an involution, each listed once
from its least point. -/
def orbitPartition (f : Fin n → Fin n) (hf : Involutive f) : SetPartition n where
  blocks := ((List.finRange n).filter fun x => x ≤ f x).map fun x => {x, f x}
  blocks_nonempty := by
    intro B hB
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hB
    exact ⟨x, Finset.mem_insert_self _ _⟩
  blocks_disjoint := by
    rw [List.pairwise_map]
    refine ((List.pairwise_lt_finRange n).filter _).imp_of_mem ?_
    intro x y hx hy hxy
    have hxf : x ≤ f x := of_decide_eq_true (List.mem_filter.mp hx).2
    have hyf : y ≤ f y := of_decide_eq_true (List.mem_filter.mp hy).2
    rw [Finset.disjoint_left]
    intro z hzx hzy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzx hzy
    rcases hzx with h₁ | h₁ <;> rcases hzy with h₂ | h₂
    · exact hxy.ne (h₁.symm.trans h₂)
    · -- `x = f y` would give `y ≤ f y = x < y`
      exact lt_irrefl _ (lt_of_le_of_lt (hyf.trans_eq (h₂.symm.trans h₁)) hxy)
    · -- `f x = y` would give `f y = x`, so `y ≤ x < y`
      have hfy : f y = x := by rw [← h₂, h₁, hf x]
      exact lt_irrefl _ (lt_of_le_of_lt (hyf.trans_eq hfy) hxy)
    · exact hxy.ne (hf.injective (h₁.symm.trans h₂))
  blocks_cover := by
    ext x
    simp only [Finset.mem_univ, iff_true, mem_foldl_union, Finset.notMem_empty, false_or,
      List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    rcases le_total x (f x) with hx | hx
    · exact ⟨_, ⟨x, hx, rfl⟩, Finset.mem_insert_self _ _⟩
    · exact ⟨_, ⟨f x, by rwa [hf x], rfl⟩,
        Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (hf x).symm)⟩

/-- **The orbit partition of an involution is noncrossing exactly when its chords do not
interleave.** -/
theorem orbitPartition_isNoncrossing_iff {f : Fin n → Fin n} (hf : Involutive f) :
    (orbitPartition f hf).isNoncrossing ↔ IsNoncrossing f := by
  have hmemB : ∀ B ∈ (orbitPartition f hf).blocks, ∃ x, x ≤ f x ∧ B = {x, f x} := by
    intro B hB
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hB
    exact ⟨x, of_decide_eq_true (List.mem_filter.mp hx).2, rfl⟩
  -- two distinct points of one orbit block are partners
  have hpartner : ∀ x, x ≤ f x → ∀ a c, a ∈ ({x, f x} : Finset (Fin n)) →
      c ∈ ({x, f x} : Finset (Fin n)) → a < c → c = f a := by
    intro x hx a c ha hc hac
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc
    · exact absurd (ha.trans hc.symm) hac.ne
    · rw [hc, ha]
    · rw [hc, ha, hf x]
    · exact absurd (ha.trans hc.symm) hac.ne
  constructor
  · intro hnc a b hab hbfa hfafb
    apply hnc
    have hBa : ({a, f a} : Finset (Fin n)) ∈ (orbitPartition f hf).blocks :=
      List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_finRange a,
        decide_eq_true (hab.trans hbfa).le⟩, rfl⟩
    have hBb : ({b, f b} : Finset (Fin n)) ∈ (orbitPartition f hf).blocks :=
      List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_finRange b,
        decide_eq_true (hbfa.trans hfafb).le⟩, rfl⟩
    refine ⟨_, hBa, _, hBb, ?_, a, f a, Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _), b, f b,
      Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
      hab, hbfa, hfafb⟩
    intro heq
    have ha : a ∈ ({b, f b} : Finset (Fin n)) := heq ▸ Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with h | h
    · exact hab.ne h
    · exact lt_irrefl a (lt_of_lt_of_eq (hab.trans (hbfa.trans hfafb)) h.symm)
  · rintro hnc ⟨B₁, hB₁, B₂, hB₂, -, a, c, ha, hc, b, d, hb, hd, hab, hbc, hcd⟩
    obtain ⟨x, hx, rfl⟩ := hmemB B₁ hB₁
    obtain ⟨y, hy, rfl⟩ := hmemB B₂ hB₂
    have hca : c = f a := hpartner x hx a c ha hc (hab.trans hbc)
    have hdb : d = f b := hpartner y hy b d hb hd (hbc.trans hcd)
    subst hca hdb
    exact hnc a b hab hbc hcd

end Mettapedia.ProbabilityTheory.FreeProbability
