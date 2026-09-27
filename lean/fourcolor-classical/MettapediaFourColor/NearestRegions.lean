import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Regions nearest to compact sets

For a family of compact sets, assign a point to a set when its distance to
that set is strictly smaller than its distance to every other member. The
resulting regions are pairwise disjoint and, for a finite family, open.

If the part of a compact set belonging to no other member is connected,
then its nearest region is connected. Indeed, a segment from any point of
the region to a closest point of the compact set stays inside the region
and ends in that exclusive part.

These statements do not assume convexity of the compact sets or impose a
dimension bound on the real normed space.
-/

namespace Mettapedia.Topology.NearestRegions

open Set Metric

variable {ι E : Type*}

section Metric

variable [MetricSpace E]

/-- Points of one member that belong to no other member. -/
def core (K : ι → Set E) (i : ι) : Set E :=
  {x | x ∈ K i ∧ ∀ j, j ≠ i → x ∉ K j}

/-- The region strictly closer to one member than to every other member. -/
def region (K : ι → Set E) (i : ι) : Set E :=
  {x | ∀ j, j ≠ i → infDist x (K i) < infDist x (K j)}

theorem disjoint_region (K : ι → Set E) {i j : ι} (hij : i ≠ j) :
    Disjoint (region K i) (region K j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact (hxi j hij.symm).not_gt (hxj i hij)

theorem core_subset_region (K : ι → Set E)
    (hclosed : ∀ j, IsClosed (K j)) (hne : ∀ j, (K j).Nonempty) (i : ι) :
    core K i ⊆ region K i := by
  intro x hx j hji
  rw [infDist_zero_of_mem hx.1]
  exact ((hclosed j).notMem_iff_infDist_pos (hne j)).mp (hx.2 j hji)

theorem isOpen_region [Finite ι] (K : ι → Set E) (i : ι) :
    IsOpen (region K i) := by
  simp only [region, ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
    isOpen_lt (continuous_infDist_pt (K i)) (continuous_infDist_pt (K j))

end Metric

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Moving towards a closest point preserves every strict distance comparison. -/
theorem segment_subset_region (K : ι → Set E) {i : ι} {x q : E}
    (hx : x ∈ region K i) (hq : q ∈ K i)
    (hclosest : infDist x (K i) = dist x q) :
    segment ℝ x q ⊆ region K i := by
  intro z hz j hji
  have hstrict := hx j hji
  rw [hclosest] at hstrict
  have hupper : infDist z (K i) ≤ dist z q := infDist_le_dist_of_mem hq
  have hlower : infDist x (K j) ≤ infDist z (K j) + dist x z :=
    infDist_le_infDist_add_dist
  have hadd := dist_add_dist_of_mem_segment hz
  linarith

/-- A closest point of the winning compact set lies in its exclusive core. -/
theorem exists_core_segment (K : ι → Set E) {i : ι}
    (hc : IsCompact (K i)) (hne : (K i).Nonempty) {x : E}
    (hx : x ∈ region K i) :
    ∃ q ∈ core K i, segment ℝ x q ⊆ region K i := by
  obtain ⟨q, hq, hclosest⟩ := hc.exists_infDist_eq_dist hne x
  refine ⟨q, ⟨hq, ?_⟩, segment_subset_region K hx hq hclosest⟩
  intro j hji hqj
  have hupper : infDist x (K j) ≤ dist x q := infDist_le_dist_of_mem hqj
  have hstrict := hx j hji
  rw [hclosest] at hstrict
  exact hstrict.not_ge hupper

/-- A connected exclusive core makes the entire strict nearest region connected. -/
theorem isConnected_region (K : ι → Set E)
    (hc : ∀ j, IsCompact (K j)) (hne : ∀ j, (K j).Nonempty)
    (i : ι) (hcore : IsConnected (core K i)) : IsConnected (region K i) := by
  have hsub := core_subset_region K (fun j => (hc j).isClosed) hne i
  obtain ⟨p, hp⟩ := hcore.nonempty
  refine ⟨⟨p, hsub hp⟩, isPreconnected_of_forall p ?_⟩
  intro x hx
  obtain ⟨q, hq, hseg⟩ := exists_core_segment K (hc i) (hne i) hx
  refine ⟨core K i ∪ segment ℝ x q, union_subset hsub hseg,
    Or.inl hp, Or.inr (left_mem_segment ℝ x q), ?_⟩
  exact hcore.isPreconnected.union q hq (right_mem_segment ℝ x q)
    (convex_segment x q).isPreconnected

end Normed

section Metric

variable [MetricSpace E]

/-- Density of the exclusive core makes every site point a limit of its region. -/
theorem subset_closure_region (K : ι → Set E)
    (hclosed : ∀ j, IsClosed (K j)) (hne : ∀ j, (K j).Nonempty)
    (i : ι) (hdense : K i ⊆ closure (core K i)) :
    K i ⊆ closure (region K i) :=
  hdense.trans (closure_mono (core_subset_region K hclosed hne i))

/-- A point of one site cannot be a limit of another region unless it also
belongs to that other site. This will exclude spurious triple contacts. -/
theorem notMem_closure_region (K : ι → Set E)
    (hclosed : ∀ j, IsClosed (K j)) (hne : ∀ j, (K j).Nonempty)
    {i j : ι} {z : E} (hzi : z ∈ K i) (hzj : z ∉ K j) :
    z ∉ closure (region K j) := by
  have hij : i ≠ j := fun h => hzj (h ▸ hzi)
  have hsub : region K j ⊆ {x | infDist x (K j) ≤ infDist x (K i)} :=
    fun _ hx => (hx i hij).le
  have hclosed' : IsClosed {x | infDist x (K j) ≤ infDist x (K i)} :=
    isClosed_le (continuous_infDist_pt (K j)) (continuous_infDist_pt (K i))
  intro hz
  have hle := (closure_minimal hsub hclosed') hz
  have hpos := ((hclosed j).notMem_iff_infDist_pos (hne j)).mp hzj
  rw [mem_ofPred_eq, infDist_zero_of_mem hzi] at hle
  exact hpos.not_ge hle

end Metric

end Mettapedia.Topology.NearestRegions
