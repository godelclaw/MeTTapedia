import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-!
# Nested fundamental shores along a tree path

For path edge i, take the start component after deleting that edge.
Path positions at most i are inside and all later positions are outside.
The resulting shores are strictly nested; their sizes include the entire
path prefix and suffix, not just the two endpoints of the removed edge.
-/

namespace Mettapedia.GraphTheory.FourColor.TreePathShore

open SimpleGraph

variable {V : Type*} {H : SimpleGraph V} {a b : V}

noncomputable section

def pathEdge (p : H.Walk a b) (i : ℕ) : Sym2 V :=
  s(p.getVert i, p.getVert (i + 1))

def shore (p : H.Walk a b) (i : ℕ) : Set V :=
  {v | (H.deleteEdges {pathEdge p i}).Reachable a v}

theorem reachable_prefix (p : H.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hi : i < p.length) (hj : j ≤ i) :
    p.getVert j ∈ shore p i := by
  apply SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
  refine ⟨p.take j, ?_⟩
  intro he
  have hm := (p.take j).snd_mem_support_of_mem_edges he
  obtain ⟨q, hq, hlen⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hm
  rw [SimpleGraph.Walk.take_getVert] at hq
  have heq := hp.getVert_injOn
    (show min j q ≤ p.length by omega) (show i + 1 ≤ p.length by omega) hq
  omega

theorem reachable_suffix (p : H.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hi : i < j) (hj : j ≤ p.length) :
    (H.deleteEdges {pathEdge p i}).Reachable (p.getVert j) b := by
  apply SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
  refine ⟨p.drop j, ?_⟩
  intro he
  have hm := (p.drop j).fst_mem_support_of_mem_edges he
  obtain ⟨q, hq, hlen⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hm
  rw [SimpleGraph.Walk.drop_getVert] at hq
  rw [SimpleGraph.Walk.drop_length] at hlen
  have heq := hp.getVert_injOn
    (show j + q ≤ p.length by omega) (show i ≤ p.length by omega) hq
  omega

theorem shore_eq_endpoint_region (p : H.Walk a b) (hp : p.IsPath)
    {i : ℕ} (hi : i < p.length) :
    shore p i = {v | (H.deleteEdges {pathEdge p i}).Reachable (p.getVert i) v} := by
  ext v
  have h := reachable_prefix p hp hi le_rfl
  exact ⟨fun hv => h.symm.trans hv, fun hv => h.trans hv⟩

theorem end_not_mem (htree : H.IsTree) (p : H.Walk a b) (hp : p.IsPath)
    {i : ℕ} (hi : i < p.length) : b ∉ shore p i := by
  have hb : H.IsBridge (pathEdge p i) :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp htree.isAcyclic
      (p.adj_getVert_succ hi)
  have hsep := SimpleGraph.isBridge_iff.mp hb
  intro h
  exact hsep ((reachable_prefix p hp hi le_rfl).symm.trans
    (h.trans (reachable_suffix p hp (by omega) (by omega)).symm))

theorem getVert_mem_iff (htree : H.IsTree) (p : H.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hi : i < p.length) (hj : j ≤ p.length) :
    p.getVert j ∈ shore p i ↔ j ≤ i := by
  refine ⟨?_, reachable_prefix p hp hi⟩
  intro h
  by_contra hn
  exact end_not_mem htree p hp hi (h.trans (reachable_suffix p hp (by omega) hj))

/-- A later removed edge lies entirely outside the earlier start component. -/
theorem shore_mono (htree : H.IsTree) (p : H.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hij : i ≤ j) (hj : j < p.length) : shore p i ⊆ shore p j := by
  classical
  rcases hij.eq_or_lt with rfl | hij
  · exact Set.Subset.rfl
  intro v hv
  obtain ⟨q⟩ := hv
  apply SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
  refine ⟨q.map (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _)), ?_⟩
  intro he
  have he' : pathEdge p j ∈ q.edges := by
    change pathEdge p j ∈ (q.map (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _))).edges at he
    rw [SimpleGraph.Walk.edges_map] at he
    simpa only [SimpleGraph.Hom.coe_ofLE,
      Sym2.map_id, List.map_id_fun, id_eq] using he
  have hmem := q.fst_mem_support_of_mem_edges he'
  have hreach : p.getVert j ∈ shore p i := ⟨q.takeUntil _ hmem⟩
  have := (getVert_mem_iff htree p hp (by omega) (by omega)).mp hreach
  omega

theorem shore_ssubset (htree : H.IsTree) (p : H.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hij : i < j) (hj : j < p.length) : shore p i ⊂ shore p j := by
  refine ⟨shore_mono htree p hp hij.le hj, ?_⟩
  intro h
  have hm := h (reachable_prefix p hp hj le_rfl)
  have := (getVert_mem_iff htree p hp (by omega) (by omega)).mp hm
  omega

theorem prefix_card_le [Fintype V] (p : H.Walk a b) (hp : p.IsPath)
    {i : ℕ} (hi : i < p.length) : i + 1 ≤ Nat.card (shore p i) := by
  classical
  let f : Fin (i + 1) → shore p i := fun j =>
    ⟨p.getVert j.val, reachable_prefix p hp hi (by omega)⟩
  have hf : Function.Injective f := by
    intro j k h
    apply Fin.ext
    exact hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) (congrArg Subtype.val h)
  simpa using Nat.card_le_card_of_injective f hf

theorem suffix_card_le [Fintype V] (htree : H.IsTree)
    (p : H.Walk a b) (hp : p.IsPath) {i : ℕ} (hi : i < p.length) :
    p.length - i ≤ Nat.card ↥((shore p i)ᶜ) := by
  classical
  let f : Fin (p.length - i) → ↥((shore p i)ᶜ) := fun j =>
    ⟨p.getVert (i + 1 + j.val), by
      change p.getVert (i + 1 + j.val) ∉ shore p i
      rw [getVert_mem_iff htree p hp hi (by omega)]
      omega⟩
  have hf : Function.Injective f := by
    intro j k h
    have heq := hp.getVert_injOn
      (show i + 1 + j.val ≤ p.length by omega)
      (show i + 1 + k.val ≤ p.length by omega) (congrArg Subtype.val h)
    exact Fin.ext (by omega)
  simpa using Nat.card_le_card_of_injective f hf

end
end Mettapedia.GraphTheory.FourColor.TreePathShore
