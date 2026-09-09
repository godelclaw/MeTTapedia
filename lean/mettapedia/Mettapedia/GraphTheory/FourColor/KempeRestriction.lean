import Mettapedia.GraphTheory.FourColor.KempeEmbeddingFusion

/-!
# Kempe reachability restricts along graph embeddings

An ambient component can meet several components of an induced subgraph.
Its switch therefore need not restrict to a single switch. It does restrict
to a finite valid-pair Kempe sequence when the smaller graph is finite.
Consequently restriction cannot split an ambient Kempe orbit between two
smaller orbits. The reverse lifting assertion is not made.
-/

namespace Mettapedia.GraphTheory.FourColor.KempeRestriction

open SimpleGraph GoertzelV24LocalSwapKempeGeneration
open GoertzelV24KempeComponentEmbeddingBoundary

universe u v
variable {A : Type u} {B : Type v} {G : SimpleGraph A} {H : SimpleGraph B}

/-- A component switch is one local transposition at every touched vertex,
and the identity at every untouched vertex. -/
theorem locallySwapRelated_switch (c : H.EdgeColoring Color)
    (a b : Color) (K : (c.bicoloredSubgraph a b).ConnectedComponent) :
    LocallySwapRelated c (c.swapOnKempeComponent a b K) := by
  classical
  intro v
  by_cases ht : ∃ e : H.edgeSet, v ∈ (e.val : Sym2 B) ∧
      e ∈ c.kempeComponentSet a b K
  · obtain ⟨e, hev, heK⟩ := ht
    refine ⟨a, b, ?_⟩
    intro f hfv
    by_cases hf : f ∈ c.bicoloredSet a b
    · have hfK : f ∈ c.kempeComponentSet a b K := by
        by_cases hfe : f = e
        · simpa [hfe] using heK
        · exact c.mem_kempeComponentSet_of_adj heK
            (H.lineGraph_adj_of_edgeSet_common_vertex (Ne.symm hfe) hev hfv) hf
      exact c.swapOnKempeComponent_apply_of_mem hfK
    · rw [c.swapOnKempeComponent_apply_of_not_mem
          (fun h => hf (c.mem_bicoloredSet_of_mem_kempeComponentSet h))]
      symm
      exact Equiv.swap_apply_of_ne_of_ne (fun h => hf (Or.inl h))
        (fun h => hf (Or.inr h))
  · refine ⟨0, 0, ?_⟩
    intro e hev
    rw [c.swapOnKempeComponent_apply_of_not_mem (fun he => ht ⟨e, hev, he⟩)]
    simp

/-- Restriction preserves a local transposition relation. -/
theorem locallySwapRelated_pullback (embedding : G ↪g H)
    {c d : H.EdgeColoring Color} (h : LocallySwapRelated c d) :
    LocallySwapRelated (c.pullbackEmbedding embedding) (d.pullbackEmbedding embedding) := by
  intro v
  obtain ⟨a, b, hv⟩ := h (embedding v)
  refine ⟨a, b, ?_⟩
  intro e hev
  apply hv
  exact Sym2.mem_map.mpr ⟨v, hev, rfl⟩

variable [Fintype A] [DecidableEq A] [DecidableRel G.Adj]

/-- One ambient valid-pair switch restricts to a sequence, not necessarily
one component switch, in the finite smaller graph. -/
theorem reachable_pullback_of_step (embedding : G ↪g H)
    {c d : H.EdgeColoring Color} (hc : IsTaitEdgeColoring H c)
    (h : TaitKempeStep c d) :
    TaitKempeReachable (c.pullbackEmbedding embedding) (d.pullbackEmbedding embedding) := by
  have hd := isTaitEdgeColoring_of_taitKempeStep hc h
  apply taitKempeReachable_of_locallySwapRelated _ _
    (isTaitEdgeColoring_pullbackEmbedding c embedding hc)
    (isTaitEdgeColoring_pullbackEmbedding d embedding hd)
  obtain ⟨a, b, _, K, rfl⟩ := h
  exact locallySwapRelated_pullback embedding (locallySwapRelated_switch c a b K)

/-- An ambient Kempe orbit has its entire restriction in a single smaller
Kempe orbit. No assumption excluding component fusion is required. -/
theorem reachable_pullback (embedding : G ↪g H)
    {c d : H.EdgeColoring Color} (hc : IsTaitEdgeColoring H c)
    (h : TaitKempeReachable c d) :
    TaitKempeReachable (c.pullbackEmbedding embedding) (d.pullbackEmbedding embedding) := by
  induction h with
  | refl => exact .refl
  | tail path step ih =>
      exact ih.trans (reachable_pullback_of_step embedding
        (isTaitEdgeColoring_of_taitKempeReachable hc path) step)

end Mettapedia.GraphTheory.FourColor.KempeRestriction
