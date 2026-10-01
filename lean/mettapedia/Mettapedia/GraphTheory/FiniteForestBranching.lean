import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# A finite forest cannot support a network without leaves

If every edge at a vertex has a distinct second neighbour, the graph has no
leaf. A longest path shows that a finite acyclic graph with this property
has no edges. This is useful for eliminating nonzero conservative support
without imposing a fixed bound on the number of vertices.
-/

namespace Mettapedia.GraphTheory.FiniteForestBranching

variable {V : Type*} [Finite V] (G : SimpleGraph V)

theorem eq_bot (hforest : G.IsAcyclic)
    (hbranch : ∀ {u v}, G.Adj u v → ∃ w, G.Adj u w ∧ w ≠ v) : G = ⊥ := by
  classical
  apply SimpleGraph.ext
  funext a b
  apply propext
  simp only [SimpleGraph.bot_adj, iff_false]
  intro hab
  let : Nonempty V := ⟨a⟩
  obtain ⟨u,v,p,hp,hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hpos : 0 < p.length := by
    have h := hmax a b (.cons hab .nil) (by simp [hab.ne])
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h
    omega
  have hn : ¬p.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpos
  obtain ⟨w,hw,hne⟩ := hbranch (p.adj_snd hn)
  have hmem : w ∈ p.support := by
    by_contra hnot
    have h := hmax w v (p.cons hw.symm) (hp.cons hnot)
    simp only [SimpleGraph.Walk.length_cons] at h
    omega
  exact hne (hforest.eq_snd_of_adj_start hp hw hmem)

end Mettapedia.GraphTheory.FiniteForestBranching
