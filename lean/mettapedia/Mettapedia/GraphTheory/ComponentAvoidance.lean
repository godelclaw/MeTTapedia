import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connected components away from a modification locus

Two graphs may differ arbitrarily on a displayed vertex set.  If their
adjacency relations agree whenever the first endpoint is outside that set,
then every component of the first graph which avoids the set is unchanged in
the second graph.  The hypothesis is oriented only for convenience: simple
graph adjacency is symmetric.
-/

namespace Mettapedia.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G H : SimpleGraph V}

/-- Reachability from a component avoiding a modification set is invariant
when the two adjacency relations agree off that set. -/
theorem reachable_iff_of_adj_iff_off_set
    (modified : Set V) {root target : V}
    (havoid : ∀ vertex, vertex ∈ modified →
      ¬ G.Reachable root vertex)
    (hadj : ∀ {left right : V}, left ∉ modified →
      (G.Adj left right ↔ H.Adj left right)) :
    G.Reachable root target ↔ H.Reachable root target := by
  rw [SimpleGraph.reachable_iff_reflTransGen,
    SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro path
    induction path with
    | refl => exact Relation.ReflTransGen.refl
    | @tail middle right hprefix edge inductionHypothesis =>
        have hmiddle : middle ∉ modified := by
          intro hmem
          exact havoid middle hmem
            ((SimpleGraph.reachable_iff_reflTransGen _ _).2 hprefix)
        exact Relation.ReflTransGen.tail inductionHypothesis
          ((hadj hmiddle).1 edge)
  · intro path
    induction path with
    | refl => exact Relation.ReflTransGen.refl
    | @tail middle right hprefix edge inductionHypothesis =>
        have hmiddle : middle ∉ modified := by
          intro hmem
          exact havoid middle hmem
            ((SimpleGraph.reachable_iff_reflTransGen _ _).2
              inductionHypothesis)
        exact Relation.ReflTransGen.tail inductionHypothesis
          ((hadj hmiddle).2 edge)

/-- Set-level form: the connected component of an avoiding root has exactly
the same support before and after the modification. -/
theorem connectedComponentMk_supp_eq_of_adj_iff_off_set
    (modified : Set V) (root : V)
    (havoid : ∀ vertex, vertex ∈ modified →
      ¬ G.Reachable root vertex)
    (hadj : ∀ {left right : V}, left ∉ modified →
      (G.Adj left right ↔ H.Adj left right)) :
    (G.connectedComponentMk root).supp =
      (H.connectedComponentMk root).supp := by
  ext vertex
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq]
  simpa only [SimpleGraph.reachable_comm] using
    reachable_iff_of_adj_iff_off_set modified havoid hadj
      (root := root) (target := vertex)

end Mettapedia.GraphTheory
