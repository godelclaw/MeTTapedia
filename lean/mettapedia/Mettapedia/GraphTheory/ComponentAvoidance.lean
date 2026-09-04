import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric

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

section Metric

variable [DecidableEq V]

/-- Transfer a walk into a graph with the same adjacency away from a
modification set, provided the walk starts in a component which avoids that
set.  The component-avoidance hypothesis rules out every possible changed
edge along the walk. -/
private noncomputable def transferWalkFromAvoidingComponent
    (modified : Set V) {root target : V}
    (havoid : ∀ vertex, vertex ∈ modified →
      ¬ G.Reachable root vertex)
    (hadj : ∀ {left right : V}, left ∉ modified →
      (G.Adj left right ↔ H.Adj left right))
    (walk : H.Walk root target) :
    G.Walk root target := by
  apply walk.transfer G
  intro edge hedge
  induction edge using Sym2.inductionOn with
  | _ left right =>
      have hleftSupport : left ∈ walk.support :=
        walk.fst_mem_support_of_mem_edges hedge
      have hleftReachableH : H.Reachable root left :=
        (walk.takeUntil left hleftSupport).reachable
      have hleftReachableG : G.Reachable root left :=
        (reachable_iff_of_adj_iff_off_set modified havoid hadj).2
          hleftReachableH
      have hleftOutside : left ∉ modified := by
        intro hleftModified
        exact havoid left hleftModified hleftReachableG
      apply G.mem_edgeSet.mpr
      apply (hadj hleftOutside).2
      exact H.mem_edgeSet.mp (walk.edges_subset_edgeSet hedge)

/-- Exact metric form of component avoidance.  If the whole component of
`root` misses the locus where two graphs may differ, then every distance from
`root` is unchanged.  Requiring the entire component, rather than one chosen
path, is essential: a modification elsewhere could otherwise create a
shorter route. -/
theorem dist_eq_of_adj_iff_off_set
    (modified : Set V) {root target : V}
    (havoid : ∀ vertex, vertex ∈ modified →
      ¬ G.Reachable root vertex)
    (hadj : ∀ {left right : V}, left ∉ modified →
      (G.Adj left right ↔ H.Adj left right)) :
    G.dist root target = H.dist root target := by
  by_cases hreach : G.Reachable root target
  · have hreachH : H.Reachable root target :=
      (reachable_iff_of_adj_iff_off_set modified havoid hadj).1 hreach
    obtain ⟨walkG, hlengthG⟩ := hreach.exists_walk_length_eq_dist
    obtain ⟨walkH, hlengthH⟩ := hreachH.exists_walk_length_eq_dist
    apply Nat.le_antisymm
    · calc
        G.dist root target ≤
            (transferWalkFromAvoidingComponent modified havoid hadj walkH).length :=
          SimpleGraph.dist_le _
        _ = walkH.length := Walk.length_transfer _ _
        _ = H.dist root target := hlengthH
    · let walkGtoH : H.Walk root target := by
          apply walkG.transfer H
          intro edge hedge
          induction edge using Sym2.inductionOn with
          | _ left right =>
              have hleftSupport : left ∈ walkG.support :=
                walkG.fst_mem_support_of_mem_edges hedge
              have hleftReachableG : G.Reachable root left :=
                (walkG.takeUntil left hleftSupport).reachable
              have hleftOutside : left ∉ modified := by
                intro hleftModified
                exact havoid left hleftModified hleftReachableG
              apply H.mem_edgeSet.mpr
              apply (hadj hleftOutside).1
              exact G.mem_edgeSet.mp (walkG.edges_subset_edgeSet hedge)
      calc
        H.dist root target ≤ walkGtoH.length := SimpleGraph.dist_le _
        _ = walkG.length := Walk.length_transfer _ _
        _ = G.dist root target := hlengthG
  · have hnotH : ¬ H.Reachable root target := by
      intro hreachH
      exact hreach
        ((reachable_iff_of_adj_iff_off_set modified havoid hadj).2 hreachH)
    have hGzero : G.dist root target = 0 :=
      SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.2 (Or.inr hreach)
    have hHzero : H.dist root target = 0 :=
      SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.2 (Or.inr hnotH)
    rw [hGzero, hHzero]

end Metric

end Mettapedia.GraphTheory
