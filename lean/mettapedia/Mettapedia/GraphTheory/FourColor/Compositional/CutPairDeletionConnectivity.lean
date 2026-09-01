import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mettapedia.GraphTheory.FourColor.CyclicEdgeCut

/-!
# Connectivity after deleting two crossing edges

This file isolates a graph-theoretic fact used by small-cut boundary-order
arguments.  If a vertex shore and its complement are both connected, then an
undeleted third crossing edge still joins them after two other crossing edges
are removed.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CutPairDeletionConnectivity

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Connected shores joined by a third crossing edge remain connected after
two different crossing edges are deleted.  The theorem is independent of
planarity and of the cardinality or provenance of the ambient cut. -/
theorem deleteEdges_pair_connected_of_connected_shores
    (side : V → Prop)
    (hsideConnected : (G.induce side).Connected)
    (hcomplementConnected :
      (G.induce (fun vertex ↦ ¬ side vertex)).Connected)
    (first second third : G.edgeSet)
    (hfirstCross : EdgeCrossesVertexSide G side first)
    (hsecondCross : EdgeCrossesVertexSide G side second)
    (hthirdCross : EdgeCrossesVertexSide G side third)
    (hthirdFirst : third ≠ first) (hthirdSecond : third ≠ second) :
    (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).Connected := by
  classical
  let removed : Set (Sym2 V) := {first.1, second.1}
  rcases hthirdCross with
    ⟨inner, outer, hinnerEdge, houterEdge, hinnerSide, houterSide⟩
  have hinnerOuterNe : inner ≠ outer := by
    intro heq
    exact houterSide (heq ▸ hinnerSide)
  have hthirdPair : (third.1 : Sym2 V) = s(inner, outer) :=
    sym2_eq_mk_of_mem_of_mem_of_ne
      hinnerEdge houterEdge hinnerOuterNe
  have hinnerOuterAdj : G.Adj inner outer := by
    apply (SimpleGraph.mem_edgeSet G).1
    rw [← hthirdPair]
    exact third.2
  have hsideEdgeAvoids : ∀ {left right : V},
      side left → side right → G.Adj left right →
        s(left, right) ∉ removed := by
    intro left right hleft hright hadj hmem
    rcases hmem with hfirst | hsecond
    · have hopposite :=
        not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
          hfirst.symm hfirstCross
      exact hopposite ⟨fun _ ↦ hright, fun _ ↦ hleft⟩
    · have hopposite :=
        not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
          hsecond.symm hsecondCross
      exact hopposite ⟨fun _ ↦ hright, fun _ ↦ hleft⟩
  have hcomplementEdgeAvoids : ∀ {left right : V},
      ¬ side left → ¬ side right → G.Adj left right →
        s(left, right) ∉ removed := by
    intro left right hleft hright hadj hmem
    rcases hmem with hfirst | hsecond
    · have hopposite :=
        not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
          hfirst.symm hfirstCross
      exact hopposite
        ⟨fun hleftSide ↦ (hleft hleftSide).elim,
          fun hrightSide ↦ (hright hrightSide).elim⟩
    · have hopposite :=
        not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
          hsecond.symm hsecondCross
      exact hopposite
        ⟨fun hleftSide ↦ (hleft hleftSide).elim,
          fun hrightSide ↦ (hright hrightSide).elim⟩
  let sideHom : G.induce side →g G.deleteEdges removed :=
    { toFun := Subtype.val
      map_rel' := by
        intro left right hadj
        apply SimpleGraph.deleteEdges_adj.mpr
        exact ⟨hadj,
          hsideEdgeAvoids left.2 right.2 hadj⟩ }
  let complementHom :
      G.induce (fun vertex ↦ ¬ side vertex) →g
        G.deleteEdges removed :=
    { toFun := Subtype.val
      map_rel' := by
        intro left right hadj
        apply SimpleGraph.deleteEdges_adj.mpr
        exact ⟨hadj,
          hcomplementEdgeAvoids left.2 right.2 hadj⟩ }
  have hsideReach : ∀ {left right : V},
      side left → side right →
        (G.deleteEdges removed).Reachable left right := by
    intro left right hleft hright
    simpa [sideHom] using
      (hsideConnected ⟨left, hleft⟩ ⟨right, hright⟩).map sideHom
  have hcomplementReach : ∀ {left right : V},
      ¬ side left → ¬ side right →
        (G.deleteEdges removed).Reachable left right := by
    intro left right hleft hright
    simpa [complementHom] using
      (hcomplementConnected ⟨left, hleft⟩
        ⟨right, hright⟩).map complementHom
  have hthirdAvoids : s(inner, outer) ∉ removed := by
    intro hmem
    rcases hmem with hfirst | hsecond
    · apply hthirdFirst
      apply Subtype.ext
      exact hthirdPair.trans hfirst
    · apply hthirdSecond
      apply Subtype.ext
      exact hthirdPair.trans hsecond
  have hcrossing : (G.deleteEdges removed).Adj inner outer :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hinnerOuterAdj, hthirdAvoids⟩
  letI : Nonempty V := ⟨inner⟩
  have hdeletedConnected : (G.deleteEdges removed).Connected := by
    refine ⟨?_⟩
    intro left right
    by_cases hleft : side left <;>
      by_cases hright : side right
    · exact hsideReach hleft hright
    · exact (hsideReach hleft hinnerSide).trans
        (hcrossing.reachable.trans
          (hcomplementReach houterSide hright))
    · exact (hcomplementReach hleft houterSide).trans
        (hcrossing.symm.reachable.trans
          (hsideReach hinnerSide hright))
    · exact hcomplementReach hleft hright
  simpa [removed] using hdeletedConnected

end CutPairDeletionConnectivity

end Mettapedia.GraphTheory.FourColor.Compositional
