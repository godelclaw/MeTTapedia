import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationEdgeBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCut

/-!
# Singleton rotation boundaries are bridges

This is the generic cut lemma behind several normalization and descent
arguments.  If a finite vertex side has exactly one boundary edge, deleting
that edge prevents every path from leaving the side.  Consequently a
bridge-free rotation system has no singleton vertex-side boundary.

The statement is deliberately independent of digons or any particular cut
normal form.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationBoundaryBridge

open GoertzelV24RotationEdgeBridge

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Adjacency avoiding the removed edge never leaves a vertex set whose only
boundary edge is that removed edge. -/
theorem mem_of_adj_edgeDeleted (RS : RotationSystem V E)
    (side : Finset V) (removed : E)
    (hboundary : RS.vertexSideEdgeBoundary side = {removed})
    {left right : V} (hleft : left ∈ side)
    (hadj : (edgeDeletedPrimalGraph RS removed).Adj left right) :
    right ∈ side := by
  classical
  obtain ⟨dart, hne, hvertLeft, hvertRight⟩ := hadj
  by_contra hright
  apply hne
  have hedge : RS.edgeOf dart ∈ RS.vertexSideEdgeBoundary side := by
    rw [RS.mem_vertexSideEdgeBoundary_iff]
    have hdart : dart ∈ RS.dartsOn (RS.edgeOf dart) := by simp
    rw [RS.endpoints_eq_pair_of_mem hdart, hvertLeft, hvertRight]
    have hinter : ({left, right} : Finset V) ∩ side = {left} := by
      ext vertex
      simp only [Finset.mem_inter, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hmem⟩
        · rfl
        · exact False.elim (hright hmem)
      · rintro rfl
        exact ⟨Or.inl rfl, hleft⟩
    rw [hinter, Finset.card_singleton]
  rw [hboundary] at hedge
  simpa using hedge

/-- Reachability after deleting the unique boundary edge remains on the same
vertex side. -/
theorem mem_of_reachable_edgeDeleted (RS : RotationSystem V E)
    (side : Finset V) (removed : E)
    (hboundary : RS.vertexSideEdgeBoundary side = {removed})
    {left right : V} (hleft : left ∈ side)
    (hreach : (edgeDeletedPrimalGraph RS removed).Reachable left right) :
    right ∈ side := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact hleft
  | tail _ hadj ih =>
      exact mem_of_adj_edgeDeleted RS side removed hboundary ih hadj

/-- **A singleton boundary edge is a bridge.**  Hence a bridge-free rotation
system has no finite vertex side whose edge boundary is a singleton. -/
theorem not_boundary_singleton_of_edgeBridgeFree
    (RS : RotationSystem V E) (hfree : EdgeBridgeFree RS)
    (side : Finset V) (removed : E)
    (hboundary : RS.vertexSideEdgeBoundary side = {removed}) : False := by
  classical
  have hremoved : removed ∈ RS.vertexSideEdgeBoundary side := by
    rw [hboundary]
    simp
  rw [RS.mem_vertexSideEdgeBoundary_iff] at hremoved
  obtain ⟨dart, hdart⟩ := RS.dartsOn_nonempty removed
  have hendpoints := RS.endpoints_eq_pair_of_mem hdart
  have hedge : RS.edgeOf dart = removed := RS.mem_dartsOn.1 hdart
  have hreach := hfree dart
  rw [hedge] at hreach
  by_cases hinside : RS.vertOf dart ∈ side
  · have houtside : RS.vertOf (RS.alpha dart) ∉ side := by
      intro hother
      rw [hendpoints] at hremoved
      have hinter :
          ({RS.vertOf dart, RS.vertOf (RS.alpha dart)} : Finset V) ∩ side =
            {RS.vertOf dart, RS.vertOf (RS.alpha dart)} := by
        rw [Finset.inter_eq_left]
        intro vertex hvertex
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvertex
        rcases hvertex with rfl | rfl <;> assumption
      rw [hinter, Finset.card_pair (RS.no_self_loops dart)] at hremoved
      omega
    exact houtside
      (mem_of_reachable_edgeDeleted RS side removed hboundary hinside hreach)
  · have hother : RS.vertOf (RS.alpha dart) ∈ side := by
      by_contra houtside
      rw [hendpoints] at hremoved
      have hinter :
          ({RS.vertOf dart, RS.vertOf (RS.alpha dart)} : Finset V) ∩ side = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro vertex hvertex
        rw [Finset.mem_inter] at hvertex
        have hendpoint := hvertex.1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hendpoint
        rcases hendpoint with rfl | rfl
        · exact hinside hvertex.2
        · exact houtside hvertex.2
      rw [hinter, Finset.card_empty] at hremoved
      omega
    exact hinside
      (mem_of_reachable_edgeDeleted RS side removed hboundary hother hreach.symm)

end

end GoertzelV24RotationBoundaryBridge

end Mettapedia.GraphTheory.FourColor
