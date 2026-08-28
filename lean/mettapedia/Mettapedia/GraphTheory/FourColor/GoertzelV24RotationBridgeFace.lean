import Mettapedia.GraphTheory.FourColor.GoertzelV24BridgeTwoSided
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationEdgeBridge

/-!
# A bridge has one facial side in a rotation system

This is the rotation-system form of the elementary map fact used by Tait
duality.  If deleting an edge separates its endpoints, a facial walk that
crosses the edge can return to its starting side only through the opposite
dart of the same edge.  Thus the two darts belong to one face orbit.

The proof is entirely combinatorial.  The two sides are the reachability
classes in the edge-deleted primal graph, and the existing return lemma does
the finite permutation bookkeeping.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationBridgeFace

open GoertzelV24BridgeTwoSided
open GoertzelV24RotationEdgeBridge

noncomputable section

universe u v

variable {V : Type u} {E : Type v}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- If the endpoints of one edge are disconnected after deleting that edge,
then its two darts lie in one face orbit. -/
theorem phi_sameCycle_alpha_of_not_edgeDeleted_reachable
    (RS : RotationSystem V E) (dart : RS.D)
    (hbridge :
      ¬ (edgeDeletedPrimalGraph RS (RS.edgeOf dart)).Reachable
          (RS.vertOf dart) (RS.vertOf (RS.alpha dart))) :
    RS.phi.SameCycle dart (RS.alpha dart) := by
  classical
  let deleted := edgeDeletedPrimalGraph RS (RS.edgeOf dart)
  let side : RS.D → Bool := fun current =>
    decide (deleted.Reachable (RS.vertOf dart) (RS.vertOf current))
  have hside_dart : side dart = true := by
    simp [side, deleted]
  have hside_alpha : side (RS.alpha dart) = false := by
    simp [side, deleted, hbridge]
  have hcross : side (RS.phi dart) ≠ side dart := by
    have hphiVert : RS.vertOf (RS.phi dart) =
        RS.vertOf (RS.alpha dart) := by
      exact RS.vert_rho (RS.alpha dart)
    rw [show side (RS.phi dart) = side (RS.alpha dart) by
      simp only [side]
      rw [hphiVert]]
    rw [hside_alpha, hside_dart]
    decide
  apply sameCycle_of_bridge RS.phi side dart (RS.alpha dart) _ hcross
  intro current hneAlpha hfar
  have hneDart : current ≠ dart := by
    intro h
    subst current
    exact hfar rfl
  have hedge : RS.edgeOf current ≠ RS.edgeOf dart := by
    intro heq
    rcases RS.edge_fiber_two_cases (d := dart) (y := current) rfl heq with
      h | h
    · exact hneDart h
    · exact hneAlpha h
  have hadj : deleted.Adj (RS.vertOf current)
      (RS.vertOf (RS.alpha current)) := by
    exact ⟨current, hedge, rfl, rfl⟩
  have hiff :
      deleted.Reachable (RS.vertOf dart) (RS.vertOf (RS.phi current)) ↔
        deleted.Reachable (RS.vertOf dart) (RS.vertOf current) := by
    have hphiVert : RS.vertOf (RS.phi current) =
        RS.vertOf (RS.alpha current) := by
      exact RS.vert_rho (RS.alpha current)
    rw [hphiVert]
    exact ⟨fun h => h.trans hadj.reachable.symm,
      fun h => h.trans hadj.reachable⟩
  simp only [side]
  exact decide_eq_decide.mpr hiff

end

end GoertzelV24RotationBridgeFace

end Mettapedia.GraphTheory.FourColor
