import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCap
import Mettapedia.GraphTheory.FourColor.CyclicEdgeCut

/-!
# L1: the restored facial cap supplies a side cycle

Closing a literal pentagon-cap opening restores five primal cycle edges.
This module records the graph-level fact needed by the cyclic-cut transport:
the ordered cap coordinates construct an actual five-step primal cycle, and
placing all five cap vertices on one side places that cycle on the same side.

This is one input to the source-formation comparison.  It does not assert that
an abstract Addendum-V frontier is itself obtained by opening a closed graph.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapSideCycle

open SimpleGraph
open GoertzelV24FacialPentagonCap

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {data : SimpleGraphDartRotation.Data G}

noncomputable section

namespace OrientedFacialPentagonCap

private theorem adjacent_step
    (cap : OrientedFacialPentagonCap data) (step : Fin 5) :
    G.Adj (cap.toFacialPentagonCap.toPentagonCap.vertex step)
      (cap.toFacialPentagonCap.toPentagonCap.vertex (step + 1)) := by
  rw [← SimpleGraph.mem_edgeSet]
  rw [← cap.cycleEdge_eq_vertices step]
  exact (cap.toFacialPentagonCap.toPentagonCap.cycleEdge step).2

/-- The literal five-step primal boundary cycle restored when the cap is
closed. -/
def primalCycle (cap : OrientedFacialPentagonCap data) :
    G.Walk (cap.toFacialPentagonCap.toPentagonCap.vertex 0)
      (cap.toFacialPentagonCap.toPentagonCap.vertex 0) :=
  .cons (adjacent_step cap 0)
    (.cons (adjacent_step cap 1)
      (.cons (adjacent_step cap 2)
        (.cons (adjacent_step cap 3)
          (.cons (adjacent_step cap 4) .nil))))

/-- Injectivity of the ordered cap coordinates makes the restored five-step
walk a genuine cycle. -/
theorem primalCycle_isCycle (cap : OrientedFacialPentagonCap data) :
    (primalCycle cap).IsCycle := by
  simp [primalCycle, Walk.cons_isCycle_iff, Walk.cons_isPath_iff,
    cap.toFacialPentagonCap.toPentagonCap.vertex.injective.eq_iff]

/-- If the five cap vertices lie on one chosen side, restoring the cap gives
a cycle wholly contained on that side. -/
theorem hasCycleOnSide_of_vertices
    (cap : OrientedFacialPentagonCap data) (side : V → Prop)
    (hvertices : ∀ step : Fin 5,
      side (cap.toFacialPentagonCap.toPentagonCap.vertex step)) :
    HasCycleOnSide G side := by
  refine ⟨cap.toFacialPentagonCap.toPentagonCap.vertex 0, hvertices 0,
    primalCycle cap, primalCycle_isCycle cap, ?_⟩
  intro vertex hvertex
  simp [primalCycle] at hvertex
  rcases hvertex with hvertex | hvertex | hvertex | hvertex | hvertex | hvertex
  · simpa [hvertex] using hvertices 0
  · simpa [hvertex] using hvertices 1
  · simpa [hvertex] using hvertices 2
  · simpa [hvertex] using hvertices 3
  · simpa [hvertex] using hvertices 4
  · simpa [hvertex] using hvertices 0

end OrientedFacialPentagonCap

end

end GoertzelV24FacialPentagonCapSideCycle

end Mettapedia.GraphTheory.FourColor
