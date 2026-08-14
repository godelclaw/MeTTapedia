import Mettapedia.GraphTheory.FourColor.GoertzelV24DeleteEdgesCyclicCutPullback
import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapOpening

/-!
# L1: cyclic-cut pullback for the literal pentagon opening

The toolchain opens a pentagon cap by deleting its five cycle edges and
retaining the five cap vertices as degree-one inner stubs.  This module
specializes the generic edge-deletion pullback: if the chosen cut side avoids
all five inner stubs, every restored cap-cycle edge lies wholly outside that
side.  Hence a cyclic cut of the opened graph pulls back to the pre-opening
frontier graph without changing its cardinality.

This is the one-cap graph transport used by Addendum V.  It does not assert
that the pre-opening frontier graph is a closed vertex-minimal
counterexample; any connectivity contradiction must be discharged from the
actual source induction data at the caller.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PentagonCapCyclicCutPullback

open GoertzelV24DeleteEdgesCyclicCutPullback
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24PentagonCapOpening
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace PentagonCap

omit [DecidableRel G.Adj] in
/-- If the chosen side avoids every cap stub, none of the five edges restored
when closing the cap can cross that side. -/
theorem cycleValueSet_noncrossing_of_vertices_outside
    (cap : PentagonCap G)
    (cut : SmallCyclicEdgeCut cap.openGraph)
    (hverticesOutside : ∀ step : Fin 5, ¬ cut.side (cap.vertex step)) :
    ∀ edge : G.edgeSet,
      edge.1 ∈ edgeFinsetValueSet cap.cycleSupport →
        ¬ EdgeCrossesVertexSide G cut.side edge := by
  intro edge hremoved hcross
  rcases (mem_edgeFinsetValueSet_iff cap.cycleSupport edge.1).1 hremoved with
    ⟨cycleEdge, hcycleEdge, hcycleValue⟩
  rcases Finset.mem_map.mp hcycleEdge with ⟨cycle, _hcycle, hcycleEq⟩
  have hedgeEq : cap.cycleEdge cycle = edge := by
    apply Subtype.ext
    calc
      (cap.cycleEdge cycle).1 = cycleEdge.1 := congrArg Subtype.val hcycleEq
      _ = edge.1 := hcycleValue
  rcases hcross with ⟨inside, outside, hinsideEdge, _houtsideEdge,
    hinside, _houtside⟩
  have hinsideCycle : inside ∈ (cap.cycleEdge cycle).1 := by
    simpa [hedgeEq] using hinsideEdge
  rcases cap.cycleEdge_endpoint_eq_vertex cycle inside hinsideCycle with
    ⟨step, hstep⟩
  exact hverticesOutside step (by simpa [hstep] using hinside)

/-- Close the literal pentagon opening around a cyclic cut whose chosen side
avoids all five inner stubs. -/
def pullbackOpenGraphCyclicCut_of_vertices_outside
    (cap : PentagonCap G)
    (cut : SmallCyclicEdgeCut cap.openGraph)
    (hverticesOutside : ∀ step : Fin 5, ¬ cut.side (cap.vertex step)) :
    SmallCyclicEdgeCut G :=
  pullbackDeleteEdges (edgeFinsetValueSet cap.cycleSupport) cut
    (cycleValueSet_noncrossing_of_vertices_outside cap cut hverticesOutside)

omit [DecidableRel G.Adj] in
@[simp]
theorem pullbackOpenGraphCyclicCut_of_vertices_outside_card
    (cap : PentagonCap G)
    (cut : SmallCyclicEdgeCut cap.openGraph)
    (hverticesOutside : ∀ step : Fin 5, ¬ cut.side (cap.vertex step)) :
    (pullbackOpenGraphCyclicCut_of_vertices_outside cap
      cut hverticesOutside).edgeCut.card = cut.edgeCut.card := by
  exact pullbackDeleteEdges_edgeCut_card
    (edgeFinsetValueSet cap.cycleSupport) cut
    (cycleValueSet_noncrossing_of_vertices_outside cap cut hverticesOutside)

omit [DecidableRel G.Adj] in
/-- Ambient cyclic connectivity can be consumed directly after the literal
cap is restored; no global cyclic-connectivity assertion about the opened
stub graph is required. -/
theorem card_ge_of_ambient_cyclicEdgeConnectivityAtLeast
    {k : Nat} (cap : PentagonCap G)
    (hcyclic : CyclicEdgeConnectivityAtLeast G k)
    (cut : SmallCyclicEdgeCut cap.openGraph)
    (hverticesOutside : ∀ step : Fin 5, ¬ cut.side (cap.vertex step)) :
    k ≤ cut.edgeCut.card := by
  exact
    GoertzelV24DeleteEdgesCyclicCutPullback.card_ge_of_ambient_cyclicEdgeConnectivityAtLeast
      (edgeFinsetValueSet cap.cycleSupport) hcyclic cut
      (cycleValueSet_noncrossing_of_vertices_outside cap cut hverticesOutside)

end PentagonCap

end

end GoertzelV24PentagonCapCyclicCutPullback

end Mettapedia.GraphTheory.FourColor
