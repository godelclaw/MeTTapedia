import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairCyclicCutPullback
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutGluing

/-!
# L1: exclude a one-sided small cut in the two-cap minimal laboratory

The simultaneous two-cap laboratory is cut directly from a closed
graph-backed vertex-minimal Tait counterexample.  The preceding transport
restores both facial pentagons and turns any one-sided opened cut of size at
most four into a small cyclic cut of that closed graph.  Minimal-counterexample
cyclic five-edge-connectivity then excludes it.

This is an unconditional contradiction for the supplied two-cap laboratory.
It is not a realization theorem for Addendum V's frontier tangle, whose outer
stubs are primitive source data rather than a second cap opening.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalFacialPentagonCapPairNoSmallCut

open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapPairCyclicCutPullback
open GoertzelV24FourEdgeCutGluing
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- A one-sided cyclic cut of the simultaneous facial two-cap opening is
impossible when the ambient carrier is a graph-backed vertex-minimal Tait
counterexample. -/
theorem false_of_openGraph_oneSidedCut
    (graphData : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (edgeCut : Finset
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet)
    (side : V → Prop)
    (hcut_eq : ∀ edge :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.edgeSet,
      edge ∈ edgeCut ↔
        EdgeCrossesVertexSide
          caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph side edge)
    (hcard_le_four : edgeCut.card ≤ 4)
    (hinside_cycle : HasCycleOnSide
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph side)
    (hinnerOutside : ∀ step : Fin 5,
      ¬ side (caps.toFacialPentagonCapPair.toPentagonCapPair.inner.vertex step))
    (houterOutside : ∀ step : Fin 5,
      ¬ side (caps.toFacialPentagonCapPair.toPentagonCapPair.outer.vertex step)) :
    False := by
  let cut : SmallCyclicEdgeCut G :=
    OrientedFacialPentagonCapPair.pullbackOpenGraphOneSided_of_vertices_outside
      caps edgeCut side hcut_eq hcard_le_four hinside_cycle
      hinnerOutside houterOutside
  exact
    (cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
      graphData minimal).not_smallCyclicEdgeCut_card_le_four cut
        cut.hcard_le_four

end

end GoertzelV24MinimalFacialPentagonCapPairNoSmallCut

end Mettapedia.GraphTheory.FourColor
