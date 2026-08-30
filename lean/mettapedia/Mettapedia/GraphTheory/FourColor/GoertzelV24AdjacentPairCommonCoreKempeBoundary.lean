import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairColoringAtlas
import Mettapedia.GraphTheory.FourColor.GoertzelV24KempeComponentEmbeddingBoundary

/-!
# Lifting common-core Kempe moves to an adjacent-pair deletion

The exact common deletion of two adjacent pairs embeds into either
pair-deletion graph.  A selected Kempe component in the common deletion either
lifts to the first deletion, or reaches an edge incident with one of the
vertices deleted only from the common core.  Iterating this statement lifts a
whole common-core Kempe sequence unless such a boundary-reaching component
appears at an intermediate colouring.

This turns abstract common-core Kempe reachability into a physical dichotomy.
It does not claim that a boundary-reaching strand already yields wall
exclusion.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairCommonCoreKempeBoundary

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24KempeComponentEmbeddingBoundary
open GoertzelV24LocalSwapKempeGeneration
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- An edge of the first pair-deletion which is not in the common-core image
has an endpoint at one of the vertices deleted by the second pair. -/
theorem exists_endpoint_at_second_pair_of_not_in_firstCommonCore_range
    (source target : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).edgeSet)
    (hnot : ¬ ∃ preimage :
        (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
          target.firstVertex target.secondVertex).edgeSet,
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
        source.secondVertex target.firstVertex target.secondVertex).mapEdgeSet
          preimage = edge) :
    ∃ endpoint : retainedVertexSet source.firstVertex source.secondVertex,
      endpoint ∈ (edge.1 : Sym2
        (retainedVertexSet source.firstVertex source.secondVertex)) ∧
      (endpoint.1 = target.firstVertex ∨
        endpoint.1 = target.secondVertex) := by
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      by_cases hleftFirst : left.1 = target.firstVertex
      · exact ⟨left, Sym2.mem_mk_left left right, Or.inl hleftFirst⟩
      · by_cases hleftSecond : left.1 = target.secondVertex
        · exact ⟨left, Sym2.mem_mk_left left right, Or.inr hleftSecond⟩
        · by_cases hrightFirst : right.1 = target.firstVertex
          · exact ⟨right, Sym2.mem_mk_right left right, Or.inl hrightFirst⟩
          · by_cases hrightSecond : right.1 = target.secondVertex
            · exact ⟨right, Sym2.mem_mk_right left right, Or.inr hrightSecond⟩
            · exfalso
              apply hnot
              let leftCommon : {vertex : V |
                  vertex ≠ source.firstVertex ∧
                    vertex ≠ source.secondVertex ∧
                    vertex ≠ target.firstVertex ∧
                    vertex ≠ target.secondVertex} :=
                ⟨left.1, left.2.1, left.2.2,
                  hleftFirst, hleftSecond⟩
              let rightCommon : {vertex : V |
                  vertex ≠ source.firstVertex ∧
                    vertex ≠ source.secondVertex ∧
                    vertex ≠ target.firstVertex ∧
                    vertex ≠ target.secondVertex} :=
                ⟨right.1, right.2.1, right.2.2,
                  hrightFirst, hrightSecond⟩
              let commonEdge :
                  (DeletedTwoPairsGraph G source.firstVertex
                    source.secondVertex target.firstVertex
                    target.secondVertex).edgeSet :=
                ⟨s(leftCommon, rightCommon), hedge⟩
              refine ⟨commonEdge, ?_⟩
              rfl

/-- A common-core component physically reaches the pair removed only when
passing from the first deletion to the common deletion. -/
def FirstComponentReachesSecondPair
    (source target : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (first second : Color)
    (component : ((firstDeletionCommonCoreColoring
      (third := target.firstVertex) (fourth := target.secondVertex)
      coloring).bicoloredSubgraph first second).ConnectedComponent) : Prop :=
  ∃ commonEdge,
    commonEdge ∈ (firstDeletionCommonCoreColoring
      (third := target.firstVertex) (fourth := target.secondVertex)
      coloring).kempeComponentSet first second component ∧
    ∃ deletionEdge,
      deletionEdge ∈ coloring.bicoloredSet first second ∧
      (DeletedAdjacentPairGraph G source.firstVertex
        source.secondVertex).lineGraph.Adj
          ((deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
            source.secondVertex target.firstVertex target.secondVertex).mapEdgeSet
              commonEdge)
          deletionEdge ∧
      ∃ endpoint : retainedVertexSet source.firstVertex source.secondVertex,
        endpoint ∈ (deletionEdge.1 : Sym2
          (retainedVertexSet source.firstVertex source.secondVertex)) ∧
        (endpoint.1 = target.firstVertex ∨
          endpoint.1 = target.secondVertex)

omit [Fintype V] [DecidableRel G.Adj] in
/-- The generic embedding-boundary horn is exactly a physical encounter with
an edge at the second deleted pair. -/
theorem firstComponentReachesSecondPair_of_touchesEmbeddingBoundary
    (source target : AdjacentPairData G)
    (coloring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (first second : Color)
    (component : ((firstDeletionCommonCoreColoring
      (third := target.firstVertex) (fourth := target.secondVertex)
      coloring).bicoloredSubgraph first second).ConnectedComponent)
    (htouches : ComponentTouchesEmbeddingBoundary coloring
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
        source.secondVertex target.firstVertex target.secondVertex)
      first second component) :
    FirstComponentReachesSecondPair source target coloring
      first second component := by
  rcases htouches with
    ⟨commonEdge, hcommon, deletionEdge, hselected, hadj, hnot⟩
  exact ⟨commonEdge, hcommon, deletionEdge, hselected, hadj,
    exists_endpoint_at_second_pair_of_not_in_firstCommonCore_range
      source target deletionEdge hnot⟩

/-- A boundary-reaching step occurs at some representative of the first
deletion's Kempe orbit. -/
def FirstOrbitReachesSecondPair
    (source target : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color) : Prop :=
  ∃ current,
    current ∈ (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeKempeClosure base ∧
    ∃ first second : Color,
      ∃ component : ((firstDeletionCommonCoreColoring
        (third := target.firstVertex) (fourth := target.secondVertex)
        current).bicoloredSubgraph first second).ConnectedComponent,
        FirstComponentReachesSecondPair source target current
          first second component

omit [Fintype V] [DecidableRel G.Adj] in
/-- **Common-core lift-or-boundary dichotomy.**  A whole common-core Kempe
sequence lifts into the first pair-deletion unless an intermediate component
reaches the vertices of the second pair. -/
theorem firstOrbitReachesSecondPair_or_exists_liftedColoring
    (source target : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetCommon :
      (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex).EdgeColoring Color)
    (hreachable : targetCommon ∈
      (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex).EdgeKempeClosure
          (firstDeletionCommonCoreColoring
            (third := target.firstVertex) (fourth := target.secondVertex)
            base)) :
    FirstOrbitReachesSecondPair source target base ∨
      ∃ lifted,
        lifted ∈ (DeletedAdjacentPairGraph G source.firstVertex
          source.secondVertex).EdgeKempeClosure base ∧
        firstDeletionCommonCoreColoring
          (third := target.firstVertex) (fourth := target.secondVertex)
          lifted = targetCommon := by
  rcases boundaryAlongLiftOrbit_or_exists_liftedColoring
      base
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
        source.secondVertex target.firstVertex target.secondVertex)
      targetCommon hreachable with
    hboundary | hlifted
  · left
    rcases hboundary with
      ⟨current, hcurrent, first, second, component, htouches⟩
    exact ⟨current, hcurrent, first, second, component,
      firstComponentReachesSecondPair_of_touchesEmbeddingBoundary
        source target current first second component htouches⟩
  · exact Or.inr hlifted

/-! ## The nonzero Tait-world specialization -/

/-- A valid-pair boundary-reaching step occurs at some representative of the
first deletion's Tait-Kempe orbit. -/
def FirstTaitOrbitReachesSecondPair
    (source target : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color) : Prop :=
  ∃ current,
    TaitKempeReachable base current ∧
    ∃ first second : Color, ValidColorPair first second ∧
      ∃ component : ((firstDeletionCommonCoreColoring
        (third := target.firstVertex) (fourth := target.secondVertex)
        current).bicoloredSubgraph first second).ConnectedComponent,
        FirstComponentReachesSecondPair source target current
          first second component

omit [Fintype V] [DecidableRel G.Adj] in
/-- **Tait-preserving common-core lift-or-boundary dichotomy.**  A whole
valid-pair common-core Kempe sequence lifts into the first pair deletion
without introducing zero, unless an intermediate component reaches the
vertices of the second pair. -/
theorem firstTaitOrbitReachesSecondPair_or_exists_liftedColoring
    (source target : AdjacentPairData G)
    (base : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (hbase : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
      base)
    (targetCommon :
      (DeletedTwoPairsGraph G source.firstVertex source.secondVertex
        target.firstVertex target.secondVertex).EdgeColoring Color)
    (hreachable : TaitKempeReachable
      (firstDeletionCommonCoreColoring
        (third := target.firstVertex) (fourth := target.secondVertex)
        base)
      targetCommon) :
    FirstTaitOrbitReachesSecondPair source target base ∨
      ∃ lifted,
        TaitKempeReachable base lifted ∧
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G source.firstVertex source.secondVertex)
          lifted ∧
        firstDeletionCommonCoreColoring
          (third := target.firstVertex) (fourth := target.secondVertex)
          lifted = targetCommon := by
  rcases taitBoundaryAlongLiftOrbit_or_exists_liftedColoring
      base hbase
      (deletedTwoPairsToFirstDeletionEmbedding G source.firstVertex
        source.secondVertex target.firstVertex target.secondVertex)
      targetCommon hreachable with
    hboundary | hlifted
  · left
    rcases hboundary with
      ⟨current, hcurrent, first, second, hpair, component, htouches⟩
    exact ⟨current, hcurrent, first, second, hpair, component,
      firstComponentReachesSecondPair_of_touchesEmbeddingBoundary
        source target current first second component htouches⟩
  · exact Or.inr hlifted

end

end GoertzelV24AdjacentPairCommonCoreKempeBoundary

end Mettapedia.GraphTheory.FourColor
