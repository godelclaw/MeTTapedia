import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeBoundaryOrbit

/-!
# One common constant-word Kempe orbit at an adjacent pair

The adjacent-pair boundary-orbit theorem reaches a prescribed nonzero
constant four-port word.  This file packages the stronger quantifier order
needed by the global formation programme: one rotation ordering and one base
colouring work for all three nonzero target colours.  The target colourings
may differ, but they lie in the same Kempe orbit of the same deleted graph.

This is a local entrance theorem.  It does not identify or synchronize the
orbits belonging to two different deleted adjacent pairs.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance commonOrbitRetainedVertexSetFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance commonOrbitRetainedVertexSetDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- Every adjacent pair in a graph-backed vertex-minimal Tait
counterexample has one rotation ordering and one deleted-graph Tait
colouring whose Kempe orbit contains each of the three nonzero constant
four-port words.

The common base colouring is load-bearing: the statement is stronger than
choosing an unrelated deleted-graph colouring separately for each target.
It still makes no compatibility assertion between distinct adjacent pairs.
-/
theorem exists_rotationOrdered_commonKempeOrbit_with_all_constantWords_of_minimal
    (graphData : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) :
    ∃ ordered : AdjacentPairData G,
      ordered.firstVertex = data.firstVertex ∧
      ordered.secondVertex = data.secondVertex ∧
      ∃ C : (DeletedAdjacentPairGraph G ordered.firstVertex
          ordered.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
          (DeletedAdjacentPairGraph G ordered.firstVertex
            ordered.secondVertex) C ∧
        ∀ target : Color, target ≠ 0 →
          ∃ C' : (DeletedAdjacentPairGraph G ordered.firstVertex
              ordered.secondVertex).EdgeColoring Color,
            C' ∈ (DeletedAdjacentPairGraph G ordered.firstVertex
                ordered.secondVertex).lineGraph.KempeClosure C ∧
            IsTaitEdgeColoring
              (DeletedAdjacentPairGraph G ordered.firstVertex
                ordered.secondVertex) C' ∧
            ∀ port : Fin 4,
              ordered.degreeTwoBoundaryData.colorWord C' port = target := by
  rcases data.exists_rotationOrdered_cyclicKempeProfile graphData minimal with
    ⟨ordered, hfirst, hsecond, ⟨profile⟩⟩
  refine ⟨ordered, hfirst, hsecond, profile.coloring,
    profile.isTaitColoring, ?_⟩
  intro target htarget
  exact profile.exists_kempeClosure_coloring_with_constant_colorWord_of_minimal
    minimal target htarget

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

/-! Publication-facing alias.  The implementation theorem belongs to the
adjacent-pair API; this alias also makes the defining module recoverable from
a manuscript citation. -/

alias GoertzelV24AdjacentPairCommonConstantOrbit.exists_rotationOrdered_commonKempeOrbit_with_all_constantWords_of_minimal :=
  GoertzelV24AdjacentPairBoundary.AdjacentPairData.exists_rotationOrdered_commonKempeOrbit_with_all_constantWords_of_minimal

end Mettapedia.GraphTheory.FourColor
