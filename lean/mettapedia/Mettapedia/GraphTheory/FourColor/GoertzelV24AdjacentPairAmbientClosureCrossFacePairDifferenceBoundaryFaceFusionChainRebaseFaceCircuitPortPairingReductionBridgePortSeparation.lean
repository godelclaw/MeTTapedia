import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitPortPairingReductionBridgeWitness

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FourDefectBoundary
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

local instance portSeparationGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance portSeparationRetainedVertexSetFintype
    (first second : V) :
    Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance portSeparationRetainedVertexSetDecidableEq
    (first second : V) :
    DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- A predicate preserved across every edge of a reachable walk has the
same truth value at the two endpoints. -/
theorem iff_of_reachable_of_forall_adj_iff
    {W : Type*} {H : SimpleGraph W} (predicate : W → Prop)
    {start finish : W} (hreachable : H.Reachable start finish)
    (hadj : ∀ {left right : W}, H.Adj left right →
      (predicate left ↔ predicate right)) :
    predicate start ↔ predicate finish := by
  rcases hreachable with ⟨walk⟩
  induction walk with
  | nil => exact Iff.rfl
  | @cons first second finish hfirst tail ih =>
      exact (hadj hfirst).trans ih

/-- The inverse vertex identification from a square reduction back to the
induced adjacent-pair deletion. -/
def deletedVertexOfReductionVertex
    (data : AdjacentPairData G)
    (vertex : RetainedVertex (deletedRegionKeep data.deletedVertices)) :
    retainedVertexSet data.firstVertex data.secondVertex :=
  ⟨vertex.1, by
    have hkeep := vertex.2
    change vertex.1 ∉ data.deletedVertices at hkeep
    simpa [deletedVertices] using hkeep⟩

omit [Fintype V] [DecidableRel G.Adj] in
@[simp]
theorem deletedVertexOfReductionVertex_val
    (data : AdjacentPairData G)
    (vertex : RetainedVertex (deletedRegionKeep data.deletedVertices)) :
    (deletedVertexOfReductionVertex data vertex).1 = vertex.1 :=
  rfl

omit [Fintype V] [DecidableRel G.Adj] in
@[simp]
theorem deletedVertexOfReductionVertex_reductionVertex
    (data : AdjacentPairData G)
    (vertex : retainedVertexSet data.firstVertex data.secondVertex) :
    deletedVertexOfReductionVertex data
      (data.reductionVertexOfDeletedVertex vertex) = vertex := by
  apply Subtype.ext
  rfl

/-- The inverse vertex identification sends the first endpoint of an old
output dart back to the first endpoint of its induced-deletion dart. -/
theorem deletedVertexOfReductionVertex_internal_fst
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    deletedVertexOfReductionVertex data
        ((data.reductionRotationSystem graphData side).vertOf
          (Sum.inl internal)) =
      (deletedDartOfInternal graphData data internal).fst := by
  rw [← reductionVertex_deletedDartOfInternal_fst
      graphData data side internal,
    deletedVertexOfReductionVertex_reductionVertex]

/-- The inverse vertex identification sends the second endpoint of an old
output dart back to the second endpoint of its induced-deletion dart. -/
theorem deletedVertexOfReductionVertex_internal_snd
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    deletedVertexOfReductionVertex data
        ((data.reductionRotationSystem graphData side).vertOf
          ((data.reductionRotationSystem graphData side).alpha
            (Sum.inl internal))) =
      (deletedDartOfInternal graphData data internal).snd := by
  rw [← reductionVertex_deletedDartOfInternal_snd
      graphData data side internal,
    deletedVertexOfReductionVertex_reductionVertex]

/-- An internal output edge different from a fixed removed internal edge
gives an adjacency surviving deletion of the corresponding retained edge. -/
theorem deletedEdgeAdj_of_internal_edgeOf_ne
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (removed other : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices))
    (hne : (data.reductionRotationSystem graphData side).edgeOf
        (Sum.inl other) ≠
      (data.reductionRotationSystem graphData side).edgeOf
        (Sum.inl removed)) :
    ((DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).deleteEdges
        {(deletedEdgeOfInternal graphData data removed).1}).Adj
      (deletedDartOfInternal graphData data other).fst
      (deletedDartOfInternal graphData data other).snd := by
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨(deletedDartOfInternal graphData data other).adj, ?_⟩
  intro hedge
  rw [Set.mem_singleton_iff] at hedge
  apply hne
  rw [← reductionEdgeOfDeletedDartOfInternal_eq_edgeOf_internal
      graphData data side other,
    ← reductionEdgeOfDeletedDartOfInternal_eq_edgeOf_internal
      graphData data side removed]
  apply congrArg (data.reductionEdgeOfDeletedEdge graphData side)
  apply Subtype.ext
  exact hedge

/-- If every seam of a square reduction stays within the first endpoint
component of a fixed retained bridge, then every surviving reduction edge
preserves that component predicate. -/
theorem reductionEdgeDeleted_adj_preserves_deletedBridgeComponent
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (removed : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices))
    (hseams : ∀ step : Fin 2,
      ((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data removed).1}).Reachable
          (deletedDartOfInternal graphData data removed).fst
          (data.retainedPort (side.leftPort step)) ↔
        ((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data removed).1}).Reachable
          (deletedDartOfInternal graphData data removed).fst
          (data.retainedPort (side.rightPort step)))
    {left right : RetainedVertex
      (deletedRegionKeep data.deletedVertices)}
    (hadj : (edgeDeletedPrimalGraph
      (data.reductionRotationSystem graphData side)
      ((data.reductionRotationSystem graphData side).edgeOf
        (Sum.inl removed))).Adj left right) :
    (((DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).deleteEdges
          {(deletedEdgeOfInternal graphData data removed).1}).Reachable
        (deletedDartOfInternal graphData data removed).fst
        (deletedVertexOfReductionVertex data left) ↔
      ((DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).deleteEdges
          {(deletedEdgeOfInternal graphData data removed).1}).Reachable
        (deletedDartOfInternal graphData data removed).fst
        (deletedVertexOfReductionVertex data right)) := by
  rcases hadj with ⟨dart, hedge, hleft, hright⟩
  rcases dart with internal | boundary
  · have hinternal := deletedEdgeAdj_of_internal_edgeOf_ne
      graphData data side removed internal hedge
    have hleft' : deletedVertexOfReductionVertex data left =
        (deletedDartOfInternal graphData data internal).fst := by
      rw [← hleft,
        deletedVertexOfReductionVertex_internal_fst]
    have hright' : deletedVertexOfReductionVertex data right =
        (deletedDartOfInternal graphData data internal).snd := by
      rw [← hright,
        deletedVertexOfReductionVertex_internal_snd]
    rw [hleft', hright']
    constructor
    · intro hreach
      exact hreach.trans hinternal.reachable
    · intro hreach
      exact hreach.trans hinternal.symm.reachable
  · rcases boundary with leftBoundary | rightBoundary
    · rcases orderedBoundaryDart_surjective
        (data.rootedRotationSystem graphData)
        (deletedRegionKeep data.deletedVertices)
        (data.leftCrossing side) (data.leftCrosses graphData side)
        leftBoundary with ⟨step, rfl⟩
      change (data.reductionRotationSystem graphData side).vertOf
        (data.reductionLeftSeamDart graphData side step) = left at hleft
      change (data.reductionRotationSystem graphData side).vertOf
        ((data.reductionRotationSystem graphData side).alpha
          (data.reductionLeftSeamDart graphData side step)) = right at hright
      rw [data.reductionRotationSystem_vertOf_leftSeamDart] at hleft
      rw [data.reductionRotationSystem_alpha_leftSeamDart,
        data.reductionRotationSystem_vertOf_rightSeamDart] at hright
      rw [← hleft, ← hright,
        deletedVertexOfReductionVertex_reductionVertex,
        deletedVertexOfReductionVertex_reductionVertex]
      exact hseams step
    · rcases orderedBoundaryDart_surjective
        (data.rootedRotationSystem graphData)
        (deletedRegionKeep data.deletedVertices)
        (data.rightCrossing side) (data.rightCrosses graphData side)
        rightBoundary with ⟨step, rfl⟩
      change (data.reductionRotationSystem graphData side).vertOf
        (data.reductionRightSeamDart graphData side step) = left at hleft
      change (data.reductionRotationSystem graphData side).vertOf
        ((data.reductionRotationSystem graphData side).alpha
          (data.reductionRightSeamDart graphData side step)) = right at hright
      rw [data.reductionRotationSystem_vertOf_rightSeamDart] at hleft
      rw [data.reductionRotationSystem_alpha_rightSeamDart,
        data.reductionRotationSystem_vertOf_leftSeamDart] at hright
      rw [← hleft, ← hright,
        deletedVertexOfReductionVertex_reductionVertex,
        deletedVertexOfReductionVertex_reductionVertex]
      exact (hseams step).symm

/-- Under the same seam hypothesis, every avoiding path in the square
reduction preserves the retained bridge-component predicate. -/
theorem reductionEdgeDeleted_reachable_preserves_deletedBridgeComponent
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (removed : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices))
    (hseams : ∀ step : Fin 2,
      ((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data removed).1}).Reachable
          (deletedDartOfInternal graphData data removed).fst
          (data.retainedPort (side.leftPort step)) ↔
        ((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data removed).1}).Reachable
          (deletedDartOfInternal graphData data removed).fst
          (data.retainedPort (side.rightPort step)))
    {left right : RetainedVertex
      (deletedRegionKeep data.deletedVertices)}
    (hreachable : (edgeDeletedPrimalGraph
      (data.reductionRotationSystem graphData side)
      ((data.reductionRotationSystem graphData side).edgeOf
        (Sum.inl removed))).Reachable left right) :
    (((DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).deleteEdges
          {(deletedEdgeOfInternal graphData data removed).1}).Reachable
        (deletedDartOfInternal graphData data removed).fst
        (deletedVertexOfReductionVertex data left) ↔
      ((DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).deleteEdges
          {(deletedEdgeOfInternal graphData data removed).1}).Reachable
        (deletedDartOfInternal graphData data removed).fst
        (deletedVertexOfReductionVertex data right)) := by
  apply iff_of_reachable_of_forall_adj_iff
    (fun vertex =>
      ((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data removed).1}).Reachable
        (deletedDartOfInternal graphData data removed).fst
        (deletedVertexOfReductionVertex data vertex))
    hreachable
  intro first second hadj
  exact reductionEdgeDeleted_adj_preserves_deletedBridgeComponent
    graphData data side removed hseams hadj

/-- The two alternate seam classes of an internal bridge witness are
opposite.  If they coincided, both canonical seams would also preserve the
bridge components, contradicting bridge-freedom of the canonical reduction. -/
theorem Join12_30InternalBridgeWitness.port03_opposite_port12
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (witness : Join12_30InternalBridgeWitness graphData data) :
    ¬ ((((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data witness.internal).1}).Reachable
          (deletedDartOfInternal graphData data witness.internal).fst
          (data.retainedPort 0)) ↔
        ((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data witness.internal).1}).Reachable
          (deletedDartOfInternal graphData data witness.internal).fst
          (data.retainedPort 1)) := by
  intro hzeroOne
  have hcanonicalSeams : ∀ step : Fin 2,
      ((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data witness.internal).1}).Reachable
          (deletedDartOfInternal graphData data witness.internal).fst
          (data.retainedPort
            (SquareReductionSide.join01_23.leftPort step)) ↔
        ((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data witness.internal).1}).Reachable
          (deletedDartOfInternal graphData data witness.internal).fst
          (data.retainedPort
            (SquareReductionSide.join01_23.rightPort step)) := by
    intro step
    fin_cases step
    · simpa [SquareReductionSide.leftPort, SquareReductionSide.rightPort,
        SquareReductionSide.join01_23] using hzeroOne.symm
    · have htwoThree := witness.pair12_sameComponent.symm.trans
        (hzeroOne.symm.trans witness.pair03_sameComponent)
      simpa [SquareReductionSide.leftPort, SquareReductionSide.rightPort,
        SquareReductionSide.join01_23] using htwoThree
  have hcanonicalReach :=
    data.reductionJoin01_23_edgeBridgeFree graphData minimal
      (Sum.inl witness.internal)
  have hpreserved :=
    reductionEdgeDeleted_reachable_preserves_deletedBridgeComponent
      graphData data SquareReductionSide.join01_23 witness.internal
        hcanonicalSeams hcanonicalReach
  rw [deletedVertexOfReductionVertex_internal_fst,
    deletedVertexOfReductionVertex_internal_snd] at hpreserved
  exact witness.retainedSeparated (hpreserved.1 SimpleGraph.Reachable.rfl)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
