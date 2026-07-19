import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitPortPairingReductionObstruction

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

local instance bridgeWitnessGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance bridgeWitnessRetainedVertexSetFintype
    (first second : V) :
    Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance bridgeWitnessRetainedVertexSetDecidableEq
    (first second : V) :
    DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- In a connected graph, deleting one dart edge leaves every vertex in
the deletion component of at least one endpoint of that dart. -/
theorem reachable_deleteEdge_endpoint_or_endpoint
    {W : Type*} {H : SimpleGraph W}
    (hconnected : H.Connected) (removed : H.Dart) (vertex : W) :
    (H.deleteEdges {removed.edge}).Reachable removed.fst vertex ∨
      (H.deleteEdges {removed.edge}).Reachable removed.snd vertex := by
  let deleted := H.deleteEdges {removed.edge}
  have propagate : ∀ {start finish : W}, H.Walk start finish →
      (deleted.Reachable removed.fst start ∨
        deleted.Reachable removed.snd start) →
      deleted.Reachable removed.fst finish ∨
        deleted.Reachable removed.snd finish := by
    intro start finish walk
    induction walk with
    | nil =>
        intro hstart
        exact hstart
    | @cons first second finish hadj tail ih =>
        intro hfirst
        have hsecond : deleted.Reachable removed.fst second ∨
            deleted.Reachable removed.snd second := by
          by_cases hedge : s(first, second) = removed.edge
          · have hsecondMem : second ∈ removed.edge := by
              rw [← hedge]
              simp
            have hcases : second = removed.fst ∨
                second = removed.snd := by
              simpa [SimpleGraph.Dart.edge, Sym2.mem_iff] using hsecondMem
            rcases hcases with rfl | rfl
            · exact Or.inl SimpleGraph.Reachable.rfl
            · exact Or.inr SimpleGraph.Reachable.rfl
          · have hdeletedAdj : deleted.Adj first second := by
              rw [SimpleGraph.deleteEdges_adj]
              refine ⟨hadj, ?_⟩
              simp [hedge]
            rcases hfirst with hleft | hright
            · exact Or.inl (hleft.trans hdeletedAdj.reachable)
            · exact Or.inr (hright.trans hdeletedAdj.reachable)
        exact ih hsecond
  rcases hconnected removed.fst vertex with ⟨walk⟩
  exact propagate walk (Or.inl SimpleGraph.Reachable.rfl)

/-- An old internal splice dart, regarded as the same oriented edge in the
induced adjacent-pair deletion. -/
def deletedDartOfInternal
    (graphData : Data G) (data : AdjacentPairData G)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Dart := by
  let left : retainedVertexSet data.firstVertex data.secondVertex :=
    ⟨internal.1.1.fst, by
      have hkeep := internal.1.2
      change internal.1.1.fst ∉ data.deletedVertices at hkeep
      simpa [deletedVertices] using hkeep⟩
  let right : retainedVertexSet data.firstVertex data.secondVertex :=
    ⟨internal.1.1.snd, by
      have hkeep := internal.2
      change internal.1.1.snd ∉ data.deletedVertices at hkeep
      simpa [deletedVertices] using hkeep⟩
  exact ⟨(left, right), internal.1.1.adj⟩

@[simp]
theorem deletedDartOfInternal_fst_val
    (graphData : Data G) (data : AdjacentPairData G)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    (deletedDartOfInternal graphData data internal).fst.1 =
      internal.1.1.fst :=
  rfl

@[simp]
theorem deletedDartOfInternal_snd_val
    (graphData : Data G) (data : AdjacentPairData G)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    (deletedDartOfInternal graphData data internal).snd.1 =
      internal.1.1.snd :=
  rfl

/-- The unoriented induced-deletion edge underlying an internal splice
dart. -/
def deletedEdgeOfInternal
    (graphData : Data G) (data : AdjacentPairData G)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
  ⟨(deletedDartOfInternal graphData data internal).edge,
    (deletedDartOfInternal graphData data internal).edge_mem⟩

/-- The induced-deletion edge represented by an internal dart embeds back
to its original ambient rotation edge. -/
theorem retainedEdgeToAmbientEdge_deletedDartOfInternal_edge
    (graphData : Data G) (data : AdjacentPairData G)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    data.retainedEdgeToAmbientEdge
        (deletedEdgeOfInternal graphData data internal) =
      (data.rootedRotationSystem graphData).edgeOf internal.1.1 := by
  apply Subtype.ext
  rfl

/-- The output edge of an internal splice dart is the square-reduction edge
obtained from the corresponding induced-deletion edge. -/
theorem reductionEdgeOfDeletedDartOfInternal_eq_edgeOf_internal
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    data.reductionEdgeOfDeletedEdge graphData side
        (deletedEdgeOfInternal graphData data internal) =
      (data.reductionRotationSystem graphData side).edgeOf
        (Sum.inl internal) := by
  apply (retainedInternalSpliceEdge_eq_iff
    (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices)
    (data.leftCrossing side) (data.rightCrossing side)
    (data.leftCrosses graphData side) (data.rightCrosses graphData side)
    (data.leftCrossing_injective side)
    (data.rightCrossing_injective side)
    (data.boundaryCover graphData side) (data.pairedCuts_disjoint side)
    (data.outer_retained graphData) (data.seamEndpoints graphData side)
    (data.retainedEdgeInternalDart graphData
      (deletedEdgeOfInternal graphData data internal))
    internal).2
  rw [data.retainedEdgeInternalDart_edgeOf,
    retainedEdgeToAmbientEdge_deletedDartOfInternal_edge]

@[simp]
theorem reductionVertex_deletedDartOfInternal_fst
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    data.reductionVertexOfDeletedVertex
        (deletedDartOfInternal graphData data internal).fst =
      (data.reductionRotationSystem graphData side).vertOf
        (Sum.inl internal) := by
  apply Subtype.ext
  rfl

@[simp]
theorem reductionVertex_deletedDartOfInternal_snd
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (internal : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices)) :
    data.reductionVertexOfDeletedVertex
        (deletedDartOfInternal graphData data internal).snd =
      (data.reductionRotationSystem graphData side).vertOf
        ((data.reductionRotationSystem graphData side).alpha
          (Sum.inl internal)) := by
  apply Subtype.ext
  rfl

/-- Adjacency surviving deletion of an old induced-deletion edge maps to
adjacency surviving deletion of the corresponding square-reduction edge. -/
theorem deletedEdgeAdj_mapsTo_reductionEdgeDeletedAdj
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (removed : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices))
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (hadj : ((DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).deleteEdges
        {(deletedEdgeOfInternal graphData data removed).1}).Adj left right) :
    (edgeDeletedPrimalGraph (data.reductionRotationSystem graphData side)
      ((data.reductionRotationSystem graphData side).edgeOf
        (Sum.inl removed))).Adj
      (data.reductionVertexOfDeletedVertex left)
      (data.reductionVertexOfDeletedVertex right) := by
  rcases SimpleGraph.deleteEdges_adj.mp hadj with
    ⟨hretainedAdj, hnotRemoved⟩
  let edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
    ⟨s(left, right), hretainedAdj⟩
  apply edgeDeletedPrimalGraph_adj_of_mem_endpoints
    (data.reductionRotationSystem graphData side)
    (edge := data.reductionEdgeOfDeletedEdge graphData side edge)
  · intro hedge
    apply hnotRemoved
    rw [Set.mem_singleton_iff]
    have hedge' : data.reductionEdgeOfDeletedEdge graphData side edge =
        data.reductionEdgeOfDeletedEdge graphData side
          (deletedEdgeOfInternal graphData data removed) := by
      exact hedge.trans
        (reductionEdgeOfDeletedDartOfInternal_eq_edgeOf_internal
          graphData data side removed).symm
    exact congrArg Subtype.val
      (data.reductionEdgeOfDeletedEdge_injective graphData side hedge')
  · apply data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
    change left ∈ s(left, right)
    rw [Sym2.mem_iff]
    exact Or.inl rfl
  · apply data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge
    change right ∈ s(left, right)
    rw [Sym2.mem_iff]
    exact Or.inr rfl
  · intro heq
    apply hretainedAdj.ne
    apply Subtype.ext
    exact congrArg
      (fun vertex : RetainedVertex
        (deletedRegionKeep data.deletedVertices) => vertex.1) heq

/-- Reachability in the retained deletion after removing an old edge maps
to reachability in either square reduction after removing its output edge. -/
theorem deletedEdgeReachable_mapsTo_reductionEdgeDeletedReachable
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide)
    (removed : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices))
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (hreachable : ((DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).deleteEdges
        {(deletedEdgeOfInternal graphData data removed).1}).Reachable
          left right) :
    (edgeDeletedPrimalGraph (data.reductionRotationSystem graphData side)
      ((data.reductionRotationSystem graphData side).edgeOf
        (Sum.inl removed))).Reachable
      (data.reductionVertexOfDeletedVertex left)
      (data.reductionVertexOfDeletedVertex right) := by
  exact reachable_map_of_adj_eq_or_adj
    data.reductionVertexOfDeletedVertex
    (fun {_ _} hadj => Or.inr
      (deletedEdgeAdj_mapsTo_reductionEdgeDeletedAdj
        graphData data side removed hadj))
    hreachable

/-- If deleting an old output edge separates a square reduction, then each
inserted seam joins ports on the same endpoint side of the corresponding
bridge in the retained deletion. -/
theorem deletedBridgeComponent_sameSide_reductionSeamPorts
    (graphData : Data G) (data : AdjacentPairData G)
    (hretained : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Connected)
    (side : SquareReductionSide)
    (removed : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices))
    (hnotReduction : ¬
      (edgeDeletedPrimalGraph (data.reductionRotationSystem graphData side)
        ((data.reductionRotationSystem graphData side).edgeOf
          (Sum.inl removed))).Reachable
        ((data.reductionRotationSystem graphData side).vertOf
          (Sum.inl removed))
        ((data.reductionRotationSystem graphData side).vertOf
          ((data.reductionRotationSystem graphData side).alpha
            (Sum.inl removed))))
    (step : Fin 2) :
    ((DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).deleteEdges
          {(deletedEdgeOfInternal graphData data removed).1}).Reachable
        (deletedDartOfInternal graphData data removed).fst
        (data.retainedPort (side.leftPort step)) ↔
      ((DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).deleteEdges
          {(deletedEdgeOfInternal graphData data removed).1}).Reachable
        (deletedDartOfInternal graphData data removed).fst
        (data.retainedPort (side.rightPort step)) := by
  let retained := DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex
  let removedDart := deletedDartOfInternal graphData data removed
  let deleted := retained.deleteEdges
    {(deletedEdgeOfInternal graphData data removed).1}
  have hseam := data.reductionSeam_adj_edgeDeleted_internalDart
    graphData side removed step
  constructor
  · intro hleft
    by_contra hnotRight
    have hcover := reachable_deleteEdge_endpoint_or_endpoint
      hretained removedDart (data.retainedPort (side.rightPort step))
    rcases hcover with hrightFromFirst | hrightFromSecond
    · exact hnotRight hrightFromFirst
    · apply hnotReduction
      rw [← reductionVertex_deletedDartOfInternal_fst
          graphData data side removed,
        ← reductionVertex_deletedDartOfInternal_snd
          graphData data side removed]
      have hleftMapped :=
        deletedEdgeReachable_mapsTo_reductionEdgeDeletedReachable
          graphData data side removed hleft
      have hrightMapped :=
        deletedEdgeReachable_mapsTo_reductionEdgeDeletedReachable
          graphData data side removed hrightFromSecond
      exact (hleftMapped.trans hseam.reachable).trans hrightMapped.symm
  · intro hright
    by_contra hnotLeft
    have hcover := reachable_deleteEdge_endpoint_or_endpoint
      hretained removedDart (data.retainedPort (side.leftPort step))
    rcases hcover with hleftFromFirst | hleftFromSecond
    · exact hnotLeft hleftFromFirst
    · apply hnotReduction
      rw [← reductionVertex_deletedDartOfInternal_fst
          graphData data side removed,
        ← reductionVertex_deletedDartOfInternal_snd
          graphData data side removed]
      have hrightMapped :=
        deletedEdgeReachable_mapsTo_reductionEdgeDeletedReachable
          graphData data side removed hright
      have hleftMapped :=
        deletedEdgeReachable_mapsTo_reductionEdgeDeletedReachable
          graphData data side removed hleftFromSecond
      exact (hrightMapped.trans hseam.symm.reachable).trans
        hleftMapped.symm

/-- For the alternate square pairing, the preceding component constraint
gives the two port-component equalities `0 ~ 3` and `1 ~ 2`. -/
theorem deletedBridgeComponent_join12_30_pairs
    (graphData : Data G) (data : AdjacentPairData G)
    (hretained : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Connected)
    (removed : InternalDart (data.rootedRotationSystem graphData)
      (deletedRegionKeep data.deletedVertices))
    (hnotReduction : ¬
      (edgeDeletedPrimalGraph
        (data.reductionRotationSystem graphData
          SquareReductionSide.join12_30)
        ((data.reductionRotationSystem graphData
          SquareReductionSide.join12_30).edgeOf
            (Sum.inl removed))).Reachable
        ((data.reductionRotationSystem graphData
          SquareReductionSide.join12_30).vertOf
            (Sum.inl removed))
        ((data.reductionRotationSystem graphData
          SquareReductionSide.join12_30).vertOf
            ((data.reductionRotationSystem graphData
              SquareReductionSide.join12_30).alpha
                (Sum.inl removed)))) :
    ((((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data removed).1}).Reachable
          (deletedDartOfInternal graphData data removed).fst
          (data.retainedPort 0) ↔
        ((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data removed).1}).Reachable
          (deletedDartOfInternal graphData data removed).fst
          (data.retainedPort 3)) ∧
      (((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data removed).1}).Reachable
          (deletedDartOfInternal graphData data removed).fst
          (data.retainedPort 1) ↔
        ((DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).deleteEdges
            {(deletedEdgeOfInternal graphData data removed).1}).Reachable
          (deletedDartOfInternal graphData data removed).fst
          (data.retainedPort 2))) := by
  have hzero := deletedBridgeComponent_sameSide_reductionSeamPorts
    graphData data hretained SquareReductionSide.join12_30 removed
      hnotReduction (0 : Fin 2)
  have hone := deletedBridgeComponent_sameSide_reductionSeamPorts
    graphData data hretained SquareReductionSide.join12_30 removed
      hnotReduction (1 : Fin 2)
  constructor
  · simpa [SquareReductionSide.leftPort, SquareReductionSide.rightPort,
      SquareReductionSide.join01_23,
      SquareReductionSide.join12_30] using hzero
  · simpa [SquareReductionSide.leftPort, SquareReductionSide.rightPort,
      SquareReductionSide.join01_23,
      SquareReductionSide.join12_30] using hone

/-- The left orientation of either inserted square seam is never a bridge
when the retained adjacent-pair deletion is connected. -/
theorem reductionLeftSeamDart_reachable_without_edge
    (graphData : Data G) (data : AdjacentPairData G)
    (hretained : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Connected)
    (side : SquareReductionSide) (step : Fin 2) :
    (edgeDeletedPrimalGraph (data.reductionRotationSystem graphData side)
      ((data.reductionRotationSystem graphData side).edgeOf
        (data.reductionLeftSeamDart graphData side step))).Reachable
      ((data.reductionRotationSystem graphData side).vertOf
        (data.reductionLeftSeamDart graphData side step))
      ((data.reductionRotationSystem graphData side).vertOf
        ((data.reductionRotationSystem graphData side).alpha
          (data.reductionLeftSeamDart graphData side step))) := by
  rw [data.reductionRotationSystem_edgeOf_leftSeamDart,
    data.reductionRotationSystem_vertOf_leftSeamDart,
    data.reductionRotationSystem_alpha_leftSeamDart,
    data.reductionRotationSystem_vertOf_rightSeamDart]
  exact data.reductionSeamEndpoints_reachable_without_seam
    graphData hretained side step

/-- The right orientation of either inserted square seam is never a bridge
when the retained adjacent-pair deletion is connected. -/
theorem reductionRightSeamDart_reachable_without_edge
    (graphData : Data G) (data : AdjacentPairData G)
    (hretained : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Connected)
    (side : SquareReductionSide) (step : Fin 2) :
    (edgeDeletedPrimalGraph (data.reductionRotationSystem graphData side)
      ((data.reductionRotationSystem graphData side).edgeOf
        (data.reductionRightSeamDart graphData side step))).Reachable
      ((data.reductionRotationSystem graphData side).vertOf
        (data.reductionRightSeamDart graphData side step))
      ((data.reductionRotationSystem graphData side).vertOf
        ((data.reductionRotationSystem graphData side).alpha
          (data.reductionRightSeamDart graphData side step))) := by
  rw [data.reductionRotationSystem_edgeOf_rightSeamDart,
    data.reductionRotationSystem_vertOf_rightSeamDart,
    data.reductionRotationSystem_alpha_rightSeamDart,
    data.reductionRotationSystem_vertOf_leftSeamDart]
  exact (data.reductionSeamEndpoints_reachable_without_seam
    graphData hretained side step).symm

/-- Once the retained deletion is connected, bridge-freedom of either
square reduction is equivalent to avoiding every old retained edge.  The
two newly inserted seams contribute no bridge cases. -/
theorem reduction_edgeBridgeFree_iff_forall_internalDart_reachable
    (graphData : Data G) (data : AdjacentPairData G)
    (hretained : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Connected)
    (side : SquareReductionSide) :
    EdgeBridgeFree (data.reductionRotationSystem graphData side) ↔
      ∀ internal : InternalDart (data.rootedRotationSystem graphData)
          (deletedRegionKeep data.deletedVertices),
        (edgeDeletedPrimalGraph
          (data.reductionRotationSystem graphData side)
          ((data.reductionRotationSystem graphData side).edgeOf
            (Sum.inl internal))).Reachable
          ((data.reductionRotationSystem graphData side).vertOf
            (Sum.inl internal))
          ((data.reductionRotationSystem graphData side).vertOf
            ((data.reductionRotationSystem graphData side).alpha
              (Sum.inl internal))) := by
  constructor
  · intro hfree internal
    exact hfree (Sum.inl internal)
  · intro hinternal dart
    rcases dart with internal | boundary
    · exact hinternal internal
    · rcases boundary with left | right
      · rcases orderedBoundaryDart_surjective
          (data.rootedRotationSystem graphData)
          (deletedRegionKeep data.deletedVertices)
          (data.leftCrossing side) (data.leftCrosses graphData side) left with
          ⟨step, rfl⟩
        exact reductionLeftSeamDart_reachable_without_edge
          graphData data hretained side step
      · rcases orderedBoundaryDart_surjective
          (data.rootedRotationSystem graphData)
          (deletedRegionKeep data.deletedVertices)
          (data.rightCrossing side) (data.rightCrosses graphData side) right with
          ⟨step, rfl⟩
        exact reductionRightSeamDart_reachable_without_edge
          graphData data hretained side step

/-- A non-bridge-free square reduction of a vertex-minimal counterexample
therefore has a concrete old retained dart whose endpoints are separated by
deleting its output edge. -/
theorem exists_internalDart_not_reachable_of_reduction_not_edgeBridgeFree
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) (side : SquareReductionSide)
    (hnot : ¬ EdgeBridgeFree
      (data.reductionRotationSystem graphData side)) :
    ∃ internal : InternalDart (data.rootedRotationSystem graphData)
        (deletedRegionKeep data.deletedVertices),
      ¬ (edgeDeletedPrimalGraph
          (data.reductionRotationSystem graphData side)
          ((data.reductionRotationSystem graphData side).edgeOf
            (Sum.inl internal))).Reachable
          ((data.reductionRotationSystem graphData side).vertOf
            (Sum.inl internal))
          ((data.reductionRotationSystem graphData side).vertOf
            ((data.reductionRotationSystem graphData side).alpha
              (Sum.inl internal))) := by
  have hretained :
      (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Connected :=
    retainedRegion_connected_of_vertexMinimalTaitCounterexample
      graphData minimal data
  have hnotInternal : ¬ ∀ internal :
      InternalDart (data.rootedRotationSystem graphData)
        (deletedRegionKeep data.deletedVertices),
      (edgeDeletedPrimalGraph
        (data.reductionRotationSystem graphData side)
        ((data.reductionRotationSystem graphData side).edgeOf
          (Sum.inl internal))).Reachable
        ((data.reductionRotationSystem graphData side).vertOf
          (Sum.inl internal))
        ((data.reductionRotationSystem graphData side).vertOf
          ((data.reductionRotationSystem graphData side).alpha
            (Sum.inl internal))) := by
    intro hinternal
    exact hnot
      ((reduction_edgeBridgeFree_iff_forall_internalDart_reachable
        graphData data hretained side).2 hinternal)
  simpa only [not_forall] using hnotInternal

/-- The retained dart witnessing a bridge in a square reduction is already
a bridge witness in the induced adjacent-pair deletion.  Adding seams can
only create paths; it cannot destroy an old retained path. -/
theorem exists_internalDart_reductionBridge_and_deletedBridge
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) (side : SquareReductionSide)
    (hnot : ¬ EdgeBridgeFree
      (data.reductionRotationSystem graphData side)) :
    ∃ internal : InternalDart (data.rootedRotationSystem graphData)
        (deletedRegionKeep data.deletedVertices),
      (¬ (edgeDeletedPrimalGraph
          (data.reductionRotationSystem graphData side)
          ((data.reductionRotationSystem graphData side).edgeOf
            (Sum.inl internal))).Reachable
          ((data.reductionRotationSystem graphData side).vertOf
            (Sum.inl internal))
          ((data.reductionRotationSystem graphData side).vertOf
            ((data.reductionRotationSystem graphData side).alpha
              (Sum.inl internal)))) ∧
        ¬ ((DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).deleteEdges
              {(deletedEdgeOfInternal graphData data internal).1}).Reachable
            (deletedDartOfInternal graphData data internal).fst
            (deletedDartOfInternal graphData data internal).snd := by
  rcases exists_internalDart_not_reachable_of_reduction_not_edgeBridgeFree
      graphData minimal data side hnot with ⟨internal, hnotReduction⟩
  refine ⟨internal, hnotReduction, ?_⟩
  intro hretained
  apply hnotReduction
  have hmapped := deletedEdgeReachable_mapsTo_reductionEdgeDeletedReachable
    graphData data side internal hretained
  rw [← reductionVertex_deletedDartOfInternal_fst
      graphData data side internal,
    ← reductionVertex_deletedDartOfInternal_snd
      graphData data side internal]
  exact hmapped

/-- In particular, every bridge obstruction in the alternate square
pairing is represented by a concrete old bridge of the retained deletion. -/
theorem exists_internalDart_join12_30_reductionBridge_and_deletedBridge
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (hnot : ¬ EdgeBridgeFree
      (data.reductionRotationSystem graphData
        SquareReductionSide.join12_30)) :
    ∃ internal : InternalDart (data.rootedRotationSystem graphData)
        (deletedRegionKeep data.deletedVertices),
      (¬ (edgeDeletedPrimalGraph
          (data.reductionRotationSystem graphData
            SquareReductionSide.join12_30)
          ((data.reductionRotationSystem graphData
            SquareReductionSide.join12_30).edgeOf
              (Sum.inl internal))).Reachable
          ((data.reductionRotationSystem graphData
            SquareReductionSide.join12_30).vertOf
              (Sum.inl internal))
          ((data.reductionRotationSystem graphData
            SquareReductionSide.join12_30).vertOf
              ((data.reductionRotationSystem graphData
                SquareReductionSide.join12_30).alpha
                  (Sum.inl internal)))) ∧
        ¬ ((DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).deleteEdges
              {(deletedEdgeOfInternal graphData data internal).1}).Reachable
            (deletedDartOfInternal graphData data internal).fst
            (deletedDartOfInternal graphData data internal).snd :=
  exists_internalDart_reductionBridge_and_deletedBridge
    graphData minimal data SquareReductionSide.join12_30 hnot

/-- Concrete retained-edge witness carried by a bridge obstruction in the
alternate square reduction.  Besides separation in both graphs, it records
the forced port-component equalities `0 ~ 3` and `1 ~ 2`. -/
structure Join12_30InternalBridgeWitness
    (graphData : Data G) (data : AdjacentPairData G) where
  internal : InternalDart (data.rootedRotationSystem graphData)
    (deletedRegionKeep data.deletedVertices)
  reductionSeparated : ¬
    (edgeDeletedPrimalGraph
      (data.reductionRotationSystem graphData
        SquareReductionSide.join12_30)
      ((data.reductionRotationSystem graphData
        SquareReductionSide.join12_30).edgeOf
          (Sum.inl internal))).Reachable
      ((data.reductionRotationSystem graphData
        SquareReductionSide.join12_30).vertOf
          (Sum.inl internal))
      ((data.reductionRotationSystem graphData
        SquareReductionSide.join12_30).vertOf
          ((data.reductionRotationSystem graphData
            SquareReductionSide.join12_30).alpha
              (Sum.inl internal)))
  retainedSeparated : ¬
    ((DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).deleteEdges
          {(deletedEdgeOfInternal graphData data internal).1}).Reachable
      (deletedDartOfInternal graphData data internal).fst
      (deletedDartOfInternal graphData data internal).snd
  pair03_sameComponent :
    (((DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).deleteEdges
          {(deletedEdgeOfInternal graphData data internal).1}).Reachable
      (deletedDartOfInternal graphData data internal).fst
      (data.retainedPort 0) ↔
    ((DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).deleteEdges
          {(deletedEdgeOfInternal graphData data internal).1}).Reachable
      (deletedDartOfInternal graphData data internal).fst
      (data.retainedPort 3))
  pair12_sameComponent :
    (((DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).deleteEdges
          {(deletedEdgeOfInternal graphData data internal).1}).Reachable
      (deletedDartOfInternal graphData data internal).fst
      (data.retainedPort 1) ↔
    ((DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).deleteEdges
          {(deletedEdgeOfInternal graphData data internal).1}).Reachable
      (deletedDartOfInternal graphData data internal).fst
      (data.retainedPort 2))

/-- Every alternate reduction bridge obstruction in a vertex-minimal
counterexample supplies the preceding concrete retained-edge witness. -/
theorem nonempty_join12_30InternalBridgeWitness_of_not_edgeBridgeFree
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (hnot : ¬ EdgeBridgeFree
      (data.reductionRotationSystem graphData
        SquareReductionSide.join12_30)) :
    Nonempty (Join12_30InternalBridgeWitness graphData data) := by
  rcases
      exists_internalDart_join12_30_reductionBridge_and_deletedBridge
        graphData minimal data hnot with
    ⟨internal, hnotReduction, hnotRetained⟩
  have hretained :
      (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Connected :=
    retainedRegion_connected_of_vertexMinimalTaitCounterexample
      graphData minimal data
  rcases deletedBridgeComponent_join12_30_pairs graphData data hretained
      internal hnotReduction with ⟨hpair03, hpair12⟩
  exact ⟨{
    internal := internal
    reductionSeparated := hnotReduction
    retainedSeparated := hnotRetained
    pair03_sameComponent := hpair03
    pair12_sameComponent := hpair12 }⟩

/-- The alternate square branch is now a concrete dichotomy: an old retained
bridge whose seams preserve the pairs `03` and `12`, or an honest all-equal
Tait coloring of the deleted four-pole. -/
theorem nonempty_join12_30InternalBridgeWitness_or_exists_deletedColoring_allEqual_of_order
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData) :
    Nonempty (Join12_30InternalBridgeWitness graphData data) ∨
      ∃ deletedColoring :
          (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
            (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
            deletedColoring ∧
          SquareBoundaryWord.AllEqual
            (data.degreeTwoBoundaryData.colorWord deletedColoring) := by
  rcases
      reductionJoin12_30_not_edgeBridgeFree_or_exists_deletedColoring_allEqual_of_order
        graphData minimal data horder with hbridge | hallEqual
  · exact Or.inl
      (nonempty_join12_30InternalBridgeWitness_of_not_edgeBridgeFree
        graphData minimal data hbridge)
  · exact Or.inr hallEqual

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
