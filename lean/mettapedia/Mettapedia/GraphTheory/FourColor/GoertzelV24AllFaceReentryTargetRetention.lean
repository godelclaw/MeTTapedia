import Mettapedia.GraphTheory.EdgeColoringEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceNormalReentry

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- The common induced graph left after deleting two ordered vertex pairs. -/
abbrev DeletedTwoPairsGraph
    (G : SimpleGraph V) (first second third fourth : V) :
    SimpleGraph {vertex : V |
      vertex ≠ first ∧ vertex ≠ second ∧
        vertex ≠ third ∧ vertex ≠ fourth} :=
  G.induce {vertex |
    vertex ≠ first ∧ vertex ≠ second ∧
      vertex ≠ third ∧ vertex ≠ fourth}

/-- The common four-vertex deletion embeds into the deletion of its first
ordered pair. -/
def deletedTwoPairsToFirstDeletionEmbedding
    (G : SimpleGraph V) (first second third fourth : V) :
    DeletedTwoPairsGraph G first second third fourth ↪g
      DeletedAdjacentPairGraph G first second where
  toFun vertex := ⟨vertex.1, vertex.2.1, vertex.2.2.1⟩
  inj' left right heq := by
    apply Subtype.ext
    exact congrArg
      (fun vertex : retainedVertexSet first second => vertex.1) heq
  map_rel_iff' := Iff.rfl

/-- The same common deletion embeds into the deletion of its second
ordered pair. -/
def deletedTwoPairsToSecondDeletionEmbedding
    (G : SimpleGraph V) (first second third fourth : V) :
    DeletedTwoPairsGraph G first second third fourth ↪g
      DeletedAdjacentPairGraph G third fourth where
  toFun vertex := ⟨vertex.1, vertex.2.2.2.1, vertex.2.2.2.2⟩
  inj' left right heq := by
    apply Subtype.ext
    exact congrArg
      (fun vertex : retainedVertexSet third fourth => vertex.1) heq
  map_rel_iff' := Iff.rfl

/-- Restrict a coloring of the first adjacent-pair deletion to the common
four-vertex deleted graph. -/
def firstDeletionCommonCoreColoring
    {first second third fourth : V}
    (coloring :
      (DeletedAdjacentPairGraph G first second).EdgeColoring Color) :
    (DeletedTwoPairsGraph G first second third fourth).EdgeColoring Color :=
  coloring.pullbackEmbedding
    (deletedTwoPairsToFirstDeletionEmbedding G first second third fourth)

/-- Restrict a coloring of the second adjacent-pair deletion to the same
common four-vertex deleted graph. -/
def secondDeletionCommonCoreColoring
    {first second third fourth : V}
    (coloring :
      (DeletedAdjacentPairGraph G third fourth).EdgeColoring Color) :
    (DeletedTwoPairsGraph G first second third fourth).EdgeColoring Color :=
  coloring.pullbackEmbedding
    (deletedTwoPairsToSecondDeletionEmbedding G first second third fourth)

/-- The two actual Tait colorings attached to a recursive reentry, restricted
to their identical common four-vertex deleted graph.  No equality or Kempe
transport between the two restrictions is included. -/
structure RotationOrderedFusionReentryCommonCoreColorState
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source target : G.Dart) where
  sourceBase : AdjacentPairData G
  sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal sourceBase
  sourceLaunch : sourceNormal.CertifiedRebasePumpingLaunch
  sourceDart : centralDart
    (RecoveredRotationOrderedData graphData minimal
      sourceBase).centralAdjacent = source
  targetBase : AdjacentPairData G
  targetNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal targetBase
  targetOutcome : targetNormal.TerminalFusionOutcome ∨
    targetNormal.CertifiedRebasePumpingLaunch
  targetDart : centralDart
    (RecoveredRotationOrderedData graphData minimal
      targetBase).centralAdjacent = target
  targetFirstRetained :
    (RecoveredRotationOrderedData graphData minimal
        targetBase).firstVertex ∈
      retainedVertexSet
        (RecoveredRotationOrderedData graphData minimal
          sourceBase).firstVertex
        (RecoveredRotationOrderedData graphData minimal
          sourceBase).secondVertex
  targetSecondRetained :
    (RecoveredRotationOrderedData graphData minimal
        targetBase).secondVertex ∈
      retainedVertexSet
        (RecoveredRotationOrderedData graphData minimal
          sourceBase).firstVertex
        (RecoveredRotationOrderedData graphData minimal
          sourceBase).secondVertex
  sourceEscape : sourceNormal.KempeOrbitAdjacentEscape
  targetEscape : targetNormal.KempeOrbitAdjacentEscape

namespace RotationOrderedFusionReentryCommonCoreColorState

/-- The common graph on which the source and target escape colorings can be
compared without any change of carrier. -/
abbrev commonCore
    {source target : G.Dart}
    (state : RotationOrderedFusionReentryCommonCoreColorState
      graphData minimal source target) :=
  DeletedTwoPairsGraph G
    (RecoveredRotationOrderedData graphData minimal
      state.sourceBase).firstVertex
    (RecoveredRotationOrderedData graphData minimal
      state.sourceBase).secondVertex
    (RecoveredRotationOrderedData graphData minimal
      state.targetBase).firstVertex
    (RecoveredRotationOrderedData graphData minimal
      state.targetBase).secondVertex

/-- The source escape coloring restricted to the common core. -/
def sourceColoring
    {source target : G.Dart}
    (state : RotationOrderedFusionReentryCommonCoreColorState
      graphData minimal source target) :
    state.commonCore.EdgeColoring Color :=
  firstDeletionCommonCoreColoring state.sourceEscape.coloring

/-- The target escape coloring restricted to the same common core. -/
def targetColoring
    {source target : G.Dart}
    (state : RotationOrderedFusionReentryCommonCoreColorState
      graphData minimal source target) :
    state.commonCore.EdgeColoring Color :=
  secondDeletionCommonCoreColoring state.targetEscape.coloring

end RotationOrderedFusionReentryCommonCoreColorState

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Avoiding the central edge and all four boundary edges is the intrinsic
edge-level characterization needed to regard an ambient edge as retained. -/
theorem isRetainedAmbientEdge_of_ne_central_boundary
    (data : AdjacentPairData G) (edge : G.edgeSet)
    (hcentral : centralEdge data ≠ edge)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ≠ edge) :
    IsRetainedAmbientEdge data edge := by
  apply isRetainedAmbientEdge_of_ne data edge
  · intro hedge
    apply hcentral
    exact Subtype.ext hedge.symm
  · intro hedge
    apply hboundary 0
    exact Subtype.ext hedge.symm
  · intro hedge
    apply hboundary 1
    exact Subtype.ext hedge.symm
  · intro hedge
    apply hboundary 2
    exact Subtype.ext hedge.symm
  · intro hedge
    apply hboundary 3
    exact Subtype.ext hedge.symm

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Every intrinsic singleton-triangle target is an actual edge of the
source adjacent-pair deletion. -/
theorem IntrinsicShortFusionTarget.isRetainedAmbientEdge
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (target : cycle.IntrinsicShortFusionTarget targetEdge) :
    IsRetainedAmbientEdge
      (RecoveredRotationOrderedData graphData minimal baseData) targetEdge := by
  rcases target with
    ⟨_first, _second, _hne, _hadj, _hvalue, hcentral, hboundary,
      _hkempe, _hsingleton, _hcrossing⟩
  apply isRetainedAmbientEdge_of_ne_central_boundary
    (RecoveredRotationOrderedData graphData minimal baseData) targetEdge
      hcentral
  intro port
  simpa [RecoveredRotationOrderedData] using hboundary port

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

/-- A recovery gain edge lies on the selected face of its restoring arc;
that face excludes the source central and boundary edges, so the gain edge
is retained by the source deletion. -/
theorem ClosureRecoveryFaceTransfer.recoveryEdge_isRetainedAmbientEdge
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    (transfer : ClosureRecoveryFaceTransfer rebaseCircuit) :
    IsRetainedAmbientEdge
      (RecoveredRotationOrderedData graphData minimal baseData)
      transfer.recovery.edge := by
  have hedgeFace : transfer.recovery.edge ∈
      orbitFaceBoundary graphData.toRotationSystem
        transfer.recovery.recoveryArc.selectedFace := by
    rw [transfer.recovery.recoveryArc_selectedFace]
    exact transfer.recovery.edge_mem_targetFace
  have hcentral :
      centralEdge
          (RecoveredRotationOrderedData graphData minimal baseData) ≠
        transfer.recovery.edge := by
    intro hedge
    exact transfer.recovery.recoveryArc.transition.central_not_mem_face
      (hedge ▸ hedgeFace)
  have hboundary : ∀ port : Fin 4,
      boundaryEdge
          (RecoveredRotationOrderedData graphData minimal baseData) port ≠
        transfer.recovery.edge := by
    intro port hedge
    exact transfer.recovery.recoveryArc.transition.boundary_not_mem_face port
      (hedge ▸ hedgeFace)
  exact isRetainedAmbientEdge_of_ne_central_boundary
    (RecoveredRotationOrderedData graphData minimal baseData)
      transfer.recovery.edge hcentral hboundary

/-- Both recursive geometries choose a target edge already present in the
source adjacent-pair deletion. -/
theorem IntrinsicShortOrRecoveryGeometry.isRetainedAmbientEdge
    {targetEdge : G.edgeSet}
    (geometry : IntrinsicShortOrRecoveryGeometry graphData minimal baseData
      targetEdge) :
    IsRetainedAmbientEdge
      (RecoveredRotationOrderedData graphData minimal baseData) targetEdge := by
  rcases geometry with
    ⟨_circuit, _hminimal, _cycle, target⟩ |
      ⟨_circuit, _hminimal, _rotated, _hlength, transfer, htarget⟩
  · exact target.isRetainedAmbientEdge
  · subst targetEdge
    exact transfer.recoveryEdge_isRetainedAmbientEdge

/-- Every recursive step supplies two genuine escape colorings on one
identical common induced graph: delete the source pair and the target pair.
This provides a common carrier for cross-base transport arguments. -/
theorem RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry.nonempty_commonCoreColorState
    {source target : G.Dart}
    (reentry : RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
      graphData minimal source target) :
    Nonempty (RotationOrderedFusionReentryCommonCoreColorState
      graphData minimal source target) := by
  rcases reentry with
    ⟨sourceBase, sourceNormal, hlaunch, targetEdge, hsource, _hne,
      hedge, hkempe, hgeometry⟩
  have hretained := hgeometry.isRetainedAmbientEdge
  have htargetFstRetained : target.fst ∈
      retainedVertexSet
        (RecoveredRotationOrderedData graphData minimal
          sourceBase).firstVertex
        (RecoveredRotationOrderedData graphData minimal
          sourceBase).secondVertex := by
    apply endpoints_mem_retainedVertexSet
      (RecoveredRotationOrderedData graphData minimal sourceBase)
        targetEdge hretained target.fst
    rw [hedge]
    change target.fst ∈ s(target.fst, target.snd)
    exact Sym2.mem_mk_left _ _
  have htargetSndRetained : target.snd ∈
      retainedVertexSet
        (RecoveredRotationOrderedData graphData minimal
          sourceBase).firstVertex
        (RecoveredRotationOrderedData graphData minimal
          sourceBase).secondVertex := by
    apply endpoints_mem_retainedVertexSet
      (RecoveredRotationOrderedData graphData minimal sourceBase)
        targetEdge hretained target.snd
    rw [hedge]
    change target.snd ∈ s(target.fst, target.snd)
    exact Sym2.mem_mk_right _ _
  rcases sourceNormal.nonempty_kempeOrbitAdjacentEscape with
    ⟨sourceEscape⟩
  rcases hkempe with
    ⟨targetBase, htargetFirst, htargetSecond, targetNormal,
      htargetOutcome, ⟨targetEscape⟩⟩
  have htargetFirst' :
      (RecoveredRotationOrderedData graphData minimal
        targetBase).firstVertex = target.fst := by
    simpa [RecoveredRotationOrderedData, rotationOrderedData] using
      htargetFirst
  have htargetSecond' :
      (RecoveredRotationOrderedData graphData minimal
        targetBase).secondVertex = target.snd := by
    simpa [RecoveredRotationOrderedData, rotationOrderedData] using
      htargetSecond
  have htargetDart : centralDart
      (RecoveredRotationOrderedData graphData minimal
        targetBase).centralAdjacent = target := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext htargetFirst' htargetSecond'
  exact ⟨{
    sourceBase := sourceBase
    sourceNormal := sourceNormal
    sourceLaunch := hlaunch
    sourceDart := hsource
    targetBase := targetBase
    targetNormal := targetNormal
    targetOutcome := htargetOutcome
    targetDart := htargetDart
    targetFirstRetained := htargetFirst'.symm ▸ htargetFstRetained
    targetSecondRetained := htargetSecond'.symm ▸ htargetSndRetained
    sourceEscape := sourceEscape
    targetEscape := targetEscape }⟩

/-- The oriented endpoints of every recursive target both survive the
source adjacent-pair deletion. -/
theorem RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry.exists_sourceBase_targetEndpointsRetained
    {source target : G.Dart}
    (reentry : RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
      graphData minimal source target) :
    ∃ sourceBase : AdjacentPairData G,
      centralDart
          (RecoveredRotationOrderedData graphData minimal
            sourceBase).centralAdjacent = source ∧
        target.fst ∈ retainedVertexSet
          (RecoveredRotationOrderedData graphData minimal
            sourceBase).firstVertex
          (RecoveredRotationOrderedData graphData minimal
            sourceBase).secondVertex ∧
        target.snd ∈ retainedVertexSet
          (RecoveredRotationOrderedData graphData minimal
            sourceBase).firstVertex
          (RecoveredRotationOrderedData graphData minimal
            sourceBase).secondVertex := by
  rcases reentry with
    ⟨sourceBase, _sourceNormal, _hlaunch, targetEdge, hsource, _hne,
      hedge, _hkempe, hgeometry⟩
  have hretained := hgeometry.isRetainedAmbientEdge
  refine ⟨sourceBase, hsource, ?_, ?_⟩
  · apply endpoints_mem_retainedVertexSet
      (RecoveredRotationOrderedData graphData minimal sourceBase)
        targetEdge hretained target.fst
    rw [hedge]
    change target.fst ∈ s(target.fst, target.snd)
    exact Sym2.mem_mk_left _ _
  · apply endpoints_mem_retainedVertexSet
      (RecoveredRotationOrderedData graphData minimal sourceBase)
        targetEdge hretained target.snd
    rw [hedge]
    change target.snd ∈ s(target.fst, target.snd)
    exact Sym2.mem_mk_right _ _

/-- A normal-retaining reentry therefore exposes its target as a concrete
retained edge on which the source normal's coloring is defined, while also
retaining the target's Kempe package. -/
theorem RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry.exists_sourceRetainedTargetEdge
    {source target : G.Dart}
    (reentry : RotationOrderedFusionNormalIntrinsicShortOrRecoveryDartReentry
      graphData minimal source target) :
    ∃ (sourceBase : AdjacentPairData G)
        (sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
          graphData minimal sourceBase)
        (targetInSource :
          (DeletedAdjacentPairGraph G
            (RecoveredRotationOrderedData graphData minimal
              sourceBase).firstVertex
            (RecoveredRotationOrderedData graphData minimal
              sourceBase).secondVertex).edgeSet),
      sourceNormal.CertifiedRebasePumpingLaunch ∧
        centralDart
            (RecoveredRotationOrderedData graphData minimal
              sourceBase).centralAdjacent = source ∧
        (retainedEdgeToAmbientEdge
            (RecoveredRotationOrderedData graphData minimal sourceBase)
            targetInSource).1 = target.edge ∧
        HasRotationOrderedFusionKempeOrbitEscape
          graphData minimal target.fst target.snd := by
  rcases reentry with
    ⟨sourceBase, sourceNormal, hlaunch, targetEdge, hsource, _hne,
      hedge, hkempe, hgeometry⟩
  have hretained := hgeometry.isRetainedAmbientEdge
  let targetInSource := ambientEdgeToRetainedEdge
    (RecoveredRotationOrderedData graphData minimal sourceBase)
      targetEdge hretained
  refine ⟨sourceBase, sourceNormal, targetInSource, hlaunch, hsource, ?_,
    hkempe⟩
  calc
    (retainedEdgeToAmbientEdge
        (RecoveredRotationOrderedData graphData minimal sourceBase)
        targetInSource).1 = targetEdge.1 := by
      rw [show retainedEdgeToAmbientEdge
          (RecoveredRotationOrderedData graphData minimal sourceBase)
          targetInSource = targetEdge by
        exact retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge
          (RecoveredRotationOrderedData graphData minimal sourceBase)
            targetEdge hretained]
    _ = target.edge := hedge

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
