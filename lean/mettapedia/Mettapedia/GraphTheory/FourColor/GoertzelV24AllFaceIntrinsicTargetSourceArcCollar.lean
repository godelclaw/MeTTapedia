import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortReentry
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceRemoteCycleSourceArcEmbedding

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24RecoveredAdjacentPairData
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

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- A short intrinsic restart edge together with two distinct physical
source arcs whose selected faces both contain that edge. -/
structure IntrinsicTargetSourceArcCollar
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (targetEdge : G.edgeSet) where
  leftStep : Fin cycle.walk.length
  rightStep : Fin cycle.walk.length
  leftStep_ne_rightStep : leftStep ≠ rightStep
  target_mem_leftSourceFace : targetEdge ∈ orbitFaceBoundary
    graphData.toRotationSystem
      (rebaseCircuit.arcAt
        (cycle.sourcePosition leftStep)).selectedFace
  target_mem_rightSourceFace : targetEdge ∈ orbitFaceBoundary
    graphData.toRotationSystem
      (rebaseCircuit.arcAt
        (cycle.sourcePosition rightStep)).selectedFace

/-- A crossed edge of the remote cycle has its two consecutive cycle
faces as a source-arc collar. -/
theorem nonempty_intrinsicTargetSourceArcCollar_of_mem_crossingEdges
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {targetEdge : G.edgeSet}
    (htarget : targetEdge ∈ cycle.crossingEdges) :
    Nonempty (cycle.IntrinsicTargetSourceArcCollar targetEdge) := by
  rcases (mem_dualWalkCrossingEdges_iff
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      cycle.walk targetEdge).1 htarget with ⟨step, hstep⟩
  let next := finRotate cycle.walk.length step
  have hcrossing : cycle.crossingAt step = targetEdge := by
    simpa [crossingAt] using hstep
  refine ⟨{
    leftStep := step
    rightStep := next
    leftStep_ne_rightStep := ?_
    target_mem_leftSourceFace := ?_
    target_mem_rightSourceFace := ?_ }⟩
  · intro heq
    apply cycle.sourcePosition_finRotate_ne step
    change cycle.sourcePosition next = cycle.sourcePosition step
    rw [← heq]
  · rw [← hcrossing]
    exact cycle.crossingAt_mem_sourceFace step
  · rw [← hcrossing]
    exact cycle.crossingAt_mem_successorSourceFace step

/-- The two chord faces of an adjacent-pair profile give a source-arc
collar for its internal edge. -/
def AdjacentPairPrimalCutProfile.intrinsicEdgeSourceArcCollar
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    (profile : cycle.AdjacentPairPrimalCutProfile) :
    cycle.IntrinsicTargetSourceArcCollar profile.internalEdge := by
  let leftWitness :=
    GoertzelV24DualCycleChord.exists_fin_getVert_eq_of_mem_support_of_isCycle
      cycle.isCycle profile.leftFace_mem_support
  let rightWitness :=
    GoertzelV24DualCycleChord.exists_fin_getVert_eq_of_mem_support_of_isCycle
      cycle.isCycle profile.rightFace_mem_support
  let leftStep := Classical.choose leftWitness
  let rightStep := Classical.choose rightWitness
  have hleft : cycle.walk.getVert leftStep = profile.leftFace :=
    Classical.choose_spec leftWitness
  have hright : cycle.walk.getVert rightStep = profile.rightFace :=
    Classical.choose_spec rightWitness
  have hleftSourceFace :
      (rebaseCircuit.arcAt
          (cycle.sourcePosition leftStep)).selectedFace =
        profile.leftFace.1 := by
    have hanchor :
        (rebaseCircuit.arcAt
            (cycle.sourcePosition leftStep)).selectedFace =
          (cycle.walk.getVert leftStep).1 := by
      simpa [CrossCentralExactFaceCertifiedRebaseArc.dualFace] using
        congrArg Subtype.val
          (cycle.arcAt_sourcePosition_dualFace leftStep)
    exact hanchor.trans (congrArg Subtype.val hleft)
  have hrightSourceFace :
      (rebaseCircuit.arcAt
          (cycle.sourcePosition rightStep)).selectedFace =
        profile.rightFace.1 := by
    have hanchor :
        (rebaseCircuit.arcAt
            (cycle.sourcePosition rightStep)).selectedFace =
          (cycle.walk.getVert rightStep).1 := by
      simpa [CrossCentralExactFaceCertifiedRebaseArc.dualFace] using
        congrArg Subtype.val
          (cycle.arcAt_sourcePosition_dualFace rightStep)
    exact hanchor.trans (congrArg Subtype.val hright)
  exact {
    leftStep := leftStep
    rightStep := rightStep
    leftStep_ne_rightStep := by
      intro heq
      apply profile.leftFace_ne_rightFace
      calc
        profile.leftFace = cycle.walk.getVert leftStep := hleft.symm
        _ = cycle.walk.getVert rightStep := by rw [heq]
        _ = profile.rightFace := hright
    target_mem_leftSourceFace := by
      rw [hleftSourceFace]
      exact profile.internalEdge_mem_leftFace
    target_mem_rightSourceFace := by
      rw [hrightSourceFace]
      exact profile.internalEdge_mem_rightFace }

/-- Every intrinsic singleton-star restart edge carries a two-anchor
source collar on consecutive faces of its remote triangle. -/
theorem IntrinsicShortFusionTarget.nonempty_sourceArcCollar
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (target : cycle.IntrinsicShortFusionTarget targetEdge) :
    Nonempty (cycle.IntrinsicTargetSourceArcCollar targetEdge) := by
  rcases target with
    ⟨_first, _second, _hne, _hadj, _hvalue, _hcentral, _hboundary,
      _hkempe, _hsingleton, hcrossing⟩
  exact cycle.nonempty_intrinsicTargetSourceArcCollar_of_mem_crossingEdges
    hcrossing

/-- The two collar anchors occupy distinct physical source positions. -/
theorem IntrinsicTargetSourceArcCollar.leftPosition_ne_rightPosition
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicTargetSourceArcCollar targetEdge) :
    cycle.sourcePosition collar.leftStep ≠
      cycle.sourcePosition collar.rightStep := by
  intro hposition
  exact collar.leftStep_ne_rightStep
    (cycle.sourcePosition_injective hposition)

/-- The source circuit normalized at the left incident face. -/
def IntrinsicTargetSourceArcCollar.leftCircuit
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicTargetSourceArcCollar targetEdge) :
    CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal
      baseData :=
  cycle.rotateAtSourcePosition collar.leftStep

/-- The source circuit normalized at the right incident face. -/
def IntrinsicTargetSourceArcCollar.rightCircuit
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicTargetSourceArcCollar targetEdge) :
    CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal
      baseData :=
  cycle.rotateAtSourcePosition collar.rightStep

/-- The target edge lies on the first selected face of the left-normalized
source circuit. -/
theorem IntrinsicTargetSourceArcCollar.target_mem_leftCircuit_firstFace
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicTargetSourceArcCollar targetEdge) :
    targetEdge ∈ orbitFaceBoundary graphData.toRotationSystem
      collar.leftCircuit.first.selectedFace := by
  rw [IntrinsicTargetSourceArcCollar.leftCircuit,
    cycle.rotateAtSourcePosition_first]
  exact collar.target_mem_leftSourceFace

/-- The target edge lies on the first selected face of the right-normalized
source circuit. -/
theorem IntrinsicTargetSourceArcCollar.target_mem_rightCircuit_firstFace
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicTargetSourceArcCollar targetEdge) :
    targetEdge ∈ orbitFaceBoundary graphData.toRotationSystem
      collar.rightCircuit.first.selectedFace := by
  rw [IntrinsicTargetSourceArcCollar.rightCircuit,
    cycle.rotateAtSourcePosition_first]
  exact collar.target_mem_rightSourceFace

/-- Both normalized source circuits retain the original certified arc
count. -/
theorem IntrinsicTargetSourceArcCollar.normalized_arcLengths
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicTargetSourceArcCollar targetEdge) :
    collar.leftCircuit.arcLength = rebaseCircuit.arcLength ∧
      collar.rightCircuit.arcLength = rebaseCircuit.arcLength := by
  constructor
  · exact cycle.rotateAtSourcePosition_arcLength collar.leftStep
  · exact cycle.rotateAtSourcePosition_arcLength collar.rightStep

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
