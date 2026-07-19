import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceRemotePrimalCutProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutCollarChordCrossing

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

/-- The internal dual chord of an adjacent-pair remote four-cycle cuts
off a source-supported remote triangle.  Its chord crossing is the
internal edge of the adjacent pair. -/
theorem AdjacentPairPrimalCutProfile.exists_sourceSupportedTriangle
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    (profile : cycle.AdjacentPairPrimalCutProfile) :
    ∃ triangleCycle :
        CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
          rebaseCircuit,
      triangleCycle.walk.length = 3 ∧
        profile.internalEdge ∈ triangleCycle.crossingEdges := by
  have hchord : cycle.walk.IsChord
      s(profile.leftFace, profile.rightFace) :=
    GoertzelV24DualCycleCollar.isChord_of_shared_primal_edge_not_mem_crossings
      graphData (pairwiseUniqueSharedInteriorEdges graphData minimal)
        cycle.walk profile.leftFace_mem_support
          profile.rightFace_mem_support profile.leftFace_ne_rightFace
            profile.internalEdge_mem_leftFace
              profile.internalEdge_mem_rightFace
                profile.internalEdge_not_crossing
  rcases
      GoertzelV24DualCycleChord.exists_opposite_getVert_of_isCycle_of_length_eq_four_of_isChord
        cycle.isCycle profile.length_eq_four hchord with
    ⟨step, hleftPosition, hrightPosition⟩
  rcases (SimpleGraph.Walk.isChord_sym2Mk.1 hchord) with
    ⟨hleftRight, _hnotEdge, _hleftSupport, _hrightSupport⟩
  let next := finRotate cycle.walk.length step
  let opposite := finRotate cycle.walk.length next
  let middle := cycle.walk.getVert next.val
  have hrightAtOpposite : cycle.walk.getVert opposite.val =
      profile.rightFace := by
    simpa [opposite, next] using hrightPosition
  have hleftMiddle :
      (interiorDualGraph
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace graphData.toRotationSystem))).Adj
            profile.leftFace middle := by
    have hadj := cycle.walk.adj_getVert_succ step.isLt
    have hsuccessor :=
      GoertzelV24DualCycleChord.getVert_succ_eq_getVert_finRotate_of_isCycle
        cycle.isCycle step
    rw [hsuccessor] at hadj
    simpa [middle, next, hleftPosition] using hadj
  have hmiddleRight :
      (interiorDualGraph
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace graphData.toRotationSystem))).Adj
            middle profile.rightFace := by
    have hadj := cycle.walk.adj_getVert_succ next.isLt
    have hsuccessor :=
      GoertzelV24DualCycleChord.getVert_succ_eq_getVert_finRotate_of_isCycle
        cycle.isCycle next
    rw [hsuccessor] at hadj
    rw [hrightAtOpposite] at hadj
    simpa [middle, next, opposite] using hadj
  let triangle :
      (interiorDualGraph
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace graphData.toRotationSystem))).Walk
            profile.leftFace profile.leftFace :=
    .cons hleftMiddle
      (.cons hmiddleRight (.cons hleftRight.symm .nil))
  have htriangleCycle : triangle.IsCycle := by
    simp [triangle, SimpleGraph.Walk.isCycle_def,
      SimpleGraph.Walk.isTrail_def, hleftMiddle.ne,
      hleftMiddle.ne.symm, hmiddleRight.ne, hleftRight.ne,
      hleftRight.ne.symm]
  have htriangleLength : triangle.length = 3 := by
    simp [triangle]
  have htriangleSupport : ∀ face ∈ triangle.support,
      face ∈ cycle.walk.support := by
    intro face hface
    simp [triangle] at hface
    rcases hface with hface | hface | hface | hface
    · simpa [hface] using profile.leftFace_mem_support
    · subst face
      exact cycle.walk.getVert_mem_support next
    · simpa [hface] using profile.rightFace_mem_support
    · simpa [hface] using profile.leftFace_mem_support
  let triangleCycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit := {
    start := profile.leftFace
    walk := triangle
    isCycle := htriangleCycle
    support_mem_cyclicDualFaces := fun face hface =>
      cycle.support_mem_cyclicDualFaces face (htriangleSupport face hface)
    central_not_mem := fun face hface =>
      cycle.central_not_mem face (htriangleSupport face hface)
    boundary_not_mem := fun face hface port =>
      cycle.boundary_not_mem face (htriangleSupport face hface) port }
  have hinternalCrossing : profile.internalEdge ∈
      triangleCycle.crossingEdges := by
    apply
      GoertzelV24DualCycleCollar.mem_dualWalkCrossingEdges_of_shared_primal_edge_of_mem_walk_edges
        graphData (pairwiseUniqueSharedInteriorEdges graphData minimal)
          triangle profile.leftFace_ne_rightFace
            profile.internalEdge_mem_leftFace
              profile.internalEdge_mem_rightFace
    simp only [triangle, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_nil, List.mem_cons, List.not_mem_nil,
      or_false]
    show s(profile.leftFace, profile.rightFace) =
        s(profile.leftFace, middle) ∨
      s(profile.leftFace, profile.rightFace) =
          s(middle, profile.rightFace) ∨
        s(profile.leftFace, profile.rightFace) =
          s(profile.rightFace, profile.leftFace)
    exact Or.inr (Or.inr Sym2.eq_swap)
  exact ⟨triangleCycle, htriangleLength, hinternalCrossing⟩

/-- Thus every adjacent-pair short side refines to a singleton-star
remote triangle supported by the same physical rebase circuit. -/
theorem AdjacentPairPrimalCutProfile.exists_singletonTriangleRefinement
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    (profile : cycle.AdjacentPairPrimalCutProfile) :
    ∃ triangleCycle :
        CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
          rebaseCircuit,
      Nonempty triangleCycle.SingletonPrimalCutProfile ∧
        profile.internalEdge ∈ triangleCycle.crossingEdges := by
  rcases profile.exists_sourceSupportedTriangle with
    ⟨triangleCycle, hlength, hinternal⟩
  rcases triangleCycle.primalCutScopeProfile with
    hlong | hsingleton | hadjacent
  · have hge := hlong.length_ge_five
    rw [hlength] at hge
    omega
  · exact ⟨triangleCycle, ⟨hsingleton⟩, hinternal⟩
  · have heq := hadjacent.length_eq_four
    rw [hlength] at heq
    omega

/-- Every remote cycle is either already a long exact separator or has a
source-supported remote triangle cutting off a singleton component.  In
the adjacent-pair case the triangle is obtained by inserting the collar's
internal dual chord. -/
theorem exists_longPrimalCut_or_singletonTriangleRefinement
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) :
    Nonempty cycle.LongPrimalCutProfile ∨
      ∃ triangleCycle :
          CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
            rebaseCircuit,
        Nonempty triangleCycle.SingletonPrimalCutProfile := by
  cases cycle.primalCutScopeProfile with
  | long profile => exact Or.inl ⟨profile⟩
  | singleton profile => exact Or.inr ⟨cycle, ⟨profile⟩⟩
  | adjacentPair profile =>
      rcases profile.exists_singletonTriangleRefinement with
        ⟨triangleCycle, hsingleton, _hinternal⟩
      exact Or.inr ⟨triangleCycle, hsingleton⟩

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
