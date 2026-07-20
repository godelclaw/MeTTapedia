import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionClosedTurn

/-! Every closed complementary support route exposes a second signed turn. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]

omit [DecidableEq W] [DecidableRel H.Adj] in
/-- In a finite graph of maximum degree two, a simple cycle exhausts the
connected component of its root. -/
theorem isCycle_toSubgraph_verts_eq_connectedComponentSupp_of_degree_le_two
    {start : W} {cycle : H.Walk start start}
    (hcycle : cycle.IsCycle)
    (hdegree : ∀ vertex : W, H.degree vertex ≤ 2) :
    cycle.toSubgraph.verts = (H.connectedComponentMk start).supp := by
  classical
  have hclosed : ∀ vertex ∈ cycle.toSubgraph.verts, ∀ neighbor,
      H.Adj vertex neighbor → cycle.toSubgraph.Adj vertex neighbor := by
    intro vertex hvertex neighbor hadjacent
    have hsubset : cycle.toSubgraph.neighborSet vertex ⊆
        H.neighborSet vertex :=
      cycle.toSubgraph.neighborSet_subset vertex
    have hcycleCard :
        (cycle.toSubgraph.neighborSet vertex).ncard = 2 :=
      hcycle.ncard_neighborSet_toSubgraph_eq_two
        (cycle.mem_verts_toSubgraph.mp hvertex)
    have hambientCard : (H.neighborSet vertex).ncard ≤ 2 := by
      rw [neighborSet_ncard_eq_degree]
      exact hdegree vertex
    have hneighborEq : cycle.toSubgraph.neighborSet vertex =
        H.neighborSet vertex := by
      apply Set.eq_of_subset_of_ncard_le hsubset
      omega
    change neighbor ∈ cycle.toSubgraph.neighborSet vertex
    rw [hneighborEq]
    exact hadjacent
  rcases cycle.toSubgraph_connected.exists_verts_eq_connectedComponentSupp
      hclosed with ⟨component, hcomponent⟩
  have hstartCycle : start ∈ cycle.toSubgraph.verts := by
    exact cycle.start_mem_verts_toSubgraph
  have hstartComponent : start ∈ component.supp := by
    rw [← hcomponent]
    exact hstartCycle
  have hcomponentEq : component = H.connectedComponentMk start := by
    exact ((component.mem_supp_iff start).1
      hstartComponent).symm
  rw [hcomponentEq] at hcomponent
  exact hcomponent

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

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

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}
  {firstHit : FirstHitSingletonCompanionTransferPath
    (collar := collar) (sourceEscape := sourceEscape)}
  {change : firstHit.TransverseCompanionChange}

namespace FirstHitSingletonCompanionTransferPath.TransverseCompanionChange.ComplementarySupportCorner

namespace FirstTerminalSupportStrand.ClosedContinuationCycle

variable {corner : change.ComplementarySupportCorner}
  {strand : corner.FirstTerminalSupportStrand}
  {continuation : strand.TerminalContinuation}
  (closed : strand.ClosedContinuationCycle continuation)

/-- A cycle reached after a degree-two terminal passage lies in the same
maximum-degree-two component as the signed launch and can be rerooted there. -/
noncomputable def toClosedSupportStrand : corner.ClosedSupportStrand := by
  let supportGraph := corner.complementarySupportGraph
  have hdegree : ∀ vertex : collar.commonCoreVertex,
      supportGraph.degree vertex ≤ 2 := by
    intro vertex
    rw [← incidentEdgeFinset_card_eq_degree]
    exact taitDiscrepancySupport_incidentCard_le_two
      (collar.sourceCommonColoring sourceEscape)
      collar.targetCommonColoring
      (collar.sourceCommonColoring_isTait sourceEscape)
      collar.targetCommonColoring_isTait
      (!firstHit.transfer.coordinate) vertex
      (collar.commonCore_incidentEdgeFinset_card_le_three vertex)
  have hcycleComponent : closed.supportCycle.toSubgraph.verts =
      (supportGraph.connectedComponentMk strand.finish.1).supp :=
    isCycle_toSubgraph_verts_eq_connectedComponentSupp_of_degree_le_two
      closed.supportCycle_isCycle hdegree
  have hjunctionComponent : corner.complementarySupportJunction ∈
      (supportGraph.connectedComponentMk strand.finish.1).supp := by
    rw [(supportGraph.connectedComponentMk strand.finish.1).mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.sound strand.path.reachable
  have hjunctionVerts : corner.complementarySupportJunction ∈
      closed.supportCycle.toSubgraph.verts := by
    rw [hcycleComponent]
    exact hjunctionComponent
  have hjunctionSupport : corner.complementarySupportJunction ∈
      closed.supportCycle.support := by
    exact closed.supportCycle.mem_verts_toSubgraph.mp hjunctionVerts
  let launchCycle := closed.supportCycle.rotate
    corner.complementarySupportJunction hjunctionSupport
  have hlaunchCycle : launchCycle.IsCycle :=
    closed.supportCycle_isCycle.rotate hjunctionSupport
  have hjunctionDegree : supportGraph.degree
      corner.complementarySupportJunction = 2 := by
    rw [← incidentEdgeFinset_card_eq_degree]
    exact corner.supportJunction_degree_eq_two
  refine {
    cycle := launchCycle
    cycle_isCycle := hlaunchCycle
    incoming_mem := ?_
    transverse_mem := ?_ }
  · apply edge_mem_rooted_isCycle_of_degree_eq_two
      hlaunchCycle hjunctionDegree corner.incomingSupportEdge
    exact SimpleGraph.lineGraphCommonVertex_mem_left
      corner.incoming_transverse_adj
  · apply edge_mem_rooted_isCycle_of_degree_eq_two
      hlaunchCycle hjunctionDegree (transverseSupportEdge change)
    exact SimpleGraph.lineGraphCommonVertex_mem_right
      corner.incoming_transverse_adj

end FirstTerminalSupportStrand.ClosedContinuationCycle

namespace ClosedSupportRoute

variable {corner : change.ComplementarySupportCorner}

/-- Both constructors of a closed route canonically reduce to a cycle rooted
at the original signed launch. -/
noncomputable def rootedAtLaunch
    (route : corner.ClosedSupportRoute) : corner.ClosedSupportStrand :=
  match route with
  | .direct strand => strand
  | .continued _strand _continuation closed => closed.toClosedSupportStrand

/-- Direct and continued closed routes both force a second signed turn,
resolved as a collar port or an interior transverse emission. -/
theorem exists_internal_boundaryPort_or_transverseEmission
    (route : corner.ClosedSupportRoute) :
    ∃ (before : List corner.complementarySupportGraph.edgeSet)
        (first second : corner.complementarySupportGraph.edgeSet)
        (after : List corner.complementarySupportGraph.edgeSet)
        (hadjacent : corner.complementarySupportGraph.lineGraph.Adj
          first second),
      route.rootedAtLaunch.cycle.edgeSubtypeSupport =
          before ++ first :: second :: after ∧
        (corner.supportEdgeColorState first).companionColor ≠
          (corner.supportEdgeColorState second).companionColor ∧
        ((∃ sourcePort : Fin 4,
            SimpleGraph.lineGraphCommonVertex
                (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
              collar.sourcePortInCommonCore sourcePort) ∨
          (∃ targetPort : Fin 4,
            SimpleGraph.lineGraphCommonVertex
                (corner.supportEdgeAmbientEdge_lineGraph_adj hadjacent) =
              collar.targetPortInCommonCore targetPort) ∨
          ∃ thirdEdge : collar.commonCore.edgeSet,
            collar.commonCore.lineGraph.Adj
                (corner.supportEdgeAmbientEdge first) thirdEdge ∧
              collar.commonCore.lineGraph.Adj
                (corner.supportEdgeAmbientEdge second) thirdEdge ∧
              collar.sourceCommonColoring sourceEscape thirdEdge +
                  collar.targetCommonColoring thirdEdge =
                crossFaceZeroColor (!firstHit.transfer.coordinate) ∧
              crossFaceCoordinate firstHit.transfer.coordinate
                (collar.sourceCommonColoring sourceEscape thirdEdge +
                  collar.targetCommonColoring thirdEdge) ≠ 0) := by
  exact route.rootedAtLaunch.exists_internal_boundaryPort_or_transverseEmission

end ClosedSupportRoute
end FirstHitSingletonCompanionTransferPath.TransverseCompanionChange.ComplementarySupportCorner
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
