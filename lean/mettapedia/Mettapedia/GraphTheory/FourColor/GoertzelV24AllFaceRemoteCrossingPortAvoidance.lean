import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceReentryTargetRetention
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceCutTrailTransport

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24DualCycleCollar
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Two distinct edges incident to one vertex of a cyclic cubic rotation
system share a quotient face. -/
theorem exists_common_orbitFace_of_distinct_incident_edges
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    {first second : E} (hne : first ≠ second) {vertex : V}
    (hfirst : vertex ∈ RS.endpoints first)
    (hsecond : vertex ∈ RS.endpoints second) :
    ∃ face : OrbitFace RS,
      first ∈ orbitFaceBoundary RS face ∧
        second ∈ orbitFaceBoundary RS face := by
  rcases (RS.mem_endpoints_iff).1 hfirst with
    ⟨firstDart, hfirstOn, hfirstVertex⟩
  rcases (RS.mem_endpoints_iff).1 hsecond with
    ⟨secondDart, hsecondOn, hsecondVertex⟩
  have hfirstEdge : RS.edgeOf firstDart = first :=
    (RS.mem_dartsOn).1 hfirstOn
  have hsecondEdge : RS.edgeOf secondDart = second :=
    (RS.mem_dartsOn).1 hsecondOn
  have hdartsNe : firstDart ≠ secondDart := by
    intro hdarts
    apply hne
    calc
      first = RS.edgeOf firstDart := hfirstEdge.symm
      _ = RS.edgeOf secondDart := congrArg RS.edgeOf hdarts
      _ = second := hsecondEdge
  have hbase : RS.vertOf secondDart = RS.vertOf firstDart :=
    hsecondVertex.trans hfirstVertex.symm
  rcases RS.rho_eq_or_rho_eq_of_cubic hcubic hrotation hbase hdartsNe with
    hforward | hreverse
  · refine ⟨dartOrbitFace RS secondDart, ?_, ?_⟩
    · have hmem :=
        edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha firstDart)
      rw [RS.edge_alpha, hfirstEdge,
        dartOrbitFace_alpha_eq_dartOrbitFace_rho RS firstDart,
        hforward] at hmem
      exact hmem
    · rw [← hsecondEdge]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS secondDart
  · refine ⟨dartOrbitFace RS firstDart, ?_, ?_⟩
    · rw [← hfirstEdge]
      exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS firstDart
    · have hmem :=
        edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha secondDart)
      rw [RS.edge_alpha, hsecondEdge,
        dartOrbitFace_alpha_eq_dartOrbitFace_rho RS secondDart,
        hreverse] at hmem
      exact hmem

end RotationSystem

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

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

/-- No endpoint of a remote crossing edge is one of the four source ports. -/
theorem crossingEdge_endpoint_ne_portVertex
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    {edge : G.edgeSet} (hcrossing : edge ∈ cycle.crossingEdges)
    {vertex : V} (hvertex : vertex ∈ (edge.1 : Sym2 V))
    (port : Fin 4) :
    vertex ≠
      (RecoveredRotationOrderedData graphData minimal baseData).portVertex
        port := by
  intro hvertexPort
  let data := RecoveredRotationOrderedData graphData minimal baseData
  have htargetEndpoint : vertex ∈
      graphData.toRotationSystem.endpoints edge :=
    (mem_simpleGraphRotationSystem_endpoints_iff graphData edge vertex).2
      hvertex
  have hboundaryValue : vertex ∈
      ((boundaryEdge data port).1 : Sym2 V) := by
    rw [hvertexPort]
    exact data.portVertex_mem_boundaryEdgeValue port
  have hboundaryEndpoint : vertex ∈
      graphData.toRotationSystem.endpoints (boundaryEdge data port) :=
    (mem_simpleGraphRotationSystem_endpoints_iff graphData
      (boundaryEdge data port) vertex).2 hboundaryValue
  have hne : edge ≠ boundaryEdge data port := by
    simpa [data, RecoveredRotationOrderedData] using
      (cycle.crossingEdge_ne_boundary hcrossing port).symm
  rcases graphData.toRotationSystem.exists_common_orbitFace_of_distinct_incident_edges
      minimal.spherical.cubic minimal.vertexRotationCyclic hne
        htargetEndpoint hboundaryEndpoint with
    ⟨face, hedgeFace, hboundaryFace⟩
  have hsupport :
      (⟨face, Finset.mem_univ face⟩ : AmbientFace
        (Finset.univ : Finset
          (OrbitFace graphData.toRotationSystem))) ∈ cycle.walk.support :=
    face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
      graphData (pairwiseUniqueSharedInteriorEdges graphData minimal)
        cycle.walk hcrossing hedgeFace
  exact cycle.boundary_not_mem
    ⟨face, Finset.mem_univ face⟩ hsupport port hboundaryFace

/-- The endpoints chosen by an intrinsic singleton target avoid all four
source ports. -/
theorem IntrinsicShortFusionTarget.exists_endpoints_avoiding_sourcePorts
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (target : cycle.IntrinsicShortFusionTarget targetEdge) :
    ∃ first second : V,
      targetEdge.1 = s(first, second) ∧
        ∀ port : Fin 4,
          first ≠
              (RecoveredRotationOrderedData graphData minimal
                baseData).portVertex port ∧
            second ≠
              (RecoveredRotationOrderedData graphData minimal
                baseData).portVertex port := by
  rcases target with
    ⟨first, second, _hne, _hadj, htarget, _hcentral, _hboundary,
      _hkempe, _hsingleton, hcrossing⟩
  refine ⟨first, second, htarget, ?_⟩
  intro port
  constructor
  · apply cycle.crossingEdge_endpoint_ne_portVertex hcrossing
    rw [htarget]
    exact Sym2.mem_mk_left first second
  · apply cycle.crossingEdge_endpoint_ne_portVertex hcrossing
    rw [htarget]
    exact Sym2.mem_mk_right first second

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
