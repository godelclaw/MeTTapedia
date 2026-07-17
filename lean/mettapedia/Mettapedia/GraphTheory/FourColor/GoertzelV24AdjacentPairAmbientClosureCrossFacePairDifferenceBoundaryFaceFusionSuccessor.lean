import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionSignature

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every edge occurring in the ambient image of a retained walk is a
retained ambient edge. -/
theorem isRetainedAmbientEdge_of_mem_retainedWalkToAmbient_edges
    (data : AdjacentPairData G)
    {left right : retainedVertexSet data.firstVertex data.secondVertex}
    (walk : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk left right)
    (edge : G.edgeSet)
    (hedge : edge.1 ∈ (data.retainedWalkToAmbient walk).edges) :
    IsRetainedAmbientEdge data edge := by
  apply isRetainedAmbientEdge_of_ne data edge
  · intro heq
    apply data.centralEdgeValue_not_mem_retainedWalkToAmbient_edges walk
    rw [← heq]
    exact hedge
  · intro heq
    apply data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges walk 0
    rw [← heq]
    exact hedge
  · intro heq
    apply data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges walk 1
    rw [← heq]
    exact hedge
  · intro heq
    apply data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges walk 2
    rw [← heq]
    exact hedge
  · intro heq
    apply data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges walk 3
    rw [← heq]
    exact hedge

/-- Every edge of a face avoiding the deleted pair's five incident edges
is retained. -/
theorem isRetainedAmbientEdge_of_mem_remoteFace
    {graphData : Data G} (data : AdjacentPairData G)
    (face : OrbitFace graphData.toRotationSystem)
    (hcentral : centralEdge data ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    (edge : G.edgeSet)
    (hedge : edge ∈ orbitFaceBoundary graphData.toRotationSystem face) :
    IsRetainedAmbientEdge data edge := by
  by_contra hnotRetained
  rcases (not_isRetainedAmbientEdge_iff data edge).1 hnotRetained with
    hcentralEdge | ⟨port, hboundaryEdge⟩
  · apply hcentral
    have hedgeEq : edge = centralEdge data := Subtype.ext hcentralEdge
    exact hedgeEq ▸ hedge
  · apply hboundary port
    have hedgeEq : edge = boundaryEdge data port :=
      Subtype.ext hboundaryEdge
    exact hedgeEq ▸ hedge

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A simple ambient cycle all of whose edges are retained lifts to a simple
cycle in the induced deletion, and mapping the lift back recovers the
original cycle exactly. -/
theorem exists_retainedCycle_of_forall_edge_retained
    (data : AdjacentPairData G)
    {root : V} (cycle : G.Walk root root)
    (hcycle : cycle.IsCycle)
    (hretained : ∀ edge : G.edgeSet, edge.1 ∈ cycle.edges →
      IsRetainedAmbientEdge data edge) :
    ∃ (hroot : root ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (retainedCycle : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk ⟨root, hroot⟩ ⟨root, hroot⟩),
      retainedCycle.IsCycle ∧
        data.retainedWalkToAmbient retainedCycle = cycle := by
  have hsupport : ∀ vertex ∈ cycle.support,
      vertex ∈ retainedVertexSet data.firstVertex data.secondVertex := by
    intro vertex hvertex
    rcases (cycle.mem_support_iff_exists_mem_edges_of_not_nil
        hcycle.not_nil).1 hvertex with ⟨edgeValue, hedge, hvertexEdge⟩
    let edge : G.edgeSet :=
      ⟨edgeValue, cycle.edges_subset_edgeSet hedge⟩
    exact endpoints_mem_retainedVertexSet data edge
      (hretained edge hedge) vertex hvertexEdge
  let retainedCycle := cycle.induce
    (retainedVertexSet data.firstVertex data.secondVertex) hsupport
  have hmapped : data.retainedWalkToAmbient retainedCycle = cycle := by
    change retainedCycle.map
      (SimpleGraph.Embedding.induce
        (retainedVertexSet data.firstVertex data.secondVertex)).toHom = cycle
    simpa [retainedCycle] using
      (SimpleGraph.Walk.map_induce cycle hsupport)
  have hretainedCycle : retainedCycle.IsCycle := by
    apply (SimpleGraph.Walk.map_isCycle_iff_of_injective
      (f := (SimpleGraph.Embedding.induce
        (retainedVertexSet data.firstVertex data.secondVertex)).toHom)
      Subtype.val_injective).1
    rw [SimpleGraph.Walk.map_induce]
    exact hcycle
  exact ⟨hsupport root cycle.start_mem_support,
    retainedCycle, hretainedCycle, hmapped⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A simple retained path between the alternate opposite ports also closes
to a simple ambient cycle through the deleted adjacent pair. -/
theorem alternateOppositePortClosure_isCycle
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hpath : path.IsPath) :
    (data.alternateOppositePortClosure path).IsCycle := by
  have hambientPath : (data.retainedWalkToAmbient path).IsPath :=
    data.retainedWalkToAmbient_isPath hpath
  have hreturnPath :
      data.alternateOppositePortCentralReturnRetained.IsPath :=
    data.alternateOppositePortCentralReturnRetained_isPath
  have hstartNotAmbientTail : data.portVertex 1 ∉
      (data.retainedWalkToAmbient path).support.tail := by
    have hnodup := hambientPath.support_nodup
    rw [← (data.retainedWalkToAmbient path).cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hdisjoint :
      (data.retainedWalkToAmbient path).support.tail.Disjoint
        data.alternateOppositePortCentralReturnRetained.support.tail := by
    rw [List.disjoint_left]
    intro vertex hambient hreturn
    have hambientSupport : vertex ∈
        (data.retainedWalkToAmbient path).support :=
      List.mem_of_mem_tail hambient
    have hambientMap := hambientSupport
    rw [retainedWalkToAmbient, SimpleGraph.Walk.support_map] at hambientMap
    rcases List.mem_map.mp hambientMap with
      ⟨retained, _hretainedSupport, hvertex⟩
    change retained.1 = vertex at hvertex
    subst vertex
    simp only [alternateOppositePortCentralReturnRetained,
      SimpleGraph.Walk.support_copy, alternateOppositePortCentralReturn,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hreturn
    rcases hreturn with hsecond | hfirst | hone
    · exact retained.2.2 hsecond
    · exact retained.2.1 hfirst
    · exact hstartNotAmbientTail (hone ▸ hambient)
  apply hambientPath.isCycle_append hreturnPath hdisjoint
  exact Or.inr (by
    change 1 < 3
    omega)

/-- A boundary edge used by a remote-face fusion of an opposite-port
closure must be one of that closure's two boundary return edges. -/
theorem boundaryPort_eq_zero_or_two_of_mem_oppositePortFusion
    {graphData : Data G} (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    {fusionRoot : V} (fusion : G.Walk fusionRoot fusionRoot)
    (hsupport : ∀ edge : G.edgeSet, edge.1 ∈ fusion.edges →
      edge.1 ∈ (data.oppositePortClosure path).edges ∨
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (port : Fin 4)
    (hport : (boundaryEdge data port : Sym2 V) ∈ fusion.edges) :
    port = 0 ∨ port = 2 := by
  rcases hsupport (boundaryEdge data port) hport with hclosure | hface
  · exact
      (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff path port).1
        hclosure
  · exact False.elim (hboundary port hface)

/-- For the alternate closure, every boundary edge in a remote-face fusion
is one of ports `1` and `3`. -/
theorem boundaryPort_eq_one_or_three_of_mem_alternateOppositePortFusion
    {graphData : Data G} (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    {fusionRoot : V} (fusion : G.Walk fusionRoot fusionRoot)
    (hsupport : ∀ edge : G.edgeSet, edge.1 ∈ fusion.edges →
      edge.1 ∈ (data.alternateOppositePortClosure path).edges ∨
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (port : Fin 4)
    (hport : (boundaryEdge data port : Sym2 V) ∈ fusion.edges) :
    port = 1 ∨ port = 3 := by
  rcases hsupport (boundaryEdge data port) hport with hclosure | hface
  · exact
      (boundaryEdgeValue_mem_alternateOppositePortClosure_edges_iff
        data path port).1 hclosure
  · exact False.elim (hboundary port hface)

/-- If an opposite-port fusion cycle retains the central edge, deleting its
three-edge return exposes a new simple opposite-port path. Every edge of the
new path lies in the fusion cycle, so any retained edge avoided by the fusion
is avoided by the successor path as well. -/
theorem oppositePortFusion_exists_successor_of_central
    {graphData : Data G} (data : AdjacentPairData G)
    (parentPath : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    {fusionRoot : V} (fusion : G.Walk fusionRoot fusionRoot)
    (hfusion : fusion.IsCycle)
    (hsupport : ∀ edge : G.edgeSet, edge.1 ∈ fusion.edges →
      edge.1 ∈ (data.oppositePortClosure parentPath).edges ∨
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (hcentralFusion : centralEdgeValue data ∈ fusion.edges)
    (avoided : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (havoidedFusion : (retainedEdgeToAmbientEdge data avoided).1 ∉
      fusion.edges) :
    ∃ successor : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2),
      successor.IsPath ∧
        avoided.1 ∉ successor.edges ∧
        (data.oppositePortClosure successor).IsCycle ∧
        (data.retainedWalkToAmbient successor).edges ⊆ fusion.edges := by
  have hcentralEdge : (centralEdge data : Sym2 V) ∈ fusion.edges := by
    simpa using hcentralFusion
  rcases exists_crossSide_retainedPortPath_of_central_cycle data
      hfusion hcentralEdge with
    ⟨secondPort, firstPort, returnPath, hsecondSide, hfirstSide,
      hreturnPath, hsecondBoundary, hfirstBoundary, hreturnSubset⟩
  have hsecondAllowed :=
    boundaryPort_eq_zero_or_two_of_mem_oppositePortFusion data parentPath
      face hboundary fusion hsupport secondPort hsecondBoundary
  have hfirstAllowed :=
    boundaryPort_eq_zero_or_two_of_mem_oppositePortFusion data parentPath
      face hboundary fusion hsupport firstPort hfirstBoundary
  have hsecondPort : secondPort = 2 := by omega
  have hfirstPort : firstPort = 0 := by omega
  subst secondPort
  subst firstPort
  let successor := returnPath.reverse
  have hsuccessorPath : successor.IsPath := hreturnPath.reverse
  have hambientReverse : data.retainedWalkToAmbient successor =
      (data.retainedWalkToAmbient returnPath).reverse := by
    change returnPath.reverse.map data.retainedGraphHom =
      (returnPath.map data.retainedGraphHom).reverse
    exact (SimpleGraph.Walk.reverse_map data.retainedGraphHom returnPath).symm
  have hsuccessorSubset :
      (data.retainedWalkToAmbient successor).edges ⊆ fusion.edges := by
    intro edge hedge
    rw [hambientReverse, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse] at hedge
    exact hreturnSubset hedge
  have havoidedSuccessor : avoided.1 ∉ successor.edges := by
    intro havoided
    apply havoidedFusion
    apply hsuccessorSubset
    exact
      (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data successor avoided).2 havoided
  exact ⟨successor, hsuccessorPath, havoidedSuccessor,
    data.oppositePortClosure_isCycle successor hsuccessorPath,
    hsuccessorSubset⟩

/-- The central-edge branch of an alternate fusion likewise exposes a new
simple path from port `1` to port `3`, supported by the fusion cycle and
preserving every retained-edge avoidance condition. -/
theorem alternateOppositePortFusion_exists_successor_of_central
    {graphData : Data G} (data : AdjacentPairData G)
    (parentPath : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    {fusionRoot : V} (fusion : G.Walk fusionRoot fusionRoot)
    (hfusion : fusion.IsCycle)
    (hsupport : ∀ edge : G.edgeSet, edge.1 ∈ fusion.edges →
      edge.1 ∈ (data.alternateOppositePortClosure parentPath).edges ∨
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (hcentralFusion : centralEdgeValue data ∈ fusion.edges)
    (avoided : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (havoidedFusion : (retainedEdgeToAmbientEdge data avoided).1 ∉
      fusion.edges) :
    ∃ successor : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3),
      successor.IsPath ∧
        avoided.1 ∉ successor.edges ∧
        (data.alternateOppositePortClosure successor).IsCycle ∧
        (data.retainedWalkToAmbient successor).edges ⊆ fusion.edges := by
  have hcentralEdge : (centralEdge data : Sym2 V) ∈ fusion.edges := by
    simpa using hcentralFusion
  rcases exists_crossSide_retainedPortPath_of_central_cycle data
      hfusion hcentralEdge with
    ⟨secondPort, firstPort, returnPath, hsecondSide, hfirstSide,
      hreturnPath, hsecondBoundary, hfirstBoundary, hreturnSubset⟩
  have hsecondAllowed :=
    boundaryPort_eq_one_or_three_of_mem_alternateOppositePortFusion data
      parentPath face hboundary fusion hsupport secondPort hsecondBoundary
  have hfirstAllowed :=
    boundaryPort_eq_one_or_three_of_mem_alternateOppositePortFusion data
      parentPath face hboundary fusion hsupport firstPort hfirstBoundary
  have hsecondPort : secondPort = 3 := by omega
  have hfirstPort : firstPort = 1 := by omega
  subst secondPort
  subst firstPort
  let successor := returnPath.reverse
  have hsuccessorPath : successor.IsPath := hreturnPath.reverse
  have hambientReverse : data.retainedWalkToAmbient successor =
      (data.retainedWalkToAmbient returnPath).reverse := by
    change returnPath.reverse.map data.retainedGraphHom =
      (returnPath.map data.retainedGraphHom).reverse
    exact (SimpleGraph.Walk.reverse_map data.retainedGraphHom returnPath).symm
  have hsuccessorSubset :
      (data.retainedWalkToAmbient successor).edges ⊆ fusion.edges := by
    intro edge hedge
    rw [hambientReverse, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse] at hedge
    exact hreturnSubset hedge
  have havoidedSuccessor : avoided.1 ∉ successor.edges := by
    intro havoided
    apply havoidedFusion
    apply hsuccessorSubset
    exact
      (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data successor avoided).2 havoided
  exact ⟨successor, hsuccessorPath, havoidedSuccessor,
    alternateOppositePortClosure_isCycle data successor hsuccessorPath,
    hsuccessorSubset⟩

/-- If a remote-face fusion of an opposite-port closure omits the central
edge, then the entire fusion cycle lies in the retained deletion. -/
theorem oppositePortFusion_exists_retainedCycle_of_not_central
    {graphData : Data G} (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    {fusionRoot : V} (fusion : G.Walk fusionRoot fusionRoot)
    (hfusion : fusion.IsCycle)
    (hsupport : ∀ edge : G.edgeSet, edge.1 ∈ fusion.edges →
      edge.1 ∈ (data.oppositePortClosure path).edges ∨
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (hcentralFusion : centralEdgeValue data ∉ fusion.edges) :
    ∃ (hroot : fusionRoot ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk ⟨fusionRoot, hroot⟩
            ⟨fusionRoot, hroot⟩),
      retainedFusion.IsCycle ∧
        data.retainedWalkToAmbient retainedFusion = fusion := by
  have hsignature := oppositePortFusion_returnEdge_mem_iff data path face
    hboundary fusion hfusion hsupport
  have hzeroFusion : boundaryEdgeValue data 0 ∉ fusion.edges := by
    intro hzero
    exact hcentralFusion (hsignature.1.1 hzero)
  have htwoFusion : boundaryEdgeValue data 2 ∉ fusion.edges := by
    intro htwo
    exact hcentralFusion (hsignature.2.1 htwo)
  have hboundaryFusion : ∀ port : Fin 4,
      boundaryEdgeValue data port ∉ fusion.edges := by
    intro port hport
    fin_cases port
    · exact hzeroFusion hport
    · let edge : G.edgeSet := boundaryEdge data 1
      rcases hsupport edge hport with hclosure | hface
      · have hports :=
          (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff path 1).1
            hclosure
        omega
      · exact hboundary 1 hface
    · exact htwoFusion hport
    · let edge : G.edgeSet := boundaryEdge data 3
      rcases hsupport edge hport with hclosure | hface
      · have hports :=
          (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff path 3).1
            hclosure
        omega
      · exact hboundary 3 hface
  apply exists_retainedCycle_of_forall_edge_retained data fusion hfusion
  intro edge hedge
  by_contra hnotRetained
  rcases (not_isRetainedAmbientEdge_iff data edge).1 hnotRetained with
    hcentral | ⟨port, hport⟩
  · apply hcentralFusion
    rw [← hcentral]
    exact hedge
  · apply hboundaryFusion port
    rw [← hport]
    exact hedge

/-- The same retained-cycle alternative holds for a remote-face fusion of
the alternate opposite-port closure. -/
theorem alternateOppositePortFusion_exists_retainedCycle_of_not_central
    {graphData : Data G} (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    {fusionRoot : V} (fusion : G.Walk fusionRoot fusionRoot)
    (hfusion : fusion.IsCycle)
    (hsupport : ∀ edge : G.edgeSet, edge.1 ∈ fusion.edges →
      edge.1 ∈ (data.alternateOppositePortClosure path).edges ∨
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (hcentralFusion : centralEdgeValue data ∉ fusion.edges) :
    ∃ (hroot : fusionRoot ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk ⟨fusionRoot, hroot⟩
            ⟨fusionRoot, hroot⟩),
      retainedFusion.IsCycle ∧
        data.retainedWalkToAmbient retainedFusion = fusion := by
  have hsignature := alternateOppositePortFusion_returnEdge_mem_iff data path
    face hboundary fusion hfusion hsupport
  have honeFusion : boundaryEdgeValue data 1 ∉ fusion.edges := by
    intro hone
    exact hcentralFusion (hsignature.1.1 hone)
  have hthreeFusion : boundaryEdgeValue data 3 ∉ fusion.edges := by
    intro hthree
    exact hcentralFusion (hsignature.2.1 hthree)
  have hboundaryFusion : ∀ port : Fin 4,
      boundaryEdgeValue data port ∉ fusion.edges := by
    intro port hport
    fin_cases port
    · let edge : G.edgeSet := boundaryEdge data 0
      rcases hsupport edge hport with hclosure | hface
      · have hports :=
          (boundaryEdgeValue_mem_alternateOppositePortClosure_edges_iff
            data path 0).1 hclosure
        omega
      · exact hboundary 0 hface
    · exact honeFusion hport
    · let edge : G.edgeSet := boundaryEdge data 2
      rcases hsupport edge hport with hclosure | hface
      · have hports :=
          (boundaryEdgeValue_mem_alternateOppositePortClosure_edges_iff
            data path 2).1 hclosure
        omega
      · exact hboundary 2 hface
    · exact hthreeFusion hport
  apply exists_retainedCycle_of_forall_edge_retained data fusion hfusion
  intro edge hedge
  by_contra hnotRetained
  rcases (not_isRetainedAmbientEdge_iff data edge).1 hnotRetained with
    hcentral | ⟨port, hport⟩
  · apply hcentralFusion
    rw [← hcentral]
    exact hedge
  · apply hboundaryFusion port
    rw [← hport]
    exact hedge

/-- Every remote-face fusion of an opposite-port closure has one of two
structural outcomes: it is already a cycle in the retained deletion, or its
central return can be removed to give a new opposite-port successor path.
The latter preserves avoidance of any prescribed retained edge. -/
theorem oppositePortFusion_retainedCycle_or_successor
    {graphData : Data G} (data : AdjacentPairData G)
    (parentPath : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    {fusionRoot : V} (fusion : G.Walk fusionRoot fusionRoot)
    (hfusion : fusion.IsCycle)
    (hsupport : ∀ edge : G.edgeSet, edge.1 ∈ fusion.edges →
      edge.1 ∈ (data.oppositePortClosure parentPath).edges ∨
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (avoided : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (havoidedFusion : (retainedEdgeToAmbientEdge data avoided).1 ∉
      fusion.edges) :
    (∃ (hroot : fusionRoot ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk ⟨fusionRoot, hroot⟩
            ⟨fusionRoot, hroot⟩),
      retainedFusion.IsCycle ∧
        data.retainedWalkToAmbient retainedFusion = fusion) ∨
    ∃ successor : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2),
      successor.IsPath ∧
        avoided.1 ∉ successor.edges ∧
        (data.oppositePortClosure successor).IsCycle ∧
        (data.retainedWalkToAmbient successor).edges ⊆ fusion.edges := by
  by_cases hcentral : centralEdgeValue data ∈ fusion.edges
  · exact Or.inr (oppositePortFusion_exists_successor_of_central data
      parentPath face hboundary fusion hfusion hsupport hcentral avoided
        havoidedFusion)
  · exact Or.inl
      (oppositePortFusion_exists_retainedCycle_of_not_central data parentPath
        face hboundary fusion hfusion hsupport hcentral)

/-- The alternate remote-face fusion has the parallel retained-cycle or
successor-path resolution, now on ports `1` and `3`. -/
theorem alternateOppositePortFusion_retainedCycle_or_successor
    {graphData : Data G} (data : AdjacentPairData G)
    (parentPath : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    {fusionRoot : V} (fusion : G.Walk fusionRoot fusionRoot)
    (hfusion : fusion.IsCycle)
    (hsupport : ∀ edge : G.edgeSet, edge.1 ∈ fusion.edges →
      edge.1 ∈ (data.alternateOppositePortClosure parentPath).edges ∨
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (avoided : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (havoidedFusion : (retainedEdgeToAmbientEdge data avoided).1 ∉
      fusion.edges) :
    (∃ (hroot : fusionRoot ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk ⟨fusionRoot, hroot⟩
            ⟨fusionRoot, hroot⟩),
      retainedFusion.IsCycle ∧
        data.retainedWalkToAmbient retainedFusion = fusion) ∨
    ∃ successor : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3),
      successor.IsPath ∧
        avoided.1 ∉ successor.edges ∧
        (data.alternateOppositePortClosure successor).IsCycle ∧
        (data.retainedWalkToAmbient successor).edges ⊆ fusion.edges := by
  by_cases hcentral : centralEdgeValue data ∈ fusion.edges
  · exact Or.inr
      (alternateOppositePortFusion_exists_successor_of_central data
        parentPath face hboundary fusion hfusion hsupport hcentral avoided
          havoidedFusion)
  · exact Or.inl
      (alternateOppositePortFusion_exists_retainedCycle_of_not_central data
        parentPath face hboundary fusion hfusion hsupport hcentral)

/-- Resolving both cross-free fusion cycles of an exact pair yields two
independent retained-cycle-or-successor alternatives. In either successor
branch the original exact cross remains absent. -/
theorem CrossCentralExactFaceCutPair.fusionCyclePair_resolution
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    {firstRoot : V} (firstFusion : G.Walk firstRoot firstRoot)
    (hfirstCycle : firstFusion.IsCycle)
    (hfirstCross : (retainedEdgeToAmbientEdge data cross).1 ∉
      firstFusion.edges)
    (hfirstSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ firstFusion.edges →
        edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    {secondRoot : V} (secondFusion : G.Walk secondRoot secondRoot)
    (hsecondCycle : secondFusion.IsCycle)
    (hsecondCross : (retainedEdgeToAmbientEdge data cross).1 ∉
      secondFusion.edges)
    (hsecondSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ secondFusion.edges →
        edge.1 ∈
            (data.alternateOppositePortClosure pair.suffixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face) :
    ((∃ (hroot : firstRoot ∈
            retainedVertexSet data.firstVertex data.secondVertex)
          (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).Walk ⟨firstRoot, hroot⟩
              ⟨firstRoot, hroot⟩),
        retainedFusion.IsCycle ∧
          data.retainedWalkToAmbient retainedFusion = firstFusion) ∨
      ∃ successor : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2),
        successor.IsPath ∧
          cross.1 ∉ successor.edges ∧
          (data.oppositePortClosure successor).IsCycle ∧
          (data.retainedWalkToAmbient successor).edges ⊆
            firstFusion.edges) ∧
    ((∃ (hroot : secondRoot ∈
            retainedVertexSet data.firstVertex data.secondVertex)
          (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).Walk ⟨secondRoot, hroot⟩
              ⟨secondRoot, hroot⟩),
        retainedFusion.IsCycle ∧
          data.retainedWalkToAmbient retainedFusion = secondFusion) ∨
      ∃ successor : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3),
        successor.IsPath ∧
          cross.1 ∉ successor.edges ∧
          (data.alternateOppositePortClosure successor).IsCycle ∧
          (data.retainedWalkToAmbient successor).edges ⊆
            secondFusion.edges) := by
  constructor
  · exact oppositePortFusion_retainedCycle_or_successor data
      pair.prefixTrail face hboundary firstFusion hfirstCycle hfirstSupport
        cross hfirstCross
  · exact alternateOppositePortFusion_retainedCycle_or_successor data
      pair.suffixTrail face hboundary secondFusion hsecondCycle hsecondSupport
        cross hsecondCross

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
