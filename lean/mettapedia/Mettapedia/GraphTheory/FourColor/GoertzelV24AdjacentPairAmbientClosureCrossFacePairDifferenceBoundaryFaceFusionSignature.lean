import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusion

namespace SimpleGraph.Walk

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- At the terminal endpoint of a prescribed cycle dart, the cycle contains
another incident edge distinct from the prescribed edge. -/
theorem IsCycle.exists_nextEdge_ne_at_dart
    {base : V} {cycle : G.Walk base base}
    (hcycle : cycle.IsCycle) (root : G.Dart)
    (hroot : root.edge ∈ cycle.edges) :
    ∃ edge : G.edgeSet,
      root.snd ∈ (edge.1 : Sym2 V) ∧
        edge.1 ∈ cycle.edges ∧ edge.1 ≠ root.edge := by
  rcases hcycle.exists_complementaryPath_at_dart root hroot with
    ⟨complement, _hcomplement, hrootComplement, hexact⟩
  have hcomplementNotNil : ¬complement.Nil :=
    SimpleGraph.Walk.not_nil_of_ne root.adj.ne.symm
  have hnext : s(root.snd, complement.snd) ∈ complement.edges :=
    complement.mk_start_snd_mem_edges hcomplementNotNil
  let edge : G.edgeSet :=
    ⟨s(root.snd, complement.snd),
      complement.edges_subset_edgeSet hnext⟩
  refine ⟨edge, ?_, (hexact edge.1).2 (Or.inr hnext), ?_⟩
  · simp [edge]
  · intro hedge
    apply hrootComplement
    rw [← hedge]
    exact hnext

end SimpleGraph.Walk

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
/-- The alternate exact closure contains exactly restored boundary edges
`1` and `3`. -/
theorem boundaryEdgeValue_mem_alternateOppositePortClosure_edges_iff
    (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (port : Fin 4) :
    boundaryEdgeValue data port ∈
        (data.alternateOppositePortClosure path).edges ↔
      port = 1 ∨ port = 3 := by
  change boundaryEdgeValue data port ∈
      ((data.retainedWalkToAmbient path).append
        data.alternateOppositePortCentralReturnRetained).edges ↔ _
  rw [SimpleGraph.Walk.edges_append, List.mem_append]
  constructor
  · rintro (hretained | hreturn)
    · exact False.elim
        (data.boundaryEdgeValue_not_mem_retainedWalkToAmbient_edges
          path port hretained)
    · rw [data.alternateOppositePortCentralReturnRetained_edges,
        data.alternateOppositePortCentralReturn_edges] at hreturn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hreturn
      rcases hreturn with hthree | hcentral | hone
      · exact Or.inr (boundaryEdgeValue_injective data hthree)
      · exact False.elim
          (centralEdgeValue_ne_boundaryEdgeValue data port hcentral.symm)
      · exact Or.inl (boundaryEdgeValue_injective data hone)
  · intro hport
    apply Or.inr
    rw [data.alternateOppositePortCentralReturnRetained_edges,
      data.alternateOppositePortCentralReturn_edges]
    rcases hport with rfl | rfl <;> simp

/-- Under a closure-or-remote-face support bound, a three-way incident-edge
classification loses any boundary edge absent from both supports. -/
theorem edge_eq_central_or_boundary_of_supported_threeWay
    {graphData : Data G} (data : AdjacentPairData G)
    {parentRoot : V} (parent : G.Walk parentRoot parentRoot)
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4,
      boundaryEdge data port ∉
        orbitFaceBoundary graphData.toRotationSystem face)
    {fusionRoot : V} (fusion : G.Walk fusionRoot fusionRoot)
    (hsupport : ∀ edge : G.edgeSet, edge.1 ∈ fusion.edges →
      edge.1 ∈ parent.edges ∨
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (selected wrong : Fin 4)
    (hwrongParent : boundaryEdgeValue data wrong ∉ parent.edges)
    (edge : G.edgeSet) (hedge : edge.1 ∈ fusion.edges)
    (hcases : edge.1 = centralEdgeValue data ∨
      edge.1 = boundaryEdgeValue data selected ∨
      edge.1 = boundaryEdgeValue data wrong) :
    edge.1 = centralEdgeValue data ∨
      edge.1 = boundaryEdgeValue data selected := by
  rcases hcases with hcentral | hselected | hwrong
  · exact Or.inl hcentral
  · exact Or.inr hselected
  · rcases hsupport edge hedge with hparent | hface
    · apply False.elim
      apply hwrongParent
      rw [← hwrong]
      exact hparent
    · apply False.elim
      apply hboundary wrong
      have hedgeEq : edge = boundaryEdge data wrong :=
        Subtype.ext hwrong
      rw [← hedgeEq]
      exact hface

/-- A simple cycle supported by an opposite-port closure and a face avoiding
the restored boundary uses the closure's three-edge return all at once or
not at all. Equivalently, each selected boundary edge occurs exactly when
the central edge occurs. -/
theorem oppositePortFusion_returnEdge_mem_iff
    {graphData : Data G} (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4,
      boundaryEdge data port ∉
        orbitFaceBoundary graphData.toRotationSystem face)
    {fusionRoot : V} (fusion : G.Walk fusionRoot fusionRoot)
    (hfusion : fusion.IsCycle)
    (hsupport : ∀ edge : G.edgeSet, edge.1 ∈ fusion.edges →
      edge.1 ∈ (data.oppositePortClosure path).edges ∨
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face) :
    (boundaryEdgeValue data 0 ∈ fusion.edges ↔
        centralEdgeValue data ∈ fusion.edges) ∧
      (boundaryEdgeValue data 2 ∈ fusion.edges ↔
        centralEdgeValue data ∈ fusion.edges) := by
  have hwrongOne : boundaryEdgeValue data 1 ∉
      (data.oppositePortClosure path).edges := by
    intro hmem
    have hport :=
      (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff path 1).1 hmem
    omega
  have hwrongThree : boundaryEdgeValue data 3 ∉
      (data.oppositePortClosure path).edges := by
    intro hmem
    have hport :=
      (data.boundaryEdgeValue_mem_oppositePortClosure_edges_iff path 3).1 hmem
    omega
  have hclassifyFirst (edge : G.edgeSet) (hedge : edge.1 ∈ fusion.edges)
      (hfirst : data.firstVertex ∈ (edge.1 : Sym2 V)) :
      edge.1 = centralEdgeValue data ∨
        edge.1 = boundaryEdgeValue data 0 := by
    apply edge_eq_central_or_boundary_of_supported_threeWay data
      (data.oppositePortClosure path) face hboundary fusion hsupport
        0 1 hwrongOne edge hedge
    simpa [centralEdgeValue] using
      data.edge_eq_central_or_firstPort_of_mem edge hfirst
  have hclassifySecond (edge : G.edgeSet) (hedge : edge.1 ∈ fusion.edges)
      (hsecond : data.secondVertex ∈ (edge.1 : Sym2 V)) :
      edge.1 = centralEdgeValue data ∨
        edge.1 = boundaryEdgeValue data 2 := by
    apply edge_eq_central_or_boundary_of_supported_threeWay data
      (data.oppositePortClosure path) face hboundary fusion hsupport
        2 3 hwrongThree edge hedge
    simpa [centralEdgeValue] using
      data.edge_eq_central_or_secondPort_of_mem edge hsecond
  have hcentralToZero (hcentral : centralEdgeValue data ∈ fusion.edges) :
      boundaryEdgeValue data 0 ∈ fusion.edges := by
    let root : G.Dart :=
      ⟨(data.secondVertex, data.firstVertex), data.centralAdjacent.symm⟩
    have hrootEdge : root.edge = centralEdgeValue data := by
      simp [root, SimpleGraph.Dart.edge, centralEdgeValue, Sym2.eq_swap]
    have hroot : root.edge ∈ fusion.edges := hrootEdge ▸ hcentral
    rcases hfusion.exists_nextEdge_ne_at_dart root hroot with
      ⟨edge, hfirst, hedge, hne⟩
    rcases hclassifyFirst edge hedge hfirst with hcentralEdge | hzero
    · exact False.elim (hne (hcentralEdge.trans hrootEdge.symm))
    · rw [← hzero]
      exact hedge
  have hcentralToTwo (hcentral : centralEdgeValue data ∈ fusion.edges) :
      boundaryEdgeValue data 2 ∈ fusion.edges := by
    let root : G.Dart :=
      ⟨(data.firstVertex, data.secondVertex), data.centralAdjacent⟩
    have hrootEdge : root.edge = centralEdgeValue data := by
      rfl
    have hroot : root.edge ∈ fusion.edges := hrootEdge ▸ hcentral
    rcases hfusion.exists_nextEdge_ne_at_dart root hroot with
      ⟨edge, hsecond, hedge, hne⟩
    rcases hclassifySecond edge hedge hsecond with hcentralEdge | htwo
    · exact False.elim (hne (hcentralEdge.trans hrootEdge.symm))
    · rw [← htwo]
      exact hedge
  have hzeroToCentral (hzero : boundaryEdgeValue data 0 ∈ fusion.edges) :
      centralEdgeValue data ∈ fusion.edges := by
    let root : G.Dart :=
      ⟨(data.portVertex 0, data.firstVertex), data.first_adj_port_zero.symm⟩
    have hrootEdge : root.edge = boundaryEdgeValue data 0 := by
      simp [root, SimpleGraph.Dart.edge, Sym2.eq_swap]
    have hroot : root.edge ∈ fusion.edges := hrootEdge ▸ hzero
    rcases hfusion.exists_nextEdge_ne_at_dart root hroot with
      ⟨edge, hfirst, hedge, hne⟩
    rcases hclassifyFirst edge hedge hfirst with hcentral | hzeroEdge
    · rw [← hcentral]
      exact hedge
    · exact False.elim (hne (hzeroEdge.trans hrootEdge.symm))
  have htwoToCentral (htwo : boundaryEdgeValue data 2 ∈ fusion.edges) :
      centralEdgeValue data ∈ fusion.edges := by
    let root : G.Dart :=
      ⟨(data.portVertex 2, data.secondVertex), data.second_adj_port_two.symm⟩
    have hrootEdge : root.edge = boundaryEdgeValue data 2 := by
      simp [root, SimpleGraph.Dart.edge, Sym2.eq_swap]
    have hroot : root.edge ∈ fusion.edges := hrootEdge ▸ htwo
    rcases hfusion.exists_nextEdge_ne_at_dart root hroot with
      ⟨edge, hsecond, hedge, hne⟩
    rcases hclassifySecond edge hedge hsecond with hcentral | htwoEdge
    · rw [← hcentral]
      exact hedge
    · exact False.elim (hne (htwoEdge.trans hrootEdge.symm))
  exact ⟨⟨hzeroToCentral, hcentralToZero⟩,
    ⟨htwoToCentral, hcentralToTwo⟩⟩

/-- The same all-or-none return classification holds for a cycle supported
by the alternate opposite-port closure and a boundary-avoiding face. -/
theorem alternateOppositePortFusion_returnEdge_mem_iff
    {graphData : Data G} (data : AdjacentPairData G)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4,
      boundaryEdge data port ∉
        orbitFaceBoundary graphData.toRotationSystem face)
    {fusionRoot : V} (fusion : G.Walk fusionRoot fusionRoot)
    (hfusion : fusion.IsCycle)
    (hsupport : ∀ edge : G.edgeSet, edge.1 ∈ fusion.edges →
      edge.1 ∈ (data.alternateOppositePortClosure path).edges ∨
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face) :
    (boundaryEdgeValue data 1 ∈ fusion.edges ↔
        centralEdgeValue data ∈ fusion.edges) ∧
      (boundaryEdgeValue data 3 ∈ fusion.edges ↔
        centralEdgeValue data ∈ fusion.edges) := by
  have hwrongZero : boundaryEdgeValue data 0 ∉
      (data.alternateOppositePortClosure path).edges := by
    intro hmem
    have hport :=
      (boundaryEdgeValue_mem_alternateOppositePortClosure_edges_iff
        data path 0).1 hmem
    omega
  have hwrongTwo : boundaryEdgeValue data 2 ∉
      (data.alternateOppositePortClosure path).edges := by
    intro hmem
    have hport :=
      (boundaryEdgeValue_mem_alternateOppositePortClosure_edges_iff
        data path 2).1 hmem
    omega
  have hclassifyFirst (edge : G.edgeSet) (hedge : edge.1 ∈ fusion.edges)
      (hfirst : data.firstVertex ∈ (edge.1 : Sym2 V)) :
      edge.1 = centralEdgeValue data ∨
        edge.1 = boundaryEdgeValue data 1 := by
    apply edge_eq_central_or_boundary_of_supported_threeWay data
      (data.alternateOppositePortClosure path) face hboundary fusion
        hsupport 1 0 hwrongZero edge hedge
    rcases data.edge_eq_central_or_firstPort_of_mem edge hfirst with
      hcentral | hzero | hone
    · exact Or.inl (by simpa [centralEdgeValue] using hcentral)
    · exact Or.inr (Or.inr (by simpa using hzero))
    · exact Or.inr (Or.inl (by simpa using hone))
  have hclassifySecond (edge : G.edgeSet) (hedge : edge.1 ∈ fusion.edges)
      (hsecond : data.secondVertex ∈ (edge.1 : Sym2 V)) :
      edge.1 = centralEdgeValue data ∨
        edge.1 = boundaryEdgeValue data 3 := by
    apply edge_eq_central_or_boundary_of_supported_threeWay data
      (data.alternateOppositePortClosure path) face hboundary fusion
        hsupport 3 2 hwrongTwo edge hedge
    rcases data.edge_eq_central_or_secondPort_of_mem edge hsecond with
      hcentral | htwo | hthree
    · exact Or.inl (by simpa [centralEdgeValue] using hcentral)
    · exact Or.inr (Or.inr (by simpa using htwo))
    · exact Or.inr (Or.inl (by simpa using hthree))
  have hcentralToOne (hcentral : centralEdgeValue data ∈ fusion.edges) :
      boundaryEdgeValue data 1 ∈ fusion.edges := by
    let root : G.Dart :=
      ⟨(data.secondVertex, data.firstVertex), data.centralAdjacent.symm⟩
    have hrootEdge : root.edge = centralEdgeValue data := by
      simp [root, SimpleGraph.Dart.edge, centralEdgeValue, Sym2.eq_swap]
    have hroot : root.edge ∈ fusion.edges := hrootEdge ▸ hcentral
    rcases hfusion.exists_nextEdge_ne_at_dart root hroot with
      ⟨edge, hfirst, hedge, hne⟩
    rcases hclassifyFirst edge hedge hfirst with hcentralEdge | hone
    · exact False.elim (hne (hcentralEdge.trans hrootEdge.symm))
    · rw [← hone]
      exact hedge
  have hcentralToThree (hcentral : centralEdgeValue data ∈ fusion.edges) :
      boundaryEdgeValue data 3 ∈ fusion.edges := by
    let root : G.Dart :=
      ⟨(data.firstVertex, data.secondVertex), data.centralAdjacent⟩
    have hrootEdge : root.edge = centralEdgeValue data := by
      rfl
    have hroot : root.edge ∈ fusion.edges := hrootEdge ▸ hcentral
    rcases hfusion.exists_nextEdge_ne_at_dart root hroot with
      ⟨edge, hsecond, hedge, hne⟩
    rcases hclassifySecond edge hedge hsecond with hcentralEdge | hthree
    · exact False.elim (hne (hcentralEdge.trans hrootEdge.symm))
    · rw [← hthree]
      exact hedge
  have honeToCentral (hone : boundaryEdgeValue data 1 ∈ fusion.edges) :
      centralEdgeValue data ∈ fusion.edges := by
    let root : G.Dart :=
      ⟨(data.portVertex 1, data.firstVertex), data.first_adj_port_one.symm⟩
    have hrootEdge : root.edge = boundaryEdgeValue data 1 := by
      simp [root, SimpleGraph.Dart.edge, Sym2.eq_swap]
    have hroot : root.edge ∈ fusion.edges := hrootEdge ▸ hone
    rcases hfusion.exists_nextEdge_ne_at_dart root hroot with
      ⟨edge, hfirst, hedge, hne⟩
    rcases hclassifyFirst edge hedge hfirst with hcentral | honeEdge
    · rw [← hcentral]
      exact hedge
    · exact False.elim (hne (honeEdge.trans hrootEdge.symm))
  have hthreeToCentral (hthree : boundaryEdgeValue data 3 ∈ fusion.edges) :
      centralEdgeValue data ∈ fusion.edges := by
    let root : G.Dart :=
      ⟨(data.portVertex 3, data.secondVertex), data.second_adj_port_three.symm⟩
    have hrootEdge : root.edge = boundaryEdgeValue data 3 := by
      simp [root, SimpleGraph.Dart.edge, Sym2.eq_swap]
    have hroot : root.edge ∈ fusion.edges := hrootEdge ▸ hthree
    rcases hfusion.exists_nextEdge_ne_at_dart root hroot with
      ⟨edge, hsecond, hedge, hne⟩
    rcases hclassifySecond edge hedge hsecond with hcentral | hthreeEdge
    · rw [← hcentral]
      exact hedge
    · exact False.elim (hne (hthreeEdge.trans hrootEdge.symm))
  exact ⟨⟨honeToCentral, hcentralToOne⟩,
    ⟨hthreeToCentral, hcentralToThree⟩⟩

/-- The two remote-face fusion cycles therefore have exact all-or-none
return signatures: ports `0,2` track the central edge on the first cycle,
and ports `1,3` track it on the second. -/
theorem CrossCentralExactFaceCutPair.fusionCyclePair_returnEdge_mem_iff
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4,
      boundaryEdge data port ∉
        orbitFaceBoundary graphData.toRotationSystem face)
    {firstRoot : V} (firstFusion : G.Walk firstRoot firstRoot)
    (hfirstCycle : firstFusion.IsCycle)
    (hfirstSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ firstFusion.edges →
        edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    {secondRoot : V} (secondFusion : G.Walk secondRoot secondRoot)
    (hsecondCycle : secondFusion.IsCycle)
    (hsecondSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ secondFusion.edges →
        edge.1 ∈
            (data.alternateOppositePortClosure pair.suffixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face) :
    ((boundaryEdgeValue data 0 ∈ firstFusion.edges ↔
          centralEdgeValue data ∈ firstFusion.edges) ∧
        (boundaryEdgeValue data 2 ∈ firstFusion.edges ↔
          centralEdgeValue data ∈ firstFusion.edges)) ∧
      ((boundaryEdgeValue data 1 ∈ secondFusion.edges ↔
          centralEdgeValue data ∈ secondFusion.edges) ∧
        (boundaryEdgeValue data 3 ∈ secondFusion.edges ↔
          centralEdgeValue data ∈ secondFusion.edges)) := by
  exact ⟨oppositePortFusion_returnEdge_mem_iff data pair.prefixTrail face
      hboundary firstFusion hfirstCycle hfirstSupport,
    alternateOppositePortFusion_returnEdge_mem_iff data pair.suffixTrail face
      hboundary secondFusion hsecondCycle hsecondSupport⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
