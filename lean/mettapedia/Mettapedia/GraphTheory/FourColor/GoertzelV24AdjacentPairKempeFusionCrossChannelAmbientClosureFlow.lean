import Mettapedia.GraphTheory.FourColor.CDLFlow
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureBranchTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpaceEquality

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24OrbitFaceCycleSpaceEquality
open GoertzelV24PrimalCycleSpace
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation
open scoped BigOperators

namespace GoertzelV24PrimalCycleSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The scalar Kirchhoff sum is the vertex coordinate of the unoriented
incidence map. -/
theorem scalarVertexKirchhoffSum_eq_f2IncidenceMatrix_mulVec
    (chain : G.edgeSet → F2) (vertex : V) :
    scalarVertexKirchhoffSum G chain vertex =
      (f2IncidenceMatrix G).mulVecLin chain vertex := by
  classical
  unfold scalarVertexKirchhoffSum incidentEdgeFinset
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    f2IncidenceMatrix, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]

/-- Every scalar cycle-space vector satisfies Kirchhoff's law at each
vertex. -/
theorem scalarVertexKirchhoffSum_eq_zero_of_mem_f2CycleSpace
    {chain : G.edgeSet → F2} (hchain : chain ∈ f2CycleSpace G)
    (vertex : V) :
    scalarVertexKirchhoffSum G chain vertex = 0 := by
  have hzero := congrFun ((LinearMap.mem_ker).1 hchain) vertex
  rw [Pi.zero_apply] at hzero
  rw [scalarVertexKirchhoffSum_eq_f2IncidenceMatrix_mulVec]
  exact hzero

end

end GoertzelV24PrimalCycleSpace

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The paired exact-cut transfer is a genuine `F2²` graph circulation.
Each coordinate is a facial boundary and hence lies in the scalar cycle
space. -/
theorem CrossCentralExactFaceCutPair.edgeTransfer_isGraphFlow
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    IsGraphFlow G pair.edgeTransfer := by
  have hprefix :
      orbitFaceBoundaryLinearMap graphData.toRotationSystem
          pair.prefixLabels ∈ f2CycleSpace G :=
    range_orbitFaceBoundaryLinearMap_le_f2CycleSpace graphData
      minimal.facesTwoSided ⟨pair.prefixLabels, rfl⟩
  have hsuffix :
      orbitFaceBoundaryLinearMap graphData.toRotationSystem
          pair.suffixLabels ∈ f2CycleSpace G :=
    range_orbitFaceBoundaryLinearMap_le_f2CycleSpace graphData
      minimal.facesTwoSided ⟨pair.suffixLabels, rfl⟩
  intro vertex
  apply Prod.ext
  · rw [← scalarVertexKirchhoffSum_fst]
    change scalarVertexKirchhoffSum G
      (orbitFaceBoundaryLinearMap graphData.toRotationSystem
        pair.prefixLabels) vertex = 0
    exact scalarVertexKirchhoffSum_eq_zero_of_mem_f2CycleSpace
      hprefix vertex
  · rw [← scalarVertexKirchhoffSum_snd]
    change scalarVertexKirchhoffSum G
      (orbitFaceBoundaryLinearMap graphData.toRotationSystem
        pair.suffixLabels) vertex = 0
    exact scalarVertexKirchhoffSum_eq_zero_of_mem_f2CycleSpace
      hsuffix vertex

private theorem CrossCentralExactFaceCutPair.isCDLGoodAtVertex_of_mem_support
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (hprefixCycle :
      (data.oppositePortClosure pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      (data.alternateOppositePortClosure pair.suffixTrail).IsCycle)
    (vertex : V)
    (hvertex :
      vertex ∈ (data.oppositePortClosure pair.prefixTrail).support ∨
        vertex ∈
          (data.alternateOppositePortClosure pair.suffixTrail).support) :
    IsCDLGoodAtVertex G pair.edgeTransfer vertex := by
  rcases hvertex with hprefix | hsuffix
  · have hcard :
        ((data.oppositePortClosure pair.prefixTrail).toSubgraph.neighborSet
          vertex).ncard = 2 :=
      hprefixCycle.ncard_neighborSet_toSubgraph_eq_two hprefix
    rcases Set.nonempty_of_ncard_ne_zero (by omega :
        ((data.oppositePortClosure pair.prefixTrail).toSubgraph.neighborSet
          vertex).ncard ≠ 0) with ⟨neighbor, hadj⟩
    let edge : G.edgeSet := ⟨s(vertex, neighbor), hadj.adj_sub⟩
    have hedgeIncident : edge ∈ incidentEdgeFinset G vertex := by
      simp [incidentEdgeFinset, edge]
    have hedgePrefix : edge.1 ∈
        (data.oppositePortClosure pair.prefixTrail).edges :=
      (data.oppositePortClosure pair.prefixTrail).mem_edges_toSubgraph.mp hadj
    refine ⟨edge, hedgeIncident, ?_⟩
    intro hzero
    have hfst := congrArg Prod.fst hzero
    have hone := (pair.edgeTransfer_fst_eq_one_iff minimal edge).2
      hedgePrefix
    rw [hone] at hfst
    exact one_ne_zero hfst
  · have hcard :
        ((data.alternateOppositePortClosure pair.suffixTrail).toSubgraph.neighborSet
          vertex).ncard = 2 :=
      hsuffixCycle.ncard_neighborSet_toSubgraph_eq_two hsuffix
    rcases Set.nonempty_of_ncard_ne_zero (by omega :
        ((data.alternateOppositePortClosure pair.suffixTrail).toSubgraph.neighborSet
          vertex).ncard ≠ 0) with ⟨neighbor, hadj⟩
    let edge : G.edgeSet := ⟨s(vertex, neighbor), hadj.adj_sub⟩
    have hedgeIncident : edge ∈ incidentEdgeFinset G vertex := by
      simp [incidentEdgeFinset, edge]
    have hedgeSuffix : edge.1 ∈
        (data.alternateOppositePortClosure pair.suffixTrail).edges :=
      (data.alternateOppositePortClosure pair.suffixTrail)
        |>.mem_edges_toSubgraph.mp hadj
    refine ⟨edge, hedgeIncident, ?_⟩
    intro hzero
    have hsnd := congrArg Prod.snd hzero
    have hone := (pair.edgeTransfer_snd_eq_one_iff minimal edge).2
      hedgeSuffix
    rw [hone] at hsnd
    exact one_ne_zero hsnd

/-- The vertices where the paired transfer is locally nonzero are exactly
the carrier of the two closure cycles. -/
theorem CrossCentralExactFaceCutPair.isCDLGoodAtVertex_iff_mem_closure_support
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (hprefixCycle :
      (data.oppositePortClosure pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      (data.alternateOppositePortClosure pair.suffixTrail).IsCycle)
    (vertex : V) :
    IsCDLGoodAtVertex G pair.edgeTransfer vertex ↔
      vertex ∈ (data.oppositePortClosure pair.prefixTrail).support ∨
        vertex ∈
          (data.alternateOppositePortClosure pair.suffixTrail).support := by
  constructor
  · rintro ⟨edge, hedgeIncident, hedgeNonzero⟩
    have hvertexEdge : vertex ∈ (edge.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using hedgeIncident
    by_contra houtside
    push Not at houtside
    apply hedgeNonzero
    apply (pair.edgeTransfer_eq_zero_iff minimal edge).2
    constructor
    · intro hedge
      exact houtside.1
        ((data.oppositePortClosure pair.prefixTrail)
          |>.mem_support_of_mem_edges hedge hvertexEdge)
    · intro hedge
      exact houtside.2
        ((data.alternateOppositePortClosure pair.suffixTrail)
          |>.mem_support_of_mem_edges hedge hvertexEdge)
  · exact pair.isCDLGoodAtVertex_of_mem_support minimal hprefixCycle
      hsuffixCycle vertex

/-- Flow form of the finite irreducible interface: the paired transfer is
Kirchhoff everywhere, is supported locally exactly on the two cycles, and
has all three nonzero letters at each of their four common branches. -/
theorem CrossCentralExactFaceCutPair.four_branch_flow_profile
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (hprefixCycle :
      (data.oppositePortClosure pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      (data.alternateOppositePortClosure pair.suffixTrail).IsCycle) :
    IsGraphFlow G pair.edgeTransfer ∧
      (∀ vertex : V,
        IsCDLGoodAtVertex G pair.edgeTransfer vertex ↔
          vertex ∈ (data.oppositePortClosure pair.prefixTrail).support ∨
            vertex ∈
              (data.alternateOppositePortClosure pair.suffixTrail).support) ∧
      ((data.oppositePortClosure pair.prefixTrail).support.toFinset ∩
          (data.alternateOppositePortClosure
            pair.suffixTrail).support.toFinset).card = 4 ∧
      ∀ vertex ∈
          (data.oppositePortClosure pair.prefixTrail).support.toFinset ∩
            (data.alternateOppositePortClosure
              pair.suffixTrail).support.toFinset,
        (incidentEdgeFinset G vertex).image pair.edgeTransfer =
          {red, blue, purple} := by
  exact ⟨pair.edgeTransfer_isGraphFlow minimal,
    pair.isCDLGoodAtVertex_iff_mem_closure_support minimal hprefixCycle
      hsuffixCycle,
    pair.four_branch_transfer_profile minimal hprefixCycle hsuffixCycle⟩

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
