import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelTerminalFaceState
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTerminalFaceCutTransport

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Support in a cross splice implies support in the union of its two
source routes, also after forgetting retained edge subtypes. -/
theorem EvenKempePortPath.walk_edges_subset_route_supports_of_subset_crossSplice
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a b firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a c secondLeft secondRight)
    (site : first.CrossSite second)
    {start finish : retainedVertexSet data.firstVertex data.secondVertex}
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk start finish)
    (hsupport : path.edges ⊆
      (first.crossSplice second site).support.map Subtype.val) :
    path.edges ⊆
      (first.ambientPath.support ++ second.ambientPath.support).map
        Subtype.val := by
  intro edge hedge
  rcases List.mem_map.mp (hsupport hedge) with
    ⟨retainedEdge, hsplice, hvalue⟩
  apply List.mem_map.mpr
  exact ⟨retainedEdge,
    first.crossSplice_support_subset_route_supports second site hsplice,
    hvalue⟩

/-- In a singleton `bc` cross channel, all four right-terminal route edges
at the unused ports avoid the opposite-port closure cut. -/
theorem EvenKempeFusionLens.bcRightTerminalEdges_not_mem_oppositePortClosure
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val) :
    (retainedEdgeToAmbientEdge data lens01.bRoute.rightEdge.1).1 ∉
        (data.oppositePortClosure path).edges ∧
      (retainedEdgeToAmbientEdge data lens01.cRoute.rightEdge.1).1 ∉
        (data.oppositePortClosure path).edges ∧
      (retainedEdgeToAmbientEdge data lens23.bRoute.rightEdge.1).1 ∉
        (data.oppositePortClosure path).edges ∧
      (retainedEdgeToAmbientEdge data lens23.cRoute.rightEdge.1).1 ∉
        (data.oppositePortClosure path).edges := by
  have htails :=
    EvenKempeFusionLens.bcCrossSpliceSuffixes_not_mem_oppositePortClosure_edges
      data lens01 lens23 hcount site path hsupport
  have hrouteSupport :=
    EvenKempePortPath.walk_edges_subset_route_supports_of_subset_crossSplice
      lens01.bRoute
      lens23.cRoute site path hsupport
  have hb01Tail : lens01.bRoute.rightEdge.1 ∈
      (lens01.bRoute.firstSuffixFromCrossSite
        lens23.cRoute site).support.tail := by
    apply SimpleGraph.Walk.end_mem_tail_support
    intro hnil
    have hzero := SimpleGraph.Walk.length_eq_zero_iff.mpr hnil
    have hpositive := lens01.bRoute.firstSuffixFromCrossSite_length_pos
      lens23.cRoute hab hbc site
    omega
  have hc23Tail : lens23.cRoute.rightEdge.1 ∈
      (lens01.bRoute.secondSuffixFromCrossSite
        lens23.cRoute site).support.tail := by
    apply SimpleGraph.Walk.end_mem_tail_support
    intro hnil
    have hzero := SimpleGraph.Walk.length_eq_zero_iff.mpr hnil
    have hpositive := lens01.bRoute.secondSuffixFromCrossSite_length_pos
      lens23.cRoute hac hbc site
    omega
  have hc01Mem : lens01.cRoute.rightEdge.1 ∈
      lens01.cRoute.ambientPath.support :=
    lens01.cRoute.ambientPath.end_mem_support
  have hb23Mem : lens23.bRoute.rightEdge.1 ∈
      lens23.bRoute.ambientPath.support :=
    lens23.bRoute.ambientPath.end_mem_support
  exact ⟨
    htails.1 lens01.bRoute.rightEdge.1 hb01Tail,
    EvenKempeFusionLens.c01_not_mem_bcOppositePortClosure_edges_of_not_mem_b01
      data lens01 lens23 hcDisjoint path hrouteSupport hc01Mem
        (lens01.cRightEdge_not_mem_bAmbientPath_support hab hac),
    EvenKempeFusionLens.b23_not_mem_bcOppositePortClosure_edges_of_not_mem_c23
      data lens01 lens23 hbDisjoint path hrouteSupport hb23Mem
        (lens23.bRightEdge_not_mem_cAmbientPath_support hab hac),
    htails.2 lens23.cRoute.rightEdge.1 hc23Tail⟩

/-- The symmetric `cb` cross channel has the same four-terminal cut
freedom. -/
theorem EvenKempeFusionLens.cbRightTerminalEdges_not_mem_oppositePortClosure
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val) :
    (retainedEdgeToAmbientEdge data lens01.bRoute.rightEdge.1).1 ∉
        (data.oppositePortClosure path).edges ∧
      (retainedEdgeToAmbientEdge data lens01.cRoute.rightEdge.1).1 ∉
        (data.oppositePortClosure path).edges ∧
      (retainedEdgeToAmbientEdge data lens23.bRoute.rightEdge.1).1 ∉
        (data.oppositePortClosure path).edges ∧
      (retainedEdgeToAmbientEdge data lens23.cRoute.rightEdge.1).1 ∉
        (data.oppositePortClosure path).edges := by
  have htails :=
    EvenKempeFusionLens.cbCrossSpliceSuffixes_not_mem_oppositePortClosure_edges
      data lens01 lens23 hcount site path hsupport
  have hrouteSupport :=
    EvenKempePortPath.walk_edges_subset_route_supports_of_subset_crossSplice
      lens01.cRoute
      lens23.bRoute site path hsupport
  have hc01Tail : lens01.cRoute.rightEdge.1 ∈
      (lens01.cRoute.firstSuffixFromCrossSite
        lens23.bRoute site).support.tail := by
    apply SimpleGraph.Walk.end_mem_tail_support
    intro hnil
    have hzero := SimpleGraph.Walk.length_eq_zero_iff.mpr hnil
    have hpositive := lens01.cRoute.firstSuffixFromCrossSite_length_pos
      lens23.bRoute hac hbc.symm site
    omega
  have hb23Tail : lens23.bRoute.rightEdge.1 ∈
      (lens01.cRoute.secondSuffixFromCrossSite
        lens23.bRoute site).support.tail := by
    apply SimpleGraph.Walk.end_mem_tail_support
    intro hnil
    have hzero := SimpleGraph.Walk.length_eq_zero_iff.mpr hnil
    have hpositive := lens01.cRoute.secondSuffixFromCrossSite_length_pos
      lens23.bRoute hab hbc.symm site
    omega
  have hb01Mem : lens01.bRoute.rightEdge.1 ∈
      lens01.bRoute.ambientPath.support :=
    lens01.bRoute.ambientPath.end_mem_support
  have hc23Mem : lens23.cRoute.rightEdge.1 ∈
      lens23.cRoute.ambientPath.support :=
    lens23.cRoute.ambientPath.end_mem_support
  exact ⟨
    EvenKempeFusionLens.b01_not_mem_cbOppositePortClosure_edges_of_not_mem_c01
      data lens01 lens23 hbDisjoint path hrouteSupport hb01Mem
        (lens01.bRightEdge_not_mem_cAmbientPath_support hab hac),
    htails.1 lens01.cRoute.rightEdge.1 hc01Tail,
    htails.2 lens23.bRoute.rightEdge.1 hb23Tail,
    EvenKempeFusionLens.c23_not_mem_cbOppositePortClosure_edges_of_not_mem_b23
      data lens01 lens23 hcDisjoint path hrouteSupport hc23Mem
        (lens23.cRightEdge_not_mem_bAmbientPath_support hab hac)⟩

/-- When both route-terminal edges at a cubic boundary port avoid an exact
cut, their face labels agree. -/
theorem EvenKempeFusionLens.rightTerminalFaceLabels_eq_of_edges_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hbNot : ¬cut (retainedEdgeToAmbientEdge data
      lens.bRoute.rightEdge.1))
    (hcNot : ¬cut (retainedEdgeToAmbientEdge data
      lens.cRoute.rightEdge.1)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientBRightTerminalDart data lens)) =
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientCRightTerminalDart data lens)) := by
  have hbEdge : graphData.toRotationSystem.edgeOf
      (ambientBRightTerminalDart data lens) =
        retainedEdgeToAmbientEdge data lens.bRoute.rightEdge.1 := by
    apply Subtype.ext
    simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
  have hcEdge : graphData.toRotationSystem.edgeOf
      (ambientCRightTerminalDart data lens) =
        retainedEdgeToAmbientEdge data lens.cRoute.rightEdge.1 := by
    apply Subtype.ext
    simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
  apply graphData.toRotationSystem.labels_eq_of_distinct_dartsAt_of_edges_not_cut
    hcubic hrotation labels cut hexact
  · simp
  · exact (ambientRightTerminalDarts_pairwise_ne data lens hbc).2.2
  · rw [hbEdge]
    exact hbNot
  · rw [hcEdge]
    exact hcNot

/-- In a sparse `bc` channel, the two route-terminal face labels agree at
each unused boundary port. -/
theorem EvenKempeFusionLens.bcRightTerminalFaceLabels_eq_at_unusedPorts
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          (data.oppositePortClosure path).edges) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientBRightTerminalDart data lens01)) =
        labels (dartOrbitFace graphData.toRotationSystem
          (ambientCRightTerminalDart data lens01)) ∧
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientBRightTerminalDart data lens23)) =
        labels (dartOrbitFace graphData.toRotationSystem
          (ambientCRightTerminalDart data lens23)) := by
  have hnot :=
    EvenKempeFusionLens.bcRightTerminalEdges_not_mem_oppositePortClosure
      data lens01 lens23 hab hac hbc hbDisjoint hcDisjoint hcount site path
        hsupport
  constructor
  · exact EvenKempeFusionLens.rightTerminalFaceLabels_eq_of_edges_not_cut
      graphData hcubic hrotation data lens01 hbc labels
        (fun edge ↦ edge.1 ∈ (data.oppositePortClosure path).edges)
        hexact hnot.1 hnot.2.1
  · exact EvenKempeFusionLens.rightTerminalFaceLabels_eq_of_edges_not_cut
      graphData hcubic hrotation data lens23 hbc labels
        (fun edge ↦ edge.1 ∈ (data.oppositePortClosure path).edges)
        hexact hnot.2.2.1 hnot.2.2.2

/-- The same unused-port equality holds for a sparse `cb` channel. -/
theorem EvenKempeFusionLens.cbRightTerminalFaceLabels_eq_at_unusedPorts
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (path : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk
        (data.retainedPort 0) (data.retainedPort 2))
    (hsupport : path.edges ⊆
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈
          (data.oppositePortClosure path).edges) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientBRightTerminalDart data lens01)) =
        labels (dartOrbitFace graphData.toRotationSystem
          (ambientCRightTerminalDart data lens01)) ∧
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientBRightTerminalDart data lens23)) =
        labels (dartOrbitFace graphData.toRotationSystem
          (ambientCRightTerminalDart data lens23)) := by
  have hnot :=
    EvenKempeFusionLens.cbRightTerminalEdges_not_mem_oppositePortClosure
      data lens01 lens23 hab hac hbc hbDisjoint hcDisjoint hcount site path
        hsupport
  constructor
  · exact EvenKempeFusionLens.rightTerminalFaceLabels_eq_of_edges_not_cut
      graphData hcubic hrotation data lens01 hbc labels
        (fun edge ↦ edge.1 ∈ (data.oppositePortClosure path).edges)
        hexact hnot.1 hnot.2.1
  · exact EvenKempeFusionLens.rightTerminalFaceLabels_eq_of_edges_not_cut
      graphData hcubic hrotation data lens23 hbc labels
        (fun edge ↦ edge.1 ∈ (data.oppositePortClosure path).edges)
        hexact hnot.2.2.1 hnot.2.2.2

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
