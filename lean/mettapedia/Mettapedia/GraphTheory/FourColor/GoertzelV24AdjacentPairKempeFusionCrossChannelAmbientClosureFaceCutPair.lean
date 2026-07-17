import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosurePair
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOppositePortFaceCut

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
open GoertzelV24WalkFaceCut
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24WalkFaceCut

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance ambientClosureFaceCutPairGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Two closed trails in a graph-backed minimal spherical map admit
simultaneous exact binary face cuts. Their two cut coordinates change
together exactly on the common edges of the trails. -/
theorem exists_exactOrbitFaceCutPair_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {firstBase secondBase : V}
    (first : G.Walk firstBase firstBase)
    (second : G.Walk secondBase secondBase)
    (hfirst : first.IsTrail) (hsecond : second.IsTrail) :
    ∃ firstLabels secondLabels :
        OrbitFace graphData.toRotationSystem → F2,
      orbitFaceBoundaryLinearMap graphData.toRotationSystem firstLabels =
          walkEdgeParity first ∧
        orbitFaceBoundaryLinearMap graphData.toRotationSystem secondLabels =
          walkEdgeParity second ∧
        (∀ dart : graphData.toRotationSystem.D,
          firstLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
              firstLabels (dartOrbitFace graphData.toRotationSystem
                (graphData.toRotationSystem.alpha dart)) ↔
            (graphData.toRotationSystem.edgeOf dart).1 ∈ first.edges) ∧
        (∀ dart : graphData.toRotationSystem.D,
          secondLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
              secondLabels (dartOrbitFace graphData.toRotationSystem
                (graphData.toRotationSystem.alpha dart)) ↔
            (graphData.toRotationSystem.edgeOf dart).1 ∈ second.edges) ∧
        (∀ dart : graphData.toRotationSystem.D,
          (firstLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
                firstLabels (dartOrbitFace graphData.toRotationSystem
                  (graphData.toRotationSystem.alpha dart)) ∧
            secondLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
                secondLabels (dartOrbitFace graphData.toRotationSystem
                  (graphData.toRotationSystem.alpha dart))) ↔
            (graphData.toRotationSystem.edgeOf dart).1 ∈ first.edges ∧
              (graphData.toRotationSystem.edgeOf dart).1 ∈ second.edges) := by
  rcases exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_minimal
      graphData minimal first hfirst with
    ⟨firstLabels, hfirstBoundary, hfirstExact⟩
  rcases exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_minimal
      graphData minimal second hsecond with
    ⟨secondLabels, hsecondBoundary, hsecondExact⟩
  refine ⟨firstLabels, secondLabels, hfirstBoundary, hsecondBoundary,
    hfirstExact, hsecondExact, ?_⟩
  intro dart
  rw [hfirstExact dart, hsecondExact dart]

end

end GoertzelV24WalkFaceCut

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- A rejected unique `bc` cross in a graph-backed minimal spherical map
produces two exact face cuts whose coordinates change together precisely on
the selected retained cross edge and the restored central edge. -/
theorem EvenKempeFusionLens.exists_bcExactAmbientClosureFaceCutPair_of_rejected
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    ∃ (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2))
        (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 1) (data.retainedPort 3))
        (prefixLabels suffixLabels :
          OrbitFace graphData.toRotationSystem → F2),
      (data.oppositePortClosure prefixTrail).IsTrail ∧
        (data.alternateOppositePortClosure suffixTrail).IsTrail ∧
        orbitFaceBoundaryLinearMap graphData.toRotationSystem prefixLabels =
          walkEdgeParity (data.oppositePortClosure prefixTrail) ∧
        orbitFaceBoundaryLinearMap graphData.toRotationSystem suffixLabels =
          walkEdgeParity (data.alternateOppositePortClosure suffixTrail) ∧
        (retainedEdgeToAmbientEdge data site.1).1 ≠ centralEdgeValue data ∧
        (∀ dart : graphData.toRotationSystem.D,
          (prefixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
                prefixLabels (dartOrbitFace graphData.toRotationSystem
                  (graphData.toRotationSystem.alpha dart)) ∧
            suffixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
                suffixLabels (dartOrbitFace graphData.toRotationSystem
                  (graphData.toRotationSystem.alpha dart))) ↔
            (graphData.toRotationSystem.edgeOf dart).1 =
                (retainedEdgeToAmbientEdge data site.1).1 ∨
              (graphData.toRotationSystem.edgeOf dart).1 =
                centralEdgeValue data) := by
  rcases EvenKempeFusionLens.exists_bcExactAmbientClosurePair_of_rejected
      graphData data lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
        hcount site hfalse with
    ⟨prefixTrail, suffixTrail, hprefixTrail, hsuffixTrail,
      hedgesDistinct, hintersection⟩
  rcases exists_exactOrbitFaceCutPair_of_minimal graphData minimal
      (data.oppositePortClosure prefixTrail)
      (data.alternateOppositePortClosure suffixTrail)
      hprefixTrail hsuffixTrail with
    ⟨prefixLabels, suffixLabels, hprefixBoundary, hsuffixBoundary,
      _hprefixExact, _hsuffixExact, hjoint⟩
  refine ⟨prefixTrail, suffixTrail, prefixLabels, suffixLabels,
    hprefixTrail, hsuffixTrail, hprefixBoundary, hsuffixBoundary,
    hedgesDistinct, ?_⟩
  intro dart
  rw [hjoint dart]
  exact hintersection (graphData.toRotationSystem.edgeOf dart).1

/-- The symmetric rejected unique `cb` cross has the identical simultaneous
two-cut profile. -/
theorem EvenKempeFusionLens.exists_cbExactAmbientClosureFaceCutPair_of_rejected
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    ∃ (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2))
        (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 1) (data.retainedPort 3))
        (prefixLabels suffixLabels :
          OrbitFace graphData.toRotationSystem → F2),
      (data.oppositePortClosure prefixTrail).IsTrail ∧
        (data.alternateOppositePortClosure suffixTrail).IsTrail ∧
        orbitFaceBoundaryLinearMap graphData.toRotationSystem prefixLabels =
          walkEdgeParity (data.oppositePortClosure prefixTrail) ∧
        orbitFaceBoundaryLinearMap graphData.toRotationSystem suffixLabels =
          walkEdgeParity (data.alternateOppositePortClosure suffixTrail) ∧
        (retainedEdgeToAmbientEdge data site.1).1 ≠ centralEdgeValue data ∧
        (∀ dart : graphData.toRotationSystem.D,
          (prefixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
                prefixLabels (dartOrbitFace graphData.toRotationSystem
                  (graphData.toRotationSystem.alpha dart)) ∧
            suffixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
                suffixLabels (dartOrbitFace graphData.toRotationSystem
                  (graphData.toRotationSystem.alpha dart))) ↔
            (graphData.toRotationSystem.edgeOf dart).1 =
                (retainedEdgeToAmbientEdge data site.1).1 ∨
              (graphData.toRotationSystem.edgeOf dart).1 =
                centralEdgeValue data) := by
  rcases EvenKempeFusionLens.exists_cbExactAmbientClosurePair_of_rejected
      graphData data lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
        hcount site hfalse with
    ⟨prefixTrail, suffixTrail, hprefixTrail, hsuffixTrail,
      hedgesDistinct, hintersection⟩
  rcases exists_exactOrbitFaceCutPair_of_minimal graphData minimal
      (data.oppositePortClosure prefixTrail)
      (data.alternateOppositePortClosure suffixTrail)
      hprefixTrail hsuffixTrail with
    ⟨prefixLabels, suffixLabels, hprefixBoundary, hsuffixBoundary,
      _hprefixExact, _hsuffixExact, hjoint⟩
  refine ⟨prefixTrail, suffixTrail, prefixLabels, suffixLabels,
    hprefixTrail, hsuffixTrail, hprefixBoundary, hsuffixBoundary,
    hedgesDistinct, ?_⟩
  intro dart
  rw [hjoint dart]
  exact hintersection (graphData.toRotationSystem.edgeOf dart).1

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
