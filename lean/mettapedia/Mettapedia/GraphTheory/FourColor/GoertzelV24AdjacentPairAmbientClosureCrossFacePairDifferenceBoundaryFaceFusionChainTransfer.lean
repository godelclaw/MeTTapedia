import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileAlignedChain

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
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

/-- The exact cross-side transfer witness, with the remote fusion pair
resolved through the complete finite fusion-chain normal form. -/
structure CrossSideRemoteFusionChainTransferWitness
    (graphData : Data G) (data : AdjacentPairData G)
    (cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (pair : CrossCentralExactFaceCutPair graphData data cross) where
  coordinate : Bool
  firstIndex : Fin 2
  secondIndex : Fin 2
  path : (DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex).Walk
      (data.retainedPort (firstSidePort firstIndex))
      (data.retainedPort (secondSidePort secondIndex))
  path_isPath : path.IsPath
  path_avoids_cross : cross.1 ∉ path.edges
  path_closure_isCycle :
    (data.crossSidePortClosure firstIndex secondIndex path).IsCycle
  coordinate_parity :
    pair.centralReturnCoordinateParity coordinate
      firstIndex secondIndex = 1
  cross_mem_coordinate_face :
    retainedEdgeToAmbientEdge data cross ∈
      orbitFaceBoundary graphData.toRotationSystem
        (edgeCrossFaceCoordinateOrbitFace graphData
          (retainedEdgeToAmbientEdge data cross) coordinate)
  central_not_mem_coordinate_face :
    centralEdge data ∉
      orbitFaceBoundary graphData.toRotationSystem
        (edgeCrossFaceCoordinateOrbitFace graphData
          (retainedEdgeToAmbientEdge data cross) coordinate)
  resolution :
    rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex ≠
        Equiv.refl (Bool × Bool) →
      (∀ port : Fin 4, boundaryEdge data port ∉
        orbitFaceBoundary graphData.toRotationSystem
          (edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge data cross) coordinate)) ∧
      ∃ (firstRoot : V) (firstFusion : G.Walk firstRoot firstRoot)
          (secondRoot : V) (secondFusion : G.Walk secondRoot secondRoot),
        firstFusion.IsCycle ∧
        (retainedEdgeToAmbientEdge data cross).1 ∉ firstFusion.edges ∧
        (∀ edge : G.edgeSet, edge.1 ∈ firstFusion.edges →
          edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges ∨
            edge ∈ orbitFaceBoundary graphData.toRotationSystem
              (edgeCrossFaceCoordinateOrbitFace graphData
                (retainedEdgeToAmbientEdge data cross) coordinate)) ∧
        secondFusion.IsCycle ∧
        (retainedEdgeToAmbientEdge data cross).1 ∉ secondFusion.edges ∧
        (∀ edge : G.edgeSet, edge.1 ∈ secondFusion.edges →
          edge.1 ∈
              (data.alternateOppositePortClosure pair.suffixTrail).edges ∨
            edge ∈ orbitFaceBoundary graphData.toRotationSystem
              (edgeCrossFaceCoordinateOrbitFace graphData
                (retainedEdgeToAmbientEdge data cross) coordinate)) ∧
        ((∃ (hroot : firstRoot ∈
              retainedVertexSet data.firstVertex data.secondVertex)
            (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
              data.secondVertex).Walk ⟨firstRoot, hroot⟩
                ⟨firstRoot, hroot⟩),
          retainedFusion.IsCycle ∧
            data.retainedWalkToAmbient retainedFusion = firstFusion) ∨
          (∃ (hroot : secondRoot ∈
              retainedVertexSet data.firstVertex data.secondVertex)
            (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
              data.secondVertex).Walk ⟨secondRoot, hroot⟩
                ⟨secondRoot, hroot⟩),
          retainedFusion.IsCycle ∧
            data.retainedWalkToAmbient retainedFusion = secondFusion) ∨
          Nonempty (LocalizedFusionSuccessorResolution pair
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge data cross) coordinate)
            firstFusion secondFusion))

/-- A source exact-cut closure has a strict cycle descent when cycle bypass
extracts a shorter simple cycle supported on either one of its two closed
trails. -/
def CrossCentralSourceClosureCycleDescent
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) : Prop :=
  ((data.oppositePortClosure pair.prefixTrail).cycleBypass.IsCycle ∧
      (data.oppositePortClosure pair.prefixTrail).cycleBypass.length <
        (data.oppositePortClosure pair.prefixTrail).length ∧
      (data.oppositePortClosure pair.prefixTrail).cycleBypass.edges ⊆
        (data.oppositePortClosure pair.prefixTrail).edges) ∨
    ((data.alternateOppositePortClosure
          pair.suffixTrail).cycleBypass.IsCycle ∧
      (data.alternateOppositePortClosure
          pair.suffixTrail).cycleBypass.length <
        (data.alternateOppositePortClosure pair.suffixTrail).length ∧
      (data.alternateOppositePortClosure
          pair.suffixTrail).cycleBypass.edges ⊆
        (data.alternateOppositePortClosure pair.suffixTrail).edges)

/-- The compensated cross-side transfer theorem now propagates through
remote-face fusion, successor extraction, finite profiles, and aligned
fusion-chain decomposition. -/
theorem CrossCentralExactFaceCutPair.exists_exactCrossSideClosedTransfer_remoteFaceFusionChainResolution
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross)
    (hprefixCycle :
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).oppositePortClosure
          pair.prefixTrail).IsCycle)
    (hsuffixCycle :
      ((baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).alternateOppositePortClosure
          pair.suffixTrail).IsCycle) :
    Nonempty (CrossSideRemoteFusionChainTransferWitness graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross pair) := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  rcases pair.exists_exactCrossSideClosedTransfer_remoteFaceFusion minimal
      baseData hprefixCycle hsuffixCycle with
    ⟨coordinate, firstIndex, secondIndex, path,
      hpath, hcross, hclosure, hparity, hcrossFace, hcentralFace,
      hremoteFusion⟩
  refine ⟨{
    coordinate := coordinate
    firstIndex := firstIndex
    secondIndex := secondIndex
    path := path
    path_isPath := hpath
    path_avoids_cross := hcross
    path_closure_isCycle := hclosure
    coordinate_parity := hparity
    cross_mem_coordinate_face := hcrossFace
    central_not_mem_coordinate_face := hcentralFace
    resolution := ?_ }⟩
  intro htransfer
  rcases hremoteFusion htransfer with
    ⟨hboundary, firstRoot, firstFusion, secondRoot, secondFusion,
      hfirstCycle, hfirstCross, hfirstSupport,
      hsecondCycle, hsecondCross, hsecondSupport⟩
  let face := edgeCrossFaceCoordinateOrbitFace graphData
    (retainedEdgeToAmbientEdge data cross) coordinate
  have houtcome :=
    pair.fusionCyclePair_retainedCycle_or_fusionChainResolution minimal
      face hboundary firstFusion hfirstCycle hfirstCross hfirstSupport
      secondFusion hsecondCycle hsecondCross hsecondSupport
  exact ⟨hboundary, firstRoot, firstFusion, secondRoot, secondFusion,
    hfirstCycle, hfirstCross, hfirstSupport,
    hsecondCycle, hsecondCross, hsecondSupport, houtcome⟩

/-- Every rotation-ordered exact rejected-cross pair has an unconditional
descent normal form. A nonsimple source closure immediately yields a strict
cycle bypass; otherwise the exact closed transfer propagates through the
complete remote fusion-chain resolution. -/
theorem CrossCentralExactFaceCutPair.sourceClosureCycleDescent_or_exists_exactCrossSideClosedTransfer_remoteFaceFusionChainResolution
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {cross : (DeletedAdjacentPairGraph G baseData.firstVertex
      baseData.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic) cross) :
    CrossCentralSourceClosureCycleDescent pair ∨
      Nonempty (CrossSideRemoteFusionChainTransferWitness graphData
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) cross pair) := by
  rcases pair.cycleDescent_or_exactSimpleCyclePair with
    hdescent | hcycles
  · exact Or.inl hdescent
  · exact Or.inr
      (pair.exists_exactCrossSideClosedTransfer_remoteFaceFusionChainResolution
        minimal baseData hcycles.1 hcycles.2.1)

/-- A rejected singleton `bc` cross in rotation order reaches the complete
remote fusion-chain normal form unless one of its two exact source closures
already has a strict cycle-bypass descent. The exact two splice supports are
retained in either branch. -/
theorem EvenKempeFusionLens.exists_rotationOrdered_bcSourceClosureCycleDescent_or_remoteFaceFusionChainResolution_of_rejected
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 0 1)
    (lens23 : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 2 3)
    (hdata : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    ∃ pair : CrossCentralExactFaceCutPair graphData
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) site.1,
      pair.prefixTrail.edges =
          (lens01.bRoute.crossSplice lens23.cRoute site).support.map
            Subtype.val ∧
        pair.suffixTrail.edges =
          (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
            Subtype.val ∧
        (CrossCentralSourceClosureCycleDescent pair ∨
          Nonempty (CrossSideRemoteFusionChainTransferWitness graphData
            (baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic) site.1 pair)) := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  rcases EvenKempeFusionLens.exists_bcCrossCentralExactFaceCutPair_of_rejected
      graphData minimal data lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount site hfalse with
    ⟨pair, hprefix, hsuffix⟩
  exact ⟨pair, hprefix, hsuffix,
    pair.sourceClosureCycleDescent_or_exists_exactCrossSideClosedTransfer_remoteFaceFusionChainResolution
      minimal baseData⟩

/-- The symmetric rejected singleton `cb` cross has the same unconditional
source-descent or remote fusion-chain normal form, again retaining both
exact splice supports. -/
theorem EvenKempeFusionLens.exists_rotationOrdered_cbSourceClosureCycleDescent_or_remoteFaceFusionChainResolution_of_rejected
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).firstVertex
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic).secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 0 1)
    (lens23 : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 2 3)
    (hdata : (baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic).degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    ∃ pair : CrossCentralExactFaceCutPair graphData
        (baseData.rotationOrderedData graphData minimal.spherical.cubic
          minimal.vertexRotationCyclic) site.1,
      pair.prefixTrail.edges =
          (lens01.cRoute.crossSplice lens23.bRoute site).support.map
            Subtype.val ∧
        pair.suffixTrail.edges =
          (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
            Subtype.val ∧
        (CrossCentralSourceClosureCycleDescent pair ∨
          Nonempty (CrossSideRemoteFusionChainTransferWitness graphData
            (baseData.rotationOrderedData graphData minimal.spherical.cubic
              minimal.vertexRotationCyclic) site.1 pair)) := by
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  rcases EvenKempeFusionLens.exists_cbCrossCentralExactFaceCutPair_of_rejected
      graphData minimal data lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount site hfalse with
    ⟨pair, hprefix, hsuffix⟩
  exact ⟨pair, hprefix, hsuffix,
    pair.sourceClosureCycleDescent_or_exists_exactCrossSideClosedTransfer_remoteFaceFusionChainResolution
      minimal baseData⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
