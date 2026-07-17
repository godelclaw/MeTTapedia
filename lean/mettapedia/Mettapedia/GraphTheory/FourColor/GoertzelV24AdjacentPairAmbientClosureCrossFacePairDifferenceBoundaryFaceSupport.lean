import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceIncidence

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24MinimalFaceIntersections

local instance ambientClosureBoundaryFaceSupportGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- In a graph-backed minimal map, membership in the canonical incident-face
pair of an edge is exactly membership of that edge in the quotient face's
actual boundary. -/
theorem mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (face : OrbitFace graphData.toRotationSystem) (edge : G.edgeSet) :
    face ∈ edgeOrbitFacePair graphData edge ↔
      edge ∈ orbitFaceBoundary graphData.toRotationSystem face := by
  let RS := graphData.toRotationSystem
  let dart := RS.dartRepresentative edge
  have hedge : RS.edgeOf dart = edge := RS.dartRepresentative_edgeOf edge
  change face ∈
      ({dartOrbitFace RS dart,
        dartOrbitFace RS (RS.alpha dart)} : Finset (OrbitFace RS)) ↔
    edge ∈ orbitFaceBoundary RS face
  rw [← orbitFace_incidentFaces_eq_dartSide_pair
    RS minimal.facesTwoSided dart]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hedge]

end GoertzelV24MinimalFaceIntersections

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Every first-side boundary edge belongs to the selected cross face
exactly when that face takes the first restored exterior turn. -/
theorem CrossCentralExactFaceCutPair.boundaryEdge_mem_selectedFaceBoundary_iff_firstExteriorTurn
    {graphData : Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool) (firstIndex : Fin 2)
    (hfirstExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge data (firstSidePort candidate))) ≠ 0 ↔
        candidate = firstIndex)
    (candidate : Fin 2) :
    boundaryEdge data (firstSidePort candidate) ∈
        orbitFaceBoundary graphData.toRotationSystem
          (edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge data cross) coordinate) ↔
      pair.CrossFaceUsesFirstExteriorTurn coordinate := by
  rw [← mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary
      graphData minimal,
    ← crossFaceCoordinate_edgeCrossFaceProfile_ne_zero_iff
      graphData minimal (retainedEdgeToAmbientEdge data cross)
        (boundaryEdge data (firstSidePort candidate)) coordinate,
    pair.crossFaceCoordinate_singletonProfile_firstSide_ne_zero_iff
      minimal coordinate firstIndex hfirstExact candidate,
    ← pair.crossFaceUsesFirstExteriorTurn_iff minimal coordinate
      firstIndex hfirstExact]

/-- The same pointwise boundary characterization holds on the second
restored side. -/
theorem CrossCentralExactFaceCutPair.boundaryEdge_mem_selectedFaceBoundary_iff_secondExteriorTurn
    {graphData : Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool) (secondIndex : Fin 2)
    (hsecondExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge data (secondSidePort candidate))) ≠ 0 ↔
        candidate = secondIndex)
    (candidate : Fin 2) :
    boundaryEdge data (secondSidePort candidate) ∈
        orbitFaceBoundary graphData.toRotationSystem
          (edgeCrossFaceCoordinateOrbitFace graphData
            (retainedEdgeToAmbientEdge data cross) coordinate) ↔
      pair.CrossFaceUsesSecondExteriorTurn coordinate := by
  rw [← mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary
      graphData minimal,
    ← crossFaceCoordinate_edgeCrossFaceProfile_ne_zero_iff
      graphData minimal (retainedEdgeToAmbientEdge data cross)
        (boundaryEdge data (secondSidePort candidate)) coordinate,
    pair.crossFaceCoordinate_singletonProfile_secondSide_ne_zero_iff
      minimal coordinate secondIndex hsecondExact candidate,
    ← pair.crossFaceUsesSecondExteriorTurn_iff minimal coordinate
      secondIndex hsecondExact]

/-- A quotient face has one-sided restored boundary support when it contains
both boundary edges at exactly one of the two restored vertices. -/
def FaceHasOneSidedRestoredBoundarySupport
    (graphData : Data G) (data : AdjacentPairData G)
    (face : OrbitFace graphData.toRotationSystem) : Prop :=
  ((∀ candidate : Fin 2,
      boundaryEdge data (firstSidePort candidate) ∈
        orbitFaceBoundary graphData.toRotationSystem face) ∧
    (∀ candidate : Fin 2,
      boundaryEdge data (secondSidePort candidate) ∉
        orbitFaceBoundary graphData.toRotationSystem face)) ∨
  ((∀ candidate : Fin 2,
      boundaryEdge data (firstSidePort candidate) ∉
        orbitFaceBoundary graphData.toRotationSystem face) ∧
    (∀ candidate : Fin 2,
      boundaryEdge data (secondSidePort candidate) ∈
        orbitFaceBoundary graphData.toRotationSystem face))

/-- After central-return compensation, the rejected-cross transfer closes
trivially exactly when the selected quotient face contains both restored
boundary edges on one side and avoids both restored boundary edges on the
other. -/
theorem CrossCentralExactFaceCutPair.closedTransfer_eq_refl_iff_selectedFaceBoundary_oneSided
    {graphData : Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (coordinate : Bool) (firstIndex secondIndex : Fin 2)
    (hfirstExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge data (firstSidePort candidate))) ≠ 0 ↔
        candidate = firstIndex)
    (hsecondExact : ∀ candidate : Fin 2,
      crossFaceCoordinate coordinate
          (pair.crossFaceDifferenceProfile
            (boundaryEdge data (secondSidePort candidate))) ≠ 0 ↔
        candidate = secondIndex) :
    rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
          Equiv.refl (Bool × Bool) ↔
      FaceHasOneSidedRestoredBoundarySupport graphData data
        (edgeCrossFaceCoordinateOrbitFace graphData
          (retainedEdgeToAmbientEdge data cross) coordinate) := by
  have hmixed :
      rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
          Equiv.refl (Bool × Bool) ↔
        Xor (pair.CrossFaceUsesFirstExteriorTurn coordinate)
          (pair.CrossFaceUsesSecondExteriorTurn coordinate) := by
    rw [rejectedCrossCentralReturnClosedTransfer_eq_refl_iff]
    exact pair.mixedChannel_iff_crossFaceUsesExactlyOneExteriorTurn
      minimal coordinate firstIndex secondIndex hfirstExact hsecondExact
  have hfirst :=
    pair.boundaryEdge_mem_selectedFaceBoundary_iff_firstExteriorTurn
      minimal coordinate firstIndex hfirstExact
  have hsecond :=
    pair.boundaryEdge_mem_selectedFaceBoundary_iff_secondExteriorTurn
      minimal coordinate secondIndex hsecondExact
  unfold FaceHasOneSidedRestoredBoundarySupport
  constructor
  · intro hclosed
    rcases hmixed.1 hclosed with
      hfirstOnly | hsecondOnly
    · exact Or.inl ⟨
        fun candidate => (hfirst candidate).2 hfirstOnly.1,
        fun candidate hmem => hfirstOnly.2 ((hsecond candidate).1 hmem)⟩
    · exact Or.inr ⟨
        fun candidate hmem => hsecondOnly.2 ((hfirst candidate).1 hmem),
        fun candidate => (hsecond candidate).2 hsecondOnly.1⟩
  · intro honeSided
    apply hmixed.2
    rcases honeSided with hfirstOnly | hsecondOnly
    · exact Or.inl ⟨
        (hfirst 0).1 (hfirstOnly.1 0),
        fun hturn => hfirstOnly.2 0 ((hsecond 0).2 hturn)⟩
    · exact Or.inr ⟨
        (hsecond 0).1 (hsecondOnly.2 0),
        fun hturn => hsecondOnly.1 0 ((hfirst 0).2 hturn)⟩

/-- The exact compensated witness can be stated wholly in primal facial
geometry.  Its selected face contains the rejected cross, avoids the
restored central edge, and an identity closed transfer is equivalent to
one-sided restored boundary support. -/
theorem CrossCentralExactFaceCutPair.exists_exactCrossSideClosedTransfer_selectedFaceBoundarySupport
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    ∃ (coordinate : Bool) (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort (firstSidePort firstIndex))
            (data.retainedPort (secondSidePort secondIndex))),
      path.IsPath ∧
        (cross : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        crossFaceCoordinate coordinate
            (pair.crossFaceDifferenceProfile (centralEdge data)) ≠ 0 ∧
        (∀ candidate : Fin 2,
          crossFaceCoordinate coordinate
              (pair.crossFaceDifferenceProfile
                (boundaryEdge data (firstSidePort candidate))) ≠ 0 ↔
            candidate = firstIndex) ∧
        (∀ candidate : Fin 2,
          crossFaceCoordinate coordinate
              (pair.crossFaceDifferenceProfile
                (boundaryEdge data (secondSidePort candidate))) ≠ 0 ↔
            candidate = secondIndex) ∧
        (data.crossSidePortClosure firstIndex secondIndex path).IsCycle ∧
        pair.centralReturnCoordinateParity coordinate
            firstIndex secondIndex = 1 ∧
        retainedEdgeToAmbientEdge data cross ∈
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge data cross) coordinate) ∧
        centralEdge data ∉
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge data cross) coordinate) ∧
        (rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
              Equiv.refl (Bool × Bool) ↔
          FaceHasOneSidedRestoredBoundarySupport graphData data
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge data cross) coordinate)) := by
  rcases pair.exists_exactCrossSideClosedTransfer_selectedFaceGeometry
      minimal with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      hcentral, hfirstExact, hsecondExact, hcycle, hparity,
      hsource, hnotCentral, _hcriterion⟩
  have hsourceBoundary : retainedEdgeToAmbientEdge data cross ∈
      orbitFaceBoundary graphData.toRotationSystem
        (edgeCrossFaceCoordinateOrbitFace graphData
          (retainedEdgeToAmbientEdge data cross) coordinate) :=
    (mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary
      graphData minimal _ _).1 hsource
  have hnotCentralBoundary : centralEdge data ∉
      orbitFaceBoundary graphData.toRotationSystem
        (edgeCrossFaceCoordinateOrbitFace graphData
          (retainedEdgeToAmbientEdge data cross) coordinate) := by
    intro hmem
    exact hnotCentral
      ((mem_edgeOrbitFacePair_iff_mem_orbitFaceBoundary
        graphData minimal _ _).2 hmem)
  exact ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hcentral, hfirstExact, hsecondExact, hcycle, hparity,
    hsourceBoundary, hnotCentralBoundary,
    pair.closedTransfer_eq_refl_iff_selectedFaceBoundary_oneSided
      minimal coordinate firstIndex secondIndex hfirstExact hsecondExact⟩

/-- The rejected zero-fusion `bc` residual has an actual selected face with
the same source, central-avoidance, and exact one-sided boundary-support
criterion. -/
theorem EvenKempeFusionLens.exists_bcClosedTransfer_selectedFaceBoundarySupport_of_rejected_of_zeroFusion
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
      lens01 graphData lens23 hab hac hbc site = false)
    (hzero01 : lens01.fusionSiteCount = 0)
    (hzero23 : lens23.fusionSiteCount = 0) :
    ∃ (pair : CrossCentralExactFaceCutPair graphData data site.1)
        (coordinate : Bool) (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort (firstSidePort firstIndex))
            (data.retainedPort (secondSidePort secondIndex))),
      path.IsPath ∧
        (site.1 : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        (data.crossSidePortClosure firstIndex secondIndex path).IsCycle ∧
        pair.centralReturnCoordinateParity coordinate
            firstIndex secondIndex = 1 ∧
        retainedEdgeToAmbientEdge data site.1 ∈
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge data site.1) coordinate) ∧
        centralEdge data ∉
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge data site.1) coordinate) ∧
        (crossSideCentralReturnCutTransfer firstIndex secondIndex *
              EvenKempeFusionLens.bcCombinedSignedTransfer
                lens01 graphData lens23 hab hac hbc site =
              Equiv.refl (Bool × Bool) ↔
          FaceHasOneSidedRestoredBoundarySupport graphData data
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge data site.1) coordinate)) := by
  rcases EvenKempeFusionLens.exists_bcCrossCentralExactFaceCutPair_of_rejected
      graphData minimal data lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount site hfalse with
    ⟨pair, _hprefixEdges, _hsuffixEdges⟩
  rcases pair.exists_exactCrossSideClosedTransfer_selectedFaceBoundarySupport
      minimal with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      _hcentral, _hfirstExact, _hsecondExact, hcycle, hparity,
      hsource, hnotCentral, hcriterion⟩
  refine ⟨pair, coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hcycle, hparity, hsource, hnotCentral, ?_⟩
  rw [EvenKempeFusionLens.bcCombinedSignedTransfer_eq_diagonal_of_rejected_of_fusionSiteCounts_eq_zero
    graphData data lens01 lens23 hab hac hbc site hfalse hzero01 hzero23]
  simpa only [rejectedCrossCentralReturnClosedTransfer] using hcriterion

/-- The complementary rejected zero-fusion `cb` residual has the same
primal facial-boundary normal form. -/
theorem EvenKempeFusionLens.exists_cbClosedTransfer_selectedFaceBoundarySupport_of_rejected_of_zeroFusion
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
      lens01 graphData lens23 hab hac hbc site = false)
    (hzero01 : lens01.fusionSiteCount = 0)
    (hzero23 : lens23.fusionSiteCount = 0) :
    ∃ (pair : CrossCentralExactFaceCutPair graphData data site.1)
        (coordinate : Bool) (firstIndex secondIndex : Fin 2)
        (path : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort (firstSidePort firstIndex))
            (data.retainedPort (secondSidePort secondIndex))),
      path.IsPath ∧
        (site.1 : Sym2 (retainedVertexSet data.firstVertex
          data.secondVertex)) ∉ path.edges ∧
        (data.crossSidePortClosure firstIndex secondIndex path).IsCycle ∧
        pair.centralReturnCoordinateParity coordinate
            firstIndex secondIndex = 1 ∧
        retainedEdgeToAmbientEdge data site.1 ∈
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge data site.1) coordinate) ∧
        centralEdge data ∉
          orbitFaceBoundary graphData.toRotationSystem
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge data site.1) coordinate) ∧
        (crossSideCentralReturnCutTransfer firstIndex secondIndex *
              EvenKempeFusionLens.cbCombinedSignedTransfer
                lens01 graphData lens23 hab hac hbc site =
              Equiv.refl (Bool × Bool) ↔
          FaceHasOneSidedRestoredBoundarySupport graphData data
            (edgeCrossFaceCoordinateOrbitFace graphData
              (retainedEdgeToAmbientEdge data site.1) coordinate)) := by
  rcases EvenKempeFusionLens.exists_cbCrossCentralExactFaceCutPair_of_rejected
      graphData minimal data lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount site hfalse with
    ⟨pair, _hprefixEdges, _hsuffixEdges⟩
  rcases pair.exists_exactCrossSideClosedTransfer_selectedFaceBoundarySupport
      minimal with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      _hcentral, _hfirstExact, _hsecondExact, hcycle, hparity,
      hsource, hnotCentral, hcriterion⟩
  refine ⟨pair, coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hcycle, hparity, hsource, hnotCentral, ?_⟩
  rw [EvenKempeFusionLens.cbCombinedSignedTransfer_eq_diagonal_of_rejected_of_fusionSiteCounts_eq_zero
    graphData data lens01 lens23 hab hac hbc site hfalse hzero01 hzero23]
  simpa only [rejectedCrossCentralReturnClosedTransfer] using hcriterion

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
