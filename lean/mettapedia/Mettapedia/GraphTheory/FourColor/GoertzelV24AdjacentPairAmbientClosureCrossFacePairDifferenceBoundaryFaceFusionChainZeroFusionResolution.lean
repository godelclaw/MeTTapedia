import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainSparseChannel
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionZeroFusionResolution

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
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

/-- Rotation-ordered adjacent-pair data selected by a minimal spherical
counterexample. -/
abbrev RotationOrderedMinimalPairData
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G) : AdjacentPairData G :=
  baseData.rotationOrderedData graphData minimal.spherical.cubic
    minimal.vertexRotationCyclic

/-- The irreducible single-cross residual of two sparse fusion lenses. Both
lenses are zero-fusion simple cycles, the surviving rejected cross has the
diagonal four-state transfer, and its exact splice pair reaches a certified
stopping state unless it enters a nonempty closed certified rebase chain. -/
structure SparseSingleCrossFusionChainResidual
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G
      (RotationOrderedMinimalPairData graphData minimal baseData).firstVertex
      (RotationOrderedMinimalPairData graphData minimal baseData).secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : (RotationOrderedMinimalPairData graphData minimal
      baseData).degreeTwoBoundaryData.EvenKempeFusionLens C a b c 0 1)
    (lens23 : (RotationOrderedMinimalPairData graphData minimal
      baseData).degreeTwoBoundaryData.EvenKempeFusionLens C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) where
  bcCrossCount : (lens01.bcCrossSites lens23).length ≤ 1
  cbCrossCount : (lens01.cbCrossSites lens23).length ≤ 1
  firstFusionSiteCount : lens01.fusionSiteCount = 0
  secondFusionSiteCount : lens23.fusionSiteCount = 0
  firstClosedWalk_isCycle : lens01.closedWalk.IsCycle
  secondClosedWalk_isCycle : lens23.closedWalk.IsCycle
  channel :
    (∃ (site : lens01.bRoute.CrossSite lens23.cRoute)
        (pair : CrossCentralExactFaceCutPair graphData
          (RotationOrderedMinimalPairData graphData minimal baseData)
          site.1),
      EvenKempeFusionLens.bcCrossExitFaceTransferBit
          lens01 graphData lens23 hab hac hbc site = false ∧
        EvenKempeFusionLens.bcCombinedSignedTransfer
            lens01 graphData lens23 hab hac hbc site =
          signedRoutePermutation true true ∧
        lens01.cbCrossSites lens23 = [] ∧
        pair.prefixTrail.edges =
          (lens01.bRoute.crossSplice lens23.cRoute site).support.map
            Subtype.val ∧
        pair.suffixTrail.edges =
          (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
            Subtype.val ∧
        pair.CertifiedRebasePumpingOutcome minimal baseData) ∨
      (∃ (site : lens01.cRoute.CrossSite lens23.bRoute)
          (pair : CrossCentralExactFaceCutPair graphData
            (RotationOrderedMinimalPairData graphData minimal baseData)
            site.1),
        EvenKempeFusionLens.cbCrossExitFaceTransferBit
            lens01 graphData lens23 hab hac hbc site = false ∧
          EvenKempeFusionLens.cbCombinedSignedTransfer
              lens01 graphData lens23 hab hac hbc site =
            signedRoutePermutation true true ∧
          lens01.bcCrossSites lens23 = [] ∧
          pair.prefixTrail.edges =
            (lens01.cRoute.crossSplice lens23.bRoute site).support.map
              Subtype.val ∧
          pair.suffixTrail.edges =
            (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
              Subtype.val ∧
          pair.CertifiedRebasePumpingOutcome minimal baseData)

/-- The rotation-ordered sparse-cross theorem with its surviving diagonal
four-state branch refined all the way to exact primal fusion chains. -/
theorem EvenKempeFusionLens.rotationOrdered_sparseCrossFusionChainResolution_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (baseData : GoertzelV24AdjacentPairBoundary.AdjacentPairData G) :
    let data := baseData.rotationOrderedData graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
    ∀ {C : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeColoring Color}
      {a b c : Color}
      (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 0 1)
      (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
        C a b c 2 3)
      (_hdata : data.degreeTwoBoundaryData.WellFormed)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (_hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
        lens23.bRoute.ambientPath.support)
      (_hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
        lens23.cRoute.ambientPath.support),
      (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
          (circuit : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).Walk start start),
          circuit.IsCircuit ∧
            (circuit.length < lens01.bRoute.ambientPath.length +
                lens23.cRoute.ambientPath.length ∨
              circuit.length < lens01.cRoute.ambientPath.length +
                lens23.bRoute.ambientPath.length ∨
              circuit.length < lens01.closedWalk.length ∨
              circuit.length < lens23.closedWalk.length ∨
              circuit.length < lens01.closedWalk.length +
                lens23.closedWalk.length)) ∨
        (lens01.bRoute.ambientPath.support ++
            lens01.cRoute.ambientPath.support).Disjoint
          (lens23.bRoute.ambientPath.support ++
            lens23.cRoute.ambientPath.support) ∨
        Nonempty (SparseSingleCrossFusionChainResidual graphData minimal
          baseData lens01 lens23 hab hac hbc) := by
  dsimp only
  intro C a b c lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
  rcases EvenKempeFusionLens.rotationOrdered_rejectedSparseCrossResolution_of_minimal
      graphData minimal baseData lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint with hshort | hdisjoint | hresidual
  · exact Or.inl hshort
  · exact Or.inr (Or.inl hdisjoint)
  · rcases hresidual with
      ⟨hcounts, hzero01, hzero23, hcycle01, hcycle23, hchannel⟩
    refine Or.inr (Or.inr ⟨{
      bcCrossCount := hcounts.1
      cbCrossCount := hcounts.2
      firstFusionSiteCount := hzero01
      secondFusionSiteCount := hzero23
      firstClosedWalk_isCycle := hcycle01
      secondClosedWalk_isCycle := hcycle23
      channel := ?_ }⟩)
    rcases hchannel with
      ⟨⟨site, hfalse, hdiagonal⟩, hcbEmpty⟩ |
        ⟨hbcEmpty, site, hfalse, hdiagonal⟩
    · rcases EvenKempeFusionLens.exists_rotationOrdered_bcSourceClosureCycleDescent_or_remoteFaceFusionChainResolution_of_rejected
          graphData minimal baseData lens01 lens23 hdata hab hac hbc
            hbDisjoint hcDisjoint hcounts.1 site hfalse with
        ⟨pair, hprefix, hsuffix, _houtcome⟩
      exact Or.inl ⟨site, pair, hfalse, hdiagonal, hcbEmpty,
        hprefix, hsuffix,
        pair.certifiedRebasePumping_outcome minimal baseData⟩
    · rcases EvenKempeFusionLens.exists_rotationOrdered_cbSourceClosureCycleDescent_or_remoteFaceFusionChainResolution_of_rejected
          graphData minimal baseData lens01 lens23 hdata hab hac hbc
            hbDisjoint hcDisjoint hcounts.2 site hfalse with
        ⟨pair, hprefix, hsuffix, _houtcome⟩
      exact Or.inr ⟨site, pair, hfalse, hdiagonal, hbcEmpty,
        hprefix, hsuffix,
        pair.certifiedRebasePumping_outcome minimal baseData⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
