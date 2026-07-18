import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseTransition
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelTransferObstruction

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

/-- A nonempty sparse `bc` channel in a rotation-ordered minimal
counterexample has an unconditional exact normal form: strict source-cycle
descent, or the complete finite exact-rebase transition resolution. -/
theorem EvenKempeFusionLens.exists_rotationOrdered_bcSourceClosureCycleDescent_or_remoteFaceFusionChainResolution_of_minimal
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
    (hnonempty : lens01.bcCrossSites lens23 ≠ []) :
    ∃ (site : lens01.bRoute.CrossSite lens23.cRoute)
        (pair : CrossCentralExactFaceCutPair graphData
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) site.1),
      pair.prefixTrail.edges =
          (lens01.bRoute.crossSplice lens23.cRoute site).support.map
            Subtype.val ∧
        pair.suffixTrail.edges =
          (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
            Subtype.val ∧
        (CrossCentralSourceClosureCycleDescent pair ∨
          (∃ witness : CrossSideRemoteFusionChainTransferWitness graphData
              (baseData.rotationOrderedData graphData minimal.spherical.cubic
                minimal.vertexRotationCyclic) site.1 pair,
            witness.FiniteRebaseTransitionOutcome)) := by
  rcases EvenKempeFusionLens.exists_rotationOrdered_bcCrossExitFaceTransferBit_eq_false_of_minimal
      graphData minimal baseData lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount hnonempty with
    ⟨site, hfalse⟩
  rcases EvenKempeFusionLens.exists_rotationOrdered_bcSourceClosureCycleDescent_or_remoteFaceFusionChainResolution_of_rejected
      graphData minimal baseData lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount site hfalse with
    ⟨pair, hprefix, hsuffix, _houtcome⟩
  exact ⟨site, pair, hprefix, hsuffix,
    pair.sourceClosureCycleDescent_or_exists_finiteRebaseTransition
      minimal baseData⟩

/-- The symmetric nonempty sparse `cb` channel has the same unconditional
source-cycle descent or complete finite exact-rebase transition resolution. -/
theorem EvenKempeFusionLens.exists_rotationOrdered_cbSourceClosureCycleDescent_or_remoteFaceFusionChainResolution_of_minimal
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
    (hnonempty : lens01.cbCrossSites lens23 ≠ []) :
    ∃ (site : lens01.cRoute.CrossSite lens23.bRoute)
        (pair : CrossCentralExactFaceCutPair graphData
          (baseData.rotationOrderedData graphData minimal.spherical.cubic
            minimal.vertexRotationCyclic) site.1),
      pair.prefixTrail.edges =
          (lens01.cRoute.crossSplice lens23.bRoute site).support.map
            Subtype.val ∧
        pair.suffixTrail.edges =
          (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
            Subtype.val ∧
        (CrossCentralSourceClosureCycleDescent pair ∨
          (∃ witness : CrossSideRemoteFusionChainTransferWitness graphData
              (baseData.rotationOrderedData graphData minimal.spherical.cubic
                minimal.vertexRotationCyclic) site.1 pair,
            witness.FiniteRebaseTransitionOutcome)) := by
  rcases EvenKempeFusionLens.exists_rotationOrdered_cbCrossExitFaceTransferBit_eq_false_of_minimal
      graphData minimal baseData lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount hnonempty with
    ⟨site, hfalse⟩
  rcases EvenKempeFusionLens.exists_rotationOrdered_cbSourceClosureCycleDescent_or_remoteFaceFusionChainResolution_of_rejected
      graphData minimal baseData lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount site hfalse with
    ⟨pair, hprefix, hsuffix, _houtcome⟩
  exact ⟨site, pair, hprefix, hsuffix,
    pair.sourceClosureCycleDescent_or_exists_finiteRebaseTransition
      minimal baseData⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
