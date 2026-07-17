import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionZeroFusionTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelMultiplicityCircuit
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelTransferObstruction

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Once every nonempty sparse cross channel is known to be rejected, the
two-lens interaction has an exact normal form.  Either cross multiplicity or
an internal fusion site gives a strictly shorter primal circuit, the complete
route containers are disjoint, or both lenses are simple zero-fusion cycles
and one surviving cross has exactly the diagonal signed transfer. -/
theorem EvenKempeFusionLens.rejectedSparseCrossResolution
    (graphData : SimpleGraphDartRotation.Data G)
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
    (hrejectBc : (lens01.bcCrossSites lens23).length ≤ 1 →
      lens01.bcCrossSites lens23 ≠ [] →
        ∃ site : lens01.bRoute.CrossSite lens23.cRoute,
          EvenKempeFusionLens.bcCrossExitFaceTransferBit
            lens01 graphData lens23 hab hac hbc site = false)
    (hrejectCb : (lens01.cbCrossSites lens23).length ≤ 1 →
      lens01.cbCrossSites lens23 ≠ [] →
        ∃ site : lens01.cRoute.CrossSite lens23.bRoute,
          EvenKempeFusionLens.cbCrossExitFaceTransferBit
            lens01 graphData lens23 hab hac hbc site = false) :
    (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
        (circuit : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk start start),
        circuit.IsCircuit ∧
          (circuit.length < lens01.bRoute.ambientPath.length +
              lens23.cRoute.ambientPath.length ∨
            circuit.length < lens01.cRoute.ambientPath.length +
              lens23.bRoute.ambientPath.length ∨
            circuit.length < lens01.closedWalk.length ∨
            circuit.length < lens23.closedWalk.length)) ∨
      (lens01.bRoute.ambientPath.support ++
          lens01.cRoute.ambientPath.support).Disjoint
        (lens23.bRoute.ambientPath.support ++
          lens23.cRoute.ambientPath.support) ∨
      ((lens01.bcCrossSites lens23).length ≤ 1 ∧
          (lens01.cbCrossSites lens23).length ≤ 1) ∧
        lens01.fusionSiteCount = 0 ∧
        lens23.fusionSiteCount = 0 ∧
        lens01.closedWalk.IsCycle ∧
        lens23.closedWalk.IsCycle ∧
        ((∃ site : lens01.bRoute.CrossSite lens23.cRoute,
            EvenKempeFusionLens.bcCrossExitFaceTransferBit
                lens01 graphData lens23 hab hac hbc site = false ∧
              EvenKempeFusionLens.bcCombinedSignedTransfer
                  lens01 graphData lens23 hab hac hbc site =
                signedRoutePermutation true true) ∨
          ∃ site : lens01.cRoute.CrossSite lens23.bRoute,
            EvenKempeFusionLens.cbCrossExitFaceTransferBit
                lens01 graphData lens23 hab hac hbc site = false ∧
              EvenKempeFusionLens.cbCombinedSignedTransfer
                  lens01 graphData lens23 hab hac hbc site =
                signedRoutePermutation true true) := by
  rcases lens01.crossChannels_subsingleton_or_exists_shortPrimalCircuit
      lens23 hab hac hbc with hsparse | hcrossShort
  · by_cases hbcEmpty : lens01.bcCrossSites lens23 = []
    · by_cases hcbEmpty : lens01.cbCrossSites lens23 = []
      · right
        left
        rw [List.disjoint_left]
        intro edge hleft hright
        have hintersection :
            ∃ shared : (DeletedAdjacentPairGraph G data.firstVertex
                data.secondVertex).edgeSet,
              shared ∈ lens01.bRoute.ambientPath.support ++
                  lens01.cRoute.ambientPath.support ∧
                shared ∈ lens23.bRoute.ambientPath.support ++
                  lens23.cRoute.ambientPath.support :=
          ⟨edge, hleft, hright⟩
        rcases (lens01.routeUnions_intersect_iff_crossChannel_nonempty
            lens23 hbDisjoint hcDisjoint).1 hintersection with
          hbcNonempty | hcbNonempty
        · exact hbcNonempty hbcEmpty
        · exact hcbNonempty hcbEmpty
      · rcases hrejectCb hsparse.2 hcbEmpty with ⟨site, hfalse⟩
        by_cases hzero01 : lens01.fusionSiteCount = 0
        · by_cases hzero23 : lens23.fusionSiteCount = 0
          · right
            right
            exact ⟨hsparse, hzero01, hzero23,
              lens01.closedWalk_isCycle_of_fusionSiteCount_eq_zero
                hdata (by decide) hzero01,
              lens23.closedWalk_isCycle_of_fusionSiteCount_eq_zero
                hdata (by decide) hzero23,
              Or.inr ⟨site, hfalse,
                EvenKempeFusionLens.cbCombinedSignedTransfer_eq_diagonal_of_rejected_of_fusionSiteCounts_eq_zero
                  graphData data lens01 lens23 hab hac hbc site hfalse
                    hzero01 hzero23⟩⟩
          · left
            rcases lens23.exists_shorter_primalCircuit_of_fusionSiteCount_pos
                hdata hab hac hbc (Nat.pos_of_ne_zero hzero23) with
              ⟨start, circuit, hcircuit, hshort⟩
            exact ⟨start, circuit, hcircuit, Or.inr (Or.inr (Or.inr hshort))⟩
        · left
          rcases lens01.exists_shorter_primalCircuit_of_fusionSiteCount_pos
              hdata hab hac hbc (Nat.pos_of_ne_zero hzero01) with
            ⟨start, circuit, hcircuit, hshort⟩
          exact ⟨start, circuit, hcircuit, Or.inr (Or.inr (Or.inl hshort))⟩
    · rcases hrejectBc hsparse.1 hbcEmpty with ⟨site, hfalse⟩
      by_cases hzero01 : lens01.fusionSiteCount = 0
      · by_cases hzero23 : lens23.fusionSiteCount = 0
        · right
          right
          exact ⟨hsparse, hzero01, hzero23,
            lens01.closedWalk_isCycle_of_fusionSiteCount_eq_zero
              hdata (by decide) hzero01,
            lens23.closedWalk_isCycle_of_fusionSiteCount_eq_zero
              hdata (by decide) hzero23,
            Or.inl ⟨site, hfalse,
              EvenKempeFusionLens.bcCombinedSignedTransfer_eq_diagonal_of_rejected_of_fusionSiteCounts_eq_zero
                graphData data lens01 lens23 hab hac hbc site hfalse
                  hzero01 hzero23⟩⟩
        · left
          rcases lens23.exists_shorter_primalCircuit_of_fusionSiteCount_pos
              hdata hab hac hbc (Nat.pos_of_ne_zero hzero23) with
            ⟨start, circuit, hcircuit, hshort⟩
          exact ⟨start, circuit, hcircuit, Or.inr (Or.inr (Or.inr hshort))⟩
      · left
        rcases lens01.exists_shorter_primalCircuit_of_fusionSiteCount_pos
            hdata hab hac hbc (Nat.pos_of_ne_zero hzero01) with
          ⟨start, circuit, hcircuit, hshort⟩
        exact ⟨start, circuit, hcircuit, Or.inr (Or.inr (Or.inl hshort))⟩
  · left
    rcases hcrossShort with hbcShort | hcbShort
    · rcases hbcShort with ⟨start, circuit, hcircuit, hshort⟩
      exact ⟨start, circuit, hcircuit, Or.inl hshort⟩
    · rcases hcbShort with ⟨start, circuit, hcircuit, hshort⟩
      exact ⟨start, circuit, hcircuit, Or.inr (Or.inl hshort)⟩

/-- In a graph-backed vertex-minimal counterexample the spherical exact-cut
theorems discharge both rejection premises.  Thus the preceding normal form
is unconditional for the canonical rotation-ordered adjacent pair. -/
theorem EvenKempeFusionLens.rotationOrdered_rejectedSparseCrossResolution_of_minimal
    (graphData : SimpleGraphDartRotation.Data G)
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
              circuit.length < lens23.closedWalk.length)) ∨
        (lens01.bRoute.ambientPath.support ++
            lens01.cRoute.ambientPath.support).Disjoint
          (lens23.bRoute.ambientPath.support ++
            lens23.cRoute.ambientPath.support) ∨
        ((lens01.bcCrossSites lens23).length ≤ 1 ∧
            (lens01.cbCrossSites lens23).length ≤ 1) ∧
          lens01.fusionSiteCount = 0 ∧
          lens23.fusionSiteCount = 0 ∧
          lens01.closedWalk.IsCycle ∧
          lens23.closedWalk.IsCycle ∧
          ((∃ site : lens01.bRoute.CrossSite lens23.cRoute,
              EvenKempeFusionLens.bcCrossExitFaceTransferBit
                  lens01 graphData lens23 hab hac hbc site = false ∧
                EvenKempeFusionLens.bcCombinedSignedTransfer
                    lens01 graphData lens23 hab hac hbc site =
                  signedRoutePermutation true true) ∨
            ∃ site : lens01.cRoute.CrossSite lens23.bRoute,
              EvenKempeFusionLens.cbCrossExitFaceTransferBit
                  lens01 graphData lens23 hab hac hbc site = false ∧
                EvenKempeFusionLens.cbCombinedSignedTransfer
                    lens01 graphData lens23 hab hac hbc site =
                  signedRoutePermutation true true) := by
  dsimp only
  intro C a b c lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
  apply EvenKempeFusionLens.rejectedSparseCrossResolution
    graphData _ lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
  · intro hcount hnonempty
    exact
      EvenKempeFusionLens.exists_rotationOrdered_bcCrossExitFaceTransferBit_eq_false_of_minimal
        graphData minimal baseData lens01 lens23 hdata hab hac hbc
          hbDisjoint hcDisjoint hcount hnonempty
  · intro hcount hnonempty
    exact
      EvenKempeFusionLens.exists_rotationOrdered_cbCrossExitFaceTransferBit_eq_false_of_minimal
        graphData minimal baseData lens01 lens23 hdata hab hac hbc
          hbDisjoint hcDisjoint hcount hnonempty

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
