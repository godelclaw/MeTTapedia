import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionSignedTransferMonoid
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionDisjointCircuit

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
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

/-- A lens with no physical fusion sites has the empty face-symbol word. -/
theorem bFusionFaceWord_eq_nil_of_fusionSiteCount_eq_zero
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hzero : lens.fusionSiteCount = 0) :
    bFusionFaceWord graphData data lens hab hac = [] := by
  apply List.eq_nil_of_length_eq_zero
  simpa only [bFusionFaceWord_length] using hzero

/-- Consequently a zero-fusion lens has the identity four-state transfer. -/
theorem bFusionTotalSignedRouteTransfer_eq_refl_of_fusionSiteCount_eq_zero
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (hzero : lens.fusionSiteCount = 0) :
    bFusionTotalSignedRouteTransfer graphData data lens hab hac =
      Equiv.refl (Bool × Bool) := by
  rw [bFusionTotalSignedRouteTransfer,
    bFusionFaceWord_eq_nil_of_fusionSiteCount_eq_zero
      graphData data lens hab hac hzero]
  rfl

/-- Zero fusion count is the geometric normal form in which the two route
supports of the lens are edge-disjoint. -/
theorem EvenKempeFusionLens.routeSupports_disjoint_of_fusionSiteCount_eq_zero
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hzero : lens.fusionSiteCount = 0) :
    lens.bRoute.ambientPath.support.Disjoint
      lens.cRoute.ambientPath.support := by
  apply lens.bFusionSites_eq_nil_iff_disjoint.mp
  apply List.eq_nil_of_length_eq_zero
  exact hzero

/-- With both lenses in zero-fusion normal form, a rejected `bc` cross is
the whole combined transfer and hence is exactly the diagonal flip. -/
theorem EvenKempeFusionLens.bcCombinedSignedTransfer_eq_diagonal_of_rejected_of_fusionSiteCounts_eq_zero
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (hzero01 : lens01.fusionSiteCount = 0)
    (hzero23 : lens23.fusionSiteCount = 0) :
    EvenKempeFusionLens.bcCombinedSignedTransfer lens01 graphData lens23
        hab hac hbc site =
      signedRoutePermutation true true := by
  rw [EvenKempeFusionLens.bcCombinedSignedTransfer,
    bFusionTotalSignedRouteTransfer_eq_refl_of_fusionSiteCount_eq_zero
      graphData data lens01 hab hac hzero01,
    bFusionTotalSignedRouteTransfer_eq_refl_of_fusionSiteCount_eq_zero
      graphData data lens23 hab hac hzero23]
  have hcross :
      (EvenKempeFusionLens.bcCrossFaceSymbol lens01 graphData lens23
        hab hac hbc site).signedRouteTransfer =
          signedRoutePermutation true true := by
    apply crossFaceSymbol_signedRouteTransfer_eq_diagonal_of_rejected
    simpa only [EvenKempeFusionLens.bcCrossExitFaceTransferBit] using hfalse
  rw [hcross]
  rfl

/-- The same exact diagonal normal form in the complementary `cb` channel. -/
theorem EvenKempeFusionLens.cbCombinedSignedTransfer_eq_diagonal_of_rejected_of_fusionSiteCounts_eq_zero
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (hzero01 : lens01.fusionSiteCount = 0)
    (hzero23 : lens23.fusionSiteCount = 0) :
    EvenKempeFusionLens.cbCombinedSignedTransfer lens01 graphData lens23
        hab hac hbc site =
      signedRoutePermutation true true := by
  rw [EvenKempeFusionLens.cbCombinedSignedTransfer,
    bFusionTotalSignedRouteTransfer_eq_refl_of_fusionSiteCount_eq_zero
      graphData data lens01 hab hac hzero01,
    bFusionTotalSignedRouteTransfer_eq_refl_of_fusionSiteCount_eq_zero
      graphData data lens23 hab hac hzero23]
  have hcross :
      (EvenKempeFusionLens.cbCrossFaceSymbol lens01 graphData lens23
        hab hac hbc site).signedRouteTransfer =
          signedRoutePermutation true true := by
    apply crossFaceSymbol_signedRouteTransfer_eq_diagonal_of_rejected
    simpa only [EvenKempeFusionLens.cbCrossExitFaceTransferBit] using hfalse
  rw [hcross]
  rfl

/-- A rejected `bc` cross now has an exact geometric trichotomy. Either an
internal fusion edge shortens one of the two primal lens circuits, or both
lenses have edge-disjoint route supports and the surviving combined transfer
is exactly the diagonal endpoint-and-route flip. -/
theorem EvenKempeFusionLens.bcRejectedCross_shortens_or_zeroFusionDiagonal
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
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
        (circuit : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk start start),
        circuit.IsCircuit ∧ circuit.length < lens01.closedWalk.length) ∨
      (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
          (circuit : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).Walk start start),
          circuit.IsCircuit ∧ circuit.length < lens23.closedWalk.length) ∨
        (lens01.bRoute.ambientPath.support.Disjoint
            lens01.cRoute.ambientPath.support ∧
          lens23.bRoute.ambientPath.support.Disjoint
            lens23.cRoute.ambientPath.support ∧
          lens01.closedWalk.IsCycle ∧
          lens23.closedWalk.IsCycle ∧
          EvenKempeFusionLens.bcCombinedSignedTransfer
              lens01 graphData lens23 hab hac hbc site =
            signedRoutePermutation true true) := by
  by_cases hzero01 : lens01.fusionSiteCount = 0
  · by_cases hzero23 : lens23.fusionSiteCount = 0
    · exact Or.inr (Or.inr ⟨
        EvenKempeFusionLens.routeSupports_disjoint_of_fusionSiteCount_eq_zero
          lens01 hzero01,
        EvenKempeFusionLens.routeSupports_disjoint_of_fusionSiteCount_eq_zero
          lens23 hzero23,
        lens01.closedWalk_isCycle_of_fusionSiteCount_eq_zero
          hdata (by decide) hzero01,
        lens23.closedWalk_isCycle_of_fusionSiteCount_eq_zero
          hdata (by decide) hzero23,
        EvenKempeFusionLens.bcCombinedSignedTransfer_eq_diagonal_of_rejected_of_fusionSiteCounts_eq_zero
          graphData data lens01 lens23 hab hac hbc site hfalse
            hzero01 hzero23⟩)
    · exact Or.inr (Or.inl
        (lens23.exists_shorter_primalCircuit_of_fusionSiteCount_pos
          hdata hab hac hbc (Nat.pos_of_ne_zero hzero23)))
  · exact Or.inl
      (lens01.exists_shorter_primalCircuit_of_fusionSiteCount_pos
        hdata hab hac hbc (Nat.pos_of_ne_zero hzero01))

/-- Complementary `cb` form of the zero-fusion diagonal trichotomy. -/
theorem EvenKempeFusionLens.cbRejectedCross_shortens_or_zeroFusionDiagonal
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
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
        (circuit : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk start start),
        circuit.IsCircuit ∧ circuit.length < lens01.closedWalk.length) ∨
      (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
          (circuit : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).Walk start start),
          circuit.IsCircuit ∧ circuit.length < lens23.closedWalk.length) ∨
        (lens01.bRoute.ambientPath.support.Disjoint
            lens01.cRoute.ambientPath.support ∧
          lens23.bRoute.ambientPath.support.Disjoint
            lens23.cRoute.ambientPath.support ∧
          lens01.closedWalk.IsCycle ∧
          lens23.closedWalk.IsCycle ∧
          EvenKempeFusionLens.cbCombinedSignedTransfer
              lens01 graphData lens23 hab hac hbc site =
            signedRoutePermutation true true) := by
  by_cases hzero01 : lens01.fusionSiteCount = 0
  · by_cases hzero23 : lens23.fusionSiteCount = 0
    · exact Or.inr (Or.inr ⟨
        EvenKempeFusionLens.routeSupports_disjoint_of_fusionSiteCount_eq_zero
          lens01 hzero01,
        EvenKempeFusionLens.routeSupports_disjoint_of_fusionSiteCount_eq_zero
          lens23 hzero23,
        lens01.closedWalk_isCycle_of_fusionSiteCount_eq_zero
          hdata (by decide) hzero01,
        lens23.closedWalk_isCycle_of_fusionSiteCount_eq_zero
          hdata (by decide) hzero23,
        EvenKempeFusionLens.cbCombinedSignedTransfer_eq_diagonal_of_rejected_of_fusionSiteCounts_eq_zero
          graphData data lens01 lens23 hab hac hbc site hfalse
            hzero01 hzero23⟩)
    · exact Or.inr (Or.inl
        (lens23.exists_shorter_primalCircuit_of_fusionSiteCount_pos
          hdata hab hac hbc (Nat.pos_of_ne_zero hzero23)))
  · exact Or.inl
      (lens01.exists_shorter_primalCircuit_of_fusionSiteCount_pos
        hdata hab hac hbc (Nat.pos_of_ne_zero hzero01))

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
