import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryChannel
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionZeroFusionTransfer

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality

/-- The indexed endpoint channel is mixed exactly when its Boolean endpoint
translation is nontrivial. -/
@[simp] theorem crossSideChannelEndpointFlip_eq_true_iff
    (first second : Fin 2) :
    crossSideChannelEndpointFlip first second = true ↔ first ≠ second := by
  fin_cases first <;> fin_cases second <;> decide

/-- The indexed endpoint channel is straight exactly when its Boolean
endpoint translation is trivial. -/
@[simp] theorem crossSideChannelEndpointFlip_eq_false_iff
    (first second : Fin 2) :
    crossSideChannelEndpointFlip first second = false ↔ first = second := by
  fin_cases first <;> fin_cases second <;> decide

/-- A four-state Boolean translation is the identity precisely when both
coordinate translations vanish. -/
theorem signedRoutePermutation_eq_refl_iff
    (endpointFlip routeFlip : Bool) :
    signedRoutePermutation endpointFlip routeFlip =
        Equiv.refl (Bool × Bool) ↔
      endpointFlip = false ∧ routeFlip = false := by
  constructor
  · intro hidentity
    have hvalue := congrArg
      (fun transfer : Equiv.Perm (Bool × Bool) =>
        transfer (false, false)) hidentity
    cases endpointFlip <;> cases routeFlip <;>
      simp [signedRoutePermutation, boolRoutePermutation] at hvalue ⊢
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Signed transfer contributed by the restored three-edge return. Its
endpoint bit is the indexed port translation, while the selected cut
coordinate changes across all three return edges and hence has odd route
parity. -/
def crossSideCentralReturnCutTransfer
    (first second : Fin 2) : Equiv.Perm (Bool × Bool) :=
  signedRoutePermutation
    (crossSideChannelEndpointFlip first second) true

/-- The restored return carries the selected first-side endpoint to the
selected second-side endpoint and reverses the binary cut side. -/
@[simp] theorem crossSideCentralReturnCutTransfer_apply
    (first second : Fin 2) (route : Bool) :
    crossSideCentralReturnCutTransfer first second
        (finTwoEquiv first, route) =
      (finTwoEquiv second, !route) := by
  fin_cases first <;> fin_cases second <;> cases route <;> rfl

/-- Close the diagonal rejected-cross transfer by the restored return. -/
def rejectedCrossCentralReturnClosedTransfer
    (first second : Fin 2) : Equiv.Perm (Bool × Bool) :=
  crossSideCentralReturnCutTransfer first second *
    signedRoutePermutation true true

/-- The odd return parity cancels the rejected cross's route flip. Only the
residual endpoint translation remains. -/
theorem rejectedCrossCentralReturnClosedTransfer_eq_endpointOnly
    (first second : Fin 2) :
    rejectedCrossCentralReturnClosedTransfer first second =
      signedRoutePermutation
        (Bool.xor true (crossSideChannelEndpointFlip first second)) false := by
  rw [rejectedCrossCentralReturnClosedTransfer,
    crossSideCentralReturnCutTransfer,
    ← signedRoutePermutation_xor true
      (crossSideChannelEndpointFlip first second) true true]
  rfl

/-- A rejected diagonal cross closes with trivial signed transfer exactly
in one of the two mixed cross-side port channels. -/
@[simp] theorem rejectedCrossCentralReturnClosedTransfer_eq_refl_iff
    (first second : Fin 2) :
    rejectedCrossCentralReturnClosedTransfer first second =
        Equiv.refl (Bool × Bool) ↔
      first ≠ second := by
  rw [rejectedCrossCentralReturnClosedTransfer_eq_endpointOnly,
    signedRoutePermutation_eq_refl_iff]
  fin_cases first <;> fin_cases second <;> decide

/-- Scalar cut parity along the three restored return edges, in traversal
order from the second side back to the first side. -/
def CrossCentralExactFaceCutPair.centralReturnCoordinateParity
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (coordinate : Bool) (first second : Fin 2) : F2 :=
  crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile
        (boundaryEdge data (secondSidePort second))) +
    crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile (centralEdge data)) +
    crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile
        (boundaryEdge data (firstSidePort first)))

private theorem f2_eq_one_of_ne_zero
    (value : F2) (hvalue : value ≠ 0) : value = 1 := by
  fin_cases value
  · exact False.elim (hvalue rfl)
  · rfl

/-- Nonzero selected values on the two boundary edges and central edge make
the restored return's scalar cut parity odd. -/
theorem CrossCentralExactFaceCutPair.centralReturnCoordinateParity_eq_one
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (coordinate : Bool) (first second : Fin 2)
    (hcentral : crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile (centralEdge data)) ≠ 0)
    (hfirst : crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile
        (boundaryEdge data (firstSidePort first))) ≠ 0)
    (hsecond : crossFaceCoordinate coordinate
      (pair.crossFaceDifferenceProfile
        (boundaryEdge data (secondSidePort second))) ≠ 0) :
    pair.centralReturnCoordinateParity coordinate first second = 1 := by
  rw [CrossCentralExactFaceCutPair.centralReturnCoordinateParity,
    f2_eq_one_of_ne_zero _ hsecond,
    f2_eq_one_of_ne_zero _ hcentral,
    f2_eq_one_of_ne_zero _ hfirst]
  decide

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The exact difference channel comes with the complete restored-return
transfer calculation: the return has odd cut parity, and after composing
with a rejected diagonal cross the closed transfer is trivial exactly when
the channel endpoints are mixed. -/
theorem CrossCentralExactFaceCutPair.exists_exactCrossSideClosedTransfer
    {graphData : SimpleGraphDartRotation.Data G}
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
        crossSideCentralReturnCutTransfer firstIndex secondIndex
            (finTwoEquiv firstIndex, coordinate) =
          (finTwoEquiv secondIndex, !coordinate) ∧
        (rejectedCrossCentralReturnClosedTransfer firstIndex secondIndex =
            Equiv.refl (Bool × Bool) ↔
          firstIndex ≠ secondIndex) := by
  rcases pair.exists_exactCrossSideCoordinateChannelClosure minimal with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      hcentral, hfirstExact, hsecondExact, _hsupport, hcycle,
      _hendpoint⟩
  have hfirst := (hfirstExact firstIndex).2 rfl
  have hsecond := (hsecondExact secondIndex).2 rfl
  exact ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hfirstExact, hsecondExact, hcycle,
    pair.centralReturnCoordinateParity_eq_one coordinate firstIndex
      secondIndex hcentral hfirst hsecond,
    crossSideCentralReturnCutTransfer_apply firstIndex secondIndex coordinate,
    rejectedCrossCentralReturnClosedTransfer_eq_refl_iff
      firstIndex secondIndex⟩

/-- In the zero-fusion `bc` normal form, closing the actual combined rejected
cross transfer by an indexed restored return is trivial exactly for a mixed
endpoint channel. -/
theorem EvenKempeFusionLens.bcCentralReturn_mul_combinedSignedTransfer_eq_refl_iff
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
    (hzero23 : lens23.fusionSiteCount = 0)
    (first second : Fin 2) :
    crossSideCentralReturnCutTransfer first second *
          EvenKempeFusionLens.bcCombinedSignedTransfer
            lens01 graphData lens23 hab hac hbc site =
        Equiv.refl (Bool × Bool) ↔
      first ≠ second := by
  rw [EvenKempeFusionLens.bcCombinedSignedTransfer_eq_diagonal_of_rejected_of_fusionSiteCounts_eq_zero
    graphData data lens01 lens23 hab hac hbc site hfalse hzero01 hzero23]
  exact rejectedCrossCentralReturnClosedTransfer_eq_refl_iff first second

/-- The complementary zero-fusion `cb` normal form has the same exact
restored-return compensation law. -/
theorem EvenKempeFusionLens.cbCentralReturn_mul_combinedSignedTransfer_eq_refl_iff
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
    (hzero23 : lens23.fusionSiteCount = 0)
    (first second : Fin 2) :
    crossSideCentralReturnCutTransfer first second *
          EvenKempeFusionLens.cbCombinedSignedTransfer
            lens01 graphData lens23 hab hac hbc site =
        Equiv.refl (Bool × Bool) ↔
      first ≠ second := by
  rw [EvenKempeFusionLens.cbCombinedSignedTransfer_eq_diagonal_of_rejected_of_fusionSiteCounts_eq_zero
    graphData data lens01 lens23 hab hac hbc site hfalse hzero01 hzero23]
  exact rejectedCrossCentralReturnClosedTransfer_eq_refl_iff first second

/-- A rejected zero-fusion `bc` cross supplies an exact cross-avoiding
difference cycle together with the compensation criterion for its actual
combined signed transfer. -/
theorem EvenKempeFusionLens.exists_bcExactCrossSideClosedTransfer_of_rejected_of_zeroFusion
    (graphData : SimpleGraphDartRotation.Data G)
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
        (crossSideCentralReturnCutTransfer firstIndex secondIndex *
              EvenKempeFusionLens.bcCombinedSignedTransfer
                lens01 graphData lens23 hab hac hbc site =
            Equiv.refl (Bool × Bool) ↔
          firstIndex ≠ secondIndex) := by
  rcases EvenKempeFusionLens.exists_bcCrossCentralExactFaceCutPair_of_rejected
      graphData minimal data lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount site hfalse with
    ⟨pair, _hprefixEdges, _hsuffixEdges⟩
  rcases pair.exists_exactCrossSideClosedTransfer minimal with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      _hfirstExact, _hsecondExact, hcycle, hparity,
      _hreturnApply, _hclosed⟩
  exact ⟨pair, coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hcycle, hparity,
    EvenKempeFusionLens.bcCentralReturn_mul_combinedSignedTransfer_eq_refl_iff
      graphData data lens01 lens23 hab hac hbc site hfalse hzero01 hzero23
        firstIndex secondIndex⟩

/-- The complementary rejected zero-fusion `cb` cross supplies the same
exact difference cycle and closed-transfer compensation criterion. -/
theorem EvenKempeFusionLens.exists_cbExactCrossSideClosedTransfer_of_rejected_of_zeroFusion
    (graphData : SimpleGraphDartRotation.Data G)
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
        (crossSideCentralReturnCutTransfer firstIndex secondIndex *
              EvenKempeFusionLens.cbCombinedSignedTransfer
                lens01 graphData lens23 hab hac hbc site =
            Equiv.refl (Bool × Bool) ↔
          firstIndex ≠ secondIndex) := by
  rcases EvenKempeFusionLens.exists_cbCrossCentralExactFaceCutPair_of_rejected
      graphData minimal data lens01 lens23 hdata hab hac hbc hbDisjoint
        hcDisjoint hcount site hfalse with
    ⟨pair, _hprefixEdges, _hsuffixEdges⟩
  rcases pair.exists_exactCrossSideClosedTransfer minimal with
    ⟨coordinate, firstIndex, secondIndex, path, hpath, hcross,
      _hfirstExact, _hsecondExact, hcycle, hparity,
      _hreturnApply, _hclosed⟩
  exact ⟨pair, coordinate, firstIndex, secondIndex, path, hpath, hcross,
    hcycle, hparity,
    EvenKempeFusionLens.cbCentralReturn_mul_combinedSignedTransfer_eq_refl_iff
      graphData data lens01 lens23 hab hac hbc site hfalse hzero01 hzero23
        firstIndex secondIndex⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
