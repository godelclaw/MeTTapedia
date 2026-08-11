import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileFaceCoordinates

/-!
# Source coverage of prefix face factors

The occurrence-level face update decomposes an outgoing fragment into old
prefix and new-Cell factors.  An old-prefix factor need not itself be open at
the incoming cut: the occurrence of the unique shared rung can be a bounded
local residue.  This file records the exact source-local alternative.  Every
old-prefix factor contributing to an outgoing boundary fragment either meets
one of the two incoming source crossings or contains the shared rung.

No arbitrary internal fragment is promoted to a finite-profile coordinate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CubicFaceBoundaryAdjacency
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceSliceFragments
open GoertzelV24TerminalProfileRegionalCoverage
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileFactorCoverageEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- Old-prefix fragments contributing occurrences to one composed outgoing
fragment. -/
noncomputable def localLayerLeftFactorFragments
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :=
  faceRegionalFactorFragments
    embedded.cellulation.rotation.toRotationSystem
    (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
      fragment.1.1)
    (aligned.toInterface.localLayerLeftPrefixRegion ∪
      aligned.toInterface.localLayerCellBoundaryRegion)
    aligned.toInterface.localLayerLeftPrefixRegion fragment.2.1

/-- A contributing old-prefix factor is either an honest incoming-profile
fragment, witnessed by one of the two incoming crossings, or the bounded
shared-rung residue.  The latter alternative is essential: in general it
cannot be promoted to an incoming boundary-fragment coordinate. -/
theorem localLayerLeftFactorFragment_touches_prefixCut_or_contains_sharedRung
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factorFragment : FaceRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        fragment.1.1)
      aligned.toInterface.localLayerLeftPrefixRegion)
    (hfactor : factorFragment ∈
      aligned.localLayerLeftFactorFragments fragment) :
    (∃ step : Fin 2,
        aligned.toInterface.localLayerPrefixCrossing step ∈
          faceRegionalFragmentEdges
            embedded.cellulation.rotation.toRotationSystem
            (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
              fragment.1.1)
            aligned.toInterface.localLayerLeftPrefixRegion factorFragment) ∨
      aligned.toInterface.localLayerSharedRungEdge ∈
        faceRegionalFragmentEdges
          embedded.cellulation.rotation.toRotationSystem
          (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
            fragment.1.1)
          aligned.toInterface.localLayerLeftPrefixRegion factorFragment := by
  let interface := aligned.toInterface
  let RS := embedded.cellulation.rotation.toRotationSystem
  let root := orbitFaceRoot RS fragment.1.1
  let leftRegion := interface.localLayerLeftPrefixRegion
  let cellRegion := interface.localLayerCellBoundaryRegion
  let largeRegion := leftRegion ∪ cellRegion
  let cut := indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing
  rcases (mem_faceRegionalFactorFragments_iff RS root largeRegion leftRegion
      fragment.2.1 factorFragment).1 hfactor with
    ⟨anchor, hanchorFactor, hanchorLarge⟩
  rcases (mem_faceRegionalFragmentPositions_iff RS root largeRegion
      fragment.2.1 anchor).1 hanchorLarge with
    ⟨anchorLarge, hanchorLargeSupp, hanchorLargeValue⟩
  let target := boundaryRegionalFragmentCutPosition RS cut largeRegion fragment
  have htargetLarge :=
    boundaryRegionalFragmentCutPosition_mem RS cut largeRegion fragment
  rcases (mem_faceRegionalFragmentPositions_iff RS root largeRegion
      fragment.2.1 target).1 htargetLarge with
    ⟨targetLarge, htargetLargeSupp, htargetLargeValue⟩
  have htargetCut : faceCycleEdge RS root target ∈ cut := by
    rw [boundaryRegionalFragmentCutPosition_edge]
    exact boundaryRegionalFragmentCutEdge_mem_cut RS cut largeRegion fragment
  rcases (mem_indexedCrossingEdgeSet_iff
      interface.nextLocalLayerPrefixCrossing
      (faceCycleEdge RS root target)).1 htargetCut with
    ⟨targetStep, htargetStep⟩
  have htargetNotLeft : faceCycleEdge RS root target ∉ leftRegion := by
    rw [← htargetStep]
    exact aligned.nextLocalLayerPrefixCrossing_not_mem_leftPrefixRegion
      targetStep
  have htargetNotFactor : target ∉
      faceRegionalFragmentPositions RS root leftRegion factorFragment := by
    intro htargetFactor
    rcases (mem_faceRegionalFragmentPositions_iff RS root leftRegion
        factorFragment target).1 htargetFactor with
      ⟨targetFactor, _htargetFactorSupp, htargetFactorValue⟩
    apply htargetNotLeft
    have htargetFactorRegion := targetFactor.2
    rw [mem_faceRegionalPositions_iff] at htargetFactorRegion
    simpa [htargetFactorValue] using htargetFactorRegion
  have hreachable := faceRegionalFragment_reachable RS root largeRegion
    fragment.2.1 hanchorLargeSupp htargetLargeSupp
  rcases hreachable with ⟨walk⟩
  let factorPositions : Set (FaceRegionalPosition RS root largeRegion) :=
    {position | position.1 ∈
      faceRegionalFragmentPositions RS root leftRegion factorFragment}
  have hanchorIn : anchorLarge ∈ factorPositions := by
    change anchorLarge.1 ∈
      faceRegionalFragmentPositions RS root leftRegion factorFragment
    simpa [hanchorLargeValue] using hanchorFactor
  have htargetOut : targetLarge ∉ factorPositions := by
    intro htargetIn
    apply htargetNotFactor
    change targetLarge.1 ∈
      faceRegionalFragmentPositions RS root leftRegion factorFragment at htargetIn
    simpa [htargetLargeValue] using htargetIn
  rcases walk.exists_boundary_dart factorPositions hanchorIn htargetOut with
    ⟨boundaryDart, _hboundaryDartWalk, hleftFactor, hrightNotFactor⟩
  rcases (mem_faceRegionalFragmentPositions_iff RS root leftRegion
      factorFragment boundaryDart.fst.1).1 hleftFactor with
    ⟨leftFactor, hleftFactorSupp, hleftFactorValue⟩
  have hrightNotLeft : faceCycleEdge RS root boundaryDart.snd.1 ∉
      leftRegion := by
    intro hrightLeft
    let rightFactor : FaceRegionalPosition RS root leftRegion :=
      ⟨boundaryDart.snd.1,
        (mem_faceRegionalPositions_iff RS root leftRegion
          boundaryDart.snd.1).2 hrightLeft⟩
    have hadjFactor :
        (faceRegionalPositionGraph RS root leftRegion).Adj leftFactor
          rightFactor := by
      change (faceCyclePositionGraph RS root).Adj leftFactor.1
        boundaryDart.snd.1
      rw [hleftFactorValue]
      exact boundaryDart.2
    have hleftComponent :
        (faceRegionalPositionGraph RS root leftRegion).connectedComponentMk
            leftFactor = factorFragment :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff factorFragment leftFactor).1
        hleftFactorSupp
    have hrightComponent :
        (faceRegionalPositionGraph RS root leftRegion).connectedComponentMk
            rightFactor = factorFragment :=
      (SimpleGraph.ConnectedComponent.sound hadjFactor.symm.reachable).trans
        hleftComponent
    have hrightFactor : rightFactor ∈ factorFragment.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff factorFragment rightFactor).2
        hrightComponent
    apply hrightNotFactor
    change boundaryDart.snd.1 ∈
      faceRegionalFragmentPositions RS root leftRegion factorFragment
    exact (mem_faceRegionalFragmentPositions_iff RS root leftRegion
      factorFragment boundaryDart.snd.1).2
      ⟨rightFactor, hrightFactor, rfl⟩
  have hleftRegion : faceCycleEdge RS root boundaryDart.fst.1 ∈ leftRegion := by
    have hleftFactorRegion := leftFactor.2
    rw [mem_faceRegionalPositions_iff] at hleftFactorRegion
    simpa [hleftFactorValue] using hleftFactorRegion
  have hrightLarge : faceCycleEdge RS root boundaryDart.snd.1 ∈
      largeRegion := by
    have hrightLargeRegion := boundaryDart.snd.2
    rw [mem_faceRegionalPositions_iff] at hrightLargeRegion
    exact hrightLargeRegion
  by_cases hleftCell : faceCycleEdge RS root boundaryDart.fst.1 ∈ cellRegion
  · right
    have hinter : faceCycleEdge RS root boundaryDart.fst.1 ∈
        leftRegion ∩ cellRegion := Finset.mem_inter.2 ⟨hleftRegion, hleftCell⟩
    have hshared : faceCycleEdge RS root boundaryDart.fst.1 =
        interface.localLayerSharedRungEdge := by
      rw [interface.localLayerLeftPrefixRegion_inter_cellBoundary_eq_singleton]
        at hinter
      exact Finset.mem_singleton.1 hinter
    exact (mem_faceRegionalFragmentEdges_iff RS root leftRegion factorFragment
      interface.localLayerSharedRungEdge).2
      ⟨boundaryDart.fst.1, hleftFactor, hshared⟩
  · left
    have hrightCell : faceCycleEdge RS root boundaryDart.snd.1 ∈ cellRegion := by
      rcases Finset.mem_union.1 hrightLarge with hrightLeft | hrightCell
      · exact (hrightNotLeft hrightLeft).elim
      · exact hrightCell
    have hfaceAdj : (faceCyclePositionGraph RS root).Adj
        boundaryDart.fst.1 boundaryDart.snd.1 := by
      exact boundaryDart.2
    have hedgeAdj := edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
      RS hcubic hrotation root hfaceAdj
    rcases aligned.exists_crossing_step_of_left_only_right_only_adj
        hcubic hrotation hleftRegion hleftCell hrightCell hrightNotLeft
          hedgeAdj with
      ⟨step, hleftCrossing, _hrightCrossing⟩
    refine ⟨step, ?_⟩
    exact (mem_faceRegionalFragmentEdges_iff RS root leftRegion factorFragment
      (interface.localLayerPrefixCrossing step)).2
      ⟨boundaryDart.fst.1, hleftFactor, hleftCrossing⟩

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
