import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileFactorCaps

/-!
# The shared-rung prefix-factor residue

The old-prefix factor coverage theorem has one non-profile alternative: a
factor may contain the rung shared with the newly exposed source hexagon.
This file proves that such a factor is not an unbounded hidden state.  Its
named face is the new hexagon, so its old-prefix edge support is exactly the
singleton shared rung and its cap-at-five value is one.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceCapUpdate
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileFactorResidueEdgeSetDecidableEq :
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

/-- A contributing factor containing the shared rung is carried by the newly
exposed hexagon's ambient face. -/
theorem localLayerLeftFactor_face_eq_nextCenter_of_containsSharedRung
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment)
    (hshared :
      aligned.LocalLayerLeftFactorContainsSharedRung fragment factor) :
    fragment.1.1 = aligned.toInterface.nextCenterLayerFace.1 := by
  let interface := aligned.toInterface
  let RS := embedded.cellulation.rotation.toRotationSystem
  let cut := indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing
  let largeRegion := interface.localLayerLeftPrefixRegion ∪
    interface.localLayerCellBoundaryRegion
  let outgoingEdge :=
    boundaryRegionalFragmentCutEdge RS cut largeRegion fragment
  have houtgoingFragment : outgoingEdge ∈
      boundaryRegionalFragmentEdges RS cut largeRegion fragment :=
    boundaryRegionalFragmentCutEdge_mem_fragment RS cut largeRegion fragment
  have houtgoingFace : outgoingEdge ∈ orbitFaceBoundary RS fragment.1.1 :=
    (Finset.mem_inter.1
      (boundaryRegionalFragmentEdges_subset_boundary_inter_region RS cut
        largeRegion fragment houtgoingFragment)).1
  have houtgoingCut : outgoingEdge ∈ cut :=
    boundaryRegionalFragmentCutEdge_mem_cut RS cut largeRegion fragment
  rcases (mem_indexedCrossingEdgeSet_iff
      interface.nextLocalLayerPrefixCrossing outgoingEdge).1 houtgoingCut with
    ⟨step, hstep⟩
  have houtgoingCell : outgoingEdge ∈
      interface.localLayerCellBoundaryRegion := by
    rw [← hstep]
    exact aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion step
  have houtgoingNext : outgoingEdge ∈
      orbitFaceBoundary RS interface.nextCenterLayerFace.1 := by
    simpa [SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
      RS] using houtgoingCell
  have hsharedFace : interface.localLayerSharedRungEdge ∈
      orbitFaceBoundary RS fragment.1.1 := by
    have hvalid := faceRegionalFragmentEdges_subset_boundary_inter_region RS
      (orbitFaceRoot RS fragment.1.1)
      interface.localLayerLeftPrefixRegion factor hshared
    simpa using (Finset.mem_inter.1 hvalid).1
  have hsharedNext : interface.localLayerSharedRungEdge ∈
      orbitFaceBoundary RS interface.nextCenterLayerFace.1 := by
    simpa [SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
      RS] using interface.localLayerSharedRungEdge_mem_cellBoundary
  by_contra hface
  have outgoingInterior : outgoingEdge ∈
      interiorEdgeSupport (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) := by
    apply (mem_interiorEdgeSupport_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
    exact ⟨Finset.mem_biUnion.2
        ⟨fragment.1.1, Finset.mem_univ _, houtgoingFace⟩,
      orbitFace_totalIncidenceCount_eq_two_of_twoSided RS htwoSided
        outgoingEdge⟩
  have sharedInterior : interface.localLayerSharedRungEdge ∈
      interiorEdgeSupport (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) := by
    apply (mem_interiorEdgeSupport_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
    exact ⟨Finset.mem_biUnion.2
        ⟨fragment.1.1, Finset.mem_univ _, hsharedFace⟩,
      orbitFace_totalIncidenceCount_eq_two_of_twoSided RS htwoSided
        interface.localLayerSharedRungEdge⟩
  have outgoingShared : outgoingEdge ∈
      sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) fragment.1.1
        interface.nextCenterLayerFace.1 :=
    (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
      ⟨outgoingInterior, houtgoingFace, houtgoingNext⟩
  have rungShared : interface.localLayerSharedRungEdge ∈
      sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) fragment.1.1
        interface.nextCenterLayerFace.1 :=
    (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
      ⟨sharedInterior, hsharedFace, hsharedNext⟩
  have hedgeEq : outgoingEdge = interface.localLayerSharedRungEdge :=
    (Finset.card_le_one_iff.1
      (hunique fragment.1.1 (Finset.mem_univ _)
        interface.nextCenterLayerFace.1 (Finset.mem_univ _) hface))
      outgoingShared rungShared
  exact aligned.nextLocalLayerPrefixCrossing_ne_sharedRungEdge step
    (hstep.trans hedgeEq)

/-- Consequently the residue's complete edge support is the shared rung and
nothing else. -/
theorem localLayerLeftFactorEdges_eq_singleton_of_containsSharedRung
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment)
    (hshared :
      aligned.LocalLayerLeftFactorContainsSharedRung fragment factor) :
    aligned.localLayerLeftFactorEdges fragment factor =
      {aligned.toInterface.localLayerSharedRungEdge} := by
  let interface := aligned.toInterface
  let RS := embedded.cellulation.rotation.toRotationSystem
  have hface := aligned
    |>.localLayerLeftFactor_face_eq_nextCenter_of_containsSharedRung
      fragment factor hshared
  apply Finset.Subset.antisymm
  · intro edge hedge
    have hvalid := faceRegionalFragmentEdges_subset_boundary_inter_region RS
      (orbitFaceRoot RS fragment.1.1) interface.localLayerLeftPrefixRegion
      factor hedge
    have hedgeFace : edge ∈ orbitFaceBoundary RS fragment.1.1 := by
      simpa using (Finset.mem_inter.1 hvalid).1
    have hedgeCell : edge ∈ interface.localLayerCellBoundaryRegion := by
      simpa [SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
        RS, hface] using hedgeFace
    have hedgeBoth : edge ∈ interface.localLayerLeftPrefixRegion ∩
        interface.localLayerCellBoundaryRegion :=
      Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hvalid).2, hedgeCell⟩
    rw [interface.localLayerLeftPrefixRegion_inter_cellBoundary_eq_singleton]
      at hedgeBoth
    exact hedgeBoth
  · intro edge hedge
    have hedgeEq := Finset.mem_singleton.1 hedge
    subst edge
    exact hshared

/-- The shared-rung residue contributes the fixed occurrence cap one. -/
theorem localLayerLeftFactorPositionCap_eq_one_of_containsSharedRung
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment)
    (hshared :
      aligned.LocalLayerLeftFactorContainsSharedRung fragment factor) :
    aligned.localLayerLeftFactorPositionCap fragment factor = 1 := by
  rw [localLayerLeftFactorPositionCap,
    ← min_card_faceRegionalFragmentEdges_eq_positions
      embedded.cellulation.rotation.toRotationSystem htwoSided
      (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        fragment.1.1)
      aligned.toInterface.localLayerLeftPrefixRegion factor 5]
  change min (aligned.localLayerLeftFactorEdges fragment factor).card 5 = 1
  rw [aligned.localLayerLeftFactorEdges_eq_singleton_of_containsSharedRung
    fragment factor hshared]
  simp

/-- Every contributing old-prefix factor is therefore accounted for either
by an actual incoming cap coordinate or by the fixed local residue `1`. -/
theorem exists_localLayerLeftPrefixProfileFaceLengthCap_or_residue_eq_one
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment)
    (hfactor : factor ∈ aligned.localLayerLeftFactorFragments fragment) :
    (∃ index : aligned.LocalLayerLeftBoundaryIndex,
        (((aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor)
            |>.profile.faceLengthCap index).val) =
          aligned.localLayerLeftFactorPositionCap fragment factor) ∨
      aligned.localLayerLeftFactorPositionCap fragment factor = 1 := by
  rcases aligned.localLayerLeftFactorHasProfileCoordinate_or_containsSharedRung
      hcubic hrotation fragment factor hfactor with hcoordinate | hshared
  · exact Or.inl
      (aligned
        |>.exists_localLayerLeftPrefixProfileFaceLengthCap_eq_factorPositionCap
          color hcolor fragment factor hcoordinate)
  · exact Or.inr
      (aligned.localLayerLeftFactorPositionCap_eq_one_of_containsSharedRung
        fragment factor hshared)

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
