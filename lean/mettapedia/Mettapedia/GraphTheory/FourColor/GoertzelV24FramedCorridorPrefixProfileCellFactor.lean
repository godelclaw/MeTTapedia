import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileFactorResidue
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideBoundaryFragmentCoverage

/-!
# The newly exposed hexagon's face-factor contribution

The cumulative source-prefix update adjoins the complete boundary of the next
central hexagon.  This boundary is not identified with the complementary
two-vertex open tangle around the shared rung.  Its occurrence-sensitive face
contribution is instead computed directly from the source geometry.

For an outgoing boundary fragment carried by the new hexagon itself, the Cell
slice is the complete six-position facial cycle and hence has cap five.  For
any other named face, pairwise uniqueness of shared interior edges makes the
Cell slice the singleton selected by the outgoing cut edge, and its cap is one.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceCapUpdate
open GoertzelV24TerminalProfileFaceSliceFragments
open GoertzelV24VertexSideBoundaryFragmentCoverage
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileCellFactorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- If a region contains the complete boundary of the named face, its induced
cyclic-position graph is preconnected. -/
private theorem faceRegionalPositionGraph_preconnected_of_boundary_subset
    (RS : RotationSystem V G.edgeSet) (root : RS.D)
    (region : Finset G.edgeSet)
    (hboundary : orbitFaceBoundary RS (dartOrbitFace RS root) ⊆ region) :
    (faceRegionalPositionGraph RS root region).Preconnected := by
  let liftPosition : Fin (RS.faceOrbit root).card →
      FaceRegionalPosition RS root region :=
    fun position =>
      ⟨position, (mem_faceRegionalPositions_iff RS root region position).2
        (hboundary (faceCycleEdge_mem RS root position))⟩
  let liftHom : faceCyclePositionGraph RS root →g
      faceRegionalPositionGraph RS root region :=
    { toFun := liftPosition
      map_rel' := by
        intro left right hadj
        exact hadj }
  apply (faceCyclePositionGraph_preconnected RS root).map liftHom
  intro position
  refine ⟨position.1, ?_⟩
  exact Subtype.ext rfl

/-- If a region contains a whole face boundary, every cyclic position belongs
to each (necessarily unique) regional fragment. -/
private theorem faceRegionalFragmentPositions_eq_univ_of_boundary_subset
    (RS : RotationSystem V G.edgeSet) (root : RS.D)
    (region : Finset G.edgeSet)
    (hboundary : orbitFaceBoundary RS (dartOrbitFace RS root) ⊆ region)
    (fragment : FaceRegionalFragment RS root region) :
    faceRegionalFragmentPositions RS root region fragment = Finset.univ := by
  have hpreconnected :=
    faceRegionalPositionGraph_preconnected_of_boundary_subset
      RS root region hboundary
  have hsubsingleton :
      Subsingleton (FaceRegionalFragment RS root region) :=
    hpreconnected.subsingleton_connectedComponent
  ext position
  simp only [Finset.mem_univ, iff_true]
  let regionalPosition : FaceRegionalPosition RS root region :=
    ⟨position, (mem_faceRegionalPositions_iff RS root region position).2
      (hboundary (faceCycleEdge_mem RS root position))⟩
  apply (mem_faceRegionalFragmentPositions_iff RS root region fragment
    position).2
  refine ⟨regionalPosition, ?_, rfl⟩
  apply (SimpleGraph.ConnectedComponent.mem_supp_iff fragment
    regionalPosition).2
  exact @Subsingleton.elim _ hsubsingleton _ _

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

/-- The part of an outgoing fragment contributed by the complete boundary of
the newly exposed hexagon.  Naming this dependent carrier once keeps later
statements small. -/
noncomputable def localLayerCellFactorPositionSlice
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :=
  faceRegionalFragmentPositionSlice
    embedded.cellulation.rotation.toRotationSystem
    (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
      fragment.1.1)
    (aligned.toInterface.localLayerLeftPrefixRegion ∪
      aligned.toInterface.localLayerCellBoundaryRegion)
    aligned.toInterface.localLayerCellBoundaryRegion fragment.2.1

/-- The literal occurrence overlap of the old-prefix and new-hexagon slices.
The two edge regions meet only on the shared rung, but this definition retains
the actual occurrence until two-sidedness is used. -/
noncomputable def localLayerFactorPositionOverlap
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :=
  faceRegionalFragmentPositionSlice
      embedded.cellulation.rotation.toRotationSystem
      (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        fragment.1.1)
      (aligned.toInterface.localLayerLeftPrefixRegion ∪
        aligned.toInterface.localLayerCellBoundaryRegion)
      aligned.toInterface.localLayerLeftPrefixRegion fragment.2.1 ∩
    aligned.localLayerCellFactorPositionSlice fragment

/-- The occurrence slice contributed by the newly exposed hexagon has six
positions on that hexagon's own face and one position on every other outgoing
face. -/
theorem localLayerCellFactorPositionSlice_card_eq_ite
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :
    (aligned.localLayerCellFactorPositionSlice fragment).card =
      if fragment.1.1 = aligned.toInterface.nextCenterLayerFace.1 then 6
      else 1 := by
  let interface := aligned.toInterface
  let RS := embedded.cellulation.rotation.toRotationSystem
  let root := orbitFaceRoot RS fragment.1.1
  let cut := indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing
  let largeRegion := interface.localLayerLeftPrefixRegion ∪
    interface.localLayerCellBoundaryRegion
  let cellRegion := interface.localLayerCellBoundaryRegion
  let selectedPosition :=
    boundaryRegionalFragmentCutPosition RS cut largeRegion fragment
  change (faceRegionalFragmentPositionSlice RS root largeRegion cellRegion
    fragment.2.1).card = _
  by_cases hface : fragment.1.1 = interface.nextCenterLayerFace.1
  · rw [if_pos hface]
    have hboundary : orbitFaceBoundary RS (dartOrbitFace RS root) ⊆
        largeRegion := by
      intro edge hedge
      apply Finset.mem_union_right
      simpa [cellRegion, SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
        root, hface] using hedge
    have hpositions : faceRegionalFragmentPositions RS root largeRegion
        fragment.2.1 = Finset.univ :=
      faceRegionalFragmentPositions_eq_univ_of_boundary_subset
        RS root largeRegion hboundary fragment.2.1
    have hedgeCell : ∀ position,
        faceCycleEdge RS root position ∈ cellRegion := by
      intro position
      simpa [cellRegion, SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
        root, hface] using faceCycleEdge_mem RS root position
    have hslice : faceRegionalFragmentPositionSlice RS root largeRegion
        cellRegion fragment.2.1 = Finset.univ := by
      ext position
      simp [faceRegionalFragmentPositionSlice, hpositions,
        hedgeCell position]
    have horbit : (RS.faceOrbit root).card = 6 := by
      calc
        (RS.faceOrbit root).card =
            (orbitFaceDarts RS (dartOrbitFace RS root)).card := by
          rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
        _ = (orbitFaceBoundary RS (dartOrbitFace RS root)).card := by
          exact (orbitFaceBoundarySimple_of_twoSided RS htwoSided
            (dartOrbitFace RS root)).symm
        _ = (orbitFaceBoundary RS interface.nextCenterLayerFace.1).card := by
          rw [show dartOrbitFace RS root = fragment.1.1 by simp [root], hface]
        _ = 6 := interface.nextCenterLayerFace_boundary_card_eq_six
    change (faceRegionalFragmentPositionSlice RS root largeRegion cellRegion
      fragment.2.1).card = 6
    calc
      (faceRegionalFragmentPositionSlice RS root largeRegion cellRegion
          fragment.2.1).card = (Finset.univ :
            Finset (Fin (RS.faceOrbit root).card)).card :=
        congrArg Finset.card hslice
      _ = 6 := by simp [horbit]
  · rw [if_neg hface]
    have hselectedLarge : selectedPosition ∈
        faceRegionalFragmentPositions RS root largeRegion fragment.2.1 := by
      exact boundaryRegionalFragmentCutPosition_mem RS cut largeRegion fragment
    have hselectedCut : boundaryRegionalFragmentCutEdge RS cut largeRegion
        fragment ∈ cut :=
      boundaryRegionalFragmentCutEdge_mem_cut RS cut largeRegion fragment
    rcases (mem_indexedCrossingEdgeSet_iff
      interface.nextLocalLayerPrefixCrossing
      (boundaryRegionalFragmentCutEdge RS cut largeRegion fragment)).1
        hselectedCut with ⟨step, hstep⟩
    have hselectedCell : faceCycleEdge RS root selectedPosition ∈
        cellRegion := by
      rw [boundaryRegionalFragmentCutPosition_edge, ← hstep]
      exact aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion step
    have hselectedSlice : selectedPosition ∈
        faceRegionalFragmentPositionSlice RS root largeRegion cellRegion
          fragment.2.1 :=
      Finset.mem_filter.2 ⟨hselectedLarge, hselectedCell⟩
    have hslice : faceRegionalFragmentPositionSlice RS root largeRegion
        cellRegion fragment.2.1 = {selectedPosition} := by
      apply Finset.Subset.antisymm
      · intro position hposition
        rcases Finset.mem_filter.1 hposition with
          ⟨_hpositionLarge, hpositionCell⟩
        have hpositionFace : faceCycleEdge RS root position ∈
            orbitFaceBoundary RS fragment.1.1 := by
          simpa [root] using faceCycleEdge_mem RS root position
        have hpositionNext : faceCycleEdge RS root position ∈
            orbitFaceBoundary RS interface.nextCenterLayerFace.1 := by
          simpa [cellRegion,
            SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
            RS] using hpositionCell
        have hselectedFace : faceCycleEdge RS root selectedPosition ∈
            orbitFaceBoundary RS fragment.1.1 := by
          simpa [root] using faceCycleEdge_mem RS root selectedPosition
        have hselectedNext : faceCycleEdge RS root selectedPosition ∈
            orbitFaceBoundary RS interface.nextCenterLayerFace.1 := by
          simpa [cellRegion,
            SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
            RS] using hselectedCell
        have hpositionInterior : faceCycleEdge RS root position ∈
            interiorEdgeSupport (orbitFaceBoundary RS)
              (Finset.univ : Finset (OrbitFace RS)) := by
          apply (mem_interiorEdgeSupport_iff (orbitFaceBoundary RS)
            (Finset.univ : Finset (OrbitFace RS))).2
          exact ⟨Finset.mem_biUnion.2
              ⟨fragment.1.1, Finset.mem_univ _, hpositionFace⟩,
            orbitFace_totalIncidenceCount_eq_two_of_twoSided RS htwoSided _⟩
        have hselectedInterior : faceCycleEdge RS root selectedPosition ∈
            interiorEdgeSupport (orbitFaceBoundary RS)
              (Finset.univ : Finset (OrbitFace RS)) := by
          apply (mem_interiorEdgeSupport_iff (orbitFaceBoundary RS)
            (Finset.univ : Finset (OrbitFace RS))).2
          exact ⟨Finset.mem_biUnion.2
              ⟨fragment.1.1, Finset.mem_univ _, hselectedFace⟩,
            orbitFace_totalIncidenceCount_eq_two_of_twoSided RS htwoSided _⟩
        have hpositionShared : faceCycleEdge RS root position ∈
            sharedInteriorEdges (orbitFaceBoundary RS)
              (Finset.univ : Finset (OrbitFace RS)) fragment.1.1
                interface.nextCenterLayerFace.1 :=
          (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
            (Finset.univ : Finset (OrbitFace RS))).2
              ⟨hpositionInterior, hpositionFace, hpositionNext⟩
        have hselectedShared : faceCycleEdge RS root selectedPosition ∈
            sharedInteriorEdges (orbitFaceBoundary RS)
              (Finset.univ : Finset (OrbitFace RS)) fragment.1.1
                interface.nextCenterLayerFace.1 :=
          (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
            (Finset.univ : Finset (OrbitFace RS))).2
              ⟨hselectedInterior, hselectedFace, hselectedNext⟩
        have hedge : faceCycleEdge RS root position =
            faceCycleEdge RS root selectedPosition :=
          (Finset.card_le_one_iff.1
            (hunique fragment.1.1 (Finset.mem_univ _)
              interface.nextCenterLayerFace.1 (Finset.mem_univ _) hface))
            hpositionShared hselectedShared
        exact Finset.mem_singleton.2
          (faceCycleEdge_injective RS htwoSided root hedge)
      · intro position hposition
        rw [Finset.mem_singleton] at hposition
        simpa [hposition] using hselectedSlice
    change (faceRegionalFragmentPositionSlice RS root largeRegion cellRegion
      fragment.2.1).card = 1
    rw [hslice]
    simp

/-- The finite cap contributed by the newly exposed hexagon is therefore a
two-valued geometric coordinate: five on the hexagon itself and one on every
other outgoing face. -/
theorem localLayerCellFactorFragmentCapSum_eq_ite
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :
    aligned.toInterface.localLayerFactorFragmentCapSum
        aligned.toInterface.localLayerCellBoundaryRegion fragment =
      if fragment.1.1 = aligned.toInterface.nextCenterLayerFace.1 then 5
      else 1 := by
  let interface := aligned.toInterface
  let RS := embedded.cellulation.rotation.toRotationSystem
  let root := orbitFaceRoot RS fragment.1.1
  let largeRegion := interface.localLayerLeftPrefixRegion ∪
    interface.localLayerCellBoundaryRegion
  change interface.localLayerFactorFragmentCapSum
      interface.localLayerCellBoundaryRegion fragment =
    if fragment.1.1 = interface.nextCenterLayerFace.1 then 5 else 1
  have hcap :=
    min_card_faceRegionalFragmentPositionSlice_eq_min_sum_fragmentCaps
      RS root largeRegion interface.localLayerCellBoundaryRegion
        Finset.subset_union_right fragment.2.1
  change min
      (faceRegionalFragmentPositionSlice RS root largeRegion
        interface.localLayerCellBoundaryRegion fragment.2.1).card 5 =
      interface.localLayerFactorFragmentCapSum
        interface.localLayerCellBoundaryRegion fragment at hcap
  rw [← hcap]
  have hslice :=
    aligned.localLayerCellFactorPositionSlice_card_eq_ite fragment
  change
    (faceRegionalFragmentPositionSlice RS root largeRegion
      interface.localLayerCellBoundaryRegion fragment.2.1).card =
        (if fragment.1.1 = interface.nextCenterLayerFace.1 then 6 else 1)
    at hslice
  rw [hslice]
  by_cases hface : fragment.1.1 = interface.nextCenterLayerFace.1
  · simp [hface]
  · simp [hface]

/-- An occurrence in both factor slices forces the outgoing fragment to be
carried by the newly exposed hexagon.  Otherwise its selected outgoing cut
edge and the shared rung would be two distinct edges shared by the same pair
of faces. -/
theorem localLayerFactorPositionOverlap_face_eq_nextCenter
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (position : Fin (embedded.cellulation.rotation.toRotationSystem.faceOrbit
      (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        fragment.1.1)).card)
    (hposition : position ∈
      aligned.localLayerFactorPositionOverlap fragment) :
    fragment.1.1 = aligned.toInterface.nextCenterLayerFace.1 := by
  let interface := aligned.toInterface
  let RS := embedded.cellulation.rotation.toRotationSystem
  let root := orbitFaceRoot RS fragment.1.1
  let cut := indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing
  let leftRegion := interface.localLayerLeftPrefixRegion
  let cellRegion := interface.localLayerCellBoundaryRegion
  let largeRegion := leftRegion ∪ cellRegion
  change position ∈
      faceRegionalFragmentPositionSlice RS root largeRegion leftRegion
          fragment.2.1 ∩
        faceRegionalFragmentPositionSlice RS root largeRegion cellRegion
          fragment.2.1 at hposition
  rcases Finset.mem_inter.1 hposition with ⟨hpositionLeft, hpositionCell⟩
  have hedgeLeft : faceCycleEdge RS root position ∈ leftRegion :=
    (Finset.mem_filter.1 hpositionLeft).2
  have hedgeCell : faceCycleEdge RS root position ∈ cellRegion :=
    (Finset.mem_filter.1 hpositionCell).2
  have hedgeBoth : faceCycleEdge RS root position ∈ leftRegion ∩ cellRegion :=
    Finset.mem_inter.2 ⟨hedgeLeft, hedgeCell⟩
  rw [interface.localLayerLeftPrefixRegion_inter_cellBoundary_eq_singleton]
    at hedgeBoth
  have hedgeRung : faceCycleEdge RS root position =
      interface.localLayerSharedRungEdge :=
    Finset.mem_singleton.1 hedgeBoth
  by_contra hface
  let selectedPosition :=
    boundaryRegionalFragmentCutPosition RS cut largeRegion fragment
  have hselectedCut : boundaryRegionalFragmentCutEdge RS cut largeRegion
      fragment ∈ cut :=
    boundaryRegionalFragmentCutEdge_mem_cut RS cut largeRegion fragment
  rcases (mem_indexedCrossingEdgeSet_iff
    interface.nextLocalLayerPrefixCrossing
      (boundaryRegionalFragmentCutEdge RS cut largeRegion fragment)).1
      hselectedCut with ⟨step, hstep⟩
  have hselectedCell : faceCycleEdge RS root selectedPosition ∈ cellRegion := by
    rw [boundaryRegionalFragmentCutPosition_edge, ← hstep]
    exact aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion step
  have hselectedFace : faceCycleEdge RS root selectedPosition ∈
      orbitFaceBoundary RS fragment.1.1 := by
    simpa [root] using faceCycleEdge_mem RS root selectedPosition
  have hselectedNext : faceCycleEdge RS root selectedPosition ∈
      orbitFaceBoundary RS interface.nextCenterLayerFace.1 := by
    simpa [cellRegion,
      SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion, RS] using
      hselectedCell
  have hrungFace : interface.localLayerSharedRungEdge ∈
      orbitFaceBoundary RS fragment.1.1 := by
    rw [← hedgeRung]
    simpa [root] using faceCycleEdge_mem RS root position
  have hrungNext : interface.localLayerSharedRungEdge ∈
      orbitFaceBoundary RS interface.nextCenterLayerFace.1 := by
    exact interface.localLayerSharedRungEdge_mem_cellBoundary
  have hselectedInterior : faceCycleEdge RS root selectedPosition ∈
      interiorEdgeSupport (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) := by
    apply (mem_interiorEdgeSupport_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
    exact ⟨Finset.mem_biUnion.2
        ⟨fragment.1.1, Finset.mem_univ _, hselectedFace⟩,
      orbitFace_totalIncidenceCount_eq_two_of_twoSided RS htwoSided _⟩
  have hrungInterior : interface.localLayerSharedRungEdge ∈
      interiorEdgeSupport (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) := by
    apply (mem_interiorEdgeSupport_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
    exact ⟨Finset.mem_biUnion.2
        ⟨fragment.1.1, Finset.mem_univ _, hrungFace⟩,
      orbitFace_totalIncidenceCount_eq_two_of_twoSided RS htwoSided _⟩
  have hselectedShared : faceCycleEdge RS root selectedPosition ∈
      sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) fragment.1.1
          interface.nextCenterLayerFace.1 :=
    (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
        ⟨hselectedInterior, hselectedFace, hselectedNext⟩
  have hrungShared : interface.localLayerSharedRungEdge ∈
      sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) fragment.1.1
          interface.nextCenterLayerFace.1 :=
    (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
        ⟨hrungInterior, hrungFace, hrungNext⟩
  have hedgeEq : faceCycleEdge RS root selectedPosition =
      interface.localLayerSharedRungEdge :=
    (Finset.card_le_one_iff.1
      (hunique fragment.1.1 (Finset.mem_univ _)
        interface.nextCenterLayerFace.1 (Finset.mem_univ _) hface))
      hselectedShared hrungShared
  exact aligned.nextLocalLayerPrefixCrossing_ne_sharedRungEdge step
    (hstep.trans
      (boundaryRegionalFragmentCutPosition_edge RS cut largeRegion fragment
        |>.symm.trans hedgeEq))

/-- The subtraction term in the one-Cell face-cap update is exactly one on
the new hexagon and zero on every other outgoing face. -/
theorem localLayerFactorFragmentOverlapCard_eq_ite
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :
    aligned.toInterface.localLayerFactorFragmentOverlapCard fragment =
      if fragment.1.1 = aligned.toInterface.nextCenterLayerFace.1 then 1
      else 0 := by
  let interface := aligned.toInterface
  let RS := embedded.cellulation.rotation.toRotationSystem
  let root := orbitFaceRoot RS fragment.1.1
  let leftRegion := interface.localLayerLeftPrefixRegion
  let cellRegion := interface.localLayerCellBoundaryRegion
  let largeRegion := leftRegion ∪ cellRegion
  change (aligned.localLayerFactorPositionOverlap fragment).card = _
  by_cases hface : fragment.1.1 = interface.nextCenterLayerFace.1
  · rw [if_pos hface]
    have hrungFace : interface.localLayerSharedRungEdge ∈
        orbitFaceBoundary RS (dartOrbitFace RS root) := by
      simpa [root, hface,
        SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion, RS] using
        interface.localLayerSharedRungEdge_mem_cellBoundary
    rcases existsUnique_faceCycleEdge_eq RS htwoSided root
      interface.localLayerSharedRungEdge hrungFace with
      ⟨rungPosition, hrungPosition, _hrungUnique⟩
    have hboundary : orbitFaceBoundary RS (dartOrbitFace RS root) ⊆
        largeRegion := by
      intro edge hedge
      apply Finset.mem_union_right
      simpa [cellRegion,
        SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
        root, hface] using hedge
    have hpositions : faceRegionalFragmentPositions RS root largeRegion
        fragment.2.1 = Finset.univ :=
      faceRegionalFragmentPositions_eq_univ_of_boundary_subset
        RS root largeRegion hboundary fragment.2.1
    have hrungLarge : rungPosition ∈
        faceRegionalFragmentPositions RS root largeRegion fragment.2.1 := by
      rw [hpositions]
      simp
    have hrungLeft : faceCycleEdge RS root rungPosition ∈ leftRegion := by
      rw [hrungPosition]
      exact interface.localLayerSharedRungEdge_mem_leftPrefix
    have hrungCell : faceCycleEdge RS root rungPosition ∈ cellRegion := by
      rw [hrungPosition]
      change interface.localLayerSharedRungEdge ∈
        interface.localLayerCellBoundaryRegion
      exact interface.localLayerSharedRungEdge_mem_cellBoundary
    have hrungOverlap : rungPosition ∈
        aligned.localLayerFactorPositionOverlap fragment := by
      change rungPosition ∈
          faceRegionalFragmentPositionSlice RS root largeRegion leftRegion
              fragment.2.1 ∩
            faceRegionalFragmentPositionSlice RS root largeRegion cellRegion
              fragment.2.1
      exact Finset.mem_inter.2
        ⟨Finset.mem_filter.2 ⟨hrungLarge, hrungLeft⟩,
          Finset.mem_filter.2 ⟨hrungLarge, hrungCell⟩⟩
    have hoverlap : aligned.localLayerFactorPositionOverlap fragment =
        {rungPosition} := by
      apply Finset.Subset.antisymm
      · intro position hposition
        change position ∈
            faceRegionalFragmentPositionSlice RS root largeRegion leftRegion
                fragment.2.1 ∩
              faceRegionalFragmentPositionSlice RS root largeRegion cellRegion
                fragment.2.1 at hposition
        rcases Finset.mem_inter.1 hposition with ⟨hleft, hcell⟩
        have hedgeBoth : faceCycleEdge RS root position ∈
            leftRegion ∩ cellRegion :=
          Finset.mem_inter.2
            ⟨(Finset.mem_filter.1 hleft).2,
              (Finset.mem_filter.1 hcell).2⟩
        rw [interface.localLayerLeftPrefixRegion_inter_cellBoundary_eq_singleton]
          at hedgeBoth
        have hedgeRung : faceCycleEdge RS root position =
            interface.localLayerSharedRungEdge :=
          Finset.mem_singleton.1 hedgeBoth
        exact Finset.mem_singleton.2
          (faceCycleEdge_injective RS htwoSided root
            (hedgeRung.trans hrungPosition.symm))
      · intro position hposition
        rw [Finset.mem_singleton] at hposition
        simpa [hposition] using hrungOverlap
    rw [hoverlap]
    simp
  · rw [if_neg hface]
    have hoverlap : aligned.localLayerFactorPositionOverlap fragment = ∅ := by
      apply Finset.Subset.antisymm
      · intro position hposition
        exact (hface
          (aligned.localLayerFactorPositionOverlap_face_eq_nextCenter
            fragment position hposition)).elim
      · exact Finset.empty_subset _
    rw [hoverlap]
    simp

/-- The exact outgoing fragment cap after adjoining one source Cell.  The
old-prefix factor sum is the only nonlocal input: the new hexagon contributes
`5` to its own face and `1` to every other outgoing face, while the common
rung is subtracted exactly on the new face. -/
theorem localLayerRightPrefixBoundaryFragment_cap_eq_cellUpdate
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :
    min (boundaryRegionalFragmentEdges
          embedded.cellulation.rotation.toRotationSystem
          (indexedCrossingEdgeSet
            aligned.toInterface.nextLocalLayerPrefixCrossing)
          (aligned.toInterface.localLayerLeftPrefixRegion ∪
            aligned.toInterface.localLayerCellBoundaryRegion)
          fragment).card 5 =
      min
        (aligned.toInterface.localLayerFactorFragmentCapSum
            aligned.toInterface.localLayerLeftPrefixRegion fragment +
          (if fragment.1.1 = aligned.toInterface.nextCenterLayerFace.1 then 5
            else 1) -
          (if fragment.1.1 = aligned.toInterface.nextCenterLayerFace.1 then 1
            else 0))
        5 := by
  rw [aligned.toInterface.localLayerRightPrefixBoundaryFragment_cap_eq_factorCaps,
    aligned.localLayerCellFactorFragmentCapSum_eq_ite,
    aligned.localLayerFactorFragmentOverlapCard_eq_ite]

/-- Coordinate form of the exact one-Cell cap update on the actual outgoing
finite profile. -/
theorem localLayerRightPrefixBoundedProfile_faceLengthCap_eq_cellUpdate
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (index : Fin (Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet
        aligned.toInterface.nextLocalLayerPrefixCrossing)
      aligned.toInterface.localLayerRightPrefixRegion))) :
    (((aligned.toInterface.localLayerRightPrefixBoundedProfile color hcolor)
        |>.profile.faceLengthCap index).val) =
      min
        (aligned.toInterface.localLayerFactorFragmentCapSum
            aligned.toInterface.localLayerLeftPrefixRegion
            (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
              index) +
          (if (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
                  index).1.1 = aligned.toInterface.nextCenterLayerFace.1 then 5
            else 1) -
          (if (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
                  index).1.1 = aligned.toInterface.nextCenterLayerFace.1 then 1
            else 0))
        5 := by
  rw [aligned.toInterface
      |>.localLayerRightPrefixBoundedProfile_faceLengthCap_eq_factorCaps,
    aligned.localLayerCellFactorFragmentCapSum_eq_ite,
    aligned.localLayerFactorFragmentOverlapCard_eq_ite]

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
