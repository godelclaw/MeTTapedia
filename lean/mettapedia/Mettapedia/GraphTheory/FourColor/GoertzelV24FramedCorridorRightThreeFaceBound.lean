import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixThreeFaceBound

/-!
# Three-face bound after one source Cell

The right cross-section of a literal source Cell is again a simple two-step
dual path through three named faces.  This module proves directly that its
cumulative-prefix boundary has at most three occurrence-sensitive face
fragments.  It is the outgoing counterpart of the established left-prefix
bound; no successor Cell and no equality with three are assumed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorPrefixProfile
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24VertexSideBoundaryFragmentCoverage
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorRightThreeFaceBoundEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

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

/-- Every orbit face meeting the two-edge right cross-section is one of the
three literal faces of its simple dual path. -/
theorem mem_nextLocalLayerPrefixCutIncidentFaces
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (face : OrbitFace embedded.cellulation.rotation.toRotationSystem)
    (hface : face ∈ cutIncidentFaces
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)) :
    face = interface.firstLayerFace.1 ∨
      face = interface.nextCenterLayerFace.1 ∨
      face = interface.secondLayerFace.1 := by
  rcases (mem_cutIncidentFaces_iff
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing) face).1 hface with
    ⟨edge, hedgeCut, hedgeFace⟩
  rcases (mem_indexedCrossingEdgeSet_iff
    interface.nextLocalLayerPrefixCrossing edge).1 hedgeCut with ⟨step, hstep⟩
  subst edge
  have hcases := orbitFace_eq_left_or_right_of_mem_dualWalkCrossingEdge
    embedded.cellulation.rotation.toRotationSystem htwoSided hunique
    interface.nextLocalLayer.walk
    (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm step) face hedgeFace
  fin_cases step
  · simp [nextLocalLayer, nextLocalLayerWalk] at hcases
    rcases hcases with hfirst | hcenter
    · exact Or.inl hfirst
    · exact Or.inr (Or.inl hcenter)
  · simp [nextLocalLayer, nextLocalLayerWalk] at hcases
    rcases hcases with hcenter | hsecond
    · exact Or.inr (Or.inl hcenter)
    · exact Or.inr (Or.inr hsecond)

/-- The displayed right cross-section meets at most three orbit faces. -/
theorem card_nextLocalLayerPrefixCutIncidentFaces_le_three
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (cutIncidentFaces embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)).card ≤ 3 := by
  let faces : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem) :=
    {interface.firstLayerFace.1, interface.nextCenterLayerFace.1,
      interface.secondLayerFace.1}
  have hsubset : cutIncidentFaces
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing) ⊆ faces := by
    intro face hface
    rcases interface.mem_nextLocalLayerPrefixCutIncidentFaces face hface with
      hfirst | hcenter | hsecond
    · simp [faces, hfirst]
    · simp [faces, hcenter]
    · simp [faces, hsecond]
  calc
    (cutIncidentFaces embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)).card ≤
        faces.card := Finset.card_le_card hsubset
    _ ≤ 3 := by
      have htail : ({interface.nextCenterLayerFace.1,
          interface.secondLayerFace.1} : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)).card ≤ 2 :=
        Finset.card_insert_le _ _
      have hhead := Finset.card_insert_le interface.firstLayerFace.1
        ({interface.nextCenterLayerFace.1, interface.secondLayerFace.1} : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      dsimp [faces]
      omega

/-- Away from the next central face, two right-cut edges incident to the same
face must be the same displayed crossing. -/
theorem nextLocalLayerPrefixCutEdge_eq_of_same_noncenter_face
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (face : OrbitFace embedded.cellulation.rotation.toRotationSystem)
    (hnotCenter : face ≠ interface.nextCenterLayerFace.1)
    {leftEdge rightEdge : G.edgeSet}
    (hleftCut : leftEdge ∈
      indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
    (hrightCut : rightEdge ∈
      indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
    (hleftFace : leftEdge ∈ orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem face)
    (hrightFace : rightEdge ∈ orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem face) :
    leftEdge = rightEdge := by
  rcases (mem_indexedCrossingEdgeSet_iff
    interface.nextLocalLayerPrefixCrossing leftEdge).1 hleftCut with
    ⟨leftStep, hleftStep⟩
  rcases (mem_indexedCrossingEdgeSet_iff
    interface.nextLocalLayerPrefixCrossing rightEdge).1 hrightCut with
    ⟨rightStep, hrightStep⟩
  have hleftFace' : interface.nextLocalLayerPrefixCrossing leftStep ∈
      orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem face := by
    rw [hleftStep]
    exact hleftFace
  have hrightFace' : interface.nextLocalLayerPrefixCrossing rightStep ∈
      orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem face := by
    rw [hrightStep]
    exact hrightFace
  rw [← hleftStep, ← hrightStep]
  have hleftCases := orbitFace_eq_left_or_right_of_mem_dualWalkCrossingEdge
    embedded.cellulation.rotation.toRotationSystem htwoSided hunique
    interface.nextLocalLayer.walk
    (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm leftStep)
    face (by
      simpa [nextLocalLayerPrefixCrossing,
        GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
        hleftFace')
  have hrightCases := orbitFace_eq_left_or_right_of_mem_dualWalkCrossingEdge
    embedded.cellulation.rotation.toRotationSystem htwoSided hunique
    interface.nextLocalLayer.walk
    (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm rightStep)
    face (by
      simpa [nextLocalLayerPrefixCrossing,
        GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
        hrightFace')
  fin_cases leftStep <;> fin_cases rightStep
  · rfl
  · simp [nextLocalLayer, nextLocalLayerWalk] at hleftCases hrightCases
    rcases hleftCases with hfirst | hcenter
    · rcases hrightCases with hcenter | hsecond
      · exact False.elim (interface.firstLayerFace_ne_nextCenterLayerFace
          (Subtype.ext (hfirst.symm.trans hcenter)))
      · exact False.elim (interface.firstLayerFace_ne_secondLayerFace
          (Subtype.ext (hfirst.symm.trans hsecond)))
    · exact False.elim (hnotCenter hcenter)
  · simp [nextLocalLayer, nextLocalLayerWalk] at hleftCases hrightCases
    rcases hleftCases with hcenter | hsecond
    · exact False.elim (hnotCenter hcenter)
    · rcases hrightCases with hfirst | hcenter
      · exact False.elim (interface.firstLayerFace_ne_secondLayerFace
          (Subtype.ext (hfirst.symm.trans hsecond)))
      · exact False.elim (interface.secondLayerFace_ne_nextCenterLayerFace
          (Subtype.ext (hsecond.symm.trans hcenter)))
  · rfl

/-- Outgoing occurrence-sensitive fragments inject into the three incident
faces.  The next central face has its complete boundary retained; each outer
face contains only one displayed cut edge. -/
theorem localLayerRightPrefixBoundaryFragment_face_injective
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Function.Injective (fun fragment : BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion => fragment.1) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let cut := indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing
  let region := interface.localLayerRightPrefixRegion
  intro left right hface
  rcases left with ⟨leftFace, ⟨leftFragment, leftTouches⟩⟩
  rcases right with ⟨rightFace, ⟨rightFragment, rightTouches⟩⟩
  have hfaceValue : leftFace.1 = rightFace.1 := congrArg Subtype.val hface
  have hfaceSubtype : leftFace = rightFace := Subtype.ext hfaceValue
  subst rightFace
  by_cases hcenter : leftFace.1 = interface.nextCenterLayerFace.1
  · have hboundary : orbitFaceBoundary RS
        (dartOrbitFace RS (orbitFaceRoot RS leftFace.1)) ⊆ region := by
      have hprefix := corridorFaceBoundary_subset_prefixEdgeRegion
        realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        (leftInterior.center.val + 2)
        (nextCorridorInterior leftInterior hnext).center (by
          change leftInterior.center.val + 1 < leftInterior.center.val + 2
          omega)
      simpa [RS, region, localLayerRightPrefixRegion, nextCenterLayerFace,
        hcenter] using hprefix
    have hpreconnected :=
      faceRegionalPositionGraph_preconnected_of_boundary_subset RS
        (orbitFaceRoot RS leftFace.1) region hboundary
    have hsubsingleton : Subsingleton
        (FaceRegionalFragment RS (orbitFaceRoot RS leftFace.1) region) :=
      hpreconnected.subsingleton_connectedComponent
    have hfragments : leftFragment = rightFragment :=
      @Subsingleton.elim _ hsubsingleton _ _
    subst rightFragment
    rfl
  · have hleftChosenFace : boundaryRegionalFragmentCutEdge RS cut region
        ⟨leftFace, ⟨leftFragment, leftTouches⟩⟩ ∈
        orbitFaceBoundary RS leftFace.1 := by
      exact (Finset.mem_inter.1
        (boundaryRegionalFragmentEdges_subset_boundary_inter_region RS cut
          region ⟨leftFace, ⟨leftFragment, leftTouches⟩⟩
          (boundaryRegionalFragmentCutEdge_mem_fragment RS cut region
            ⟨leftFace, ⟨leftFragment, leftTouches⟩⟩))).1
    have hrightChosenFace : boundaryRegionalFragmentCutEdge RS cut region
        ⟨leftFace, ⟨rightFragment, rightTouches⟩⟩ ∈
        orbitFaceBoundary RS leftFace.1 := by
      exact (Finset.mem_inter.1
        (boundaryRegionalFragmentEdges_subset_boundary_inter_region RS cut
          region ⟨leftFace, ⟨rightFragment, rightTouches⟩⟩
          (boundaryRegionalFragmentCutEdge_mem_fragment RS cut region
            ⟨leftFace, ⟨rightFragment, rightTouches⟩⟩))).1
    have hedge := interface.nextLocalLayerPrefixCutEdge_eq_of_same_noncenter_face
      leftFace.1 hcenter
      (boundaryRegionalFragmentCutEdge_mem_cut RS cut region
        ⟨leftFace, ⟨leftFragment, leftTouches⟩⟩)
      (boundaryRegionalFragmentCutEdge_mem_cut RS cut region
        ⟨leftFace, ⟨rightFragment, rightTouches⟩⟩)
      hleftChosenFace hrightChosenFace
    have hfragments : leftFragment = rightFragment := by
      by_contra hne
      have hdisjoint := disjoint_faceRegionalFragmentEdges_of_ne RS htwoSided
        (orbitFaceRoot RS leftFace.1) region hne
      have hleftMem := boundaryRegionalFragmentCutEdge_mem_fragment RS cut
        region ⟨leftFace, ⟨leftFragment, leftTouches⟩⟩
      have hrightMem := boundaryRegionalFragmentCutEdge_mem_fragment RS cut
        region ⟨leftFace, ⟨rightFragment, rightTouches⟩⟩
      dsimp only [boundaryRegionalFragmentEdges] at hleftMem hrightMem
      rw [← hedge] at hrightMem
      exact (Finset.disjoint_left.1 hdisjoint) hleftMem hrightMem
    subst rightFragment
    rfl

/-- The actual outgoing cumulative-prefix boundary has at most three open
face fragments. -/
theorem card_localLayerRightPrefixBoundaryRegionalFragment_le_three
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion) ≤ 3 := by
  calc
    Fintype.card (BoundaryRegionalFragment
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.localLayerRightPrefixRegion) ≤
        Fintype.card (CutIncidentFace
          embedded.cellulation.rotation.toRotationSystem
          (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)) :=
      Fintype.card_le_of_injective (fun fragment => fragment.1)
        interface.localLayerRightPrefixBoundaryFragment_face_injective
    _ = (cutIncidentFaces embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)).card := by
      simp only [Fintype.card_coe]
    _ ≤ 3 := interface.card_nextLocalLayerPrefixCutIncidentFaces_le_three

/-- The outgoing bounded profile after one literal Cell occupies only the
`0`--`3` face-count fibers. -/
theorem localLayerRightPrefixBoundedProfile_faceFragmentCount_le_three
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (interface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    (interface.localLayerRightPrefixBoundedProfile color hcolor
      ).faceFragmentCount.val ≤ 3 := by
  change Fintype.card (BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
    interface.localLayerRightPrefixRegion) ≤ 3
  exact interface.card_localLayerRightPrefixBoundaryRegionalFragment_le_three

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
