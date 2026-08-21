import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixTerminalFaceCoordinates
import Mettapedia.GraphTheory.FourColor.GoertzelV24SharedFacesTwoEdgeSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideBoundaryFragmentCoverage

/-!
# Three-face bound for a source corridor cross-section

A literal source Cell cross-section is a simple dual path with two steps and
three distinct facial vertices.  This file begins the next `L7` compression
by proving that its two displayed primal crossings meet no other orbit faces.
The statement is about the actual cumulative-prefix carrier; it does not
postulate a smaller profile alphabet.
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
open GoertzelV24SharedFacesTwoEdgeSeparator
open GoertzelV24VertexSideBoundaryFragmentCoverage
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- On a two-sided rotation, the only faces incident to a dual-walk crossing
are the two facial vertices at that step. -/
theorem orbitFace_eq_left_or_right_of_mem_dualWalkCrossingEdge
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace RS))}
    (walk : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Walk start finish)
    (step : Fin walk.length) (face : OrbitFace RS)
    (hface : dualWalkCrossingEdge (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step ∈
        orbitFaceBoundary RS face) :
    face = (walk.getVert step.val).1 ∨
      face = (walk.getVert (step.val + 1)).1 := by
  let left := walk.getVert step.val
  let right := walk.getVert (step.val + 1)
  let edge := dualWalkCrossingEdge (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS)) hunique walk step
  have hleft : edge ∈ orbitFaceBoundary RS left.1 :=
    dualWalkCrossingEdge_mem_leftFace (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step
  have hright : edge ∈ orbitFaceBoundary RS right.1 :=
    dualWalkCrossingEdge_mem_rightFace (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique walk step
  have hne : left.1 ≠ right.1 := by
    intro heq
    exact (walk.adj_getVert_succ step.isLt).ne (Subtype.ext heq)
  have hpair := orbitFace_incidentFaces_eq_pair_of_mem RS htwoSided hne
    edge hleft hright
  have hmem : face ∈ Finset.univ.filter fun candidate : OrbitFace RS =>
      edge ∈ orbitFaceBoundary RS candidate := by
    simp [edge, hface]
  rw [hpair] at hmem
  simpa [left, right] using hmem

/-- Retaining a complete facial boundary leaves only one connected regional
fragment of that face. -/
theorem faceRegionalPositionGraph_preconnected_of_boundary_subset
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
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
  exact ⟨position.1, Subtype.ext rfl⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance framedCorridorPrefixThreeFaceBoundEdgeSetDecidableEq :
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

/-- Every orbit face meeting the two-edge left cross-section is one of the
three literal faces of its simple dual path. -/
theorem mem_localLayerPrefixCutIncidentFaces
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (face : OrbitFace embedded.cellulation.rotation.toRotationSystem)
    (hface : face ∈ cutIncidentFaces
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.localLayerPrefixCrossing)) :
    face = interface.firstLayerFace.1 ∨
      face = interface.centerLayerFace.1 ∨
      face = interface.secondLayerFace.1 := by
  rcases (mem_cutIncidentFaces_iff
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet interface.localLayerPrefixCrossing) face).1 hface with
    ⟨edge, hedgeCut, hedgeFace⟩
  rcases (mem_indexedCrossingEdgeSet_iff
    interface.localLayerPrefixCrossing edge).1 hedgeCut with ⟨step, hstep⟩
  subst edge
  have hcases := orbitFace_eq_left_or_right_of_mem_dualWalkCrossingEdge
    embedded.cellulation.rotation.toRotationSystem htwoSided hunique
    interface.localLayer.walk
    (Fin.cast interface.localLayer_walk_length_eq_two.symm step) face hedgeFace
  fin_cases step
  · simp [localLayer, localLayerWalk] at hcases
    rcases hcases with hfirst | hcenter
    · exact Or.inl hfirst
    · exact Or.inr (Or.inl hcenter)
  · simp [localLayer, localLayerWalk] at hcases
    rcases hcases with hcenter | hsecond
    · exact Or.inr (Or.inl hcenter)
    · exact Or.inr (Or.inr hsecond)

/-- The displayed two-edge source cross-section meets at most three orbit
faces. -/
theorem card_localLayerPrefixCutIncidentFaces_le_three
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (cutIncidentFaces embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.localLayerPrefixCrossing)).card ≤ 3 := by
  let faces : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem) :=
    {interface.firstLayerFace.1, interface.centerLayerFace.1,
      interface.secondLayerFace.1}
  have hsubset : cutIncidentFaces
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.localLayerPrefixCrossing) ⊆ faces := by
    intro face hface
    rcases interface.mem_localLayerPrefixCutIncidentFaces face hface with
      hfirst | hcenter | hsecond
    · simp [faces, hfirst]
    · simp [faces, hcenter]
    · simp [faces, hsecond]
  calc
    (cutIncidentFaces embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.localLayerPrefixCrossing)).card ≤
        faces.card := Finset.card_le_card hsubset
    _ ≤ 3 := by
      have htail : ({interface.centerLayerFace.1,
          interface.secondLayerFace.1} : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)).card ≤ 2 :=
        Finset.card_insert_le _ _
      have hhead := Finset.card_insert_le interface.firstLayerFace.1
        ({interface.centerLayerFace.1, interface.secondLayerFace.1} : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      dsimp [faces]
      omega

/-- Away from the central face, two cut edges incident to the same face must
be the same displayed crossing.  The alternative would make that face occur
on both steps of the simple three-face dual path. -/
theorem localLayerPrefixCutEdge_eq_of_same_noncenter_face
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (face : OrbitFace embedded.cellulation.rotation.toRotationSystem)
    (hnotCenter : face ≠ interface.centerLayerFace.1)
    {leftEdge rightEdge : G.edgeSet}
    (hleftCut : leftEdge ∈
      indexedCrossingEdgeSet interface.localLayerPrefixCrossing)
    (hrightCut : rightEdge ∈
      indexedCrossingEdgeSet interface.localLayerPrefixCrossing)
    (hleftFace : leftEdge ∈ orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem face)
    (hrightFace : rightEdge ∈ orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem face) :
    leftEdge = rightEdge := by
  rcases (mem_indexedCrossingEdgeSet_iff
    interface.localLayerPrefixCrossing leftEdge).1 hleftCut with
    ⟨leftStep, hleftStep⟩
  rcases (mem_indexedCrossingEdgeSet_iff
    interface.localLayerPrefixCrossing rightEdge).1 hrightCut with
    ⟨rightStep, hrightStep⟩
  have hleftFace' : interface.localLayerPrefixCrossing leftStep ∈
      orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem face := by
    rw [hleftStep]
    exact hleftFace
  have hrightFace' : interface.localLayerPrefixCrossing rightStep ∈
      orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem face := by
    rw [hrightStep]
    exact hrightFace
  rw [← hleftStep, ← hrightStep]
  have hleftCases := orbitFace_eq_left_or_right_of_mem_dualWalkCrossingEdge
    embedded.cellulation.rotation.toRotationSystem htwoSided hunique
    interface.localLayer.walk
    (Fin.cast interface.localLayer_walk_length_eq_two.symm leftStep)
    face (by
      simpa [localLayerPrefixCrossing,
        GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
        hleftFace')
  have hrightCases := orbitFace_eq_left_or_right_of_mem_dualWalkCrossingEdge
    embedded.cellulation.rotation.toRotationSystem htwoSided hunique
    interface.localLayer.walk
    (Fin.cast interface.localLayer_walk_length_eq_two.symm rightStep)
    face (by
      simpa [localLayerPrefixCrossing,
        GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using
        hrightFace')
  fin_cases leftStep <;> fin_cases rightStep
  · rfl
  · simp [localLayer, localLayerWalk] at hleftCases hrightCases
    rcases hleftCases with hfirst | hcenter
    · rcases hrightCases with hcenter | hsecond
      · exact False.elim (interface.firstLayerFace_ne_centerLayerFace
          (Subtype.ext (hfirst.symm.trans hcenter)))
      · exact False.elim (interface.firstLayerFace_ne_secondLayerFace
          (Subtype.ext (hfirst.symm.trans hsecond)))
    · exact False.elim (hnotCenter hcenter)
  · simp [localLayer, localLayerWalk] at hleftCases hrightCases
    rcases hleftCases with hcenter | hsecond
    · exact False.elim (hnotCenter hcenter)
    · rcases hrightCases with hfirst | hcenter
      · exact False.elim (interface.firstLayerFace_ne_secondLayerFace
          (Subtype.ext (hfirst.symm.trans hsecond)))
      · exact False.elim (interface.secondLayerFace_ne_centerLayerFace
          (Subtype.ext (hsecond.symm.trans hcenter)))
  · rfl

/-- The open regional fragments of the literal cumulative prefix inject into
the three incident faces.  The central face contributes one fragment because
its complete hexagonal boundary is retained; either outer face contains only
one of the two displayed cut edges. -/
theorem localLayerPrefixBoundaryFragment_face_injective
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Function.Injective (fun fragment : BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.localLayerPrefixCrossing)
      (corridorPrefixEdgeRegion
        realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        (leftInterior.center.val + 1)) => fragment.1) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let cut := indexedCrossingEdgeSet interface.localLayerPrefixCrossing
  let region := corridorPrefixEdgeRegion
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    (leftInterior.center.val + 1)
  intro left right hface
  rcases left with ⟨leftFace, ⟨leftFragment, leftTouches⟩⟩
  rcases right with ⟨rightFace, ⟨rightFragment, rightTouches⟩⟩
  have hfaceValue : leftFace.1 = rightFace.1 := congrArg Subtype.val hface
  have hfaceSubtype : leftFace = rightFace := Subtype.ext hfaceValue
  subst rightFace
  by_cases hcenter : leftFace.1 = interface.centerLayerFace.1
  · have hboundary : orbitFaceBoundary RS
        (dartOrbitFace RS (orbitFaceRoot RS leftFace.1)) ⊆ region := by
      have hprefix := corridorFaceBoundary_subset_prefixEdgeRegion
        realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        (leftInterior.center.val + 1) leftInterior.center (by omega)
      simpa [RS, region, centerLayerFace, hcenter] using hprefix
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
    have hedge := interface.localLayerPrefixCutEdge_eq_of_same_noncenter_face
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

/-- The actual source-prefix boundary has at most three open face fragments,
improving the generic two-dart-per-crossing bound from four. -/
theorem card_localLayerPrefixBoundaryRegionalFragment_le_three
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.localLayerPrefixCrossing)
      (corridorPrefixEdgeRegion
        realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        (leftInterior.center.val + 1))) ≤ 3 := by
  calc
    Fintype.card (BoundaryRegionalFragment
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.localLayerPrefixCrossing)
        (corridorPrefixEdgeRegion
          realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
          (leftInterior.center.val + 1))) ≤
        Fintype.card (CutIncidentFace
          embedded.cellulation.rotation.toRotationSystem
          (indexedCrossingEdgeSet interface.localLayerPrefixCrossing)) :=
      Fintype.card_le_of_injective (fun fragment => fragment.1)
        interface.localLayerPrefixBoundaryFragment_face_injective
    _ = (cutIncidentFaces embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.localLayerPrefixCrossing)).card := by
      simp only [Fintype.card_coe]
    _ ≤ 3 := interface.card_localLayerPrefixCutIncidentFaces_le_three

/-- The literal cumulative-prefix profile therefore occupies only the
`0`--`3` face-count fibers of its previously proved four-fragment carrier.
This is a source theorem about the constructed Cell cross-section, not a
smaller alphabet postulated for `L7`. -/
theorem localLayerLeftPrefixBoundedProfile_faceFragmentCount_le_three
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (interface.localLayerPrefixCrossing step) ≠ 0) :
    (interface.localLayerLeftPrefixBoundedProfile color hcolor).faceFragmentCount.val ≤ 3 := by
  change Fintype.card (BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet interface.localLayerPrefixCrossing)
    (corridorPrefixEdgeRegion
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      (leftInterior.center.val + 1))) ≤ 3
  exact interface.card_localLayerPrefixBoundaryRegionalFragment_le_three

end SourceConsecutiveSlabInterface

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

/-- The terminal-aware input to the one-Cell connectivity update inherits the
same proved three-fragment bound.  Retaining the shared rung adds a terminal
coordinate; it does not create a new face fragment. -/
theorem localLayerLeftPrefixSharedRungBoundedProfile_faceFragmentCount_le_three
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0) :
    (aligned.localLayerLeftPrefixSharedRungBoundedProfile color hcolor).faceFragmentCount.val ≤ 3 := by
  rw [aligned.localLayerLeftPrefixSharedRungBoundedProfile_faceFragmentCount]
  exact aligned.toInterface
    |>.localLayerLeftPrefixBoundedProfile_faceFragmentCount_le_three
      color hcolor

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
