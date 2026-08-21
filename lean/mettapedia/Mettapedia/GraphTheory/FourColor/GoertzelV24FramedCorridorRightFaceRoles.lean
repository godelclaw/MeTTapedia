import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorFiniteProfileCoordinates

/-!
# Exact outgoing face roles of one literal source Cell

The preceding right-bound theorem injects outgoing boundary fragments into
the three faces of the displayed two-edge dual path.  Here the reverse
coverage is proved: because the complete displayed cut is retained in the
outgoing prefix region, every cut-incident face contributes an actual open
fragment.  Hence the outgoing fragment carrier has exactly three elements.

The coverage argument is occurrence-sensitive.  It uses the regional
face-position decomposition and remains valid for a facial walk which sees a
bridge twice; it does not replace dart occurrences by bare edge incidence.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- If every displayed cut edge is retained in the region, every
cut-incident face has an occurrence-sensitive open regional fragment. -/
theorem boundaryRegionalFragmentFace_surjective_of_cut_subset_region
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (cut region : Finset E) (hcut : cut ⊆ region) :
    Function.Surjective (fun fragment : BoundaryRegionalFragment RS cut region =>
      fragment.1) := by
  intro face
  rcases (mem_cutIncidentFaces_iff RS cut face.1).1 face.2 with
    ⟨edge, hedgeCut, hedgeFace⟩
  have hedgeRegion : edge ∈ region := hcut hedgeCut
  have hedgeAll : edge ∈ allFaceRegionalFragmentEdges RS
      (orbitFaceRoot RS face.1) region := by
    rw [allFaceRegionalFragmentEdges_eq_boundary_inter_region RS htwoSided]
    simpa using Finset.mem_inter.2 ⟨hedgeFace, hedgeRegion⟩
  rw [allFaceRegionalFragmentEdges, Finset.mem_biUnion] at hedgeAll
  rcases hedgeAll with ⟨fragment, _hfragment, hedgeFragment⟩
  let result : BoundaryRegionalFragment RS cut region :=
    ⟨face, ⟨fragment, ⟨edge, hedgeFragment, hedgeCut⟩⟩⟩
  exact ⟨result, rfl⟩

/-- Under face injectivity and cut retention, the open fragments and the
cut-incident face occurrences are equivalent. -/
noncomputable def boundaryRegionalFragmentFaceEquivCutIncidentFace
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (cut region : Finset E) (hcut : cut ⊆ region)
    (hinjective : Function.Injective
      (fun fragment : BoundaryRegionalFragment RS cut region => fragment.1)) :
    BoundaryRegionalFragment RS cut region ≃ CutIncidentFace RS cut :=
  Equiv.ofBijective (fun fragment => fragment.1)
    ⟨hinjective,
      boundaryRegionalFragmentFace_surjective_of_cut_subset_region
        RS htwoSided cut region hcut⟩

/-- Stable semantic roles of the three outgoing faces of a literal Cell.
Unlike the ambient fragment enumeration, these names do not depend on a
choice of `Fintype.equivFin`. -/
inductive LocalLayerRightFaceRole where
  | first
  | center
  | second
  deriving DecidableEq, Fintype

@[simp]
theorem card_localLayerRightFaceRole :
    Fintype.card LocalLayerRightFaceRole = 3 := by
  decide

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance framedCorridorRightFaceRolesEdgeSetDecidableEq :
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

/-- All three named faces of the displayed right dual path, and no others,
are incident to its two-edge cut. -/
theorem nextLocalLayerPrefixCutIncidentFaces_eq_three
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    cutIncidentFaces embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing) =
      {interface.firstLayerFace.1, interface.nextCenterLayerFace.1,
        interface.secondLayerFace.1} := by
  ext face
  constructor
  · intro hface
    rcases interface.mem_nextLocalLayerPrefixCutIncidentFaces face hface with
      hfirst | hcenter | hsecond
    · simp [hfirst]
    · simp [hcenter]
    · simp [hsecond]
  · intro hface
    simp only [Finset.mem_insert, Finset.mem_singleton] at hface
    rcases hface with hfirst | hcenter | hsecond
    · subst face
      apply (mem_cutIncidentFaces_iff
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.firstLayerFace.1).2
      refine ⟨interface.nextLocalLayerPrefixCrossing 0, ?_, ?_⟩
      · exact (mem_indexedCrossingEdgeSet_iff
          interface.nextLocalLayerPrefixCrossing _).2 ⟨0, rfl⟩
      · simpa [nextLocalLayerPrefixCrossing,
          GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge,
          nextLocalLayer, nextLocalLayerWalk] using
          (dualWalkCrossingEdge_mem_leftFace
            (orbitFaceBoundary
              embedded.cellulation.rotation.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace embedded.cellulation.rotation.toRotationSystem))
            hunique interface.nextLocalLayer.walk
            (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm 0))
    · subst face
      apply (mem_cutIncidentFaces_iff
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.nextCenterLayerFace.1).2
      refine ⟨interface.nextLocalLayerPrefixCrossing 0, ?_, ?_⟩
      · exact (mem_indexedCrossingEdgeSet_iff
          interface.nextLocalLayerPrefixCrossing _).2 ⟨0, rfl⟩
      · simpa [nextLocalLayerPrefixCrossing,
          GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge,
          nextLocalLayer, nextLocalLayerWalk] using
          (dualWalkCrossingEdge_mem_rightFace
            (orbitFaceBoundary
              embedded.cellulation.rotation.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace embedded.cellulation.rotation.toRotationSystem))
            hunique interface.nextLocalLayer.walk
            (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm 0))
    · subst face
      apply (mem_cutIncidentFaces_iff
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.secondLayerFace.1).2
      refine ⟨interface.nextLocalLayerPrefixCrossing 1, ?_, ?_⟩
      · exact (mem_indexedCrossingEdgeSet_iff
          interface.nextLocalLayerPrefixCrossing _).2 ⟨1, rfl⟩
      · simpa [nextLocalLayerPrefixCrossing,
          GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge,
          nextLocalLayer, nextLocalLayerWalk] using
          (dualWalkCrossingEdge_mem_rightFace
            (orbitFaceBoundary
              embedded.cellulation.rotation.toRotationSystem)
            (Finset.univ : Finset
              (OrbitFace embedded.cellulation.rotation.toRotationSystem))
            hunique interface.nextLocalLayer.walk
            (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm 1))

/-- The right cut meets exactly three orbit-face occurrences. -/
theorem card_nextLocalLayerPrefixCutIncidentFaces_eq_three
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    (cutIncidentFaces embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet
        interface.nextLocalLayerPrefixCrossing)).card = 3 := by
  rw [interface.nextLocalLayerPrefixCutIncidentFaces_eq_three]
  have hfirstCenter : interface.firstLayerFace.1 ≠
      interface.nextCenterLayerFace.1 := by
    intro heq
    exact interface.firstLayerFace_ne_nextCenterLayerFace (Subtype.ext heq)
  have hfirstSecond : interface.firstLayerFace.1 ≠
      interface.secondLayerFace.1 := by
    intro heq
    exact interface.firstLayerFace_ne_secondLayerFace (Subtype.ext heq)
  have hcenterSecond : interface.nextCenterLayerFace.1 ≠
      interface.secondLayerFace.1 := by
    intro heq
    exact interface.secondLayerFace_ne_nextCenterLayerFace
      (Subtype.ext heq.symm)
  simp [hfirstCenter, hfirstSecond, hcenterSecond]

/-- Every displayed right-cut edge belongs to the cumulative outgoing region. -/
theorem indexedNextLocalLayerPrefixCrossing_subset_rightPrefixRegion
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing ⊆
      interface.localLayerRightPrefixRegion := by
  intro edge hedge
  rcases (mem_indexedCrossingEdgeSet_iff
      interface.nextLocalLayerPrefixCrossing edge).1 hedge with ⟨step, hstep⟩
  rw [← hstep]
  simpa [localLayerRightPrefixRegion] using
    interface.nextLocalLayerPrefixCrossing_mem_prefixEdgeRegion step

/-- The actual outgoing open-fragment carrier is equivalent to the three
cut-incident face occurrences. -/
noncomputable def localLayerRightBoundaryFragmentEquivCutIncidentFace
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    BoundaryRegionalFragment
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.localLayerRightPrefixRegion ≃
      CutIncidentFace embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing) :=
  boundaryRegionalFragmentFaceEquivCutIncidentFace
    embedded.cellulation.rotation.toRotationSystem htwoSided
    (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
    interface.localLayerRightPrefixRegion
    interface.indexedNextLocalLayerPrefixCrossing_subset_rightPrefixRegion
    interface.localLayerRightPrefixBoundaryFragment_face_injective

/-- There are exactly three occurrence-sensitive outgoing boundary
fragments, not merely at most three. -/
theorem card_localLayerRightPrefixBoundaryRegionalFragment_eq_three
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion) = 3 := by
  calc
    Fintype.card (BoundaryRegionalFragment
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.localLayerRightPrefixRegion) =
        Fintype.card (CutIncidentFace
          embedded.cellulation.rotation.toRotationSystem
          (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)) :=
      Fintype.card_congr
        interface.localLayerRightBoundaryFragmentEquivCutIncidentFace
    _ = (cutIncidentFaces embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet
          interface.nextLocalLayerPrefixCrossing)).card := by
      simp only [Fintype.card_coe]
    _ = 3 := interface.card_nextLocalLayerPrefixCutIncidentFaces_eq_three

/-- Interpret a stable role as its literal orbit face. -/
def localLayerRightFaceOfRole
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) : LocalLayerRightFaceRole →
      OrbitFace embedded.cellulation.rotation.toRotationSystem
  | .first => interface.firstLayerFace.1
  | .center => interface.nextCenterLayerFace.1
  | .second => interface.secondLayerFace.1

/-- The three named role faces are distinct. -/
theorem localLayerRightFaceOfRole_injective
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Function.Injective interface.localLayerRightFaceOfRole := by
  intro left right heq
  cases left <;> cases right
  · rfl
  · exact False.elim (interface.firstLayerFace_ne_nextCenterLayerFace
      (Subtype.ext heq))
  · exact False.elim (interface.firstLayerFace_ne_secondLayerFace
      (Subtype.ext heq))
  · exact False.elim (interface.firstLayerFace_ne_nextCenterLayerFace
      (Subtype.ext heq.symm))
  · rfl
  · exact False.elim (interface.secondLayerFace_ne_nextCenterLayerFace
      (Subtype.ext heq.symm))
  · exact False.elim (interface.firstLayerFace_ne_secondLayerFace
      (Subtype.ext heq.symm))
  · exact False.elim (interface.secondLayerFace_ne_nextCenterLayerFace
      (Subtype.ext heq))
  · rfl

/-- Every stable role is a cut-incident face occurrence. -/
def localLayerRightRoleCutIncidentFace
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (role : LocalLayerRightFaceRole) :
    CutIncidentFace embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing) :=
  ⟨interface.localLayerRightFaceOfRole role, by
    rw [interface.nextLocalLayerPrefixCutIncidentFaces_eq_three]
    cases role <;> simp [localLayerRightFaceOfRole]⟩

/-- The named roles enumerate every cut-incident face, with semantic rather
than arbitrary finite coordinates. -/
theorem localLayerRightRoleCutIncidentFace_surjective
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Function.Surjective interface.localLayerRightRoleCutIncidentFace := by
  intro face
  have htransport := congrArg
    (fun faces : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem) =>
      face.1 ∈ faces)
    interface.nextLocalLayerPrefixCutIncidentFaces_eq_three
  have hface : face.1 ∈
      ({interface.firstLayerFace.1, interface.nextCenterLayerFace.1,
        interface.secondLayerFace.1} : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem)) :=
    htransport.mp face.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hface
  rcases hface with hfirst | hcenter | hsecond
  · refine ⟨.first, Subtype.ext ?_⟩
    simpa [localLayerRightRoleCutIncidentFace,
      localLayerRightFaceOfRole] using hfirst.symm
  · refine ⟨.center, Subtype.ext ?_⟩
    simpa [localLayerRightRoleCutIncidentFace,
      localLayerRightFaceOfRole] using hcenter.symm
  · refine ⟨.second, Subtype.ext ?_⟩
    simpa [localLayerRightRoleCutIncidentFace,
      localLayerRightFaceOfRole] using hsecond.symm

/-- Semantic equivalence between the three role names and the actual
cut-incident face occurrences. -/
noncomputable def localLayerRightFaceRoleEquivCutIncidentFace
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    LocalLayerRightFaceRole ≃
      CutIncidentFace embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing) :=
  Equiv.ofBijective interface.localLayerRightRoleCutIncidentFace
    ⟨fun _ _ heq => interface.localLayerRightFaceOfRole_injective
        (congrArg Subtype.val heq),
      interface.localLayerRightRoleCutIncidentFace_surjective⟩

/-- Every actual outgoing boundary fragment receives its unique stable
`first`/`center`/`second` role. -/
noncomputable def localLayerRightBoundaryFragmentRole
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion) : LocalLayerRightFaceRole :=
  interface.localLayerRightFaceRoleEquivCutIncidentFace.symm
    (interface.localLayerRightBoundaryFragmentEquivCutIncidentFace fragment)

/-- The stable role records the literal ambient face of the fragment. -/
theorem localLayerRightFaceOfRole_boundaryFragmentRole
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion) :
    interface.localLayerRightFaceOfRole
        (interface.localLayerRightBoundaryFragmentRole fragment) =
      fragment.1.1 := by
  have happly := interface.localLayerRightFaceRoleEquivCutIncidentFace.apply_symm_apply
    (interface.localLayerRightBoundaryFragmentEquivCutIncidentFace fragment)
  exact congrArg Subtype.val happly

/-- The three stable roles are equivalent to the actual occurrence-sensitive
outgoing fragments. -/
noncomputable def localLayerRightFaceRoleEquivBoundaryFragment
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    LocalLayerRightFaceRole ≃ BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion :=
  interface.localLayerRightFaceRoleEquivCutIncidentFace.trans
    interface.localLayerRightBoundaryFragmentEquivCutIncidentFace.symm

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
