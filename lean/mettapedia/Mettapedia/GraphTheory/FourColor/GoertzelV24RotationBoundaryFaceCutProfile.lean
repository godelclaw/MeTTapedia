import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationAllFaceCutProfile

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationBoundaryFaceCutProfile

open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationVertexCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Orbit faces incident to a specified finite edge cut. This deliberately
excludes faces wholly internal to either complementary side. -/
def cutIncidentFaces (RS : RotationSystem V E) (cut : Finset E) :
    Finset (OrbitFace RS) :=
  cut.biUnion fun edge =>
    Finset.univ.filter fun face => edge ∈ orbitFaceBoundary RS face

@[simp]
theorem mem_cutIncidentFaces_iff
    (RS : RotationSystem V E) (cut : Finset E) (face : OrbitFace RS) :
    face ∈ cutIncidentFaces RS cut ↔
      ∃ edge ∈ cut, edge ∈ orbitFaceBoundary RS face := by
  simp [cutIncidentFaces]

/-- Every cut edge belongs to at most two orbit faces, so the number of faces
meeting a cut is at most twice the cut width. -/
theorem card_cutIncidentFaces_le_two_mul_card
    (RS : RotationSystem V E) (cut : Finset E) :
    (cutIncidentFaces RS cut).card ≤ 2 * cut.card := by
  calc
    (cutIncidentFaces RS cut).card ≤ cut.card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro edge hedge
      simpa [totalIncidenceCount] using
        orbitFace_totalIncidenceCount_le_two RS edge
    _ = 2 * cut.card := Nat.mul_comm _ _

/-- A face carrying a proof that it meets the specified edge cut. -/
abbrev CutIncidentFace (RS : RotationSystem V E) (cut : Finset E) :=
  ↥(cutIncidentFaces RS cut)

theorem card_cutIncidentFace_le_two_mul_card
    (RS : RotationSystem V E) (cut : Finset E) :
    Fintype.card (CutIncidentFace RS cut) ≤ 2 * cut.card := by
  simpa only [Fintype.card_coe] using
    card_cutIncidentFaces_le_two_mul_card RS cut

/-- A connected regional fragment of a cut-incident face is open precisely
when its actual edge support meets the cut. These, rather than all regional
face components, are the partial faces relevant to a splice boundary. -/
def FaceFragmentTouchesCut
    (RS : RotationSystem V E) (cut region : Finset E)
    (face : CutIncidentFace RS cut)
    (fragment : FaceRegionalFragment RS (orbitFaceRoot RS face.1) region) : Prop :=
  ∃ edge ∈ faceRegionalFragmentEdges RS (orbitFaceRoot RS face.1)
      region fragment,
    edge ∈ cut

/-- All open regional face fragments at a finite cut, retaining their actual
orbit-face occurrence. -/
abbrev BoundaryRegionalFragment
    (RS : RotationSystem V E) (cut region : Finset E) :=
  Σ face : CutIncidentFace RS cut,
    { fragment : FaceRegionalFragment RS (orbitFaceRoot RS face.1) region //
      FaceFragmentTouchesCut RS cut region face fragment }

/-- Edge support of an open regional face fragment. -/
def boundaryRegionalFragmentEdges
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) : Finset E :=
  faceRegionalFragmentEdges RS (orbitFaceRoot RS fragment.1.1)
    region fragment.2.1

/-- Every open fragment lies on its named face and in the regional edge set. -/
theorem boundaryRegionalFragmentEdges_subset_boundary_inter_region
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) :
    boundaryRegionalFragmentEdges RS cut region fragment ⊆
      orbitFaceBoundary RS fragment.1.1 ∩ region := by
  simpa only [boundaryRegionalFragmentEdges,
    dartOrbitFace_orbitFaceRoot] using
    faceRegionalFragmentEdges_subset_boundary_inter_region RS
      (orbitFaceRoot RS fragment.1.1) region fragment.2.1

/-- Every open fragment is nonempty, independently of its cut witness. -/
theorem boundaryRegionalFragmentEdges_nonempty
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) :
    (boundaryRegionalFragmentEdges RS cut region fragment).Nonempty :=
  faceRegionalFragmentEdges_nonempty RS (orbitFaceRoot RS fragment.1.1)
    region fragment.2.1

/-- A canonical cut edge belonging to an open fragment. -/
def boundaryRegionalFragmentCutEdge
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) : E :=
  Classical.choose fragment.2.2

theorem boundaryRegionalFragmentCutEdge_mem_fragment
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) :
    boundaryRegionalFragmentCutEdge RS cut region fragment ∈
      boundaryRegionalFragmentEdges RS cut region fragment :=
  (Classical.choose_spec fragment.2.2).1

theorem boundaryRegionalFragmentCutEdge_mem_cut
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) :
    boundaryRegionalFragmentCutEdge RS cut region fragment ∈ cut :=
  (Classical.choose_spec fragment.2.2).2

/-- A primal cut-edge/orbit-face incidence. -/
abbrev CutEdgeFaceIncidence (RS : RotationSystem V E) (cut : Finset E) :=
  Σ edge : ↥cut,
    { face : OrbitFace RS // edge.1 ∈ orbitFaceBoundary RS face }

/-- Map an open face fragment to one actual cut-edge/face incidence that it
contains. -/
def boundaryRegionalFragmentIncidence
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) :
    CutEdgeFaceIncidence RS cut :=
  have hboundary := boundaryRegionalFragmentEdges_subset_boundary_inter_region
    RS cut region fragment
    (boundaryRegionalFragmentCutEdge_mem_fragment RS cut region fragment)
  ⟨⟨boundaryRegionalFragmentCutEdge RS cut region fragment,
      boundaryRegionalFragmentCutEdge_mem_cut RS cut region fragment⟩,
    ⟨fragment.1.1, (Finset.mem_inter.1 hboundary).1⟩⟩

/-- On two-sided faces, the incidence map is injective: two distinct open
components of the same face have disjoint edge supports. -/
theorem boundaryRegionalFragmentIncidence_injective
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (cut region : Finset E) :
    Function.Injective (boundaryRegionalFragmentIncidence RS cut region) := by
  intro left right heq
  have hedge :
      boundaryRegionalFragmentCutEdge RS cut region left =
        boundaryRegionalFragmentCutEdge RS cut region right :=
    congrArg (fun occurrence => occurrence.1.1) heq
  have hface : left.1.1 = right.1.1 :=
    congrArg (fun occurrence => occurrence.2.1) heq
  rcases left with ⟨leftFace, ⟨leftFragment, leftTouches⟩⟩
  rcases right with ⟨rightFace, ⟨rightFragment, rightTouches⟩⟩
  dsimp only at hface
  have hfaceSubtype : leftFace = rightFace := Subtype.ext hface
  subst rightFace
  have hfragment : leftFragment = rightFragment := by
    by_contra hne
    have hdisjoint := disjoint_faceRegionalFragmentEdges_of_ne RS htwoSided
      (orbitFaceRoot RS leftFace.1) region hne
    have hleftMem := boundaryRegionalFragmentCutEdge_mem_fragment RS cut region
      (⟨leftFace, ⟨leftFragment, leftTouches⟩⟩ :
        BoundaryRegionalFragment RS cut region)
    have hrightMem := boundaryRegionalFragmentCutEdge_mem_fragment RS cut region
      (⟨leftFace, ⟨rightFragment, rightTouches⟩⟩ :
        BoundaryRegionalFragment RS cut region)
    dsimp only [boundaryRegionalFragmentEdges] at hleftMem hrightMem
    rw [← hedge] at hrightMem
    exact (Finset.disjoint_left.1 hdisjoint) hleftMem hrightMem
  subst rightFragment
  rfl

/-- The number of cut-edge/orbit-face incidences is at most twice the cut
width. This is the global double-counting form of the two-darts-per-edge law. -/
theorem card_cutEdgeFaceIncidence_le_two_mul_card
    (RS : RotationSystem V E) (cut : Finset E) :
    Fintype.card (CutEdgeFaceIncidence RS cut) ≤ 2 * cut.card := by
  rw [Fintype.card_sigma]
  calc
    (∑ edge : ↥cut,
        Fintype.card { face : OrbitFace RS //
          edge.1 ∈ orbitFaceBoundary RS face }) ≤
        ∑ _edge : ↥cut, 2 := by
      apply Finset.sum_le_sum
      intro edge hedge
      rw [Fintype.card_subtype]
      simpa [totalIncidenceCount] using
        orbitFace_totalIncidenceCount_le_two RS edge.1
    _ = 2 * cut.card := by simp [Nat.mul_comm]

noncomputable instance boundaryRegionalFragmentFintype
    (RS : RotationSystem V E) (cut region : Finset E) :
    Fintype (BoundaryRegionalFragment RS cut region) :=
  Fintype.ofFinite (BoundaryRegionalFragment RS cut region)

/-- The number of open regional face fragments is bounded by twice the cut
width, independent of the size of either complementary region. -/
theorem card_boundaryRegionalFragment_le_two_mul_card
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (cut region : Finset E) :
    Fintype.card (BoundaryRegionalFragment RS cut region) ≤ 2 * cut.card := by
  exact (Fintype.card_le_of_injective
    (boundaryRegionalFragmentIncidence RS cut region)
    (boundaryRegionalFragmentIncidence_injective RS htwoSided cut region)).trans
      (card_cutEdgeFaceIncidence_le_two_mul_card RS cut)

/-- Canonical finite enumeration of the open regional face fragments. -/
def boundaryRegionalFragmentAt
    (RS : RotationSystem V E) (cut region : Finset E)
    (index : Fin (Fintype.card (BoundaryRegionalFragment RS cut region))) :
    BoundaryRegionalFragment RS cut region :=
  (Fintype.equivFin (BoundaryRegionalFragment RS cut region)).symm index

theorem boundaryRegionalFragmentAt_injective
    (RS : RotationSystem V E) (cut region : Finset E) :
    Function.Injective (boundaryRegionalFragmentAt RS cut region) :=
  (Fintype.equivFin (BoundaryRegionalFragment RS cut region)).symm.injective

theorem exists_boundaryRegionalFragmentAt_eq
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) :
    ∃ index : Fin (Fintype.card (BoundaryRegionalFragment RS cut region)),
      boundaryRegionalFragmentAt RS cut region index = fragment := by
  refine ⟨Fintype.equivFin (BoundaryRegionalFragment RS cut region) fragment, ?_⟩
  exact (Fintype.equivFin
    (BoundaryRegionalFragment RS cut region)).symm_apply_apply fragment

/-- Boundary-local graph-derived cut data for a finite vertex side. Its face
fields are exactly the connected regional components that meet an actual
crossing edge. -/
def vertexSetBoundaryGraphCutData
    (RS : RotationSystem V E) (inside : Finset V) :
    GraphCorridorCutData RS
      (Fintype.card (VertexSetCrossingEdge RS inside)) 0
      (Fintype.card (BoundaryRegionalFragment RS
        (vertexSetCrossingEdges RS inside)
        (vertexSetRegionEdges RS inside))) where
  regionEdges := vertexSetRegionEdges RS inside
  crossingEdge := vertexSetCrossingEdgeAt RS inside
  terminalEdge := fun terminal => Fin.elim0 terminal
  fragmentFace := fun fragment =>
    (boundaryRegionalFragmentAt RS (vertexSetCrossingEdges RS inside)
      (vertexSetRegionEdges RS inside) fragment).1.1
  fragmentEdges := fun fragment =>
    boundaryRegionalFragmentEdges RS (vertexSetCrossingEdges RS inside)
      (vertexSetRegionEdges RS inside)
      (boundaryRegionalFragmentAt RS (vertexSetCrossingEdges RS inside)
        (vertexSetRegionEdges RS inside) fragment)

theorem vertexSetBoundaryGraphCutData_portsInRegion
    (RS : RotationSystem V E) (inside : Finset V) :
    (vertexSetBoundaryGraphCutData RS inside).PortsInRegion := by
  intro port
  rcases port with crossing | terminal
  · exact vertexSetCrossingEdges_subset_regionEdges RS inside
      (vertexSetCrossingEdgeAt_mem_crossing RS inside crossing)
  · exact Fin.elim0 terminal

theorem vertexSetBoundaryGraphCutData_portsInjective
    (RS : RotationSystem V E) (inside : Finset V) :
    (vertexSetBoundaryGraphCutData RS inside).PortsInjective := by
  intro first second heq
  rcases first with first | first
  · rcases second with second | second
    · congr 1
      exact vertexSetCrossingEdgeAt_injective RS inside heq
    · exact Fin.elim0 second
  · exact Fin.elim0 first

theorem vertexSetBoundaryGraphCutData_fragmentsOnFaceInRegion
    (RS : RotationSystem V E) (inside : Finset V) :
    (vertexSetBoundaryGraphCutData RS inside).FragmentsOnFaceInRegion := by
  intro fragment
  exact boundaryRegionalFragmentEdges_subset_boundary_inter_region RS
    (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)
    (boundaryRegionalFragmentAt RS (vertexSetCrossingEdges RS inside)
      (vertexSetRegionEdges RS inside) fragment)

theorem vertexSetBoundaryGraphCutData_fragmentEdges_nonempty
    (RS : RotationSystem V E) (inside : Finset V)
    (fragment : Fin (Fintype.card (BoundaryRegionalFragment RS
      (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)))) :
    ((vertexSetBoundaryGraphCutData RS inside).fragmentEdges fragment).Nonempty :=
  boundaryRegionalFragmentEdges_nonempty RS
    (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)
    (boundaryRegionalFragmentAt RS (vertexSetCrossingEdges RS inside)
      (vertexSetRegionEdges RS inside) fragment)

/-- Every enumerated boundary-local fragment contains an actual crossing
edge; no wholly internal face component survives in this carrier. -/
theorem vertexSetBoundaryGraphCutData_fragment_touches_crossing
    (RS : RotationSystem V E) (inside : Finset V)
    (fragment : Fin (Fintype.card (BoundaryRegionalFragment RS
      (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)))) :
    ∃ edge ∈ (vertexSetBoundaryGraphCutData RS inside).fragmentEdges fragment,
      edge ∈ vertexSetCrossingEdges RS inside := by
  exact (boundaryRegionalFragmentAt RS (vertexSetCrossingEdges RS inside)
    (vertexSetRegionEdges RS inside) fragment).2.2

/-- The boundary-local face-field count is controlled solely by the actual
crossing-port count. -/
theorem vertexSetBoundaryGraphCutData_fragmentCount_le_two_mul_crossingPortCount
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (inside : Finset V) :
    Fintype.card (BoundaryRegionalFragment RS
      (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)) ≤
      2 * Fintype.card (VertexSetCrossingEdge RS inside) := by
  rw [card_vertexSetCrossingEdge]
  exact card_boundaryRegionalFragment_le_two_mul_card RS htwoSided
    (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)

end

end GoertzelV24RotationBoundaryFaceCutProfile

end Mettapedia.GraphTheory.FourColor
