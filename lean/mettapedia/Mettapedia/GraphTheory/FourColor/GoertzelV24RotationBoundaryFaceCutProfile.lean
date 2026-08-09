import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationAllFaceCutProfile

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationBoundaryFaceCutProfile

open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
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

/-- A chosen cyclic occurrence of the chosen cut edge in an open fragment.
Keeping the occurrence, rather than only its underlying edge, is essential
when a facial walk traverses a bridge twice. -/
def boundaryRegionalFragmentCutPosition
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) :
    Fin (RS.faceOrbit (orbitFaceRoot RS fragment.1.1)).card :=
  Classical.choose <|
    (mem_faceRegionalFragmentEdges_iff RS
      (orbitFaceRoot RS fragment.1.1) region fragment.2.1
      (boundaryRegionalFragmentCutEdge RS cut region fragment)).1
        (boundaryRegionalFragmentCutEdge_mem_fragment RS cut region fragment)

theorem boundaryRegionalFragmentCutPosition_mem
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) :
    boundaryRegionalFragmentCutPosition RS cut region fragment ∈
      faceRegionalFragmentPositions RS (orbitFaceRoot RS fragment.1.1)
        region fragment.2.1 :=
  (Classical.choose_spec <|
    (mem_faceRegionalFragmentEdges_iff RS
      (orbitFaceRoot RS fragment.1.1) region fragment.2.1
      (boundaryRegionalFragmentCutEdge RS cut region fragment)).1
        (boundaryRegionalFragmentCutEdge_mem_fragment RS cut region fragment)).1

theorem boundaryRegionalFragmentCutPosition_edge
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) :
    faceCycleEdge RS (orbitFaceRoot RS fragment.1.1)
        (boundaryRegionalFragmentCutPosition RS cut region fragment) =
      boundaryRegionalFragmentCutEdge RS cut region fragment :=
  (Classical.choose_spec <|
    (mem_faceRegionalFragmentEdges_iff RS
      (orbitFaceRoot RS fragment.1.1) region fragment.2.1
      (boundaryRegionalFragmentCutEdge RS cut region fragment)).1
        (boundaryRegionalFragmentCutEdge_mem_fragment RS cut region fragment)).2

/-- A dart occurrence over a cut edge.  Unlike edge/face incidence, this
retains the two occurrences of a bridge on one facial walk. -/
abbrev CutDartOccurrence (RS : RotationSystem V E) (cut : Finset E) :=
  { dart : RS.D // RS.edgeOf dart ∈ cut }

/-- There are at most two cut-dart occurrences per cut edge, directly from
the rotation system's two-darts-per-edge law. -/
theorem card_cutDartOccurrence_le_two_mul_card
    (RS : RotationSystem V E) (cut : Finset E) :
    Fintype.card (CutDartOccurrence RS cut) ≤ 2 * cut.card := by
  let encode : CutDartOccurrence RS cut →
      Σ edge : ↥cut, { dart : RS.D // dart ∈ RS.dartsOn edge.1 } :=
    fun occurrence =>
      ⟨⟨RS.edgeOf occurrence.1, occurrence.2⟩,
        ⟨occurrence.1, (RS.mem_dartsOn).2 rfl⟩⟩
  have hinjective : Function.Injective encode := by
    intro left right heq
    apply Subtype.ext
    exact congrArg (fun occurrence => occurrence.2.1) heq
  calc
    Fintype.card (CutDartOccurrence RS cut) ≤
        Fintype.card
          (Σ edge : ↥cut, { dart : RS.D // dart ∈ RS.dartsOn edge.1 }) :=
      Fintype.card_le_of_injective encode hinjective
    _ = ∑ edge : ↥cut,
        Fintype.card { dart : RS.D // dart ∈ RS.dartsOn edge.1 } := by
      rw [Fintype.card_sigma]
    _ = ∑ _edge : ↥cut, 2 := by
      apply Finset.sum_congr rfl
      intro edge _hedge
      rw [Fintype.card_coe, RS.dartsOn_card_two]
    _ = 2 * cut.card := by simp [Nat.mul_comm]

/-- Map an open face fragment to one actual cut-dart occurrence that it
contains. -/
def boundaryRegionalFragmentDartOccurrence
    (RS : RotationSystem V E) (cut region : Finset E)
    (fragment : BoundaryRegionalFragment RS cut region) :
    CutDartOccurrence RS cut :=
  ⟨faceCycleDart RS (orbitFaceRoot RS fragment.1.1)
      (boundaryRegionalFragmentCutPosition RS cut region fragment), by
    change faceCycleEdge RS (orbitFaceRoot RS fragment.1.1)
        (boundaryRegionalFragmentCutPosition RS cut region fragment) ∈ cut
    rw [boundaryRegionalFragmentCutPosition_edge]
    exact boundaryRegionalFragmentCutEdge_mem_cut RS cut region fragment⟩

/-- The occurrence-sensitive fragment map is injective without any global
two-sided-face hypothesis.  Equal darts determine the same quotient face and
the same cyclic position; distinct connected fragments have disjoint position
sets. -/
theorem boundaryRegionalFragmentDartOccurrence_injective
    (RS : RotationSystem V E) (cut region : Finset E) :
    Function.Injective
      (boundaryRegionalFragmentDartOccurrence RS cut region) := by
  intro left right heq
  have hdart :
      faceCycleDart RS (orbitFaceRoot RS left.1.1)
          (boundaryRegionalFragmentCutPosition RS cut region left) =
        faceCycleDart RS (orbitFaceRoot RS right.1.1)
          (boundaryRegionalFragmentCutPosition RS cut region right) :=
    congrArg Subtype.val heq
  have hface : left.1.1 = right.1.1 := by
    calc
      left.1.1 = dartOrbitFace RS
          (faceCycleDart RS (orbitFaceRoot RS left.1.1)
            (boundaryRegionalFragmentCutPosition RS cut region left)) := by
        rw [dartOrbitFace_faceCycleDart, dartOrbitFace_orbitFaceRoot]
      _ = dartOrbitFace RS
          (faceCycleDart RS (orbitFaceRoot RS right.1.1)
            (boundaryRegionalFragmentCutPosition RS cut region right)) := by
        rw [hdart]
      _ = right.1.1 := by
        rw [dartOrbitFace_faceCycleDart, dartOrbitFace_orbitFaceRoot]
  rcases left with ⟨leftFace, ⟨leftFragment, leftTouches⟩⟩
  rcases right with ⟨rightFace, ⟨rightFragment, rightTouches⟩⟩
  dsimp only at hface
  have hfaceSubtype : leftFace = rightFace := Subtype.ext hface
  subst rightFace
  have hposition :
      boundaryRegionalFragmentCutPosition RS cut region
          (⟨leftFace, ⟨leftFragment, leftTouches⟩⟩ :
            BoundaryRegionalFragment RS cut region) =
        boundaryRegionalFragmentCutPosition RS cut region
          (⟨leftFace, ⟨rightFragment, rightTouches⟩⟩ :
            BoundaryRegionalFragment RS cut region) := by
    apply faceCycleDart_injective RS (orbitFaceRoot RS leftFace.1)
    exact hdart
  have hfragment : leftFragment = rightFragment := by
    by_contra hne
    have hdisjoint := disjoint_faceRegionalFragmentPositions_of_ne RS
      (orbitFaceRoot RS leftFace.1) region hne
    have hleftMem := boundaryRegionalFragmentCutPosition_mem RS cut region
      (⟨leftFace, ⟨leftFragment, leftTouches⟩⟩ :
        BoundaryRegionalFragment RS cut region)
    have hrightMem := boundaryRegionalFragmentCutPosition_mem RS cut region
      (⟨leftFace, ⟨rightFragment, rightTouches⟩⟩ :
        BoundaryRegionalFragment RS cut region)
    exact (Finset.disjoint_left.1 hdisjoint) hleftMem (hposition ▸ hrightMem)
  subst rightFragment
  rfl

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

/-- Occurrence-sensitive form of the open-fragment bound.  It remains valid
when an edge is a bridge and both of its dart sides belong to the same quotient
face, so no global `OrbitFacesTwoSided` premise is required. -/
theorem card_boundaryRegionalFragment_le_two_mul_card_of_dartOccurrences
    (RS : RotationSystem V E) (cut region : Finset E) :
    Fintype.card (BoundaryRegionalFragment RS cut region) ≤ 2 * cut.card := by
  exact (Fintype.card_le_of_injective
    (boundaryRegionalFragmentDartOccurrence RS cut region)
    (boundaryRegionalFragmentDartOccurrence_injective RS cut region)).trans
      (card_cutDartOccurrence_le_two_mul_card RS cut)

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

/-- On the canonical boundary profile, the new incidence matrix is exactly
membership of the enumerated crossing edge in the actual open face fragment. -/
theorem vertexSetBoundaryGraphCutData_profile_fragmentContainsPort_iff
    (RS : RotationSystem V E) (inside : Finset V)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (fragment : Fin (Fintype.card (BoundaryRegionalFragment RS
      (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside))))
    (crossing : Fin (Fintype.card (VertexSetCrossingEdge RS inside))) :
    ((vertexSetBoundaryGraphCutData RS inside).profile C hC).fragmentContainsPort
        fragment (.inl crossing) = true ↔
      vertexSetCrossingEdgeAt RS inside crossing ∈
        (vertexSetBoundaryGraphCutData RS inside).fragmentEdges fragment := by
  rw [GraphCorridorCutData.profile_fragmentContainsPort_eq_true_iff]
  rw [GraphCorridorCutData.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
    (vertexSetBoundaryGraphCutData RS inside)
    (vertexSetBoundaryGraphCutData_fragmentsOnFaceInRegion RS inside)]
  rfl

/-- Every open face fragment in the canonical boundary profile contains at
least one actual crossing port. -/
theorem vertexSetBoundaryGraphCutData_profile_fragmentContainsPort_nonempty
    (RS : RotationSystem V E) (inside : Finset V)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (fragment : Fin (Fintype.card (BoundaryRegionalFragment RS
      (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)))) :
    ∃ crossing : Fin (Fintype.card (VertexSetCrossingEdge RS inside)),
      ((vertexSetBoundaryGraphCutData RS inside).profile C hC).fragmentContainsPort
        fragment (.inl crossing) = true := by
  rcases vertexSetBoundaryGraphCutData_fragment_touches_crossing RS inside
      fragment with ⟨edge, hedgeFragment, hedgeCrossing⟩
  rcases exists_vertexSetCrossingEdgeAt_eq RS inside hedgeCrossing with
    ⟨crossing, hcrossing⟩
  refine ⟨crossing,
    (vertexSetBoundaryGraphCutData_profile_fragmentContainsPort_iff
      RS inside C hC fragment crossing).2 ?_⟩
  simpa only [hcrossing] using hedgeFragment

/-- Boundary-local graph-derived cut data under a caller-selected crossing
coordinate.  This retains the exact same regional fragments as the canonical
profile while allowing a genuine transversal construction to supply its own
port order.  The indexing alone makes no planarity claim. -/
def vertexSetBoundaryGraphCutDataWithIndexing
    (RS : RotationSystem V E) (inside : Finset V)
    (indexing : VertexSetCrossingIndexing RS inside) :
    GraphCorridorCutData RS
      (Fintype.card (VertexSetCrossingEdge RS inside)) 0
      (Fintype.card (BoundaryRegionalFragment RS
        (vertexSetCrossingEdges RS inside)
        (vertexSetRegionEdges RS inside))) where
  regionEdges := vertexSetRegionEdges RS inside
  crossingEdge := vertexSetCrossingEdgeAtWithIndexing RS inside indexing
  terminalEdge := fun terminal => Fin.elim0 terminal
  fragmentFace := fun fragment =>
    (boundaryRegionalFragmentAt RS (vertexSetCrossingEdges RS inside)
      (vertexSetRegionEdges RS inside) fragment).1.1
  fragmentEdges := fun fragment =>
    boundaryRegionalFragmentEdges RS (vertexSetCrossingEdges RS inside)
      (vertexSetRegionEdges RS inside)
      (boundaryRegionalFragmentAt RS (vertexSetCrossingEdges RS inside)
        (vertexSetRegionEdges RS inside) fragment)

theorem vertexSetBoundaryGraphCutDataWithIndexing_portsInRegion
    (RS : RotationSystem V E) (inside : Finset V)
    (indexing : VertexSetCrossingIndexing RS inside) :
    (vertexSetBoundaryGraphCutDataWithIndexing RS inside indexing).PortsInRegion := by
  intro port
  rcases port with crossing | terminal
  · exact vertexSetCrossingEdges_subset_regionEdges RS inside
      (vertexSetCrossingEdgeAtWithIndexing_mem_crossing RS inside indexing crossing)
  · exact Fin.elim0 terminal

theorem vertexSetBoundaryGraphCutDataWithIndexing_portsInjective
    (RS : RotationSystem V E) (inside : Finset V)
    (indexing : VertexSetCrossingIndexing RS inside) :
    (vertexSetBoundaryGraphCutDataWithIndexing RS inside indexing).PortsInjective := by
  intro first second heq
  rcases first with first | first
  · rcases second with second | second
    · congr 1
      exact vertexSetCrossingEdgeAtWithIndexing_injective RS inside indexing heq
    · exact Fin.elim0 second
  · exact Fin.elim0 first

theorem vertexSetBoundaryGraphCutDataWithIndexing_fragmentsOnFaceInRegion
    (RS : RotationSystem V E) (inside : Finset V)
    (indexing : VertexSetCrossingIndexing RS inside) :
    (vertexSetBoundaryGraphCutDataWithIndexing RS inside indexing).FragmentsOnFaceInRegion := by
  intro fragment
  exact boundaryRegionalFragmentEdges_subset_boundary_inter_region RS
    (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)
    (boundaryRegionalFragmentAt RS (vertexSetCrossingEdges RS inside)
      (vertexSetRegionEdges RS inside) fragment)

/-- Under any supplied crossing coordinate, the computed face-port incidence
still says exactly that the named crossing edge lies in the open fragment. -/
theorem vertexSetBoundaryGraphCutDataWithIndexing_profile_fragmentContainsPort_iff
    (RS : RotationSystem V E) (inside : Finset V)
    (indexing : VertexSetCrossingIndexing RS inside)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (fragment : Fin (Fintype.card (BoundaryRegionalFragment RS
      (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside))))
    (crossing : Fin (Fintype.card (VertexSetCrossingEdge RS inside))) :
    ((vertexSetBoundaryGraphCutDataWithIndexing RS inside indexing).profile C hC).fragmentContainsPort
      fragment (.inl crossing) = true ↔
      vertexSetCrossingEdgeAtWithIndexing RS inside indexing crossing ∈
        (vertexSetBoundaryGraphCutDataWithIndexing RS inside indexing).fragmentEdges
          fragment := by
  rw [GraphCorridorCutData.profile_fragmentContainsPort_eq_true_iff]
  rw [GraphCorridorCutData.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
    (vertexSetBoundaryGraphCutDataWithIndexing RS inside indexing)
    (vertexSetBoundaryGraphCutDataWithIndexing_fragmentsOnFaceInRegion
      RS inside indexing)]
  rfl

/-- Every open fragment retains a crossing port under a caller-selected
coordinate, with no appeal to the canonical enumeration. -/
theorem vertexSetBoundaryGraphCutDataWithIndexing_profile_fragmentContainsPort_nonempty
    (RS : RotationSystem V E) (inside : Finset V)
    (indexing : VertexSetCrossingIndexing RS inside)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (fragment : Fin (Fintype.card (BoundaryRegionalFragment RS
      (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)))) :
    ∃ crossing : Fin (Fintype.card (VertexSetCrossingEdge RS inside)),
      ((vertexSetBoundaryGraphCutDataWithIndexing RS inside indexing).profile C hC).fragmentContainsPort
        fragment (.inl crossing) = true := by
  rcases (boundaryRegionalFragmentAt RS (vertexSetCrossingEdges RS inside)
    (vertexSetRegionEdges RS inside) fragment).2.2 with
      ⟨edge, hedgeFragment, hedgeCrossing⟩
  rcases exists_vertexSetCrossingEdgeAtWithIndexing_eq RS inside indexing
      hedgeCrossing with ⟨crossing, hcrossing⟩
  refine ⟨crossing,
    (vertexSetBoundaryGraphCutDataWithIndexing_profile_fragmentContainsPort_iff
      RS inside indexing C hC fragment crossing).2 ?_⟩
  simpa [vertexSetBoundaryGraphCutDataWithIndexing,
    boundaryRegionalFragmentEdges, hcrossing] using hedgeFragment

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

/-- The boundary-local face-field count is controlled by crossing width even
for framed graphs with bridge stubs. -/
theorem vertexSetBoundaryGraphCutData_fragmentCount_le_two_mul_crossingPortCount_of_dartOccurrences
    (RS : RotationSystem V E) (inside : Finset V) :
    Fintype.card (BoundaryRegionalFragment RS
      (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)) ≤
      2 * Fintype.card (VertexSetCrossingEdge RS inside) := by
  rw [card_vertexSetCrossingEdge]
  exact card_boundaryRegionalFragment_le_two_mul_card_of_dartOccurrences RS
    (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)

end

end GoertzelV24RotationBoundaryFaceCutProfile

end Mettapedia.GraphTheory.FourColor
