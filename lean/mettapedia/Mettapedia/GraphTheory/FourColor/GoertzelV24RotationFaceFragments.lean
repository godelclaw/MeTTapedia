import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexFaceRungType

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationFaceFragments

open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationVertexCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Cyclic positions of one actual face whose boundary edges belong to a
specified regional edge set. -/
def faceRegionalPositions (RS : RotationSystem V E) (root : RS.D)
    (region : Finset E) : Finset (Fin (RS.faceOrbit root).card) :=
  Finset.univ.filter fun position => faceCycleEdge RS root position ∈ region

@[simp]
theorem mem_faceRegionalPositions_iff
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (position : Fin (RS.faceOrbit root).card) :
    position ∈ faceRegionalPositions RS root region ↔
      faceCycleEdge RS root position ∈ region := by
  simp [faceRegionalPositions]

/-- The actual cyclic adjacency graph on the bounded powers of a face
permutation. The inequality guard handles a possible one-dart orbit without
introducing a loop. -/
def faceCyclePositionGraph (RS : RotationSystem V E) (root : RS.D) :
    SimpleGraph (Fin (RS.faceOrbit root).card) where
  Adj left right :=
    left ≠ right ∧
      (faceCycleDart RS root right = RS.phi (faceCycleDart RS root left) ∨
        faceCycleDart RS root left = RS.phi (faceCycleDart RS root right))
  symm := ⟨by
    rintro left right ⟨hne, hstep⟩
    rcases hstep with hforward | hbackward
    · exact ⟨hne.symm, Or.inr hforward⟩
    · exact ⟨hne.symm, Or.inl hbackward⟩⟩
  loopless := ⟨by
    intro position hadj
    exact hadj.1 rfl⟩

/-- A regional position is an actual face-cycle position whose edge lies in
the region. -/
abbrev FaceRegionalPosition (RS : RotationSystem V E) (root : RS.D)
    (region : Finset E) :=
  ↥(faceRegionalPositions RS root region)

/-- The face-cycle graph induced on the actual positions retained by the
regional edge set. -/
def faceRegionalPositionGraph (RS : RotationSystem V E) (root : RS.D)
    (region : Finset E) :
    SimpleGraph (FaceRegionalPosition RS root region) where
  Adj left right := (faceCyclePositionGraph RS root).Adj left.1 right.1
  symm := ⟨fun _ _ hadj => hadj.symm⟩
  loopless := ⟨fun _ hadj => hadj.ne rfl⟩

/-- A regional face fragment is a connected component of the actual face
cycle after positions outside the edge region have been removed. -/
abbrev FaceRegionalFragment (RS : RotationSystem V E) (root : RS.D)
    (region : Finset E) :=
  (faceRegionalPositionGraph RS root region).ConnectedComponent

/-- Cyclic face positions belonging to one regional fragment. -/
def faceRegionalFragmentPositions
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (fragment : FaceRegionalFragment RS root region) :
    Finset (Fin (RS.faceOrbit root).card) := by
  classical
  exact fragment.supp.toFinset.image Subtype.val

theorem mem_faceRegionalFragmentPositions_iff
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (fragment : FaceRegionalFragment RS root region)
    (position : Fin (RS.faceOrbit root).card) :
    position ∈ faceRegionalFragmentPositions RS root region fragment ↔
      ∃ regionalPosition : FaceRegionalPosition RS root region,
        regionalPosition ∈ fragment.supp ∧ regionalPosition.1 = position := by
  classical
  simp [faceRegionalFragmentPositions, and_comm]

/-- Edge support of one regional face fragment, obtained from its actual
cyclic positions. -/
def faceRegionalFragmentEdges
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (fragment : FaceRegionalFragment RS root region) : Finset E :=
  (faceRegionalFragmentPositions RS root region fragment).image
    (faceCycleEdge RS root)

theorem mem_faceRegionalFragmentEdges_iff
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (fragment : FaceRegionalFragment RS root region) (edge : E) :
    edge ∈ faceRegionalFragmentEdges RS root region fragment ↔
      ∃ position ∈ faceRegionalFragmentPositions RS root region fragment,
        faceCycleEdge RS root position = edge := by
  simp [faceRegionalFragmentEdges]

/-- Any two retained positions in one fragment are joined through retained
successor/predecessor steps of the actual face cycle. -/
theorem faceRegionalFragment_reachable
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (fragment : FaceRegionalFragment RS root region)
    {left right : FaceRegionalPosition RS root region}
    (hleft : left ∈ fragment.supp) (hright : right ∈ fragment.supp) :
    (faceRegionalPositionGraph RS root region).Reachable left right := by
  apply SimpleGraph.ConnectedComponent.exact
  exact ((SimpleGraph.ConnectedComponent.mem_supp_iff fragment left).1 hleft).trans
    ((SimpleGraph.ConnectedComponent.mem_supp_iff fragment right).1 hright).symm

/-- Every fragment edge genuinely lies both on the named face boundary and
in the regional edge set. -/
theorem faceRegionalFragmentEdges_subset_boundary_inter_region
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (fragment : FaceRegionalFragment RS root region) :
    faceRegionalFragmentEdges RS root region fragment ⊆
      orbitFaceBoundary RS (dartOrbitFace RS root) ∩ region := by
  intro edge hedge
  rcases (mem_faceRegionalFragmentEdges_iff RS root region fragment edge).1 hedge with
    ⟨position, hpositionFragment, rfl⟩
  rcases (mem_faceRegionalFragmentPositions_iff RS root region fragment position).1
      hpositionFragment with ⟨regionalPosition, _, hposition⟩
  have hregional := regionalPosition.2
  rw [hposition, mem_faceRegionalPositions_iff] at hregional
  exact Finset.mem_inter.2 ⟨faceCycleEdge_mem RS root position, hregional⟩

/-- Every connected component contributes at least one actual boundary edge. -/
theorem faceRegionalFragmentEdges_nonempty
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (fragment : FaceRegionalFragment RS root region) :
    (faceRegionalFragmentEdges RS root region fragment).Nonempty := by
  rcases SimpleGraph.ConnectedComponent.nonempty_supp fragment with
    ⟨regionalPosition, hposition⟩
  refine ⟨faceCycleEdge RS root regionalPosition.1, ?_⟩
  rw [mem_faceRegionalFragmentEdges_iff]
  refine ⟨regionalPosition.1, ?_, rfl⟩
  rw [mem_faceRegionalFragmentPositions_iff]
  exact ⟨regionalPosition, hposition, rfl⟩

/-- Distinct connected components have disjoint cyclic position sets. -/
theorem disjoint_faceRegionalFragmentPositions_of_ne
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    {left right : FaceRegionalFragment RS root region} (hne : left ≠ right) :
    Disjoint (faceRegionalFragmentPositions RS root region left)
      (faceRegionalFragmentPositions RS root region right) := by
  rw [Finset.disjoint_left]
  intro position hleft hright
  rcases (mem_faceRegionalFragmentPositions_iff RS root region left position).1 hleft with
    ⟨leftPosition, hleftSupp, hleftValue⟩
  rcases (mem_faceRegionalFragmentPositions_iff RS root region right position).1 hright with
    ⟨rightPosition, hrightSupp, hrightValue⟩
  have hpositions : leftPosition = rightPosition :=
    Subtype.ext (hleftValue.trans hrightValue.symm)
  subst rightPosition
  exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex
    hleftSupp hrightSupp)

/-- On a two-sided face, distinct regional fragments have disjoint edge
supports as well as disjoint position supports. -/
theorem disjoint_faceRegionalFragmentEdges_of_ne
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (root : RS.D) (region : Finset E)
    {left right : FaceRegionalFragment RS root region} (hne : left ≠ right) :
    Disjoint (faceRegionalFragmentEdges RS root region left)
      (faceRegionalFragmentEdges RS root region right) := by
  rw [Finset.disjoint_left]
  intro edge hleft hright
  rcases (mem_faceRegionalFragmentEdges_iff RS root region left edge).1 hleft with
    ⟨leftPosition, hleftPosition, hleftEdge⟩
  rcases (mem_faceRegionalFragmentEdges_iff RS root region right edge).1 hright with
    ⟨rightPosition, hrightPosition, hrightEdge⟩
  have hpositions : leftPosition = rightPosition :=
    faceCycleEdge_injective RS htwoSided root
      (hleftEdge.trans hrightEdge.symm)
  exact (Finset.disjoint_left.1
    (disjoint_faceRegionalFragmentPositions_of_ne RS root region hne))
      hleftPosition (hpositions ▸ hrightPosition)

/-- The regional cyclic positions map exactly onto the intersection of the
actual face boundary with the edge region. -/
theorem image_faceRegionalPositions_eq_boundary_inter_region
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (root : RS.D) (region : Finset E) :
    (faceRegionalPositions RS root region).image (faceCycleEdge RS root) =
      orbitFaceBoundary RS (dartOrbitFace RS root) ∩ region := by
  ext edge
  constructor
  · intro hedge
    rcases Finset.mem_image.1 hedge with ⟨position, hposition, rfl⟩
    exact Finset.mem_inter.2 ⟨faceCycleEdge_mem RS root position,
      (mem_faceRegionalPositions_iff RS root region position).1 hposition⟩
  · intro hedge
    have hedge' := Finset.mem_inter.1 hedge
    rcases existsUnique_faceCycleEdge_eq RS htwoSided root edge hedge'.1 with
      ⟨position, hpositionEdge, _⟩
    exact Finset.mem_image.2 ⟨position,
      (mem_faceRegionalPositions_iff RS root region position).2
        (hpositionEdge ▸ hedge'.2),
      hpositionEdge⟩

/-- Union of all connected regional face fragments. -/
def allFaceRegionalFragmentEdges
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E) : Finset E := by
  classical
  exact Finset.univ.biUnion (faceRegionalFragmentEdges RS root region)

/-- The connected fragments form an exact, pairwise-disjoint decomposition
of the retained part of a two-sided face boundary. -/
theorem allFaceRegionalFragmentEdges_eq_boundary_inter_region
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (root : RS.D) (region : Finset E) :
    allFaceRegionalFragmentEdges RS root region =
      orbitFaceBoundary RS (dartOrbitFace RS root) ∩ region := by
  apply Finset.Subset.antisymm
  · intro edge hedge
    rw [allFaceRegionalFragmentEdges, Finset.mem_biUnion] at hedge
    rcases hedge with ⟨fragment, _, hedge⟩
    exact faceRegionalFragmentEdges_subset_boundary_inter_region
      RS root region fragment hedge
  · intro edge hedge
    have himage := image_faceRegionalPositions_eq_boundary_inter_region
      RS htwoSided root region
    have hedgeImage : edge ∈
        (faceRegionalPositions RS root region).image (faceCycleEdge RS root) := by
      rw [himage]
      exact hedge
    rcases Finset.mem_image.1 hedgeImage with
      ⟨position, hpositionRegional, hpositionEdge⟩
    let regionalPosition : FaceRegionalPosition RS root region :=
      ⟨position, hpositionRegional⟩
    let fragment : FaceRegionalFragment RS root region :=
      (faceRegionalPositionGraph RS root region).connectedComponentMk
        regionalPosition
    rw [allFaceRegionalFragmentEdges, Finset.mem_biUnion]
    refine ⟨fragment, Finset.mem_univ _, ?_⟩
    rw [mem_faceRegionalFragmentEdges_iff]
    refine ⟨position, ?_, hpositionEdge⟩
    rw [mem_faceRegionalFragmentPositions_iff]
    exact ⟨regionalPosition,
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem, rfl⟩

/-- Canonical finite enumeration of the connected regional fragments of one
actual face. -/
def faceRegionalFragmentAt
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (index : Fin (Fintype.card (FaceRegionalFragment RS root region))) :
    FaceRegionalFragment RS root region :=
  (Fintype.equivFin (FaceRegionalFragment RS root region)).symm index

theorem faceRegionalFragmentAt_injective
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E) :
    Function.Injective (faceRegionalFragmentAt RS root region) :=
  (Fintype.equivFin (FaceRegionalFragment RS root region)).symm.injective

theorem exists_faceRegionalFragmentAt_eq
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (fragment : FaceRegionalFragment RS root region) :
    ∃ index : Fin (Fintype.card (FaceRegionalFragment RS root region)),
      faceRegionalFragmentAt RS root region index = fragment := by
  refine ⟨Fintype.equivFin (FaceRegionalFragment RS root region) fragment, ?_⟩
  exact (Fintype.equivFin
    (FaceRegionalFragment RS root region)).symm_apply_apply fragment

/-- The exact vertex-side cut data augmented by every connected regional
fragment of one named face. Crossing ports and face fragments are both
canonically enumerated from the graph and rotation data. -/
def vertexSetOneFaceGraphCutData
    (RS : RotationSystem V E) (inside : Finset V) (root : RS.D) :
    GraphCorridorCutData RS
      (Fintype.card (VertexSetCrossingEdge RS inside)) 0
      (Fintype.card (FaceRegionalFragment RS root
        (vertexSetRegionEdges RS inside))) where
  regionEdges := vertexSetRegionEdges RS inside
  crossingEdge := vertexSetCrossingEdgeAt RS inside
  terminalEdge := fun terminal => Fin.elim0 terminal
  fragmentFace := fun _ => dartOrbitFace RS root
  fragmentEdges := fun fragment =>
    faceRegionalFragmentEdges RS root (vertexSetRegionEdges RS inside)
      (faceRegionalFragmentAt RS root (vertexSetRegionEdges RS inside) fragment)

theorem vertexSetOneFaceGraphCutData_portsInRegion
    (RS : RotationSystem V E) (inside : Finset V) (root : RS.D) :
    (vertexSetOneFaceGraphCutData RS inside root).PortsInRegion := by
  intro port
  rcases port with crossing | terminal
  · exact vertexSetCrossingEdges_subset_regionEdges RS inside
      (vertexSetCrossingEdgeAt_mem_crossing RS inside crossing)
  · exact Fin.elim0 terminal

/-- The one-face cut's fragment validity predicate is derived from the
connected-component construction rather than stored in the cut data. -/
theorem vertexSetOneFaceGraphCutData_fragmentsOnFaceInRegion
    (RS : RotationSystem V E) (inside : Finset V) (root : RS.D) :
    (vertexSetOneFaceGraphCutData RS inside root).FragmentsOnFaceInRegion := by
  intro fragment
  exact faceRegionalFragmentEdges_subset_boundary_inter_region RS root
    (vertexSetRegionEdges RS inside)
    (faceRegionalFragmentAt RS root (vertexSetRegionEdges RS inside) fragment)

theorem vertexSetOneFaceGraphCutData_fragmentEdges_nonempty
    (RS : RotationSystem V E) (inside : Finset V) (root : RS.D)
    (fragment : Fin (Fintype.card (FaceRegionalFragment RS root
      (vertexSetRegionEdges RS inside)))) :
    ((vertexSetOneFaceGraphCutData RS inside root).fragmentEdges fragment).Nonempty :=
  faceRegionalFragmentEdges_nonempty RS root (vertexSetRegionEdges RS inside)
    (faceRegionalFragmentAt RS root (vertexSetRegionEdges RS inside) fragment)

/-- Under two-sidedness, distinct enumerated fragments of the named face have
disjoint actual edge supports. -/
theorem vertexSetOneFaceGraphCutData_fragmentEdges_disjoint
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (inside : Finset V) (root : RS.D)
    {left right : Fin (Fintype.card (FaceRegionalFragment RS root
      (vertexSetRegionEdges RS inside)))} (hne : left ≠ right) :
    Disjoint
      ((vertexSetOneFaceGraphCutData RS inside root).fragmentEdges left)
      ((vertexSetOneFaceGraphCutData RS inside root).fragmentEdges right) := by
  apply disjoint_faceRegionalFragmentEdges_of_ne RS htwoSided root
    (vertexSetRegionEdges RS inside)
  intro heq
  exact hne (faceRegionalFragmentAt_injective RS root
    (vertexSetRegionEdges RS inside) heq)

/-- The enumerated fragment fields of the one-face cut cover exactly the
retained part of that named face boundary. -/
theorem vertexSetOneFaceGraphCutData_fragmentEdges_biUnion
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (inside : Finset V) (root : RS.D) :
    Finset.univ.biUnion
      (vertexSetOneFaceGraphCutData RS inside root).fragmentEdges =
      orbitFaceBoundary RS (dartOrbitFace RS root) ∩
        vertexSetRegionEdges RS inside := by
  apply Finset.Subset.antisymm
  · intro edge hedge
    rw [Finset.mem_biUnion] at hedge
    rcases hedge with ⟨fragment, _, hedge⟩
    exact faceRegionalFragmentEdges_subset_boundary_inter_region RS root
      (vertexSetRegionEdges RS inside)
      (faceRegionalFragmentAt RS root (vertexSetRegionEdges RS inside) fragment)
      hedge
  · intro edge hedge
    have hall := allFaceRegionalFragmentEdges_eq_boundary_inter_region
      RS htwoSided root (vertexSetRegionEdges RS inside)
    have hedgeAll : edge ∈ allFaceRegionalFragmentEdges RS root
        (vertexSetRegionEdges RS inside) := by
      rw [hall]
      exact hedge
    rw [allFaceRegionalFragmentEdges, Finset.mem_biUnion] at hedgeAll
    rcases hedgeAll with ⟨fragment, _, hfragmentEdge⟩
    rcases exists_faceRegionalFragmentAt_eq RS root
      (vertexSetRegionEdges RS inside) fragment with ⟨index, hindex⟩
    rw [Finset.mem_biUnion]
    refine ⟨index, Finset.mem_univ _, ?_⟩
    simpa [vertexSetOneFaceGraphCutData, hindex] using hfragmentEdge

end

end GoertzelV24RotationFaceFragments

end Mettapedia.GraphTheory.FourColor
