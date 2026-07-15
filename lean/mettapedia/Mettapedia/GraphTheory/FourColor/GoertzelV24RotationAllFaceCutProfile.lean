import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceFragments

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationAllFaceCutProfile

open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationVertexCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A canonical dart representative of an orbit face. -/
def orbitFaceRoot (RS : RotationSystem V E) (face : OrbitFace RS) : RS.D :=
  Classical.choose (exists_dartOrbitFace_eq RS face)

@[simp]
theorem dartOrbitFace_orbitFaceRoot
    (RS : RotationSystem V E) (face : OrbitFace RS) :
    dartOrbitFace RS (orbitFaceRoot RS face) = face :=
  Classical.choose_spec (exists_dartOrbitFace_eq RS face)

/-- All regional face fragments, with the face occurrence retained. An edge
incident to two faces may correctly occur in two different sigma fibers. -/
abbrev AllFaceRegionalFragment (RS : RotationSystem V E)
    (region : Finset E) :=
  Σ face : OrbitFace RS,
    FaceRegionalFragment RS (orbitFaceRoot RS face) region

/-- Edge support of one face-indexed regional fragment. -/
def indexedFaceRegionalFragmentEdges
    (RS : RotationSystem V E) (region : Finset E)
    (fragment : AllFaceRegionalFragment RS region) : Finset E :=
  faceRegionalFragmentEdges RS (orbitFaceRoot RS fragment.1) region fragment.2

/-- Every face-indexed fragment lies on its own named face and in the region. -/
theorem indexedFaceRegionalFragmentEdges_subset_boundary_inter_region
    (RS : RotationSystem V E) (region : Finset E)
    (fragment : AllFaceRegionalFragment RS region) :
    indexedFaceRegionalFragmentEdges RS region fragment ⊆
      orbitFaceBoundary RS fragment.1 ∩ region := by
  rcases fragment with ⟨face, fragment⟩
  simpa [indexedFaceRegionalFragmentEdges] using
    faceRegionalFragmentEdges_subset_boundary_inter_region RS
    (orbitFaceRoot RS face) region fragment

/-- Every face-indexed regional fragment is nonempty. -/
theorem indexedFaceRegionalFragmentEdges_nonempty
    (RS : RotationSystem V E) (region : Finset E)
    (fragment : AllFaceRegionalFragment RS region) :
    (indexedFaceRegionalFragmentEdges RS region fragment).Nonempty := by
  rcases fragment with ⟨face, fragment⟩
  exact faceRegionalFragmentEdges_nonempty RS (orbitFaceRoot RS face)
    region fragment

/-- Distinct fragments in the same face fiber have disjoint edge supports.
No disjointness is claimed between different incident faces. -/
theorem disjoint_indexedFaceRegionalFragmentEdges_of_same_face
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (region : Finset E)
    {left right : AllFaceRegionalFragment RS region}
    (hface : left.1 = right.1) (hne : left ≠ right) :
    Disjoint (indexedFaceRegionalFragmentEdges RS region left)
      (indexedFaceRegionalFragmentEdges RS region right) := by
  rcases left with ⟨leftFace, leftFragment⟩
  rcases right with ⟨rightFace, rightFragment⟩
  dsimp at hface
  subst rightFace
  apply disjoint_faceRegionalFragmentEdges_of_ne RS htwoSided
    (orbitFaceRoot RS leftFace) region
  intro hfragments
  apply hne
  cases hfragments
  rfl

/-- Every retained edge occurrence on a two-sided face lies in exactly one
connected regional fragment of that face. -/
theorem existsUnique_faceRegionalFragment_edge_mem
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (region : Finset E) (face : OrbitFace RS) (edge : E)
    (hedge : edge ∈ orbitFaceBoundary RS face ∩ region) :
    ∃! fragment : FaceRegionalFragment RS (orbitFaceRoot RS face) region,
      edge ∈ faceRegionalFragmentEdges RS (orbitFaceRoot RS face)
        region fragment := by
  have hedgeRoot : edge ∈ orbitFaceBoundary RS
      (dartOrbitFace RS (orbitFaceRoot RS face)) ∩ region := by
    simpa using hedge
  have hall := allFaceRegionalFragmentEdges_eq_boundary_inter_region RS
    htwoSided (orbitFaceRoot RS face) region
  have hedgeAll : edge ∈
      GoertzelV24RotationFaceFragments.allFaceRegionalFragmentEdges RS
      (orbitFaceRoot RS face) region := by
    rw [hall]
    exact hedgeRoot
  rw [GoertzelV24RotationFaceFragments.allFaceRegionalFragmentEdges,
    Finset.mem_biUnion] at hedgeAll
  rcases hedgeAll with ⟨fragment, _, hfragmentEdge⟩
  refine ⟨fragment, hfragmentEdge, ?_⟩
  intro other hotherEdge
  by_contra hotherNe
  have hfragmentNe : fragment ≠ other := fun heq => hotherNe heq.symm
  exact (Finset.disjoint_left.1
    (disjoint_faceRegionalFragmentEdges_of_ne RS
      (htwoSided := htwoSided) (root := orbitFaceRoot RS face)
      (region := region) hfragmentNe)) hfragmentEdge hotherEdge

/-- Canonical enumeration of all face-indexed regional fragments. -/
def allFaceRegionalFragmentAt
    (RS : RotationSystem V E) (region : Finset E)
    (index : Fin (Fintype.card (AllFaceRegionalFragment RS region))) :
    AllFaceRegionalFragment RS region :=
  (Fintype.equivFin (AllFaceRegionalFragment RS region)).symm index

theorem allFaceRegionalFragmentAt_injective
    (RS : RotationSystem V E) (region : Finset E) :
    Function.Injective (allFaceRegionalFragmentAt RS region) :=
  (Fintype.equivFin (AllFaceRegionalFragment RS region)).symm.injective

theorem exists_allFaceRegionalFragmentAt_eq
    (RS : RotationSystem V E) (region : Finset E)
    (fragment : AllFaceRegionalFragment RS region) :
    ∃ index : Fin (Fintype.card (AllFaceRegionalFragment RS region)),
      allFaceRegionalFragmentAt RS region index = fragment := by
  refine ⟨Fintype.equivFin (AllFaceRegionalFragment RS region) fragment, ?_⟩
  exact (Fintype.equivFin
    (AllFaceRegionalFragment RS region)).symm_apply_apply fragment

/-- Full graph-derived cut data for a finite vertex side: actual crossing
edges and every connected partial-face occurrence are both computed from the
rotation system. -/
def vertexSetAllFacesGraphCutData
    (RS : RotationSystem V E) (inside : Finset V) :
    GraphCorridorCutData RS
      (Fintype.card (VertexSetCrossingEdge RS inside)) 0
      (Fintype.card (AllFaceRegionalFragment RS
        (vertexSetRegionEdges RS inside))) where
  regionEdges := vertexSetRegionEdges RS inside
  crossingEdge := vertexSetCrossingEdgeAt RS inside
  terminalEdge := fun terminal => Fin.elim0 terminal
  fragmentFace := fun fragment =>
    (allFaceRegionalFragmentAt RS (vertexSetRegionEdges RS inside) fragment).1
  fragmentEdges := fun fragment =>
    indexedFaceRegionalFragmentEdges RS (vertexSetRegionEdges RS inside)
      (allFaceRegionalFragmentAt RS (vertexSetRegionEdges RS inside) fragment)

theorem vertexSetAllFacesGraphCutData_portsInRegion
    (RS : RotationSystem V E) (inside : Finset V) :
    (vertexSetAllFacesGraphCutData RS inside).PortsInRegion := by
  intro port
  rcases port with crossing | terminal
  · exact vertexSetCrossingEdges_subset_regionEdges RS inside
      (vertexSetCrossingEdgeAt_mem_crossing RS inside crossing)
  · exact Fin.elim0 terminal

/-- All full-cut fragment fields satisfy the graph-derived face-and-region
predicate by construction. -/
theorem vertexSetAllFacesGraphCutData_fragmentsOnFaceInRegion
    (RS : RotationSystem V E) (inside : Finset V) :
    (vertexSetAllFacesGraphCutData RS inside).FragmentsOnFaceInRegion := by
  intro fragment
  exact indexedFaceRegionalFragmentEdges_subset_boundary_inter_region RS
    (vertexSetRegionEdges RS inside)
    (allFaceRegionalFragmentAt RS (vertexSetRegionEdges RS inside) fragment)

theorem vertexSetAllFacesGraphCutData_fragmentEdges_nonempty
    (RS : RotationSystem V E) (inside : Finset V)
    (fragment : Fin (Fintype.card (AllFaceRegionalFragment RS
      (vertexSetRegionEdges RS inside)))) :
    ((vertexSetAllFacesGraphCutData RS inside).fragmentEdges fragment).Nonempty :=
  indexedFaceRegionalFragmentEdges_nonempty RS (vertexSetRegionEdges RS inside)
    (allFaceRegionalFragmentAt RS (vertexSetRegionEdges RS inside) fragment)

/-- Every retained face-edge occurrence appears among the enumerated full-cut
fragment fields. -/
theorem exists_vertexSetAllFacesGraphCutData_fragment_of_edge_mem
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (inside : Finset V) (face : OrbitFace RS) (edge : E)
    (hedge : edge ∈ orbitFaceBoundary RS face ∩
      vertexSetRegionEdges RS inside) :
    ∃ fragment : Fin (Fintype.card (AllFaceRegionalFragment RS
        (vertexSetRegionEdges RS inside))),
      (vertexSetAllFacesGraphCutData RS inside).fragmentFace fragment = face ∧
      edge ∈ (vertexSetAllFacesGraphCutData RS inside).fragmentEdges fragment := by
  rcases existsUnique_faceRegionalFragment_edge_mem RS htwoSided
    (vertexSetRegionEdges RS inside) face edge hedge with
    ⟨faceFragment, hfaceFragment, _⟩
  let allFragment : AllFaceRegionalFragment RS
      (vertexSetRegionEdges RS inside) := ⟨face, faceFragment⟩
  rcases exists_allFaceRegionalFragmentAt_eq RS
    (vertexSetRegionEdges RS inside) allFragment with ⟨index, hindex⟩
  refine ⟨index, ?_, ?_⟩
  · exact congrArg Sigma.fst hindex
  · change edge ∈ indexedFaceRegionalFragmentEdges RS
      (vertexSetRegionEdges RS inside)
      (allFaceRegionalFragmentAt RS (vertexSetRegionEdges RS inside) index)
    rw [hindex]
    exact hfaceFragment

end

end GoertzelV24RotationAllFaceCutProfile

end Mettapedia.GraphTheory.FourColor
