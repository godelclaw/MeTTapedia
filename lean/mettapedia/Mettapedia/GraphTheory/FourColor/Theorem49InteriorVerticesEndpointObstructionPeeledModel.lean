import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVerticesAnnulusConstruction
import Mettapedia.GraphTheory.FourColor.Theorem49SynthesisCore
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusConstruction
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.FacialCyclePlanarEmbeddingWithBoundary
import Mettapedia.GraphTheory.OrderedPlanarEmbeddingWithBoundary
import Mettapedia.GraphTheory.WalkPlanarEmbeddingWithBoundary
import Mathlib.Tactic.FinCases

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49InteriorVerticesEndpointObstruction
/-- A minimal edge-disjoint peeled model where endpoint no-touch still fails.  The root face
contains two selected-boundary edges and the interior edge; the peeled face is a singleton face
containing only the shared interior edge. -/
def peeledEndpointTouchGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 3)} : Set (Sym2 (Fin 4)))

def pet01 : peeledEndpointTouchGraph.edgeSet := ⟨s(0, 1), by
  simp [peeledEndpointTouchGraph]⟩

def pet12 : peeledEndpointTouchGraph.edgeSet := ⟨s(1, 2), by
  simp [peeledEndpointTouchGraph]⟩

def pet23 : peeledEndpointTouchGraph.edgeSet := ⟨s(2, 3), by
  simp [peeledEndpointTouchGraph]⟩

theorem peeledEndpointTouch_edge_eq
    (e : peeledEndpointTouchGraph.edgeSet) :
    e = pet01 ∨ e = pet12 ∨ e = pet23 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 3)) ∧
        ¬ e.1.IsDiag := by
    simpa [peeledEndpointTouchGraph] using e.2
  rcases h.1 with h01 | h12 | h23
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr (Or.inl (Subtype.ext h12))
  · exact Or.inr (Or.inr (Subtype.ext h23))

noncomputable instance peeledEndpointTouchGraph_edgeSet_fintype :
    Fintype peeledEndpointTouchGraph.edgeSet :=
  ⟨{pet01, pet12, pet23}, by
    intro e
    rcases peeledEndpointTouch_edge_eq e with rfl | rfl | rfl <;> simp⟩

private theorem peeledEndpointTouch_sym2_edges_length_le_three
    {l : List (Sym2 (Fin 4))} (hnodup : l.Nodup)
    (hmem : ∀ e ∈ l, e = s(0, 1) ∨ e = s(1, 2) ∨ e = s(2, 3)) :
    l.length ≤ 3 := by
  have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnodup
  rw [← hcard]
  have hsubset : l.toFinset ⊆ ({s(0, 1), s(1, 2), s(2, 3)} : Finset (Sym2 (Fin 4))) := by
    intro e he
    rcases List.mem_toFinset.mp he with he'
    rcases hmem e he' with rfl | rfl | rfl <;> simp
  exact Finset.card_le_card hsubset

theorem peeledEndpointTouch_no_triangle {a b c : Fin 4} :
    ¬ (peeledEndpointTouchGraph.Adj a b ∧
      peeledEndpointTouchGraph.Adj b c ∧
      peeledEndpointTouchGraph.Adj c a) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [peeledEndpointTouchGraph]

theorem peeledEndpointTouch_edges_length_le_three
    {v w : Fin 4} (p : peeledEndpointTouchGraph.Walk v w) (htrail : p.IsTrail) :
    p.length ≤ 3 := by
  have hsub :
      ∀ e ∈ p.edges, e = s(0, 1) ∨ e = s(1, 2) ∨ e = s(2, 3) := by
    intro e he
    have hedge : e ∈ peeledEndpointTouchGraph.edgeSet := p.edges_subset_edgeSet he
    have h : (e = s(0, 1) ∨ e = s(1, 2) ∨ e = s(2, 3)) ∧ ¬ e.IsDiag := by
      simpa [peeledEndpointTouchGraph] using hedge
    exact h.1
  have hle_edges :
      p.edges.length ≤ 3 :=
    peeledEndpointTouch_sym2_edges_length_le_three htrail.edges_nodup hsub
  simpa [SimpleGraph.Walk.length_edges] using hle_edges

theorem peeledEndpointTouchGraph_isAcyclic : peeledEndpointTouchGraph.IsAcyclic := by
  intro v c hc
  have hle : c.length ≤ 3 := peeledEndpointTouch_edges_length_le_three c hc.isTrail
  have hge : 3 ≤ c.length := hc.three_le_length
  have hlen : c.length = 3 := by omega
  cases c with
  | nil =>
      simp at hlen
  | cons h1 c1 =>
      cases c1 with
      | nil =>
          simp at hlen
      | cons h2 c2 =>
          cases c2 with
          | nil =>
              simp at hlen
          | cons h3 c3 =>
              cases c3 with
              | nil =>
                  exact peeledEndpointTouch_no_triangle ⟨h1, h2, h3⟩
              | cons h4 c4 =>
                  simp at hlen

abbrev PeeledEndpointTouchFace := Fin 2

def peeledEndpointTouchFaces : Finset PeeledEndpointTouchFace := Finset.univ

def peeledEndpointTouchFaceBoundary :
    PeeledEndpointTouchFace → Finset peeledEndpointTouchGraph.edgeSet
  | ⟨0, _⟩ => {pet01, pet12, pet23}
  | ⟨1, _⟩ => {pet12}

theorem totalIncidenceCount_pet01 :
    totalIncidenceCount peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces pet01 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      peeledEndpointTouchFaces.filter
          (fun f => pet01 ∈ peeledEndpointTouchFaceBoundary f) =
        {(0 : PeeledEndpointTouchFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_pet12 :
    totalIncidenceCount peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces pet12 = 2 := by
  unfold totalIncidenceCount
  have hfilter :
      peeledEndpointTouchFaces.filter
          (fun f => pet12 ∈ peeledEndpointTouchFaceBoundary f) =
        peeledEndpointTouchFaces := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp [peeledEndpointTouchFaces]

theorem totalIncidenceCount_pet23 :
    totalIncidenceCount peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces pet23 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      peeledEndpointTouchFaces.filter
          (fun f => pet23 ∈ peeledEndpointTouchFaceBoundary f) =
        {(0 : PeeledEndpointTouchFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

def peeledEndpointTouchEmbedding : PlaneEmbeddingWithBoundary peeledEndpointTouchGraph where
  Face := PeeledEndpointTouchFace
  faceDecidableEq := inferInstance
  faces := peeledEndpointTouchFaces
  faceBoundary := peeledEndpointTouchFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases peeledEndpointTouch_edge_eq e with rfl | rfl | rfl
    · rw [Finset.mem_biUnion]
      exact ⟨(0 : PeeledEndpointTouchFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(0 : PeeledEndpointTouchFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(0 : PeeledEndpointTouchFace), by exact Finset.mem_univ _, by decide⟩
  edge_one_or_two_faces := by
    intro e _he
    rcases peeledEndpointTouch_edge_eq e with rfl | rfl | rfl
    · left
      exact totalIncidenceCount_pet01
    · right
      exact totalIncidenceCount_pet12
    · left
      exact totalIncidenceCount_pet23

theorem pet01_mem_selectedBoundarySupport :
    pet01 ∈ selectedBoundarySupport
      peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
      peeledEndpointTouchEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(0 : PeeledEndpointTouchFace), by
        change (0 : PeeledEndpointTouchFace) ∈ peeledEndpointTouchFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_pet01⟩

theorem pet23_mem_selectedBoundarySupport :
    pet23 ∈ selectedBoundarySupport
      peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
      peeledEndpointTouchEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(0 : PeeledEndpointTouchFace), by
        change (0 : PeeledEndpointTouchFace) ∈ peeledEndpointTouchFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_pet23⟩

theorem pet12_mem_interiorEdgeSupport :
    pet12 ∈ interiorEdgeSupport peeledEndpointTouchEmbedding.faceBoundary
      peeledEndpointTouchEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(0 : PeeledEndpointTouchFace), by
        change (0 : PeeledEndpointTouchFace) ∈ peeledEndpointTouchFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_pet12⟩

theorem pet12_not_mem_selectedBoundarySupport :
    pet12 ∉ selectedBoundarySupport
      peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
      peeledEndpointTouchEmbedding.faces := by
  intro h
  have hcount :
      totalIncidenceCount peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces pet12 = 1 :=
    (mem_selectedBoundarySupport_iff peeledEndpointTouchEmbedding.faceBoundary
      peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces).1 h |>.2
  simp [peeledEndpointTouchEmbedding, totalIncidenceCount_pet12] at hcount

theorem peeledEndpointTouch_interiorEdgeSupport_eq_singleton :
    interiorEdgeSupport peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces = {pet12} := by
  ext e
  constructor
  · intro he
    rcases peeledEndpointTouch_edge_eq e with rfl | rfl | rfl
    · have hcount :
          totalIncidenceCount peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces pet01 = 2 :=
        (mem_interiorEdgeSupport_iff peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces).1 he |>.2
      simp [peeledEndpointTouchEmbedding, totalIncidenceCount_pet01] at hcount
    · simp
    · have hcount :
          totalIncidenceCount peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces pet23 = 2 :=
        (mem_interiorEdgeSupport_iff peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces).1 he |>.2
      simp [peeledEndpointTouchEmbedding, totalIncidenceCount_pet23] at hcount
  · intro he
    have he' : e = pet12 := by
      simpa using he
    subst e
    exact pet12_mem_interiorEdgeSupport

theorem vertex_one_mem_pet01 : (1 : Fin 4) ∈ (pet01 : Sym2 (Fin 4)) := by
  simp [pet01]

theorem vertex_zero_mem_pet01 : (0 : Fin 4) ∈ (pet01 : Sym2 (Fin 4)) := by
  simp [pet01]

theorem vertex_one_mem_pet12 : (1 : Fin 4) ∈ (pet12 : Sym2 (Fin 4)) := by
  simp [pet12]

theorem vertex_two_mem_pet12 : (2 : Fin 4) ∈ (pet12 : Sym2 (Fin 4)) := by
  simp [pet12]

theorem vertex_two_mem_pet23 : (2 : Fin 4) ∈ (pet23 : Sym2 (Fin 4)) := by
  simp [pet23]

theorem vertex_three_mem_pet23 : (3 : Fin 4) ∈ (pet23 : Sym2 (Fin 4)) := by
  simp [pet23]

theorem not_endpointSupport_disjoint_peeledEndpointTouch :
    ¬ Disjoint (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding)
      (edgeEndpointSupport
        (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) := by
  intro hdisj
  have hNoEndpoint :
      ∀ v : Fin 4,
        (∃ e ∈ interiorEdgeSupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces, v ∈ (e : Sym2 (Fin 4))) →
          ∀ e ∈ selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces,
            v ∉ (e : Sym2 (Fin 4)) := by
    exact
      (edgeEndpointSupport_disjoint_iff_no_shared_endpoint
        (interiorEdgeSupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces)
        (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)).1
        (by simpa [interiorEdgeEndpointSupport] using hdisj)
  exact hNoEndpoint 1 ⟨pet12, pet12_mem_interiorEdgeSupport, vertex_one_mem_pet12⟩
    pet01 pet01_mem_selectedBoundarySupport vertex_one_mem_pet01

theorem vertex_one_mem_interiorEdgeEndpointSupport_peeledEndpointTouch :
    (1 : Fin 4) ∈ interiorEdgeEndpointSupport peeledEndpointTouchEmbedding :=
  (mem_interiorEdgeEndpointSupport_iff peeledEndpointTouchEmbedding).2
    ⟨pet12, pet12_mem_interiorEdgeSupport, vertex_one_mem_pet12⟩

theorem vertex_one_not_mem_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    (1 : Fin 4) ∉
      selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding :=
  not_mem_verticesAvoidingEdgeSupport_of_incident_boundary_edge
    pet01_mem_selectedBoundarySupport vertex_one_mem_pet01

theorem vertex_two_mem_interiorEdgeEndpointSupport_peeledEndpointTouch :
    (2 : Fin 4) ∈ interiorEdgeEndpointSupport peeledEndpointTouchEmbedding :=
  (mem_interiorEdgeEndpointSupport_iff peeledEndpointTouchEmbedding).2
    ⟨pet12, pet12_mem_interiorEdgeSupport, vertex_two_mem_pet12⟩

theorem vertex_two_not_mem_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    (2 : Fin 4) ∉
      selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding :=
  not_mem_verticesAvoidingEdgeSupport_of_incident_boundary_edge
    pet23_mem_selectedBoundarySupport vertex_two_mem_pet23

theorem selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch :
    selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ := by
  ext v
  constructor
  · intro hv
    rcases (mem_selectedBoundaryInteriorEdgeEndpointVertices_iff
        peeledEndpointTouchEmbedding).1 hv with ⟨hvInterior, hAvoids⟩
    rcases hvInterior with ⟨e, heInterior, hve⟩
    have he12 : e = pet12 := by
      have heSingleton : e ∈ ({pet12} : Finset peeledEndpointTouchGraph.edgeSet) := by
        simpa [peeledEndpointTouch_interiorEdgeSupport_eq_singleton] using heInterior
      simpa using heSingleton
    subst e
    fin_cases v
    · simp [pet12] at hve
    · exact False.elim
        (hAvoids pet01 pet01_mem_selectedBoundarySupport vertex_one_mem_pet01)
    · exact False.elim
        (hAvoids pet23 pet23_mem_selectedBoundarySupport vertex_two_mem_pet23)
    · simp [pet12] at hve
  · simp

theorem graphEdgeEndpointSupport_nonempty_peeledEndpointTouch :
    (graphEdgeEndpointSupport peeledEndpointTouchGraph).Nonempty :=
  ⟨1, mem_graphEdgeEndpointSupport_of_mem_edge vertex_one_mem_pet12⟩

/-- In the endpoint-touch model, every graph vertex is incident to some graph edge.  Thus the
previous graph-endpoint-subcarrier obstruction is already an arbitrary finite-carrier obstruction
on this vertex type. -/
theorem graphEdgeEndpointSupport_eq_univ_peeledEndpointTouch :
    graphEdgeEndpointSupport peeledEndpointTouchGraph = Finset.univ := by
  ext v
  constructor
  · intro _hv
    simp
  · intro _hv
    fin_cases v
    · exact mem_graphEdgeEndpointSupport_of_mem_edge vertex_zero_mem_pet01
    · exact mem_graphEdgeEndpointSupport_of_mem_edge vertex_one_mem_pet01
    · exact mem_graphEdgeEndpointSupport_of_mem_edge vertex_two_mem_pet23
    · exact mem_graphEdgeEndpointSupport_of_mem_edge vertex_three_mem_pet23

/-- In the endpoint-touch model, the selected-boundary endpoints cover the whole finite vertex
type.  Any selected-boundary purification over this graph therefore has no vertex left to use. -/
theorem selectedBoundaryEndpointSupport_eq_univ_peeledEndpointTouch :
    edgeEndpointSupport
        (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces) =
      Finset.univ := by
  ext v
  constructor
  · intro _hv
    simp
  · intro _hv
    rw [mem_edgeEndpointSupport_iff]
    fin_cases v
    · exact ⟨pet01, pet01_mem_selectedBoundarySupport, vertex_zero_mem_pet01⟩
    · exact ⟨pet01, pet01_mem_selectedBoundarySupport, vertex_one_mem_pet01⟩
    · exact ⟨pet23, pet23_mem_selectedBoundarySupport, vertex_two_mem_pet23⟩
    · exact ⟨pet23, pet23_mem_selectedBoundarySupport, vertex_three_mem_pet23⟩

theorem selectedBoundaryGraphInteriorVertices_eq_empty_peeledEndpointTouch :
    selectedBoundaryGraphInteriorVertices peeledEndpointTouchEmbedding = ∅ := by
  ext v
  constructor
  · intro hv
    rcases (mem_selectedBoundaryGraphInteriorVertices_iff
        peeledEndpointTouchEmbedding).1 hv with ⟨_hvGraph, hAvoids⟩
    fin_cases v
    · exact False.elim
        (hAvoids pet01 pet01_mem_selectedBoundarySupport vertex_zero_mem_pet01)
    · exact False.elim
        (hAvoids pet01 pet01_mem_selectedBoundarySupport vertex_one_mem_pet01)
    · exact False.elim
        (hAvoids pet23 pet23_mem_selectedBoundarySupport vertex_two_mem_pet23)
    · exact False.elim
        (hAvoids pet23 pet23_mem_selectedBoundarySupport vertex_three_mem_pet23)
  · simp

theorem not_selectedBoundaryGraphInteriorVertices_nonempty_peeledEndpointTouch :
    ¬ (selectedBoundaryGraphInteriorVertices peeledEndpointTouchEmbedding).Nonempty := by
  rintro ⟨v, hv⟩
  simp [selectedBoundaryGraphInteriorVertices_eq_empty_peeledEndpointTouch] at hv

/-- Any attempted finite interior-vertex carrier drawn from graph-edge endpoints becomes empty
after selected-boundary purification in the endpoint-touch model.  This blocks replacing the
interior-edge endpoint carrier by an arbitrary subcarrier of the graph endpoints. -/
theorem selectedBoundaryInteriorVertices_eq_empty_of_subset_graphEdgeEndpointSupport_peeledEndpointTouch
    (vertices : Finset (Fin 4))
    (hvertices : vertices ⊆ graphEdgeEndpointSupport peeledEndpointTouchGraph) :
    selectedBoundaryInteriorVertices peeledEndpointTouchEmbedding vertices = ∅ := by
  ext v
  constructor
  · intro hv
    rcases (mem_selectedBoundaryInteriorVertices_iff
        peeledEndpointTouchEmbedding vertices).1 hv with ⟨hvVertices, hAvoids⟩
    have hvGraph : v ∈ graphEdgeEndpointSupport peeledEndpointTouchGraph :=
      hvertices hvVertices
    have hvSelectedGraph :
        v ∈ selectedBoundaryGraphInteriorVertices peeledEndpointTouchEmbedding := by
      rw [selectedBoundaryGraphInteriorVertices]
      exact (mem_selectedBoundaryInteriorVertices_iff
        peeledEndpointTouchEmbedding (graphEdgeEndpointSupport peeledEndpointTouchGraph)).2
        ⟨hvGraph, hAvoids⟩
    simp [selectedBoundaryGraphInteriorVertices_eq_empty_peeledEndpointTouch] at hvSelectedGraph
  · simp

/-- Stronger arbitrary-carrier form: in the endpoint-touch model, no finite vertex carrier on the
existing vertex type survives selected-boundary purification.  Repairing the route by choosing a
different carrier inside this model is therefore impossible, not merely the graph-endpoint or
interior-edge-endpoint variants. -/
theorem selectedBoundaryInteriorVertices_eq_empty_peeledEndpointTouch
    (vertices : Finset (Fin 4)) :
    selectedBoundaryInteriorVertices peeledEndpointTouchEmbedding vertices = ∅ := by
  exact
    selectedBoundaryInteriorVertices_eq_empty_of_subset_graphEdgeEndpointSupport_peeledEndpointTouch
      vertices
      (by
        intro v _hv
        simp [graphEdgeEndpointSupport_eq_univ_peeledEndpointTouch])

theorem not_selectedBoundaryInteriorVertices_nonempty_peeledEndpointTouch
    (vertices : Finset (Fin 4)) :
    ¬ (selectedBoundaryInteriorVertices peeledEndpointTouchEmbedding vertices).Nonempty := by
  rintro ⟨v, hv⟩
  simp [selectedBoundaryInteriorVertices_eq_empty_peeledEndpointTouch vertices] at hv

theorem selectedBoundaryInteriorEdgeEndpointVertices_ne_interiorEdgeEndpointSupport_peeledEndpointTouch :
    selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding ≠
      interiorEdgeEndpointSupport peeledEndpointTouchEmbedding :=
  selectedBoundaryInteriorEdgeEndpointVertices_ne_interiorEdgeEndpointSupport_of_endpoint_shared
    pet12_mem_interiorEdgeSupport pet01_mem_selectedBoundarySupport
    vertex_one_mem_pet12 vertex_one_mem_pet01

theorem selectedBoundaryInteriorEdgeEndpointVertices_strictly_refines_interiorEdgeEndpointSupport_peeledEndpointTouch :
    selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding ⊆
        interiorEdgeEndpointSupport peeledEndpointTouchEmbedding ∧
      selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding ≠
        interiorEdgeEndpointSupport peeledEndpointTouchEmbedding :=
  ⟨selectedBoundaryInteriorEdgeEndpointVertices_subset_interiorEdgeEndpointSupport
      peeledEndpointTouchEmbedding,
    selectedBoundaryInteriorEdgeEndpointVertices_ne_interiorEdgeEndpointSupport_peeledEndpointTouch⟩

def peeledEndpointTouchRootFace : AmbientFace peeledEndpointTouchEmbedding.faces :=
  ⟨(0 : PeeledEndpointTouchFace), by
    change (0 : PeeledEndpointTouchFace) ∈ peeledEndpointTouchFaces
    exact Finset.mem_univ _⟩

def peeledEndpointTouchPeelFace : AmbientFace peeledEndpointTouchEmbedding.faces :=
  ⟨(1 : PeeledEndpointTouchFace), by
    change (1 : PeeledEndpointTouchFace) ∈ peeledEndpointTouchFaces
    exact Finset.mem_univ _⟩

def peeledEndpointTouchRoots : Finset (AmbientFace peeledEndpointTouchEmbedding.faces) :=
  {peeledEndpointTouchRootFace}

def peeledEndpointTouchPeelFaces : Finset (AmbientFace peeledEndpointTouchEmbedding.faces) :=
  {peeledEndpointTouchPeelFace}

theorem peeledEndpointTouch_ambientFace_eq
    (f : AmbientFace peeledEndpointTouchEmbedding.faces) :
    f = peeledEndpointTouchRootFace ∨ f = peeledEndpointTouchPeelFace := by
  rcases f with ⟨⟨n, hn⟩, hf⟩
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr (Subtype.ext rfl)

theorem peeledEndpointTouchRootFace_ne_peelFace :
    peeledEndpointTouchRootFace ≠ peeledEndpointTouchPeelFace := by
  decide

theorem peeledEndpointTouch_interiorDual_adj_root_peel :
    (interiorDualGraph peeledEndpointTouchEmbedding.faceBoundary
      peeledEndpointTouchEmbedding.faces).Adj
      peeledEndpointTouchRootFace peeledEndpointTouchPeelFace := by
  refine (interiorDualGraph_adj_iff peeledEndpointTouchEmbedding.faceBoundary
    peeledEndpointTouchEmbedding.faces).2 ?_
  refine ⟨?_, pet12, pet12_mem_interiorEdgeSupport, ?_, ?_⟩
  · intro h
    exact peeledEndpointTouchRootFace_ne_peelFace (Subtype.ext h)
  · decide
  · decide

theorem pairwiseUniqueSharedInteriorEdges_peeledEndpointTouch :
    PairwiseUniqueSharedInteriorEdges peeledEndpointTouchEmbedding.faceBoundary
      peeledEndpointTouchEmbedding.faces := by
  change PairwiseUniqueSharedInteriorEdges peeledEndpointTouchFaceBoundary
    peeledEndpointTouchFaces
  have hInterior :
      interiorEdgeSupport peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces =
        {pet12} := by
    simpa [peeledEndpointTouchEmbedding] using
      peeledEndpointTouch_interiorEdgeSupport_eq_singleton
  intro f _hf g _hg hfg
  have hsubset :
      sharedInteriorEdges peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces f g ⊆
        {pet12} := by
    intro e he
    have heInterior :
        e ∈ interiorEdgeSupport peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces :=
      (mem_sharedInteriorEdges_iff peeledEndpointTouchFaceBoundary
        peeledEndpointTouchFaces).1 he |>.1
    simpa [hInterior] using heInterior
  calc
    (sharedInteriorEdges peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces f g).card
        ≤ ({pet12} : Finset peeledEndpointTouchGraph.edgeSet).card :=
      Finset.card_le_card hsubset
    _ = 1 := by simp

theorem hall_peeledEndpointTouch
    (e : peeledEndpointTouchGraph.edgeSet) :
    totalIncidenceCount peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces e ≤ 2 := by
  rcases peeledEndpointTouch_edge_eq e with rfl | rfl | rfl
  · simp [peeledEndpointTouchEmbedding, totalIncidenceCount_pet01]
  · simp [peeledEndpointTouchEmbedding, totalIncidenceCount_pet12]
  · simp [peeledEndpointTouchEmbedding, totalIncidenceCount_pet23]

theorem rootSetCovers_peeledEndpointTouch :
    RootSetCovers
      (interiorDualGraph peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces)
      peeledEndpointTouchRoots := by
  intro f
  rcases peeledEndpointTouch_ambientFace_eq f with rfl | rfl
  · exact ⟨peeledEndpointTouchRootFace, by simp [peeledEndpointTouchRoots],
      SimpleGraph.Reachable.refl _⟩
  · exact ⟨peeledEndpointTouchRootFace, by simp [peeledEndpointTouchRoots],
      peeledEndpointTouch_interiorDual_adj_root_peel.symm.reachable⟩

theorem rootSetSeparated_peeledEndpointTouch :
    RootSetSeparated
      (interiorDualGraph peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces)
      peeledEndpointTouchRoots := by
  intro r s hr hs _hreach
  have hr' : r = peeledEndpointTouchRootFace := by
    simpa [peeledEndpointTouchRoots] using hr
  have hs' : s = peeledEndpointTouchRootFace := by
    simpa [peeledEndpointTouchRoots] using hs
  exact hr'.trans hs'.symm

def peeledEndpointTouchFallbackEdge
    (_f : AmbientFace peeledEndpointTouchEmbedding.faces) :
    peeledEndpointTouchGraph.edgeSet :=
  pet01

theorem peeledEndpointTouch_rootedWitness_peel_eq :
    rootedSharedInteriorEdgeOfPairwiseUnique
        peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
        pairwiseUniqueSharedInteriorEdges_peeledEndpointTouch
        (interiorDualSpanningForestRoot peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchRoots
          rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch)
        peeledEndpointTouchFallbackEdge peeledEndpointTouchPeelFace = pet12 := by
  let rootFace : AmbientFace peeledEndpointTouchEmbedding.faces →
      AmbientFace peeledEndpointTouchEmbedding.faces :=
    interiorDualSpanningForestRoot peeledEndpointTouchEmbedding.faceBoundary
      peeledEndpointTouchEmbedding.faces peeledEndpointTouchRoots
      rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch
  have hdisj : Disjoint peeledEndpointTouchPeelFaces peeledEndpointTouchRoots := by
    rw [Finset.disjoint_left]
    intro f hfPeel hfRoot
    have hfPeel' : f = peeledEndpointTouchPeelFace := by
      simpa [peeledEndpointTouchPeelFaces] using hfPeel
    have hfRoot' : f = peeledEndpointTouchRootFace := by
      simpa [peeledEndpointTouchRoots] using hfRoot
    exact peeledEndpointTouchRootFace_ne_peelFace (hfRoot'.symm.trans hfPeel')
  have hneq :
      peeledEndpointTouchPeelFace ≠ rootFace peeledEndpointTouchPeelFace :=
    ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
      peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
      peeledEndpointTouchPeelFaces peeledEndpointTouchRoots
      rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch
      hdisj (by simp [peeledEndpointTouchPeelFaces])
  rcases parentTowardsRoot_spec_of_ne
      (T := interiorDualSpanningForest peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces)
      (root := rootFace)
      (u := peeledEndpointTouchPeelFace)
      (h := reachable_interiorDualSpanningForestRoot
        peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
        peeledEndpointTouchRoots rootSetCovers_peeledEndpointTouch
        rootSetSeparated_peeledEndpointTouch peeledEndpointTouchPeelFace)
      hneq with ⟨p, hfp, _hadj, _hdist⟩
  have hpeel : pet12 ∈
      peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchPeelFace.1 := by
    decide
  have hp : pet12 ∈ peeledEndpointTouchEmbedding.faceBoundary p.1 := by
    rcases peeledEndpointTouch_ambientFace_eq p with rfl | rfl <;> decide
  exact rootedSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_interiorEdgeSupport
    peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
    pairwiseUniqueSharedInteriorEdges_peeledEndpointTouch rootFace
    peeledEndpointTouchFallbackEdge hfp pet12_mem_interiorEdgeSupport hpeel hp

theorem hpeelInterior_peeledEndpointTouch :
    ∀ f ∈ peeledEndpointTouchPeelFaces,
      Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
        (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces) := by
  intro f hf
  have hf' : f = peeledEndpointTouchPeelFace := by
    simpa [peeledEndpointTouchPeelFaces] using hf
  subst f
  rw [Finset.disjoint_left]
  intro e heFace heBoundary
  have he : e = pet12 := by
    simpa [peeledEndpointTouchEmbedding, peeledEndpointTouchFaceBoundary,
      peeledEndpointTouchPeelFace] using heFace
  exact pet12_not_mem_selectedBoundarySupport (by simpa [he] using heBoundary)

theorem hcover_peeledEndpointTouch :
    interiorEdgeSupport peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces ⊆
      peeledEndpointTouchPeelFaces.image
        (rootedSharedInteriorEdgeOfPairwiseUnique
          peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
          pairwiseUniqueSharedInteriorEdges_peeledEndpointTouch
          (interiorDualSpanningForestRoot peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchRoots
            rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch)
          peeledEndpointTouchFallbackEdge) := by
  intro e he
  have he' : e = pet12 := by
    simpa [peeledEndpointTouch_interiorEdgeSupport_eq_singleton] using he
  subst e
  refine Finset.mem_image.2 ⟨peeledEndpointTouchPeelFace, by
    simp [peeledEndpointTouchPeelFaces], ?_⟩
  exact peeledEndpointTouch_rootedWitness_peel_eq

theorem hchildren_peeledEndpointTouch :
    ∀ f ∈ peeledEndpointTouchPeelFaces,
      ∀ e ∈ (peeledEndpointTouchEmbedding.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique
          peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
          pairwiseUniqueSharedInteriorEdges_peeledEndpointTouch
          (interiorDualSpanningForestRoot peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchRoots
            rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch)
          peeledEndpointTouchFallbackEdge f),
        e ∈ selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces ∨
          ∃ g ∈ peeledEndpointTouchPeelFaces,
            (interiorDualSpanningForest peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces).Adj f g ∧
            e ∈ peeledEndpointTouchEmbedding.faceBoundary g.1 ∧
            (interiorDualSpanningForest peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces).dist f
                (interiorDualSpanningForestRoot peeledEndpointTouchEmbedding.faceBoundary
                  peeledEndpointTouchEmbedding.faces peeledEndpointTouchRoots
                  rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch f) <
              (interiorDualSpanningForest peeledEndpointTouchEmbedding.faceBoundary
                peeledEndpointTouchEmbedding.faces).dist g
                (interiorDualSpanningForestRoot peeledEndpointTouchEmbedding.faceBoundary
                  peeledEndpointTouchEmbedding.faces peeledEndpointTouchRoots
                  rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch g) := by
  intro f hf e he
  have hf' : f = peeledEndpointTouchPeelFace := by
    simpa [peeledEndpointTouchPeelFaces] using hf
  subst f
  have hwitness := peeledEndpointTouch_rootedWitness_peel_eq
  have hempty :
      e ∈
        (peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchPeelFace.1).erase
          pet12 := by
    simpa [hwitness] using he
  simp [peeledEndpointTouchEmbedding, peeledEndpointTouchFaceBoundary,
    peeledEndpointTouchPeelFace] at hempty

def peeledEndpointTouchBoundaryData :
    PlanarBoundaryAnnulusBoundaryData peeledEndpointTouchEmbedding where
  outerAmbientBoundary := {pet01}
  innerAmbientBoundary := {pet23}
  houterAmbientBoundaryNonempty := by simp
  hinnerAmbientBoundaryNonempty := by simp
  houterAmbientBoundarySubset := by
    intro e he
    have he' : e = pet01 := by
      simpa using he
    subst e
    exact pet01_mem_selectedBoundarySupport
  hinnerAmbientBoundarySubset := by
    intro e he
    have he' : e = pet23 := by
      simpa using he
    subst e
    exact pet23_mem_selectedBoundarySupport
  hambientBoundaryCover := by
    intro e he
    rcases peeledEndpointTouch_edge_eq e with rfl | rfl | rfl
    · simp
    · exact False.elim (pet12_not_mem_selectedBoundarySupport he)
    · simp
  hambientBoundaryDisjoint := by
    rw [Finset.disjoint_left]
    intro e he01 he23
    have h01 : e = pet01 := by
      simpa using he01
    have h23 : e = pet23 := by
      simpa using he23
    have hbad : pet01 = pet23 := h01.symm.trans h23
    have hval := congrArg Subtype.val hbad
    simp [pet01, pet23] at hval

noncomputable def peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData :
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelData peeledEndpointTouchEmbedding :=
  planarBoundaryOuterBoundaryRootAdjDistancePeelDataOfCoverSeparatedOuterBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover
    peeledEndpointTouchBoundaryData
    peeledEndpointTouchPeelFaces peeledEndpointTouchRoots
    pairwiseUniqueSharedInteriorEdges_peeledEndpointTouch
    peeledEndpointTouchFallbackEdge
    rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch
    hpeelInterior_peeledEndpointTouch
    (by
      intro r hr
      have hr' : r = peeledEndpointTouchRootFace := by
        simpa [peeledEndpointTouchRoots] using hr
      subst r
      exact ⟨pet01, by decide, by simp [peeledEndpointTouchBoundaryData]⟩)
    hcover_peeledEndpointTouch
    hchildren_peeledEndpointTouch
    hall_peeledEndpointTouch

theorem nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
      peeledEndpointTouchEmbedding) :=
  ⟨peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData⟩

/-- The endpoint-touch model already carries the generic boundary-root adjacency-distance
interior-dual package, via the interior payload of its stronger outer-boundary-rooted data. -/
theorem nonempty_interiorDualBoundaryRootAdjDistancePeelData_peeledEndpointTouch :
    Nonempty
      (PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) :=
  ⟨peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData.interiorData⟩

noncomputable def peeledEndpointTouchAnnulusConstruction :
    PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding :=
  planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData

theorem nonempty_planarBoundaryAnnulusConstruction_peeledEndpointTouch :
    Nonempty (PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding) :=
  ⟨peeledEndpointTouchAnnulusConstruction⟩

theorem peeledEndpointTouchAnnulusConstruction_peelFaces_edge_disjoint_selectedBoundarySupport :
    ∀ f ∈ peeledEndpointTouchAnnulusConstruction.peelFaces,
      Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
        (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces) := by
  intro f hf
  have hfInterior :
      f ∈ peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData.interiorData.peelFaces := by
    simpa [peeledEndpointTouchAnnulusConstruction,
      planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData,
      planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData]
      using hf
  have hfPeel : f ∈ peeledEndpointTouchPeelFaces := by
    simpa [peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData,
      planarBoundaryOuterBoundaryRootAdjDistancePeelDataOfCoverSeparatedOuterBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover,
      interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundarySubsetRootsCanonicalRootedSharedEdgeFaceMembershipCover,
      interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover]
      using hfInterior
  exact hpeelInterior_peeledEndpointTouch f hfPeel

/-- In the peeled endpoint-touch model, the exact construction-level no-touch obligation fails:
the peeled singleton face has endpoint `1` on its interior edge, and the selected-boundary edge
`pet01` has the same endpoint. -/
theorem peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch :
    ¬ (∀ f ∈
        (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
          peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData).peelFaces,
        Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
          (edgeEndpointSupport
            (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) := by
  intro hNoTouch
  have hpeel :
      peeledEndpointTouchPeelFace ∈
        (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
          peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData).peelFaces := by
    have hInterior :
        peeledEndpointTouchPeelFace ∈
          peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData.interiorData.peelFaces := by
      simp [peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData,
        planarBoundaryOuterBoundaryRootAdjDistancePeelDataOfCoverSeparatedOuterBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover,
        interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundarySubsetRootsCanonicalRootedSharedEdgeFaceMembershipCover,
        interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover,
        peeledEndpointTouchPeelFaces]
    simpa [planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData,
      planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData]
      using hInterior
  have hFaceEndpoint :
      (1 : Fin 4) ∈ edgeEndpointSupport
        (peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchPeelFace.1) :=
    (mem_edgeEndpointSupport_iff
      (peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchPeelFace.1)).2
      ⟨pet12, by decide, vertex_one_mem_pet12⟩
  have hBoundaryEndpoint :
      (1 : Fin 4) ∈ edgeEndpointSupport
        (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces) :=
    (mem_edgeEndpointSupport_iff
      (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)).2
      ⟨pet01, pet01_mem_selectedBoundarySupport, vertex_one_mem_pet01⟩
  exact (Finset.disjoint_left.mp
    (hNoTouch peeledEndpointTouchPeelFace hpeel)) hFaceEndpoint hBoundaryEndpoint

/-- The same failure stated in the aggregate finite-support language: the union of peeled-face
boundary endpoints is not disjoint from selected-boundary endpoints. -/
theorem not_peelFacesEndpointDisjointSelectedBoundarySupport_peeledEndpointTouchAnnulusConstruction :
    ¬ peeledEndpointTouchAnnulusConstruction.peelFacesEndpointDisjointSelectedBoundarySupport := by
  intro hNoTouch
  have hPointwise :
      ∀ f ∈
        (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
          peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData).peelFaces,
        Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
          (edgeEndpointSupport
            (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) := by
    simpa [peeledEndpointTouchAnnulusConstruction] using
      (PlanarBoundaryAnnulusConstruction.peelFacesEndpointDisjointSelectedBoundarySupport_iff
        peeledEndpointTouchAnnulusConstruction).1 hNoTouch
  exact peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch
    hPointwise

/-- The outer-boundary-rooted peeled edge-disjoint package does not imply the stronger
peeled-face endpoint no-touch obligation used by the raw-carrier bridge. -/
theorem
    outerBoundaryRootAdjDistancePeelData_does_not_imply_peelFaces_endpoint_disjoint_selectedBoundarySupport_peeledEndpointTouch :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      ¬ (∀ f ∈
          (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
            peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData).peelFaces,
          Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
                peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch⟩

/-- Even at the annulus-construction layer, peeled-face edge-disjointness from the selected
boundary support does not imply peeled-face endpoint no-touch. -/
theorem
    planarBoundaryAnnulusConstruction_edge_disjoint_peelFaces_does_not_imply_endpoint_noTouch_peeledEndpointTouch :
    ∃ data : PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding,
      (∀ f ∈ data.peelFaces,
        Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) ∧
        ¬ (∀ f ∈ data.peelFaces,
          Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
                peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) := by
  exact ⟨peeledEndpointTouchAnnulusConstruction,
    peeledEndpointTouchAnnulusConstruction_peelFaces_edge_disjoint_selectedBoundarySupport,
    peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch⟩

/-- The aggregate finite-support formulation is also not derivable from peeled-face edge
disjointness at the annulus-construction surface. -/
theorem
    planarBoundaryAnnulusConstruction_edge_disjoint_peelFaces_does_not_imply_aggregate_endpoint_noTouch_peeledEndpointTouch :
    ∃ data : PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding,
      (∀ f ∈ data.peelFaces,
        Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) ∧
        ¬ data.peelFacesEndpointDisjointSelectedBoundarySupport := by
  exact ⟨peeledEndpointTouchAnnulusConstruction,
    peeledEndpointTouchAnnulusConstruction_peelFaces_edge_disjoint_selectedBoundarySupport,
    not_peelFacesEndpointDisjointSelectedBoundarySupport_peeledEndpointTouchAnnulusConstruction⟩

/-- There is no theorem, even for this fixed embedding, deriving peeled-face endpoint no-touch
from annulus-construction data plus peeled-face edge-disjointness from the selected boundary. -/
theorem
    not_forall_planarBoundaryAnnulusConstruction_edge_disjoint_implies_endpoint_noTouch_peeledEndpointTouch :
    ¬ (∀ data : PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding,
      (∀ f ∈ data.peelFaces,
        Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) →
        ∀ f ∈ data.peelFaces,
          Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
                peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) := by
  intro h
  exact peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch
    (h peeledEndpointTouchAnnulusConstruction
      peeledEndpointTouchAnnulusConstruction_peelFaces_edge_disjoint_selectedBoundarySupport)

/-- The same fixed-embedding obstruction for the aggregate peeled-face endpoint carrier. -/
theorem
    not_forall_planarBoundaryAnnulusConstruction_edge_disjoint_implies_aggregate_endpoint_noTouch_peeledEndpointTouch :
    ¬ (∀ data : PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding,
      (∀ f ∈ data.peelFaces,
        Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) →
        data.peelFacesEndpointDisjointSelectedBoundarySupport) := by
  intro h
  exact not_peelFacesEndpointDisjointSelectedBoundarySupport_peeledEndpointTouchAnnulusConstruction
    (h peeledEndpointTouchAnnulusConstruction
      peeledEndpointTouchAnnulusConstruction_peelFaces_edge_disjoint_selectedBoundarySupport)


end Theorem49InteriorVerticesEndpointObstruction

end Mettapedia.GraphTheory.FourColor
