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

/-- A two-edge path graph used to isolate the endpoint-level obstruction in the
interior-vertex route. -/
def sharedEndpointGraph : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet ({s(0, 1), s(1, 2)} : Set (Sym2 (Fin 3)))

def eb01 : sharedEndpointGraph.edgeSet := ⟨s(0, 1), by simp [sharedEndpointGraph]⟩

def ei12 : sharedEndpointGraph.edgeSet := ⟨s(1, 2), by simp [sharedEndpointGraph]⟩

theorem eb01_ne_ei12 : eb01 ≠ ei12 := by
  intro h
  have := congrArg Subtype.val h
  simp [eb01, ei12] at this

theorem edge_eq_eb01_or_ei12 (e : sharedEndpointGraph.edgeSet) : e = eb01 ∨ e = ei12 := by
  have h : (e.1 = s(0, 1) ∨ e.1 = s(1, 2)) ∧ ¬ e.1.IsDiag := by
    simpa [sharedEndpointGraph] using e.2
  rcases h.1 with h01 | h12
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr (Subtype.ext h12)

abbrev SharedFace := Fin 2

def sharedFaces : Finset SharedFace := Finset.univ

def sharedFaceBoundary : SharedFace → Finset sharedEndpointGraph.edgeSet
  | ⟨0, _⟩ => {eb01, ei12}
  | ⟨1, _⟩ => {ei12}

theorem totalIncidenceCount_eb01 :
    totalIncidenceCount sharedFaceBoundary sharedFaces eb01 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      sharedFaces.filter (fun f => eb01 ∈ sharedFaceBoundary f) = {(0 : SharedFace)} := by
    ext f
    fin_cases f <;> simp [sharedFaces, sharedFaceBoundary, eb01_ne_ei12]
  rw [hfilter]
  simp

theorem totalIncidenceCount_ei12 :
    totalIncidenceCount sharedFaceBoundary sharedFaces ei12 = 2 := by
  unfold totalIncidenceCount
  have hfilter :
      sharedFaces.filter (fun f => ei12 ∈ sharedFaceBoundary f) = sharedFaces := by
    ext f
    fin_cases f <;> simp [sharedFaces, sharedFaceBoundary]
  rw [hfilter]
  simp [sharedFaces]

/-- A weak boundary-aware embedding whose face-incidence data makes `eb01` a selected-boundary
edge and `ei12` an interior edge.  The edges share vertex `1`, so edge-level disjointness is not
enough for the raw interior-endpoint carrier. -/
def sharedEndpointEmbedding : PlaneEmbeddingWithBoundary sharedEndpointGraph where
  Face := SharedFace
  faceDecidableEq := inferInstance
  faces := sharedFaces
  faceBoundary := sharedFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases edge_eq_eb01_or_ei12 e with rfl | rfl <;>
      simp [sharedFaces, sharedFaceBoundary]
  edge_one_or_two_faces := by
    intro e _he
    rcases edge_eq_eb01_or_ei12 e with rfl | rfl
    · left
      exact totalIncidenceCount_eb01
    · right
      exact totalIncidenceCount_ei12

def sharedFaceOne : {f // f ∈ sharedEndpointEmbedding.faces} :=
  ⟨(1 : SharedFace), by simp [sharedEndpointEmbedding, sharedFaces]⟩

theorem eb01_mem_selectedBoundarySupport :
    eb01 ∈ selectedBoundarySupport
      sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
      sharedEndpointEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by simp [sharedEndpointEmbedding, sharedFaces, sharedFaceBoundary],
    totalIncidenceCount_eb01⟩

theorem ei12_mem_interiorEdgeSupport :
    ei12 ∈ interiorEdgeSupport sharedEndpointEmbedding.faceBoundary
      sharedEndpointEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by simp [sharedEndpointEmbedding, sharedFaces, sharedFaceBoundary],
    totalIncidenceCount_ei12⟩

theorem vertex_one_mem_eb01 : (1 : Fin 3) ∈ (eb01 : Sym2 (Fin 3)) := by
  simp [eb01]

theorem vertex_one_mem_ei12 : (1 : Fin 3) ∈ (ei12 : Sym2 (Fin 3)) := by
  simp [ei12]

theorem planarEmbeddingBoundaryEdgeEndpointAdj_eb01_ei12 :
    planarEmbeddingBoundaryEdgeEndpointAdj eb01 ei12 := by
  exact ⟨eb01_ne_ei12, 1, vertex_one_mem_eb01, vertex_one_mem_ei12⟩

/-- The same weak incidence model still has a linear endpoint-sharing order on every face
boundary.  Thus linear boundary-order data alone cannot prove the raw endpoint-support
separation needed below. -/
def sharedEndpointOrderedFaceBoundaryData :
    PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData sharedEndpointEmbedding where
  faceBoundaryOrder := fun f => if f.1 = (0 : SharedFace) then [eb01, ei12] else [ei12]
  hchain := by
    intro f
    by_cases hf : f.1 = (0 : SharedFace)
    · simp [hf, planarEmbeddingBoundaryEdgeEndpointAdj_eb01_ei12]
    · simp [hf]
  hnodup := by
    intro f
    by_cases hf : f.1 = (0 : SharedFace)
    · simp [hf, eb01_ne_ei12]
    · simp [hf]
  hmem := by
    intro f e
    rcases f with ⟨f, hfmem⟩
    change SharedFace at f
    fin_cases f <;>
      rcases edge_eq_eb01_or_ei12 e with rfl | rfl <;>
        simp [sharedEndpointEmbedding, sharedFaces, sharedFaceBoundary, eb01_ne_ei12]

theorem nonempty_orderedFaceBoundaryData_sharedEndpoint :
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData sharedEndpointEmbedding) :=
  ⟨sharedEndpointOrderedFaceBoundaryData⟩

theorem nonempty_faceBoundaryRunGeometry_sharedEndpoint :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry sharedEndpointEmbedding) :=
  ⟨sharedEndpointOrderedFaceBoundaryData.toFaceBoundaryRunGeometry⟩

theorem sharedFaceOne_faceBoundaryOrder_eq_singleton
    (data : PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData sharedEndpointEmbedding) :
    data.faceBoundaryOrder sharedFaceOne = [ei12] := by
  generalize hrun : data.faceBoundaryOrder sharedFaceOne = run
  have hmem_i : ei12 ∈ run := by
    simpa [hrun] using
      (data.hmem sharedFaceOne ei12).2
        (by simp [sharedEndpointEmbedding, sharedFaceOne, sharedFaceBoundary])
  have hnodup : run.Nodup := by
    simpa [hrun] using data.hnodup sharedFaceOne
  have hsubset : ∀ e ∈ run, e = ei12 := by
    intro e he
    have hface : e ∈ sharedEndpointEmbedding.faceBoundary sharedFaceOne.1 := by
      exact (data.hmem sharedFaceOne e).1 (by simpa [hrun] using he)
    rcases edge_eq_eb01_or_ei12 e with rfl | rfl
    · exfalso
      simp [sharedEndpointEmbedding, sharedFaceOne, sharedFaceBoundary, eb01_ne_ei12] at hface
    · rfl
  cases run with
  | nil =>
      cases hmem_i
  | cons a tl =>
      have ha : a = ei12 := hsubset a (by simp)
      subst a
      have hnotmem : ei12 ∉ tl := (List.nodup_cons.mp hnodup).1
      have htl : tl = [] := by
        apply List.eq_nil_iff_forall_not_mem.2
        intro e he
        exact hnotmem ((hsubset e (by simp [he])) ▸ he)
      simp [htl]

theorem not_planarEmbeddingBoundaryEdgeEndpointAdj_ei12_self :
    ¬ planarEmbeddingBoundaryEdgeEndpointAdj ei12 ei12 := by
  intro h
  exact h.1 rfl

theorem not_nonempty_cyclicOrderedFaceBoundaryData_sharedEndpoint :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData sharedEndpointEmbedding) := by
  rintro ⟨data⟩
  have hrun : data.faceBoundaryOrder sharedFaceOne = [ei12] :=
    sharedFaceOne_faceBoundaryOrder_eq_singleton data.toOrderedFaceBoundaryData
  have hwrap : planarEmbeddingBoundaryEdgeEndpointAdj ei12 ei12 :=
    data.hwrap sharedFaceOne ei12 ei12 (by simp [hrun]) (by simp [hrun])
  exact not_planarEmbeddingBoundaryEdgeEndpointAdj_ei12_self hwrap

theorem not_nonempty_faceBoundaryClosedRunGeometry_sharedEndpoint :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry sharedEndpointEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedRunGeometry]
  exact not_nonempty_cyclicOrderedFaceBoundaryData_sharedEndpoint

theorem not_nonempty_faceBoundaryClosedVertexWalkGeometry_sharedEndpoint :
    ¬ Nonempty
      (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry sharedEndpointEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry]
  exact not_nonempty_cyclicOrderedFaceBoundaryData_sharedEndpoint

theorem not_nonempty_faceBoundaryClosedWalkGeometry_sharedEndpoint :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry sharedEndpointEmbedding) := by
  intro h
  exact not_nonempty_cyclicOrderedFaceBoundaryData_sharedEndpoint
    (nonempty_faceBoundaryClosedWalkGeometry_implies_nonempty_cyclicOrderedFaceBoundaryData h)

/-- The edge supports are disjoint for the usual incidence-count reason. -/
theorem selectedBoundarySupport_disjoint_interiorEdgeSupport_sharedEndpoint :
    Disjoint
      (selectedBoundarySupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
        sharedEndpointEmbedding.faces)
      (interiorEdgeSupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces) :=
  selectedBoundarySupport_disjoint_interiorEdgeSupport
    sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces

/-- Nevertheless, a selected-boundary edge and an interior edge can share a primal endpoint. -/
theorem exists_selectedBoundarySupport_interiorEdgeSupport_shared_endpoint :
    ∃ v : Fin 3, ∃ eInterior eBoundary : sharedEndpointGraph.edgeSet,
      eInterior ∈ interiorEdgeSupport sharedEndpointEmbedding.faceBoundary
        sharedEndpointEmbedding.faces ∧
      eBoundary ∈ selectedBoundarySupport sharedEndpointEmbedding.faceBoundary
        sharedEndpointEmbedding.faces sharedEndpointEmbedding.faces ∧
      v ∈ (eInterior : Sym2 (Fin 3)) ∧
      v ∈ (eBoundary : Sym2 (Fin 3)) :=
  ⟨1, ei12, eb01, ei12_mem_interiorEdgeSupport, eb01_mem_selectedBoundarySupport,
    vertex_one_mem_ei12, vertex_one_mem_eb01⟩

/-- The endpoint-support version of the obstruction: the finite vertex endpoint supports are not
disjoint even though the corresponding edge supports are disjoint. -/
theorem not_endpointSupport_disjoint_sharedEndpoint :
    ¬ Disjoint (interiorEdgeEndpointSupport sharedEndpointEmbedding)
      (edgeEndpointSupport
        (selectedBoundarySupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
          sharedEndpointEmbedding.faces)) := by
  intro hdisj
  have hNoEndpoint :
      ∀ v : Fin 3,
        (∃ e ∈ interiorEdgeSupport sharedEndpointEmbedding.faceBoundary
          sharedEndpointEmbedding.faces, v ∈ (e : Sym2 (Fin 3))) →
          ∀ e ∈ selectedBoundarySupport sharedEndpointEmbedding.faceBoundary
            sharedEndpointEmbedding.faces sharedEndpointEmbedding.faces,
            v ∉ (e : Sym2 (Fin 3)) := by
    exact
      (edgeEndpointSupport_disjoint_iff_no_shared_endpoint
        (interiorEdgeSupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces)
        (selectedBoundarySupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
          sharedEndpointEmbedding.faces)).1
        (by simpa [interiorEdgeEndpointSupport] using hdisj)
  exact hNoEndpoint 1 ⟨ei12, ei12_mem_interiorEdgeSupport, vertex_one_mem_ei12⟩
    eb01 eb01_mem_selectedBoundarySupport vertex_one_mem_eb01

/-- Linear endpoint-sharing face-boundary order is still insufficient for the raw endpoint route:
the countermodel admits such ordered runs while failing endpoint-support disjointness. -/
theorem orderedFaceBoundaryData_does_not_imply_endpointSupport_disjoint_sharedEndpoint :
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData sharedEndpointEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport sharedEndpointEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
            sharedEndpointEmbedding.faces)) :=
  ⟨nonempty_orderedFaceBoundaryData_sharedEndpoint, not_endpointSupport_disjoint_sharedEndpoint⟩

/-- The shared-endpoint countermodel is a linear-run obstruction only: it refutes the linear
boundary-order shortcut, but the cyclic and honest closed-walk source layers reject it because the
one-edge interior face would have to close by making an edge adjacent to itself. -/
theorem linearRun_endpointSupport_obstruction_not_closedWalk_sharedEndpoint :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry sharedEndpointEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport sharedEndpointEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
            sharedEndpointEmbedding.faces)) ∧
      ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry sharedEndpointEmbedding) ∧
      ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry sharedEndpointEmbedding) :=
  ⟨nonempty_faceBoundaryRunGeometry_sharedEndpoint, not_endpointSupport_disjoint_sharedEndpoint,
    not_nonempty_faceBoundaryClosedRunGeometry_sharedEndpoint,
    not_nonempty_faceBoundaryClosedWalkGeometry_sharedEndpoint⟩

/-- This concrete model refutes the false shortcut from edge-level disjointness to the
endpoint-level separation needed for raw interior-edge endpoints. -/
theorem edge_disjointness_does_not_imply_endpoint_separation_sharedEndpoint :
    Disjoint
        (selectedBoundarySupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
          sharedEndpointEmbedding.faces)
        (interiorEdgeSupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces) ∧
      ¬ (∀ v : Fin 3,
        (∃ e ∈ interiorEdgeSupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces,
          v ∈ (e : Sym2 (Fin 3))) →
          ∀ e ∈ selectedBoundarySupport sharedEndpointEmbedding.faceBoundary
            sharedEndpointEmbedding.faces sharedEndpointEmbedding.faces,
            v ∉ (e : Sym2 (Fin 3))) := by
  constructor
  · exact selectedBoundarySupport_disjoint_interiorEdgeSupport_sharedEndpoint
  · intro hEndpoint
    exact hEndpoint 1 ⟨ei12, ei12_mem_interiorEdgeSupport, vertex_one_mem_ei12⟩
      eb01 eb01_mem_selectedBoundarySupport vertex_one_mem_eb01

/-- Consequently the raw interior-edge endpoint carrier is not already the purified carrier in
this model. -/
theorem selectedBoundaryInteriorEdgeEndpointVertices_ne_interiorEdgeEndpointSupport_sharedEndpoint :
    selectedBoundaryInteriorEdgeEndpointVertices sharedEndpointEmbedding ≠
      interiorEdgeEndpointSupport sharedEndpointEmbedding :=
  selectedBoundaryInteriorEdgeEndpointVertices_ne_interiorEdgeEndpointSupport_of_endpoint_shared
    (emb := sharedEndpointEmbedding) (v := (1 : Fin 3)) (eInterior := ei12)
    (eBoundary := eb01) ei12_mem_interiorEdgeSupport eb01_mem_selectedBoundarySupport
    vertex_one_mem_ei12 vertex_one_mem_eb01

/-- A two-triangle diamond used to test whether cyclic closed face-boundary runs are enough to
force the raw endpoint-separation side condition. -/
def diamondGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(0, 2), s(1, 3), s(2, 3)} : Set (Sym2 (Fin 4)))

def d01 : diamondGraph.edgeSet := ⟨s(0, 1), by simp [diamondGraph]⟩

def d12 : diamondGraph.edgeSet := ⟨s(1, 2), by simp [diamondGraph]⟩

def d02 : diamondGraph.edgeSet := ⟨s(0, 2), by simp [diamondGraph]⟩

def d13 : diamondGraph.edgeSet := ⟨s(1, 3), by simp [diamondGraph]⟩

def d23 : diamondGraph.edgeSet := ⟨s(2, 3), by simp [diamondGraph]⟩

theorem d01_ne_d12 : d01 ≠ d12 := by
  intro h
  have := congrArg Subtype.val h
  simp [d01, d12] at this

theorem d01_ne_d02 : d01 ≠ d02 := by
  intro h
  have := congrArg Subtype.val h
  simp [d01, d02] at this

theorem d12_ne_d02 : d12 ≠ d02 := by
  intro h
  have := congrArg Subtype.val h
  simp [d12, d02] at this

theorem d12_ne_d23 : d12 ≠ d23 := by
  intro h
  have := congrArg Subtype.val h
  simp [d12, d23] at this

theorem d12_ne_d13 : d12 ≠ d13 := by
  intro h
  have := congrArg Subtype.val h
  simp [d12, d13] at this

theorem d23_ne_d13 : d23 ≠ d13 := by
  intro h
  have := congrArg Subtype.val h
  simp [d23, d13] at this

theorem diamond_edge_eq
    (e : diamondGraph.edgeSet) :
    e = d01 ∨ e = d12 ∨ e = d02 ∨ e = d13 ∨ e = d23 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(0, 2) ∨ e.1 = s(1, 3) ∨
          e.1 = s(2, 3)) ∧
        ¬ e.1.IsDiag := by
    simpa [diamondGraph] using e.2
  rcases h.1 with h01 | h12 | h02 | h13 | h23
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr (Or.inl (Subtype.ext h12))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h02)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h13))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h23))))

abbrev DiamondFace := Fin 2

def diamondFaces : Finset DiamondFace := Finset.univ

def diamondFaceBoundary : DiamondFace → Finset diamondGraph.edgeSet
  | ⟨0, _⟩ => {d01, d12, d02}
  | ⟨1, _⟩ => {d12, d23, d13}

theorem totalIncidenceCount_d01 :
    totalIncidenceCount diamondFaceBoundary diamondFaces d01 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondFaces.filter (fun f => d01 ∈ diamondFaceBoundary f) = {(0 : DiamondFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_d12 :
    totalIncidenceCount diamondFaceBoundary diamondFaces d12 = 2 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondFaces.filter (fun f => d12 ∈ diamondFaceBoundary f) = diamondFaces := by
    ext f
    fin_cases f <;> simp [diamondFaces, diamondFaceBoundary]
  rw [hfilter]
  simp [diamondFaces]

theorem totalIncidenceCount_d02 :
    totalIncidenceCount diamondFaceBoundary diamondFaces d02 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondFaces.filter (fun f => d02 ∈ diamondFaceBoundary f) = {(0 : DiamondFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_d13 :
    totalIncidenceCount diamondFaceBoundary diamondFaces d13 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondFaces.filter (fun f => d13 ∈ diamondFaceBoundary f) = {(1 : DiamondFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_d23 :
    totalIncidenceCount diamondFaceBoundary diamondFaces d23 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondFaces.filter (fun f => d23 ∈ diamondFaceBoundary f) = {(1 : DiamondFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

/-- A weak incidence embedding of the two-triangle diamond.  The shared edge `d12` is an interior
edge, while `d01` is a selected-boundary edge sharing endpoint `1` with it. -/
def diamondEmbedding : PlaneEmbeddingWithBoundary diamondGraph where
  Face := DiamondFace
  faceDecidableEq := inferInstance
  faces := diamondFaces
  faceBoundary := diamondFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases diamond_edge_eq e with rfl | rfl | rfl | rfl | rfl <;>
      simp [diamondFaces, diamondFaceBoundary]
  edge_one_or_two_faces := by
    intro e _he
    rcases diamond_edge_eq e with rfl | rfl | rfl | rfl | rfl
    · left
      exact totalIncidenceCount_d01
    · right
      exact totalIncidenceCount_d12
    · left
      exact totalIncidenceCount_d02
    · left
      exact totalIncidenceCount_d13
    · left
      exact totalIncidenceCount_d23

theorem d01_mem_selectedBoundarySupport :
    d01 ∈ selectedBoundarySupport
      diamondEmbedding.faceBoundary diamondEmbedding.faces diamondEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by simp [diamondEmbedding, diamondFaces, diamondFaceBoundary],
    totalIncidenceCount_d01⟩

theorem d02_mem_selectedBoundarySupport :
    d02 ∈ selectedBoundarySupport
      diamondEmbedding.faceBoundary diamondEmbedding.faces diamondEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by simp [diamondEmbedding, diamondFaces, diamondFaceBoundary],
    totalIncidenceCount_d02⟩

theorem d13_mem_selectedBoundarySupport :
    d13 ∈ selectedBoundarySupport
      diamondEmbedding.faceBoundary diamondEmbedding.faces diamondEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by simp [diamondEmbedding, diamondFaces, diamondFaceBoundary],
    totalIncidenceCount_d13⟩

theorem d23_mem_selectedBoundarySupport :
    d23 ∈ selectedBoundarySupport
      diamondEmbedding.faceBoundary diamondEmbedding.faces diamondEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by simp [diamondEmbedding, diamondFaces, diamondFaceBoundary],
    totalIncidenceCount_d23⟩

theorem d12_mem_interiorEdgeSupport :
    d12 ∈ interiorEdgeSupport diamondEmbedding.faceBoundary diamondEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by simp [diamondEmbedding, diamondFaces, diamondFaceBoundary],
    totalIncidenceCount_d12⟩

theorem vertex_one_mem_d01 : (1 : Fin 4) ∈ (d01 : Sym2 (Fin 4)) := by
  simp [d01]

theorem vertex_one_mem_d12 : (1 : Fin 4) ∈ (d12 : Sym2 (Fin 4)) := by
  simp [d12]

theorem diamondAdj_d01_d12 : planarEmbeddingBoundaryEdgeEndpointAdj d01 d12 := by
  exact ⟨d01_ne_d12, 1, vertex_one_mem_d01, vertex_one_mem_d12⟩

theorem diamondAdj_d12_d02 : planarEmbeddingBoundaryEdgeEndpointAdj d12 d02 := by
  refine ⟨d12_ne_d02, 2, ?_, ?_⟩ <;> simp [d12, d02]

theorem diamondAdj_d02_d01 : planarEmbeddingBoundaryEdgeEndpointAdj d02 d01 := by
  refine ⟨d01_ne_d02.symm, 0, ?_, ?_⟩ <;> simp [d02, d01]

theorem diamondAdj_d12_d23 : planarEmbeddingBoundaryEdgeEndpointAdj d12 d23 := by
  refine ⟨d12_ne_d23, 2, ?_, ?_⟩ <;> simp [d12, d23]

theorem diamondAdj_d23_d13 : planarEmbeddingBoundaryEdgeEndpointAdj d23 d13 := by
  refine ⟨d23_ne_d13, 3, ?_, ?_⟩ <;> simp [d23, d13]

theorem diamondAdj_d13_d12 : planarEmbeddingBoundaryEdgeEndpointAdj d13 d12 := by
  refine ⟨d12_ne_d13.symm, 1, ?_, ?_⟩ <;> simp [d13, d12]

/-- The diamond has genuine cyclic closed face-boundary runs on both triangular faces. -/
def diamondCyclicOrderedFaceBoundaryData :
    PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData diamondEmbedding where
  faceBoundaryOrder := fun f =>
    if f.1 = (0 : DiamondFace) then [d01, d12, d02] else [d12, d23, d13]
  hchain := by
    intro f
    by_cases hf : f.1 = (0 : DiamondFace)
    · simp [hf, diamondAdj_d01_d12, diamondAdj_d12_d02]
    · simp [hf, diamondAdj_d12_d23, diamondAdj_d23_d13]
  hnodup := by
    intro f
    by_cases hf : f.1 = (0 : DiamondFace)
    · simp [hf, d01_ne_d12, d01_ne_d02, d12_ne_d02]
    · simp [hf, d12_ne_d23, d12_ne_d13, d23_ne_d13]
  hmem := by
    intro f e
    rcases f with ⟨f, hfmem⟩
    change DiamondFace at f
    fin_cases f <;>
      rcases diamond_edge_eq e with rfl | rfl | rfl | rfl | rfl <;>
        simp [diamondEmbedding, diamondFaces, diamondFaceBoundary,
          d01_ne_d12, d01_ne_d02, d12_ne_d02, d12_ne_d23, d12_ne_d13, d23_ne_d13]
  hwrap := by
    intro f first last hfirst hlast
    by_cases hf : f.1 = (0 : DiamondFace)
    · have hfirst' : first = d01 := by simpa [hf] using hfirst.symm
      have hlast' : last = d02 := by simpa [hf] using hlast.symm
      subst first
      subst last
      exact diamondAdj_d02_d01
    · have hfirst' : first = d12 := by simpa [hf] using hfirst.symm
      have hlast' : last = d13 := by simpa [hf] using hlast.symm
      subst first
      subst last
      exact diamondAdj_d13_d12

theorem nonempty_cyclicOrderedFaceBoundaryData_diamond :
    Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData diamondEmbedding) :=
  ⟨diamondCyclicOrderedFaceBoundaryData⟩

theorem nonempty_faceBoundaryClosedRunGeometry_diamond :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry diamondEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedRunGeometry]
  exact nonempty_cyclicOrderedFaceBoundaryData_diamond

theorem nonempty_faceBoundaryClosedVertexWalkGeometry_diamond :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry diamondEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry]
  exact nonempty_cyclicOrderedFaceBoundaryData_diamond

def dart01 : diamondGraph.Dart := ⟨((0 : Fin 4), 1), by simp [diamondGraph]⟩

def dart12 : diamondGraph.Dart := ⟨((1 : Fin 4), 2), by simp [diamondGraph]⟩

def dart20 : diamondGraph.Dart := ⟨((2 : Fin 4), 0), by simp [diamondGraph]⟩

def dart23 : diamondGraph.Dart := ⟨((2 : Fin 4), 3), by simp [diamondGraph]⟩

def dart31 : diamondGraph.Dart := ⟨((3 : Fin 4), 1), by simp [diamondGraph]⟩

/-- The lower triangular face of the diamond as an honest oriented facial dart cycle. -/
def diamondFace0PureDartCycle
    (hf : (0 : DiamondFace) ∈ diamondEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle diamondEmbedding ⟨(0 : DiamondFace), hf⟩ where
  darts := [dart01, dart12, dart20]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dart01, dart12, dart20]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondEmbedding, diamondFaceBoundary, d01, d12, d02, dart01, dart12, dart20]
  hface_sub := by
    intro e he
    have he' : e = d01 ∨ e = d12 ∨ e = d02 := by
      simpa [diamondEmbedding, diamondFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [d01, d12, d02, dart01, dart12, dart20]

/-- The upper triangular face of the diamond as an honest oriented facial dart cycle. -/
def diamondFace1PureDartCycle
    (hf : (1 : DiamondFace) ∈ diamondEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle diamondEmbedding ⟨(1 : DiamondFace), hf⟩ where
  darts := [dart12, dart23, dart31]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dart12, dart23, dart31]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondEmbedding, diamondFaceBoundary, d12, d23, d13, dart12, dart23, dart31]
  hface_sub := by
    intro e he
    have he' : e = d12 ∨ e = d23 ∨ e = d13 := by
      simpa [diamondEmbedding, diamondFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [d12, d23, d13, dart12, dart23, dart31]

/-- The two-triangle diamond has actual facial dart cycles, hence actual facial closed walks. -/
def diamondFaceBoundaryPureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry diamondEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change DiamondFace at f
    by_cases h0 : f = (0 : DiamondFace)
    · subst f
      exact diamondFace0PureDartCycle hfmem
    · have h1 : f = (1 : DiamondFace) := by
        fin_cases f
        · exact False.elim (h0 rfl)
        · rfl
      subst f
      exact diamondFace1PureDartCycle hfmem

theorem nonempty_faceBoundaryClosedWalkGeometry_diamond :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry diamondEmbedding) :=
  ⟨diamondFaceBoundaryPureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry⟩

/-- A rotated lower-face dart cycle whose induced linear edge run begins with the two selected
boundary edges. This is used to show that selected-arc contiguity is still not enough to force
endpoint separation. -/
def diamondFace0SelectedArcPureDartCycle
    (hf : (0 : DiamondFace) ∈ diamondEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle diamondEmbedding ⟨(0 : DiamondFace), hf⟩ where
  darts := [dart20, dart01, dart12]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dart20, dart01, dart12]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondEmbedding, diamondFaceBoundary, d01, d12, d02, dart20, dart01, dart12]
  hface_sub := by
    intro e he
    have he' : e = d01 ∨ e = d12 ∨ e = d02 := by
      simpa [diamondEmbedding, diamondFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [d01, d12, d02, dart20, dart01, dart12]

/-- A rotated upper-face dart cycle whose induced linear edge run begins with the two selected
boundary edges. -/
def diamondFace1SelectedArcPureDartCycle
    (hf : (1 : DiamondFace) ∈ diamondEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle diamondEmbedding ⟨(1 : DiamondFace), hf⟩ where
  darts := [dart23, dart31, dart12]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dart23, dart31, dart12]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondEmbedding, diamondFaceBoundary, d12, d23, d13, dart23, dart31, dart12]
  hface_sub := by
    intro e he
    have he' : e = d12 ∨ e = d23 ∨ e = d13 := by
      simpa [diamondEmbedding, diamondFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [d12, d23, d13, dart23, dart31, dart12]

/-- The diamond also admits honest facial dart cycles whose induced linear runs make the selected
boundary edges contiguous on each triangular face. -/
def diamondSelectedArcPureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry diamondEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change DiamondFace at f
    by_cases h0 : f = (0 : DiamondFace)
    · subst f
      exact diamondFace0SelectedArcPureDartCycle hfmem
    · have h1 : f = (1 : DiamondFace) := by
        fin_cases f
        · exact False.elim (h0 rfl)
        · rfl
      subst f
      exact diamondFace1SelectedArcPureDartCycle hfmem

def diamondSelectedArcClosedWalkEmbeddingData :
    PlanarBoundaryClosedWalkEmbeddingData diamondEmbedding :=
  diamondSelectedArcPureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

theorem diamondSelectedArcClosedWalkEmbeddingData_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace diamondEmbedding.faces,
      (diamondSelectedArcClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f := by
  intro f
  let f0 : AmbientFace diamondEmbedding.faces :=
    ⟨(0 : DiamondFace), by simp [diamondEmbedding, diamondFaces]⟩
  let f1 : AmbientFace diamondEmbedding.faces :=
    ⟨(1 : DiamondFace), by simp [diamondEmbedding, diamondFaces]⟩
  have hf_cases : f = f0 ∨ f = f1 := by
    rcases f with ⟨⟨n, hn⟩, hfmem⟩
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · left
      exact Subtype.ext rfl
    · right
      exact Subtype.ext rfl
  rcases hf_cases with rfl | rfl
  · change
      (diamondSelectedArcClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f0
    refine ⟨[d02, d01], ?_, ?_⟩
    · decide
    · intro e
      rcases diamond_edge_eq e with rfl | rfl | rfl | rfl | rfl <;>
        decide
  · change
      (diamondSelectedArcClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f1
    refine ⟨[d23, d13], ?_, ?_⟩
    · decide
    · intro e
      rcases diamond_edge_eq e with rfl | rfl | rfl | rfl | rfl <;>
        decide

theorem nonempty_closedWalkEmbeddingDataAndSelectedBoundaryArcOnFace_diamond :
    ∃ geom : PlanarBoundaryClosedWalkEmbeddingData diamondEmbedding,
      ∀ f : AmbientFace diamondEmbedding.faces,
        (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f :=
  ⟨diamondSelectedArcClosedWalkEmbeddingData,
    diamondSelectedArcClosedWalkEmbeddingData_selectedBoundaryArcOnFace⟩

theorem not_endpointSupport_disjoint_diamond :
    ¬ Disjoint (interiorEdgeEndpointSupport diamondEmbedding)
      (edgeEndpointSupport
        (selectedBoundarySupport diamondEmbedding.faceBoundary diamondEmbedding.faces
          diamondEmbedding.faces)) := by
  intro hdisj
  have hNoEndpoint :
      ∀ v : Fin 4,
        (∃ e ∈ interiorEdgeSupport diamondEmbedding.faceBoundary
          diamondEmbedding.faces, v ∈ (e : Sym2 (Fin 4))) →
          ∀ e ∈ selectedBoundarySupport diamondEmbedding.faceBoundary
            diamondEmbedding.faces diamondEmbedding.faces,
            v ∉ (e : Sym2 (Fin 4)) := by
    exact
      (edgeEndpointSupport_disjoint_iff_no_shared_endpoint
        (interiorEdgeSupport diamondEmbedding.faceBoundary diamondEmbedding.faces)
        (selectedBoundarySupport diamondEmbedding.faceBoundary diamondEmbedding.faces
          diamondEmbedding.faces)).1
        (by simpa [interiorEdgeEndpointSupport] using hdisj)
  exact hNoEndpoint 1 ⟨d12, d12_mem_interiorEdgeSupport, vertex_one_mem_d12⟩
    d01 d01_mem_selectedBoundarySupport vertex_one_mem_d01

/-- Cyclic closed face-boundary runs alone still do not prove the raw endpoint-support separation
needed by the unpurified interior-edge endpoint carrier.  The two-triangle diamond has cyclic
closed runs, but its interior shared edge touches a selected-boundary edge at a primal endpoint. -/
theorem cyclicClosedRun_does_not_imply_endpointSupport_disjoint_diamond :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry diamondEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport diamondEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport diamondEmbedding.faceBoundary diamondEmbedding.faces
            diamondEmbedding.faces)) :=
  ⟨nonempty_faceBoundaryClosedRunGeometry_diamond, not_endpointSupport_disjoint_diamond⟩

/-- Even honest facial closed-walk geometry does not by itself prove the raw endpoint-support
separation needed by the unpurified interior-edge endpoint carrier.  The two-triangle diamond has
closed walks around both triangular faces, but its interior shared edge touches a selected-boundary
edge at a primal endpoint. -/
theorem faceBoundaryClosedWalkGeometry_does_not_imply_endpointSupport_disjoint_diamond :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry diamondEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport diamondEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport diamondEmbedding.faceBoundary diamondEmbedding.faces
            diamondEmbedding.faces)) :=
  ⟨nonempty_faceBoundaryClosedWalkGeometry_diamond, not_endpointSupport_disjoint_diamond⟩

/-- Even honest facial closed walks whose induced linear runs make the selected-boundary edges a
contiguous arc on each face do not by themselves imply the endpoint-support separation needed by
the raw interior-edge endpoint carrier. The missing ingredient is still an annular no-touch
condition tying the chosen interior to the selected boundary. -/
theorem closedWalkSelectedArc_does_not_imply_endpointSupport_disjoint_diamond :
    (∃ geom : PlanarBoundaryClosedWalkEmbeddingData diamondEmbedding,
      ∀ f : AmbientFace diamondEmbedding.faces,
        (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport diamondEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport diamondEmbedding.faceBoundary diamondEmbedding.faces
            diamondEmbedding.faces)) :=
  ⟨nonempty_closedWalkEmbeddingDataAndSelectedBoundaryArcOnFace_diamond,
    not_endpointSupport_disjoint_diamond⟩


end Theorem49InteriorVerticesEndpointObstruction

end Mettapedia.GraphTheory.FourColor
