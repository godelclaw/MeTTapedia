import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVerticesAnnulusConstruction
import Mettapedia.GraphTheory.FourColor.Theorem49SynthesisCore
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusConstruction
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceCanonicalWitness
import Mettapedia.GraphTheory.FacialCyclePlanarEmbeddingWithBoundary
import Mettapedia.GraphTheory.OrderedPlanarEmbeddingWithBoundary
import Mettapedia.GraphTheory.WalkPlanarEmbeddingWithBoundary
import Mathlib.Tactic.FinCases

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49InteriorVerticesEndpointObstruction
/-- A two-component boundary model: one component is the diamond carrying the raw endpoint
failure, and the second component is a separate triangular boundary component.  This lets the
model satisfy the two-root annulus boundary-source package while preserving the endpoint-support
obstruction. -/
def diamondWithTriangleGraph : SimpleGraph (Fin 7) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(0, 2), s(1, 3), s(2, 3),
        s(4, 5), s(5, 6), s(6, 4)} : Set (Sym2 (Fin 7)))

def dt01 : diamondWithTriangleGraph.edgeSet := ⟨s(0, 1), by simp [diamondWithTriangleGraph]⟩

def dt12 : diamondWithTriangleGraph.edgeSet := ⟨s(1, 2), by simp [diamondWithTriangleGraph]⟩

def dt02 : diamondWithTriangleGraph.edgeSet := ⟨s(0, 2), by simp [diamondWithTriangleGraph]⟩

def dt13 : diamondWithTriangleGraph.edgeSet := ⟨s(1, 3), by simp [diamondWithTriangleGraph]⟩

def dt23 : diamondWithTriangleGraph.edgeSet := ⟨s(2, 3), by simp [diamondWithTriangleGraph]⟩

def dt45 : diamondWithTriangleGraph.edgeSet := ⟨s(4, 5), by simp [diamondWithTriangleGraph]⟩

def dt56 : diamondWithTriangleGraph.edgeSet := ⟨s(5, 6), by simp [diamondWithTriangleGraph]⟩

def dt64 : diamondWithTriangleGraph.edgeSet := ⟨s(6, 4), by simp [diamondWithTriangleGraph]⟩

theorem diamondWithTriangle_edge_eq
    (e : diamondWithTriangleGraph.edgeSet) :
    e = dt01 ∨ e = dt12 ∨ e = dt02 ∨ e = dt13 ∨ e = dt23 ∨
      e = dt45 ∨ e = dt56 ∨ e = dt64 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(0, 2) ∨ e.1 = s(1, 3) ∨
          e.1 = s(2, 3) ∨ e.1 = s(4, 5) ∨ e.1 = s(5, 6) ∨ e.1 = s(6, 4)) ∧
        ¬ e.1.IsDiag := by
    simpa [diamondWithTriangleGraph] using e.2
  rcases h.1 with h01 | h12 | h02 | h13 | h23 | h45 | h56 | h64
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr (Or.inl (Subtype.ext h12))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h02)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h13))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h23)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h45))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h56)))))))
  · exact Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h64)))))))

noncomputable instance diamondWithTriangleGraph_edgeSet_fintype :
    Fintype diamondWithTriangleGraph.edgeSet :=
  ⟨{dt01, dt12, dt02, dt13, dt23, dt45, dt56, dt64}, by
    intro e
    rcases diamondWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp⟩

instance diamondWithTriangleGraph_lineGraph_adj_decidable :
    DecidableRel diamondWithTriangleGraph.lineGraph.Adj := by
  intro e f
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  infer_instance

abbrev DiamondWithTriangleFace := Fin 3

def diamondWithTriangleFaces : Finset DiamondWithTriangleFace := Finset.univ

def diamondWithTriangleFaceBoundary :
    DiamondWithTriangleFace → Finset diamondWithTriangleGraph.edgeSet
  | ⟨0, _⟩ => {dt02, dt01, dt12}
  | ⟨1, _⟩ => {dt23, dt13, dt12}
  | ⟨2, _⟩ => {dt45, dt56, dt64}

theorem totalIncidenceCount_dt01 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt01 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt01 ∈ diamondWithTriangleFaceBoundary f) =
        {(0 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt12 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt12 = 2 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt12 ∈ diamondWithTriangleFaceBoundary f) =
        ({(0 : DiamondWithTriangleFace), (1 : DiamondWithTriangleFace)} : Finset _) := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt02 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt02 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt02 ∈ diamondWithTriangleFaceBoundary f) =
        {(0 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt13 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt13 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt13 ∈ diamondWithTriangleFaceBoundary f) =
        {(1 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt23 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt23 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt23 ∈ diamondWithTriangleFaceBoundary f) =
        {(1 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt45 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt45 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt45 ∈ diamondWithTriangleFaceBoundary f) =
        {(2 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt56 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt56 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt56 ∈ diamondWithTriangleFaceBoundary f) =
        {(2 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt64 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt64 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt64 ∈ diamondWithTriangleFaceBoundary f) =
        {(2 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

def diamondWithTriangleEmbedding : PlaneEmbeddingWithBoundary diamondWithTriangleGraph where
  Face := DiamondWithTriangleFace
  faceDecidableEq := inferInstance
  faces := diamondWithTriangleFaces
  faceBoundary := diamondWithTriangleFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases diamondWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Finset.mem_biUnion]
      exact ⟨(0 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(0 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(0 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(1 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(1 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(2 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(2 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(2 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
  edge_one_or_two_faces := by
    intro e _he
    rcases diamondWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left
      exact totalIncidenceCount_dt01
    · right
      exact totalIncidenceCount_dt12
    · left
      exact totalIncidenceCount_dt02
    · left
      exact totalIncidenceCount_dt13
    · left
      exact totalIncidenceCount_dt23
    · left
      exact totalIncidenceCount_dt45
    · left
      exact totalIncidenceCount_dt56
    · left
      exact totalIncidenceCount_dt64

theorem dt01_mem_selectedBoundarySupport :
    dt01 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(0 : DiamondWithTriangleFace), by
        change (0 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt01⟩

theorem dt02_mem_selectedBoundarySupport :
    dt02 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(0 : DiamondWithTriangleFace), by
        change (0 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt02⟩

theorem dt13_mem_selectedBoundarySupport :
    dt13 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(1 : DiamondWithTriangleFace), by
        change (1 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt13⟩

theorem dt23_mem_selectedBoundarySupport :
    dt23 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(1 : DiamondWithTriangleFace), by
        change (1 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt23⟩

theorem dt45_mem_selectedBoundarySupport :
    dt45 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(2 : DiamondWithTriangleFace), by
        change (2 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt45⟩

theorem dt56_mem_selectedBoundarySupport :
    dt56 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(2 : DiamondWithTriangleFace), by
        change (2 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt56⟩

theorem dt64_mem_selectedBoundarySupport :
    dt64 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(2 : DiamondWithTriangleFace), by
        change (2 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt64⟩

theorem dt12_mem_interiorEdgeSupport :
    dt12 ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
      diamondWithTriangleEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(0 : DiamondWithTriangleFace), by
      change (0 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
      exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt12⟩

theorem exists_selectedBoundarySupport_of_dt12_mem_faceBoundary_diamondWithTriangle
    {f : AmbientFace diamondWithTriangleEmbedding.faces}
    (hf12 : dt12 ∈ diamondWithTriangleEmbedding.faceBoundary f.1) :
    ∃ e ∈ diamondWithTriangleEmbedding.faceBoundary f.1,
      e ∈ selectedBoundarySupport
        diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
        diamondWithTriangleEmbedding.faces := by
  rcases f with ⟨f, _hf⟩
  change DiamondWithTriangleFace at f
  fin_cases f
  · exact ⟨dt01, by
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary],
      dt01_mem_selectedBoundarySupport⟩
  · exact ⟨dt13, by
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary],
      dt13_mem_selectedBoundarySupport⟩
  · have hnot :
        dt12 ∉ diamondWithTriangleEmbedding.faceBoundary (2 : DiamondWithTriangleFace) := by
      decide
    exact False.elim (hnot (by simpa using hf12))

theorem dt12_not_mem_selectedBoundarySupport :
    dt12 ∉ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  intro h
  have hcount :
      totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
        diamondWithTriangleEmbedding.faces dt12 = 1 :=
    (mem_selectedBoundarySupport_iff diamondWithTriangleEmbedding.faceBoundary
      diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces).1 h |>.2
  simp [diamondWithTriangleEmbedding, totalIncidenceCount_dt12] at hcount

theorem vertex_one_mem_dt01 : (1 : Fin 7) ∈ (dt01 : Sym2 (Fin 7)) := by
  simp [dt01]

theorem vertex_one_mem_dt12 : (1 : Fin 7) ∈ (dt12 : Sym2 (Fin 7)) := by
  simp [dt12]

theorem not_endpointSupport_disjoint_diamondWithTriangle :
    ¬ Disjoint (interiorEdgeEndpointSupport diamondWithTriangleEmbedding)
      (edgeEndpointSupport
        (selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces)) := by
  intro hdisj
  have hNoEndpoint :
      ∀ v : Fin 7,
        (∃ e ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces, v ∈ (e : Sym2 (Fin 7))) →
          ∀ e ∈ selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces,
            v ∉ (e : Sym2 (Fin 7)) := by
    exact
      (edgeEndpointSupport_disjoint_iff_no_shared_endpoint
        (interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces)
        (selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces)).1
        (by simpa [interiorEdgeEndpointSupport] using hdisj)
  exact hNoEndpoint 1 ⟨dt12, dt12_mem_interiorEdgeSupport, vertex_one_mem_dt12⟩
    dt01 dt01_mem_selectedBoundarySupport vertex_one_mem_dt01

def dtDart01 : diamondWithTriangleGraph.Dart := ⟨((0 : Fin 7), 1), by
  simp [diamondWithTriangleGraph]⟩

def dtDart12 : diamondWithTriangleGraph.Dart := ⟨((1 : Fin 7), 2), by
  simp [diamondWithTriangleGraph]⟩

def dtDart20 : diamondWithTriangleGraph.Dart := ⟨((2 : Fin 7), 0), by
  simp [diamondWithTriangleGraph]⟩

def dtDart23 : diamondWithTriangleGraph.Dart := ⟨((2 : Fin 7), 3), by
  simp [diamondWithTriangleGraph]⟩

def dtDart31 : diamondWithTriangleGraph.Dart := ⟨((3 : Fin 7), 1), by
  simp [diamondWithTriangleGraph]⟩

def dtDart45 : diamondWithTriangleGraph.Dart := ⟨((4 : Fin 7), 5), by
  simp [diamondWithTriangleGraph]⟩

def dtDart56 : diamondWithTriangleGraph.Dart := ⟨((5 : Fin 7), 6), by
  simp [diamondWithTriangleGraph]⟩

def dtDart64 : diamondWithTriangleGraph.Dart := ⟨((6 : Fin 7), 4), by
  simp [diamondWithTriangleGraph]⟩

def diamondWithTriangleFace0SelectedArcPureDartCycle
    (hf : (0 : DiamondWithTriangleFace) ∈ diamondWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      diamondWithTriangleEmbedding ⟨(0 : DiamondWithTriangleFace), hf⟩ where
  darts := [dtDart20, dtDart01, dtDart12]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dtDart20, dtDart01, dtDart12]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary,
        dt02, dt01, dt12, dtDart20, dtDart01, dtDart12]
  hface_sub := by
    intro e he
    have he' : e = dt02 ∨ e = dt01 ∨ e = dt12 := by
      simpa [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [dt02, dt01, dt12, dtDart20, dtDart01, dtDart12]

def diamondWithTriangleFace1SelectedArcPureDartCycle
    (hf : (1 : DiamondWithTriangleFace) ∈ diamondWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      diamondWithTriangleEmbedding ⟨(1 : DiamondWithTriangleFace), hf⟩ where
  darts := [dtDart23, dtDart31, dtDart12]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dtDart23, dtDart31, dtDart12]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary,
        dt23, dt13, dt12, dtDart23, dtDart31, dtDart12]
  hface_sub := by
    intro e he
    have he' : e = dt23 ∨ e = dt13 ∨ e = dt12 := by
      simpa [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [dt23, dt13, dt12, dtDart23, dtDart31, dtDart12]

def diamondWithTriangleFace2PureDartCycle
    (hf : (2 : DiamondWithTriangleFace) ∈ diamondWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      diamondWithTriangleEmbedding ⟨(2 : DiamondWithTriangleFace), hf⟩ where
  darts := [dtDart45, dtDart56, dtDart64]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dtDart45, dtDart56, dtDart64]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary,
        dt45, dt56, dt64, dtDart45, dtDart56, dtDart64]
  hface_sub := by
    intro e he
    have he' : e = dt45 ∨ e = dt56 ∨ e = dt64 := by
      simpa [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [dt45, dt56, dt64, dtDart45, dtDart56, dtDart64]

def diamondWithTrianglePureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry diamondWithTriangleEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change DiamondWithTriangleFace at f
    by_cases h0 : f = (0 : DiamondWithTriangleFace)
    · subst f
      exact diamondWithTriangleFace0SelectedArcPureDartCycle hfmem
    · by_cases h1 : f = (1 : DiamondWithTriangleFace)
      · subst f
        exact diamondWithTriangleFace1SelectedArcPureDartCycle hfmem
      · have h2 : f = (2 : DiamondWithTriangleFace) := by
          rcases f with ⟨n, hn⟩
          have hn012 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
          rcases hn012 with rfl | rfl | rfl
          · exact False.elim (h0 rfl)
          · exact False.elim (h1 rfl)
          · rfl
        subst f
        exact diamondWithTriangleFace2PureDartCycle hfmem

def diamondWithTriangleClosedWalkEmbeddingData :
    PlanarBoundaryClosedWalkEmbeddingData diamondWithTriangleEmbedding :=
  diamondWithTrianglePureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

theorem diamondWithTriangleClosedWalkEmbeddingData_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
      (diamondWithTriangleClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f := by
  intro f
  let f0 : AmbientFace diamondWithTriangleEmbedding.faces :=
    ⟨(0 : DiamondWithTriangleFace), by
      change (0 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
      exact Finset.mem_univ _⟩
  let f1 : AmbientFace diamondWithTriangleEmbedding.faces :=
    ⟨(1 : DiamondWithTriangleFace), by
      change (1 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
      exact Finset.mem_univ _⟩
  let f2 : AmbientFace diamondWithTriangleEmbedding.faces :=
    ⟨(2 : DiamondWithTriangleFace), by
      change (2 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
      exact Finset.mem_univ _⟩
  have hf_cases : f = f0 ∨ f = f1 ∨ f = f2 := by
    rcases f with ⟨⟨n, hn⟩, hfmem⟩
    have hn012 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn012 with rfl | rfl | rfl
    · left
      exact Subtype.ext rfl
    · right
      left
      exact Subtype.ext rfl
    · right
      right
      exact Subtype.ext rfl
  rcases hf_cases with rfl | rfl | rfl
  · change
      (diamondWithTriangleClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f0
    refine ⟨[dt02, dt01], ?_, ?_⟩
    · decide
    · intro e
      rcases diamondWithTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · change
      (diamondWithTriangleClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f1
    refine ⟨[dt23, dt13], ?_, ?_⟩
    · decide
    · intro e
      rcases diamondWithTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · change
      (diamondWithTriangleClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f2
    refine ⟨[dt45, dt56, dt64], ?_, ?_⟩
    · decide
    · intro e
      rcases diamondWithTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide

/-- The honest facial closed-walk witness on the diamond-with-triangle embedding already upgrades
to the stronger cyclic ordered face-arc source shell. This blocks the natural workaround where the
source side is strengthened from explicit closed walks to cyclic per-face boundary order plus
selected-boundary contiguity. -/
noncomputable def diamondWithTriangleCyclicOrderedFaceArcEmbeddingData :
    PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding :=
  diamondWithTriangleClosedWalkEmbeddingData.toPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    diamondWithTriangleClosedWalkEmbeddingData_selectedBoundaryArcOnFace

theorem nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle :
    Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) :=
  ⟨diamondWithTriangleCyclicOrderedFaceArcEmbeddingData⟩

noncomputable def diamondWithTriangleSelectedBoundaryArcGeometry :
    PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding :=
  diamondWithTriangleCyclicOrderedFaceArcEmbeddingData.toPlanarBoundarySelectedBoundaryArcGeometry

theorem nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle :
    Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) :=
  ⟨diamondWithTriangleSelectedBoundaryArcGeometry⟩

def diamondWithTriangleOuterRoot : PlanarBoundaryEdgeVertex diamondWithTriangleEmbedding :=
  ⟨dt01, dt01_mem_selectedBoundarySupport⟩

def diamondWithTriangleInnerRoot : PlanarBoundaryEdgeVertex diamondWithTriangleEmbedding :=
  ⟨dt45, dt45_mem_selectedBoundarySupport⟩

def diamondWithTriangleBoundaryLabel
    (e : PlanarBoundaryEdgeVertex diamondWithTriangleEmbedding) : Bool :=
  if e.1 = dt45 ∨ e.1 = dt56 ∨ e.1 = dt64 then true else false

theorem diamondWithTriangle_boundaryEdge_eq
    (e : PlanarBoundaryEdgeVertex diamondWithTriangleEmbedding) :
    e = ⟨dt01, dt01_mem_selectedBoundarySupport⟩ ∨
      e = ⟨dt02, dt02_mem_selectedBoundarySupport⟩ ∨
      e = ⟨dt13, dt13_mem_selectedBoundarySupport⟩ ∨
      e = ⟨dt23, dt23_mem_selectedBoundarySupport⟩ ∨
      e = ⟨dt45, dt45_mem_selectedBoundarySupport⟩ ∨
      e = ⟨dt56, dt56_mem_selectedBoundarySupport⟩ ∨
      e = ⟨dt64, dt64_mem_selectedBoundarySupport⟩ := by
  rcases diamondWithTriangle_edge_eq e.1 with
    h01 | h12 | h02 | h13 | h23 | h45 | h56 | h64
  · exact Or.inl (Subtype.ext h01)
  · exact False.elim (dt12_not_mem_selectedBoundarySupport (by simpa [h12] using e.2))
  · exact Or.inr (Or.inl (Subtype.ext h02))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h13)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h23))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h45)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h56))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h64))))))

theorem diamondWithTriangleBoundaryAdj_preserves_label :
    ∀ ⦃e f : PlanarBoundaryEdgeVertex diamondWithTriangleEmbedding⦄,
      (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj e f →
        diamondWithTriangleBoundaryLabel e = diamondWithTriangleBoundaryLabel f := by
  intro e f hadj
  rcases diamondWithTriangle_boundaryEdge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases diamondWithTriangle_boundaryEdge_eq f with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact False.elim
          (by
            rcases hadj with ⟨_, v, hvE, hvF⟩
            fin_cases v <;>
              simp [dt01, dt02, dt13, dt23, dt45, dt56, dt64] at hvE hvF)

theorem diamondWithTriangleOuterRoot_ne_innerRoot :
    diamondWithTriangleOuterRoot ≠ diamondWithTriangleInnerRoot := by
  intro h
  have := congrArg Subtype.val h
  simp [diamondWithTriangleOuterRoot, diamondWithTriangleInnerRoot, dt01, dt45] at this

def diamondWithTriangleAnnulusBoundaryReachabilityData :
    PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding where
  outerRoot := diamondWithTriangleOuterRoot
  innerRoot := diamondWithTriangleInnerRoot
  hroots_ne := diamondWithTriangleOuterRoot_ne_innerRoot
  hcoverRoots := by
    intro e
    rcases diamondWithTriangle_boundaryEdge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨diamondWithTriangleOuterRoot, by simp [diamondWithTriangleOuterRoot_ne_innerRoot],
        SimpleGraph.Reachable.refl _⟩
    · refine ⟨diamondWithTriangleOuterRoot, by simp [diamondWithTriangleOuterRoot_ne_innerRoot],
        ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
            ⟨dt02, dt02_mem_selectedBoundarySupport⟩
            diamondWithTriangleOuterRoot := by
        refine ⟨?_, 0, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [diamondWithTriangleOuterRoot, dt02, dt01] at this
        · simp [dt02]
        · simp [diamondWithTriangleOuterRoot, dt01]
      exact hadj.reachable
    · refine ⟨diamondWithTriangleOuterRoot, by simp [diamondWithTriangleOuterRoot_ne_innerRoot],
        ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
            ⟨dt13, dt13_mem_selectedBoundarySupport⟩
            diamondWithTriangleOuterRoot := by
        refine ⟨?_, 1, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [diamondWithTriangleOuterRoot, dt13, dt01] at this
        · simp [dt13]
        · simp [diamondWithTriangleOuterRoot, dt01]
      exact hadj.reachable
    · refine ⟨diamondWithTriangleOuterRoot, by simp [diamondWithTriangleOuterRoot_ne_innerRoot],
        ?_⟩
      have h23_13 :
          (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Reachable
            ⟨dt23, dt23_mem_selectedBoundarySupport⟩
            ⟨dt13, dt13_mem_selectedBoundarySupport⟩ := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
              ⟨dt23, dt23_mem_selectedBoundarySupport⟩
              ⟨dt13, dt13_mem_selectedBoundarySupport⟩ := by
          refine ⟨?_, 3, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [dt23, dt13] at this
          · simp [dt23]
          · simp [dt13]
        exact hadj.reachable
      have h13_outer :
          (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Reachable
            ⟨dt13, dt13_mem_selectedBoundarySupport⟩
            diamondWithTriangleOuterRoot := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
              ⟨dt13, dt13_mem_selectedBoundarySupport⟩
              diamondWithTriangleOuterRoot := by
          refine ⟨?_, 1, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [diamondWithTriangleOuterRoot, dt13, dt01] at this
          · simp [dt13]
          · simp [diamondWithTriangleOuterRoot, dt01]
        exact hadj.reachable
      exact h23_13.trans h13_outer
    · refine ⟨diamondWithTriangleInnerRoot, by simp,
        SimpleGraph.Reachable.refl _⟩
    · refine ⟨diamondWithTriangleInnerRoot, by simp,
        ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
            ⟨dt56, dt56_mem_selectedBoundarySupport⟩
            diamondWithTriangleInnerRoot := by
        refine ⟨?_, 5, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [diamondWithTriangleInnerRoot, dt56, dt45] at this
        · simp [dt56]
        · simp [diamondWithTriangleInnerRoot, dt45]
      exact hadj.reachable
    · refine ⟨diamondWithTriangleInnerRoot, by simp,
        ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
            ⟨dt64, dt64_mem_selectedBoundarySupport⟩
            diamondWithTriangleInnerRoot := by
        refine ⟨?_, 4, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [diamondWithTriangleInnerRoot, dt64, dt45] at this
        · simp [dt64]
        · simp [diamondWithTriangleInnerRoot, dt45]
      exact hadj.reachable
  hsepRoots := by
    intro r s hr hs hreach
    have hlabelEq :
        diamondWithTriangleBoundaryLabel r = diamondWithTriangleBoundaryLabel s :=
      eq_of_reachable_of_eq_on_adj
        (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding)
        diamondWithTriangleBoundaryLabel
        (by
          intro u v huv
          exact diamondWithTriangleBoundaryAdj_preserves_label huv)
        hreach
    have hOuterLabel :
        diamondWithTriangleBoundaryLabel diamondWithTriangleOuterRoot = false := by
      decide
    have hInnerLabel :
        diamondWithTriangleBoundaryLabel diamondWithTriangleInnerRoot = true := by
      decide
    have hr_cases : r = diamondWithTriangleOuterRoot ∨
        r = diamondWithTriangleInnerRoot := by
      simpa [diamondWithTriangleOuterRoot_ne_innerRoot] using hr
    have hs_cases : s = diamondWithTriangleOuterRoot ∨
        s = diamondWithTriangleInnerRoot := by
      simpa [diamondWithTriangleOuterRoot_ne_innerRoot] using hs
    rcases hr_cases with rfl | rfl <;> rcases hs_cases with rfl | rfl
    · rfl
    · rw [hOuterLabel, hInnerLabel] at hlabelEq
      cases hlabelEq
    · rw [hInnerLabel, hOuterLabel] at hlabelEq
      cases hlabelEq
    · rfl

def diamondWithTriangleClosedWalkAnnulusBoundarySource :
    PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields
    diamondWithTriangleAnnulusBoundaryReachabilityData
    diamondWithTriangleClosedWalkEmbeddingData
    diamondWithTriangleClosedWalkEmbeddingData_selectedBoundaryArcOnFace

theorem nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) :=
  ⟨diamondWithTriangleClosedWalkAnnulusBoundarySource⟩

/-- Each face of the diamond-with-triangle source has at most one interior edge.  Thus this
countermodel also satisfies the canonical source-witness choice hypothesis mined by the
validation lab. -/
theorem diamondWithTriangle_facewiseAtMostOneInteriorEdge :
    ∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
      ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
        (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces)).card ≤ 1 := by
  intro f
  fin_cases f <;> decide

theorem nonempty_planarBoundaryCanonicalWitnessChoice_diamondWithTriangle :
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) :=
  (nonempty_planarBoundaryCanonicalWitnessChoice_iff_facewiseAtMostOneInteriorEdge_of_closedWalkAnnulusBoundarySource
    diamondWithTriangleClosedWalkAnnulusBoundarySource).2
    diamondWithTriangle_facewiseAtMostOneInteriorEdge

/-- The full closed-walk annulus boundary-source package still does not imply the raw
endpoint-support separation.  This model has two separated boundary components and honest facial
closed walks with selected-boundary arcs, but the diamond component contains an interior edge
touching a selected-boundary edge at a primal endpoint. -/
theorem closedWalkAnnulusBoundarySource_does_not_imply_endpointSupport_disjoint_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport diamondWithTriangleEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces)) :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
    not_endpointSupport_disjoint_diamondWithTriangle⟩

def diamondWithTriangleOuterBoundaryCycleSet :
    Finset diamondWithTriangleGraph.edgeSet :=
  {dt02, dt23, dt13, dt01}

def diamondWithTriangleInnerBoundaryCycleSet :
    Finset diamondWithTriangleGraph.edgeSet :=
  {dt45, dt56, dt64}

theorem diamondWithTriangleBoundaryAdj_dt02_dt23 :
    (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
      ⟨dt02, dt02_mem_selectedBoundarySupport⟩
      ⟨dt23, dt23_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 2, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [dt02, dt23] at this
  · simp [dt02]
  · simp [dt23]

theorem diamondWithTriangleBoundaryAdj_dt23_dt13 :
    (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
      ⟨dt23, dt23_mem_selectedBoundarySupport⟩
      ⟨dt13, dt13_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 3, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [dt23, dt13] at this
  · simp [dt23]
  · simp [dt13]

theorem diamondWithTriangleBoundaryAdj_dt13_dt01 :
    (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
      ⟨dt13, dt13_mem_selectedBoundarySupport⟩
      ⟨dt01, dt01_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 1, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [dt13, dt01] at this
  · simp [dt13]
  · simp [dt01]

theorem diamondWithTriangleBoundaryAdj_dt01_dt02 :
    (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
      ⟨dt01, dt01_mem_selectedBoundarySupport⟩
      ⟨dt02, dt02_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 0, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [dt01, dt02] at this
  · simp [dt01]
  · simp [dt02]

theorem diamondWithTriangleBoundaryAdj_dt45_dt56 :
    (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
      ⟨dt45, dt45_mem_selectedBoundarySupport⟩
      ⟨dt56, dt56_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 5, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [dt45, dt56] at this
  · simp [dt45]
  · simp [dt56]

theorem diamondWithTriangleBoundaryAdj_dt56_dt64 :
    (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
      ⟨dt56, dt56_mem_selectedBoundarySupport⟩
      ⟨dt64, dt64_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 6, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [dt56, dt64] at this
  · simp [dt56]
  · simp [dt64]

theorem diamondWithTriangleBoundaryAdj_dt64_dt45 :
    (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
      ⟨dt64, dt64_mem_selectedBoundarySupport⟩
      ⟨dt45, dt45_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 4, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [dt64, dt45] at this
  · simp [dt64]
  · simp [dt45]

theorem boundaryEdgeSetCyclicRun_outer_diamondWithTriangle :
    BoundaryEdgeSetCyclicRun diamondWithTriangleEmbedding
      diamondWithTriangleOuterBoundaryCycleSet := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp [diamondWithTriangleOuterBoundaryCycleSet] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact dt02_mem_selectedBoundarySupport
    · exact dt23_mem_selectedBoundarySupport
    · exact dt13_mem_selectedBoundarySupport
    · exact dt01_mem_selectedBoundarySupport
  · refine ⟨[
      ⟨dt02, dt02_mem_selectedBoundarySupport⟩,
      ⟨dt23, dt23_mem_selectedBoundarySupport⟩,
      ⟨dt13, dt13_mem_selectedBoundarySupport⟩,
      ⟨dt01, dt01_mem_selectedBoundarySupport⟩], ?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · change List.IsChain (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
        [⟨dt02, dt02_mem_selectedBoundarySupport⟩,
          ⟨dt23, dt23_mem_selectedBoundarySupport⟩,
          ⟨dt13, dt13_mem_selectedBoundarySupport⟩,
          ⟨dt01, dt01_mem_selectedBoundarySupport⟩,
          ⟨dt02, dt02_mem_selectedBoundarySupport⟩]
      exact (List.isChain_cons_cons).2
        ⟨diamondWithTriangleBoundaryAdj_dt02_dt23,
          (List.isChain_cons_cons).2
            ⟨diamondWithTriangleBoundaryAdj_dt23_dt13,
              (List.isChain_cons_cons).2
                ⟨diamondWithTriangleBoundaryAdj_dt13_dt01,
                  (List.isChain_pair).2 diamondWithTriangleBoundaryAdj_dt01_dt02⟩⟩⟩
    · intro x
      rcases diamondWithTriangle_boundaryEdge_eq x with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide

theorem boundaryEdgeSetCyclicRun_inner_diamondWithTriangle :
    BoundaryEdgeSetCyclicRun diamondWithTriangleEmbedding
      diamondWithTriangleInnerBoundaryCycleSet := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp [diamondWithTriangleInnerBoundaryCycleSet] at he
    rcases he with rfl | rfl | rfl
    · exact dt45_mem_selectedBoundarySupport
    · exact dt56_mem_selectedBoundarySupport
    · exact dt64_mem_selectedBoundarySupport
  · refine ⟨[
      ⟨dt45, dt45_mem_selectedBoundarySupport⟩,
      ⟨dt56, dt56_mem_selectedBoundarySupport⟩,
      ⟨dt64, dt64_mem_selectedBoundarySupport⟩], ?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · change List.IsChain (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
        [⟨dt45, dt45_mem_selectedBoundarySupport⟩,
          ⟨dt56, dt56_mem_selectedBoundarySupport⟩,
          ⟨dt64, dt64_mem_selectedBoundarySupport⟩,
          ⟨dt45, dt45_mem_selectedBoundarySupport⟩]
      exact (List.isChain_cons_cons).2
        ⟨diamondWithTriangleBoundaryAdj_dt45_dt56,
          (List.isChain_cons_cons).2
            ⟨diamondWithTriangleBoundaryAdj_dt56_dt64,
              (List.isChain_pair).2 diamondWithTriangleBoundaryAdj_dt64_dt45⟩⟩
    · intro x
      rcases diamondWithTriangle_boundaryEdge_eq x with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide

theorem outer_inner_boundaryCycleEndpointSupports_disjoint_diamondWithTriangle :
    Disjoint
      (boundaryEdgeSetEndpointSupport diamondWithTriangleOuterBoundaryCycleSet)
      (boundaryEdgeSetEndpointSupport diamondWithTriangleInnerBoundaryCycleSet) := by
  rw [Finset.disjoint_left]
  intro v hvOuter hvInner
  fin_cases v <;>
    simp [boundaryEdgeSetEndpointSupport, diamondWithTriangleOuterBoundaryCycleSet,
      diamondWithTriangleInnerBoundaryCycleSet, dt02, dt23, dt13, dt01,
      dt45, dt56, dt64] at hvOuter hvInner

theorem annulusBoundaryCyclePair_diamondWithTriangle :
    AnnulusBoundaryCyclePair diamondWithTriangleEmbedding
      diamondWithTriangleOuterBoundaryCycleSet diamondWithTriangleInnerBoundaryCycleSet :=
  ⟨boundaryEdgeSetCyclicRun_outer_diamondWithTriangle,
    boundaryEdgeSetCyclicRun_inner_diamondWithTriangle,
    outer_inner_boundaryCycleEndpointSupports_disjoint_diamondWithTriangle⟩

theorem eq_dt12_of_mem_interiorEdgeSupport_diamondWithTriangle
    {e : diamondWithTriangleGraph.edgeSet}
    (he : e ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
      diamondWithTriangleEmbedding.faces) :
    e = dt12 := by
  rcases diamondWithTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hcount :=
      (mem_interiorEdgeSupport_iff diamondWithTriangleEmbedding.faceBoundary
        diamondWithTriangleEmbedding.faces).1 he |>.2
    simp [diamondWithTriangleEmbedding, totalIncidenceCount_dt01] at hcount
  · rfl
  · have hcount :=
      (mem_interiorEdgeSupport_iff diamondWithTriangleEmbedding.faceBoundary
        diamondWithTriangleEmbedding.faces).1 he |>.2
    simp [diamondWithTriangleEmbedding, totalIncidenceCount_dt02] at hcount
  · have hcount :=
      (mem_interiorEdgeSupport_iff diamondWithTriangleEmbedding.faceBoundary
        diamondWithTriangleEmbedding.faces).1 he |>.2
    simp [diamondWithTriangleEmbedding, totalIncidenceCount_dt13] at hcount
  · have hcount :=
      (mem_interiorEdgeSupport_iff diamondWithTriangleEmbedding.faceBoundary
        diamondWithTriangleEmbedding.faces).1 he |>.2
    simp [diamondWithTriangleEmbedding, totalIncidenceCount_dt23] at hcount
  · have hcount :=
      (mem_interiorEdgeSupport_iff diamondWithTriangleEmbedding.faceBoundary
        diamondWithTriangleEmbedding.faces).1 he |>.2
    simp [diamondWithTriangleEmbedding, totalIncidenceCount_dt45] at hcount
  · have hcount :=
      (mem_interiorEdgeSupport_iff diamondWithTriangleEmbedding.faceBoundary
        diamondWithTriangleEmbedding.faces).1 he |>.2
    simp [diamondWithTriangleEmbedding, totalIncidenceCount_dt56] at hcount
  · have hcount :=
      (mem_interiorEdgeSupport_iff diamondWithTriangleEmbedding.faceBoundary
        diamondWithTriangleEmbedding.faces).1 he |>.2
    simp [diamondWithTriangleEmbedding, totalIncidenceCount_dt64] at hcount

theorem selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle :
    selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ := by
  ext v
  constructor
  · intro hv
    rcases (mem_selectedBoundaryInteriorEdgeEndpointVertices_iff
        diamondWithTriangleEmbedding).1 hv with
      ⟨hInterior, hAvoid⟩
    rcases hInterior with ⟨e, heInterior, hvEdge⟩
    have he : e = dt12 :=
      eq_dt12_of_mem_interiorEdgeSupport_diamondWithTriangle heInterior
    subst he
    have hv_cases : v = (1 : Fin 7) ∨ v = (2 : Fin 7) := by
      fin_cases v
      · simp [dt12] at hvEdge
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp [dt12] at hvEdge
      · simp [dt12] at hvEdge
      · simp [dt12] at hvEdge
      · simp [dt12] at hvEdge
    rcases hv_cases with rfl | rfl
    · exact False.elim
        (hAvoid dt01 dt01_mem_selectedBoundarySupport vertex_one_mem_dt01)
    · have htwo : (2 : Fin 7) ∈ (dt02 : Sym2 (Fin 7)) := by
        simp [dt02]
      exact False.elim (hAvoid dt02 dt02_mem_selectedBoundarySupport htwo)
  · intro hv
    simp at hv

theorem not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle :
    ¬ (selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding).Nonempty := by
  rintro ⟨v, hv⟩
  simp [selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle] at hv

theorem not_interiorEdgesNotSelectedBoundaryChords_diamondWithTriangle :
    ¬ InteriorEdgesNotSelectedBoundaryChords diamondWithTriangleEmbedding := by
  intro hChordFree
  rcases hChordFree dt12 dt12_mem_interiorEdgeSupport with ⟨v, hvEdge, hAvoid⟩
  have hv_cases : v = (1 : Fin 7) ∨ v = (2 : Fin 7) := by
    fin_cases v
    · simp [dt12] at hvEdge
    · exact Or.inl rfl
    · exact Or.inr rfl
    · simp [dt12] at hvEdge
    · simp [dt12] at hvEdge
    · simp [dt12] at hvEdge
    · simp [dt12] at hvEdge
  rcases hv_cases with rfl | rfl
  · exact hAvoid dt01 dt01_mem_selectedBoundarySupport vertex_one_mem_dt01
  · have htwo : (2 : Fin 7) ∈ (dt02 : Sym2 (Fin 7)) := by
      simp [dt02]
    exact hAvoid dt02 dt02_mem_selectedBoundarySupport htwo

/-- The diamond-with-triangle model has honest closed-walk annulus source data and both
distinguished boundary components are finite endpoint cycles with disjoint vertex supports.
Nevertheless the purified selected-boundary carrier is empty.  Thus the boundary-cycle
strengthening of the source packet still does not imply the nonempty carrier needed by the
non-vacuous synthesis endpoint. -/
theorem
    closedWalkAnnulusBoundarySource_and_boundaryCyclePair_does_not_imply_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      AnnulusBoundaryCyclePair diamondWithTriangleEmbedding
        diamondWithTriangleOuterBoundaryCycleSet diamondWithTriangleInnerBoundaryCycleSet ∧
        ¬ (selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding).Nonempty :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
    annulusBoundaryCyclePair_diamondWithTriangle,
    not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle⟩

/-- Strengthening the same source packet by a canonical witness choice still does not force a
nonempty selected-boundary-purified carrier.  This is the Lean regression for the validation-lab
rejection of the closed-walk boundary-cycle plus witness-assignment route. -/
theorem
    closedWalkAnnulusBoundarySource_boundaryCyclePair_and_canonicalWitnessChoice_does_not_imply_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      AnnulusBoundaryCyclePair diamondWithTriangleEmbedding
        diamondWithTriangleOuterBoundaryCycleSet diamondWithTriangleInnerBoundaryCycleSet ∧
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
          ¬ (selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding).Nonempty :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
    annulusBoundaryCyclePair_diamondWithTriangle,
    nonempty_planarBoundaryCanonicalWitnessChoice_diamondWithTriangle,
    not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle⟩

/-- The same boundary-cycle source packet still permits an interior edge whose two endpoints lie
on the selected boundary.  Hence this concrete source strengthening does not derive the no-chord
premise used by the surviving nonempty-carrier route. -/
theorem
    closedWalkAnnulusBoundarySource_and_boundaryCyclePair_does_not_imply_interiorEdgesNotSelectedBoundaryChords_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      AnnulusBoundaryCyclePair diamondWithTriangleEmbedding
        diamondWithTriangleOuterBoundaryCycleSet diamondWithTriangleInnerBoundaryCycleSet ∧
        ¬ InteriorEdgesNotSelectedBoundaryChords diamondWithTriangleEmbedding :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
    annulusBoundaryCyclePair_diamondWithTriangle,
    not_interiorEdgesNotSelectedBoundaryChords_diamondWithTriangle⟩

/-- The closed-walk boundary-cycle plus canonical witness-choice packet also still permits an
interior selected-boundary chord. -/
theorem
    closedWalkAnnulusBoundarySource_boundaryCyclePair_and_canonicalWitnessChoice_does_not_imply_interiorEdgesNotSelectedBoundaryChords_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      AnnulusBoundaryCyclePair diamondWithTriangleEmbedding
        diamondWithTriangleOuterBoundaryCycleSet diamondWithTriangleInnerBoundaryCycleSet ∧
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
          ¬ InteriorEdgesNotSelectedBoundaryChords diamondWithTriangleEmbedding :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
    annulusBoundaryCyclePair_diamondWithTriangle,
    nonempty_planarBoundaryCanonicalWitnessChoice_diamondWithTriangle,
    not_interiorEdgesNotSelectedBoundaryChords_diamondWithTriangle⟩

/-- The same boundary-cycle source packet also cannot derive selected-boundary inducedness.
Selected-boundary inducedness would imply the no-chord premise, already refuted on this model. -/
theorem not_selectedBoundaryInducedSubgraph_diamondWithTriangle :
    ¬ SelectedBoundaryInducedSubgraph diamondWithTriangleEmbedding := by
  intro hInduced
  exact not_interiorEdgesNotSelectedBoundaryChords_diamondWithTriangle
    (interiorEdgesNotSelectedBoundaryChords_of_selectedBoundaryInducedSubgraph hInduced)

theorem
    closedWalkAnnulusBoundarySource_and_boundaryCyclePair_does_not_imply_selectedBoundaryInducedSubgraph_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      AnnulusBoundaryCyclePair diamondWithTriangleEmbedding
        diamondWithTriangleOuterBoundaryCycleSet diamondWithTriangleInnerBoundaryCycleSet ∧
        ¬ SelectedBoundaryInducedSubgraph diamondWithTriangleEmbedding :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
    annulusBoundaryCyclePair_diamondWithTriangle,
    not_selectedBoundaryInducedSubgraph_diamondWithTriangle⟩

/-- The same canonical witness-choice strengthening also cannot derive selected-boundary
inducedness. -/
theorem
    closedWalkAnnulusBoundarySource_boundaryCyclePair_and_canonicalWitnessChoice_does_not_imply_selectedBoundaryInducedSubgraph_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      AnnulusBoundaryCyclePair diamondWithTriangleEmbedding
        diamondWithTriangleOuterBoundaryCycleSet diamondWithTriangleInnerBoundaryCycleSet ∧
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
          ¬ SelectedBoundaryInducedSubgraph diamondWithTriangleEmbedding :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
    annulusBoundaryCyclePair_diamondWithTriangle,
    nonempty_planarBoundaryCanonicalWitnessChoice_diamondWithTriangle,
    not_selectedBoundaryInducedSubgraph_diamondWithTriangle⟩

/-- Fixed-graph universal obstruction: even if an embedding of this graph carries closed-walk
annulus source data and some cyclic outer/inner boundary edge pair, that source package still
does not force a nonempty selected-boundary-purified carrier. -/
theorem
    not_forall_closedWalkAnnulusBoundarySource_and_exists_boundaryCyclePair_implies_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_diamondWithTriangleGraph :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
        (∃ outer inner : Finset diamondWithTriangleGraph.edgeSet,
          AnnulusBoundaryCyclePair emb outer inner) →
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle
    (h nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      ⟨diamondWithTriangleOuterBoundaryCycleSet,
        diamondWithTriangleInnerBoundaryCycleSet,
        annulusBoundaryCyclePair_diamondWithTriangle⟩)

/-- Fixed-graph universal obstruction for the surviving no-chord repair premise: closed-walk
annulus source data plus some cyclic outer/inner boundary edge pair still does not force
`InteriorEdgesNotSelectedBoundaryChords`. -/
theorem
    not_forall_closedWalkAnnulusBoundarySource_and_exists_boundaryCyclePair_implies_interiorEdgesNotSelectedBoundaryChords_diamondWithTriangleGraph :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
        (∃ outer inner : Finset diamondWithTriangleGraph.edgeSet,
          AnnulusBoundaryCyclePair emb outer inner) →
          InteriorEdgesNotSelectedBoundaryChords emb := by
  intro h
  exact not_interiorEdgesNotSelectedBoundaryChords_diamondWithTriangle
    (h nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      ⟨diamondWithTriangleOuterBoundaryCycleSet,
        diamondWithTriangleInnerBoundaryCycleSet,
        annulusBoundaryCyclePair_diamondWithTriangle⟩)

/-- Fixed-graph universal obstruction for the selected-boundary inducedness repair premise:
closed-walk annulus source data plus some cyclic outer/inner boundary edge pair still does not
force the combined selected-boundary endpoint support to be induced. -/
theorem
    not_forall_closedWalkAnnulusBoundarySource_and_exists_boundaryCyclePair_implies_selectedBoundaryInducedSubgraph_diamondWithTriangleGraph :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
        (∃ outer inner : Finset diamondWithTriangleGraph.edgeSet,
          AnnulusBoundaryCyclePair emb outer inner) →
          SelectedBoundaryInducedSubgraph emb := by
  intro h
  exact not_selectedBoundaryInducedSubgraph_diamondWithTriangle
    (h nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle
      ⟨diamondWithTriangleOuterBoundaryCycleSet,
        diamondWithTriangleInnerBoundaryCycleSet,
        annulusBoundaryCyclePair_diamondWithTriangle⟩)

/-- The preceding boundary-source countermodel is deliberately not a countermodel to the peeled
interior-dual annulus route.  In this embedding, covering the unique interior edge `dt12` would
force a peeled witness face to be one of the two diamond triangles, but both such faces contain
selected-boundary edges.  This contradicts the edge-disjoint `hpeelInterior` field of
`InteriorDualBoundaryRootAdjDistancePeelData`. -/
theorem false_of_interiorDualBoundaryRootAdjDistancePeelData_of_forcing_interiorEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    {e : G.edgeSet}
    (heInterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hforcing : ∀ {f : AmbientFace emb.faces},
      e ∈ emb.faceBoundary f.1 →
        ∃ b ∈ emb.faceBoundary f.1,
          b ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    False := by
  have hdisj : Disjoint data.peelFaces data.roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      emb.faceBoundary emb.faces data.peelFaces data.roots
      data.hpeelInterior data.hrootsBoundary
  have hcovered :
      e ∈ data.peelFaces.image
        (rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces
          data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary
            emb.faces data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge) :=
    data.hcover heInterior
  rcases Finset.mem_image.1 hcovered with ⟨f, hfPeel, hWitness⟩
  have hneq :
      f ≠ interiorDualSpanningForestRoot emb.faceBoundary
        emb.faces data.roots data.hcoverRoots data.hsepRoots f :=
    ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
      emb.faceBoundary emb.faces
      data.peelFaces data.roots data.hcoverRoots data.hsepRoots hdisj hfPeel
  rcases parentTowardsRoot_spec_of_ne
      (T := interiorDualSpanningForest emb.faceBoundary emb.faces)
      (root := interiorDualSpanningForestRoot emb.faceBoundary
        emb.faces data.roots data.hcoverRoots data.hsepRoots)
      (u := f)
      (h := reachable_interiorDualSpanningForestRoot
        emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots f)
      hneq with ⟨p, hfp, _hadj, _hdist⟩
  have hfWitness :
      rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces
          data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary
            emb.faces data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge f ∈ emb.faceBoundary f.1 :=
    rootedSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
      emb.faceBoundary emb.faces
      data.hunique
      (interiorDualSpanningForestRoot emb.faceBoundary
        emb.faces data.roots data.hcoverRoots data.hsepRoots)
      data.fallbackEdge hfp
  have heFace : e ∈ emb.faceBoundary f.1 := by
    simpa [hWitness] using hfWitness
  rcases hforcing heFace with ⟨b, hbf, hbBoundary⟩
  exact (Finset.disjoint_left.mp (data.hpeelInterior f hfPeel)) hbf hbBoundary

theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  rintro ⟨data⟩
  exact
    false_of_interiorDualBoundaryRootAdjDistancePeelData_of_forcing_interiorEdge
      data dt12_mem_interiorEdgeSupport
      (fun hf12 =>
        exists_selectedBoundarySupport_of_dt12_mem_faceBoundary_diamondWithTriangle hf12)

/-- The honest closed-walk annulus boundary source on the diamond-with-triangle embedding still
does not reach the peeled interior-dual route. The source-side boundary geometry exists, but the
interior-dual boundary-root adjacency-distance package is empty on this embedding. -/
theorem
    closedWalkAnnulusBoundarySource_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- The diamond-with-triangle embedding is a finite countermodel to deriving the current
boundary-root interior-dual distance package from raw closed-walk annulus-boundary source data
alone. -/
theorem not_forall_closedWalkSource_implies_interiorDualRootDistance_diamondWithTriangle :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
          emb.faces emb.faceBoundary) := by
  intro h
  exact not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle
    (h nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle)

/-- Strengthening the same source embedding to the cyclic ordered face-arc shell still does not
start the current peeled interior-dual route. The diamond-with-triangle embedding carries both the
annulus boundary reachability package and the stronger cyclic per-face boundary order with
selected-boundary arcs, but the peeled interior-dual adjacency-distance package remains empty. -/
theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- Weakening the source to the bundled selected-boundary arc geometry still does not start the
peeled interior-dual route on the diamond-with-triangle embedding. So even after discarding the
cyclic face-order data and retaining only one contiguous selected-boundary arc on each chosen face
boundary run, the rooted interior-dual adjacency-distance package remains empty. -/
theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- The same diamond-with-triangle model blocks the weaker construction-side annulus route as
soon as peeled faces are required to be edge-disjoint from the selected boundary support. The
only interior edge `dt12` lies on the two diamond faces, but each such face also contains a
selected-boundary edge, so no peeled face can witness `dt12`. -/
theorem
    false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_of_forcing_interiorEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    {e : G.edgeSet}
    (heInterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hforcing : ∀ {f : AmbientFace emb.faces},
      e ∈ emb.faceBoundary f.1 →
        ∃ b ∈ emb.faceBoundary f.1,
          b ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    False := by
  have hcovered : e ∈ data.peelFaces.image data.witnessEdge := data.hcover heInterior
  rcases Finset.mem_image.1 hcovered with ⟨f, hfPeel, hWitness⟩
  have hfWitness : data.witnessEdge f ∈ emb.faceBoundary f.1 := data.hwitness f hfPeel
  have heFace : e ∈ emb.faceBoundary f.1 := by
    simpa [hWitness] using hfWitness
  rcases hforcing heFace with ⟨b, hbf, hbBoundary⟩
  exact (Finset.disjoint_left.mp (hpeelInterior f hfPeel)) hbf hbBoundary

/-- The same diamond-with-triangle model blocks the weaker construction-side annulus route as
soon as peeled faces are required to be edge-disjoint from the selected boundary support. The
only interior edge `dt12` lies on the two diamond faces, but each such face also contains a
selected-boundary edge, so no peeled face can witness `dt12`. -/
theorem false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_diamondWithTriangle
    (data : PlanarBoundaryAnnulusConstruction diamondWithTriangleEmbedding)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (diamondWithTriangleEmbedding.faceBoundary f.1)
        (selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces)) :
    False := by
  exact
    false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_of_forcing_interiorEdge
      data hpeelInterior dt12_mem_interiorEdgeSupport
      (fun hf12 =>
        exists_selectedBoundarySupport_of_dt12_mem_faceBoundary_diamondWithTriangle hf12)

theorem not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData diamondWithTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_diamondWithTriangle
      data.construction data.hpeelInterior

theorem not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_diamondWithTriangle :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFacePartitionData diamondWithTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_diamondWithTriangle
      data.construction data.hpeelInterior

theorem not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangle :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionPositiveFrontierData diamondWithTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_diamondWithTriangle
      data.construction data.hpeelInterior

theorem not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangle :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFaceLayerData diamondWithTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_diamondWithTriangle
      data.construction data.hpeelInterior

/-- Honest same-embedding boundary reachability plus facial closed walks still do not force even
the weakest current construction-side geometric shell. The diamond-with-triangle model has the
full closed-walk annulus-boundary source, but no peeled-interior boundary-support face data can
exist on that embedding. -/
theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          diamondWithTriangleEmbedding) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle⟩

/-- The same stronger cyclic ordered face-arc source shell also still falls short of even the
weakest current peeled-interior construction target. So strengthening the source from explicit
closed walks to cyclic ordered face arcs does not bypass the forcing-edge obstruction. -/
theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          diamondWithTriangleEmbedding) := by
  exact
    ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle⟩

/-- The same weakening to bundled selected-boundary arc geometry still does not reach even the
weakest peeled-interior construction shell on the diamond-with-triangle embedding. So keeping
only the per-face selected-boundary arc witness does not bypass the forcing-edge obstruction. -/
theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          diamondWithTriangleEmbedding) := by
  exact
    ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle⟩


end Theorem49InteriorVerticesEndpointObstruction

end Mettapedia.GraphTheory.FourColor
