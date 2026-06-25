import Mettapedia.GraphTheory.FourColor.Theorem49TargetSubspace

/-!
Finite F2 boundary-zero regressions mined from the ignored CAP5 validation lab.

The lab checks two small annular shells against forced interior-edge supports.
This module records the buildable Lean endpoint: if the forced set covers the
whole interior support, selected-boundary-zero chains have no remaining
coordinate where an obstruction can hide.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49BoundaryZeroForcedEdgeRegression

/-! ## Shared-interior-pair shell -/

def sharedInteriorPairGraph : SimpleGraph (Fin 8) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 3), s(3, 0), s(2, 4), s(4, 0),
        s(5, 6), s(6, 7), s(7, 5)} : Set (Sym2 (Fin 8)))

theorem mem_sharedInteriorPairGraph_edgeSet_of_eq
    {e : Sym2 (Fin 8)}
    (h : e = s(0, 1) ∨ e = s(1, 2) ∨ e = s(2, 3) ∨ e = s(3, 0) ∨
      e = s(2, 4) ∨ e = s(4, 0) ∨ e = s(5, 6) ∨ e = s(6, 7) ∨
      e = s(7, 5)) : e ∈ sharedInteriorPairGraph.edgeSet := by
  rw [sharedInteriorPairGraph, SimpleGraph.edgeSet_fromEdgeSet]
  refine ⟨?_, ?_⟩
  · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  · rcases h with h | h | h | h | h | h | h | h | h
    all_goals subst e; decide

def sip01 : sharedInteriorPairGraph.edgeSet :=
  ⟨s(0, 1), mem_sharedInteriorPairGraph_edgeSet_of_eq (by decide)⟩

def sip12 : sharedInteriorPairGraph.edgeSet :=
  ⟨s(1, 2), mem_sharedInteriorPairGraph_edgeSet_of_eq (by decide)⟩

def sip23 : sharedInteriorPairGraph.edgeSet :=
  ⟨s(2, 3), mem_sharedInteriorPairGraph_edgeSet_of_eq (by decide)⟩

def sip30 : sharedInteriorPairGraph.edgeSet :=
  ⟨s(3, 0), mem_sharedInteriorPairGraph_edgeSet_of_eq (by decide)⟩

def sip24 : sharedInteriorPairGraph.edgeSet :=
  ⟨s(2, 4), mem_sharedInteriorPairGraph_edgeSet_of_eq (by decide)⟩

def sip40 : sharedInteriorPairGraph.edgeSet :=
  ⟨s(4, 0), mem_sharedInteriorPairGraph_edgeSet_of_eq (by decide)⟩

def sip56 : sharedInteriorPairGraph.edgeSet :=
  ⟨s(5, 6), mem_sharedInteriorPairGraph_edgeSet_of_eq (by decide)⟩

def sip67 : sharedInteriorPairGraph.edgeSet :=
  ⟨s(6, 7), mem_sharedInteriorPairGraph_edgeSet_of_eq (by decide)⟩

def sip75 : sharedInteriorPairGraph.edgeSet :=
  ⟨s(7, 5), mem_sharedInteriorPairGraph_edgeSet_of_eq (by decide)⟩

theorem sharedInteriorPair_edge_eq
    (e : sharedInteriorPairGraph.edgeSet) :
    e = sip01 ∨ e = sip12 ∨ e = sip23 ∨ e = sip30 ∨ e = sip24 ∨
      e = sip40 ∨ e = sip56 ∨ e = sip67 ∨ e = sip75 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 3) ∨ e.1 = s(3, 0) ∨
          e.1 = s(2, 4) ∨ e.1 = s(4, 0) ∨ e.1 = s(5, 6) ∨ e.1 = s(6, 7) ∨
          e.1 = s(7, 5)) ∧
        ¬ e.1.IsDiag := by
    simpa [sharedInteriorPairGraph] using e.2
  rcases h.1 with h01 | h12 | h23 | h30 | h24 | h40 | h56 | h67 | h75
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr <| Or.inl (Subtype.ext h12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h23)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h30)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h24)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h40)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h56)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext h67)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr (Subtype.ext h75)

abbrev SharedInteriorPairFace := Fin 3

def sharedInteriorPairFaces : Finset SharedInteriorPairFace := Finset.univ

def sharedInteriorPairFaceBoundary :
    SharedInteriorPairFace → Finset sharedInteriorPairGraph.edgeSet
  | ⟨0, _⟩ => {sip01, sip12, sip23, sip30}
  | ⟨1, _⟩ => {sip01, sip12, sip24, sip40}
  | ⟨2, _⟩ => {sip56, sip67, sip75}

theorem totalIncidenceCount_sip01 :
    totalIncidenceCount sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip01 = 2 := by
  decide

theorem totalIncidenceCount_sip12 :
    totalIncidenceCount sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip12 = 2 := by
  decide

theorem totalIncidenceCount_sip23 :
    totalIncidenceCount sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip23 = 1 := by
  decide

theorem totalIncidenceCount_sip30 :
    totalIncidenceCount sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip30 = 1 := by
  decide

theorem totalIncidenceCount_sip24 :
    totalIncidenceCount sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip24 = 1 := by
  decide

theorem totalIncidenceCount_sip40 :
    totalIncidenceCount sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip40 = 1 := by
  decide

theorem totalIncidenceCount_sip56 :
    totalIncidenceCount sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip56 = 1 := by
  decide

theorem totalIncidenceCount_sip67 :
    totalIncidenceCount sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip67 = 1 := by
  decide

theorem totalIncidenceCount_sip75 :
    totalIncidenceCount sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip75 = 1 := by
  decide

def sharedInteriorPairEmbedding : PlaneEmbeddingWithBoundary sharedInteriorPairGraph where
  Face := SharedInteriorPairFace
  faceDecidableEq := inferInstance
  faces := sharedInteriorPairFaces
  faceBoundary := sharedInteriorPairFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases sharedInteriorPair_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases sharedInteriorPair_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

theorem sip23_mem_selectedBoundarySupport :
    sip23 ∈ selectedBoundarySupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces
      sharedInteriorPairEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip23⟩

theorem sip30_mem_selectedBoundarySupport :
    sip30 ∈ selectedBoundarySupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces
      sharedInteriorPairEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip30⟩

theorem sip24_mem_selectedBoundarySupport :
    sip24 ∈ selectedBoundarySupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces
      sharedInteriorPairEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip24⟩

theorem sip40_mem_selectedBoundarySupport :
    sip40 ∈ selectedBoundarySupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces
      sharedInteriorPairEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip40⟩

theorem sip56_mem_selectedBoundarySupport :
    sip56 ∈ selectedBoundarySupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces
      sharedInteriorPairEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip56⟩

theorem sip67_mem_selectedBoundarySupport :
    sip67 ∈ selectedBoundarySupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces
      sharedInteriorPairEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip67⟩

theorem sip75_mem_selectedBoundarySupport :
    sip75 ∈ selectedBoundarySupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces
      sharedInteriorPairEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip75⟩

/-! ## Wheel-with-inner-triangle shell -/

def wheelWithInnerTriangleGraph : SimpleGraph (Fin 7) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(2, 3), s(3, 1),
        s(4, 5), s(5, 6), s(6, 4)} : Set (Sym2 (Fin 7)))

def wit01 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(0, 1), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit02 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(0, 2), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit03 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(0, 3), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit12 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(1, 2), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit23 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(2, 3), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit31 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(3, 1), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit45 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(4, 5), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit56 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(5, 6), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit64 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(6, 4), by
  simp [wheelWithInnerTriangleGraph]⟩

theorem wheelWithInnerTriangle_edge_eq
    (e : wheelWithInnerTriangleGraph.edgeSet) :
    e = wit01 ∨ e = wit02 ∨ e = wit03 ∨ e = wit12 ∨ e = wit23 ∨
      e = wit31 ∨ e = wit45 ∨ e = wit56 ∨ e = wit64 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(0, 2) ∨ e.1 = s(0, 3) ∨
          e.1 = s(1, 2) ∨ e.1 = s(2, 3) ∨ e.1 = s(3, 1) ∨
          e.1 = s(4, 5) ∨ e.1 = s(5, 6) ∨ e.1 = s(6, 4)) ∧
        ¬ e.1.IsDiag := by
    simpa [wheelWithInnerTriangleGraph] using e.2
  rcases h.1 with h01 | h02 | h03 | h12 | h23 | h31 | h45 | h56 | h64
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr <| Or.inl (Subtype.ext h02)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h03)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h12)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h23)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h31)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext h56)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr (Subtype.ext h64)

abbrev WheelWithInnerTriangleFace := Fin 4

def wheelWithInnerTriangleFaces : Finset WheelWithInnerTriangleFace := Finset.univ

def wheelWithInnerTriangleFaceBoundary :
    WheelWithInnerTriangleFace → Finset wheelWithInnerTriangleGraph.edgeSet
  | ⟨0, _⟩ => {wit01, wit02, wit12}
  | ⟨1, _⟩ => {wit02, wit03, wit23}
  | ⟨2, _⟩ => {wit03, wit01, wit31}
  | ⟨3, _⟩ => {wit45, wit56, wit64}

theorem totalIncidenceCount_wit01 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit01 = 2 := by
  decide

theorem totalIncidenceCount_wit02 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit02 = 2 := by
  decide

theorem totalIncidenceCount_wit03 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit03 = 2 := by
  decide

theorem totalIncidenceCount_wit12 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit12 = 1 := by
  decide

theorem totalIncidenceCount_wit23 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit23 = 1 := by
  decide

theorem totalIncidenceCount_wit31 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit31 = 1 := by
  decide

theorem totalIncidenceCount_wit45 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit45 = 1 := by
  decide

theorem totalIncidenceCount_wit56 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit56 = 1 := by
  decide

theorem totalIncidenceCount_wit64 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit64 = 1 := by
  decide

def wheelWithInnerTriangleEmbedding :
    PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph where
  Face := WheelWithInnerTriangleFace
  faceDecidableEq := inferInstance
  faces := wheelWithInnerTriangleFaces
  faceBoundary := wheelWithInnerTriangleFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases wheelWithInnerTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases wheelWithInnerTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

theorem wit12_mem_selectedBoundarySupport :
    wit12 ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit12⟩

theorem wit23_mem_selectedBoundarySupport :
    wit23 ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit23⟩

theorem wit31_mem_selectedBoundarySupport :
    wit31 ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit31⟩

theorem wit45_mem_selectedBoundarySupport :
    wit45 ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit45⟩

theorem wit56_mem_selectedBoundarySupport :
    wit56 ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit56⟩

theorem wit64_mem_selectedBoundarySupport :
    wit64 ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit64⟩

/-! ## Boundary-zero forced-edge verdicts -/

/-- In the shared-interior-pair shell, the two interior edges plus the selected boundary support
cover every edge. Hence any selected-boundary-zero chain vanishing on both interior edges is
zero. -/
theorem sharedInteriorPair_boundaryZero_no_evader_of_vanishes_on_interiorEdges
    (z : sharedInteriorPairGraph.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding)
    (hsip01 : z sip01 = 0) (hsip12 : z sip12 = 0) :
    z = 0 := by
  funext e
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsip01
  · exact hsip12
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      sip23 sip23_mem_selectedBoundarySupport
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      sip30 sip30_mem_selectedBoundarySupport
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      sip24 sip24_mem_selectedBoundarySupport
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      sip40 sip40_mem_selectedBoundarySupport
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      sip56 sip56_mem_selectedBoundarySupport
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      sip67 sip67_mem_selectedBoundarySupport
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      sip75 sip75_mem_selectedBoundarySupport

/-- In the wheel-with-inner-triangle shell, the three spokes plus the selected boundary support
cover every edge. Hence any selected-boundary-zero chain vanishing on all three spokes is zero. -/
theorem wheelWithInnerTriangle_boundaryZero_no_evader_of_vanishes_on_interiorEdges
    (z : wheelWithInnerTriangleGraph.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding)
    (hwit01 : z wit01 = 0) (hwit02 : z wit02 = 0) (hwit03 : z wit03 = 0) :
    z = 0 := by
  funext e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hwit01
  · exact hwit02
  · exact hwit03
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      wit12 wit12_mem_selectedBoundarySupport
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      wit23 wit23_mem_selectedBoundarySupport
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      wit31 wit31_mem_selectedBoundarySupport
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      wit45 wit45_mem_selectedBoundarySupport
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      wit56 wit56_mem_selectedBoundarySupport
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary
      wit64 wit64_mem_selectedBoundarySupport

end Theorem49BoundaryZeroForcedEdgeRegression

end Mettapedia.GraphTheory.FourColor
