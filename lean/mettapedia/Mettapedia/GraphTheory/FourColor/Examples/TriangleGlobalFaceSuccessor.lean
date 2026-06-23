import Mettapedia.GraphTheory.FourColor.PlanarBoundaryRotationSystem

namespace Mettapedia.GraphTheory.FourColor.Examples

namespace TriangleGlobalFaceSuccessor

/-- The complete graph on three vertices, viewed as an oriented triangular
rotation example. -/
def triangleGraph : SimpleGraph (Fin 3) :=
  ⊤

instance triangleGraphDecidableRel : DecidableRel triangleGraph.Adj := by
  dsimp [triangleGraph]
  infer_instance

def dart01 : triangleGraph.Dart := ⟨((0 : Fin 3), 1), by simp [triangleGraph]⟩
def dart12 : triangleGraph.Dart := ⟨((1 : Fin 3), 2), by simp [triangleGraph]⟩
def dart20 : triangleGraph.Dart := ⟨((2 : Fin 3), 0), by simp [triangleGraph]⟩
def dart02 : triangleGraph.Dart := ⟨((0 : Fin 3), 2), by simp [triangleGraph]⟩
def dart21 : triangleGraph.Dart := ⟨((2 : Fin 3), 1), by simp [triangleGraph]⟩
def dart10 : triangleGraph.Dart := ⟨((1 : Fin 3), 0), by simp [triangleGraph]⟩

/-- Counterclockwise around one triangular face and clockwise around the other. -/
def faceSuccessor (d : triangleGraph.Dart) : triangleGraph.Dart :=
  match d.fst, d.snd with
  | 0, 1 => dart12
  | 1, 2 => dart20
  | 2, 0 => dart01
  | 0, 2 => dart21
  | 2, 1 => dart10
  | 1, 0 => dart02
  | _, _ => dart01

/-- The inverse orientation of `faceSuccessor`. -/
def facePredecessor (d : triangleGraph.Dart) : triangleGraph.Dart :=
  match d.fst, d.snd with
  | 0, 1 => dart20
  | 2, 0 => dart12
  | 1, 2 => dart01
  | 0, 2 => dart10
  | 1, 0 => dart21
  | 2, 1 => dart02
  | _, _ => dart01

theorem facePredecessor_leftInverse :
    Function.LeftInverse facePredecessor faceSuccessor := by
  intro d
  rcases d with ⟨⟨a, b⟩, h⟩
  fin_cases a <;> fin_cases b <;>
    simp [triangleGraph, faceSuccessor, facePredecessor, dart01, dart12,
      dart20, dart02, dart21, dart10] at h ⊢

theorem facePredecessor_rightInverse :
    Function.RightInverse facePredecessor faceSuccessor := by
  intro d
  rcases d with ⟨⟨a, b⟩, h⟩
  fin_cases a <;> fin_cases b <;>
    simp [triangleGraph, faceSuccessor, facePredecessor, dart01, dart12,
      dart20, dart02, dart21, dart10] at h ⊢

theorem faceSuccessor_fst :
    ∀ d : triangleGraph.Dart, (faceSuccessor d).fst = d.snd := by
  intro d
  rcases d with ⟨⟨a, b⟩, h⟩
  fin_cases a <;> fin_cases b <;>
    simp [triangleGraph, faceSuccessor, dart01, dart12, dart20, dart02,
      dart21, dart10] at h ⊢

/-- The first concrete active example of the global face-successor function
package. It supplies a genuine global successor/predecessor pair on all darts
of the triangle. -/
def globalFaceSuccessorFunctionData :
    SimpleGraphDartRotation.FaceSuccessorFunctionData triangleGraph where
  faceSuccessor := faceSuccessor
  facePredecessor := facePredecessor
  left_inv := facePredecessor_leftInverse
  right_inv := facePredecessor_rightInverse
  faceSuccessor_fst := faceSuccessor_fst
  outer := dart01

/-- The concrete triangle example lowers to the permutation-based global
face-successor package. -/
def globalFaceSuccessorData :
    SimpleGraphDartRotation.FaceSuccessorData triangleGraph :=
  globalFaceSuccessorFunctionData.toFaceSuccessorData

/-- The concrete triangle example lowers all the way to a bare rotation system. -/
noncomputable def rotationSystem : RotationSystem (Fin 3) triangleGraph.edgeSet :=
  globalFaceSuccessorFunctionData.toRotationSystem

@[simp]
theorem rotationSystem_phi (d : triangleGraph.Dart) :
    globalFaceSuccessorFunctionData.toRotationSystem.phi d = faceSuccessor d := by
  exact SimpleGraphDartRotation.FaceSuccessorFunctionData.toRotationSystem_phi
    (G := triangleGraph) globalFaceSuccessorFunctionData d

/-- The two sides of the triangular embedding. -/
inductive TriangleFace
  | outer
  | inner
  deriving DecidableEq, Fintype

def edge01 : triangleGraph.edgeSet := ⟨dart01.edge, dart01.edge_mem⟩
def edge12 : triangleGraph.edgeSet := ⟨dart12.edge, dart12.edge_mem⟩
def edge20 : triangleGraph.edgeSet := ⟨dart20.edge, dart20.edge_mem⟩

/-- The three unoriented edges on either side of the triangle. -/
def triangleFaceBoundary : Finset triangleGraph.edgeSet := {edge01, edge12, edge20}

theorem mem_triangleFaceBoundary (e : triangleGraph.edgeSet) :
    e ∈ triangleFaceBoundary := by
  fin_cases e <;>
    simp [triangleFaceBoundary, edge01, edge12, edge20, dart01, dart12, dart20,
      triangleGraph]

/-- A tiny plane-embedding-with-boundary source: both faces of the triangle are
incident to all three triangle edges. -/
def triangleEmbedding : PlaneEmbeddingWithBoundary triangleGraph where
  Face := TriangleFace
  faceDecidableEq := inferInstance
  faces := Finset.univ
  faceBoundary := fun _ => triangleFaceBoundary
  edge_mem_faceSupport := by
    intro e
    exact Finset.mem_biUnion.2 ⟨TriangleFace.outer, by simp, mem_triangleFaceBoundary e⟩
  edge_one_or_two_faces := by
    intro e he
    right
    have hfilter :
        (Finset.univ.filter fun _ : TriangleFace => e ∈ triangleFaceBoundary) =
          Finset.univ := by
      ext f
      simp [mem_triangleFaceBoundary e]
    rw [hfilter]
    decide

def outerFace : {f // f ∈ triangleEmbedding.faces} :=
  ⟨TriangleFace.outer, by simp [triangleEmbedding]⟩

def innerFace : {f // f ∈ triangleEmbedding.faces} :=
  ⟨TriangleFace.inner, by simp [triangleEmbedding]⟩

def outerDarts : List triangleGraph.Dart := [dart01, dart12, dart20]
def innerDarts : List triangleGraph.Dart := [dart02, dart21, dart10]

theorem outerDarts_hnodup_edges : (outerDarts.map fun d => d.edge).Nodup := by
  decide

theorem innerDarts_hnodup_edges : (innerDarts.map fun d => d.edge).Nodup := by
  decide

theorem dart01_edge_mem_boundary_image :
    dart01.edge ∈ triangleFaceBoundary.image Subtype.val := by
  exact Finset.mem_image.2 ⟨edge01, mem_triangleFaceBoundary edge01, rfl⟩

theorem dart12_edge_mem_boundary_image :
    dart12.edge ∈ triangleFaceBoundary.image Subtype.val := by
  exact Finset.mem_image.2 ⟨edge12, mem_triangleFaceBoundary edge12, rfl⟩

theorem dart20_edge_mem_boundary_image :
    dart20.edge ∈ triangleFaceBoundary.image Subtype.val := by
  exact Finset.mem_image.2 ⟨edge20, mem_triangleFaceBoundary edge20, rfl⟩

theorem dart02_edge_mem_boundary_image :
    dart02.edge ∈ triangleFaceBoundary.image Subtype.val := by
  refine Finset.mem_image.2 ⟨edge20, mem_triangleFaceBoundary edge20, ?_⟩
  simp [edge20, dart20, dart02]

theorem dart21_edge_mem_boundary_image :
    dart21.edge ∈ triangleFaceBoundary.image Subtype.val := by
  refine Finset.mem_image.2 ⟨edge12, mem_triangleFaceBoundary edge12, ?_⟩
  simp [edge12, dart12, dart21]

theorem dart10_edge_mem_boundary_image :
    dart10.edge ∈ triangleFaceBoundary.image Subtype.val := by
  refine Finset.mem_image.2 ⟨edge01, mem_triangleFaceBoundary edge01, ?_⟩
  simp [edge01, dart01, dart10]

theorem outerDarts_hedge_sub :
    ∀ d ∈ outerDarts,
      d.edge ∈ (triangleEmbedding.faceBoundary TriangleFace.outer).image Subtype.val := by
  intro d hd
  simp [outerDarts] at hd
  rcases hd with rfl | rfl | rfl
  · exact dart01_edge_mem_boundary_image
  · exact dart12_edge_mem_boundary_image
  · exact dart20_edge_mem_boundary_image

theorem innerDarts_hedge_sub :
    ∀ d ∈ innerDarts,
      d.edge ∈ (triangleEmbedding.faceBoundary TriangleFace.inner).image Subtype.val := by
  intro d hd
  simp [innerDarts] at hd
  rcases hd with rfl | rfl | rfl
  · exact dart02_edge_mem_boundary_image
  · exact dart21_edge_mem_boundary_image
  · exact dart10_edge_mem_boundary_image

theorem outerDarts_hface_sub :
    ∀ e ∈ triangleEmbedding.faceBoundary TriangleFace.outer,
      (e : Sym2 (Fin 3)) ∈ outerDarts.map fun d => d.edge := by
  intro e he
  fin_cases e <;>
    simp [outerDarts, dart01, dart12, dart20, triangleGraph]

theorem innerDarts_hface_sub :
    ∀ e ∈ triangleEmbedding.faceBoundary TriangleFace.inner,
      (e : Sym2 (Fin 3)) ∈ innerDarts.map fun d => d.edge := by
  intro e he
  fin_cases e <;>
    simp [innerDarts, dart02, dart21, dart10, triangleGraph]

theorem outerDarts_hsuccessor_order :
    List.Forall₂ (fun d d' : triangleGraph.Dart => faceSuccessor d = d')
      outerDarts (outerDarts.tail ++ outerDarts.head?.toList) := by
  simp [outerDarts, faceSuccessor, dart01, dart12, dart20]

theorem innerDarts_hsuccessor_order :
    List.Forall₂ (fun d d' : triangleGraph.Dart => faceSuccessor d = d')
      innerDarts (innerDarts.tail ++ innerDarts.head?.toList) := by
  simp [innerDarts, faceSuccessor, dart02, dart21, dart10]

theorem outerDarts_hsuccessor_adj :
    ∀ d ∈ outerDarts, triangleGraph.DartAdj d (faceSuccessor d) := by
  intro d hd
  simp [outerDarts] at hd
  rcases hd with rfl | rfl | rfl <;>
    simp [SimpleGraph.DartAdj, faceSuccessor, dart01, dart12, dart20]

theorem innerDarts_hsuccessor_adj :
    ∀ d ∈ innerDarts, triangleGraph.DartAdj d (faceSuccessor d) := by
  intro d hd
  simp [innerDarts] at hd
  rcases hd with rfl | rfl | rfl <;>
    simp [SimpleGraph.DartAdj, faceSuccessor, dart02, dart21, dart10]

/-- The face-local successor-cycle data for the two triangular faces. -/
def triangleFaceBoundaryDartSuccessorCycle
    (f : {f // f ∈ triangleEmbedding.faces}) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle triangleEmbedding f := by
  rcases f with ⟨face, hface⟩
  cases face
  · exact
      { darts := outerDarts
        hnonempty := by simp [outerDarts]
        successor := faceSuccessor
        hsuccessor_order := outerDarts_hsuccessor_order
        hsuccessor_adj := outerDarts_hsuccessor_adj
        hnodup_edges := outerDarts_hnodup_edges
        hedge_sub := outerDarts_hedge_sub
        hface_sub := outerDarts_hface_sub }
  · exact
      { darts := innerDarts
        hnonempty := by simp [innerDarts]
        successor := faceSuccessor
        hsuccessor_order := innerDarts_hsuccessor_order
        hsuccessor_adj := innerDarts_hsuccessor_adj
        hnodup_edges := innerDarts_hnodup_edges
        hedge_sub := innerDarts_hedge_sub
        hface_sub := innerDarts_hface_sub }

/-- The triangle example as full planar-boundary global-face-successor data:
the face-local boundary cycles and the global face successor are compatible. -/
def trianglePlanarBoundaryGlobalFaceSuccessorFunctionData :
    PlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData triangleEmbedding where
  faceBoundaryDartSuccessorCycle := triangleFaceBoundaryDartSuccessorCycle
  faceSuccessor := faceSuccessor
  facePredecessor := facePredecessor
  left_inv := facePredecessor_leftInverse
  right_inv := facePredecessor_rightInverse
  faceSuccessor_fst := faceSuccessor_fst
  outerFace := outerFace
  outerDart := dart01
  outerDart_mem := by
    simp [outerFace, triangleFaceBoundaryDartSuccessorCycle, outerDarts, dart01]
  faceSuccessor_agrees := by
    intro f d hd
    rcases f with ⟨face, hface⟩
    cases face <;> rfl

/-- The rotation system obtained through the planar-boundary bridge. -/
noncomputable def planarBoundaryRotationSystem :
    RotationSystem (Fin 3) triangleGraph.edgeSet :=
  trianglePlanarBoundaryGlobalFaceSuccessorFunctionData.toRotationSystem

@[simp]
theorem planarBoundaryRotationSystem_phi (d : triangleGraph.Dart) :
    trianglePlanarBoundaryGlobalFaceSuccessorFunctionData.toRotationSystem.phi d =
      faceSuccessor d := by
  exact PlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData.toRotationSystem_phi
    (G := triangleGraph) trianglePlanarBoundaryGlobalFaceSuccessorFunctionData d

theorem triangleGraph_admitsPlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData :
    AdmitsPlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData triangleGraph :=
  ⟨triangleEmbedding, ⟨trianglePlanarBoundaryGlobalFaceSuccessorFunctionData⟩⟩

theorem triangleGraph_admitsPlanarBoundaryGlobalFaceSuccessorEmbeddingData :
    AdmitsPlanarBoundaryGlobalFaceSuccessorEmbeddingData triangleGraph :=
  admitsPlanarBoundaryGlobalFaceSuccessorEmbeddingData_of_admitsPlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData
    triangleGraph_admitsPlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData

theorem triangleGraph_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData :
    AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData triangleGraph :=
  admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_of_admitsPlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData
    triangleGraph_admitsPlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData

/-- The two local face cycles cover every oriented dart of the concrete
triangle. -/
theorem triangleFaceCycles_cover_all_darts :
    trianglePlanarBoundaryGlobalFaceSuccessorFunctionData.CoversAllDarts := by
  refine ⟨?_⟩
  intro d
  rcases d with ⟨⟨a, b⟩, h⟩
  fin_cases a <;> fin_cases b
  · simp [triangleGraph] at h
  · exact
      ⟨outerFace, by
        simp [trianglePlanarBoundaryGlobalFaceSuccessorFunctionData,
          triangleFaceBoundaryDartSuccessorCycle, outerFace, outerDarts, dart01]⟩
  · exact
      ⟨innerFace, by
        simp [trianglePlanarBoundaryGlobalFaceSuccessorFunctionData,
          triangleFaceBoundaryDartSuccessorCycle, innerFace, innerDarts, dart02]⟩
  · exact
      ⟨innerFace, by
        simp [trianglePlanarBoundaryGlobalFaceSuccessorFunctionData,
          triangleFaceBoundaryDartSuccessorCycle, innerFace, innerDarts, dart10]⟩
  · simp [triangleGraph] at h
  · exact
      ⟨outerFace, by
        simp [trianglePlanarBoundaryGlobalFaceSuccessorFunctionData,
          triangleFaceBoundaryDartSuccessorCycle, outerFace, outerDarts, dart12]⟩
  · exact
      ⟨outerFace, by
        simp [trianglePlanarBoundaryGlobalFaceSuccessorFunctionData,
          triangleFaceBoundaryDartSuccessorCycle, outerFace, outerDarts, dart20]⟩
  · exact
      ⟨innerFace, by
        simp [trianglePlanarBoundaryGlobalFaceSuccessorFunctionData,
          triangleFaceBoundaryDartSuccessorCycle, innerFace, innerDarts, dart21]⟩
  · simp [triangleGraph] at h

/-- The concrete triangle's two local face cycles assign each oriented dart to
at most one face. -/
theorem triangleFaceCycles_cover_all_darts_disjoint :
    trianglePlanarBoundaryGlobalFaceSuccessorFunctionData.CoversAllDartsDisjoint := by
  refine
    { dart_cover := triangleFaceCycles_cover_all_darts.dart_cover
      dart_unique := ?_ }
  intro f g d hf hg
  rcases f with ⟨faceF, hfaceF⟩
  rcases g with ⟨faceG, hfaceG⟩
  cases faceF <;> cases faceG
  · exact Subtype.ext rfl
  · exfalso
    have hfOuter : d ∈ outerDarts := by
      simpa [trianglePlanarBoundaryGlobalFaceSuccessorFunctionData,
        triangleFaceBoundaryDartSuccessorCycle] using hf
    have hgInner : d ∈ innerDarts := by
      simpa [trianglePlanarBoundaryGlobalFaceSuccessorFunctionData,
        triangleFaceBoundaryDartSuccessorCycle] using hg
    simp [outerDarts] at hfOuter
    rcases hfOuter with rfl | rfl | rfl <;>
      simp [innerDarts, dart01, dart12, dart20, dart02, dart21, dart10,
        triangleGraph] at hgInner
  · exfalso
    have hfInner : d ∈ innerDarts := by
      simpa [trianglePlanarBoundaryGlobalFaceSuccessorFunctionData,
        triangleFaceBoundaryDartSuccessorCycle] using hf
    have hgOuter : d ∈ outerDarts := by
      simpa [trianglePlanarBoundaryGlobalFaceSuccessorFunctionData,
        triangleFaceBoundaryDartSuccessorCycle] using hg
    simp [innerDarts] at hfInner
    rcases hfInner with rfl | rfl | rfl <;>
      simp [outerDarts, dart01, dart12, dart20, dart02, dart21, dart10,
        triangleGraph] at hgOuter
  · exact Subtype.ext rfl

theorem triangleFaceCycles_exists_local_successor_eq
    (d : triangleGraph.Dart) :
    ∃ f : {f // f ∈ triangleEmbedding.faces},
      d ∈ (trianglePlanarBoundaryGlobalFaceSuccessorFunctionData.faceBoundaryDartSuccessorCycle f).darts ∧
        faceSuccessor d =
          (trianglePlanarBoundaryGlobalFaceSuccessorFunctionData.faceBoundaryDartSuccessorCycle f).successor d :=
  trianglePlanarBoundaryGlobalFaceSuccessorFunctionData.exists_local_successor_eq_of_covers
    triangleFaceCycles_cover_all_darts d

end TriangleGlobalFaceSuccessor

end Mettapedia.GraphTheory.FourColor.Examples
