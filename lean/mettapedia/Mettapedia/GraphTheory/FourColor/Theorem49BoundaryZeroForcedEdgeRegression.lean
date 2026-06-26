import Mettapedia.GraphTheory.FourColor.Theorem49TargetSubspace
import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryFreeSelectorConstruction
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.FourColor.CAP5WitnessGenerator
import Mettapedia.GraphTheory.FourColor.CAP5PathXorDetector
import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorCoordinateDetector

/-!
Finite F2 boundary-zero regressions mined from the ignored CAP5 validation lab.

The lab checks small annular shells against forced interior-edge supports.
This module records the buildable Lean endpoint: if the forced set covers the
whole interior support, selected-boundary-zero chains have no remaining
coordinate where an obstruction can hide.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49ForcingInteriorEdgeObstruction

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

@[simp] theorem sip01_ne_sip12 : sip01 ≠ sip12 := by
  decide

@[simp] theorem sip12_ne_sip01 : sip12 ≠ sip01 := by
  decide

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

noncomputable instance sharedInteriorPairGraph_edgeSet_fintype :
    Fintype sharedInteriorPairGraph.edgeSet :=
  ⟨{sip01, sip12, sip23, sip30, sip24, sip40, sip56, sip67, sip75}, by
    intro e
    rcases sharedInteriorPair_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp⟩

theorem sharedInteriorPair_incidentEdgeFinset_one :
    incidentEdgeFinset sharedInteriorPairGraph (1 : Fin 8) = {sip01, sip12} := by
  ext e
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem sharedInteriorPair_vertexKirchhoffSum_one
    (z : sharedInteriorPairGraph.edgeSet → Color) :
    vertexKirchhoffSum sharedInteriorPairGraph z (1 : Fin 8) =
      z sip01 + z sip12 := by
  unfold vertexKirchhoffSum
  rw [sharedInteriorPair_incidentEdgeFinset_one]
  simp

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

theorem sip01_not_mem_selectedBoundarySupport :
    sip01 ∉ selectedBoundarySupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces
      sharedInteriorPairEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces
      sharedInteriorPairEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip01 = 1 := by
    simpa [sharedInteriorPairEmbedding] using hcount
  rw [totalIncidenceCount_sip01] at hcount'
  norm_num at hcount'

theorem sip12_not_mem_selectedBoundarySupport :
    sip12 ∉ selectedBoundarySupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces
      sharedInteriorPairEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces
      sharedInteriorPairEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip12 = 1 := by
    simpa [sharedInteriorPairEmbedding] using hcount
  rw [totalIncidenceCount_sip12] at hcount'
  norm_num at hcount'

theorem sip01_mem_interiorEdgeSupport :
    sip01 ∈ interiorEdgeSupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip01⟩

theorem sip12_mem_interiorEdgeSupport :
    sip12 ∈ interiorEdgeSupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip12⟩

theorem sharedInteriorPair_interiorEdgeSupport_eq :
    interiorEdgeSupport
        sharedInteriorPairEmbedding.faceBoundary
        sharedInteriorPairEmbedding.faces =
      ({sip01, sip12} : Finset sharedInteriorPairGraph.edgeSet) := by
  ext e
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

def sipFace0 : AmbientFace sharedInteriorPairEmbedding.faces :=
  ⟨(0 : SharedInteriorPairFace), by decide⟩

def sipFace1 : AmbientFace sharedInteriorPairEmbedding.faces :=
  ⟨(1 : SharedInteriorPairFace), by decide⟩

def sipFace2 : AmbientFace sharedInteriorPairEmbedding.faces :=
  ⟨(2 : SharedInteriorPairFace), by decide⟩

theorem sipFace_cases
    (f : AmbientFace sharedInteriorPairEmbedding.faces) :
    f = sipFace0 ∨ f = sipFace1 ∨ f = sipFace2 := by
  rcases f with ⟨⟨n, hn⟩, hf⟩
  interval_cases n <;> simp [sipFace0, sipFace1, sipFace2]

theorem sip01_mem_faceBoundary_iff
    (f : AmbientFace sharedInteriorPairEmbedding.faces) :
    sip01 ∈ sharedInteriorPairEmbedding.faceBoundary f.1 ↔
      f = sipFace0 ∨ f = sipFace1 := by
  rcases sipFace_cases f with rfl | rfl | rfl <;>
    decide

theorem sip12_mem_faceBoundary_iff
    (f : AmbientFace sharedInteriorPairEmbedding.faces) :
    sip12 ∈ sharedInteriorPairEmbedding.faceBoundary f.1 ↔
      f = sipFace0 ∨ f = sipFace1 := by
  rcases sipFace_cases f with rfl | rfl | rfl <;>
    decide

theorem sip12_mem_faceBoundary_of_sip01_mem
    {f : AmbientFace sharedInteriorPairEmbedding.faces}
    (hf : sip01 ∈ sharedInteriorPairEmbedding.faceBoundary f.1) :
    sip12 ∈ sharedInteriorPairEmbedding.faceBoundary f.1 :=
  (sip12_mem_faceBoundary_iff f).2 ((sip01_mem_faceBoundary_iff f).1 hf)

theorem sip01_mem_faceBoundary_of_sip12_mem
    {f : AmbientFace sharedInteriorPairEmbedding.faces}
    (hf : sip12 ∈ sharedInteriorPairEmbedding.faceBoundary f.1) :
    sip01 ∈ sharedInteriorPairEmbedding.faceBoundary f.1 :=
  (sip01_mem_faceBoundary_iff f).2 ((sip12_mem_faceBoundary_iff f).1 hf)

theorem not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair :
    ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          sharedInteriorPairEmbedding) := by
  rintro ⟨data⟩
  rcases Finset.mem_image.1 (data.hcover sip01_mem_interiorEdgeSupport) with
    ⟨f01, hf01Peel, hf01Witness⟩
  have hf01WitnessMem :
      data.witnessEdge f01 ∈ sharedInteriorPairEmbedding.faceBoundary f01.1 :=
    data.hwitness f01 hf01Peel
  have hsip01_f01 :
      sip01 ∈ sharedInteriorPairEmbedding.faceBoundary f01.1 := by
    simpa [hf01Witness] using hf01WitnessMem
  have hsip12_f01 :
      sip12 ∈ sharedInteriorPairEmbedding.faceBoundary f01.1 :=
    sip12_mem_faceBoundary_of_sip01_mem hsip01_f01
  have hsip12_erase :
      sip12 ∈
        (sharedInteriorPairEmbedding.faceBoundary f01.1).erase
          (data.witnessEdge f01) := by
    refine Finset.mem_erase.2 ⟨?_, hsip12_f01⟩
    intro h
    exact sip01_ne_sip12 (hf01Witness.symm.trans h.symm)
  rcases data.hrest f01 hf01Peel sip12 hsip12_erase with
    hsip12Boundary | ⟨f12, hf12Peel, hf12Witness, hlt01_12⟩
  · exact sip12_not_mem_selectedBoundarySupport hsip12Boundary
  have hf12WitnessMem :
      data.witnessEdge f12 ∈ sharedInteriorPairEmbedding.faceBoundary f12.1 :=
    data.hwitness f12 hf12Peel
  have hsip12_f12 :
      sip12 ∈ sharedInteriorPairEmbedding.faceBoundary f12.1 := by
    simpa [hf12Witness] using hf12WitnessMem
  have hsip01_f12 :
      sip01 ∈ sharedInteriorPairEmbedding.faceBoundary f12.1 :=
    sip01_mem_faceBoundary_of_sip12_mem hsip12_f12
  have hsip01_erase :
      sip01 ∈
        (sharedInteriorPairEmbedding.faceBoundary f12.1).erase
          (data.witnessEdge f12) := by
    refine Finset.mem_erase.2 ⟨?_, hsip01_f12⟩
    intro h
    exact sip01_ne_sip12 (h.trans hf12Witness)
  rcases data.hrest f12 hf12Peel sip01 hsip01_erase with
    hsip01Boundary | ⟨f01Next, hf01NextPeel, hf01NextWitness, hlt12_next⟩
  · exact sip01_not_mem_selectedBoundarySupport hsip01Boundary
  have hf01NextWitnessMem :
      data.witnessEdge f01Next ∈
        sharedInteriorPairEmbedding.faceBoundary f01Next.1 :=
    data.hwitness f01Next hf01NextPeel
  have hsip01_f01Next :
      sip01 ∈ sharedInteriorPairEmbedding.faceBoundary f01Next.1 := by
    simpa [hf01NextWitness] using hf01NextWitnessMem
  have hf01_cases : f01 = sipFace0 ∨ f01 = sipFace1 :=
    (sip01_mem_faceBoundary_iff f01).1 hsip01_f01
  have hf12_cases : f12 = sipFace0 ∨ f12 = sipFace1 :=
    (sip12_mem_faceBoundary_iff f12).1 hsip12_f12
  have hf01Next_cases : f01Next = sipFace0 ∨ f01Next = sipFace1 :=
    (sip01_mem_faceBoundary_iff f01Next).1 hsip01_f01Next
  have hf01_ne_f12 : f01 ≠ f12 := by
    intro h
    subst h
    exact sip01_ne_sip12 (hf01Witness.symm.trans hf12Witness)
  have hf01Next_ne_f12 : f01Next ≠ f12 := by
    intro h
    subst h
    exact sip01_ne_sip12 (hf01NextWitness.symm.trans hf12Witness)
  have hf01Next_eq_f01 : f01Next = f01 := by
    rcases hf01_cases with rfl | rfl
    · rcases hf12_cases with rfl | rfl
      · exact False.elim (hf01_ne_f12 rfl)
      · rcases hf01Next_cases with rfl | rfl
        · rfl
        · exact False.elim (hf01Next_ne_f12 rfl)
    · rcases hf12_cases with rfl | rfl
      · rcases hf01Next_cases with rfl | rfl
        · exact False.elim (hf01Next_ne_f12 rfl)
        · rfl
      · exact False.elim (hf01_ne_f12 rfl)
  have hlt01_next : data.height f01 < data.height f01Next :=
    lt_trans hlt01_12 hlt12_next
  rw [hf01Next_eq_f01] at hlt01_next
  exact (Nat.lt_irrefl _ hlt01_next).elim

/-- Boundary-zero-only evader when the shared-interior-pair shell forces only `sip01`. -/
def sharedInteriorPairSip01OnlyEvader : sharedInteriorPairGraph.edgeSet → Color :=
  indicatorChain red ({sip12} : Finset sharedInteriorPairGraph.edgeSet)

/-- Boundary-zero-only evader when the shared-interior-pair shell forces only `sip12`. -/
def sharedInteriorPairSip12OnlyEvader : sharedInteriorPairGraph.edgeSet → Color :=
  indicatorChain red ({sip01} : Finset sharedInteriorPairGraph.edgeSet)

/-- Boundary-zero/Kirchhoff evader when no shared-interior-pair interior edge is forced. -/
def sharedInteriorPairNoForceKirchhoffEvader : sharedInteriorPairGraph.edgeSet → Color :=
  indicatorChain red ({sip01, sip12} : Finset sharedInteriorPairGraph.edgeSet)

theorem sharedInteriorPairSip01OnlyEvader_mem_planarBoundaryZeroSubmodule :
    sharedInteriorPairSip01OnlyEvader ∈
      planarBoundaryZeroSubmodule sharedInteriorPairEmbedding := by
  intro e he
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · exact False.elim (sip12_not_mem_selectedBoundarySupport he)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem sharedInteriorPairSip12OnlyEvader_mem_planarBoundaryZeroSubmodule :
    sharedInteriorPairSip12OnlyEvader ∈
      planarBoundaryZeroSubmodule sharedInteriorPairEmbedding := by
  intro e he
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (sip01_not_mem_selectedBoundarySupport he)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem sharedInteriorPairNoForceKirchhoffEvader_mem_planarBoundaryZeroSubmodule :
    sharedInteriorPairNoForceKirchhoffEvader ∈
      planarBoundaryZeroSubmodule sharedInteriorPairEmbedding := by
  intro e he
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (sip01_not_mem_selectedBoundarySupport he)
  · exact False.elim (sip12_not_mem_selectedBoundarySupport he)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem sharedInteriorPairNoForceKirchhoffEvader_mem_kirchhoffSubmodule :
    sharedInteriorPairNoForceKirchhoffEvader ∈
      kirchhoffSubmodule sharedInteriorPairGraph
        ({(1 : Fin 8)} : Finset (Fin 8)) := by
  intro v hv
  have hv1 : v = (1 : Fin 8) := by
    simpa using hv
  subst v
  rw [sharedInteriorPair_vertexKirchhoffSum_one]
  simp [sharedInteriorPairNoForceKirchhoffEvader]

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

@[simp] theorem wit01_ne_wit02 : wit01 ≠ wit02 := by
  decide

@[simp] theorem wit01_ne_wit03 : wit01 ≠ wit03 := by
  decide

@[simp] theorem wit02_ne_wit01 : wit02 ≠ wit01 := by
  decide

@[simp] theorem wit02_ne_wit03 : wit02 ≠ wit03 := by
  decide

@[simp] theorem wit03_ne_wit01 : wit03 ≠ wit01 := by
  decide

@[simp] theorem wit03_ne_wit02 : wit03 ≠ wit02 := by
  decide

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

noncomputable instance wheelWithInnerTriangleGraph_edgeSet_fintype :
    Fintype wheelWithInnerTriangleGraph.edgeSet :=
  ⟨{wit01, wit02, wit03, wit12, wit23, wit31, wit45, wit56, wit64}, by
    intro e
    rcases wheelWithInnerTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp⟩

theorem wheelWithInnerTriangle_incidentEdgeFinset_zero :
    incidentEdgeFinset wheelWithInnerTriangleGraph (0 : Fin 7) = {wit01, wit02, wit03} := by
  ext e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem wheelWithInnerTriangle_vertexKirchhoffSum_zero
    (z : wheelWithInnerTriangleGraph.edgeSet → Color) :
    vertexKirchhoffSum wheelWithInnerTriangleGraph z (0 : Fin 7) =
      z wit01 + z wit02 + z wit03 := by
  unfold vertexKirchhoffSum
  rw [wheelWithInnerTriangle_incidentEdgeFinset_zero]
  simp [add_assoc]

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

theorem wit01_not_mem_selectedBoundarySupport :
    wit01 ∉ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount wheelWithInnerTriangleFaceBoundary
        wheelWithInnerTriangleFaces wit01 = 1 := by
    simpa [wheelWithInnerTriangleEmbedding] using hcount
  rw [totalIncidenceCount_wit01] at hcount'
  norm_num at hcount'

theorem wit02_not_mem_selectedBoundarySupport :
    wit02 ∉ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount wheelWithInnerTriangleFaceBoundary
        wheelWithInnerTriangleFaces wit02 = 1 := by
    simpa [wheelWithInnerTriangleEmbedding] using hcount
  rw [totalIncidenceCount_wit02] at hcount'
  norm_num at hcount'

theorem wit03_not_mem_selectedBoundarySupport :
    wit03 ∉ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount wheelWithInnerTriangleFaceBoundary
        wheelWithInnerTriangleFaces wit03 = 1 := by
    simpa [wheelWithInnerTriangleEmbedding] using hcount
  rw [totalIncidenceCount_wit03] at hcount'
  norm_num at hcount'

theorem wheelWithInnerTriangle_interiorEdgeSupport_eq :
    interiorEdgeSupport
        wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces =
      ({wit01, wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
  ext e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- Boundary-zero/Kirchhoff evader when the wheel shell forces only `wit01`. -/
def wheelWithInnerTriangleWit01OnlyEvader : wheelWithInnerTriangleGraph.edgeSet → Color :=
  indicatorChain red ({wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet)

/-- Boundary-zero/Kirchhoff evader when the wheel shell forces only `wit02`. -/
def wheelWithInnerTriangleWit02OnlyEvader : wheelWithInnerTriangleGraph.edgeSet → Color :=
  indicatorChain red ({wit01, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet)

/-- Boundary-zero/Kirchhoff evader when the wheel shell forces only `wit03`. -/
def wheelWithInnerTriangleWit03OnlyEvader : wheelWithInnerTriangleGraph.edgeSet → Color :=
  indicatorChain red ({wit01, wit02} : Finset wheelWithInnerTriangleGraph.edgeSet)

/-- Boundary-zero-only evader when the wheel shell forces `wit01` and `wit02`. -/
def wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader :
    wheelWithInnerTriangleGraph.edgeSet → Color :=
  indicatorChain red ({wit03} : Finset wheelWithInnerTriangleGraph.edgeSet)

/-- Boundary-zero-only evader when the wheel shell forces `wit01` and `wit03`. -/
def wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader :
    wheelWithInnerTriangleGraph.edgeSet → Color :=
  indicatorChain red ({wit02} : Finset wheelWithInnerTriangleGraph.edgeSet)

/-- Boundary-zero-only evader when the wheel shell forces `wit02` and `wit03`. -/
def wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader :
    wheelWithInnerTriangleGraph.edgeSet → Color :=
  indicatorChain red ({wit01} : Finset wheelWithInnerTriangleGraph.edgeSet)

theorem wheelWithInnerTriangleWit01OnlyEvader_mem_planarBoundaryZeroSubmodule :
    wheelWithInnerTriangleWit01OnlyEvader ∈
      planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding := by
  intro e he
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · exact False.elim (wit02_not_mem_selectedBoundarySupport he)
  · exact False.elim (wit03_not_mem_selectedBoundarySupport he)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem wheelWithInnerTriangleWit02OnlyEvader_mem_planarBoundaryZeroSubmodule :
    wheelWithInnerTriangleWit02OnlyEvader ∈
      planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding := by
  intro e he
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (wit01_not_mem_selectedBoundarySupport he)
  · decide
  · exact False.elim (wit03_not_mem_selectedBoundarySupport he)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem wheelWithInnerTriangleWit03OnlyEvader_mem_planarBoundaryZeroSubmodule :
    wheelWithInnerTriangleWit03OnlyEvader ∈
      planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding := by
  intro e he
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (wit01_not_mem_selectedBoundarySupport he)
  · exact False.elim (wit02_not_mem_selectedBoundarySupport he)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader_mem_planarBoundaryZeroSubmodule :
    wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader ∈
      planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding := by
  intro e he
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · exact False.elim (wit03_not_mem_selectedBoundarySupport he)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader_mem_planarBoundaryZeroSubmodule :
    wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader ∈
      planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding := by
  intro e he
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · exact False.elim (wit02_not_mem_selectedBoundarySupport he)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader_mem_planarBoundaryZeroSubmodule :
    wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader ∈
      planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding := by
  intro e he
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (wit01_not_mem_selectedBoundarySupport he)
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem wheelWithInnerTriangleWit01OnlyEvader_mem_kirchhoffSubmodule :
    wheelWithInnerTriangleWit01OnlyEvader ∈
      kirchhoffSubmodule wheelWithInnerTriangleGraph
        ({(0 : Fin 7)} : Finset (Fin 7)) := by
  intro v hv
  have hv0 : v = (0 : Fin 7) := by
    simpa using hv
  subst v
  rw [wheelWithInnerTriangle_vertexKirchhoffSum_zero]
  simp [wheelWithInnerTriangleWit01OnlyEvader]

theorem wheelWithInnerTriangleWit02OnlyEvader_mem_kirchhoffSubmodule :
    wheelWithInnerTriangleWit02OnlyEvader ∈
      kirchhoffSubmodule wheelWithInnerTriangleGraph
        ({(0 : Fin 7)} : Finset (Fin 7)) := by
  intro v hv
  have hv0 : v = (0 : Fin 7) := by
    simpa using hv
  subst v
  rw [wheelWithInnerTriangle_vertexKirchhoffSum_zero]
  simp [wheelWithInnerTriangleWit02OnlyEvader]

theorem wheelWithInnerTriangleWit03OnlyEvader_mem_kirchhoffSubmodule :
    wheelWithInnerTriangleWit03OnlyEvader ∈
      kirchhoffSubmodule wheelWithInnerTriangleGraph
        ({(0 : Fin 7)} : Finset (Fin 7)) := by
  intro v hv
  have hv0 : v = (0 : Fin 7) := by
    simpa using hv
  subst v
  rw [wheelWithInnerTriangle_vertexKirchhoffSum_zero]
  simp [wheelWithInnerTriangleWit03OnlyEvader]

/-! ## Endpoint-touch path counterexample shell -/

def endpointTouchPathGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 3)} : Set (Sym2 (Fin 4)))

def et01 : endpointTouchPathGraph.edgeSet := ⟨s(0, 1), by
  simp [endpointTouchPathGraph]⟩

def et12 : endpointTouchPathGraph.edgeSet := ⟨s(1, 2), by
  simp [endpointTouchPathGraph]⟩

def et23 : endpointTouchPathGraph.edgeSet := ⟨s(2, 3), by
  simp [endpointTouchPathGraph]⟩

@[simp] theorem et01_ne_et12 : et01 ≠ et12 := by
  decide

@[simp] theorem et01_ne_et23 : et01 ≠ et23 := by
  decide

@[simp] theorem et12_ne_et01 : et12 ≠ et01 := by
  decide

@[simp] theorem et12_ne_et23 : et12 ≠ et23 := by
  decide

@[simp] theorem et23_ne_et01 : et23 ≠ et01 := by
  decide

@[simp] theorem et23_ne_et12 : et23 ≠ et12 := by
  decide

theorem endpointTouchPath_edge_eq
    (e : endpointTouchPathGraph.edgeSet) :
    e = et01 ∨ e = et12 ∨ e = et23 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 3)) ∧
        ¬ e.1.IsDiag := by
    simpa [endpointTouchPathGraph] using e.2
  rcases h.1 with h01 | h12 | h23
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr <| Or.inl (Subtype.ext h12)
  · exact Or.inr <| Or.inr (Subtype.ext h23)

noncomputable instance endpointTouchPathGraph_edgeSet_fintype :
    Fintype endpointTouchPathGraph.edgeSet :=
  ⟨{et01, et12, et23}, by
    intro e
    rcases endpointTouchPath_edge_eq e with rfl | rfl | rfl <;> simp⟩

abbrev EndpointTouchPathFace := Fin 2

def endpointTouchPathFaces : Finset EndpointTouchPathFace := Finset.univ

def endpointTouchPathFaceBoundary :
    EndpointTouchPathFace → Finset endpointTouchPathGraph.edgeSet
  | ⟨0, _⟩ => {et01, et12}
  | ⟨1, _⟩ => {et12, et23}

theorem totalIncidenceCount_et01 :
    totalIncidenceCount endpointTouchPathFaceBoundary endpointTouchPathFaces et01 = 1 := by
  decide

theorem totalIncidenceCount_et12 :
    totalIncidenceCount endpointTouchPathFaceBoundary endpointTouchPathFaces et12 = 2 := by
  decide

theorem totalIncidenceCount_et23 :
    totalIncidenceCount endpointTouchPathFaceBoundary endpointTouchPathFaces et23 = 1 := by
  decide

def endpointTouchPathEmbedding :
    PlaneEmbeddingWithBoundary endpointTouchPathGraph where
  Face := EndpointTouchPathFace
  faceDecidableEq := inferInstance
  faces := endpointTouchPathFaces
  faceBoundary := endpointTouchPathFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases endpointTouchPath_edge_eq e with rfl | rfl | rfl <;> decide
  edge_one_or_two_faces := by
    intro e _he
    rcases endpointTouchPath_edge_eq e with rfl | rfl | rfl <;> decide

theorem et01_mem_selectedBoundarySupport :
    et01 ∈ selectedBoundarySupport
      endpointTouchPathEmbedding.faceBoundary
      endpointTouchPathEmbedding.faces
      endpointTouchPathEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_et01⟩

theorem et23_mem_selectedBoundarySupport :
    et23 ∈ selectedBoundarySupport
      endpointTouchPathEmbedding.faceBoundary
      endpointTouchPathEmbedding.faces
      endpointTouchPathEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_et23⟩

theorem et12_not_mem_selectedBoundarySupport :
    et12 ∉ selectedBoundarySupport
      endpointTouchPathEmbedding.faceBoundary
      endpointTouchPathEmbedding.faces
      endpointTouchPathEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      endpointTouchPathEmbedding.faceBoundary
      endpointTouchPathEmbedding.faces
      endpointTouchPathEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount endpointTouchPathFaceBoundary endpointTouchPathFaces et12 = 1 := by
    simpa [endpointTouchPathEmbedding] using hcount
  rw [totalIncidenceCount_et12] at hcount'
  norm_num at hcount'

theorem endpointTouchPath_et12_no_boundaryFree_incident_face :
    ∀ f ∈ endpointTouchPathEmbedding.faces,
      et12 ∈ endpointTouchPathEmbedding.faceBoundary f →
        ∃ b ∈ selectedBoundarySupport
            endpointTouchPathEmbedding.faceBoundary
            endpointTouchPathEmbedding.faces
            endpointTouchPathEmbedding.faces,
          b ∈ endpointTouchPathEmbedding.faceBoundary f := by
  intro f _hf _het12
  change EndpointTouchPathFace at f
  change ∃ b ∈ selectedBoundarySupport endpointTouchPathFaceBoundary
      endpointTouchPathFaces endpointTouchPathFaces,
    b ∈ endpointTouchPathFaceBoundary f
  fin_cases f
  · exact ⟨et01, by simpa [endpointTouchPathEmbedding] using et01_mem_selectedBoundarySupport,
      by decide⟩
  · exact ⟨et23, by simpa [endpointTouchPathEmbedding] using et23_mem_selectedBoundarySupport,
      by decide⟩

theorem endpointTouchPath_et12_touches_selectedBoundaryEndpoint :
    ∃ b ∈ selectedBoundarySupport
        endpointTouchPathEmbedding.faceBoundary
        endpointTouchPathEmbedding.faces
        endpointTouchPathEmbedding.faces,
      ∃ v : Fin 4, v ∈ (et12 : Sym2 (Fin 4)) ∧ v ∈ (b : Sym2 (Fin 4)) := by
  exact ⟨et01, et01_mem_selectedBoundarySupport, 1, by decide, by decide⟩

theorem endpointTouchPath_outerBoundaryEdgeSet_induced :
    BoundaryEdgeSetInducedSubgraph
      ({et01} : Finset endpointTouchPathGraph.edgeSet) := by
  intro e hEndpoints
  rcases endpointTouchPath_edge_eq e with rfl | rfl | rfl
  · simp
  · have htwo := hEndpoints (2 : Fin 4) (by decide)
    simp [boundaryEdgeSetEndpointSupport, et01] at htwo
  · have htwo := hEndpoints (2 : Fin 4) (by decide)
    simp [boundaryEdgeSetEndpointSupport, et01] at htwo

theorem endpointTouchPath_innerBoundaryEdgeSet_induced :
    BoundaryEdgeSetInducedSubgraph
      ({et23} : Finset endpointTouchPathGraph.edgeSet) := by
  intro e hEndpoints
  rcases endpointTouchPath_edge_eq e with rfl | rfl | rfl
  · have hone := hEndpoints (1 : Fin 4) (by decide)
    simp [boundaryEdgeSetEndpointSupport, et23] at hone
  · have hone := hEndpoints (1 : Fin 4) (by decide)
    simp [boundaryEdgeSetEndpointSupport, et23] at hone
  · simp

theorem endpointTouchPath_selectedBoundaryEndpoints_of_et12 :
    ∀ v : Fin 4, v ∈ (et12 : Sym2 (Fin 4)) →
      v ∈ boundaryEdgeSetEndpointSupport
        (selectedBoundarySupport endpointTouchPathEmbedding.faceBoundary
          endpointTouchPathEmbedding.faces endpointTouchPathEmbedding.faces) := by
  intro v hv
  fin_cases v
  · simp [et12] at hv
  · exact
      (mem_boundaryEdgeSetEndpointSupport_iff
        (selectedBoundarySupport endpointTouchPathEmbedding.faceBoundary
          endpointTouchPathEmbedding.faces endpointTouchPathEmbedding.faces)).2
        ⟨et01, et01_mem_selectedBoundarySupport, by decide⟩
  · exact
      (mem_boundaryEdgeSetEndpointSupport_iff
        (selectedBoundarySupport endpointTouchPathEmbedding.faceBoundary
          endpointTouchPathEmbedding.faces endpointTouchPathEmbedding.faces)).2
        ⟨et23, et23_mem_selectedBoundarySupport, by decide⟩
  · simp [et12] at hv

theorem not_selectedBoundaryInducedSubgraph_endpointTouchPath :
    ¬ SelectedBoundaryInducedSubgraph endpointTouchPathEmbedding :=
  not_selectedBoundaryInducedSubgraph_of_edge_not_mem_of_endpoint_subset
    et12_not_mem_selectedBoundarySupport
    endpointTouchPath_selectedBoundaryEndpoints_of_et12

theorem not_endpointTouchPath_outer_inner_crossComponentChordFree :
    ¬ BoundaryEdgeSetCrossComponentChordFree
      ({et01} : Finset endpointTouchPathGraph.edgeSet)
      ({et23} : Finset endpointTouchPathGraph.edgeSet) := by
  intro hCross
  have hEndpoints :
      ∀ v : Fin 4, v ∈ (et12 : Sym2 (Fin 4)) →
        v ∈ boundaryEdgeSetEndpointSupport
          (({et01} : Finset endpointTouchPathGraph.edgeSet) ∪ {et23}) := by
    intro v hv
    fin_cases v
    · simp [et12] at hv
    · exact
        (mem_boundaryEdgeSetEndpointSupport_iff
          (({et01} : Finset endpointTouchPathGraph.edgeSet) ∪ {et23})).2
          ⟨et01, by simp, by decide⟩
    · exact
        (mem_boundaryEdgeSetEndpointSupport_iff
          (({et01} : Finset endpointTouchPathGraph.edgeSet) ∪ {et23})).2
          ⟨et23, by simp, by decide⟩
    · simp [et12] at hv
  have hLeft :
      ∃ v : Fin 4, v ∈ (et12 : Sym2 (Fin 4)) ∧
        v ∈ boundaryEdgeSetEndpointSupport
          ({et01} : Finset endpointTouchPathGraph.edgeSet) :=
    ⟨1, by decide,
      (mem_boundaryEdgeSetEndpointSupport_iff
        ({et01} : Finset endpointTouchPathGraph.edgeSet)).2
        ⟨et01, by simp, by decide⟩⟩
  have hRight :
      ∃ v : Fin 4, v ∈ (et12 : Sym2 (Fin 4)) ∧
        v ∈ boundaryEdgeSetEndpointSupport
          ({et23} : Finset endpointTouchPathGraph.edgeSet) :=
    ⟨2, by decide,
      (mem_boundaryEdgeSetEndpointSupport_iff
        ({et23} : Finset endpointTouchPathGraph.edgeSet)).2
        ⟨et23, by simp, by decide⟩⟩
  have het12Union :
      et12 ∈ ({et01} : Finset endpointTouchPathGraph.edgeSet) ∪ {et23} :=
    hCross et12 hEndpoints hLeft hRight
  simp at het12Union

theorem endpointTouchPath_component_induced_not_selectedBoundaryInduced :
    BoundaryEdgeSetInducedSubgraph
        ({et01} : Finset endpointTouchPathGraph.edgeSet) ∧
      BoundaryEdgeSetInducedSubgraph
        ({et23} : Finset endpointTouchPathGraph.edgeSet) ∧
        ¬ SelectedBoundaryInducedSubgraph endpointTouchPathEmbedding :=
  ⟨endpointTouchPath_outerBoundaryEdgeSet_induced,
    endpointTouchPath_innerBoundaryEdgeSet_induced,
    not_selectedBoundaryInducedSubgraph_endpointTouchPath⟩

theorem endpointTouchPath_component_induced_not_crossComponentChordFree :
    BoundaryEdgeSetInducedSubgraph
        ({et01} : Finset endpointTouchPathGraph.edgeSet) ∧
      BoundaryEdgeSetInducedSubgraph
        ({et23} : Finset endpointTouchPathGraph.edgeSet) ∧
        ¬ BoundaryEdgeSetCrossComponentChordFree
          ({et01} : Finset endpointTouchPathGraph.edgeSet)
          ({et23} : Finset endpointTouchPathGraph.edgeSet) :=
  ⟨endpointTouchPath_outerBoundaryEdgeSet_induced,
    endpointTouchPath_innerBoundaryEdgeSet_induced,
    not_endpointTouchPath_outer_inner_crossComponentChordFree⟩

theorem endpointTouchPath_boundaryZero_no_evader_of_vanishes_on_interiorEdge
    (z : endpointTouchPathGraph.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule endpointTouchPathEmbedding)
    (het12 : z et12 = 0) :
    z = 0 := by
  refine eq_zero_of_mem_planarBoundaryZeroSubmodule_of_control_or_boundary
    z hzBoundary ({et12} : Finset endpointTouchPathGraph.edgeSet) ?_ ?_
  · intro e he
    have he12 : e = et12 := by simpa using he
    subst e
    exact het12
  · intro e
    rcases endpointTouchPath_edge_eq e with rfl | rfl | rfl
    · exact Or.inr et01_mem_selectedBoundarySupport
    · exact Or.inl (by simp)
    · exact Or.inr et23_mem_selectedBoundarySupport

theorem endpointTouchPath_boundaryZeroKirchhoff_no_evader_of_vanishes_on_interiorEdge
    (z : endpointTouchPathGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      endpointTouchPathEmbedding ({(1 : Fin 4), (2 : Fin 4)} : Finset (Fin 4)))
    (het12 : z et12 = 0) :
    z = 0 :=
  endpointTouchPath_boundaryZero_no_evader_of_vanishes_on_interiorEdge z
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
      endpointTouchPathEmbedding ({(1 : Fin 4), (2 : Fin 4)} : Finset (Fin 4)) hz)
    het12

theorem endpointTouchPath_interiorEdgeSupport_eq_singleton :
    interiorEdgeSupport endpointTouchPathEmbedding.faceBoundary
        endpointTouchPathEmbedding.faces = {et12} := by
  ext e
  constructor
  · intro he
    rcases endpointTouchPath_edge_eq e with rfl | rfl | rfl
    · have hcount :
          totalIncidenceCount endpointTouchPathEmbedding.faceBoundary
            endpointTouchPathEmbedding.faces et01 = 2 :=
        (mem_interiorEdgeSupport_iff endpointTouchPathEmbedding.faceBoundary
          endpointTouchPathEmbedding.faces).1 he |>.2
      simp [endpointTouchPathEmbedding, totalIncidenceCount_et01] at hcount
    · simp
    · have hcount :
          totalIncidenceCount endpointTouchPathEmbedding.faceBoundary
            endpointTouchPathEmbedding.faces et23 = 2 :=
        (mem_interiorEdgeSupport_iff endpointTouchPathEmbedding.faceBoundary
          endpointTouchPathEmbedding.faces).1 he |>.2
      simp [endpointTouchPathEmbedding, totalIncidenceCount_et23] at hcount
  · intro he
    have he' : e = et12 := by
      simpa using he
    subst e
    rw [mem_interiorEdgeSupport_iff]
    exact ⟨by decide, totalIncidenceCount_et12⟩

theorem selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_endpointTouchPath :
    selectedBoundaryInteriorEdgeEndpointVertices endpointTouchPathEmbedding = ∅ := by
  ext v
  constructor
  · intro hv
    exfalso
    rcases (mem_selectedBoundaryInteriorEdgeEndpointVertices_iff
        endpointTouchPathEmbedding).1 hv with ⟨hvInterior, hAvoids⟩
    rcases hvInterior with ⟨e, heInterior, hve⟩
    have he12 : e = et12 := by
      simpa [endpointTouchPath_interiorEdgeSupport_eq_singleton] using heInterior
    subst e
    fin_cases v
    · simp [et12] at hve
    · exact hAvoids et01 et01_mem_selectedBoundarySupport (by decide)
    · exact hAvoids et23 et23_mem_selectedBoundarySupport (by decide)
    · simp [et12] at hve
  · intro hv
    simp at hv

theorem endpointTouchPath_interiorEdgeSupport_nonempty :
    (interiorEdgeSupport endpointTouchPathEmbedding.faceBoundary
      endpointTouchPathEmbedding.faces).Nonempty := by
  refine ⟨et12, ?_⟩
  rw [endpointTouchPath_interiorEdgeSupport_eq_singleton]
  simp

theorem endpointTouchPath_component_induced_purifiedCarrier_empty :
    BoundaryEdgeSetInducedSubgraph
        ({et01} : Finset endpointTouchPathGraph.edgeSet) ∧
      BoundaryEdgeSetInducedSubgraph
        ({et23} : Finset endpointTouchPathGraph.edgeSet) ∧
        (interiorEdgeSupport endpointTouchPathEmbedding.faceBoundary
          endpointTouchPathEmbedding.faces).Nonempty ∧
          selectedBoundaryInteriorEdgeEndpointVertices endpointTouchPathEmbedding = ∅ :=
  ⟨endpointTouchPath_outerBoundaryEdgeSet_induced,
    endpointTouchPath_innerBoundaryEdgeSet_induced,
    endpointTouchPath_interiorEdgeSupport_nonempty,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_endpointTouchPath⟩

theorem endpointTouchPath_component_induced_not_purifiedCarrier_nonempty :
    BoundaryEdgeSetInducedSubgraph
        ({et01} : Finset endpointTouchPathGraph.edgeSet) ∧
      BoundaryEdgeSetInducedSubgraph
        ({et23} : Finset endpointTouchPathGraph.edgeSet) ∧
        (interiorEdgeSupport endpointTouchPathEmbedding.faceBoundary
          endpointTouchPathEmbedding.faces).Nonempty ∧
          ¬ (selectedBoundaryInteriorEdgeEndpointVertices
            endpointTouchPathEmbedding).Nonempty := by
  refine ⟨endpointTouchPath_outerBoundaryEdgeSet_induced,
    endpointTouchPath_innerBoundaryEdgeSet_induced,
    endpointTouchPath_interiorEdgeSupport_nonempty, ?_⟩
  rw [selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_endpointTouchPath]
  simp

theorem endpointTouchPath_boundaryZero_controlEdges_interiorEdge :
    ∀ ⦃z : endpointTouchPathGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule endpointTouchPathEmbedding →
      (∀ e ∈ ({et12} : Finset endpointTouchPathGraph.edgeSet), z e = 0) →
        z = 0 := by
  intro z hzBoundary hcontrol
  exact endpointTouchPath_boundaryZero_no_evader_of_vanishes_on_interiorEdge
    z hzBoundary (hcontrol et12 (by simp))

theorem endpointTouchPath_boundaryZeroKirchhoff_controlEdges_interiorEdge :
    ∀ ⦃z : endpointTouchPathGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          endpointTouchPathEmbedding ({(1 : Fin 4), (2 : Fin 4)} : Finset (Fin 4)) →
      (∀ e ∈ ({et12} : Finset endpointTouchPathGraph.edgeSet), z e = 0) →
        z = 0 := by
  intro z hz hcontrol
  exact endpointTouchPath_boundaryZeroKirchhoff_no_evader_of_vanishes_on_interiorEdge
    z hz (hcontrol et12 (by simp))

theorem endpointTouchPath_f2_no_evader_emptyCarrier_endpointTouch_obstruction :
    (∀ ⦃z : endpointTouchPathGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule endpointTouchPathEmbedding →
      (∀ e ∈ ({et12} : Finset endpointTouchPathGraph.edgeSet), z e = 0) →
        z = 0) ∧
      (∀ ⦃z : endpointTouchPathGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            endpointTouchPathEmbedding ({(1 : Fin 4), (2 : Fin 4)} : Finset (Fin 4)) →
        (∀ e ∈ ({et12} : Finset endpointTouchPathGraph.edgeSet), z e = 0) →
          z = 0) ∧
        selectedBoundaryInteriorEdgeEndpointVertices endpointTouchPathEmbedding = ∅ ∧
          (∃ b ∈ selectedBoundarySupport
              endpointTouchPathEmbedding.faceBoundary
              endpointTouchPathEmbedding.faces
              endpointTouchPathEmbedding.faces,
            ∃ v : Fin 4, v ∈ (et12 : Sym2 (Fin 4)) ∧ v ∈ (b : Sym2 (Fin 4))) := by
  exact ⟨endpointTouchPath_boundaryZero_controlEdges_interiorEdge,
    endpointTouchPath_boundaryZeroKirchhoff_controlEdges_interiorEdge,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_endpointTouchPath,
    endpointTouchPath_et12_touches_selectedBoundaryEndpoint⟩

/-! ## Cross-component bridge annulus counterexample shell -/

def crossComponentBridgeAnnulusGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 0), s(3, 4), s(4, 5), s(5, 3),
        s(0, 3), s(1, 4), s(2, 5), s(0, 4), s(1, 5), s(2, 3)} :
      Set (Sym2 (Fin 6)))

def ccbO01 : crossComponentBridgeAnnulusGraph.edgeSet := ⟨s(0, 1), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbO12 : crossComponentBridgeAnnulusGraph.edgeSet := ⟨s(1, 2), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbO20 : crossComponentBridgeAnnulusGraph.edgeSet := ⟨s(2, 0), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbI34 : crossComponentBridgeAnnulusGraph.edgeSet := ⟨s(3, 4), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbI45 : crossComponentBridgeAnnulusGraph.edgeSet := ⟨s(4, 5), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbI53 : crossComponentBridgeAnnulusGraph.edgeSet := ⟨s(5, 3), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbR03 : crossComponentBridgeAnnulusGraph.edgeSet := ⟨s(0, 3), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbR14 : crossComponentBridgeAnnulusGraph.edgeSet := ⟨s(1, 4), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbR25 : crossComponentBridgeAnnulusGraph.edgeSet := ⟨s(2, 5), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbD04 : crossComponentBridgeAnnulusGraph.edgeSet := ⟨s(0, 4), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbD15 : crossComponentBridgeAnnulusGraph.edgeSet := ⟨s(1, 5), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbD23 : crossComponentBridgeAnnulusGraph.edgeSet := ⟨s(2, 3), by
  simp [crossComponentBridgeAnnulusGraph]⟩

theorem crossComponentBridgeAnnulus_edge_eq
    (e : crossComponentBridgeAnnulusGraph.edgeSet) :
    e = ccbO01 ∨ e = ccbO12 ∨ e = ccbO20 ∨ e = ccbI34 ∨ e = ccbI45 ∨
      e = ccbI53 ∨ e = ccbR03 ∨ e = ccbR14 ∨ e = ccbR25 ∨ e = ccbD04 ∨
      e = ccbD15 ∨ e = ccbD23 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 0) ∨
          e.1 = s(3, 4) ∨ e.1 = s(4, 5) ∨ e.1 = s(5, 3) ∨
          e.1 = s(0, 3) ∨ e.1 = s(1, 4) ∨ e.1 = s(2, 5) ∨
          e.1 = s(0, 4) ∨ e.1 = s(1, 5) ∨ e.1 = s(2, 3)) ∧
        ¬ e.1.IsDiag := by
    simpa [crossComponentBridgeAnnulusGraph] using e.2
  rcases h.1 with
    hO01 | hO12 | hO20 | hI34 | hI45 | hI53 | hR03 | hR14 | hR25 | hD04 |
    hD15 | hD23
  · exact Or.inl (Subtype.ext hO01)
  · exact Or.inr <| Or.inl (Subtype.ext hO12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext hO20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI34)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hI53)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hR03)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext hR14)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inl (Subtype.ext hR25)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hD04)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hD15)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext hD23)

noncomputable instance crossComponentBridgeAnnulusGraph_edgeSet_fintype :
    Fintype crossComponentBridgeAnnulusGraph.edgeSet :=
  ⟨{ccbO01, ccbO12, ccbO20, ccbI34, ccbI45, ccbI53, ccbR03, ccbR14,
      ccbR25, ccbD04, ccbD15, ccbD23}, by
    intro e
    rcases crossComponentBridgeAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp⟩

def crossComponentBridgeAnnulusOuterBoundarySet :
    Finset crossComponentBridgeAnnulusGraph.edgeSet :=
  {ccbO01, ccbO12, ccbO20}

def crossComponentBridgeAnnulusInnerBoundarySet :
    Finset crossComponentBridgeAnnulusGraph.edgeSet :=
  {ccbI34, ccbI45, ccbI53}

def crossComponentBridgeAnnulusInteriorEdges :
    Finset crossComponentBridgeAnnulusGraph.edgeSet :=
  {ccbR03, ccbR14, ccbR25, ccbD04, ccbD15, ccbD23}

abbrev CrossComponentBridgeAnnulusFace := Fin 6

def crossComponentBridgeAnnulusFaces :
    Finset CrossComponentBridgeAnnulusFace := Finset.univ

def crossComponentBridgeAnnulusFaceBoundary :
    CrossComponentBridgeAnnulusFace → Finset crossComponentBridgeAnnulusGraph.edgeSet
  | ⟨0, _⟩ => {ccbO01, ccbR14, ccbD04}
  | ⟨1, _⟩ => {ccbI34, ccbD04, ccbR03}
  | ⟨2, _⟩ => {ccbO12, ccbR25, ccbD15}
  | ⟨3, _⟩ => {ccbI45, ccbD15, ccbR14}
  | ⟨4, _⟩ => {ccbO20, ccbR03, ccbD23}
  | ⟨5, _⟩ => {ccbI53, ccbD23, ccbR25}

theorem totalIncidenceCount_ccbO01 :
    totalIncidenceCount crossComponentBridgeAnnulusFaceBoundary
      crossComponentBridgeAnnulusFaces ccbO01 = 1 := by
  decide

theorem totalIncidenceCount_ccbO12 :
    totalIncidenceCount crossComponentBridgeAnnulusFaceBoundary
      crossComponentBridgeAnnulusFaces ccbO12 = 1 := by
  decide

theorem totalIncidenceCount_ccbO20 :
    totalIncidenceCount crossComponentBridgeAnnulusFaceBoundary
      crossComponentBridgeAnnulusFaces ccbO20 = 1 := by
  decide

theorem totalIncidenceCount_ccbI34 :
    totalIncidenceCount crossComponentBridgeAnnulusFaceBoundary
      crossComponentBridgeAnnulusFaces ccbI34 = 1 := by
  decide

theorem totalIncidenceCount_ccbI45 :
    totalIncidenceCount crossComponentBridgeAnnulusFaceBoundary
      crossComponentBridgeAnnulusFaces ccbI45 = 1 := by
  decide

theorem totalIncidenceCount_ccbI53 :
    totalIncidenceCount crossComponentBridgeAnnulusFaceBoundary
      crossComponentBridgeAnnulusFaces ccbI53 = 1 := by
  decide

theorem totalIncidenceCount_ccbR03 :
    totalIncidenceCount crossComponentBridgeAnnulusFaceBoundary
      crossComponentBridgeAnnulusFaces ccbR03 = 2 := by
  decide

theorem totalIncidenceCount_ccbR14 :
    totalIncidenceCount crossComponentBridgeAnnulusFaceBoundary
      crossComponentBridgeAnnulusFaces ccbR14 = 2 := by
  decide

theorem totalIncidenceCount_ccbR25 :
    totalIncidenceCount crossComponentBridgeAnnulusFaceBoundary
      crossComponentBridgeAnnulusFaces ccbR25 = 2 := by
  decide

theorem totalIncidenceCount_ccbD04 :
    totalIncidenceCount crossComponentBridgeAnnulusFaceBoundary
      crossComponentBridgeAnnulusFaces ccbD04 = 2 := by
  decide

theorem totalIncidenceCount_ccbD15 :
    totalIncidenceCount crossComponentBridgeAnnulusFaceBoundary
      crossComponentBridgeAnnulusFaces ccbD15 = 2 := by
  decide

theorem totalIncidenceCount_ccbD23 :
    totalIncidenceCount crossComponentBridgeAnnulusFaceBoundary
      crossComponentBridgeAnnulusFaces ccbD23 = 2 := by
  decide

def crossComponentBridgeAnnulusEmbedding :
    PlaneEmbeddingWithBoundary crossComponentBridgeAnnulusGraph where
  Face := CrossComponentBridgeAnnulusFace
  faceDecidableEq := inferInstance
  faces := crossComponentBridgeAnnulusFaces
  faceBoundary := crossComponentBridgeAnnulusFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases crossComponentBridgeAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases crossComponentBridgeAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

theorem ccbO01_mem_selectedBoundarySupport :
    ccbO01 ∈ selectedBoundarySupport
      crossComponentBridgeAnnulusEmbedding.faceBoundary
      crossComponentBridgeAnnulusEmbedding.faces
      crossComponentBridgeAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_ccbO01⟩

theorem ccbO12_mem_selectedBoundarySupport :
    ccbO12 ∈ selectedBoundarySupport
      crossComponentBridgeAnnulusEmbedding.faceBoundary
      crossComponentBridgeAnnulusEmbedding.faces
      crossComponentBridgeAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_ccbO12⟩

theorem ccbO20_mem_selectedBoundarySupport :
    ccbO20 ∈ selectedBoundarySupport
      crossComponentBridgeAnnulusEmbedding.faceBoundary
      crossComponentBridgeAnnulusEmbedding.faces
      crossComponentBridgeAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_ccbO20⟩

theorem ccbI34_mem_selectedBoundarySupport :
    ccbI34 ∈ selectedBoundarySupport
      crossComponentBridgeAnnulusEmbedding.faceBoundary
      crossComponentBridgeAnnulusEmbedding.faces
      crossComponentBridgeAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_ccbI34⟩

theorem ccbI45_mem_selectedBoundarySupport :
    ccbI45 ∈ selectedBoundarySupport
      crossComponentBridgeAnnulusEmbedding.faceBoundary
      crossComponentBridgeAnnulusEmbedding.faces
      crossComponentBridgeAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_ccbI45⟩

theorem ccbI53_mem_selectedBoundarySupport :
    ccbI53 ∈ selectedBoundarySupport
      crossComponentBridgeAnnulusEmbedding.faceBoundary
      crossComponentBridgeAnnulusEmbedding.faces
      crossComponentBridgeAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_ccbI53⟩

theorem ccbR03_not_mem_selectedBoundarySupport :
    ccbR03 ∉ selectedBoundarySupport
      crossComponentBridgeAnnulusEmbedding.faceBoundary
      crossComponentBridgeAnnulusEmbedding.faces
      crossComponentBridgeAnnulusEmbedding.faces := by
  decide

theorem crossComponentBridgeAnnulus_selectedBoundarySupport_eq :
    selectedBoundarySupport
        crossComponentBridgeAnnulusEmbedding.faceBoundary
        crossComponentBridgeAnnulusEmbedding.faces
        crossComponentBridgeAnnulusEmbedding.faces =
      crossComponentBridgeAnnulusOuterBoundarySet ∪
        crossComponentBridgeAnnulusInnerBoundarySet := by
  ext e
  rcases crossComponentBridgeAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem crossComponentBridgeAnnulus_interiorEdgeSupport_eq :
    interiorEdgeSupport
        crossComponentBridgeAnnulusEmbedding.faceBoundary
        crossComponentBridgeAnnulusEmbedding.faces =
      crossComponentBridgeAnnulusInteriorEdges := by
  ext e
  rcases crossComponentBridgeAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem crossComponentBridgeAnnulus_outerBoundaryEdgeSet_induced :
    BoundaryEdgeSetInducedSubgraph
      crossComponentBridgeAnnulusOuterBoundarySet := by
  intro e hEndpoints
  rcases crossComponentBridgeAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [crossComponentBridgeAnnulusOuterBoundarySet]
  · simp [crossComponentBridgeAnnulusOuterBoundarySet]
  · simp [crossComponentBridgeAnnulusOuterBoundarySet]
  · exfalso
    have hbad := hEndpoints (3 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusOuterBoundarySet, ccbO01, ccbO12, ccbO20] at hbad
  · exfalso
    have hbad := hEndpoints (4 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusOuterBoundarySet, ccbO01, ccbO12, ccbO20] at hbad
  · exfalso
    have hbad := hEndpoints (3 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusOuterBoundarySet, ccbO01, ccbO12, ccbO20] at hbad
  · exfalso
    have hbad := hEndpoints (3 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusOuterBoundarySet, ccbO01, ccbO12, ccbO20] at hbad
  · exfalso
    have hbad := hEndpoints (4 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusOuterBoundarySet, ccbO01, ccbO12, ccbO20] at hbad
  · exfalso
    have hbad := hEndpoints (5 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusOuterBoundarySet, ccbO01, ccbO12, ccbO20] at hbad
  · exfalso
    have hbad := hEndpoints (4 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusOuterBoundarySet, ccbO01, ccbO12, ccbO20] at hbad
  · exfalso
    have hbad := hEndpoints (5 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusOuterBoundarySet, ccbO01, ccbO12, ccbO20] at hbad
  · exfalso
    have hbad := hEndpoints (3 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusOuterBoundarySet, ccbO01, ccbO12, ccbO20] at hbad

theorem crossComponentBridgeAnnulus_innerBoundaryEdgeSet_induced :
    BoundaryEdgeSetInducedSubgraph
      crossComponentBridgeAnnulusInnerBoundarySet := by
  intro e hEndpoints
  rcases crossComponentBridgeAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    have hbad := hEndpoints (0 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusInnerBoundarySet, ccbI34, ccbI45, ccbI53] at hbad
  · exfalso
    have hbad := hEndpoints (1 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusInnerBoundarySet, ccbI34, ccbI45, ccbI53] at hbad
  · exfalso
    have hbad := hEndpoints (0 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusInnerBoundarySet, ccbI34, ccbI45, ccbI53] at hbad
  · simp [crossComponentBridgeAnnulusInnerBoundarySet]
  · simp [crossComponentBridgeAnnulusInnerBoundarySet]
  · simp [crossComponentBridgeAnnulusInnerBoundarySet]
  · exfalso
    have hbad := hEndpoints (0 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusInnerBoundarySet, ccbI34, ccbI45, ccbI53] at hbad
  · exfalso
    have hbad := hEndpoints (1 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusInnerBoundarySet, ccbI34, ccbI45, ccbI53] at hbad
  · exfalso
    have hbad := hEndpoints (2 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusInnerBoundarySet, ccbI34, ccbI45, ccbI53] at hbad
  · exfalso
    have hbad := hEndpoints (0 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusInnerBoundarySet, ccbI34, ccbI45, ccbI53] at hbad
  · exfalso
    have hbad := hEndpoints (1 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusInnerBoundarySet, ccbI34, ccbI45, ccbI53] at hbad
  · exfalso
    have hbad := hEndpoints (2 : Fin 6) (by decide)
    simp [boundaryEdgeSetEndpointSupport,
      crossComponentBridgeAnnulusInnerBoundarySet, ccbI34, ccbI45, ccbI53] at hbad

theorem crossComponentBridgeAnnulus_selectedBoundaryEndpoints_of_ccbR03 :
    ∀ v : Fin 6, v ∈ (ccbR03 : Sym2 (Fin 6)) →
      v ∈ boundaryEdgeSetEndpointSupport
        (selectedBoundarySupport crossComponentBridgeAnnulusEmbedding.faceBoundary
          crossComponentBridgeAnnulusEmbedding.faces
          crossComponentBridgeAnnulusEmbedding.faces) := by
  intro v hv
  fin_cases v
  · exact
      (mem_boundaryEdgeSetEndpointSupport_iff
        (selectedBoundarySupport crossComponentBridgeAnnulusEmbedding.faceBoundary
          crossComponentBridgeAnnulusEmbedding.faces
          crossComponentBridgeAnnulusEmbedding.faces)).2
        ⟨ccbO01, ccbO01_mem_selectedBoundarySupport, by decide⟩
  · simp [ccbR03] at hv
  · simp [ccbR03] at hv
  · exact
      (mem_boundaryEdgeSetEndpointSupport_iff
        (selectedBoundarySupport crossComponentBridgeAnnulusEmbedding.faceBoundary
          crossComponentBridgeAnnulusEmbedding.faces
          crossComponentBridgeAnnulusEmbedding.faces)).2
        ⟨ccbI34, ccbI34_mem_selectedBoundarySupport, by decide⟩
  · simp [ccbR03] at hv
  · simp [ccbR03] at hv

theorem not_selectedBoundaryInducedSubgraph_crossComponentBridgeAnnulus :
    ¬ SelectedBoundaryInducedSubgraph crossComponentBridgeAnnulusEmbedding :=
  not_selectedBoundaryInducedSubgraph_of_edge_not_mem_of_endpoint_subset
    ccbR03_not_mem_selectedBoundarySupport
    crossComponentBridgeAnnulus_selectedBoundaryEndpoints_of_ccbR03

theorem not_crossComponentBridgeAnnulus_outer_inner_crossComponentChordFree :
    ¬ BoundaryEdgeSetCrossComponentChordFree
      crossComponentBridgeAnnulusOuterBoundarySet
      crossComponentBridgeAnnulusInnerBoundarySet := by
  intro hCross
  have hEndpoints :
      ∀ v : Fin 6, v ∈ (ccbR03 : Sym2 (Fin 6)) →
        v ∈ boundaryEdgeSetEndpointSupport
          (crossComponentBridgeAnnulusOuterBoundarySet ∪
            crossComponentBridgeAnnulusInnerBoundarySet) := by
    intro v hv
    fin_cases v
    · exact
        (mem_boundaryEdgeSetEndpointSupport_iff
          (crossComponentBridgeAnnulusOuterBoundarySet ∪
            crossComponentBridgeAnnulusInnerBoundarySet)).2
          ⟨ccbO01, by simp [crossComponentBridgeAnnulusOuterBoundarySet,
            crossComponentBridgeAnnulusInnerBoundarySet], by decide⟩
    · simp [ccbR03] at hv
    · simp [ccbR03] at hv
    · exact
        (mem_boundaryEdgeSetEndpointSupport_iff
          (crossComponentBridgeAnnulusOuterBoundarySet ∪
            crossComponentBridgeAnnulusInnerBoundarySet)).2
          ⟨ccbI34, by simp [crossComponentBridgeAnnulusOuterBoundarySet,
            crossComponentBridgeAnnulusInnerBoundarySet], by decide⟩
    · simp [ccbR03] at hv
    · simp [ccbR03] at hv
  have hLeft :
      ∃ v : Fin 6, v ∈ (ccbR03 : Sym2 (Fin 6)) ∧
        v ∈ boundaryEdgeSetEndpointSupport
          crossComponentBridgeAnnulusOuterBoundarySet :=
    ⟨0, by decide,
      (mem_boundaryEdgeSetEndpointSupport_iff
        crossComponentBridgeAnnulusOuterBoundarySet).2
        ⟨ccbO01, by simp [crossComponentBridgeAnnulusOuterBoundarySet],
          by decide⟩⟩
  have hRight :
      ∃ v : Fin 6, v ∈ (ccbR03 : Sym2 (Fin 6)) ∧
        v ∈ boundaryEdgeSetEndpointSupport
          crossComponentBridgeAnnulusInnerBoundarySet :=
    ⟨3, by decide,
      (mem_boundaryEdgeSetEndpointSupport_iff
        crossComponentBridgeAnnulusInnerBoundarySet).2
        ⟨ccbI34, by simp [crossComponentBridgeAnnulusInnerBoundarySet],
          by decide⟩⟩
  have hR03Union :
      ccbR03 ∈ crossComponentBridgeAnnulusOuterBoundarySet ∪
        crossComponentBridgeAnnulusInnerBoundarySet :=
    hCross ccbR03 hEndpoints hLeft hRight
  have hR03NotUnion :
      ccbR03 ∉ crossComponentBridgeAnnulusOuterBoundarySet ∪
        crossComponentBridgeAnnulusInnerBoundarySet := by
    decide
  exact hR03NotUnion hR03Union

theorem crossComponentBridgeAnnulus_component_induced_not_crossComponentChordFree :
    BoundaryEdgeSetInducedSubgraph
        crossComponentBridgeAnnulusOuterBoundarySet ∧
      BoundaryEdgeSetInducedSubgraph
        crossComponentBridgeAnnulusInnerBoundarySet ∧
        ¬ BoundaryEdgeSetCrossComponentChordFree
          crossComponentBridgeAnnulusOuterBoundarySet
          crossComponentBridgeAnnulusInnerBoundarySet :=
  ⟨crossComponentBridgeAnnulus_outerBoundaryEdgeSet_induced,
    crossComponentBridgeAnnulus_innerBoundaryEdgeSet_induced,
    not_crossComponentBridgeAnnulus_outer_inner_crossComponentChordFree⟩

theorem crossComponentBridgeAnnulus_component_induced_not_selectedBoundaryInduced :
    BoundaryEdgeSetInducedSubgraph
        crossComponentBridgeAnnulusOuterBoundarySet ∧
      BoundaryEdgeSetInducedSubgraph
        crossComponentBridgeAnnulusInnerBoundarySet ∧
        selectedBoundarySupport
          crossComponentBridgeAnnulusEmbedding.faceBoundary
          crossComponentBridgeAnnulusEmbedding.faces
          crossComponentBridgeAnnulusEmbedding.faces =
            crossComponentBridgeAnnulusOuterBoundarySet ∪
              crossComponentBridgeAnnulusInnerBoundarySet ∧
          ¬ SelectedBoundaryInducedSubgraph crossComponentBridgeAnnulusEmbedding :=
  ⟨crossComponentBridgeAnnulus_outerBoundaryEdgeSet_induced,
    crossComponentBridgeAnnulus_innerBoundaryEdgeSet_induced,
    crossComponentBridgeAnnulus_selectedBoundarySupport_eq,
    not_selectedBoundaryInducedSubgraph_crossComponentBridgeAnnulus⟩

theorem ccbR03_mem_interiorEdgeSupport :
    ccbR03 ∈ interiorEdgeSupport
      crossComponentBridgeAnnulusEmbedding.faceBoundary
      crossComponentBridgeAnnulusEmbedding.faces := by
  rw [crossComponentBridgeAnnulus_interiorEdgeSupport_eq]
  simp [crossComponentBridgeAnnulusInteriorEdges]

theorem crossComponentBridgeAnnulus_vertex_incident_selectedBoundarySupport
    (v : Fin 6) :
    ∃ b ∈ selectedBoundarySupport
        crossComponentBridgeAnnulusEmbedding.faceBoundary
        crossComponentBridgeAnnulusEmbedding.faces
        crossComponentBridgeAnnulusEmbedding.faces,
      v ∈ (b : Sym2 (Fin 6)) := by
  fin_cases v
  · exact ⟨ccbO01, ccbO01_mem_selectedBoundarySupport, by decide⟩
  · exact ⟨ccbO01, ccbO01_mem_selectedBoundarySupport, by decide⟩
  · exact ⟨ccbO12, ccbO12_mem_selectedBoundarySupport, by decide⟩
  · exact ⟨ccbI34, ccbI34_mem_selectedBoundarySupport, by decide⟩
  · exact ⟨ccbI34, ccbI34_mem_selectedBoundarySupport, by decide⟩
  · exact ⟨ccbI45, ccbI45_mem_selectedBoundarySupport, by decide⟩

theorem selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_crossComponentBridgeAnnulus :
    selectedBoundaryInteriorEdgeEndpointVertices crossComponentBridgeAnnulusEmbedding = ∅ := by
  ext v
  constructor
  · intro hv
    exfalso
    rcases (mem_selectedBoundaryInteriorEdgeEndpointVertices_iff
        crossComponentBridgeAnnulusEmbedding).1 hv with ⟨_hvInterior, hAvoid⟩
    rcases crossComponentBridgeAnnulus_vertex_incident_selectedBoundarySupport v with
      ⟨b, hbBoundary, hvb⟩
    exact hAvoid b hbBoundary hvb
  · intro hv
    simp at hv

theorem not_interiorEdgesNotSelectedBoundaryChords_crossComponentBridgeAnnulus :
    ¬ InteriorEdgesNotSelectedBoundaryChords crossComponentBridgeAnnulusEmbedding := by
  intro hChordFree
  rcases hChordFree ccbR03 ccbR03_mem_interiorEdgeSupport with
    ⟨v, hvR03, hAvoid⟩
  fin_cases v
  · exact hAvoid ccbO01 ccbO01_mem_selectedBoundarySupport (by decide)
  · simp [ccbR03] at hvR03
  · simp [ccbR03] at hvR03
  · exact hAvoid ccbI34 ccbI34_mem_selectedBoundarySupport (by decide)
  · simp [ccbR03] at hvR03
  · simp [ccbR03] at hvR03

def ccbDart01 : crossComponentBridgeAnnulusGraph.Dart := ⟨((0 : Fin 6), 1), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbDart12 : crossComponentBridgeAnnulusGraph.Dart := ⟨((1 : Fin 6), 2), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbDart20 : crossComponentBridgeAnnulusGraph.Dart := ⟨((2 : Fin 6), 0), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbDart34 : crossComponentBridgeAnnulusGraph.Dart := ⟨((3 : Fin 6), 4), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbDart45 : crossComponentBridgeAnnulusGraph.Dart := ⟨((4 : Fin 6), 5), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbDart53 : crossComponentBridgeAnnulusGraph.Dart := ⟨((5 : Fin 6), 3), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbDart03 : crossComponentBridgeAnnulusGraph.Dart := ⟨((0 : Fin 6), 3), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbDart14 : crossComponentBridgeAnnulusGraph.Dart := ⟨((1 : Fin 6), 4), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbDart25 : crossComponentBridgeAnnulusGraph.Dart := ⟨((2 : Fin 6), 5), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbDart40 : crossComponentBridgeAnnulusGraph.Dart := ⟨((4 : Fin 6), 0), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbDart51 : crossComponentBridgeAnnulusGraph.Dart := ⟨((5 : Fin 6), 1), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def ccbDart32 : crossComponentBridgeAnnulusGraph.Dart := ⟨((3 : Fin 6), 2), by
  simp [crossComponentBridgeAnnulusGraph]⟩

def crossComponentBridgeAnnulusFace0PureDartCycle
    (hf : (0 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      crossComponentBridgeAnnulusEmbedding ⟨(0 : CrossComponentBridgeAnnulusFace), hf⟩ where
  darts := [ccbDart01, ccbDart14, ccbDart40]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, ccbDart01, ccbDart14, ccbDart40]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary,
        ccbO01, ccbR14, ccbD04, ccbDart01, ccbDart14, ccbDart40]
  hface_sub := by
    intro e he
    have he' : e = ccbO01 ∨ e = ccbR14 ∨ e = ccbD04 := by
      simpa [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary]
        using he
    rcases he' with rfl | rfl | rfl <;>
      simp [ccbO01, ccbR14, ccbD04, ccbDart01, ccbDart14, ccbDart40]

def crossComponentBridgeAnnulusFace1PureDartCycle
    (hf : (1 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      crossComponentBridgeAnnulusEmbedding ⟨(1 : CrossComponentBridgeAnnulusFace), hf⟩ where
  darts := [ccbDart34, ccbDart40, ccbDart03]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, ccbDart34, ccbDart40, ccbDart03]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary,
        ccbI34, ccbD04, ccbR03, ccbDart34, ccbDart40, ccbDart03]
  hface_sub := by
    intro e he
    have he' : e = ccbI34 ∨ e = ccbD04 ∨ e = ccbR03 := by
      simpa [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary]
        using he
    rcases he' with rfl | rfl | rfl <;>
      simp [ccbI34, ccbD04, ccbR03, ccbDart34, ccbDart40, ccbDart03]

def crossComponentBridgeAnnulusFace2PureDartCycle
    (hf : (2 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      crossComponentBridgeAnnulusEmbedding ⟨(2 : CrossComponentBridgeAnnulusFace), hf⟩ where
  darts := [ccbDart12, ccbDart25, ccbDart51]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, ccbDart12, ccbDart25, ccbDart51]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary,
        ccbO12, ccbR25, ccbD15, ccbDart12, ccbDart25, ccbDart51]
  hface_sub := by
    intro e he
    have he' : e = ccbO12 ∨ e = ccbR25 ∨ e = ccbD15 := by
      simpa [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary]
        using he
    rcases he' with rfl | rfl | rfl <;>
      simp [ccbO12, ccbR25, ccbD15, ccbDart12, ccbDart25, ccbDart51]

def crossComponentBridgeAnnulusFace3PureDartCycle
    (hf : (3 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      crossComponentBridgeAnnulusEmbedding ⟨(3 : CrossComponentBridgeAnnulusFace), hf⟩ where
  darts := [ccbDart45, ccbDart51, ccbDart14]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, ccbDart45, ccbDart51, ccbDart14]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary,
        ccbI45, ccbD15, ccbR14, ccbDart45, ccbDart51, ccbDart14]
  hface_sub := by
    intro e he
    have he' : e = ccbI45 ∨ e = ccbD15 ∨ e = ccbR14 := by
      simpa [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary]
        using he
    rcases he' with rfl | rfl | rfl <;>
      simp [ccbI45, ccbD15, ccbR14, ccbDart45, ccbDart51, ccbDart14]

def crossComponentBridgeAnnulusFace4PureDartCycle
    (hf : (4 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      crossComponentBridgeAnnulusEmbedding ⟨(4 : CrossComponentBridgeAnnulusFace), hf⟩ where
  darts := [ccbDart20, ccbDart03, ccbDart32]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, ccbDart20, ccbDart03, ccbDart32]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary,
        ccbO20, ccbR03, ccbD23, ccbDart20, ccbDart03, ccbDart32]
  hface_sub := by
    intro e he
    have he' : e = ccbO20 ∨ e = ccbR03 ∨ e = ccbD23 := by
      simpa [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary]
        using he
    rcases he' with rfl | rfl | rfl <;>
      simp [ccbO20, ccbR03, ccbD23, ccbDart20, ccbDart03, ccbDart32]

def crossComponentBridgeAnnulusFace5PureDartCycle
    (hf : (5 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      crossComponentBridgeAnnulusEmbedding ⟨(5 : CrossComponentBridgeAnnulusFace), hf⟩ where
  darts := [ccbDart53, ccbDart32, ccbDart25]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, ccbDart53, ccbDart32, ccbDart25]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary,
        ccbI53, ccbD23, ccbR25, ccbDart53, ccbDart32, ccbDart25]
  hface_sub := by
    intro e he
    have he' : e = ccbI53 ∨ e = ccbD23 ∨ e = ccbR25 := by
      simpa [crossComponentBridgeAnnulusEmbedding, crossComponentBridgeAnnulusFaceBoundary]
        using he
    rcases he' with rfl | rfl | rfl <;>
      simp [ccbI53, ccbD23, ccbR25, ccbDart53, ccbDart32, ccbDart25]

def crossComponentBridgeAnnulusPureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry
      crossComponentBridgeAnnulusEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change CrossComponentBridgeAnnulusFace at f
    by_cases h0 : f = (0 : CrossComponentBridgeAnnulusFace)
    · subst f
      exact crossComponentBridgeAnnulusFace0PureDartCycle hfmem
    · by_cases h1 : f = (1 : CrossComponentBridgeAnnulusFace)
      · subst f
        exact crossComponentBridgeAnnulusFace1PureDartCycle hfmem
      · by_cases h2 : f = (2 : CrossComponentBridgeAnnulusFace)
        · subst f
          exact crossComponentBridgeAnnulusFace2PureDartCycle hfmem
        · by_cases h3 : f = (3 : CrossComponentBridgeAnnulusFace)
          · subst f
            exact crossComponentBridgeAnnulusFace3PureDartCycle hfmem
          · by_cases h4 : f = (4 : CrossComponentBridgeAnnulusFace)
            · subst f
              exact crossComponentBridgeAnnulusFace4PureDartCycle hfmem
            · have h5 : f = (5 : CrossComponentBridgeAnnulusFace) := by
                fin_cases f <;> first | rfl | contradiction
              subst f
              exact crossComponentBridgeAnnulusFace5PureDartCycle hfmem

def crossComponentBridgeAnnulusClosedWalkEmbeddingData :
    PlanarBoundaryClosedWalkEmbeddingData crossComponentBridgeAnnulusEmbedding :=
  crossComponentBridgeAnnulusPureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

theorem crossComponentBridgeAnnulusFace_cases
    (f : AmbientFace crossComponentBridgeAnnulusEmbedding.faces) :
    f = ⟨(0 : CrossComponentBridgeAnnulusFace), by
      change (0 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusFaces
      exact Finset.mem_univ _⟩ ∨
      f = ⟨(1 : CrossComponentBridgeAnnulusFace), by
        change (1 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusFaces
        exact Finset.mem_univ _⟩ ∨
      f = ⟨(2 : CrossComponentBridgeAnnulusFace), by
        change (2 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusFaces
        exact Finset.mem_univ _⟩ ∨
      f = ⟨(3 : CrossComponentBridgeAnnulusFace), by
        change (3 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusFaces
        exact Finset.mem_univ _⟩ ∨
      f = ⟨(4 : CrossComponentBridgeAnnulusFace), by
        change (4 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusFaces
        exact Finset.mem_univ _⟩ ∨
        f = ⟨(5 : CrossComponentBridgeAnnulusFace), by
          change (5 : CrossComponentBridgeAnnulusFace) ∈ crossComponentBridgeAnnulusFaces
          exact Finset.mem_univ _⟩ := by
  rcases f with ⟨f, hfmem⟩
  change CrossComponentBridgeAnnulusFace at f
  fin_cases f
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext rfl)

theorem crossComponentBridgeAnnulusClosedWalkEmbeddingData_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace crossComponentBridgeAnnulusEmbedding.faces,
      (crossComponentBridgeAnnulusClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f := by
  intro f
  rcases crossComponentBridgeAnnulusFace_cases f with
    rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨[ccbO01], ?_, ?_⟩
    · decide
    · intro e
      rcases crossComponentBridgeAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · refine ⟨[ccbI34], ?_, ?_⟩
    · decide
    · intro e
      rcases crossComponentBridgeAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · refine ⟨[ccbO12], ?_, ?_⟩
    · decide
    · intro e
      rcases crossComponentBridgeAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · refine ⟨[ccbI45], ?_, ?_⟩
    · decide
    · intro e
      rcases crossComponentBridgeAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · refine ⟨[ccbO20], ?_, ?_⟩
    · decide
    · intro e
      rcases crossComponentBridgeAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · refine ⟨[ccbI53], ?_, ?_⟩
    · decide
    · intro e
      rcases crossComponentBridgeAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide

def crossComponentBridgeAnnulusOuterRoot :
    PlanarBoundaryEdgeVertex crossComponentBridgeAnnulusEmbedding :=
  ⟨ccbO01, ccbO01_mem_selectedBoundarySupport⟩

def crossComponentBridgeAnnulusInnerRoot :
    PlanarBoundaryEdgeVertex crossComponentBridgeAnnulusEmbedding :=
  ⟨ccbI34, ccbI34_mem_selectedBoundarySupport⟩

def crossComponentBridgeAnnulusBoundaryLabel
    (e : PlanarBoundaryEdgeVertex crossComponentBridgeAnnulusEmbedding) : Bool :=
  if e.1 = ccbI34 ∨ e.1 = ccbI45 ∨ e.1 = ccbI53 then true else false

theorem crossComponentBridgeAnnulus_boundaryEdge_eq
    (e : PlanarBoundaryEdgeVertex crossComponentBridgeAnnulusEmbedding) :
    e = ⟨ccbO01, ccbO01_mem_selectedBoundarySupport⟩ ∨
      e = ⟨ccbO12, ccbO12_mem_selectedBoundarySupport⟩ ∨
      e = ⟨ccbO20, ccbO20_mem_selectedBoundarySupport⟩ ∨
      e = ⟨ccbI34, ccbI34_mem_selectedBoundarySupport⟩ ∨
      e = ⟨ccbI45, ccbI45_mem_selectedBoundarySupport⟩ ∨
        e = ⟨ccbI53, ccbI53_mem_selectedBoundarySupport⟩ := by
  rcases crossComponentBridgeAnnulus_edge_eq e.1 with
    hO01 | hO12 | hO20 | hI34 | hI45 | hI53 | hR03 | hR14 | hR25 | hD04 |
    hD15 | hD23
  · exact Or.inl (Subtype.ext hO01)
  · exact Or.inr <| Or.inl (Subtype.ext hO12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext hO20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI34)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext hI53)
  · exact False.elim (by
      have hnot :
          ccbR03 ∉ selectedBoundarySupport
            crossComponentBridgeAnnulusEmbedding.faceBoundary
            crossComponentBridgeAnnulusEmbedding.faces
            crossComponentBridgeAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hR03] using e.2))
  · exact False.elim (by
      have hnot :
          ccbR14 ∉ selectedBoundarySupport
            crossComponentBridgeAnnulusEmbedding.faceBoundary
            crossComponentBridgeAnnulusEmbedding.faces
            crossComponentBridgeAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hR14] using e.2))
  · exact False.elim (by
      have hnot :
          ccbR25 ∉ selectedBoundarySupport
            crossComponentBridgeAnnulusEmbedding.faceBoundary
            crossComponentBridgeAnnulusEmbedding.faces
            crossComponentBridgeAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hR25] using e.2))
  · exact False.elim (by
      have hnot :
          ccbD04 ∉ selectedBoundarySupport
            crossComponentBridgeAnnulusEmbedding.faceBoundary
            crossComponentBridgeAnnulusEmbedding.faces
            crossComponentBridgeAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hD04] using e.2))
  · exact False.elim (by
      have hnot :
          ccbD15 ∉ selectedBoundarySupport
            crossComponentBridgeAnnulusEmbedding.faceBoundary
            crossComponentBridgeAnnulusEmbedding.faces
            crossComponentBridgeAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hD15] using e.2))
  · exact False.elim (by
      have hnot :
          ccbD23 ∉ selectedBoundarySupport
            crossComponentBridgeAnnulusEmbedding.faceBoundary
            crossComponentBridgeAnnulusEmbedding.faces
            crossComponentBridgeAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hD23] using e.2))

theorem crossComponentBridgeAnnulusBoundaryAdj_ccbO01_ccbO12 :
    (planarBoundarySupportEndpointAdjGraph crossComponentBridgeAnnulusEmbedding).Adj
      ⟨ccbO01, ccbO01_mem_selectedBoundarySupport⟩
      ⟨ccbO12, ccbO12_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 1, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [ccbO01, ccbO12] at this
  · simp [ccbO01]
  · simp [ccbO12]

theorem crossComponentBridgeAnnulusBoundaryAdj_ccbO12_ccbO20 :
    (planarBoundarySupportEndpointAdjGraph crossComponentBridgeAnnulusEmbedding).Adj
      ⟨ccbO12, ccbO12_mem_selectedBoundarySupport⟩
      ⟨ccbO20, ccbO20_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 2, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [ccbO12, ccbO20] at this
  · simp [ccbO12]
  · simp [ccbO20]

theorem crossComponentBridgeAnnulusBoundaryAdj_ccbO20_ccbO01 :
    (planarBoundarySupportEndpointAdjGraph crossComponentBridgeAnnulusEmbedding).Adj
      ⟨ccbO20, ccbO20_mem_selectedBoundarySupport⟩
      ⟨ccbO01, ccbO01_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 0, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [ccbO20, ccbO01] at this
  · simp [ccbO20]
  · simp [ccbO01]

theorem crossComponentBridgeAnnulusBoundaryAdj_ccbO12_ccbO01 :
    (planarBoundarySupportEndpointAdjGraph crossComponentBridgeAnnulusEmbedding).Adj
      ⟨ccbO12, ccbO12_mem_selectedBoundarySupport⟩
      ⟨ccbO01, ccbO01_mem_selectedBoundarySupport⟩ :=
  (crossComponentBridgeAnnulusBoundaryAdj_ccbO01_ccbO12).symm

theorem crossComponentBridgeAnnulusBoundaryAdj_ccbO20_ccbO12 :
    (planarBoundarySupportEndpointAdjGraph crossComponentBridgeAnnulusEmbedding).Adj
      ⟨ccbO20, ccbO20_mem_selectedBoundarySupport⟩
      ⟨ccbO12, ccbO12_mem_selectedBoundarySupport⟩ :=
  (crossComponentBridgeAnnulusBoundaryAdj_ccbO12_ccbO20).symm

theorem crossComponentBridgeAnnulusBoundaryAdj_ccbI34_ccbI45 :
    (planarBoundarySupportEndpointAdjGraph crossComponentBridgeAnnulusEmbedding).Adj
      ⟨ccbI34, ccbI34_mem_selectedBoundarySupport⟩
      ⟨ccbI45, ccbI45_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 4, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [ccbI34, ccbI45] at this
  · simp [ccbI34]
  · simp [ccbI45]

theorem crossComponentBridgeAnnulusBoundaryAdj_ccbI45_ccbI53 :
    (planarBoundarySupportEndpointAdjGraph crossComponentBridgeAnnulusEmbedding).Adj
      ⟨ccbI45, ccbI45_mem_selectedBoundarySupport⟩
      ⟨ccbI53, ccbI53_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 5, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [ccbI45, ccbI53] at this
  · simp [ccbI45]
  · simp [ccbI53]

theorem crossComponentBridgeAnnulusBoundaryAdj_ccbI53_ccbI34 :
    (planarBoundarySupportEndpointAdjGraph crossComponentBridgeAnnulusEmbedding).Adj
      ⟨ccbI53, ccbI53_mem_selectedBoundarySupport⟩
      ⟨ccbI34, ccbI34_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 3, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [ccbI53, ccbI34] at this
  · simp [ccbI53]
  · simp [ccbI34]

theorem crossComponentBridgeAnnulusBoundaryAdj_ccbI45_ccbI34 :
    (planarBoundarySupportEndpointAdjGraph crossComponentBridgeAnnulusEmbedding).Adj
      ⟨ccbI45, ccbI45_mem_selectedBoundarySupport⟩
      ⟨ccbI34, ccbI34_mem_selectedBoundarySupport⟩ :=
  (crossComponentBridgeAnnulusBoundaryAdj_ccbI34_ccbI45).symm

theorem crossComponentBridgeAnnulusBoundaryAdj_ccbI53_ccbI45 :
    (planarBoundarySupportEndpointAdjGraph crossComponentBridgeAnnulusEmbedding).Adj
      ⟨ccbI53, ccbI53_mem_selectedBoundarySupport⟩
      ⟨ccbI45, ccbI45_mem_selectedBoundarySupport⟩ :=
  (crossComponentBridgeAnnulusBoundaryAdj_ccbI45_ccbI53).symm

theorem crossComponentBridgeAnnulusBoundaryAdj_preserves_label :
    ∀ ⦃e f : PlanarBoundaryEdgeVertex crossComponentBridgeAnnulusEmbedding⦄,
      (planarBoundarySupportEndpointAdjGraph crossComponentBridgeAnnulusEmbedding).Adj e f →
        crossComponentBridgeAnnulusBoundaryLabel e =
          crossComponentBridgeAnnulusBoundaryLabel f := by
  intro e f hadj
  rcases crossComponentBridgeAnnulus_boundaryEdge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases crossComponentBridgeAnnulus_boundaryEdge_eq f with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact False.elim
          (by
            rcases hadj with ⟨_, v, hvE, hvF⟩
            fin_cases v <;>
              simp [ccbO01, ccbO12, ccbO20, ccbI34, ccbI45, ccbI53] at hvE hvF)

theorem crossComponentBridgeAnnulusOuterRoot_ne_innerRoot :
    crossComponentBridgeAnnulusOuterRoot ≠ crossComponentBridgeAnnulusInnerRoot := by
  intro h
  have := congrArg Subtype.val h
  simp [crossComponentBridgeAnnulusOuterRoot, crossComponentBridgeAnnulusInnerRoot,
    ccbO01, ccbI34] at this

def crossComponentBridgeAnnulusAnnulusBoundaryReachabilityData :
    PlanarBoundaryAnnulusBoundaryReachabilityData crossComponentBridgeAnnulusEmbedding where
  outerRoot := crossComponentBridgeAnnulusOuterRoot
  innerRoot := crossComponentBridgeAnnulusInnerRoot
  hroots_ne := crossComponentBridgeAnnulusOuterRoot_ne_innerRoot
  hcoverRoots := by
    intro e
    rcases crossComponentBridgeAnnulus_boundaryEdge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨crossComponentBridgeAnnulusOuterRoot, by
        simp [crossComponentBridgeAnnulusOuterRoot_ne_innerRoot], SimpleGraph.Reachable.refl _⟩
    · refine ⟨crossComponentBridgeAnnulusOuterRoot, by
        simp [crossComponentBridgeAnnulusOuterRoot_ne_innerRoot],
        crossComponentBridgeAnnulusBoundaryAdj_ccbO12_ccbO01.reachable⟩
    · refine ⟨crossComponentBridgeAnnulusOuterRoot, by
        simp [crossComponentBridgeAnnulusOuterRoot_ne_innerRoot],
        crossComponentBridgeAnnulusBoundaryAdj_ccbO20_ccbO01.reachable⟩
    · refine ⟨crossComponentBridgeAnnulusInnerRoot, by simp, SimpleGraph.Reachable.refl _⟩
    · refine ⟨crossComponentBridgeAnnulusInnerRoot, by simp,
        crossComponentBridgeAnnulusBoundaryAdj_ccbI45_ccbI34.reachable⟩
    · refine ⟨crossComponentBridgeAnnulusInnerRoot, by simp,
        crossComponentBridgeAnnulusBoundaryAdj_ccbI53_ccbI34.reachable⟩
  hsepRoots := by
    intro r s hr hs hreach
    have hlabelEq :
        crossComponentBridgeAnnulusBoundaryLabel r =
          crossComponentBridgeAnnulusBoundaryLabel s :=
      eq_of_reachable_of_eq_on_adj
        (planarBoundarySupportEndpointAdjGraph crossComponentBridgeAnnulusEmbedding)
        crossComponentBridgeAnnulusBoundaryLabel
        (by
          intro u v huv
          exact crossComponentBridgeAnnulusBoundaryAdj_preserves_label huv)
        hreach
    have hOuterLabel :
        crossComponentBridgeAnnulusBoundaryLabel crossComponentBridgeAnnulusOuterRoot = false := by
      decide
    have hInnerLabel :
        crossComponentBridgeAnnulusBoundaryLabel crossComponentBridgeAnnulusInnerRoot = true := by
      decide
    have hr_cases : r = crossComponentBridgeAnnulusOuterRoot ∨
        r = crossComponentBridgeAnnulusInnerRoot := by
      simpa [crossComponentBridgeAnnulusOuterRoot_ne_innerRoot] using hr
    have hs_cases : s = crossComponentBridgeAnnulusOuterRoot ∨
        s = crossComponentBridgeAnnulusInnerRoot := by
      simpa [crossComponentBridgeAnnulusOuterRoot_ne_innerRoot] using hs
    rcases hr_cases with rfl | rfl <;> rcases hs_cases with rfl | rfl
    · rfl
    · rw [hOuterLabel, hInnerLabel] at hlabelEq
      cases hlabelEq
    · rw [hInnerLabel, hOuterLabel] at hlabelEq
      cases hlabelEq
    · rfl

def crossComponentBridgeAnnulusClosedWalkAnnulusBoundarySource :
    PlanarBoundaryClosedWalkAnnulusBoundarySource crossComponentBridgeAnnulusEmbedding :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields
    crossComponentBridgeAnnulusAnnulusBoundaryReachabilityData
    crossComponentBridgeAnnulusClosedWalkEmbeddingData
    crossComponentBridgeAnnulusClosedWalkEmbeddingData_selectedBoundaryArcOnFace

theorem nonempty_closedWalkAnnulusBoundarySource_crossComponentBridgeAnnulus :
    Nonempty
      (PlanarBoundaryClosedWalkAnnulusBoundarySource crossComponentBridgeAnnulusEmbedding) :=
  ⟨crossComponentBridgeAnnulusClosedWalkAnnulusBoundarySource⟩

theorem boundaryEdgeSetCyclicRun_outer_crossComponentBridgeAnnulus :
    BoundaryEdgeSetCyclicRun crossComponentBridgeAnnulusEmbedding
      crossComponentBridgeAnnulusOuterBoundarySet := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp [crossComponentBridgeAnnulusOuterBoundarySet] at he
    rcases he with rfl | rfl | rfl
    · exact ccbO01_mem_selectedBoundarySupport
    · exact ccbO12_mem_selectedBoundarySupport
    · exact ccbO20_mem_selectedBoundarySupport
  · refine ⟨[
      ⟨ccbO01, ccbO01_mem_selectedBoundarySupport⟩,
      ⟨ccbO12, ccbO12_mem_selectedBoundarySupport⟩,
      ⟨ccbO20, ccbO20_mem_selectedBoundarySupport⟩], ?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · change List.IsChain (planarBoundarySupportEndpointAdjGraph
        crossComponentBridgeAnnulusEmbedding).Adj
        [⟨ccbO01, ccbO01_mem_selectedBoundarySupport⟩,
          ⟨ccbO12, ccbO12_mem_selectedBoundarySupport⟩,
          ⟨ccbO20, ccbO20_mem_selectedBoundarySupport⟩,
          ⟨ccbO01, ccbO01_mem_selectedBoundarySupport⟩]
      exact (List.isChain_cons_cons).2
        ⟨crossComponentBridgeAnnulusBoundaryAdj_ccbO01_ccbO12,
          (List.isChain_cons_cons).2
            ⟨crossComponentBridgeAnnulusBoundaryAdj_ccbO12_ccbO20,
              (List.isChain_pair).2
                crossComponentBridgeAnnulusBoundaryAdj_ccbO20_ccbO01⟩⟩
    · intro x
      rcases crossComponentBridgeAnnulus_boundaryEdge_eq x with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem boundaryEdgeSetCyclicRun_inner_crossComponentBridgeAnnulus :
    BoundaryEdgeSetCyclicRun crossComponentBridgeAnnulusEmbedding
      crossComponentBridgeAnnulusInnerBoundarySet := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp [crossComponentBridgeAnnulusInnerBoundarySet] at he
    rcases he with rfl | rfl | rfl
    · exact ccbI34_mem_selectedBoundarySupport
    · exact ccbI45_mem_selectedBoundarySupport
    · exact ccbI53_mem_selectedBoundarySupport
  · refine ⟨[
      ⟨ccbI34, ccbI34_mem_selectedBoundarySupport⟩,
      ⟨ccbI45, ccbI45_mem_selectedBoundarySupport⟩,
      ⟨ccbI53, ccbI53_mem_selectedBoundarySupport⟩], ?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · change List.IsChain (planarBoundarySupportEndpointAdjGraph
        crossComponentBridgeAnnulusEmbedding).Adj
        [⟨ccbI34, ccbI34_mem_selectedBoundarySupport⟩,
          ⟨ccbI45, ccbI45_mem_selectedBoundarySupport⟩,
          ⟨ccbI53, ccbI53_mem_selectedBoundarySupport⟩,
          ⟨ccbI34, ccbI34_mem_selectedBoundarySupport⟩]
      exact (List.isChain_cons_cons).2
        ⟨crossComponentBridgeAnnulusBoundaryAdj_ccbI34_ccbI45,
          (List.isChain_cons_cons).2
            ⟨crossComponentBridgeAnnulusBoundaryAdj_ccbI45_ccbI53,
              (List.isChain_pair).2
                crossComponentBridgeAnnulusBoundaryAdj_ccbI53_ccbI34⟩⟩
    · intro x
      rcases crossComponentBridgeAnnulus_boundaryEdge_eq x with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem outer_inner_boundaryCycleEndpointSupports_disjoint_crossComponentBridgeAnnulus :
    Disjoint
      (boundaryEdgeSetEndpointSupport crossComponentBridgeAnnulusOuterBoundarySet)
      (boundaryEdgeSetEndpointSupport crossComponentBridgeAnnulusInnerBoundarySet) := by
  rw [Finset.disjoint_left]
  intro v hvOuter hvInner
  fin_cases v <;>
    simp [boundaryEdgeSetEndpointSupport, crossComponentBridgeAnnulusOuterBoundarySet,
      crossComponentBridgeAnnulusInnerBoundarySet, ccbO01, ccbO12, ccbO20,
      ccbI34, ccbI45, ccbI53] at hvOuter hvInner

theorem annulusBoundaryCyclePair_crossComponentBridgeAnnulus :
    AnnulusBoundaryCyclePair crossComponentBridgeAnnulusEmbedding
      crossComponentBridgeAnnulusOuterBoundarySet
      crossComponentBridgeAnnulusInnerBoundarySet :=
  ⟨boundaryEdgeSetCyclicRun_outer_crossComponentBridgeAnnulus,
    boundaryEdgeSetCyclicRun_inner_crossComponentBridgeAnnulus,
    outer_inner_boundaryCycleEndpointSupports_disjoint_crossComponentBridgeAnnulus⟩

theorem
    closedWalkAnnulusBoundarySource_boundaryCyclePair_and_componentInduced_does_not_imply_crossComponentChordFree_crossComponentBridgeAnnulus :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource crossComponentBridgeAnnulusEmbedding) ∧
      AnnulusBoundaryCyclePair crossComponentBridgeAnnulusEmbedding
        crossComponentBridgeAnnulusOuterBoundarySet
        crossComponentBridgeAnnulusInnerBoundarySet ∧
        BoundaryEdgeSetInducedSubgraph crossComponentBridgeAnnulusOuterBoundarySet ∧
          BoundaryEdgeSetInducedSubgraph crossComponentBridgeAnnulusInnerBoundarySet ∧
            ¬ BoundaryEdgeSetCrossComponentChordFree
              crossComponentBridgeAnnulusOuterBoundarySet
              crossComponentBridgeAnnulusInnerBoundarySet :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_crossComponentBridgeAnnulus,
    annulusBoundaryCyclePair_crossComponentBridgeAnnulus,
    crossComponentBridgeAnnulus_outerBoundaryEdgeSet_induced,
    crossComponentBridgeAnnulus_innerBoundaryEdgeSet_induced,
    not_crossComponentBridgeAnnulus_outer_inner_crossComponentChordFree⟩

theorem
    closedWalkAnnulusBoundarySource_boundaryCyclePair_and_componentInduced_does_not_imply_noChord_or_purifiedCarrier_crossComponentBridgeAnnulus :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource crossComponentBridgeAnnulusEmbedding) ∧
      AnnulusBoundaryCyclePair crossComponentBridgeAnnulusEmbedding
        crossComponentBridgeAnnulusOuterBoundarySet
        crossComponentBridgeAnnulusInnerBoundarySet ∧
        selectedBoundarySupport
          crossComponentBridgeAnnulusEmbedding.faceBoundary
          crossComponentBridgeAnnulusEmbedding.faces
          crossComponentBridgeAnnulusEmbedding.faces =
            crossComponentBridgeAnnulusOuterBoundarySet ∪
              crossComponentBridgeAnnulusInnerBoundarySet ∧
          BoundaryEdgeSetInducedSubgraph crossComponentBridgeAnnulusOuterBoundarySet ∧
            BoundaryEdgeSetInducedSubgraph crossComponentBridgeAnnulusInnerBoundarySet ∧
              ¬ InteriorEdgesNotSelectedBoundaryChords crossComponentBridgeAnnulusEmbedding ∧
                selectedBoundaryInteriorEdgeEndpointVertices
                  crossComponentBridgeAnnulusEmbedding = ∅ ∧
                  ¬ SelectedBoundaryInducedSubgraph crossComponentBridgeAnnulusEmbedding :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_crossComponentBridgeAnnulus,
    annulusBoundaryCyclePair_crossComponentBridgeAnnulus,
    crossComponentBridgeAnnulus_selectedBoundarySupport_eq,
    crossComponentBridgeAnnulus_outerBoundaryEdgeSet_induced,
    crossComponentBridgeAnnulus_innerBoundaryEdgeSet_induced,
    not_interiorEdgesNotSelectedBoundaryChords_crossComponentBridgeAnnulus,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_crossComponentBridgeAnnulus,
    not_selectedBoundaryInducedSubgraph_crossComponentBridgeAnnulus⟩

/-! ## Boundary-shadow path counterexample shell -/

def boundaryShadowPathGraph : SimpleGraph (Fin 18) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(2, 3), s(4, 5), s(6, 7), s(8, 9), s(10, 11),
        s(12, 13), s(14, 15), s(16, 17)} : Set (Sym2 (Fin 18)))

def gbsO0 : boundaryShadowPathGraph.edgeSet := ⟨s(0, 1), by
  simp [boundaryShadowPathGraph]⟩

def gbsP0 : boundaryShadowPathGraph.edgeSet := ⟨s(2, 3), by
  simp [boundaryShadowPathGraph]⟩

def gbsI0 : boundaryShadowPathGraph.edgeSet := ⟨s(4, 5), by
  simp [boundaryShadowPathGraph]⟩

def gbsO1 : boundaryShadowPathGraph.edgeSet := ⟨s(6, 7), by
  simp [boundaryShadowPathGraph]⟩

def gbsP1 : boundaryShadowPathGraph.edgeSet := ⟨s(8, 9), by
  simp [boundaryShadowPathGraph]⟩

def gbsI1 : boundaryShadowPathGraph.edgeSet := ⟨s(10, 11), by
  simp [boundaryShadowPathGraph]⟩

def gbsO2 : boundaryShadowPathGraph.edgeSet := ⟨s(12, 13), by
  simp [boundaryShadowPathGraph]⟩

def gbsP2 : boundaryShadowPathGraph.edgeSet := ⟨s(14, 15), by
  simp [boundaryShadowPathGraph]⟩

def gbsI2 : boundaryShadowPathGraph.edgeSet := ⟨s(16, 17), by
  simp [boundaryShadowPathGraph]⟩

theorem boundaryShadowPath_edge_eq
    (e : boundaryShadowPathGraph.edgeSet) :
    e = gbsO0 ∨ e = gbsP0 ∨ e = gbsI0 ∨ e = gbsO1 ∨ e = gbsP1 ∨
      e = gbsI1 ∨ e = gbsO2 ∨ e = gbsP2 ∨ e = gbsI2 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(2, 3) ∨ e.1 = s(4, 5) ∨
          e.1 = s(6, 7) ∨ e.1 = s(8, 9) ∨ e.1 = s(10, 11) ∨
          e.1 = s(12, 13) ∨ e.1 = s(14, 15) ∨ e.1 = s(16, 17)) ∧
        ¬ e.1.IsDiag := by
    simpa [boundaryShadowPathGraph] using e.2
  rcases h.1 with hO0 | hP0 | hI0 | hO1 | hP1 | hI1 | hO2 | hP2 | hI2
  · exact Or.inl (Subtype.ext hO0)
  · exact Or.inr <| Or.inl (Subtype.ext hP0)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext hI0)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hO1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hP1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hI1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hO2)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext hP2)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr (Subtype.ext hI2)

noncomputable instance boundaryShadowPathGraph_edgeSet_fintype :
    Fintype boundaryShadowPathGraph.edgeSet :=
  ⟨{gbsO0, gbsP0, gbsI0, gbsO1, gbsP1, gbsI1, gbsO2, gbsP2, gbsI2}, by
    intro e
    rcases boundaryShadowPath_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp⟩

abbrev BoundaryShadowPathFace := Fin 6

def boundaryShadowPathFaces : Finset BoundaryShadowPathFace := Finset.univ

def boundaryShadowPathFaceBoundary :
    BoundaryShadowPathFace → Finset boundaryShadowPathGraph.edgeSet
  | ⟨0, _⟩ => {gbsO0, gbsP0}
  | ⟨1, _⟩ => {gbsP0, gbsI0}
  | ⟨2, _⟩ => {gbsO1, gbsP1}
  | ⟨3, _⟩ => {gbsP1, gbsI1}
  | ⟨4, _⟩ => {gbsO2, gbsP2}
  | ⟨5, _⟩ => {gbsP2, gbsI2}

theorem totalIncidenceCount_gbsO0 :
    totalIncidenceCount boundaryShadowPathFaceBoundary boundaryShadowPathFaces gbsO0 = 1 := by
  decide

theorem totalIncidenceCount_gbsP0 :
    totalIncidenceCount boundaryShadowPathFaceBoundary boundaryShadowPathFaces gbsP0 = 2 := by
  decide

theorem totalIncidenceCount_gbsI0 :
    totalIncidenceCount boundaryShadowPathFaceBoundary boundaryShadowPathFaces gbsI0 = 1 := by
  decide

theorem totalIncidenceCount_gbsO1 :
    totalIncidenceCount boundaryShadowPathFaceBoundary boundaryShadowPathFaces gbsO1 = 1 := by
  decide

theorem totalIncidenceCount_gbsP1 :
    totalIncidenceCount boundaryShadowPathFaceBoundary boundaryShadowPathFaces gbsP1 = 2 := by
  decide

theorem totalIncidenceCount_gbsI1 :
    totalIncidenceCount boundaryShadowPathFaceBoundary boundaryShadowPathFaces gbsI1 = 1 := by
  decide

theorem totalIncidenceCount_gbsO2 :
    totalIncidenceCount boundaryShadowPathFaceBoundary boundaryShadowPathFaces gbsO2 = 1 := by
  decide

theorem totalIncidenceCount_gbsP2 :
    totalIncidenceCount boundaryShadowPathFaceBoundary boundaryShadowPathFaces gbsP2 = 2 := by
  decide

theorem totalIncidenceCount_gbsI2 :
    totalIncidenceCount boundaryShadowPathFaceBoundary boundaryShadowPathFaces gbsI2 = 1 := by
  decide

def boundaryShadowPathEmbedding :
    PlaneEmbeddingWithBoundary boundaryShadowPathGraph where
  Face := BoundaryShadowPathFace
  faceDecidableEq := inferInstance
  faces := boundaryShadowPathFaces
  faceBoundary := boundaryShadowPathFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases boundaryShadowPath_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases boundaryShadowPath_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

theorem gbsO0_mem_selectedBoundarySupport :
    gbsO0 ∈ selectedBoundarySupport
      boundaryShadowPathEmbedding.faceBoundary
      boundaryShadowPathEmbedding.faces
      boundaryShadowPathEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gbsO0⟩

theorem gbsI0_mem_selectedBoundarySupport :
    gbsI0 ∈ selectedBoundarySupport
      boundaryShadowPathEmbedding.faceBoundary
      boundaryShadowPathEmbedding.faces
      boundaryShadowPathEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gbsI0⟩

theorem gbsO1_mem_selectedBoundarySupport :
    gbsO1 ∈ selectedBoundarySupport
      boundaryShadowPathEmbedding.faceBoundary
      boundaryShadowPathEmbedding.faces
      boundaryShadowPathEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gbsO1⟩

theorem gbsI1_mem_selectedBoundarySupport :
    gbsI1 ∈ selectedBoundarySupport
      boundaryShadowPathEmbedding.faceBoundary
      boundaryShadowPathEmbedding.faces
      boundaryShadowPathEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gbsI1⟩

theorem gbsO2_mem_selectedBoundarySupport :
    gbsO2 ∈ selectedBoundarySupport
      boundaryShadowPathEmbedding.faceBoundary
      boundaryShadowPathEmbedding.faces
      boundaryShadowPathEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gbsO2⟩

theorem gbsI2_mem_selectedBoundarySupport :
    gbsI2 ∈ selectedBoundarySupport
      boundaryShadowPathEmbedding.faceBoundary
      boundaryShadowPathEmbedding.faces
      boundaryShadowPathEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gbsI2⟩

theorem gbsP0_not_mem_selectedBoundarySupport :
    gbsP0 ∉ selectedBoundarySupport
      boundaryShadowPathEmbedding.faceBoundary
      boundaryShadowPathEmbedding.faces
      boundaryShadowPathEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      boundaryShadowPathEmbedding.faceBoundary
      boundaryShadowPathEmbedding.faces
      boundaryShadowPathEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount boundaryShadowPathFaceBoundary boundaryShadowPathFaces gbsP0 = 1 := by
    simpa [boundaryShadowPathEmbedding] using hcount
  rw [totalIncidenceCount_gbsP0] at hcount'
  norm_num at hcount'

theorem gbsP1_not_mem_selectedBoundarySupport :
    gbsP1 ∉ selectedBoundarySupport
      boundaryShadowPathEmbedding.faceBoundary
      boundaryShadowPathEmbedding.faces
      boundaryShadowPathEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      boundaryShadowPathEmbedding.faceBoundary
      boundaryShadowPathEmbedding.faces
      boundaryShadowPathEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount boundaryShadowPathFaceBoundary boundaryShadowPathFaces gbsP1 = 1 := by
    simpa [boundaryShadowPathEmbedding] using hcount
  rw [totalIncidenceCount_gbsP1] at hcount'
  norm_num at hcount'

theorem gbsP2_not_mem_selectedBoundarySupport :
    gbsP2 ∉ selectedBoundarySupport
      boundaryShadowPathEmbedding.faceBoundary
      boundaryShadowPathEmbedding.faces
      boundaryShadowPathEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      boundaryShadowPathEmbedding.faceBoundary
      boundaryShadowPathEmbedding.faces
      boundaryShadowPathEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount boundaryShadowPathFaceBoundary boundaryShadowPathFaces gbsP2 = 1 := by
    simpa [boundaryShadowPathEmbedding] using hcount
  rw [totalIncidenceCount_gbsP2] at hcount'
  norm_num at hcount'

theorem boundaryShadowPath_pathEdges_no_boundaryFree_incident_face :
    ∀ e ∈ ({gbsP0, gbsP1, gbsP2} : Finset boundaryShadowPathGraph.edgeSet),
      ∀ f ∈ boundaryShadowPathEmbedding.faces,
        e ∈ boundaryShadowPathEmbedding.faceBoundary f →
          ∃ b ∈ selectedBoundarySupport
              boundaryShadowPathEmbedding.faceBoundary
              boundaryShadowPathEmbedding.faces
              boundaryShadowPathEmbedding.faces,
            b ∈ boundaryShadowPathEmbedding.faceBoundary f := by
  intro e he f _hf _hef
  change BoundaryShadowPathFace at f
  change ∃ b ∈ selectedBoundarySupport boundaryShadowPathFaceBoundary
      boundaryShadowPathFaces boundaryShadowPathFaces,
    b ∈ boundaryShadowPathFaceBoundary f
  rcases Finset.mem_insert.1 he with rfl | he
  · fin_cases f
    · exact ⟨gbsO0, by simpa [boundaryShadowPathEmbedding] using
        gbsO0_mem_selectedBoundarySupport, by decide⟩
    · exact ⟨gbsI0, by simpa [boundaryShadowPathEmbedding] using
        gbsI0_mem_selectedBoundarySupport, by decide⟩
    all_goals decide
  · rcases Finset.mem_insert.1 he with rfl | he
    · fin_cases f
      · decide
      · decide
      · exact ⟨gbsO1, by simpa [boundaryShadowPathEmbedding] using
          gbsO1_mem_selectedBoundarySupport, by decide⟩
      · exact ⟨gbsI1, by simpa [boundaryShadowPathEmbedding] using
          gbsI1_mem_selectedBoundarySupport, by decide⟩
      all_goals decide
    · have heP2 : e = gbsP2 := by simpa using he
      subst e
      fin_cases f
      · decide
      · decide
      · decide
      · decide
      · exact ⟨gbsO2, by simpa [boundaryShadowPathEmbedding] using
          gbsO2_mem_selectedBoundarySupport, by decide⟩
      · exact ⟨gbsI2, by simpa [boundaryShadowPathEmbedding] using
          gbsI2_mem_selectedBoundarySupport, by decide⟩

theorem boundaryShadowPath_pathEdges_endpoint_no_touch_selectedBoundarySupport :
    ∀ e ∈ ({gbsP0, gbsP1, gbsP2} : Finset boundaryShadowPathGraph.edgeSet),
      ∀ b ∈ selectedBoundarySupport
          boundaryShadowPathEmbedding.faceBoundary
          boundaryShadowPathEmbedding.faces
          boundaryShadowPathEmbedding.faces,
        ¬ ∃ v : Fin 18, v ∈ (e : Sym2 (Fin 18)) ∧ v ∈ (b : Sym2 (Fin 18)) := by
  intro e he b hb
  rcases Finset.mem_insert.1 he with rfl | he
  · rcases boundaryShadowPath_edge_eq b with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · exact False.elim (gbsP0_not_mem_selectedBoundarySupport hb)
    · decide
    · decide
    · exact False.elim (gbsP1_not_mem_selectedBoundarySupport hb)
    · decide
    · decide
    · exact False.elim (gbsP2_not_mem_selectedBoundarySupport hb)
    · decide
  · rcases Finset.mem_insert.1 he with rfl | he
    · rcases boundaryShadowPath_edge_eq b with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · exact False.elim (gbsP0_not_mem_selectedBoundarySupport hb)
      · decide
      · decide
      · exact False.elim (gbsP1_not_mem_selectedBoundarySupport hb)
      · decide
      · decide
      · exact False.elim (gbsP2_not_mem_selectedBoundarySupport hb)
      · decide
    · have heP2 : e = gbsP2 := by simpa using he
      subst e
      rcases boundaryShadowPath_edge_eq b with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · exact False.elim (gbsP0_not_mem_selectedBoundarySupport hb)
      · decide
      · decide
      · exact False.elim (gbsP1_not_mem_selectedBoundarySupport hb)
      · decide
      · decide
      · exact False.elim (gbsP2_not_mem_selectedBoundarySupport hb)
      · decide

theorem boundaryShadowPath_purifiedCarrier_nonempty :
    ∃ v : Fin 18,
      (∃ e ∈ ({gbsP0, gbsP1, gbsP2} : Finset boundaryShadowPathGraph.edgeSet),
        v ∈ (e : Sym2 (Fin 18))) ∧
      ∀ b ∈ selectedBoundarySupport
          boundaryShadowPathEmbedding.faceBoundary
          boundaryShadowPathEmbedding.faces
          boundaryShadowPathEmbedding.faces,
        v ∉ (b : Sym2 (Fin 18)) := by
  refine ⟨2, ⟨⟨gbsP0, by simp, by decide⟩, ?_⟩⟩
  intro b hb
  rcases boundaryShadowPath_edge_eq b with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · exact False.elim (gbsP0_not_mem_selectedBoundarySupport hb)
  · decide
  · decide
  · exact False.elim (gbsP1_not_mem_selectedBoundarySupport hb)
  · decide
  · decide
  · exact False.elim (gbsP2_not_mem_selectedBoundarySupport hb)
  · decide

theorem boundaryShadowPath_boundaryZero_no_evader_of_vanishes_on_pathEdges
    (z : boundaryShadowPathGraph.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule boundaryShadowPathEmbedding)
    (hcontrol :
      ∀ e ∈ ({gbsP0, gbsP1, gbsP2} : Finset boundaryShadowPathGraph.edgeSet), z e = 0) :
    z = 0 := by
  refine eq_zero_of_mem_planarBoundaryZeroSubmodule_of_control_or_boundary
    z hzBoundary ({gbsP0, gbsP1, gbsP2} : Finset boundaryShadowPathGraph.edgeSet)
    hcontrol ?_
  intro e
  rcases boundaryShadowPath_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr gbsO0_mem_selectedBoundarySupport
  · exact Or.inl (by simp)
  · exact Or.inr gbsI0_mem_selectedBoundarySupport
  · exact Or.inr gbsO1_mem_selectedBoundarySupport
  · exact Or.inl (by simp)
  · exact Or.inr gbsI1_mem_selectedBoundarySupport
  · exact Or.inr gbsO2_mem_selectedBoundarySupport
  · exact Or.inl (by simp)
  · exact Or.inr gbsI2_mem_selectedBoundarySupport

/-! ## Selected-endpoint free-face counterexample shell -/

def selectedEndpointFreeFaceGraph : SimpleGraph (Fin 12) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 3), s(4, 5), s(5, 6), s(6, 7),
        s(8, 9), s(9, 10), s(10, 11)} : Set (Sym2 (Fin 12)))

def gseO0 : selectedEndpointFreeFaceGraph.edgeSet := ⟨s(0, 1), by
  simp [selectedEndpointFreeFaceGraph]⟩

def gseP0 : selectedEndpointFreeFaceGraph.edgeSet := ⟨s(1, 2), by
  simp [selectedEndpointFreeFaceGraph]⟩

def gseI0 : selectedEndpointFreeFaceGraph.edgeSet := ⟨s(2, 3), by
  simp [selectedEndpointFreeFaceGraph]⟩

def gseO1 : selectedEndpointFreeFaceGraph.edgeSet := ⟨s(4, 5), by
  simp [selectedEndpointFreeFaceGraph]⟩

def gseP1 : selectedEndpointFreeFaceGraph.edgeSet := ⟨s(5, 6), by
  simp [selectedEndpointFreeFaceGraph]⟩

def gseI1 : selectedEndpointFreeFaceGraph.edgeSet := ⟨s(6, 7), by
  simp [selectedEndpointFreeFaceGraph]⟩

def gseO2 : selectedEndpointFreeFaceGraph.edgeSet := ⟨s(8, 9), by
  simp [selectedEndpointFreeFaceGraph]⟩

def gseP2 : selectedEndpointFreeFaceGraph.edgeSet := ⟨s(9, 10), by
  simp [selectedEndpointFreeFaceGraph]⟩

def gseI2 : selectedEndpointFreeFaceGraph.edgeSet := ⟨s(10, 11), by
  simp [selectedEndpointFreeFaceGraph]⟩

theorem selectedEndpointFreeFace_edge_eq
    (e : selectedEndpointFreeFaceGraph.edgeSet) :
    e = gseO0 ∨ e = gseP0 ∨ e = gseI0 ∨ e = gseO1 ∨ e = gseP1 ∨
      e = gseI1 ∨ e = gseO2 ∨ e = gseP2 ∨ e = gseI2 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 3) ∨
          e.1 = s(4, 5) ∨ e.1 = s(5, 6) ∨ e.1 = s(6, 7) ∨
          e.1 = s(8, 9) ∨ e.1 = s(9, 10) ∨ e.1 = s(10, 11)) ∧
        ¬ e.1.IsDiag := by
    simpa [selectedEndpointFreeFaceGraph] using e.2
  rcases h.1 with hO0 | hP0 | hI0 | hO1 | hP1 | hI1 | hO2 | hP2 | hI2
  · exact Or.inl (Subtype.ext hO0)
  · exact Or.inr <| Or.inl (Subtype.ext hP0)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext hI0)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hO1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hP1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hI1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hO2)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext hP2)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr (Subtype.ext hI2)

noncomputable instance selectedEndpointFreeFaceGraph_edgeSet_fintype :
    Fintype selectedEndpointFreeFaceGraph.edgeSet :=
  ⟨{gseO0, gseP0, gseI0, gseO1, gseP1, gseI1, gseO2, gseP2, gseI2}, by
    intro e
    rcases selectedEndpointFreeFace_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp⟩

abbrev SelectedEndpointFreeFaceFace := Fin 9

def selectedEndpointFreeFaceFaces : Finset SelectedEndpointFreeFaceFace := Finset.univ

def selectedEndpointFreeFaceFaceBoundary :
    SelectedEndpointFreeFaceFace → Finset selectedEndpointFreeFaceGraph.edgeSet
  | ⟨0, _⟩ => {gseO0, gseP0}
  | ⟨1, _⟩ => {gseP0}
  | ⟨2, _⟩ => {gseI0}
  | ⟨3, _⟩ => {gseO1, gseP1}
  | ⟨4, _⟩ => {gseP1}
  | ⟨5, _⟩ => {gseI1}
  | ⟨6, _⟩ => {gseO2, gseP2}
  | ⟨7, _⟩ => {gseP2}
  | ⟨8, _⟩ => {gseI2}

theorem totalIncidenceCount_gseO0 :
    totalIncidenceCount selectedEndpointFreeFaceFaceBoundary
      selectedEndpointFreeFaceFaces gseO0 = 1 := by
  decide

theorem totalIncidenceCount_gseP0 :
    totalIncidenceCount selectedEndpointFreeFaceFaceBoundary
      selectedEndpointFreeFaceFaces gseP0 = 2 := by
  decide

theorem totalIncidenceCount_gseI0 :
    totalIncidenceCount selectedEndpointFreeFaceFaceBoundary
      selectedEndpointFreeFaceFaces gseI0 = 1 := by
  decide

theorem totalIncidenceCount_gseO1 :
    totalIncidenceCount selectedEndpointFreeFaceFaceBoundary
      selectedEndpointFreeFaceFaces gseO1 = 1 := by
  decide

theorem totalIncidenceCount_gseP1 :
    totalIncidenceCount selectedEndpointFreeFaceFaceBoundary
      selectedEndpointFreeFaceFaces gseP1 = 2 := by
  decide

theorem totalIncidenceCount_gseI1 :
    totalIncidenceCount selectedEndpointFreeFaceFaceBoundary
      selectedEndpointFreeFaceFaces gseI1 = 1 := by
  decide

theorem totalIncidenceCount_gseO2 :
    totalIncidenceCount selectedEndpointFreeFaceFaceBoundary
      selectedEndpointFreeFaceFaces gseO2 = 1 := by
  decide

theorem totalIncidenceCount_gseP2 :
    totalIncidenceCount selectedEndpointFreeFaceFaceBoundary
      selectedEndpointFreeFaceFaces gseP2 = 2 := by
  decide

theorem totalIncidenceCount_gseI2 :
    totalIncidenceCount selectedEndpointFreeFaceFaceBoundary
      selectedEndpointFreeFaceFaces gseI2 = 1 := by
  decide

def selectedEndpointFreeFaceEmbedding :
    PlaneEmbeddingWithBoundary selectedEndpointFreeFaceGraph where
  Face := SelectedEndpointFreeFaceFace
  faceDecidableEq := inferInstance
  faces := selectedEndpointFreeFaceFaces
  faceBoundary := selectedEndpointFreeFaceFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases selectedEndpointFreeFace_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases selectedEndpointFreeFace_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

theorem gseO0_mem_selectedBoundarySupport :
    gseO0 ∈ selectedBoundarySupport
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces
      selectedEndpointFreeFaceEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gseO0⟩

theorem gseI0_mem_selectedBoundarySupport :
    gseI0 ∈ selectedBoundarySupport
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces
      selectedEndpointFreeFaceEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gseI0⟩

theorem gseO1_mem_selectedBoundarySupport :
    gseO1 ∈ selectedBoundarySupport
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces
      selectedEndpointFreeFaceEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gseO1⟩

theorem gseI1_mem_selectedBoundarySupport :
    gseI1 ∈ selectedBoundarySupport
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces
      selectedEndpointFreeFaceEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gseI1⟩

theorem gseO2_mem_selectedBoundarySupport :
    gseO2 ∈ selectedBoundarySupport
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces
      selectedEndpointFreeFaceEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gseO2⟩

theorem gseI2_mem_selectedBoundarySupport :
    gseI2 ∈ selectedBoundarySupport
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces
      selectedEndpointFreeFaceEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gseI2⟩

theorem gseP0_not_mem_selectedBoundarySupport :
    gseP0 ∉ selectedBoundarySupport
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces
      selectedEndpointFreeFaceEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces
      selectedEndpointFreeFaceEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount selectedEndpointFreeFaceFaceBoundary
        selectedEndpointFreeFaceFaces gseP0 = 1 := by
    simpa [selectedEndpointFreeFaceEmbedding] using hcount
  rw [totalIncidenceCount_gseP0] at hcount'
  norm_num at hcount'

theorem gseP1_not_mem_selectedBoundarySupport :
    gseP1 ∉ selectedBoundarySupport
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces
      selectedEndpointFreeFaceEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces
      selectedEndpointFreeFaceEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount selectedEndpointFreeFaceFaceBoundary
        selectedEndpointFreeFaceFaces gseP1 = 1 := by
    simpa [selectedEndpointFreeFaceEmbedding] using hcount
  rw [totalIncidenceCount_gseP1] at hcount'
  norm_num at hcount'

theorem gseP2_not_mem_selectedBoundarySupport :
    gseP2 ∉ selectedBoundarySupport
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces
      selectedEndpointFreeFaceEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces
      selectedEndpointFreeFaceEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount selectedEndpointFreeFaceFaceBoundary
        selectedEndpointFreeFaceFaces gseP2 = 1 := by
    simpa [selectedEndpointFreeFaceEmbedding] using hcount
  rw [totalIncidenceCount_gseP2] at hcount'
  norm_num at hcount'

theorem gseP0_mem_interiorEdgeSupport :
    gseP0 ∈ interiorEdgeSupport
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_gseP0⟩

theorem gseP1_mem_interiorEdgeSupport :
    gseP1 ∈ interiorEdgeSupport
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_gseP1⟩

theorem gseP2_mem_interiorEdgeSupport :
    gseP2 ∈ interiorEdgeSupport
      selectedEndpointFreeFaceEmbedding.faceBoundary
      selectedEndpointFreeFaceEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_gseP2⟩

theorem selectedEndpointFreeFace_interiorEdgeSupport_eq :
    interiorEdgeSupport
        selectedEndpointFreeFaceEmbedding.faceBoundary
        selectedEndpointFreeFaceEmbedding.faces =
      ({gseP0, gseP1, gseP2} : Finset selectedEndpointFreeFaceGraph.edgeSet) := by
  ext e
  rcases selectedEndpointFreeFace_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

def gseFree0 : AmbientFace selectedEndpointFreeFaceEmbedding.faces :=
  ⟨(1 : SelectedEndpointFreeFaceFace), by decide⟩

def gseFree1 : AmbientFace selectedEndpointFreeFaceEmbedding.faces :=
  ⟨(4 : SelectedEndpointFreeFaceFace), by decide⟩

def gseFree2 : AmbientFace selectedEndpointFreeFaceEmbedding.faces :=
  ⟨(7 : SelectedEndpointFreeFaceFace), by decide⟩

@[simp] theorem gseP0_ne_gseP1 : gseP0 ≠ gseP1 := by
  decide

@[simp] theorem gseP1_ne_gseP0 : gseP1 ≠ gseP0 := by
  decide

@[simp] theorem gseP0_ne_gseP2 : gseP0 ≠ gseP2 := by
  decide

@[simp] theorem gseP2_ne_gseP0 : gseP2 ≠ gseP0 := by
  decide

@[simp] theorem gseP1_ne_gseP2 : gseP1 ≠ gseP2 := by
  decide

@[simp] theorem gseP2_ne_gseP1 : gseP2 ≠ gseP1 := by
  decide

@[simp] theorem gseFree0_ne_gseFree1 : gseFree0 ≠ gseFree1 := by
  decide

@[simp] theorem gseFree1_ne_gseFree0 : gseFree1 ≠ gseFree0 := by
  decide

@[simp] theorem gseFree0_ne_gseFree2 : gseFree0 ≠ gseFree2 := by
  decide

@[simp] theorem gseFree2_ne_gseFree0 : gseFree2 ≠ gseFree0 := by
  decide

@[simp] theorem gseFree1_ne_gseFree2 : gseFree1 ≠ gseFree2 := by
  decide

@[simp] theorem gseFree2_ne_gseFree1 : gseFree2 ≠ gseFree1 := by
  decide

def selectedEndpointFreeFaceSelectorFace
    (e : selectedEndpointFreeFaceGraph.edgeSet) :
    AmbientFace selectedEndpointFreeFaceEmbedding.faces :=
  if e = gseP0 then gseFree0
  else if e = gseP1 then gseFree1
  else gseFree2

@[simp] theorem selectedEndpointFreeFaceSelectorFace_gseP0 :
    selectedEndpointFreeFaceSelectorFace gseP0 = gseFree0 := by
  simp [selectedEndpointFreeFaceSelectorFace]

@[simp] theorem selectedEndpointFreeFaceSelectorFace_gseP1 :
    selectedEndpointFreeFaceSelectorFace gseP1 = gseFree1 := by
  simp [selectedEndpointFreeFaceSelectorFace]

@[simp] theorem selectedEndpointFreeFaceSelectorFace_gseP2 :
    selectedEndpointFreeFaceSelectorFace gseP2 = gseFree2 := by
  simp [selectedEndpointFreeFaceSelectorFace]

@[simp] theorem selectedEndpointFreeFaceFaceBoundary_gseFree0 :
    selectedEndpointFreeFaceEmbedding.faceBoundary gseFree0.1 = {gseP0} := by
  rfl

@[simp] theorem selectedEndpointFreeFaceFaceBoundary_gseFree1 :
    selectedEndpointFreeFaceEmbedding.faceBoundary gseFree1.1 = {gseP1} := by
  rfl

@[simp] theorem selectedEndpointFreeFaceFaceBoundary_gseFree2 :
    selectedEndpointFreeFaceEmbedding.faceBoundary gseFree2.1 = {gseP2} := by
  rfl

noncomputable def selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector :
    BoundaryFreeIncidentFaceSelector selectedEndpointFreeFaceEmbedding where
  faceOf := fun e _ => selectedEndpointFreeFaceSelectorFace e
  edge_mem_faceOf := by
    intro e he
    have hePath :
        e ∈ ({gseP0, gseP1, gseP2} : Finset selectedEndpointFreeFaceGraph.edgeSet) := by
      simpa [selectedEndpointFreeFace_interiorEdgeSupport_eq] using he
    rcases Finset.mem_insert.1 hePath with h0 | hrest
    · subst e
      simp [selectedEndpointFreeFaceSelectorFace, gseFree0,
        selectedEndpointFreeFaceEmbedding, selectedEndpointFreeFaceFaceBoundary]
    · rcases Finset.mem_insert.1 hrest with h1 | h2
      · subst e
        simp [selectedEndpointFreeFaceSelectorFace, gseFree1,
          selectedEndpointFreeFaceEmbedding, selectedEndpointFreeFaceFaceBoundary]
      · have h2' : e = gseP2 := by simpa using h2
        subst e
        simp [selectedEndpointFreeFaceSelectorFace, gseFree2,
          selectedEndpointFreeFaceEmbedding, selectedEndpointFreeFaceFaceBoundary]
  faceOf_disjoint_selectedBoundarySupport := by
    intro e he
    rw [Finset.disjoint_left]
    intro b hbFace hbSelected
    have hePath :
        e ∈ ({gseP0, gseP1, gseP2} : Finset selectedEndpointFreeFaceGraph.edgeSet) := by
      simpa [selectedEndpointFreeFace_interiorEdgeSupport_eq] using he
    rcases Finset.mem_insert.1 hePath with h0 | hrest
    · subst e
      have hb : b = gseP0 := by
        simpa [selectedEndpointFreeFaceSelectorFace, gseFree0,
          selectedEndpointFreeFaceEmbedding, selectedEndpointFreeFaceFaceBoundary] using hbFace
      exact gseP0_not_mem_selectedBoundarySupport (by simpa [hb] using hbSelected)
    · rcases Finset.mem_insert.1 hrest with h1 | h2
      · subst e
        have hb : b = gseP1 := by
          simpa [selectedEndpointFreeFaceSelectorFace, gseFree1,
            selectedEndpointFreeFaceEmbedding, selectedEndpointFreeFaceFaceBoundary] using hbFace
        exact gseP1_not_mem_selectedBoundarySupport (by simpa [hb] using hbSelected)
      · have h2' : e = gseP2 := by simpa using h2
        subst e
        have hb : b = gseP2 := by
          simpa [selectedEndpointFreeFaceSelectorFace, gseFree2,
            selectedEndpointFreeFaceEmbedding, selectedEndpointFreeFaceFaceBoundary] using hbFace
        exact gseP2_not_mem_selectedBoundarySupport (by simpa [hb] using hbSelected)

theorem selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_injective :
    ∀ {e₁ e₂ : selectedEndpointFreeFaceGraph.edgeSet}
      (he₁ : e₁ ∈ interiorEdgeSupport
        selectedEndpointFreeFaceEmbedding.faceBoundary
        selectedEndpointFreeFaceEmbedding.faces)
      (he₂ : e₂ ∈ interiorEdgeSupport
        selectedEndpointFreeFaceEmbedding.faceBoundary
        selectedEndpointFreeFaceEmbedding.faces),
        selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector.faceOf e₁ he₁ =
          selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector.faceOf e₂ he₂ →
          e₁ = e₂ := by
    intro e₁ e₂ he₁ he₂ hface
    have hpath₁ :
        e₁ ∈ ({gseP0, gseP1, gseP2} : Finset selectedEndpointFreeFaceGraph.edgeSet) := by
      simpa [selectedEndpointFreeFace_interiorEdgeSupport_eq] using he₁
    have hpath₂ :
        e₂ ∈ ({gseP0, gseP1, gseP2} : Finset selectedEndpointFreeFaceGraph.edgeSet) := by
      simpa [selectedEndpointFreeFace_interiorEdgeSupport_eq] using he₂
    rcases Finset.mem_insert.1 hpath₁ with h10 | h1rest
    · subst e₁
      rcases Finset.mem_insert.1 hpath₂ with h20 | h2rest
      · subst e₂
        rfl
      · rcases Finset.mem_insert.1 h2rest with h21 | h22
        · subst e₂
          exact False.elim (by
            have hbad := hface
            simp [selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector] at hbad)
        · have h22' : e₂ = gseP2 := by simpa using h22
          subst e₂
          exact False.elim (by
            have hbad := hface
            simp [selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector] at hbad)
    · rcases Finset.mem_insert.1 h1rest with h11 | h12
      · subst e₁
        rcases Finset.mem_insert.1 hpath₂ with h20 | h2rest
        · subst e₂
          exact False.elim (by
            have hbad := hface
            simp [selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector] at hbad)
        · rcases Finset.mem_insert.1 h2rest with h21 | h22
          · subst e₂
            rfl
          · have h22' : e₂ = gseP2 := by simpa using h22
            subst e₂
            exact False.elim (by
              have hbad := hface
              simp [selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector] at hbad)
      · have h12' : e₁ = gseP2 := by simpa using h12
        subst e₁
        rcases Finset.mem_insert.1 hpath₂ with h20 | h2rest
        · subst e₂
          exact False.elim (by
            have hbad := hface
            simp [selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector] at hbad)
        · rcases Finset.mem_insert.1 h2rest with h21 | h22
          · subst e₂
            exact False.elim (by
              have hbad := hface
              simp [selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector] at hbad)
          · have h22' : e₂ = gseP2 := by simpa using h22
            subst e₂
            rfl

theorem selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_selectedWitnessEdge_gseFree0
    (fallbackEdge :
      AmbientFace selectedEndpointFreeFaceEmbedding.faces →
        selectedEndpointFreeFaceGraph.edgeSet) :
    selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector.selectedWitnessEdge
        fallbackEdge gseFree0 = gseP0 := by
  simpa [selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector,
    selectedEndpointFreeFaceSelectorFace] using
    selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector.selectedWitnessEdge_eq_of_faceOf
      fallbackEdge selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_injective
      gseP0_mem_interiorEdgeSupport

theorem selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_selectedWitnessEdge_gseFree1
    (fallbackEdge :
      AmbientFace selectedEndpointFreeFaceEmbedding.faces →
        selectedEndpointFreeFaceGraph.edgeSet) :
    selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector.selectedWitnessEdge
        fallbackEdge gseFree1 = gseP1 := by
  simpa [selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector,
    selectedEndpointFreeFaceSelectorFace] using
    selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector.selectedWitnessEdge_eq_of_faceOf
      fallbackEdge selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_injective
      gseP1_mem_interiorEdgeSupport

theorem selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_selectedWitnessEdge_gseFree2
    (fallbackEdge :
      AmbientFace selectedEndpointFreeFaceEmbedding.faces →
        selectedEndpointFreeFaceGraph.edgeSet) :
    selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector.selectedWitnessEdge
        fallbackEdge gseFree2 = gseP2 := by
  simpa [selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector,
    selectedEndpointFreeFaceSelectorFace] using
    selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector.selectedWitnessEdge_eq_of_faceOf
      fallbackEdge selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_injective
      gseP2_mem_interiorEdgeSupport

theorem selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_strictDescent
    (boundaryData : PlanarBoundaryAnnulusBoundaryData selectedEndpointFreeFaceEmbedding)
    (fallbackEdge :
      AmbientFace selectedEndpointFreeFaceEmbedding.faces →
        selectedEndpointFreeFaceGraph.edgeSet)
    (faceDistance : AmbientFace selectedEndpointFreeFaceEmbedding.faces → ℕ) :
    ∀ f ∈ selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector.peelFaces,
      ∀ e ∈ (selectedEndpointFreeFaceEmbedding.faceBoundary f.1).erase
        (selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector.selectedWitnessEdge
          fallbackEdge f),
        e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
          ∃ g ∈ selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector.peelFaces,
            selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector.selectedWitnessEdge
                fallbackEdge g = e ∧
              faceDistance f < faceDistance g := by
  intro f hf e he
  have hfCases : f = gseFree0 ∨ f = gseFree1 ∨ f = gseFree2 := by
    rcases Finset.mem_image.1 hf with ⟨x, _hx, hfx⟩
    have hxPath :
        x.1 ∈ ({gseP0, gseP1, gseP2} : Finset selectedEndpointFreeFaceGraph.edgeSet) := by
      rw [← selectedEndpointFreeFace_interiorEdgeSupport_eq]
      exact x.2
    rcases Finset.mem_insert.1 hxPath with hx0 | hxrest
    · left
      simpa [selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector,
        selectedEndpointFreeFaceSelectorFace, hx0] using hfx.symm
    · rcases Finset.mem_insert.1 hxrest with hx1 | hx2
      · right
        left
        simpa [selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector,
          selectedEndpointFreeFaceSelectorFace, hx1] using hfx.symm
      · right
        right
        have hx2' : x.1 = gseP2 := by simpa using hx2
        simpa [selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector,
          selectedEndpointFreeFaceSelectorFace, hx2'] using hfx.symm
  rcases hfCases with rfl | hrest
  · have hsel :=
      selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_selectedWitnessEdge_gseFree0
        fallbackEdge
    have hfalse : False := by
      have hne := (Finset.mem_erase.1 he).1
      have hmem : e = gseP0 := by
        simpa [selectedEndpointFreeFaceFaceBoundary_gseFree0] using
          (Finset.mem_erase.1 he).2
      exact hne (hmem.trans hsel.symm)
    exact False.elim hfalse
  · rcases hrest with rfl | rfl
    · have hsel :=
        selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_selectedWitnessEdge_gseFree1
          fallbackEdge
      have hfalse : False := by
        have hne := (Finset.mem_erase.1 he).1
        have hmem : e = gseP1 := by
          simpa [selectedEndpointFreeFaceFaceBoundary_gseFree1] using
            (Finset.mem_erase.1 he).2
        exact hne (hmem.trans hsel.symm)
      exact False.elim hfalse
    · have hsel :=
        selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_selectedWitnessEdge_gseFree2
          fallbackEdge
      have hfalse : False := by
        have hne := (Finset.mem_erase.1 he).1
        have hmem : e = gseP2 := by
          simpa [selectedEndpointFreeFaceFaceBoundary_gseFree2] using
            (Finset.mem_erase.1 he).2
        exact hne (hmem.trans hsel.symm)
      exact False.elim hfalse

theorem selectedEndpointFreeFace_pathEdges_have_boundaryFree_incident_face :
    ∀ e ∈ ({gseP0, gseP1, gseP2} : Finset selectedEndpointFreeFaceGraph.edgeSet),
      ∃ f ∈ selectedEndpointFreeFaceEmbedding.faces,
        e ∈ selectedEndpointFreeFaceEmbedding.faceBoundary f ∧
          ∀ b ∈ selectedBoundarySupport
              selectedEndpointFreeFaceEmbedding.faceBoundary
              selectedEndpointFreeFaceEmbedding.faces
              selectedEndpointFreeFaceEmbedding.faces,
            b ∉ selectedEndpointFreeFaceEmbedding.faceBoundary f := by
  intro e he
  rcases Finset.mem_insert.1 he with rfl | he
  · refine ⟨(1 : SelectedEndpointFreeFaceFace), by decide, by decide, ?_⟩
    intro b hb
    rcases selectedEndpointFreeFace_edge_eq b with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · exact False.elim (gseP0_not_mem_selectedBoundarySupport hb)
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · rcases Finset.mem_insert.1 he with rfl | he
    · refine ⟨(4 : SelectedEndpointFreeFaceFace), by decide, by decide, ?_⟩
      intro b hb
      rcases selectedEndpointFreeFace_edge_eq b with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
      · exact False.elim (gseP1_not_mem_selectedBoundarySupport hb)
      · decide
      · decide
      · decide
      · decide
    · have heP2 : e = gseP2 := by simpa using he
      subst e
      refine ⟨(7 : SelectedEndpointFreeFaceFace), by decide, by decide, ?_⟩
      intro b hb
      rcases selectedEndpointFreeFace_edge_eq b with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · exact False.elim (gseP2_not_mem_selectedBoundarySupport hb)
      · decide

theorem selectedEndpointFreeFace_pathEdges_touch_selectedBoundaryEndpoint :
    ∃ e ∈ ({gseP0, gseP1, gseP2} : Finset selectedEndpointFreeFaceGraph.edgeSet),
      ∃ b ∈ selectedBoundarySupport
          selectedEndpointFreeFaceEmbedding.faceBoundary
          selectedEndpointFreeFaceEmbedding.faces
          selectedEndpointFreeFaceEmbedding.faces,
        ∃ v : Fin 12, v ∈ (e : Sym2 (Fin 12)) ∧ v ∈ (b : Sym2 (Fin 12)) := by
  exact ⟨gseP0, by simp, gseO0, gseO0_mem_selectedBoundarySupport,
    1, by decide, by decide⟩

theorem selectedEndpointFreeFace_purifiedCarrier_empty :
    ∀ v : Fin 12,
      (∃ e ∈ ({gseP0, gseP1, gseP2} : Finset selectedEndpointFreeFaceGraph.edgeSet),
        v ∈ (e : Sym2 (Fin 12))) →
        ∃ b ∈ selectedBoundarySupport
            selectedEndpointFreeFaceEmbedding.faceBoundary
            selectedEndpointFreeFaceEmbedding.faces
            selectedEndpointFreeFaceEmbedding.faces,
          v ∈ (b : Sym2 (Fin 12)) := by
  decide

theorem selectedEndpointFreeFace_strictDescentSelector_purifiedCarrier_empty
    (boundaryData : PlanarBoundaryAnnulusBoundaryData selectedEndpointFreeFaceEmbedding)
    (fallbackEdge :
      AmbientFace selectedEndpointFreeFaceEmbedding.faces →
        selectedEndpointFreeFaceGraph.edgeSet)
    (faceDistance : AmbientFace selectedEndpointFreeFaceEmbedding.faces → ℕ) :
    (∃ selector : BoundaryFreeIncidentFaceSelector selectedEndpointFreeFaceEmbedding,
      (∀ {e₁ e₂ : selectedEndpointFreeFaceGraph.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport
          selectedEndpointFreeFaceEmbedding.faceBoundary
          selectedEndpointFreeFaceEmbedding.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport
          selectedEndpointFreeFaceEmbedding.faceBoundary
          selectedEndpointFreeFaceEmbedding.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂) ∧
      (∀ f ∈ selector.peelFaces,
        ∀ e ∈ (selectedEndpointFreeFaceEmbedding.faceBoundary f.1).erase
          (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)) ∧
    (∀ v : Fin 12,
      (∃ e ∈ ({gseP0, gseP1, gseP2} : Finset selectedEndpointFreeFaceGraph.edgeSet),
        v ∈ (e : Sym2 (Fin 12))) →
        ∃ b ∈ selectedBoundarySupport
            selectedEndpointFreeFaceEmbedding.faceBoundary
            selectedEndpointFreeFaceEmbedding.faces
            selectedEndpointFreeFaceEmbedding.faces,
          v ∈ (b : Sym2 (Fin 12))) := by
  exact
    ⟨⟨selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector,
      selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_injective,
      selectedEndpointFreeFaceBoundaryFreeIncidentFaceSelector_strictDescent
        boundaryData fallbackEdge faceDistance⟩,
      selectedEndpointFreeFace_purifiedCarrier_empty⟩

theorem selectedEndpointFreeFace_boundaryZero_no_evader_of_vanishes_on_pathEdges
    (z : selectedEndpointFreeFaceGraph.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule selectedEndpointFreeFaceEmbedding)
    (hcontrol :
      ∀ e ∈ ({gseP0, gseP1, gseP2} : Finset selectedEndpointFreeFaceGraph.edgeSet), z e = 0) :
    z = 0 := by
  refine eq_zero_of_mem_planarBoundaryZeroSubmodule_of_control_or_boundary
    z hzBoundary
    ({gseP0, gseP1, gseP2} : Finset selectedEndpointFreeFaceGraph.edgeSet)
    hcontrol ?_
  intro e
  rcases selectedEndpointFreeFace_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr gseO0_mem_selectedBoundarySupport
  · exact Or.inl (by simp)
  · exact Or.inr gseI0_mem_selectedBoundarySupport
  · exact Or.inr gseO1_mem_selectedBoundarySupport
  · exact Or.inl (by simp)
  · exact Or.inr gseI1_mem_selectedBoundarySupport
  · exact Or.inr gseO2_mem_selectedBoundarySupport
  · exact Or.inl (by simp)
  · exact Or.inr gseI2_mem_selectedBoundarySupport

/-! ## Touching free-face counterexample shell -/

def touchingFreeFaceGraph : SimpleGraph (Fin 15) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(3, 4), s(5, 6), s(6, 7), s(8, 9),
        s(10, 11), s(11, 12), s(13, 14)} : Set (Sym2 (Fin 15)))

def gtfO0 : touchingFreeFaceGraph.edgeSet := ⟨s(0, 1), by
  simp [touchingFreeFaceGraph]⟩

def gtfP0 : touchingFreeFaceGraph.edgeSet := ⟨s(1, 2), by
  simp [touchingFreeFaceGraph]⟩

def gtfI0 : touchingFreeFaceGraph.edgeSet := ⟨s(3, 4), by
  simp [touchingFreeFaceGraph]⟩

def gtfO1 : touchingFreeFaceGraph.edgeSet := ⟨s(5, 6), by
  simp [touchingFreeFaceGraph]⟩

def gtfP1 : touchingFreeFaceGraph.edgeSet := ⟨s(6, 7), by
  simp [touchingFreeFaceGraph]⟩

def gtfI1 : touchingFreeFaceGraph.edgeSet := ⟨s(8, 9), by
  simp [touchingFreeFaceGraph]⟩

def gtfO2 : touchingFreeFaceGraph.edgeSet := ⟨s(10, 11), by
  simp [touchingFreeFaceGraph]⟩

def gtfP2 : touchingFreeFaceGraph.edgeSet := ⟨s(11, 12), by
  simp [touchingFreeFaceGraph]⟩

def gtfI2 : touchingFreeFaceGraph.edgeSet := ⟨s(13, 14), by
  simp [touchingFreeFaceGraph]⟩

theorem touchingFreeFace_edge_eq
    (e : touchingFreeFaceGraph.edgeSet) :
    e = gtfO0 ∨ e = gtfP0 ∨ e = gtfI0 ∨ e = gtfO1 ∨ e = gtfP1 ∨
      e = gtfI1 ∨ e = gtfO2 ∨ e = gtfP2 ∨ e = gtfI2 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(3, 4) ∨
          e.1 = s(5, 6) ∨ e.1 = s(6, 7) ∨ e.1 = s(8, 9) ∨
          e.1 = s(10, 11) ∨ e.1 = s(11, 12) ∨ e.1 = s(13, 14)) ∧
        ¬ e.1.IsDiag := by
    simpa [touchingFreeFaceGraph] using e.2
  rcases h.1 with hO0 | hP0 | hI0 | hO1 | hP1 | hI1 | hO2 | hP2 | hI2
  · exact Or.inl (Subtype.ext hO0)
  · exact Or.inr <| Or.inl (Subtype.ext hP0)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext hI0)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hO1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hP1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hI1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hO2)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext hP2)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr (Subtype.ext hI2)

noncomputable instance touchingFreeFaceGraph_edgeSet_fintype :
    Fintype touchingFreeFaceGraph.edgeSet :=
  ⟨{gtfO0, gtfP0, gtfI0, gtfO1, gtfP1, gtfI1, gtfO2, gtfP2, gtfI2}, by
    intro e
    rcases touchingFreeFace_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp⟩

abbrev TouchingFreeFaceFace := Fin 9

def touchingFreeFaceFaces : Finset TouchingFreeFaceFace := Finset.univ

def touchingFreeFaceFaceBoundary :
    TouchingFreeFaceFace → Finset touchingFreeFaceGraph.edgeSet
  | ⟨0, _⟩ => {gtfO0, gtfP0}
  | ⟨1, _⟩ => {gtfP0}
  | ⟨2, _⟩ => {gtfI0}
  | ⟨3, _⟩ => {gtfO1, gtfP1}
  | ⟨4, _⟩ => {gtfP1}
  | ⟨5, _⟩ => {gtfI1}
  | ⟨6, _⟩ => {gtfO2, gtfP2}
  | ⟨7, _⟩ => {gtfP2}
  | ⟨8, _⟩ => {gtfI2}

theorem totalIncidenceCount_gtfO0 :
    totalIncidenceCount touchingFreeFaceFaceBoundary
      touchingFreeFaceFaces gtfO0 = 1 := by
  decide

theorem totalIncidenceCount_gtfP0 :
    totalIncidenceCount touchingFreeFaceFaceBoundary
      touchingFreeFaceFaces gtfP0 = 2 := by
  decide

theorem totalIncidenceCount_gtfI0 :
    totalIncidenceCount touchingFreeFaceFaceBoundary
      touchingFreeFaceFaces gtfI0 = 1 := by
  decide

theorem totalIncidenceCount_gtfO1 :
    totalIncidenceCount touchingFreeFaceFaceBoundary
      touchingFreeFaceFaces gtfO1 = 1 := by
  decide

theorem totalIncidenceCount_gtfP1 :
    totalIncidenceCount touchingFreeFaceFaceBoundary
      touchingFreeFaceFaces gtfP1 = 2 := by
  decide

theorem totalIncidenceCount_gtfI1 :
    totalIncidenceCount touchingFreeFaceFaceBoundary
      touchingFreeFaceFaces gtfI1 = 1 := by
  decide

theorem totalIncidenceCount_gtfO2 :
    totalIncidenceCount touchingFreeFaceFaceBoundary
      touchingFreeFaceFaces gtfO2 = 1 := by
  decide

theorem totalIncidenceCount_gtfP2 :
    totalIncidenceCount touchingFreeFaceFaceBoundary
      touchingFreeFaceFaces gtfP2 = 2 := by
  decide

theorem totalIncidenceCount_gtfI2 :
    totalIncidenceCount touchingFreeFaceFaceBoundary
      touchingFreeFaceFaces gtfI2 = 1 := by
  decide

def touchingFreeFaceEmbedding :
    PlaneEmbeddingWithBoundary touchingFreeFaceGraph where
  Face := TouchingFreeFaceFace
  faceDecidableEq := inferInstance
  faces := touchingFreeFaceFaces
  faceBoundary := touchingFreeFaceFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases touchingFreeFace_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases touchingFreeFace_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

theorem gtfO0_mem_selectedBoundarySupport :
    gtfO0 ∈ selectedBoundarySupport
      touchingFreeFaceEmbedding.faceBoundary
      touchingFreeFaceEmbedding.faces
      touchingFreeFaceEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gtfO0⟩

theorem gtfI0_mem_selectedBoundarySupport :
    gtfI0 ∈ selectedBoundarySupport
      touchingFreeFaceEmbedding.faceBoundary
      touchingFreeFaceEmbedding.faces
      touchingFreeFaceEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gtfI0⟩

theorem gtfO1_mem_selectedBoundarySupport :
    gtfO1 ∈ selectedBoundarySupport
      touchingFreeFaceEmbedding.faceBoundary
      touchingFreeFaceEmbedding.faces
      touchingFreeFaceEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gtfO1⟩

theorem gtfI1_mem_selectedBoundarySupport :
    gtfI1 ∈ selectedBoundarySupport
      touchingFreeFaceEmbedding.faceBoundary
      touchingFreeFaceEmbedding.faces
      touchingFreeFaceEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gtfI1⟩

theorem gtfO2_mem_selectedBoundarySupport :
    gtfO2 ∈ selectedBoundarySupport
      touchingFreeFaceEmbedding.faceBoundary
      touchingFreeFaceEmbedding.faces
      touchingFreeFaceEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gtfO2⟩

theorem gtfI2_mem_selectedBoundarySupport :
    gtfI2 ∈ selectedBoundarySupport
      touchingFreeFaceEmbedding.faceBoundary
      touchingFreeFaceEmbedding.faces
      touchingFreeFaceEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_gtfI2⟩

theorem gtfP0_not_mem_selectedBoundarySupport :
    gtfP0 ∉ selectedBoundarySupport
      touchingFreeFaceEmbedding.faceBoundary
      touchingFreeFaceEmbedding.faces
      touchingFreeFaceEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      touchingFreeFaceEmbedding.faceBoundary
      touchingFreeFaceEmbedding.faces
      touchingFreeFaceEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount touchingFreeFaceFaceBoundary
        touchingFreeFaceFaces gtfP0 = 1 := by
    simpa [touchingFreeFaceEmbedding] using hcount
  rw [totalIncidenceCount_gtfP0] at hcount'
  norm_num at hcount'

theorem gtfP1_not_mem_selectedBoundarySupport :
    gtfP1 ∉ selectedBoundarySupport
      touchingFreeFaceEmbedding.faceBoundary
      touchingFreeFaceEmbedding.faces
      touchingFreeFaceEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      touchingFreeFaceEmbedding.faceBoundary
      touchingFreeFaceEmbedding.faces
      touchingFreeFaceEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount touchingFreeFaceFaceBoundary
        touchingFreeFaceFaces gtfP1 = 1 := by
    simpa [touchingFreeFaceEmbedding] using hcount
  rw [totalIncidenceCount_gtfP1] at hcount'
  norm_num at hcount'

theorem gtfP2_not_mem_selectedBoundarySupport :
    gtfP2 ∉ selectedBoundarySupport
      touchingFreeFaceEmbedding.faceBoundary
      touchingFreeFaceEmbedding.faces
      touchingFreeFaceEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      touchingFreeFaceEmbedding.faceBoundary
      touchingFreeFaceEmbedding.faces
      touchingFreeFaceEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount touchingFreeFaceFaceBoundary
        touchingFreeFaceFaces gtfP2 = 1 := by
    simpa [touchingFreeFaceEmbedding] using hcount
  rw [totalIncidenceCount_gtfP2] at hcount'
  norm_num at hcount'

theorem touchingFreeFace_pathEdges_have_boundaryFree_incident_face :
    ∀ e ∈ ({gtfP0, gtfP1, gtfP2} : Finset touchingFreeFaceGraph.edgeSet),
      ∃ f ∈ touchingFreeFaceEmbedding.faces,
        e ∈ touchingFreeFaceEmbedding.faceBoundary f ∧
          ∀ b ∈ selectedBoundarySupport
              touchingFreeFaceEmbedding.faceBoundary
              touchingFreeFaceEmbedding.faces
              touchingFreeFaceEmbedding.faces,
            b ∉ touchingFreeFaceEmbedding.faceBoundary f := by
  intro e he
  rcases Finset.mem_insert.1 he with rfl | he
  · refine ⟨(1 : TouchingFreeFaceFace), by decide, by decide, ?_⟩
    intro b hb
    rcases touchingFreeFace_edge_eq b with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · exact False.elim (gtfP0_not_mem_selectedBoundarySupport hb)
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · rcases Finset.mem_insert.1 he with rfl | he
    · refine ⟨(4 : TouchingFreeFaceFace), by decide, by decide, ?_⟩
      intro b hb
      rcases touchingFreeFace_edge_eq b with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
      · exact False.elim (gtfP1_not_mem_selectedBoundarySupport hb)
      · decide
      · decide
      · decide
      · decide
    · have heP2 : e = gtfP2 := by simpa using he
      subst e
      refine ⟨(7 : TouchingFreeFaceFace), by decide, by decide, ?_⟩
      intro b hb
      rcases touchingFreeFace_edge_eq b with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · exact False.elim (gtfP2_not_mem_selectedBoundarySupport hb)
      · decide

theorem touchingFreeFace_pathEdges_touch_selectedBoundaryEndpoint :
    ∃ e ∈ ({gtfP0, gtfP1, gtfP2} : Finset touchingFreeFaceGraph.edgeSet),
      ∃ b ∈ selectedBoundarySupport
          touchingFreeFaceEmbedding.faceBoundary
          touchingFreeFaceEmbedding.faces
          touchingFreeFaceEmbedding.faces,
        ∃ v : Fin 15, v ∈ (e : Sym2 (Fin 15)) ∧ v ∈ (b : Sym2 (Fin 15)) := by
  exact ⟨gtfP0, by simp, gtfO0, gtfO0_mem_selectedBoundarySupport,
    1, by decide, by decide⟩

theorem not_touchingFreeFace_pathEdges_endpoint_no_touch_selectedBoundarySupport :
    ¬ (∀ e ∈ ({gtfP0, gtfP1, gtfP2} : Finset touchingFreeFaceGraph.edgeSet),
      ∀ b ∈ selectedBoundarySupport
          touchingFreeFaceEmbedding.faceBoundary
          touchingFreeFaceEmbedding.faces
          touchingFreeFaceEmbedding.faces,
        ¬ ∃ v : Fin 15, v ∈ (e : Sym2 (Fin 15)) ∧ v ∈ (b : Sym2 (Fin 15))) := by
  intro h
  exact h gtfP0 (by simp) gtfO0 gtfO0_mem_selectedBoundarySupport
    ⟨1, by decide, by decide⟩

theorem touchingFreeFace_purifiedCarrier_nonempty :
    ∃ v : Fin 15,
      (∃ e ∈ ({gtfP0, gtfP1, gtfP2} : Finset touchingFreeFaceGraph.edgeSet),
        v ∈ (e : Sym2 (Fin 15))) ∧
      ∀ b ∈ selectedBoundarySupport
          touchingFreeFaceEmbedding.faceBoundary
          touchingFreeFaceEmbedding.faces
          touchingFreeFaceEmbedding.faces,
        v ∉ (b : Sym2 (Fin 15)) := by
  refine ⟨2, ⟨⟨gtfP0, by simp, by decide⟩, ?_⟩⟩
  intro b hb
  rcases touchingFreeFace_edge_eq b with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · exact False.elim (gtfP0_not_mem_selectedBoundarySupport hb)
  · decide
  · decide
  · exact False.elim (gtfP1_not_mem_selectedBoundarySupport hb)
  · decide
  · decide
  · exact False.elim (gtfP2_not_mem_selectedBoundarySupport hb)
  · decide

theorem touchingFreeFace_boundaryFree_purifiedCarrier_not_endpointNoTouch :
    (∀ e ∈ ({gtfP0, gtfP1, gtfP2} : Finset touchingFreeFaceGraph.edgeSet),
      ∃ f ∈ touchingFreeFaceEmbedding.faces,
        e ∈ touchingFreeFaceEmbedding.faceBoundary f ∧
          ∀ b ∈ selectedBoundarySupport
              touchingFreeFaceEmbedding.faceBoundary
              touchingFreeFaceEmbedding.faces
              touchingFreeFaceEmbedding.faces,
            b ∉ touchingFreeFaceEmbedding.faceBoundary f) ∧
      (∃ v : Fin 15,
        (∃ e ∈ ({gtfP0, gtfP1, gtfP2} : Finset touchingFreeFaceGraph.edgeSet),
          v ∈ (e : Sym2 (Fin 15))) ∧
        ∀ b ∈ selectedBoundarySupport
            touchingFreeFaceEmbedding.faceBoundary
            touchingFreeFaceEmbedding.faces
            touchingFreeFaceEmbedding.faces,
          v ∉ (b : Sym2 (Fin 15))) ∧
      ¬ (∀ e ∈ ({gtfP0, gtfP1, gtfP2} : Finset touchingFreeFaceGraph.edgeSet),
        ∀ b ∈ selectedBoundarySupport
            touchingFreeFaceEmbedding.faceBoundary
            touchingFreeFaceEmbedding.faces
            touchingFreeFaceEmbedding.faces,
          ¬ ∃ v : Fin 15, v ∈ (e : Sym2 (Fin 15)) ∧ v ∈ (b : Sym2 (Fin 15))) := by
  exact ⟨touchingFreeFace_pathEdges_have_boundaryFree_incident_face,
    touchingFreeFace_purifiedCarrier_nonempty,
    not_touchingFreeFace_pathEdges_endpoint_no_touch_selectedBoundarySupport⟩

theorem touchingFreeFace_boundaryZero_no_evader_of_vanishes_on_pathEdges
    (z : touchingFreeFaceGraph.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule touchingFreeFaceEmbedding)
    (hcontrol :
      ∀ e ∈ ({gtfP0, gtfP1, gtfP2} : Finset touchingFreeFaceGraph.edgeSet), z e = 0) :
    z = 0 := by
  refine eq_zero_of_mem_planarBoundaryZeroSubmodule_of_control_or_boundary
    z hzBoundary ({gtfP0, gtfP1, gtfP2} : Finset touchingFreeFaceGraph.edgeSet)
    hcontrol ?_
  intro e
  rcases touchingFreeFace_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr gtfO0_mem_selectedBoundarySupport
  · exact Or.inl (by simp)
  · exact Or.inr gtfI0_mem_selectedBoundarySupport
  · exact Or.inr gtfO1_mem_selectedBoundarySupport
  · exact Or.inl (by simp)
  · exact Or.inr gtfI1_mem_selectedBoundarySupport
  · exact Or.inr gtfO2_mem_selectedBoundarySupport
  · exact Or.inl (by simp)
  · exact Or.inr gtfI2_mem_selectedBoundarySupport

/-! ## Positive two-collar toy survivor shell -/

def positiveTwoCollarToyGraph : SimpleGraph (Fin 9) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 0), s(6, 7), s(7, 8), s(8, 6),
        s(3, 4), s(4, 5), s(5, 3)} : Set (Sym2 (Fin 9)))

def ptcO01 : positiveTwoCollarToyGraph.edgeSet := ⟨s(0, 1), by
  simp [positiveTwoCollarToyGraph]⟩

def ptcO12 : positiveTwoCollarToyGraph.edgeSet := ⟨s(1, 2), by
  simp [positiveTwoCollarToyGraph]⟩

def ptcO20 : positiveTwoCollarToyGraph.edgeSet := ⟨s(2, 0), by
  simp [positiveTwoCollarToyGraph]⟩

def ptcI67 : positiveTwoCollarToyGraph.edgeSet := ⟨s(6, 7), by
  simp [positiveTwoCollarToyGraph]⟩

def ptcI78 : positiveTwoCollarToyGraph.edgeSet := ⟨s(7, 8), by
  simp [positiveTwoCollarToyGraph]⟩

def ptcI86 : positiveTwoCollarToyGraph.edgeSet := ⟨s(8, 6), by
  simp [positiveTwoCollarToyGraph]⟩

def ptcP34 : positiveTwoCollarToyGraph.edgeSet := ⟨s(3, 4), by
  simp [positiveTwoCollarToyGraph]⟩

def ptcP45 : positiveTwoCollarToyGraph.edgeSet := ⟨s(4, 5), by
  simp [positiveTwoCollarToyGraph]⟩

def ptcP53 : positiveTwoCollarToyGraph.edgeSet := ⟨s(5, 3), by
  simp [positiveTwoCollarToyGraph]⟩

@[simp] theorem ptcP34_ne_ptcP45 : ptcP34 ≠ ptcP45 := by
  decide

@[simp] theorem ptcP45_ne_ptcP34 : ptcP45 ≠ ptcP34 := by
  decide

@[simp] theorem ptcP34_ne_ptcP53 : ptcP34 ≠ ptcP53 := by
  decide

@[simp] theorem ptcP53_ne_ptcP34 : ptcP53 ≠ ptcP34 := by
  decide

@[simp] theorem ptcP45_ne_ptcP53 : ptcP45 ≠ ptcP53 := by
  decide

@[simp] theorem ptcP53_ne_ptcP45 : ptcP53 ≠ ptcP45 := by
  decide

theorem positiveTwoCollarToy_edge_eq
    (e : positiveTwoCollarToyGraph.edgeSet) :
    e = ptcO01 ∨ e = ptcO12 ∨ e = ptcO20 ∨ e = ptcI67 ∨ e = ptcI78 ∨
      e = ptcI86 ∨ e = ptcP34 ∨ e = ptcP45 ∨ e = ptcP53 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 0) ∨
          e.1 = s(6, 7) ∨ e.1 = s(7, 8) ∨ e.1 = s(8, 6) ∨
          e.1 = s(3, 4) ∨ e.1 = s(4, 5) ∨ e.1 = s(5, 3)) ∧
        ¬ e.1.IsDiag := by
    simpa [positiveTwoCollarToyGraph] using e.2
  rcases h.1 with hO01 | hO12 | hO20 | hI67 | hI78 | hI86 | hP34 | hP45 | hP53
  · exact Or.inl (Subtype.ext hO01)
  · exact Or.inr <| Or.inl (Subtype.ext hO12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext hO20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI67)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI78)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hI86)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hP34)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext hP45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr (Subtype.ext hP53)

noncomputable instance positiveTwoCollarToyGraph_edgeSet_fintype :
    Fintype positiveTwoCollarToyGraph.edgeSet :=
  ⟨{ptcO01, ptcO12, ptcO20, ptcI67, ptcI78, ptcI86, ptcP34, ptcP45, ptcP53}, by
    intro e
    rcases positiveTwoCollarToy_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp⟩

abbrev PositiveTwoCollarToyFace := Fin 6

def positiveTwoCollarToyFaces : Finset PositiveTwoCollarToyFace := Finset.univ

def positiveTwoCollarToyFaceBoundary :
    PositiveTwoCollarToyFace → Finset positiveTwoCollarToyGraph.edgeSet
  | ⟨0, _⟩ => {ptcO01, ptcO12, ptcO20}
  | ⟨1, _⟩ => {ptcI67, ptcI78, ptcI86}
  | ⟨2, _⟩ => {ptcP34}
  | ⟨3, _⟩ => {ptcP34, ptcP45}
  | ⟨4, _⟩ => {ptcP45, ptcP53}
  | ⟨5, _⟩ => {ptcP53}

theorem totalIncidenceCount_ptcO01 :
    totalIncidenceCount positiveTwoCollarToyFaceBoundary
      positiveTwoCollarToyFaces ptcO01 = 1 := by
  decide

theorem totalIncidenceCount_ptcO12 :
    totalIncidenceCount positiveTwoCollarToyFaceBoundary
      positiveTwoCollarToyFaces ptcO12 = 1 := by
  decide

theorem totalIncidenceCount_ptcO20 :
    totalIncidenceCount positiveTwoCollarToyFaceBoundary
      positiveTwoCollarToyFaces ptcO20 = 1 := by
  decide

theorem totalIncidenceCount_ptcI67 :
    totalIncidenceCount positiveTwoCollarToyFaceBoundary
      positiveTwoCollarToyFaces ptcI67 = 1 := by
  decide

theorem totalIncidenceCount_ptcI78 :
    totalIncidenceCount positiveTwoCollarToyFaceBoundary
      positiveTwoCollarToyFaces ptcI78 = 1 := by
  decide

theorem totalIncidenceCount_ptcI86 :
    totalIncidenceCount positiveTwoCollarToyFaceBoundary
      positiveTwoCollarToyFaces ptcI86 = 1 := by
  decide

theorem totalIncidenceCount_ptcP34 :
    totalIncidenceCount positiveTwoCollarToyFaceBoundary
      positiveTwoCollarToyFaces ptcP34 = 2 := by
  decide

theorem totalIncidenceCount_ptcP45 :
    totalIncidenceCount positiveTwoCollarToyFaceBoundary
      positiveTwoCollarToyFaces ptcP45 = 2 := by
  decide

theorem totalIncidenceCount_ptcP53 :
    totalIncidenceCount positiveTwoCollarToyFaceBoundary
      positiveTwoCollarToyFaces ptcP53 = 2 := by
  decide

def positiveTwoCollarToyEmbedding :
    PlaneEmbeddingWithBoundary positiveTwoCollarToyGraph where
  Face := PositiveTwoCollarToyFace
  faceDecidableEq := inferInstance
  faces := positiveTwoCollarToyFaces
  faceBoundary := positiveTwoCollarToyFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases positiveTwoCollarToy_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases positiveTwoCollarToy_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

theorem ptcO01_mem_selectedBoundarySupport :
    ptcO01 ∈ selectedBoundarySupport
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces
      positiveTwoCollarToyEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_ptcO01⟩

theorem ptcO12_mem_selectedBoundarySupport :
    ptcO12 ∈ selectedBoundarySupport
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces
      positiveTwoCollarToyEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_ptcO12⟩

theorem ptcO20_mem_selectedBoundarySupport :
    ptcO20 ∈ selectedBoundarySupport
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces
      positiveTwoCollarToyEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_ptcO20⟩

theorem ptcI67_mem_selectedBoundarySupport :
    ptcI67 ∈ selectedBoundarySupport
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces
      positiveTwoCollarToyEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_ptcI67⟩

theorem ptcI78_mem_selectedBoundarySupport :
    ptcI78 ∈ selectedBoundarySupport
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces
      positiveTwoCollarToyEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_ptcI78⟩

theorem ptcI86_mem_selectedBoundarySupport :
    ptcI86 ∈ selectedBoundarySupport
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces
      positiveTwoCollarToyEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_ptcI86⟩

theorem ptcP34_not_mem_selectedBoundarySupport :
    ptcP34 ∉ selectedBoundarySupport
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces
      positiveTwoCollarToyEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces
      positiveTwoCollarToyEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount positiveTwoCollarToyFaceBoundary
        positiveTwoCollarToyFaces ptcP34 = 1 := by
    simpa [positiveTwoCollarToyEmbedding] using hcount
  rw [totalIncidenceCount_ptcP34] at hcount'
  norm_num at hcount'

theorem ptcP45_not_mem_selectedBoundarySupport :
    ptcP45 ∉ selectedBoundarySupport
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces
      positiveTwoCollarToyEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces
      positiveTwoCollarToyEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount positiveTwoCollarToyFaceBoundary
        positiveTwoCollarToyFaces ptcP45 = 1 := by
    simpa [positiveTwoCollarToyEmbedding] using hcount
  rw [totalIncidenceCount_ptcP45] at hcount'
  norm_num at hcount'

theorem ptcP53_not_mem_selectedBoundarySupport :
    ptcP53 ∉ selectedBoundarySupport
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces
      positiveTwoCollarToyEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces
      positiveTwoCollarToyEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount positiveTwoCollarToyFaceBoundary
        positiveTwoCollarToyFaces ptcP53 = 1 := by
    simpa [positiveTwoCollarToyEmbedding] using hcount
  rw [totalIncidenceCount_ptcP53] at hcount'
  norm_num at hcount'

theorem ptcP34_mem_interiorEdgeSupport :
    ptcP34 ∈ interiorEdgeSupport
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_ptcP34⟩

theorem ptcP45_mem_interiorEdgeSupport :
    ptcP45 ∈ interiorEdgeSupport
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_ptcP45⟩

theorem ptcP53_mem_interiorEdgeSupport :
    ptcP53 ∈ interiorEdgeSupport
      positiveTwoCollarToyEmbedding.faceBoundary
      positiveTwoCollarToyEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_ptcP53⟩

theorem positiveTwoCollarToy_interiorEdgeSupport_eq :
    interiorEdgeSupport
        positiveTwoCollarToyEmbedding.faceBoundary
        positiveTwoCollarToyEmbedding.faces =
      ({ptcP34, ptcP45, ptcP53} : Finset positiveTwoCollarToyGraph.edgeSet) := by
  ext e
  rcases positiveTwoCollarToy_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

def ptcFace0 : AmbientFace positiveTwoCollarToyEmbedding.faces :=
  ⟨(0 : PositiveTwoCollarToyFace), by decide⟩

def ptcFace1 : AmbientFace positiveTwoCollarToyEmbedding.faces :=
  ⟨(1 : PositiveTwoCollarToyFace), by decide⟩

def ptcFace2 : AmbientFace positiveTwoCollarToyEmbedding.faces :=
  ⟨(2 : PositiveTwoCollarToyFace), by decide⟩

def ptcFace3 : AmbientFace positiveTwoCollarToyEmbedding.faces :=
  ⟨(3 : PositiveTwoCollarToyFace), by decide⟩

def ptcFace4 : AmbientFace positiveTwoCollarToyEmbedding.faces :=
  ⟨(4 : PositiveTwoCollarToyFace), by decide⟩

def ptcFace5 : AmbientFace positiveTwoCollarToyEmbedding.faces :=
  ⟨(5 : PositiveTwoCollarToyFace), by decide⟩

def positiveTwoCollarToyPeelFaces :
    Finset (AmbientFace positiveTwoCollarToyEmbedding.faces) :=
  {ptcFace2, ptcFace3, ptcFace4}

def positiveTwoCollarToyWitnessEdge
    (f : AmbientFace positiveTwoCollarToyEmbedding.faces) :
    positiveTwoCollarToyGraph.edgeSet :=
  if f = ptcFace2 then ptcP34
  else if f = ptcFace3 then ptcP45
  else if f = ptcFace4 then ptcP53
  else ptcP34

def positiveTwoCollarToyHeight
    (f : AmbientFace positiveTwoCollarToyEmbedding.faces) : ℕ :=
  if f = ptcFace2 then 2
  else if f = ptcFace3 then 1
  else 0

theorem positiveTwoCollarToy_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData :
    Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          positiveTwoCollarToyEmbedding) := by
  refine ⟨{ peelFaces := positiveTwoCollarToyPeelFaces
            witnessEdge := positiveTwoCollarToyWitnessEdge
            height := positiveTwoCollarToyHeight
            hcover := by
              intro e he
              revert he
              rcases positiveTwoCollarToy_edge_eq e with
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                decide
            hwitness := by
              decide
            hrest := by
              decide }⟩

theorem positiveTwoCollarToy_pathEdges_have_boundaryFree_incident_face :
    ∀ e ∈ ({ptcP34, ptcP45, ptcP53} : Finset positiveTwoCollarToyGraph.edgeSet),
      ∃ f ∈ positiveTwoCollarToyEmbedding.faces,
        e ∈ positiveTwoCollarToyEmbedding.faceBoundary f ∧
          ∀ b ∈ selectedBoundarySupport
              positiveTwoCollarToyEmbedding.faceBoundary
              positiveTwoCollarToyEmbedding.faces
              positiveTwoCollarToyEmbedding.faces,
            b ∉ positiveTwoCollarToyEmbedding.faceBoundary f := by
  intro e he
  rcases Finset.mem_insert.1 he with rfl | he
  · refine ⟨(2 : PositiveTwoCollarToyFace), by decide, by decide, ?_⟩
    intro b hb
    rcases positiveTwoCollarToy_edge_eq b with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact False.elim (ptcP34_not_mem_selectedBoundarySupport hb)
    · decide
    · decide
  · rcases Finset.mem_insert.1 he with rfl | he
    · refine ⟨(3 : PositiveTwoCollarToyFace), by decide, by decide, ?_⟩
      intro b hb
      rcases positiveTwoCollarToy_edge_eq b with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · exact False.elim (ptcP34_not_mem_selectedBoundarySupport hb)
      · exact False.elim (ptcP45_not_mem_selectedBoundarySupport hb)
      · decide
    · have heP53 : e = ptcP53 := by simpa using he
      subst e
      refine ⟨(5 : PositiveTwoCollarToyFace), by decide, by decide, ?_⟩
      intro b hb
      rcases positiveTwoCollarToy_edge_eq b with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · exact False.elim (ptcP53_not_mem_selectedBoundarySupport hb)

theorem positiveTwoCollarToy_pathEdges_endpoint_no_touch_selectedBoundarySupport :
    ∀ e ∈ ({ptcP34, ptcP45, ptcP53} : Finset positiveTwoCollarToyGraph.edgeSet),
      ∀ b ∈ selectedBoundarySupport
          positiveTwoCollarToyEmbedding.faceBoundary
          positiveTwoCollarToyEmbedding.faces
          positiveTwoCollarToyEmbedding.faces,
        ¬ ∃ v : Fin 9, v ∈ (e : Sym2 (Fin 9)) ∧ v ∈ (b : Sym2 (Fin 9)) := by
  decide

theorem positiveTwoCollarToy_purifiedCarrier_nonempty :
    ∃ v : Fin 9,
      (∃ e ∈ ({ptcP34, ptcP45, ptcP53} : Finset positiveTwoCollarToyGraph.edgeSet),
        v ∈ (e : Sym2 (Fin 9))) ∧
      ∀ b ∈ selectedBoundarySupport
          positiveTwoCollarToyEmbedding.faceBoundary
          positiveTwoCollarToyEmbedding.faces
          positiveTwoCollarToyEmbedding.faces,
        v ∉ (b : Sym2 (Fin 9)) := by
  refine ⟨3, ⟨⟨ptcP34, by simp, by decide⟩, ?_⟩⟩
  intro b hb
  rcases positiveTwoCollarToy_edge_eq b with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact False.elim (ptcP34_not_mem_selectedBoundarySupport hb)
  · exact False.elim (ptcP45_not_mem_selectedBoundarySupport hb)
  · exact False.elim (ptcP53_not_mem_selectedBoundarySupport hb)

theorem positiveTwoCollarToy_boundaryFree_endpointNoTouch_purifiedCarrier :
    (∀ e ∈ ({ptcP34, ptcP45, ptcP53} : Finset positiveTwoCollarToyGraph.edgeSet),
      ∃ f ∈ positiveTwoCollarToyEmbedding.faces,
        e ∈ positiveTwoCollarToyEmbedding.faceBoundary f ∧
          ∀ b ∈ selectedBoundarySupport
              positiveTwoCollarToyEmbedding.faceBoundary
              positiveTwoCollarToyEmbedding.faces
              positiveTwoCollarToyEmbedding.faces,
            b ∉ positiveTwoCollarToyEmbedding.faceBoundary f) ∧
      (∀ e ∈ ({ptcP34, ptcP45, ptcP53} : Finset positiveTwoCollarToyGraph.edgeSet),
        ∀ b ∈ selectedBoundarySupport
            positiveTwoCollarToyEmbedding.faceBoundary
            positiveTwoCollarToyEmbedding.faces
            positiveTwoCollarToyEmbedding.faces,
          ¬ ∃ v : Fin 9, v ∈ (e : Sym2 (Fin 9)) ∧ v ∈ (b : Sym2 (Fin 9))) ∧
      (∃ v : Fin 9,
        (∃ e ∈ ({ptcP34, ptcP45, ptcP53} : Finset positiveTwoCollarToyGraph.edgeSet),
          v ∈ (e : Sym2 (Fin 9))) ∧
        ∀ b ∈ selectedBoundarySupport
            positiveTwoCollarToyEmbedding.faceBoundary
            positiveTwoCollarToyEmbedding.faces
            positiveTwoCollarToyEmbedding.faces,
          v ∉ (b : Sym2 (Fin 9))) := by
  exact ⟨positiveTwoCollarToy_pathEdges_have_boundaryFree_incident_face,
    positiveTwoCollarToy_pathEdges_endpoint_no_touch_selectedBoundarySupport,
    positiveTwoCollarToy_purifiedCarrier_nonempty⟩

theorem positiveTwoCollarToy_boundaryZero_no_evader_of_vanishes_on_pathEdges
    (z : positiveTwoCollarToyGraph.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule positiveTwoCollarToyEmbedding)
    (hcontrol :
      ∀ e ∈ ({ptcP34, ptcP45, ptcP53} : Finset positiveTwoCollarToyGraph.edgeSet), z e = 0) :
    z = 0 := by
  refine eq_zero_of_mem_planarBoundaryZeroSubmodule_of_control_or_boundary
    z hzBoundary ({ptcP34, ptcP45, ptcP53} : Finset positiveTwoCollarToyGraph.edgeSet)
    hcontrol ?_
  intro e
  rcases positiveTwoCollarToy_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ptcO01_mem_selectedBoundarySupport
  · exact Or.inr ptcO12_mem_selectedBoundarySupport
  · exact Or.inr ptcO20_mem_selectedBoundarySupport
  · exact Or.inr ptcI67_mem_selectedBoundarySupport
  · exact Or.inr ptcI78_mem_selectedBoundarySupport
  · exact Or.inr ptcI86_mem_selectedBoundarySupport
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)

def positiveTwoCollarToyKirchhoffVertices : Finset (Fin 9) :=
  {(3 : Fin 9), 4, 5}

theorem positiveTwoCollarToy_incidentEdgeFinset_three :
    incidentEdgeFinset positiveTwoCollarToyGraph (3 : Fin 9) = {ptcP34, ptcP53} := by
  ext e
  rcases positiveTwoCollarToy_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem positiveTwoCollarToy_incidentEdgeFinset_four :
    incidentEdgeFinset positiveTwoCollarToyGraph (4 : Fin 9) = {ptcP34, ptcP45} := by
  ext e
  rcases positiveTwoCollarToy_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem positiveTwoCollarToy_incidentEdgeFinset_five :
    incidentEdgeFinset positiveTwoCollarToyGraph (5 : Fin 9) = {ptcP45, ptcP53} := by
  ext e
  rcases positiveTwoCollarToy_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem positiveTwoCollarToy_vertexKirchhoffSum_three
    (z : positiveTwoCollarToyGraph.edgeSet → Color) :
    vertexKirchhoffSum positiveTwoCollarToyGraph z (3 : Fin 9) =
      z ptcP34 + z ptcP53 := by
  unfold vertexKirchhoffSum
  rw [positiveTwoCollarToy_incidentEdgeFinset_three]
  simp

theorem positiveTwoCollarToy_vertexKirchhoffSum_four
    (z : positiveTwoCollarToyGraph.edgeSet → Color) :
    vertexKirchhoffSum positiveTwoCollarToyGraph z (4 : Fin 9) =
      z ptcP34 + z ptcP45 := by
  unfold vertexKirchhoffSum
  rw [positiveTwoCollarToy_incidentEdgeFinset_four]
  simp

theorem positiveTwoCollarToy_vertexKirchhoffSum_five
    (z : positiveTwoCollarToyGraph.edgeSet → Color) :
    vertexKirchhoffSum positiveTwoCollarToyGraph z (5 : Fin 9) =
      z ptcP45 + z ptcP53 := by
  unfold vertexKirchhoffSum
  rw [positiveTwoCollarToy_incidentEdgeFinset_five]
  simp

theorem positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_pathEdge_values
    (z : positiveTwoCollarToyGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      positiveTwoCollarToyEmbedding positiveTwoCollarToyKirchhoffVertices)
    (hptcP34 : z ptcP34 = 0) (hptcP45 : z ptcP45 = 0) (hptcP53 : z ptcP53 = 0) :
    z = 0 := by
  apply positiveTwoCollarToy_boundaryZero_no_evader_of_vanishes_on_pathEdges
  · exact theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
      positiveTwoCollarToyEmbedding positiveTwoCollarToyKirchhoffVertices hz
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hptcP34
    · rcases Finset.mem_insert.1 he with rfl | he
      · exact hptcP45
      · have heP53 : e = ptcP53 := by simpa using he
        subst e
        exact hptcP53

theorem positiveTwoCollarToy_boundaryZeroKirchhoff_controlEdges_interiorEdges :
    ∀ ⦃z : positiveTwoCollarToyGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          positiveTwoCollarToyEmbedding positiveTwoCollarToyKirchhoffVertices →
      (∀ e ∈ ({ptcP34, ptcP45, ptcP53} :
        Finset positiveTwoCollarToyGraph.edgeSet), z e = 0) →
        z = 0 := by
  intro z hz hcontrol
  refine
    eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport
      z hz ?_
  intro e he
  exact hcontrol e (by
    simpa [positiveTwoCollarToy_interiorEdgeSupport_eq] using he)

theorem positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_vanishes_on_ptcP34
    (z : positiveTwoCollarToyGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      positiveTwoCollarToyEmbedding positiveTwoCollarToyKirchhoffVertices)
    (hptcP34 : z ptcP34 = 0) :
    z = 0 := by
  have hptcP45 : z ptcP45 = 0 := by
    have hkirch :=
      kirchhoff_of_mem_theorem49BoundaryZeroKirchhoffSubspace
        (emb := positiveTwoCollarToyEmbedding)
        (vertices := positiveTwoCollarToyKirchhoffVertices)
        hz (4 : Fin 9) (by simp [positiveTwoCollarToyKirchhoffVertices])
    rw [positiveTwoCollarToy_vertexKirchhoffSum_four] at hkirch
    simpa [hptcP34] using hkirch
  have hptcP53 : z ptcP53 = 0 := by
    have hkirch :=
      kirchhoff_of_mem_theorem49BoundaryZeroKirchhoffSubspace
        (emb := positiveTwoCollarToyEmbedding)
        (vertices := positiveTwoCollarToyKirchhoffVertices)
        hz (3 : Fin 9) (by simp [positiveTwoCollarToyKirchhoffVertices])
    rw [positiveTwoCollarToy_vertexKirchhoffSum_three] at hkirch
    simpa [hptcP34] using hkirch
  exact positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_pathEdge_values
    z hz hptcP34 hptcP45 hptcP53

theorem positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_vanishes_on_ptcP45
    (z : positiveTwoCollarToyGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      positiveTwoCollarToyEmbedding positiveTwoCollarToyKirchhoffVertices)
    (hptcP45 : z ptcP45 = 0) :
    z = 0 := by
  have hptcP34 : z ptcP34 = 0 := by
    have hkirch :=
      kirchhoff_of_mem_theorem49BoundaryZeroKirchhoffSubspace
        (emb := positiveTwoCollarToyEmbedding)
        (vertices := positiveTwoCollarToyKirchhoffVertices)
        hz (4 : Fin 9) (by simp [positiveTwoCollarToyKirchhoffVertices])
    rw [positiveTwoCollarToy_vertexKirchhoffSum_four] at hkirch
    simpa [hptcP45] using hkirch
  have hptcP53 : z ptcP53 = 0 := by
    have hkirch :=
      kirchhoff_of_mem_theorem49BoundaryZeroKirchhoffSubspace
        (emb := positiveTwoCollarToyEmbedding)
        (vertices := positiveTwoCollarToyKirchhoffVertices)
        hz (5 : Fin 9) (by simp [positiveTwoCollarToyKirchhoffVertices])
    rw [positiveTwoCollarToy_vertexKirchhoffSum_five] at hkirch
    simpa [hptcP45] using hkirch
  exact positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_pathEdge_values
    z hz hptcP34 hptcP45 hptcP53

theorem positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_vanishes_on_ptcP53
    (z : positiveTwoCollarToyGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      positiveTwoCollarToyEmbedding positiveTwoCollarToyKirchhoffVertices)
    (hptcP53 : z ptcP53 = 0) :
    z = 0 := by
  have hptcP34 : z ptcP34 = 0 := by
    have hkirch :=
      kirchhoff_of_mem_theorem49BoundaryZeroKirchhoffSubspace
        (emb := positiveTwoCollarToyEmbedding)
        (vertices := positiveTwoCollarToyKirchhoffVertices)
        hz (3 : Fin 9) (by simp [positiveTwoCollarToyKirchhoffVertices])
    rw [positiveTwoCollarToy_vertexKirchhoffSum_three] at hkirch
    simpa [hptcP53] using hkirch
  have hptcP45 : z ptcP45 = 0 := by
    have hkirch :=
      kirchhoff_of_mem_theorem49BoundaryZeroKirchhoffSubspace
        (emb := positiveTwoCollarToyEmbedding)
        (vertices := positiveTwoCollarToyKirchhoffVertices)
        hz (5 : Fin 9) (by simp [positiveTwoCollarToyKirchhoffVertices])
    rw [positiveTwoCollarToy_vertexKirchhoffSum_five] at hkirch
    simpa [hptcP53] using hkirch
  exact positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_pathEdge_values
    z hz hptcP34 hptcP45 hptcP53

theorem positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_vanishes_on_ptcP34_ptcP45
    (z : positiveTwoCollarToyGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      positiveTwoCollarToyEmbedding positiveTwoCollarToyKirchhoffVertices)
    (hptcP34 : z ptcP34 = 0) (hptcP45 : z ptcP45 = 0) :
    z = 0 := by
  have hptcP53 : z ptcP53 = 0 := by
    have hkirch :=
      kirchhoff_of_mem_theorem49BoundaryZeroKirchhoffSubspace
        (emb := positiveTwoCollarToyEmbedding)
        (vertices := positiveTwoCollarToyKirchhoffVertices)
        hz (3 : Fin 9) (by simp [positiveTwoCollarToyKirchhoffVertices])
    rw [positiveTwoCollarToy_vertexKirchhoffSum_three] at hkirch
    simpa [hptcP34] using hkirch
  exact positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_pathEdge_values
    z hz hptcP34 hptcP45 hptcP53

theorem positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_vanishes_on_ptcP34_ptcP53
    (z : positiveTwoCollarToyGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      positiveTwoCollarToyEmbedding positiveTwoCollarToyKirchhoffVertices)
    (hptcP34 : z ptcP34 = 0) (hptcP53 : z ptcP53 = 0) :
    z = 0 := by
  have hptcP45 : z ptcP45 = 0 := by
    have hkirch :=
      kirchhoff_of_mem_theorem49BoundaryZeroKirchhoffSubspace
        (emb := positiveTwoCollarToyEmbedding)
        (vertices := positiveTwoCollarToyKirchhoffVertices)
        hz (4 : Fin 9) (by simp [positiveTwoCollarToyKirchhoffVertices])
    rw [positiveTwoCollarToy_vertexKirchhoffSum_four] at hkirch
    simpa [hptcP34] using hkirch
  exact positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_pathEdge_values
    z hz hptcP34 hptcP45 hptcP53

theorem positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_vanishes_on_ptcP45_ptcP53
    (z : positiveTwoCollarToyGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      positiveTwoCollarToyEmbedding positiveTwoCollarToyKirchhoffVertices)
    (hptcP45 : z ptcP45 = 0) (hptcP53 : z ptcP53 = 0) :
    z = 0 := by
  have hptcP34 : z ptcP34 = 0 := by
    have hkirch :=
      kirchhoff_of_mem_theorem49BoundaryZeroKirchhoffSubspace
        (emb := positiveTwoCollarToyEmbedding)
        (vertices := positiveTwoCollarToyKirchhoffVertices)
        hz (4 : Fin 9) (by simp [positiveTwoCollarToyKirchhoffVertices])
    rw [positiveTwoCollarToy_vertexKirchhoffSum_four] at hkirch
    simpa [hptcP45] using hkirch
  exact positiveTwoCollarToy_boundaryZeroKirchhoff_no_evader_of_pathEdge_values
    z hz hptcP34 hptcP45 hptcP53

/-! ## Two-band annulus stress shell -/

def twoBandAnnulusGraph : SimpleGraph (Fin 9) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 0), s(6, 7), s(7, 8), s(8, 6),
        s(0, 3), s(1, 4), s(2, 5), s(3, 6), s(4, 7), s(5, 8),
        s(3, 4), s(4, 5), s(5, 3)} : Set (Sym2 (Fin 9)))

def tbaO01 : twoBandAnnulusGraph.edgeSet := ⟨s(0, 1), by
  simp [twoBandAnnulusGraph]⟩

def tbaO12 : twoBandAnnulusGraph.edgeSet := ⟨s(1, 2), by
  simp [twoBandAnnulusGraph]⟩

def tbaO20 : twoBandAnnulusGraph.edgeSet := ⟨s(2, 0), by
  simp [twoBandAnnulusGraph]⟩

def tbaI67 : twoBandAnnulusGraph.edgeSet := ⟨s(6, 7), by
  simp [twoBandAnnulusGraph]⟩

def tbaI78 : twoBandAnnulusGraph.edgeSet := ⟨s(7, 8), by
  simp [twoBandAnnulusGraph]⟩

def tbaI86 : twoBandAnnulusGraph.edgeSet := ⟨s(8, 6), by
  simp [twoBandAnnulusGraph]⟩

def tbaR03 : twoBandAnnulusGraph.edgeSet := ⟨s(0, 3), by
  simp [twoBandAnnulusGraph]⟩

def tbaR14 : twoBandAnnulusGraph.edgeSet := ⟨s(1, 4), by
  simp [twoBandAnnulusGraph]⟩

def tbaR25 : twoBandAnnulusGraph.edgeSet := ⟨s(2, 5), by
  simp [twoBandAnnulusGraph]⟩

def tbaR36 : twoBandAnnulusGraph.edgeSet := ⟨s(3, 6), by
  simp [twoBandAnnulusGraph]⟩

def tbaR47 : twoBandAnnulusGraph.edgeSet := ⟨s(4, 7), by
  simp [twoBandAnnulusGraph]⟩

def tbaR58 : twoBandAnnulusGraph.edgeSet := ⟨s(5, 8), by
  simp [twoBandAnnulusGraph]⟩

def tbaM34 : twoBandAnnulusGraph.edgeSet := ⟨s(3, 4), by
  simp [twoBandAnnulusGraph]⟩

def tbaM45 : twoBandAnnulusGraph.edgeSet := ⟨s(4, 5), by
  simp [twoBandAnnulusGraph]⟩

def tbaM53 : twoBandAnnulusGraph.edgeSet := ⟨s(5, 3), by
  simp [twoBandAnnulusGraph]⟩

theorem twoBandAnnulus_edge_eq
    (e : twoBandAnnulusGraph.edgeSet) :
    e = tbaO01 ∨ e = tbaO12 ∨ e = tbaO20 ∨ e = tbaI67 ∨ e = tbaI78 ∨
      e = tbaI86 ∨ e = tbaR03 ∨ e = tbaR14 ∨ e = tbaR25 ∨ e = tbaR36 ∨
      e = tbaR47 ∨ e = tbaR58 ∨ e = tbaM34 ∨ e = tbaM45 ∨ e = tbaM53 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 0) ∨
          e.1 = s(6, 7) ∨ e.1 = s(7, 8) ∨ e.1 = s(8, 6) ∨
          e.1 = s(0, 3) ∨ e.1 = s(1, 4) ∨ e.1 = s(2, 5) ∨
          e.1 = s(3, 6) ∨ e.1 = s(4, 7) ∨ e.1 = s(5, 8) ∨
          e.1 = s(3, 4) ∨ e.1 = s(4, 5) ∨ e.1 = s(5, 3)) ∧
        ¬ e.1.IsDiag := by
    simpa [twoBandAnnulusGraph] using e.2
  rcases h.1 with
    hO01 | hO12 | hO20 | hI67 | hI78 | hI86 | hR03 | hR14 | hR25 | hR36 |
    hR47 | hR58 | hM34 | hM45 | hM53
  · exact Or.inl (Subtype.ext hO01)
  · exact Or.inr <| Or.inl (Subtype.ext hO12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext hO20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI67)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI78)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hI86)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hR03)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext hR14)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inl (Subtype.ext hR25)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hR36)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hR47)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hR58)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hM34)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hM45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      (Subtype.ext hM53)

noncomputable instance twoBandAnnulusGraph_edgeSet_fintype :
    Fintype twoBandAnnulusGraph.edgeSet :=
  ⟨{tbaO01, tbaO12, tbaO20, tbaI67, tbaI78, tbaI86, tbaR03, tbaR14, tbaR25,
      tbaR36, tbaR47, tbaR58, tbaM34, tbaM45, tbaM53}, by
    intro e
    rcases twoBandAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> simp⟩

def twoBandAnnulusInteriorEdges : Finset twoBandAnnulusGraph.edgeSet :=
  {tbaR03, tbaR14, tbaR25, tbaR36, tbaR47, tbaR58, tbaM34, tbaM45, tbaM53}

def twoBandAnnulusOuterBoundarySet : Finset twoBandAnnulusGraph.edgeSet :=
  {tbaO01, tbaO12, tbaO20}

def twoBandAnnulusInnerBoundarySet : Finset twoBandAnnulusGraph.edgeSet :=
  {tbaI67, tbaI78, tbaI86}

abbrev TwoBandAnnulusFace := Fin 6

def twoBandAnnulusFaces : Finset TwoBandAnnulusFace := Finset.univ

def twoBandAnnulusFaceBoundary :
    TwoBandAnnulusFace → Finset twoBandAnnulusGraph.edgeSet
  | ⟨0, _⟩ => {tbaO01, tbaR14, tbaM34, tbaR03}
  | ⟨1, _⟩ => {tbaO12, tbaR25, tbaM45, tbaR14}
  | ⟨2, _⟩ => {tbaO20, tbaR03, tbaM53, tbaR25}
  | ⟨3, _⟩ => {tbaM34, tbaR47, tbaI67, tbaR36}
  | ⟨4, _⟩ => {tbaM45, tbaR58, tbaI78, tbaR47}
  | ⟨5, _⟩ => {tbaM53, tbaR36, tbaI86, tbaR58}

theorem totalIncidenceCount_tbaO01 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaO01 = 1 := by
  decide

theorem totalIncidenceCount_tbaO12 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaO12 = 1 := by
  decide

theorem totalIncidenceCount_tbaO20 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaO20 = 1 := by
  decide

theorem totalIncidenceCount_tbaI67 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaI67 = 1 := by
  decide

theorem totalIncidenceCount_tbaI78 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaI78 = 1 := by
  decide

theorem totalIncidenceCount_tbaI86 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaI86 = 1 := by
  decide

theorem totalIncidenceCount_tbaR03 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaR03 = 2 := by
  decide

theorem totalIncidenceCount_tbaR14 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaR14 = 2 := by
  decide

theorem totalIncidenceCount_tbaR25 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaR25 = 2 := by
  decide

theorem totalIncidenceCount_tbaR36 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaR36 = 2 := by
  decide

theorem totalIncidenceCount_tbaR47 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaR47 = 2 := by
  decide

theorem totalIncidenceCount_tbaR58 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaR58 = 2 := by
  decide

theorem totalIncidenceCount_tbaM34 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaM34 = 2 := by
  decide

theorem totalIncidenceCount_tbaM45 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaM45 = 2 := by
  decide

theorem totalIncidenceCount_tbaM53 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaM53 = 2 := by
  decide

def twoBandAnnulusEmbedding :
    PlaneEmbeddingWithBoundary twoBandAnnulusGraph where
  Face := TwoBandAnnulusFace
  faceDecidableEq := inferInstance
  faces := twoBandAnnulusFaces
  faceBoundary := twoBandAnnulusFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases twoBandAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases twoBandAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
      decide

theorem tbaO01_mem_selectedBoundarySupport :
    tbaO01 ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_tbaO01⟩

theorem tbaO12_mem_selectedBoundarySupport :
    tbaO12 ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_tbaO12⟩

theorem tbaO20_mem_selectedBoundarySupport :
    tbaO20 ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_tbaO20⟩

theorem tbaI67_mem_selectedBoundarySupport :
    tbaI67 ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_tbaI67⟩

theorem tbaI78_mem_selectedBoundarySupport :
    tbaI78 ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_tbaI78⟩

theorem tbaI86_mem_selectedBoundarySupport :
    tbaI86 ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_tbaI86⟩

theorem twoBandAnnulus_selectedBoundarySupport_eq :
    selectedBoundarySupport
        twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces
        twoBandAnnulusEmbedding.faces =
      ({tbaO01, tbaO12, tbaO20, tbaI67, tbaI78, tbaI86} :
        Finset twoBandAnnulusGraph.edgeSet) := by
  ext e
  rcases twoBandAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    decide

def tbaDart01 : twoBandAnnulusGraph.Dart := ⟨((0 : Fin 9), 1), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart14 : twoBandAnnulusGraph.Dart := ⟨((1 : Fin 9), 4), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart43 : twoBandAnnulusGraph.Dart := ⟨((4 : Fin 9), 3), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart30 : twoBandAnnulusGraph.Dart := ⟨((3 : Fin 9), 0), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart12 : twoBandAnnulusGraph.Dart := ⟨((1 : Fin 9), 2), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart25 : twoBandAnnulusGraph.Dart := ⟨((2 : Fin 9), 5), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart54 : twoBandAnnulusGraph.Dart := ⟨((5 : Fin 9), 4), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart41 : twoBandAnnulusGraph.Dart := ⟨((4 : Fin 9), 1), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart20 : twoBandAnnulusGraph.Dart := ⟨((2 : Fin 9), 0), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart03 : twoBandAnnulusGraph.Dart := ⟨((0 : Fin 9), 3), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart35 : twoBandAnnulusGraph.Dart := ⟨((3 : Fin 9), 5), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart52 : twoBandAnnulusGraph.Dart := ⟨((5 : Fin 9), 2), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart34 : twoBandAnnulusGraph.Dart := ⟨((3 : Fin 9), 4), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart47 : twoBandAnnulusGraph.Dart := ⟨((4 : Fin 9), 7), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart76 : twoBandAnnulusGraph.Dart := ⟨((7 : Fin 9), 6), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart63 : twoBandAnnulusGraph.Dart := ⟨((6 : Fin 9), 3), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart45 : twoBandAnnulusGraph.Dart := ⟨((4 : Fin 9), 5), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart58 : twoBandAnnulusGraph.Dart := ⟨((5 : Fin 9), 8), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart87 : twoBandAnnulusGraph.Dart := ⟨((8 : Fin 9), 7), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart74 : twoBandAnnulusGraph.Dart := ⟨((7 : Fin 9), 4), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart53 : twoBandAnnulusGraph.Dart := ⟨((5 : Fin 9), 3), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart36 : twoBandAnnulusGraph.Dart := ⟨((3 : Fin 9), 6), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart68 : twoBandAnnulusGraph.Dart := ⟨((6 : Fin 9), 8), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart85 : twoBandAnnulusGraph.Dart := ⟨((8 : Fin 9), 5), by
  simp [twoBandAnnulusGraph]⟩

macro "tba_dart_cycle" : tactic =>
  `(tactic| simp [SimpleGraph.DartAdj, tbaDart01, tbaDart14, tbaDart43, tbaDart30,
    tbaDart12, tbaDart25, tbaDart54, tbaDart41, tbaDart20, tbaDart03, tbaDart35,
    tbaDart52, tbaDart34, tbaDart47, tbaDart76, tbaDart63, tbaDart45, tbaDart58,
    tbaDart87, tbaDart74, tbaDart53, tbaDart36, tbaDart68, tbaDart85])

def twoBandAnnulusFace0PureDartCycle
    (hf : (0 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoBandAnnulusEmbedding ⟨(0 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart01, tbaDart14, tbaDart43, tbaDart30]
  hnonempty := by simp
  hclosed := by tba_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary, tbaO01, tbaR14,
        tbaM34, tbaR03, tbaDart01, tbaDart14, tbaDart43, tbaDart30]
  hface_sub := by
    intro e he
    have he' : e = tbaO01 ∨ e = tbaR14 ∨ e = tbaM34 ∨ e = tbaR03 := by
      simpa [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [tbaO01, tbaR14, tbaM34, tbaR03, tbaDart01, tbaDart14,
        tbaDart43, tbaDart30]

def twoBandAnnulusFace1PureDartCycle
    (hf : (1 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoBandAnnulusEmbedding ⟨(1 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart12, tbaDart25, tbaDart54, tbaDart41]
  hnonempty := by simp
  hclosed := by tba_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary, tbaO12, tbaR25,
        tbaM45, tbaR14, tbaDart12, tbaDart25, tbaDart54, tbaDart41]
  hface_sub := by
    intro e he
    have he' : e = tbaO12 ∨ e = tbaR25 ∨ e = tbaM45 ∨ e = tbaR14 := by
      simpa [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [tbaO12, tbaR25, tbaM45, tbaR14, tbaDart12, tbaDart25,
        tbaDart54, tbaDart41]

def twoBandAnnulusFace2PureDartCycle
    (hf : (2 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoBandAnnulusEmbedding ⟨(2 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart20, tbaDart03, tbaDart35, tbaDart52]
  hnonempty := by simp
  hclosed := by tba_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary, tbaO20, tbaR03,
        tbaM53, tbaR25, tbaDart20, tbaDart03, tbaDart35, tbaDart52]
  hface_sub := by
    intro e he
    have he' : e = tbaO20 ∨ e = tbaR03 ∨ e = tbaM53 ∨ e = tbaR25 := by
      simpa [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [tbaO20, tbaR03, tbaM53, tbaR25, tbaDart20, tbaDart03,
        tbaDart35, tbaDart52]

def twoBandAnnulusFace3PureDartCycle
    (hf : (3 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoBandAnnulusEmbedding ⟨(3 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart34, tbaDart47, tbaDart76, tbaDart63]
  hnonempty := by simp
  hclosed := by tba_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary, tbaM34, tbaR47,
        tbaI67, tbaR36, tbaDart34, tbaDart47, tbaDart76, tbaDart63]
  hface_sub := by
    intro e he
    have he' : e = tbaM34 ∨ e = tbaR47 ∨ e = tbaI67 ∨ e = tbaR36 := by
      simpa [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [tbaM34, tbaR47, tbaI67, tbaR36, tbaDart34, tbaDart47,
        tbaDart76, tbaDart63]

def twoBandAnnulusFace4PureDartCycle
    (hf : (4 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoBandAnnulusEmbedding ⟨(4 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart45, tbaDart58, tbaDart87, tbaDart74]
  hnonempty := by simp
  hclosed := by tba_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary, tbaM45, tbaR58,
        tbaI78, tbaR47, tbaDart45, tbaDart58, tbaDart87, tbaDart74]
  hface_sub := by
    intro e he
    have he' : e = tbaM45 ∨ e = tbaR58 ∨ e = tbaI78 ∨ e = tbaR47 := by
      simpa [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [tbaM45, tbaR58, tbaI78, tbaR47, tbaDart45, tbaDart58,
        tbaDart87, tbaDart74]

def twoBandAnnulusFace5PureDartCycle
    (hf : (5 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoBandAnnulusEmbedding ⟨(5 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart53, tbaDart36, tbaDart68, tbaDart85]
  hnonempty := by simp
  hclosed := by tba_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary, tbaM53, tbaR36,
        tbaI86, tbaR58, tbaDart53, tbaDart36, tbaDart68, tbaDart85]
  hface_sub := by
    intro e he
    have he' : e = tbaM53 ∨ e = tbaR36 ∨ e = tbaI86 ∨ e = tbaR58 := by
      simpa [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [tbaM53, tbaR36, tbaI86, tbaR58, tbaDart53, tbaDart36,
        tbaDart68, tbaDart85]

def twoBandAnnulusPureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry
      twoBandAnnulusEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change TwoBandAnnulusFace at f
    by_cases h0 : f = (0 : TwoBandAnnulusFace)
    · subst f
      exact twoBandAnnulusFace0PureDartCycle hfmem
    · by_cases h1 : f = (1 : TwoBandAnnulusFace)
      · subst f
        exact twoBandAnnulusFace1PureDartCycle hfmem
      · by_cases h2 : f = (2 : TwoBandAnnulusFace)
        · subst f
          exact twoBandAnnulusFace2PureDartCycle hfmem
        · by_cases h3 : f = (3 : TwoBandAnnulusFace)
          · subst f
            exact twoBandAnnulusFace3PureDartCycle hfmem
          · by_cases h4 : f = (4 : TwoBandAnnulusFace)
            · subst f
              exact twoBandAnnulusFace4PureDartCycle hfmem
            · have h5 : f = (5 : TwoBandAnnulusFace) := by
                fin_cases f <;> first | rfl | contradiction
              subst f
              exact twoBandAnnulusFace5PureDartCycle hfmem

def twoBandAnnulusClosedWalkEmbeddingData :
    PlanarBoundaryClosedWalkEmbeddingData twoBandAnnulusEmbedding :=
  twoBandAnnulusPureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

theorem twoBandAnnulusFace_cases
    (f : AmbientFace twoBandAnnulusEmbedding.faces) :
    f = ⟨(0 : TwoBandAnnulusFace), by
      change (0 : TwoBandAnnulusFace) ∈ twoBandAnnulusFaces
      exact Finset.mem_univ _⟩ ∨
      f = ⟨(1 : TwoBandAnnulusFace), by
        change (1 : TwoBandAnnulusFace) ∈ twoBandAnnulusFaces
        exact Finset.mem_univ _⟩ ∨
      f = ⟨(2 : TwoBandAnnulusFace), by
        change (2 : TwoBandAnnulusFace) ∈ twoBandAnnulusFaces
        exact Finset.mem_univ _⟩ ∨
      f = ⟨(3 : TwoBandAnnulusFace), by
        change (3 : TwoBandAnnulusFace) ∈ twoBandAnnulusFaces
        exact Finset.mem_univ _⟩ ∨
      f = ⟨(4 : TwoBandAnnulusFace), by
        change (4 : TwoBandAnnulusFace) ∈ twoBandAnnulusFaces
        exact Finset.mem_univ _⟩ ∨
        f = ⟨(5 : TwoBandAnnulusFace), by
          change (5 : TwoBandAnnulusFace) ∈ twoBandAnnulusFaces
          exact Finset.mem_univ _⟩ := by
  rcases f with ⟨f, hfmem⟩
  change TwoBandAnnulusFace at f
  fin_cases f
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext rfl)

theorem twoBandAnnulusClosedWalkEmbeddingData_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace twoBandAnnulusEmbedding.faces,
      (twoBandAnnulusClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f := by
  intro f
  rcases twoBandAnnulusFace_cases f with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨[tbaO01], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
        decide
  · refine ⟨[tbaO12], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
        decide
  · refine ⟨[tbaO20], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
        decide
  · refine ⟨[tbaI67], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
        decide
  · refine ⟨[tbaI78], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
        decide
  · refine ⟨[tbaI86], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
        decide

theorem tbaR03_not_mem_selectedBoundarySupport :
    tbaR03 ∉ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaR03 = 1 := by
    simpa [twoBandAnnulusEmbedding] using hcount
  rw [totalIncidenceCount_tbaR03] at hcount'
  norm_num at hcount'

theorem tbaR58_not_mem_selectedBoundarySupport :
    tbaR58 ∉ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaR58 = 1 := by
    simpa [twoBandAnnulusEmbedding] using hcount
  rw [totalIncidenceCount_tbaR58] at hcount'
  norm_num at hcount'

theorem tbaM53_not_mem_selectedBoundarySupport :
    tbaM53 ∉ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  intro h
  have hcount :=
    (mem_selectedBoundarySupport_iff
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces).1 h |>.2
  have hcount' :
      totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaM53 = 1 := by
    simpa [twoBandAnnulusEmbedding] using hcount
  rw [totalIncidenceCount_tbaM53] at hcount'
  norm_num at hcount'

theorem twoBandAnnulus_interiorEdgeSupport_eq :
    interiorEdgeSupport
        twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces =
      twoBandAnnulusInteriorEdges := by
  ext e
  rcases twoBandAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem twoBandAnnulus_mem_selectedBoundarySupport_of_not_mem_interiorEdgeSupport
    {e : twoBandAnnulusGraph.edgeSet}
    (hnotInterior :
      e ∉ interiorEdgeSupport
        twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces) :
    e ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  have hnotInterior' : e ∉ twoBandAnnulusInteriorEdges := by
    simpa [twoBandAnnulus_interiorEdgeSupport_eq] using hnotInterior
  rw [twoBandAnnulus_selectedBoundarySupport_eq]
  rcases twoBandAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    simp [twoBandAnnulusInteriorEdges] at hnotInterior' ⊢

theorem twoBandAnnulus_forcedEdges_no_boundaryFree_incident_face :
    ∀ e ∈ twoBandAnnulusInteriorEdges,
      ∀ f ∈ twoBandAnnulusEmbedding.faces,
        e ∈ twoBandAnnulusEmbedding.faceBoundary f →
          ∃ b ∈ selectedBoundarySupport
              twoBandAnnulusEmbedding.faceBoundary
              twoBandAnnulusEmbedding.faces
              twoBandAnnulusEmbedding.faces,
            b ∈ twoBandAnnulusEmbedding.faceBoundary f := by
  decide

theorem not_twoBandAnnulus_forcedEdges_have_boundaryFree_incident_face :
    ¬ (∀ e ∈ twoBandAnnulusInteriorEdges,
      ∃ f ∈ twoBandAnnulusEmbedding.faces,
        e ∈ twoBandAnnulusEmbedding.faceBoundary f ∧
          ∀ b ∈ selectedBoundarySupport
              twoBandAnnulusEmbedding.faceBoundary
              twoBandAnnulusEmbedding.faces
              twoBandAnnulusEmbedding.faces,
            b ∉ twoBandAnnulusEmbedding.faceBoundary f) := by
  intro h
  rcases h tbaM34 (by simp [twoBandAnnulusInteriorEdges]) with
    ⟨f, hf, hM34f, hfree⟩
  rcases twoBandAnnulus_forcedEdges_no_boundaryFree_incident_face
      tbaM34 (by simp [twoBandAnnulusInteriorEdges]) f hf hM34f with
    ⟨b, hb, hbf⟩
  exact hfree b hb hbf

theorem not_twoBandAnnulus_forcedEdges_endpoint_no_touch_selectedBoundarySupport :
    ¬ (∀ e ∈ twoBandAnnulusInteriorEdges,
      ∀ b ∈ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces,
        ¬ ∃ v : Fin 9, v ∈ (e : Sym2 (Fin 9)) ∧ v ∈ (b : Sym2 (Fin 9))) := by
  intro h
  exact h tbaR03 (by simp [twoBandAnnulusInteriorEdges])
    tbaO01 tbaO01_mem_selectedBoundarySupport ⟨0, by decide, by decide⟩

theorem twoBandAnnulus_purifiedCarrier_nonempty :
    ∃ v : Fin 9,
      (∃ e ∈ twoBandAnnulusInteriorEdges, v ∈ (e : Sym2 (Fin 9))) ∧
      ∀ b ∈ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces,
        v ∉ (b : Sym2 (Fin 9)) := by
  decide

theorem twoBandAnnulus_selectedBoundarySupport_eq_outer_union_inner :
    selectedBoundarySupport
        twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces
        twoBandAnnulusEmbedding.faces =
      twoBandAnnulusOuterBoundarySet ∪ twoBandAnnulusInnerBoundarySet := by
  rw [twoBandAnnulus_selectedBoundarySupport_eq]
  ext e
  rcases twoBandAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem twoBandAnnulus_outerBoundaryEdgeSet_induced :
    BoundaryEdgeSetInducedSubgraph twoBandAnnulusOuterBoundarySet := by
  intro e hEndpoints
  rcases twoBandAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · simp [twoBandAnnulusOuterBoundarySet]
  · simp [twoBandAnnulusOuterBoundarySet]
  · simp [twoBandAnnulusOuterBoundarySet]
  · exfalso
    have hbad := hEndpoints (6 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      tbaO01, tbaO12, tbaO20] at hbad
  · exfalso
    have hbad := hEndpoints (7 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      tbaO01, tbaO12, tbaO20] at hbad
  · exfalso
    have hbad := hEndpoints (8 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      tbaO01, tbaO12, tbaO20] at hbad
  · exfalso
    have hbad := hEndpoints (3 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      tbaO01, tbaO12, tbaO20] at hbad
  · exfalso
    have hbad := hEndpoints (4 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      tbaO01, tbaO12, tbaO20] at hbad
  · exfalso
    have hbad := hEndpoints (5 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      tbaO01, tbaO12, tbaO20] at hbad
  · exfalso
    have hbad := hEndpoints (3 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      tbaO01, tbaO12, tbaO20] at hbad
  · exfalso
    have hbad := hEndpoints (4 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      tbaO01, tbaO12, tbaO20] at hbad
  · exfalso
    have hbad := hEndpoints (5 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      tbaO01, tbaO12, tbaO20] at hbad
  · exfalso
    have hbad := hEndpoints (3 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      tbaO01, tbaO12, tbaO20] at hbad
  · exfalso
    have hbad := hEndpoints (4 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      tbaO01, tbaO12, tbaO20] at hbad
  · exfalso
    have hbad := hEndpoints (5 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      tbaO01, tbaO12, tbaO20] at hbad

theorem twoBandAnnulus_innerBoundaryEdgeSet_induced :
    BoundaryEdgeSetInducedSubgraph twoBandAnnulusInnerBoundarySet := by
  intro e hEndpoints
  rcases twoBandAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exfalso
    have hbad := hEndpoints (0 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusInnerBoundarySet,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (1 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusInnerBoundarySet,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (2 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusInnerBoundarySet,
      tbaI67, tbaI78, tbaI86] at hbad
  · simp [twoBandAnnulusInnerBoundarySet]
  · simp [twoBandAnnulusInnerBoundarySet]
  · simp [twoBandAnnulusInnerBoundarySet]
  · exfalso
    have hbad := hEndpoints (0 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusInnerBoundarySet,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (1 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusInnerBoundarySet,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (2 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusInnerBoundarySet,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (3 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusInnerBoundarySet,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (4 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusInnerBoundarySet,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (5 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusInnerBoundarySet,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (3 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusInnerBoundarySet,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (4 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusInnerBoundarySet,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (5 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusInnerBoundarySet,
      tbaI67, tbaI78, tbaI86] at hbad

theorem twoBandAnnulus_outer_inner_crossComponentChordFree :
    BoundaryEdgeSetCrossComponentChordFree
      twoBandAnnulusOuterBoundarySet
      twoBandAnnulusInnerBoundarySet := by
  intro e hEndpoints _hLeft _hRight
  rcases twoBandAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · simp [twoBandAnnulusOuterBoundarySet, twoBandAnnulusInnerBoundarySet]
  · simp [twoBandAnnulusOuterBoundarySet, twoBandAnnulusInnerBoundarySet]
  · simp [twoBandAnnulusOuterBoundarySet, twoBandAnnulusInnerBoundarySet]
  · simp [twoBandAnnulusOuterBoundarySet, twoBandAnnulusInnerBoundarySet]
  · simp [twoBandAnnulusOuterBoundarySet, twoBandAnnulusInnerBoundarySet]
  · simp [twoBandAnnulusOuterBoundarySet, twoBandAnnulusInnerBoundarySet]
  · exfalso
    have hbad := hEndpoints (3 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      twoBandAnnulusInnerBoundarySet, tbaO01, tbaO12, tbaO20,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (4 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      twoBandAnnulusInnerBoundarySet, tbaO01, tbaO12, tbaO20,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (5 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      twoBandAnnulusInnerBoundarySet, tbaO01, tbaO12, tbaO20,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (3 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      twoBandAnnulusInnerBoundarySet, tbaO01, tbaO12, tbaO20,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (4 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      twoBandAnnulusInnerBoundarySet, tbaO01, tbaO12, tbaO20,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (5 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      twoBandAnnulusInnerBoundarySet, tbaO01, tbaO12, tbaO20,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (3 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      twoBandAnnulusInnerBoundarySet, tbaO01, tbaO12, tbaO20,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (4 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      twoBandAnnulusInnerBoundarySet, tbaO01, tbaO12, tbaO20,
      tbaI67, tbaI78, tbaI86] at hbad
  · exfalso
    have hbad := hEndpoints (5 : Fin 9) (by decide)
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      twoBandAnnulusInnerBoundarySet, tbaO01, tbaO12, tbaO20,
      tbaI67, tbaI78, tbaI86] at hbad

theorem twoBandAnnulus_selectedBoundaryInducedSubgraph :
    SelectedBoundaryInducedSubgraph twoBandAnnulusEmbedding :=
  selectedBoundaryInducedSubgraph_of_selectedBoundarySupport_eq_union_of_induced_of_crossComponentChordFree
    (left := twoBandAnnulusOuterBoundarySet)
    (right := twoBandAnnulusInnerBoundarySet)
    twoBandAnnulus_selectedBoundarySupport_eq_outer_union_inner
    twoBandAnnulus_outerBoundaryEdgeSet_induced
    twoBandAnnulus_innerBoundaryEdgeSet_induced
    twoBandAnnulus_outer_inner_crossComponentChordFree

theorem twoBandAnnulus_interiorEdgesNotSelectedBoundaryChords :
    InteriorEdgesNotSelectedBoundaryChords twoBandAnnulusEmbedding :=
  interiorEdgesNotSelectedBoundaryChords_of_selectedBoundarySupport_eq_union_of_induced_of_crossComponentChordFree
    (left := twoBandAnnulusOuterBoundarySet)
    (right := twoBandAnnulusInnerBoundarySet)
    twoBandAnnulus_selectedBoundarySupport_eq_outer_union_inner
    twoBandAnnulus_outerBoundaryEdgeSet_induced
    twoBandAnnulus_innerBoundaryEdgeSet_induced
    twoBandAnnulus_outer_inner_crossComponentChordFree

theorem twoBandAnnulus_boundaryEdge_eq
    (e : PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding) :
    e = ⟨tbaO01, tbaO01_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tbaO12, tbaO12_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tbaO20, tbaO20_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tbaI67, tbaI67_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tbaI78, tbaI78_mem_selectedBoundarySupport⟩ ∨
        e = ⟨tbaI86, tbaI86_mem_selectedBoundarySupport⟩ := by
  rcases twoBandAnnulus_edge_eq e.1 with
    hO01 | hO12 | hO20 | hI67 | hI78 | hI86 | hR03 | hR14 | hR25 | hR36 |
    hR47 | hR58 | hM34 | hM45 | hM53
  · exact Or.inl (Subtype.ext hO01)
  · exact Or.inr <| Or.inl (Subtype.ext hO12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext hO20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI67)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI78)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext hI86)
  · exact False.elim (by
      have hnot : tbaR03 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hR03] using e.2))
  · exact False.elim (by
      have hnot : tbaR14 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hR14] using e.2))
  · exact False.elim (by
      have hnot : tbaR25 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hR25] using e.2))
  · exact False.elim (by
      have hnot : tbaR36 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hR36] using e.2))
  · exact False.elim (by
      have hnot : tbaR47 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hR47] using e.2))
  · exact False.elim (by
      have hnot : tbaR58 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hR58] using e.2))
  · exact False.elim (by
      have hnot : tbaM34 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hM34] using e.2))
  · exact False.elim (by
      have hnot : tbaM45 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hM45] using e.2))
  · exact False.elim (by
      have hnot : tbaM53 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact hnot (by simpa [hM53] using e.2))

theorem twoBandAnnulusBoundaryAdj_tbaO01_tbaO12 :
    (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Adj
      ⟨tbaO01, tbaO01_mem_selectedBoundarySupport⟩
      ⟨tbaO12, tbaO12_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 1, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [tbaO01, tbaO12] at this
  · simp [tbaO01]
  · simp [tbaO12]

theorem twoBandAnnulusBoundaryAdj_tbaO12_tbaO20 :
    (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Adj
      ⟨tbaO12, tbaO12_mem_selectedBoundarySupport⟩
      ⟨tbaO20, tbaO20_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 2, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [tbaO12, tbaO20] at this
  · simp [tbaO12]
  · simp [tbaO20]

theorem twoBandAnnulusBoundaryAdj_tbaO20_tbaO01 :
    (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Adj
      ⟨tbaO20, tbaO20_mem_selectedBoundarySupport⟩
      ⟨tbaO01, tbaO01_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 0, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [tbaO20, tbaO01] at this
  · simp [tbaO20]
  · simp [tbaO01]

theorem twoBandAnnulusBoundaryAdj_tbaI67_tbaI78 :
    (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Adj
      ⟨tbaI67, tbaI67_mem_selectedBoundarySupport⟩
      ⟨tbaI78, tbaI78_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 7, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [tbaI67, tbaI78] at this
  · simp [tbaI67]
  · simp [tbaI78]

theorem twoBandAnnulusBoundaryAdj_tbaI78_tbaI86 :
    (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Adj
      ⟨tbaI78, tbaI78_mem_selectedBoundarySupport⟩
      ⟨tbaI86, tbaI86_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 8, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [tbaI78, tbaI86] at this
  · simp [tbaI78]
  · simp [tbaI86]

theorem twoBandAnnulusBoundaryAdj_tbaI86_tbaI67 :
    (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Adj
      ⟨tbaI86, tbaI86_mem_selectedBoundarySupport⟩
      ⟨tbaI67, tbaI67_mem_selectedBoundarySupport⟩ := by
  refine ⟨?_, 6, ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [tbaI86, tbaI67] at this
  · simp [tbaI86]
  · simp [tbaI67]

def twoBandAnnulusOuterRoot :
    PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding :=
  ⟨tbaO01, tbaO01_mem_selectedBoundarySupport⟩

def twoBandAnnulusInnerRoot :
    PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding :=
  ⟨tbaI67, tbaI67_mem_selectedBoundarySupport⟩

def twoBandAnnulusBoundaryLabel
    (e : PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding) : Bool :=
  if e.1 = tbaI67 ∨ e.1 = tbaI78 ∨ e.1 = tbaI86 then true else false

theorem twoBandAnnulusBoundaryAdj_preserves_label :
    ∀ ⦃e f : PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding⦄,
      (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Adj e f →
        twoBandAnnulusBoundaryLabel e =
          twoBandAnnulusBoundaryLabel f := by
  intro e f hadj
  rcases twoBandAnnulus_boundaryEdge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases twoBandAnnulus_boundaryEdge_eq f with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact False.elim
          (by
            rcases hadj with ⟨_, v, hvE, hvF⟩
            fin_cases v <;>
              simp [tbaO01, tbaO12, tbaO20, tbaI67, tbaI78, tbaI86] at hvE hvF)

theorem twoBandAnnulusOuterRoot_ne_innerRoot :
    twoBandAnnulusOuterRoot ≠ twoBandAnnulusInnerRoot := by
  intro h
  have := congrArg Subtype.val h
  simp [twoBandAnnulusOuterRoot, twoBandAnnulusInnerRoot, tbaO01, tbaI67] at this

def twoBandAnnulusAnnulusBoundaryReachabilityData :
    PlanarBoundaryAnnulusBoundaryReachabilityData twoBandAnnulusEmbedding where
  outerRoot := twoBandAnnulusOuterRoot
  innerRoot := twoBandAnnulusInnerRoot
  hroots_ne := twoBandAnnulusOuterRoot_ne_innerRoot
  hcoverRoots := by
    intro e
    rcases twoBandAnnulus_boundaryEdge_eq e with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨twoBandAnnulusOuterRoot, by
        simp [twoBandAnnulusOuterRoot_ne_innerRoot], SimpleGraph.Reachable.refl _⟩
    · refine ⟨twoBandAnnulusOuterRoot, by
        simp [twoBandAnnulusOuterRoot_ne_innerRoot],
        (twoBandAnnulusBoundaryAdj_tbaO01_tbaO12).symm.reachable⟩
    · refine ⟨twoBandAnnulusOuterRoot, by
        simp [twoBandAnnulusOuterRoot_ne_innerRoot],
        twoBandAnnulusBoundaryAdj_tbaO20_tbaO01.reachable⟩
    · refine ⟨twoBandAnnulusInnerRoot, by simp, SimpleGraph.Reachable.refl _⟩
    · refine ⟨twoBandAnnulusInnerRoot, by simp,
        (twoBandAnnulusBoundaryAdj_tbaI67_tbaI78).symm.reachable⟩
    · refine ⟨twoBandAnnulusInnerRoot, by simp,
        twoBandAnnulusBoundaryAdj_tbaI86_tbaI67.reachable⟩
  hsepRoots := by
    intro r s hr hs hreach
    have hlabelEq :
        twoBandAnnulusBoundaryLabel r =
          twoBandAnnulusBoundaryLabel s :=
      eq_of_reachable_of_eq_on_adj
        (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
        twoBandAnnulusBoundaryLabel
        (by
          intro u v huv
          exact twoBandAnnulusBoundaryAdj_preserves_label huv)
        hreach
    have hOuterLabel :
        twoBandAnnulusBoundaryLabel twoBandAnnulusOuterRoot = false := by
      decide
    have hInnerLabel :
        twoBandAnnulusBoundaryLabel twoBandAnnulusInnerRoot = true := by
      decide
    have hr_cases : r = twoBandAnnulusOuterRoot ∨
        r = twoBandAnnulusInnerRoot := by
      simpa [twoBandAnnulusOuterRoot_ne_innerRoot] using hr
    have hs_cases : s = twoBandAnnulusOuterRoot ∨
        s = twoBandAnnulusInnerRoot := by
      simpa [twoBandAnnulusOuterRoot_ne_innerRoot] using hs
    rcases hr_cases with rfl | rfl <;> rcases hs_cases with rfl | rfl
    · rfl
    · rw [hOuterLabel, hInnerLabel] at hlabelEq
      cases hlabelEq
    · rw [hInnerLabel, hOuterLabel] at hlabelEq
      cases hlabelEq
    · rfl

def twoBandAnnulusClosedWalkAnnulusBoundarySource :
    PlanarBoundaryClosedWalkAnnulusBoundarySource twoBandAnnulusEmbedding :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields
    twoBandAnnulusAnnulusBoundaryReachabilityData
    twoBandAnnulusClosedWalkEmbeddingData
    twoBandAnnulusClosedWalkEmbeddingData_selectedBoundaryArcOnFace

theorem nonempty_closedWalkAnnulusBoundarySource_twoBandAnnulus :
    Nonempty
      (PlanarBoundaryClosedWalkAnnulusBoundarySource twoBandAnnulusEmbedding) :=
  ⟨twoBandAnnulusClosedWalkAnnulusBoundarySource⟩

noncomputable abbrev twoBandAnnulusSourceBoundaryData :
    PlanarBoundaryAnnulusBoundaryData twoBandAnnulusEmbedding :=
  twoBandAnnulusClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData

noncomputable abbrev twoBandAnnulusReachabilityBoundaryData :
    PlanarBoundaryAnnulusBoundaryData twoBandAnnulusEmbedding :=
  twoBandAnnulusAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData

theorem twoBandAnnulus_uniqueReachableRoot_outerRoot :
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
        twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
        twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        twoBandAnnulusOuterRoot =
      twoBandAnnulusOuterRoot := by
  apply
    (twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
      twoBandAnnulusOuterRoot).unique
  · exact
      ⟨uniqueReachableRoot_mem_roots
          (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
          twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
          twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
          twoBandAnnulusOuterRoot,
        reachable_uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
          twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
          twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
          twoBandAnnulusOuterRoot⟩
  · exact
      ⟨by
        simp [PlanarBoundaryAnnulusBoundaryReachabilityData.rootSet,
          twoBandAnnulusAnnulusBoundaryReachabilityData,
          twoBandAnnulusOuterRoot_ne_innerRoot],
        SimpleGraph.Reachable.refl twoBandAnnulusOuterRoot⟩

theorem twoBandAnnulus_uniqueReachableRoot_innerRoot :
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
        twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
        twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        twoBandAnnulusInnerRoot =
      twoBandAnnulusInnerRoot := by
  apply
    (twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
      twoBandAnnulusInnerRoot).unique
  · exact
      ⟨uniqueReachableRoot_mem_roots
          (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
          twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
          twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
          twoBandAnnulusInnerRoot,
        reachable_uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
          twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
          twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
          twoBandAnnulusInnerRoot⟩
  · exact
      ⟨by
        simp [PlanarBoundaryAnnulusBoundaryReachabilityData.rootSet,
          twoBandAnnulusAnnulusBoundaryReachabilityData],
        SimpleGraph.Reachable.refl twoBandAnnulusInnerRoot⟩

theorem twoBandAnnulus_uniqueReachableRoot_eq_outerRoot_of_reachable
    {e : PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding}
    (hreach :
      (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Reachable
        e twoBandAnnulusOuterRoot) :
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
        twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
        twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot e =
      twoBandAnnulusOuterRoot := by
  calc
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
        twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
        twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot e =
      uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
        twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
        twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        twoBandAnnulusOuterRoot :=
        uniqueReachableRoot_eq_of_reachable
          (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
          twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
          twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
          hreach
    _ = twoBandAnnulusOuterRoot := twoBandAnnulus_uniqueReachableRoot_outerRoot

theorem twoBandAnnulus_uniqueReachableRoot_eq_innerRoot_of_reachable
    {e : PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding}
    (hreach :
      (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Reachable
        e twoBandAnnulusInnerRoot) :
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
        twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
        twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot e =
      twoBandAnnulusInnerRoot := by
  calc
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
        twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
        twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot e =
      uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
        twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
        twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        twoBandAnnulusInnerRoot :=
        uniqueReachableRoot_eq_of_reachable
          (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
          twoBandAnnulusAnnulusBoundaryReachabilityData.rootSet
          twoBandAnnulusAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
          hreach
    _ = twoBandAnnulusInnerRoot := twoBandAnnulus_uniqueReachableRoot_innerRoot

theorem tbaO01_mem_twoBandAnnulus_source_outerAmbientBoundary :
    tbaO01 ∈ twoBandAnnulusSourceBoundaryData.outerAmbientBoundary := by
  change tbaO01 ∈ twoBandAnnulusReachabilityBoundaryData.outerAmbientBoundary
  exact
    PlanarBoundaryAnnulusBoundaryReachabilityData.mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
        twoBandAnnulusAnnulusBoundaryReachabilityData
        (e := twoBandAnnulusOuterRoot)
        twoBandAnnulus_uniqueReachableRoot_outerRoot

theorem tbaO12_mem_twoBandAnnulus_source_outerAmbientBoundary :
    tbaO12 ∈ twoBandAnnulusSourceBoundaryData.outerAmbientBoundary := by
  change tbaO12 ∈ twoBandAnnulusReachabilityBoundaryData.outerAmbientBoundary
  exact
    PlanarBoundaryAnnulusBoundaryReachabilityData.mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
        twoBandAnnulusAnnulusBoundaryReachabilityData
        (e := ⟨tbaO12, tbaO12_mem_selectedBoundarySupport⟩)
        (twoBandAnnulus_uniqueReachableRoot_eq_outerRoot_of_reachable
          (twoBandAnnulusBoundaryAdj_tbaO01_tbaO12).symm.reachable)

theorem tbaO20_mem_twoBandAnnulus_source_outerAmbientBoundary :
    tbaO20 ∈ twoBandAnnulusSourceBoundaryData.outerAmbientBoundary := by
  change tbaO20 ∈ twoBandAnnulusReachabilityBoundaryData.outerAmbientBoundary
  exact
    PlanarBoundaryAnnulusBoundaryReachabilityData.mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
        twoBandAnnulusAnnulusBoundaryReachabilityData
        (e := ⟨tbaO20, tbaO20_mem_selectedBoundarySupport⟩)
        (twoBandAnnulus_uniqueReachableRoot_eq_outerRoot_of_reachable
          twoBandAnnulusBoundaryAdj_tbaO20_tbaO01.reachable)

theorem tbaI67_mem_twoBandAnnulus_source_innerAmbientBoundary :
    tbaI67 ∈ twoBandAnnulusSourceBoundaryData.innerAmbientBoundary := by
  change tbaI67 ∈ twoBandAnnulusReachabilityBoundaryData.innerAmbientBoundary
  exact
    PlanarBoundaryAnnulusBoundaryReachabilityData.mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
        twoBandAnnulusAnnulusBoundaryReachabilityData
        (e := twoBandAnnulusInnerRoot)
        twoBandAnnulus_uniqueReachableRoot_innerRoot

theorem tbaI78_mem_twoBandAnnulus_source_innerAmbientBoundary :
    tbaI78 ∈ twoBandAnnulusSourceBoundaryData.innerAmbientBoundary := by
  change tbaI78 ∈ twoBandAnnulusReachabilityBoundaryData.innerAmbientBoundary
  exact
    PlanarBoundaryAnnulusBoundaryReachabilityData.mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
        twoBandAnnulusAnnulusBoundaryReachabilityData
        (e := ⟨tbaI78, tbaI78_mem_selectedBoundarySupport⟩)
        (twoBandAnnulus_uniqueReachableRoot_eq_innerRoot_of_reachable
          (twoBandAnnulusBoundaryAdj_tbaI67_tbaI78).symm.reachable)

theorem tbaI86_mem_twoBandAnnulus_source_innerAmbientBoundary :
    tbaI86 ∈ twoBandAnnulusSourceBoundaryData.innerAmbientBoundary := by
  change tbaI86 ∈ twoBandAnnulusReachabilityBoundaryData.innerAmbientBoundary
  exact
    PlanarBoundaryAnnulusBoundaryReachabilityData.mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
        twoBandAnnulusAnnulusBoundaryReachabilityData
        (e := ⟨tbaI86, tbaI86_mem_selectedBoundarySupport⟩)
        (twoBandAnnulus_uniqueReachableRoot_eq_innerRoot_of_reachable
          twoBandAnnulusBoundaryAdj_tbaI86_tbaI67.reachable)

theorem twoBandAnnulus_source_outerAmbientBoundary_eq :
    twoBandAnnulusSourceBoundaryData.outerAmbientBoundary =
      twoBandAnnulusOuterBoundarySet := by
  ext e
  constructor
  · intro he
    have heSel :
        e ∈ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces :=
      twoBandAnnulusSourceBoundaryData.houterAmbientBoundarySubset he
    rcases twoBandAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · simp [twoBandAnnulusOuterBoundarySet]
    · simp [twoBandAnnulusOuterBoundarySet]
    · simp [twoBandAnnulusOuterBoundarySet]
    · exfalso
      exact
        (Finset.disjoint_left.mp
          twoBandAnnulusSourceBoundaryData.hambientBoundaryDisjoint)
          he tbaI67_mem_twoBandAnnulus_source_innerAmbientBoundary
    · exfalso
      exact
        (Finset.disjoint_left.mp
          twoBandAnnulusSourceBoundaryData.hambientBoundaryDisjoint)
          he tbaI78_mem_twoBandAnnulus_source_innerAmbientBoundary
    · exfalso
      exact
        (Finset.disjoint_left.mp
          twoBandAnnulusSourceBoundaryData.hambientBoundaryDisjoint)
          he tbaI86_mem_twoBandAnnulus_source_innerAmbientBoundary
    · have hnot : tbaR03 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaR14 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaR25 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaR36 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaR47 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaR58 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaM34 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaM45 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaM53 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
  · intro he
    simp [twoBandAnnulusOuterBoundarySet] at he
    rcases he with rfl | rfl | rfl
    · exact tbaO01_mem_twoBandAnnulus_source_outerAmbientBoundary
    · exact tbaO12_mem_twoBandAnnulus_source_outerAmbientBoundary
    · exact tbaO20_mem_twoBandAnnulus_source_outerAmbientBoundary

theorem twoBandAnnulus_source_innerAmbientBoundary_eq :
    twoBandAnnulusSourceBoundaryData.innerAmbientBoundary =
      twoBandAnnulusInnerBoundarySet := by
  ext e
  constructor
  · intro he
    have heSel :
        e ∈ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces :=
      twoBandAnnulusSourceBoundaryData.hinnerAmbientBoundarySubset he
    rcases twoBandAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact
        (Finset.disjoint_left.mp
          twoBandAnnulusSourceBoundaryData.hambientBoundaryDisjoint)
          tbaO01_mem_twoBandAnnulus_source_outerAmbientBoundary he
    · exfalso
      exact
        (Finset.disjoint_left.mp
          twoBandAnnulusSourceBoundaryData.hambientBoundaryDisjoint)
          tbaO12_mem_twoBandAnnulus_source_outerAmbientBoundary he
    · exfalso
      exact
        (Finset.disjoint_left.mp
          twoBandAnnulusSourceBoundaryData.hambientBoundaryDisjoint)
          tbaO20_mem_twoBandAnnulus_source_outerAmbientBoundary he
    · simp [twoBandAnnulusInnerBoundarySet]
    · simp [twoBandAnnulusInnerBoundarySet]
    · simp [twoBandAnnulusInnerBoundarySet]
    · have hnot : tbaR03 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaR14 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaR25 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaR36 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaR47 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaR58 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaM34 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaM45 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
    · have hnot : tbaM53 ∉ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces := by decide
      exact False.elim (hnot heSel)
  · intro he
    simp [twoBandAnnulusInnerBoundarySet] at he
    rcases he with rfl | rfl | rfl
    · exact tbaI67_mem_twoBandAnnulus_source_innerAmbientBoundary
    · exact tbaI78_mem_twoBandAnnulus_source_innerAmbientBoundary
    · exact tbaI86_mem_twoBandAnnulus_source_innerAmbientBoundary

theorem twoBandAnnulus_source_outerAmbientBoundary_induced :
    BoundaryEdgeSetInducedSubgraph
      twoBandAnnulusSourceBoundaryData.outerAmbientBoundary := by
  rw [twoBandAnnulus_source_outerAmbientBoundary_eq]
  exact twoBandAnnulus_outerBoundaryEdgeSet_induced

theorem twoBandAnnulus_source_innerAmbientBoundary_induced :
    BoundaryEdgeSetInducedSubgraph
      twoBandAnnulusSourceBoundaryData.innerAmbientBoundary := by
  rw [twoBandAnnulus_source_innerAmbientBoundary_eq]
  exact twoBandAnnulus_innerBoundaryEdgeSet_induced

theorem twoBandAnnulus_source_outer_inner_crossComponentChordFree :
    BoundaryEdgeSetCrossComponentChordFree
      twoBandAnnulusSourceBoundaryData.outerAmbientBoundary
      twoBandAnnulusSourceBoundaryData.innerAmbientBoundary := by
  rw [twoBandAnnulus_source_outerAmbientBoundary_eq,
    twoBandAnnulus_source_innerAmbientBoundary_eq]
  exact twoBandAnnulus_outer_inner_crossComponentChordFree

theorem twoBandAnnulus_sourceBoundaryData_selectedBoundaryInducedSubgraph :
    SelectedBoundaryInducedSubgraph twoBandAnnulusEmbedding :=
  PlanarBoundaryAnnulusBoundaryData.selectedBoundaryInducedSubgraph_of_inducedBoundaryComponents_of_crossComponentChordFree
      twoBandAnnulusSourceBoundaryData
      twoBandAnnulus_source_outerAmbientBoundary_induced
      twoBandAnnulus_source_innerAmbientBoundary_induced
      twoBandAnnulus_source_outer_inner_crossComponentChordFree

theorem twoBandAnnulus_sourceBoundaryData_interiorEdgesNotSelectedBoundaryChords :
    InteriorEdgesNotSelectedBoundaryChords twoBandAnnulusEmbedding :=
  PlanarBoundaryAnnulusBoundaryData.interiorEdgesNotSelectedBoundaryChords_of_inducedBoundaryComponents_of_crossComponentChordFree
      twoBandAnnulusSourceBoundaryData
      twoBandAnnulus_source_outerAmbientBoundary_induced
      twoBandAnnulus_source_innerAmbientBoundary_induced
      twoBandAnnulus_source_outer_inner_crossComponentChordFree

theorem selectedBoundaryInteriorEdgeEndpointVertices_nonempty_twoBandAnnulus_via_sourceBoundaryData :
    (selectedBoundaryInteriorEdgeEndpointVertices twoBandAnnulusEmbedding).Nonempty :=
  PlanarBoundaryAnnulusBoundaryData.selectedBoundaryInteriorEdgeEndpointVertices_nonempty_of_inducedBoundaryComponents_of_crossComponentChordFree_and_nonempty
      twoBandAnnulusSourceBoundaryData
      twoBandAnnulus_source_outerAmbientBoundary_induced
      twoBandAnnulus_source_innerAmbientBoundary_induced
      twoBandAnnulus_source_outer_inner_crossComponentChordFree
      (by
        refine ⟨tbaR03, ?_⟩
        rw [twoBandAnnulus_interiorEdgeSupport_eq]
        simp [twoBandAnnulusInteriorEdges])

theorem twoBandAnnulus_sourceBoundaryData_repaired_positive_packet :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource twoBandAnnulusEmbedding) ∧
      BoundaryEdgeSetInducedSubgraph
          twoBandAnnulusSourceBoundaryData.outerAmbientBoundary ∧
        BoundaryEdgeSetInducedSubgraph
            twoBandAnnulusSourceBoundaryData.innerAmbientBoundary ∧
          BoundaryEdgeSetCrossComponentChordFree
              twoBandAnnulusSourceBoundaryData.outerAmbientBoundary
              twoBandAnnulusSourceBoundaryData.innerAmbientBoundary ∧
            SelectedBoundaryInducedSubgraph twoBandAnnulusEmbedding ∧
              InteriorEdgesNotSelectedBoundaryChords twoBandAnnulusEmbedding ∧
                (selectedBoundaryInteriorEdgeEndpointVertices
                  twoBandAnnulusEmbedding).Nonempty :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_twoBandAnnulus,
    twoBandAnnulus_source_outerAmbientBoundary_induced,
    twoBandAnnulus_source_innerAmbientBoundary_induced,
    twoBandAnnulus_source_outer_inner_crossComponentChordFree,
    twoBandAnnulus_sourceBoundaryData_selectedBoundaryInducedSubgraph,
    twoBandAnnulus_sourceBoundaryData_interiorEdgesNotSelectedBoundaryChords,
    selectedBoundaryInteriorEdgeEndpointVertices_nonempty_twoBandAnnulus_via_sourceBoundaryData⟩

theorem boundaryEdgeSetCyclicRun_outer_twoBandAnnulus :
    BoundaryEdgeSetCyclicRun twoBandAnnulusEmbedding
      twoBandAnnulusOuterBoundarySet := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp [twoBandAnnulusOuterBoundarySet] at he
    rcases he with rfl | rfl | rfl
    · exact tbaO01_mem_selectedBoundarySupport
    · exact tbaO12_mem_selectedBoundarySupport
    · exact tbaO20_mem_selectedBoundarySupport
  · refine ⟨[
      ⟨tbaO01, tbaO01_mem_selectedBoundarySupport⟩,
      ⟨tbaO12, tbaO12_mem_selectedBoundarySupport⟩,
      ⟨tbaO20, tbaO20_mem_selectedBoundarySupport⟩], ?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · change List.IsChain (planarBoundarySupportEndpointAdjGraph
        twoBandAnnulusEmbedding).Adj
        [⟨tbaO01, tbaO01_mem_selectedBoundarySupport⟩,
          ⟨tbaO12, tbaO12_mem_selectedBoundarySupport⟩,
          ⟨tbaO20, tbaO20_mem_selectedBoundarySupport⟩,
          ⟨tbaO01, tbaO01_mem_selectedBoundarySupport⟩]
      exact (List.isChain_cons_cons).2
        ⟨twoBandAnnulusBoundaryAdj_tbaO01_tbaO12,
          (List.isChain_cons_cons).2
            ⟨twoBandAnnulusBoundaryAdj_tbaO12_tbaO20,
              (List.isChain_pair).2
                twoBandAnnulusBoundaryAdj_tbaO20_tbaO01⟩⟩
    · intro x
      rcases twoBandAnnulus_boundaryEdge_eq x with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem boundaryEdgeSetCyclicRun_inner_twoBandAnnulus :
    BoundaryEdgeSetCyclicRun twoBandAnnulusEmbedding
      twoBandAnnulusInnerBoundarySet := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp [twoBandAnnulusInnerBoundarySet] at he
    rcases he with rfl | rfl | rfl
    · exact tbaI67_mem_selectedBoundarySupport
    · exact tbaI78_mem_selectedBoundarySupport
    · exact tbaI86_mem_selectedBoundarySupport
  · refine ⟨[
      ⟨tbaI67, tbaI67_mem_selectedBoundarySupport⟩,
      ⟨tbaI78, tbaI78_mem_selectedBoundarySupport⟩,
      ⟨tbaI86, tbaI86_mem_selectedBoundarySupport⟩], ?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · change List.IsChain (planarBoundarySupportEndpointAdjGraph
        twoBandAnnulusEmbedding).Adj
        [⟨tbaI67, tbaI67_mem_selectedBoundarySupport⟩,
          ⟨tbaI78, tbaI78_mem_selectedBoundarySupport⟩,
          ⟨tbaI86, tbaI86_mem_selectedBoundarySupport⟩,
          ⟨tbaI67, tbaI67_mem_selectedBoundarySupport⟩]
      exact (List.isChain_cons_cons).2
        ⟨twoBandAnnulusBoundaryAdj_tbaI67_tbaI78,
          (List.isChain_cons_cons).2
            ⟨twoBandAnnulusBoundaryAdj_tbaI78_tbaI86,
              (List.isChain_pair).2
                twoBandAnnulusBoundaryAdj_tbaI86_tbaI67⟩⟩
    · intro x
      rcases twoBandAnnulus_boundaryEdge_eq x with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem outer_inner_boundaryCycleEndpointSupports_disjoint_twoBandAnnulus :
    Disjoint
      (boundaryEdgeSetEndpointSupport twoBandAnnulusOuterBoundarySet)
      (boundaryEdgeSetEndpointSupport twoBandAnnulusInnerBoundarySet) := by
  rw [Finset.disjoint_left]
  intro v hvOuter hvInner
  fin_cases v <;>
    simp [boundaryEdgeSetEndpointSupport, twoBandAnnulusOuterBoundarySet,
      twoBandAnnulusInnerBoundarySet, tbaO01, tbaO12, tbaO20,
      tbaI67, tbaI78, tbaI86] at hvOuter hvInner

theorem annulusBoundaryCyclePair_twoBandAnnulus :
    AnnulusBoundaryCyclePair twoBandAnnulusEmbedding
      twoBandAnnulusOuterBoundarySet
      twoBandAnnulusInnerBoundarySet :=
  ⟨boundaryEdgeSetCyclicRun_outer_twoBandAnnulus,
    boundaryEdgeSetCyclicRun_inner_twoBandAnnulus,
    outer_inner_boundaryCycleEndpointSupports_disjoint_twoBandAnnulus⟩

theorem twoBandAnnulus_interiorEdgeSupport_nonempty :
    (interiorEdgeSupport
      twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces).Nonempty := by
  refine ⟨tbaR03, ?_⟩
  rw [twoBandAnnulus_interiorEdgeSupport_eq]
  simp [twoBandAnnulusInteriorEdges]

theorem selectedBoundaryInteriorEdgeEndpointVertices_nonempty_twoBandAnnulus :
    (selectedBoundaryInteriorEdgeEndpointVertices twoBandAnnulusEmbedding).Nonempty :=
  selectedBoundaryInteriorEdgeEndpointVertices_nonempty_of_interiorEdgesNotSelectedBoundaryChords_and_nonempty
    twoBandAnnulus_interiorEdgesNotSelectedBoundaryChords
    twoBandAnnulus_interiorEdgeSupport_nonempty

theorem twoBandAnnulus_boundaryCyclePair_componentInduced_crossComponentChordFree_positive_packet :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource twoBandAnnulusEmbedding) ∧
      AnnulusBoundaryCyclePair twoBandAnnulusEmbedding
          twoBandAnnulusOuterBoundarySet
          twoBandAnnulusInnerBoundarySet ∧
        selectedBoundarySupport
            twoBandAnnulusEmbedding.faceBoundary
            twoBandAnnulusEmbedding.faces
            twoBandAnnulusEmbedding.faces =
          twoBandAnnulusOuterBoundarySet ∪ twoBandAnnulusInnerBoundarySet ∧
          BoundaryEdgeSetInducedSubgraph twoBandAnnulusOuterBoundarySet ∧
            BoundaryEdgeSetInducedSubgraph twoBandAnnulusInnerBoundarySet ∧
              BoundaryEdgeSetCrossComponentChordFree
                twoBandAnnulusOuterBoundarySet
                twoBandAnnulusInnerBoundarySet ∧
                SelectedBoundaryInducedSubgraph twoBandAnnulusEmbedding ∧
                  InteriorEdgesNotSelectedBoundaryChords twoBandAnnulusEmbedding ∧
                    (selectedBoundaryInteriorEdgeEndpointVertices
                      twoBandAnnulusEmbedding).Nonempty :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_twoBandAnnulus,
    annulusBoundaryCyclePair_twoBandAnnulus,
    twoBandAnnulus_selectedBoundarySupport_eq_outer_union_inner,
    twoBandAnnulus_outerBoundaryEdgeSet_induced,
    twoBandAnnulus_innerBoundaryEdgeSet_induced,
    twoBandAnnulus_outer_inner_crossComponentChordFree,
    twoBandAnnulus_selectedBoundaryInducedSubgraph,
    twoBandAnnulus_interiorEdgesNotSelectedBoundaryChords,
    selectedBoundaryInteriorEdgeEndpointVertices_nonempty_twoBandAnnulus⟩

theorem not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_twoBandAnnulus :
    ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          twoBandAnnulusEmbedding) := by
  rintro ⟨data⟩
  have hcoverInterior :
      twoBandAnnulusInteriorEdges ⊆ data.peelFaces.image data.witnessEdge := by
    intro e he
    exact data.hcover (by simpa [twoBandAnnulus_interiorEdgeSupport_eq] using he)
  have hcardLower : 9 ≤ (data.peelFaces.image data.witnessEdge).card := by
    have hcardInterior : twoBandAnnulusInteriorEdges.card = 9 := by
      decide
    calc
      9 = twoBandAnnulusInteriorEdges.card := hcardInterior.symm
      _ ≤ (data.peelFaces.image data.witnessEdge).card :=
        Finset.card_le_card hcoverInterior
  have hcardUpper : (data.peelFaces.image data.witnessEdge).card ≤ 6 := by
    calc
      (data.peelFaces.image data.witnessEdge).card ≤ data.peelFaces.card :=
        Finset.card_image_le
      _ ≤ (Finset.univ : Finset (AmbientFace twoBandAnnulusEmbedding.faces)).card :=
        Finset.card_le_card (by intro f _hf; simp)
      _ = 6 := by decide
  have hle : (9 : ℕ) ≤ 6 := le_trans hcardLower hcardUpper
  norm_num at hle

theorem twoBandAnnulus_boundaryZero_no_evader_of_vanishes_on_interiorEdges
    (z : twoBandAnnulusGraph.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding)
    (hcontrol : ∀ e ∈ twoBandAnnulusInteriorEdges, z e = 0) :
    z = 0 := by
  refine eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary ?_
  intro e he
  exact hcontrol e (by simpa [twoBandAnnulus_interiorEdgeSupport_eq] using he)

def twoBandAnnulusKirchhoffVertices : Finset (Fin 9) :=
  {(3 : Fin 9), 4, 5}

theorem twoBandAnnulus_incidentEdgeFinset_three :
    incidentEdgeFinset twoBandAnnulusGraph (3 : Fin 9) =
      {tbaR03, tbaR36, tbaM34, tbaM53} := by
  ext e
  rcases twoBandAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem twoBandAnnulus_incidentEdgeFinset_four :
    incidentEdgeFinset twoBandAnnulusGraph (4 : Fin 9) =
      {tbaR14, tbaR47, tbaM34, tbaM45} := by
  ext e
  rcases twoBandAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem twoBandAnnulus_incidentEdgeFinset_five :
    incidentEdgeFinset twoBandAnnulusGraph (5 : Fin 9) =
      {tbaR25, tbaR58, tbaM45, tbaM53} := by
  ext e
  rcases twoBandAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem twoBandAnnulus_boundaryZeroKirchhoff_no_evader_of_vanishes_on_interiorEdges
    (z : twoBandAnnulusGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices)
    (hcontrol : ∀ e ∈ twoBandAnnulusInteriorEdges, z e = 0) :
    z = 0 := by
  refine
    eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport
      z hz ?_
  intro e he
  exact hcontrol e (by simpa [twoBandAnnulus_interiorEdgeSupport_eq] using he)

def twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges :
    Finset twoBandAnnulusGraph.edgeSet :=
  {tbaM34, tbaM45, tbaM53, tbaR03, tbaR14, tbaR25}

theorem twoBandAnnulus_boundaryZeroKirchhoff_no_evader_of_middleOuterRadialControl
    (z : twoBandAnnulusGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices)
    (hcontrol : ∀ e ∈ twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges, z e = 0) :
    z = 0 := by
  refine
    eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport_control_or_kirchhoffStar
      z hz twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges hcontrol ?_
  intro e heInterior
  have he : e ∈ twoBandAnnulusInteriorEdges := by
    simpa [twoBandAnnulus_interiorEdgeSupport_eq] using heInterior
  rcases twoBandAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((by decide : tbaO01 ∉ twoBandAnnulusInteriorEdges) he)
  · exact False.elim ((by decide : tbaO12 ∉ twoBandAnnulusInteriorEdges) he)
  · exact False.elim ((by decide : tbaO20 ∉ twoBandAnnulusInteriorEdges) he)
  · exact False.elim ((by decide : tbaI67 ∉ twoBandAnnulusInteriorEdges) he)
  · exact False.elim ((by decide : tbaI78 ∉ twoBandAnnulusInteriorEdges) he)
  · exact False.elim ((by decide : tbaI86 ∉ twoBandAnnulusInteriorEdges) he)
  · exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  · exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  · exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  · refine Or.inr ⟨(3 : Fin 9), by simp [twoBandAnnulusKirchhoffVertices], ?_, ?_⟩
    · rw [twoBandAnnulus_incidentEdgeFinset_three]
      simp
    · intro e' he' hne
      rw [twoBandAnnulus_incidentEdgeFinset_three] at he'
      rcases Finset.mem_insert.1 he' with hR03 | he'
      · subst e'
        exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
      rcases Finset.mem_insert.1 he' with hR36 | he'
      · subst e'
        exact False.elim (hne rfl)
      rcases Finset.mem_insert.1 he' with hM34 | he'
      · subst e'
        exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
      have hM53 : e' = tbaM53 := by simpa using he'
      subst e'
      exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  · refine Or.inr ⟨(4 : Fin 9), by simp [twoBandAnnulusKirchhoffVertices], ?_, ?_⟩
    · rw [twoBandAnnulus_incidentEdgeFinset_four]
      simp
    · intro e' he' hne
      rw [twoBandAnnulus_incidentEdgeFinset_four] at he'
      rcases Finset.mem_insert.1 he' with hR14 | he'
      · subst e'
        exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
      rcases Finset.mem_insert.1 he' with hR47 | he'
      · subst e'
        exact False.elim (hne rfl)
      rcases Finset.mem_insert.1 he' with hM34 | he'
      · subst e'
        exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
      have hM45 : e' = tbaM45 := by simpa using he'
      subst e'
      exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  · refine Or.inr ⟨(5 : Fin 9), by simp [twoBandAnnulusKirchhoffVertices], ?_, ?_⟩
    · rw [twoBandAnnulus_incidentEdgeFinset_five]
      simp
    · intro e' he' hne
      rw [twoBandAnnulus_incidentEdgeFinset_five] at he'
      rcases Finset.mem_insert.1 he' with hR25 | he'
      · subst e'
        exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
      rcases Finset.mem_insert.1 he' with hR58 | he'
      · subst e'
        exact False.elim (hne rfl)
      rcases Finset.mem_insert.1 he' with hM45 | he'
      · subst e'
        exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
      have hM53 : e' = tbaM53 := by simpa using he'
      subst e'
      exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  · exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  · exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  · exact Or.inl (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])

def twoBandAnnulusTbaM34OnlyKirchhoffEvader : twoBandAnnulusGraph.edgeSet → Color :=
  indicatorChain red ({tbaR03, tbaR58, tbaM53} : Finset twoBandAnnulusGraph.edgeSet)

theorem twoBandAnnulusTbaM34OnlyKirchhoffEvader_mem_planarBoundaryZeroSubmodule :
    twoBandAnnulusTbaM34OnlyKirchhoffEvader ∈
      planarBoundaryZeroSubmodule twoBandAnnulusEmbedding := by
  intro e he
  rcases twoBandAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact False.elim (tbaR03_not_mem_selectedBoundarySupport he)
  · decide
  · decide
  · decide
  · decide
  · exact False.elim (tbaR58_not_mem_selectedBoundarySupport he)
  · decide
  · decide
  · exact False.elim (tbaM53_not_mem_selectedBoundarySupport he)

theorem twoBandAnnulusTbaM34OnlyKirchhoffEvader_mem_kirchhoffSubmodule :
    twoBandAnnulusTbaM34OnlyKirchhoffEvader ∈
      kirchhoffSubmodule twoBandAnnulusGraph twoBandAnnulusKirchhoffVertices := by
  intro v hv
  have hv_cases : v = (3 : Fin 9) ∨ v = (4 : Fin 9) ∨ v = (5 : Fin 9) := by
    simpa [twoBandAnnulusKirchhoffVertices] using hv
  rcases hv_cases with rfl | rfl | rfl <;>
    unfold vertexKirchhoffSum incidentEdgeFinset
  all_goals decide

theorem twoBandAnnulus_tbaM34_only_has_boundaryZeroKirchhoff_evader :
    twoBandAnnulusTbaM34OnlyKirchhoffEvader ∈ theorem49BoundaryZeroKirchhoffSubspace
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices ∧
      twoBandAnnulusTbaM34OnlyKirchhoffEvader tbaM34 = 0 ∧
      twoBandAnnulusTbaM34OnlyKirchhoffEvader tbaR03 = red ∧
      twoBandAnnulusTbaM34OnlyKirchhoffEvader tbaR58 = red ∧
      twoBandAnnulusTbaM34OnlyKirchhoffEvader tbaM53 = red ∧
      twoBandAnnulusTbaM34OnlyKirchhoffEvader ≠ 0 := by
  refine ⟨⟨twoBandAnnulusTbaM34OnlyKirchhoffEvader_mem_kirchhoffSubmodule,
    twoBandAnnulusTbaM34OnlyKirchhoffEvader_mem_planarBoundaryZeroSubmodule⟩,
    by decide, by decide, by decide, by decide, ?_⟩
  intro hzero
  have hvalue := congrFun hzero tbaR03
  have hred : twoBandAnnulusTbaM34OnlyKirchhoffEvader tbaR03 = red := by
    decide
  rw [hred] at hvalue
  exact red_ne_zero hvalue

def twoBandAnnulusNoncontrollingSixKirchhoffControlEdges :
    Finset twoBandAnnulusGraph.edgeSet :=
  {tbaM34, tbaM45, tbaR14, tbaR25, tbaR36, tbaR47}

theorem twoBandAnnulusNoncontrollingSixKirchhoffControlEdges_subset_interior :
    twoBandAnnulusNoncontrollingSixKirchhoffControlEdges ⊆
      twoBandAnnulusInteriorEdges := by
  intro e he
  simp [twoBandAnnulusNoncontrollingSixKirchhoffControlEdges,
    twoBandAnnulusInteriorEdges] at he ⊢
  tauto

theorem twoBandAnnulusNoncontrollingSixKirchhoffControlEdges_card :
    twoBandAnnulusNoncontrollingSixKirchhoffControlEdges.card = 6 := by
  decide

theorem twoBandAnnulusTbaM34OnlyKirchhoffEvader_vanishes_on_noncontrollingSix :
    ∀ e ∈ twoBandAnnulusNoncontrollingSixKirchhoffControlEdges,
      twoBandAnnulusTbaM34OnlyKirchhoffEvader e = 0 := by
  intro e he
  have he_cases :
      e = tbaM34 ∨ e = tbaM45 ∨ e = tbaR14 ∨
      e = tbaR25 ∨ e = tbaR36 ∨ e = tbaR47 := by
    simpa [twoBandAnnulusNoncontrollingSixKirchhoffControlEdges] using he
  rcases he_cases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Cardinality alone is not the two-band Kirchhoff detector criterion: this six-edge interior
set still leaves a nonzero boundary-zero Kirchhoff evader. -/
theorem twoBandAnnulus_noncontrollingSix_not_boundaryZeroKirchhoff_control :
    ¬ ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
      (∀ e ∈ twoBandAnnulusNoncontrollingSixKirchhoffControlEdges, z e = 0) →
      z = 0 := by
  intro hcontrol
  rcases twoBandAnnulus_tbaM34_only_has_boundaryZeroKirchhoff_evader with
    ⟨hz, _hM34, _hR03, _hR58, _hM53, hzNonzero⟩
  exact hzNonzero
    (hcontrol hz
      twoBandAnnulusTbaM34OnlyKirchhoffEvader_vanishes_on_noncontrollingSix)

/-- Explicit refutation of the cardinality-only repair: some six-edge interior control set does
not control the two-band boundary-zero Kirchhoff target. -/
theorem twoBandAnnulus_exists_six_interior_control_not_boundaryZeroKirchhoff_control :
    ∃ control : Finset twoBandAnnulusGraph.edgeSet,
      control ⊆ twoBandAnnulusInteriorEdges ∧
      control.card = 6 ∧
        ¬ ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
          z ∈ theorem49BoundaryZeroKirchhoffSubspace
              twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
          (∀ e ∈ control, z e = 0) →
          z = 0 := by
  exact ⟨twoBandAnnulusNoncontrollingSixKirchhoffControlEdges,
    twoBandAnnulusNoncontrollingSixKirchhoffControlEdges_subset_interior,
    twoBandAnnulusNoncontrollingSixKirchhoffControlEdges_card,
    twoBandAnnulus_noncontrollingSix_not_boundaryZeroKirchhoff_control⟩

/-- Six interior coordinates are not, by themselves, sufficient for two-band Kirchhoff control. -/
theorem twoBandAnnulus_not_all_six_interior_controls_boundaryZeroKirchhoff_control :
    ¬ ∀ control : Finset twoBandAnnulusGraph.edgeSet,
      control ⊆ twoBandAnnulusInteriorEdges →
      control.card = 6 →
        ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
          z ∈ theorem49BoundaryZeroKirchhoffSubspace
              twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
          (∀ e ∈ control, z e = 0) →
          z = 0 := by
  intro hall
  rcases twoBandAnnulus_exists_six_interior_control_not_boundaryZeroKirchhoff_control with
    ⟨control, hsubset, hcard, hnotControl⟩
  exact hnotControl (hall control hsubset hcard)

theorem twoBandAnnulusMiddleOuterRadialKirchhoffControl_scalarConstraintMap_ker_eq_bot :
    LinearMap.ker
      (theorem49BoundaryZeroKirchhoffScalarConstraintMap
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
        twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges) = ⊥ := by
  exact
    (theorem49BoundaryZeroKirchhoffSubspace_control_iff_scalarConstraintMap_ker_eq_bot
      twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
      twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges).1
      (by
        intro z hz hcontrol
        exact twoBandAnnulus_boundaryZeroKirchhoff_no_evader_of_middleOuterRadialControl
          z hz hcontrol)

theorem twoBandAnnulusNoncontrollingSixKirchhoffControl_scalarConstraintMap_ker_ne_bot :
    LinearMap.ker
      (theorem49BoundaryZeroKirchhoffScalarConstraintMap
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
        twoBandAnnulusNoncontrollingSixKirchhoffControlEdges) ≠ ⊥ := by
  intro hker
  exact twoBandAnnulus_noncontrollingSix_not_boundaryZeroKirchhoff_control
    ((theorem49BoundaryZeroKirchhoffSubspace_control_iff_scalarConstraintMap_ker_eq_bot
      twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
      twoBandAnnulusNoncontrollingSixKirchhoffControlEdges).2 hker)

def twoBandAnnulusKirchhoffColumn
    (e : twoBandAnnulusGraph.edgeSet) : Fin 3 → F2 :=
  fun i => match i with
    | ⟨0, _⟩ =>
        if e = tbaR03 ∨ e = tbaR36 ∨ e = tbaM34 ∨ e = tbaM53 then 1 else 0
    | ⟨1, _⟩ =>
        if e = tbaR14 ∨ e = tbaR47 ∨ e = tbaM34 ∨ e = tbaM45 then 1 else 0
    | ⟨2, _⟩ =>
        if e = tbaR25 ∨ e = tbaR58 ∨ e = tbaM45 ∨ e = tbaM53 then 1 else 0

theorem twoBandAnnulusKirchhoffColumn_eq_incidentIndicator
    (e : twoBandAnnulusGraph.edgeSet) :
    twoBandAnnulusKirchhoffColumn e =
      fun i => match i with
        | ⟨0, _⟩ =>
            if e ∈ incidentEdgeFinset twoBandAnnulusGraph (3 : Fin 9) then 1 else 0
        | ⟨1, _⟩ =>
            if e ∈ incidentEdgeFinset twoBandAnnulusGraph (4 : Fin 9) then 1 else 0
        | ⟨2, _⟩ =>
            if e ∈ incidentEdgeFinset twoBandAnnulusGraph (5 : Fin 9) then 1 else 0 := by
  funext i
  fin_cases i <;>
    simp [twoBandAnnulusKirchhoffColumn,
      twoBandAnnulus_incidentEdgeFinset_three,
      twoBandAnnulus_incidentEdgeFinset_four,
      twoBandAnnulus_incidentEdgeFinset_five]

def twoBandAnnulusOmittedTripleKirchhoffColumnMap
    (omitted : Fin 3 → twoBandAnnulusGraph.edgeSet) :
    (Fin 3 → F2) →ₗ[F2] (Fin 3 → F2) where
  toFun x := fun i => ∑ j : Fin 3,
    x j * twoBandAnnulusKirchhoffColumn (omitted j) i
  map_add' x y := by
    ext i
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  map_smul' a x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc
      ∑ j : Fin 3, a * x j * twoBandAnnulusKirchhoffColumn (omitted j) i =
          ∑ j : Fin 3,
            a * (x j * twoBandAnnulusKirchhoffColumn (omitted j) i) := by
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = a * ∑ j : Fin 3,
          x j * twoBandAnnulusKirchhoffColumn (omitted j) i := by
            rw [Finset.mul_sum]

def twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple :
    Fin 3 → twoBandAnnulusGraph.edgeSet
  | ⟨0, _⟩ => tbaR36
  | ⟨1, _⟩ => tbaR47
  | ⟨2, _⟩ => tbaR58

def twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple :
    Fin 3 → twoBandAnnulusGraph.edgeSet
  | ⟨0, _⟩ => tbaR03
  | ⟨1, _⟩ => tbaR58
  | ⟨2, _⟩ => tbaM53

theorem twoBandAnnulusMiddleOuterRadialKirchhoffControl_omittedInteriorEdges_eq :
    twoBandAnnulusInteriorEdges \ twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges =
      ({tbaR36, tbaR47, tbaR58} : Finset twoBandAnnulusGraph.edgeSet) := by
  decide

theorem twoBandAnnulusNoncontrollingSixKirchhoffControl_omittedInteriorEdges_eq :
    twoBandAnnulusInteriorEdges \ twoBandAnnulusNoncontrollingSixKirchhoffControlEdges =
      ({tbaR03, tbaR58, tbaM53} : Finset twoBandAnnulusGraph.edgeSet) := by
  decide

theorem twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple_columnMap_ker_eq_bot :
    LinearMap.ker
      (twoBandAnnulusOmittedTripleKirchhoffColumnMap
        twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple) = ⊥ := by
  ext x
  change
    twoBandAnnulusOmittedTripleKirchhoffColumnMap
        twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple x = 0 ↔
      x = 0
  unfold twoBandAnnulusOmittedTripleKirchhoffColumnMap
  decide +revert

theorem twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple_columnMap_ker_ne_bot :
    LinearMap.ker
      (twoBandAnnulusOmittedTripleKirchhoffColumnMap
        twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple) ≠ ⊥ := by
  let x : Fin 3 → F2 := fun _ => 1
  have hxker :
      x ∈ LinearMap.ker
        (twoBandAnnulusOmittedTripleKirchhoffColumnMap
          twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple) := by
    change
      twoBandAnnulusOmittedTripleKirchhoffColumnMap
          twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple x = 0
    unfold twoBandAnnulusOmittedTripleKirchhoffColumnMap
    decide
  have hxne : x ≠ 0 := by
    intro hxzero
    have hcoord := congrFun hxzero (0 : Fin 3)
    simp [x] at hcoord
  intro hker
  have hxbot : x ∈ (⊥ : Submodule F2 (Fin 3 → F2)) := by
    simpa [hker] using hxker
  have hxzero : x = 0 := by
    simpa using hxbot
  exact hxne hxzero

def twoBandAnnulusOmittedTripleCoordinates
    (omitted : Fin 3 → twoBandAnnulusGraph.edgeSet)
    (x : twoBandAnnulusGraph.edgeSet → F2) : Fin 3 → F2 :=
  fun i => x (omitted i)

theorem twoBandAnnulusMiddleOuterRadialKirchhoffControl_scalarKernel_omittedTripleCoordinates_mem_columnKernel
    {x : twoBandAnnulusGraph.edgeSet → F2}
    (hxker : x ∈ LinearMap.ker
      (theorem49BoundaryZeroKirchhoffScalarConstraintMap
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
        twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges)) :
    twoBandAnnulusOmittedTripleCoordinates
        twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple x ∈
      LinearMap.ker
        (twoBandAnnulusOmittedTripleKirchhoffColumnMap
          twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple) := by
  have hxmap :
      theorem49BoundaryZeroKirchhoffScalarConstraintMap
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
        twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges x = 0 := by
    simpa using hxker
  have hcontrol :
      ∀ e ∈ twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges, x e = 0 := by
    intro e he
    have hcoord := congrFun (congrArg Prod.fst hxmap) ⟨e, he⟩
    simpa [theorem49BoundaryZeroKirchhoffScalarConstraintMap] using hcoord
  have hkirchhoff :
      ∀ v ∈ twoBandAnnulusKirchhoffVertices,
        scalarVertexKirchhoffSum twoBandAnnulusGraph x v = 0 := by
    intro v hv
    have hcoord := congrFun (congrArg Prod.snd (congrArg Prod.snd hxmap)) ⟨v, hv⟩
    simpa [theorem49BoundaryZeroKirchhoffScalarConstraintMap] using hcoord
  have hxR03 : x tbaR03 = 0 :=
    hcontrol tbaR03 (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  have hxR14 : x tbaR14 = 0 :=
    hcontrol tbaR14 (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  have hxR25 : x tbaR25 = 0 :=
    hcontrol tbaR25 (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  have hxM34 : x tbaM34 = 0 :=
    hcontrol tbaM34 (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  have hxM45 : x tbaM45 = 0 :=
    hcontrol tbaM45 (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  have hxM53 : x tbaM53 = 0 :=
    hcontrol tbaM53 (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  change
    twoBandAnnulusOmittedTripleKirchhoffColumnMap
        twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple
        (twoBandAnnulusOmittedTripleCoordinates
          twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple x) = 0
  ext i
  fin_cases i
  · have hrow := hkirchhoff (3 : Fin 9) (by simp [twoBandAnnulusKirchhoffVertices])
    have hxR36 : x tbaR36 = 0 := by
      unfold scalarVertexKirchhoffSum at hrow
      rw [twoBandAnnulus_incidentEdgeFinset_three] at hrow
      rw [Finset.sum_insert] at hrow
      · rw [Finset.sum_insert] at hrow
        · rw [Finset.sum_insert] at hrow
          · rw [Finset.sum_singleton] at hrow
            simpa [hxR03, hxM34, hxM53] using hrow
          · decide
        · decide
      · decide
    have hR47 :
        ¬ (tbaR47 = tbaR03 ∨ tbaR47 = tbaR36 ∨
          tbaR47 = tbaM34 ∨ tbaR47 = tbaM53) := by
      decide
    have hR58 :
        ¬ (tbaR58 = tbaR03 ∨ tbaR58 = tbaR36 ∨
          tbaR58 = tbaM34 ∨ tbaR58 = tbaM53) := by
      decide
    change
      (∑ j : Fin 3,
        twoBandAnnulusOmittedTripleCoordinates
            twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple x j *
          twoBandAnnulusKirchhoffColumn
            (twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple j) (0 : Fin 3)) = 0
    rw [Fin.sum_univ_three]
    simp [twoBandAnnulusOmittedTripleCoordinates, twoBandAnnulusKirchhoffColumn,
      twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple,
      hR47, hR58, hxR36]
  · have hrow := hkirchhoff (4 : Fin 9) (by simp [twoBandAnnulusKirchhoffVertices])
    have hxR47 : x tbaR47 = 0 := by
      unfold scalarVertexKirchhoffSum at hrow
      rw [twoBandAnnulus_incidentEdgeFinset_four] at hrow
      rw [Finset.sum_insert] at hrow
      · rw [Finset.sum_insert] at hrow
        · rw [Finset.sum_insert] at hrow
          · rw [Finset.sum_singleton] at hrow
            simpa [hxR14, hxM34, hxM45] using hrow
          · decide
        · decide
      · decide
    have hR36 :
        ¬ (tbaR36 = tbaR14 ∨ tbaR36 = tbaR47 ∨
          tbaR36 = tbaM34 ∨ tbaR36 = tbaM45) := by
      decide
    have hR58 :
        ¬ (tbaR58 = tbaR14 ∨ tbaR58 = tbaR47 ∨
          tbaR58 = tbaM34 ∨ tbaR58 = tbaM45) := by
      decide
    change
      (∑ j : Fin 3,
        twoBandAnnulusOmittedTripleCoordinates
            twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple x j *
          twoBandAnnulusKirchhoffColumn
            (twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple j) (1 : Fin 3)) = 0
    rw [Fin.sum_univ_three]
    simp [twoBandAnnulusOmittedTripleCoordinates, twoBandAnnulusKirchhoffColumn,
      twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple,
      hR36, hR58, hxR47]
  · have hrow := hkirchhoff (5 : Fin 9) (by simp [twoBandAnnulusKirchhoffVertices])
    have hxR58 : x tbaR58 = 0 := by
      unfold scalarVertexKirchhoffSum at hrow
      rw [twoBandAnnulus_incidentEdgeFinset_five] at hrow
      rw [Finset.sum_insert] at hrow
      · rw [Finset.sum_insert] at hrow
        · rw [Finset.sum_insert] at hrow
          · rw [Finset.sum_singleton] at hrow
            simpa [hxR25, hxM45, hxM53] using hrow
          · decide
        · decide
      · decide
    have hR36 :
        ¬ (tbaR36 = tbaR25 ∨ tbaR36 = tbaR58 ∨
          tbaR36 = tbaM45 ∨ tbaR36 = tbaM53) := by
      decide
    have hR47 :
        ¬ (tbaR47 = tbaR25 ∨ tbaR47 = tbaR58 ∨
          tbaR47 = tbaM45 ∨ tbaR47 = tbaM53) := by
      decide
    change
      (∑ j : Fin 3,
        twoBandAnnulusOmittedTripleCoordinates
            twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple x j *
          twoBandAnnulusKirchhoffColumn
            (twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple j) (2 : Fin 3)) = 0
    rw [Fin.sum_univ_three]
    simp [twoBandAnnulusOmittedTripleCoordinates, twoBandAnnulusKirchhoffColumn,
      twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple,
      hR36, hR47, hxR58]

theorem twoBandAnnulusMiddleOuterRadialKirchhoffControl_scalarConstraintMap_ker_eq_bot_of_omittedTriple_columnMap_ker_eq_bot
    (hcolumn : LinearMap.ker
      (twoBandAnnulusOmittedTripleKirchhoffColumnMap
        twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple) = ⊥) :
    LinearMap.ker
      (theorem49BoundaryZeroKirchhoffScalarConstraintMap
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
        twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges) = ⊥ := by
  ext x
  constructor
  · intro hxker
    change x = 0
    have hxmap :
        theorem49BoundaryZeroKirchhoffScalarConstraintMap
          twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
          twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges x = 0 := by
      simpa using hxker
    have hcontrol :
        ∀ e ∈ twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges, x e = 0 := by
      intro e he
      have hcoord := congrFun (congrArg Prod.fst hxmap) ⟨e, he⟩
      simpa [theorem49BoundaryZeroKirchhoffScalarConstraintMap] using hcoord
    have hboundary :
        ∀ e ∈ selectedBoundarySupport
            twoBandAnnulusEmbedding.faceBoundary
            twoBandAnnulusEmbedding.faces
            twoBandAnnulusEmbedding.faces, x e = 0 := by
      intro e he
      have hcoord := congrFun (congrArg Prod.fst (congrArg Prod.snd hxmap)) ⟨e, he⟩
      simpa [theorem49BoundaryZeroKirchhoffScalarConstraintMap] using hcoord
    have hyker :=
      twoBandAnnulusMiddleOuterRadialKirchhoffControl_scalarKernel_omittedTripleCoordinates_mem_columnKernel
        (x := x) hxker
    have hybot :
        twoBandAnnulusOmittedTripleCoordinates
            twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple x ∈
          (⊥ : Submodule F2 (Fin 3 → F2)) := by
      simpa [hcolumn] using hyker
    have hyzero :
        twoBandAnnulusOmittedTripleCoordinates
            twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple x = 0 := by
      simpa using hybot
    funext e
    rcases twoBandAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact hboundary tbaO01 (by simp [twoBandAnnulus_selectedBoundarySupport_eq])
    · exact hboundary tbaO12 (by simp [twoBandAnnulus_selectedBoundarySupport_eq])
    · exact hboundary tbaO20 (by simp [twoBandAnnulus_selectedBoundarySupport_eq])
    · exact hboundary tbaI67 (by simp [twoBandAnnulus_selectedBoundarySupport_eq])
    · exact hboundary tbaI78 (by simp [twoBandAnnulus_selectedBoundarySupport_eq])
    · exact hboundary tbaI86 (by simp [twoBandAnnulus_selectedBoundarySupport_eq])
    · exact hcontrol tbaR03 (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
    · exact hcontrol tbaR14 (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
    · exact hcontrol tbaR25 (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
    · have hcoord := congrFun hyzero (0 : Fin 3)
      simpa [twoBandAnnulusOmittedTripleCoordinates,
        twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple] using hcoord
    · have hcoord := congrFun hyzero (1 : Fin 3)
      simpa [twoBandAnnulusOmittedTripleCoordinates,
        twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple] using hcoord
    · have hcoord := congrFun hyzero (2 : Fin 3)
      simpa [twoBandAnnulusOmittedTripleCoordinates,
        twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple] using hcoord
    · exact hcontrol tbaM34 (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
    · exact hcontrol tbaM45 (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
    · exact hcontrol tbaM53 (by simp [twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges])
  · intro hxbot
    change
      theorem49BoundaryZeroKirchhoffScalarConstraintMap
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
        twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges x = 0
    have hxzero : x = 0 := by
      simpa using hxbot
    simp [hxzero]

theorem twoBandAnnulusMiddleOuterRadialKirchhoffControl_scalarConstraintMap_ker_eq_bot_via_omittedTriple :
    LinearMap.ker
      (theorem49BoundaryZeroKirchhoffScalarConstraintMap
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
        twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges) = ⊥ :=
  twoBandAnnulusMiddleOuterRadialKirchhoffControl_scalarConstraintMap_ker_eq_bot_of_omittedTriple_columnMap_ker_eq_bot
    twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple_columnMap_ker_eq_bot

def twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension
    (y : Fin 3 → F2) : twoBandAnnulusGraph.edgeSet → F2 :=
  fun e =>
    if e = tbaR03 then y (0 : Fin 3)
    else if e = tbaR58 then y (1 : Fin 3)
    else if e = tbaM53 then y (2 : Fin 3)
    else 0

theorem twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple_columnKernel_lift_mem_scalarKernel
    {y : Fin 3 → F2}
    (hyker : y ∈ LinearMap.ker
      (twoBandAnnulusOmittedTripleKirchhoffColumnMap
        twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple)) :
    twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension y ∈
      LinearMap.ker
        (theorem49BoundaryZeroKirchhoffScalarConstraintMap
          twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
          twoBandAnnulusNoncontrollingSixKirchhoffControlEdges) := by
  have hymap :
      twoBandAnnulusOmittedTripleKirchhoffColumnMap
        twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple y = 0 := by
    simpa using hyker
  change
    theorem49BoundaryZeroKirchhoffScalarConstraintMap
      twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
      twoBandAnnulusNoncontrollingSixKirchhoffControlEdges
      (twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension y) = 0
  ext e
  · rcases e with ⟨e, he⟩
    change twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension y e = 0
    have he_cases :
        e = tbaM34 ∨ e = tbaM45 ∨ e = tbaR14 ∨
          e = tbaR25 ∨ e = tbaR36 ∨ e = tbaR47 := by
      simpa [twoBandAnnulusNoncontrollingSixKirchhoffControlEdges] using he
    rcases he_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
      clear hyker hymap <;> decide +revert
  · rcases e with ⟨e, he⟩
    change twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension y e = 0
    rw [twoBandAnnulus_selectedBoundarySupport_eq] at he
    have he_cases :
        e = tbaO01 ∨ e = tbaO12 ∨ e = tbaO20 ∨
          e = tbaI67 ∨ e = tbaI78 ∨ e = tbaI86 := by
      simpa using he
    rcases he_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
      clear hyker hymap <;> decide +revert
  · rcases e with ⟨v, hv⟩
    have hv_cases : v = (3 : Fin 9) ∨ v = (4 : Fin 9) ∨ v = (5 : Fin 9) := by
      simpa [twoBandAnnulusKirchhoffVertices] using hv
    rcases hv_cases with rfl | rfl | rfl
    · change scalarVertexKirchhoffSum twoBandAnnulusGraph
          (twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension y) (3 : Fin 9) = 0
      have hrow := congrFun hymap (0 : Fin 3)
      change
        (∑ j : Fin 3,
          y j * twoBandAnnulusKirchhoffColumn
            (twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple j) (0 : Fin 3)) = 0
        at hrow
      rw [Fin.sum_univ_three] at hrow
      unfold scalarVertexKirchhoffSum
      rw [twoBandAnnulus_incidentEdgeFinset_three]
      rw [Finset.sum_insert]
      · rw [Finset.sum_insert]
        · rw [Finset.sum_insert]
          · rw [Finset.sum_singleton]
            clear hyker hymap
            revert hrow
            decide +revert
          · decide
        · decide
      · decide
    · change scalarVertexKirchhoffSum twoBandAnnulusGraph
          (twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension y) (4 : Fin 9) = 0
      have hrow := congrFun hymap (1 : Fin 3)
      change
        (∑ j : Fin 3,
          y j * twoBandAnnulusKirchhoffColumn
            (twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple j) (1 : Fin 3)) = 0
        at hrow
      rw [Fin.sum_univ_three] at hrow
      unfold scalarVertexKirchhoffSum
      rw [twoBandAnnulus_incidentEdgeFinset_four]
      rw [Finset.sum_insert]
      · rw [Finset.sum_insert]
        · rw [Finset.sum_insert]
          · rw [Finset.sum_singleton]
            clear hyker hymap
            revert hrow
            decide +revert
          · decide
        · decide
      · decide
    · change scalarVertexKirchhoffSum twoBandAnnulusGraph
          (twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension y) (5 : Fin 9) = 0
      have hrow := congrFun hymap (2 : Fin 3)
      change
        (∑ j : Fin 3,
          y j * twoBandAnnulusKirchhoffColumn
            (twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple j) (2 : Fin 3)) = 0
        at hrow
      rw [Fin.sum_univ_three] at hrow
      unfold scalarVertexKirchhoffSum
      rw [twoBandAnnulus_incidentEdgeFinset_five]
      rw [Finset.sum_insert]
      · rw [Finset.sum_insert]
        · rw [Finset.sum_insert]
          · rw [Finset.sum_singleton]
            clear hyker hymap
            revert hrow
            decide +revert
          · decide
        · decide
      · decide

theorem twoBandAnnulusNoncontrollingSixKirchhoffControl_scalarConstraintMap_ker_ne_bot_of_omittedTriple_columnMap_ker_ne_bot
    (hcolumn : LinearMap.ker
      (twoBandAnnulusOmittedTripleKirchhoffColumnMap
        twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple) ≠ ⊥) :
    LinearMap.ker
      (theorem49BoundaryZeroKirchhoffScalarConstraintMap
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
        twoBandAnnulusNoncontrollingSixKirchhoffControlEdges) ≠ ⊥ := by
  intro hscalar
  apply hcolumn
  ext y
  constructor
  · intro hyker
    have hxker :=
      twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple_columnKernel_lift_mem_scalarKernel
        (y := y) hyker
    have hxbot :
        twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension y ∈
          (⊥ : Submodule F2 (twoBandAnnulusGraph.edgeSet → F2)) := by
      simpa [hscalar] using hxker
    have hxzero : twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension y = 0 := by
      simpa using hxbot
    change y = 0
    funext i
    fin_cases i
    · have hcoord := congrFun hxzero tbaR03
      simpa [twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension] using hcoord
    · have hcoord := congrFun hxzero tbaR58
      have hne : tbaR58 ≠ tbaR03 := by
        decide
      simpa [twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension, hne] using hcoord
    · have hcoord := congrFun hxzero tbaM53
      have hneR03 : tbaM53 ≠ tbaR03 := by
        decide
      have hneR58 : tbaM53 ≠ tbaR58 := by
        decide
      simpa [twoBandAnnulusNoncontrollingSixOmittedTripleScalarExtension, hneR03, hneR58]
        using hcoord
  · intro hybot
    change
      twoBandAnnulusOmittedTripleKirchhoffColumnMap
        twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple y = 0
    have hyzero : y = 0 := by
      simpa using hybot
    simp [hyzero]

theorem twoBandAnnulusNoncontrollingSixKirchhoffControl_scalarConstraintMap_ker_ne_bot_via_omittedTriple :
    LinearMap.ker
      (theorem49BoundaryZeroKirchhoffScalarConstraintMap
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
        twoBandAnnulusNoncontrollingSixKirchhoffControlEdges) ≠ ⊥ :=
  twoBandAnnulusNoncontrollingSixKirchhoffControl_scalarConstraintMap_ker_ne_bot_of_omittedTriple_columnMap_ker_ne_bot
    twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple_columnMap_ker_ne_bot

theorem twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple_no_columnKernel_evader :
    ∀ y : Fin 3 → F2,
      twoBandAnnulusOmittedTripleKirchhoffColumnMap
          twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple y = 0 →
      y = 0 :=
  LinearMap.ker_eq_bot'.mp
    twoBandAnnulusMiddleOuterRadialKirchhoffOmittedTriple_columnMap_ker_eq_bot

theorem twoBandAnnulusMiddleOuterRadialKirchhoffControl_no_scalarKernel_evader_via_omittedTriple :
    ∀ x : twoBandAnnulusGraph.edgeSet → F2,
      theorem49BoundaryZeroKirchhoffScalarConstraintMap
          twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
          twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges x = 0 →
      x = 0 :=
  LinearMap.ker_eq_bot'.mp
    twoBandAnnulusMiddleOuterRadialKirchhoffControl_scalarConstraintMap_ker_eq_bot_via_omittedTriple

theorem twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple_exists_columnKernel_evader :
    ∃ y : Fin 3 → F2,
      twoBandAnnulusOmittedTripleKirchhoffColumnMap
          twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple y = 0 ∧
      y ≠ 0 := by
  rcases (Submodule.ne_bot_iff _).mp
      twoBandAnnulusNoncontrollingSixKirchhoffOmittedTriple_columnMap_ker_ne_bot with
    ⟨y, hyker, hyne⟩
  exact ⟨y, by simpa using hyker, hyne⟩

theorem twoBandAnnulusNoncontrollingSixKirchhoffControl_exists_scalarKernel_evader_via_omittedTriple :
    ∃ x : twoBandAnnulusGraph.edgeSet → F2,
      theorem49BoundaryZeroKirchhoffScalarConstraintMap
          twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
          twoBandAnnulusNoncontrollingSixKirchhoffControlEdges x = 0 ∧
      x ≠ 0 := by
  rcases (Submodule.ne_bot_iff _).mp
      twoBandAnnulusNoncontrollingSixKirchhoffControl_scalarConstraintMap_ker_ne_bot_via_omittedTriple with
    ⟨x, hxker, hxne⟩
  exact ⟨x, by simpa using hxker, hxne⟩

theorem twoBandAnnulusIndicator_mem_planarBoundaryZeroSubmodule_of_subset_interior
    (S : Finset twoBandAnnulusGraph.edgeSet)
    (hS : S ⊆ twoBandAnnulusInteriorEdges) :
    indicatorChain red S ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding := by
  intro e heBoundary
  by_cases heS : e ∈ S
  · have heInterior : e ∈ interiorEdgeSupport
        twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces := by
      rw [twoBandAnnulus_interiorEdgeSupport_eq]
      exact hS heS
    exact False.elim
      ((Finset.disjoint_left.1
        (selectedBoundarySupport_disjoint_interiorEdgeSupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces)) heBoundary heInterior)
  · simp [indicatorChain, heS]

def twoBandAnnulusWithoutTbaM34KirchhoffEvader :
    twoBandAnnulusGraph.edgeSet → Color :=
  indicatorChain red ({tbaR36, tbaR47, tbaM34} : Finset twoBandAnnulusGraph.edgeSet)

def twoBandAnnulusWithoutTbaM45KirchhoffEvader :
    twoBandAnnulusGraph.edgeSet → Color :=
  indicatorChain red ({tbaR47, tbaR58, tbaM45} : Finset twoBandAnnulusGraph.edgeSet)

def twoBandAnnulusWithoutTbaM53KirchhoffEvader :
    twoBandAnnulusGraph.edgeSet → Color :=
  indicatorChain red ({tbaR36, tbaR58, tbaM53} : Finset twoBandAnnulusGraph.edgeSet)

def twoBandAnnulusWithoutTbaR03KirchhoffEvader :
    twoBandAnnulusGraph.edgeSet → Color :=
  indicatorChain red ({tbaR03, tbaR36} : Finset twoBandAnnulusGraph.edgeSet)

def twoBandAnnulusWithoutTbaR14KirchhoffEvader :
    twoBandAnnulusGraph.edgeSet → Color :=
  indicatorChain red ({tbaR14, tbaR47} : Finset twoBandAnnulusGraph.edgeSet)

def twoBandAnnulusWithoutTbaR25KirchhoffEvader :
    twoBandAnnulusGraph.edgeSet → Color :=
  indicatorChain red ({tbaR25, tbaR58} : Finset twoBandAnnulusGraph.edgeSet)

theorem twoBandAnnulusWithoutTbaM34KirchhoffEvader_mem_planarBoundaryZeroSubmodule :
    twoBandAnnulusWithoutTbaM34KirchhoffEvader ∈
      planarBoundaryZeroSubmodule twoBandAnnulusEmbedding :=
  twoBandAnnulusIndicator_mem_planarBoundaryZeroSubmodule_of_subset_interior
    {tbaR36, tbaR47, tbaM34} (by
      intro e he
      simp [twoBandAnnulusInteriorEdges] at he ⊢
      tauto)

theorem twoBandAnnulusWithoutTbaM45KirchhoffEvader_mem_planarBoundaryZeroSubmodule :
    twoBandAnnulusWithoutTbaM45KirchhoffEvader ∈
      planarBoundaryZeroSubmodule twoBandAnnulusEmbedding :=
  twoBandAnnulusIndicator_mem_planarBoundaryZeroSubmodule_of_subset_interior
    {tbaR47, tbaR58, tbaM45} (by
      intro e he
      simp [twoBandAnnulusInteriorEdges] at he ⊢
      tauto)

theorem twoBandAnnulusWithoutTbaM53KirchhoffEvader_mem_planarBoundaryZeroSubmodule :
    twoBandAnnulusWithoutTbaM53KirchhoffEvader ∈
      planarBoundaryZeroSubmodule twoBandAnnulusEmbedding :=
  twoBandAnnulusIndicator_mem_planarBoundaryZeroSubmodule_of_subset_interior
    {tbaR36, tbaR58, tbaM53} (by
      intro e he
      simp [twoBandAnnulusInteriorEdges] at he ⊢
      tauto)

theorem twoBandAnnulusWithoutTbaR03KirchhoffEvader_mem_planarBoundaryZeroSubmodule :
    twoBandAnnulusWithoutTbaR03KirchhoffEvader ∈
      planarBoundaryZeroSubmodule twoBandAnnulusEmbedding :=
  twoBandAnnulusIndicator_mem_planarBoundaryZeroSubmodule_of_subset_interior
    {tbaR03, tbaR36} (by
      intro e he
      simp [twoBandAnnulusInteriorEdges] at he ⊢
      tauto)

theorem twoBandAnnulusWithoutTbaR14KirchhoffEvader_mem_planarBoundaryZeroSubmodule :
    twoBandAnnulusWithoutTbaR14KirchhoffEvader ∈
      planarBoundaryZeroSubmodule twoBandAnnulusEmbedding :=
  twoBandAnnulusIndicator_mem_planarBoundaryZeroSubmodule_of_subset_interior
    {tbaR14, tbaR47} (by
      intro e he
      simp [twoBandAnnulusInteriorEdges] at he ⊢
      tauto)

theorem twoBandAnnulusWithoutTbaR25KirchhoffEvader_mem_planarBoundaryZeroSubmodule :
    twoBandAnnulusWithoutTbaR25KirchhoffEvader ∈
      planarBoundaryZeroSubmodule twoBandAnnulusEmbedding :=
  twoBandAnnulusIndicator_mem_planarBoundaryZeroSubmodule_of_subset_interior
    {tbaR25, tbaR58} (by
      intro e he
      simp [twoBandAnnulusInteriorEdges] at he ⊢
      tauto)

theorem twoBandAnnulusWithoutTbaM34KirchhoffEvader_mem_kirchhoffSubmodule :
    twoBandAnnulusWithoutTbaM34KirchhoffEvader ∈
      kirchhoffSubmodule twoBandAnnulusGraph twoBandAnnulusKirchhoffVertices := by
  intro v hv
  have hv_cases : v = (3 : Fin 9) ∨ v = (4 : Fin 9) ∨ v = (5 : Fin 9) := by
    simpa [twoBandAnnulusKirchhoffVertices] using hv
  rcases hv_cases with rfl | rfl | rfl <;>
    unfold vertexKirchhoffSum incidentEdgeFinset
  all_goals decide

theorem twoBandAnnulusWithoutTbaM45KirchhoffEvader_mem_kirchhoffSubmodule :
    twoBandAnnulusWithoutTbaM45KirchhoffEvader ∈
      kirchhoffSubmodule twoBandAnnulusGraph twoBandAnnulusKirchhoffVertices := by
  intro v hv
  have hv_cases : v = (3 : Fin 9) ∨ v = (4 : Fin 9) ∨ v = (5 : Fin 9) := by
    simpa [twoBandAnnulusKirchhoffVertices] using hv
  rcases hv_cases with rfl | rfl | rfl <;>
    unfold vertexKirchhoffSum incidentEdgeFinset
  all_goals decide

theorem twoBandAnnulusWithoutTbaM53KirchhoffEvader_mem_kirchhoffSubmodule :
    twoBandAnnulusWithoutTbaM53KirchhoffEvader ∈
      kirchhoffSubmodule twoBandAnnulusGraph twoBandAnnulusKirchhoffVertices := by
  intro v hv
  have hv_cases : v = (3 : Fin 9) ∨ v = (4 : Fin 9) ∨ v = (5 : Fin 9) := by
    simpa [twoBandAnnulusKirchhoffVertices] using hv
  rcases hv_cases with rfl | rfl | rfl <;>
    unfold vertexKirchhoffSum incidentEdgeFinset
  all_goals decide

theorem twoBandAnnulusWithoutTbaR03KirchhoffEvader_mem_kirchhoffSubmodule :
    twoBandAnnulusWithoutTbaR03KirchhoffEvader ∈
      kirchhoffSubmodule twoBandAnnulusGraph twoBandAnnulusKirchhoffVertices := by
  intro v hv
  have hv_cases : v = (3 : Fin 9) ∨ v = (4 : Fin 9) ∨ v = (5 : Fin 9) := by
    simpa [twoBandAnnulusKirchhoffVertices] using hv
  rcases hv_cases with rfl | rfl | rfl <;>
    unfold vertexKirchhoffSum incidentEdgeFinset
  all_goals decide

theorem twoBandAnnulusWithoutTbaR14KirchhoffEvader_mem_kirchhoffSubmodule :
    twoBandAnnulusWithoutTbaR14KirchhoffEvader ∈
      kirchhoffSubmodule twoBandAnnulusGraph twoBandAnnulusKirchhoffVertices := by
  intro v hv
  have hv_cases : v = (3 : Fin 9) ∨ v = (4 : Fin 9) ∨ v = (5 : Fin 9) := by
    simpa [twoBandAnnulusKirchhoffVertices] using hv
  rcases hv_cases with rfl | rfl | rfl <;>
    unfold vertexKirchhoffSum incidentEdgeFinset
  all_goals decide

theorem twoBandAnnulusWithoutTbaR25KirchhoffEvader_mem_kirchhoffSubmodule :
    twoBandAnnulusWithoutTbaR25KirchhoffEvader ∈
      kirchhoffSubmodule twoBandAnnulusGraph twoBandAnnulusKirchhoffVertices := by
  intro v hv
  have hv_cases : v = (3 : Fin 9) ∨ v = (4 : Fin 9) ∨ v = (5 : Fin 9) := by
    simpa [twoBandAnnulusKirchhoffVertices] using hv
  rcases hv_cases with rfl | rfl | rfl <;>
    unfold vertexKirchhoffSum incidentEdgeFinset
  all_goals decide

theorem twoBandAnnulus_canonicalControl_without_tbaM34_has_boundaryZeroKirchhoff_evader :
    twoBandAnnulusWithoutTbaM34KirchhoffEvader ∈ theorem49BoundaryZeroKirchhoffSubspace
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices ∧
      twoBandAnnulusWithoutTbaM34KirchhoffEvader tbaM45 = 0 ∧
      twoBandAnnulusWithoutTbaM34KirchhoffEvader tbaM53 = 0 ∧
      twoBandAnnulusWithoutTbaM34KirchhoffEvader tbaR03 = 0 ∧
      twoBandAnnulusWithoutTbaM34KirchhoffEvader tbaR14 = 0 ∧
      twoBandAnnulusWithoutTbaM34KirchhoffEvader tbaR25 = 0 ∧
      twoBandAnnulusWithoutTbaM34KirchhoffEvader tbaM34 = red ∧
      twoBandAnnulusWithoutTbaM34KirchhoffEvader ≠ 0 := by
  refine ⟨⟨twoBandAnnulusWithoutTbaM34KirchhoffEvader_mem_kirchhoffSubmodule,
    twoBandAnnulusWithoutTbaM34KirchhoffEvader_mem_planarBoundaryZeroSubmodule⟩,
    by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro hzero
  have hvalue := congrFun hzero tbaM34
  have hred : twoBandAnnulusWithoutTbaM34KirchhoffEvader tbaM34 = red := by
    decide
  rw [hred] at hvalue
  exact red_ne_zero hvalue

theorem twoBandAnnulus_canonicalControl_without_tbaM45_has_boundaryZeroKirchhoff_evader :
    twoBandAnnulusWithoutTbaM45KirchhoffEvader ∈ theorem49BoundaryZeroKirchhoffSubspace
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices ∧
      twoBandAnnulusWithoutTbaM45KirchhoffEvader tbaM34 = 0 ∧
      twoBandAnnulusWithoutTbaM45KirchhoffEvader tbaM53 = 0 ∧
      twoBandAnnulusWithoutTbaM45KirchhoffEvader tbaR03 = 0 ∧
      twoBandAnnulusWithoutTbaM45KirchhoffEvader tbaR14 = 0 ∧
      twoBandAnnulusWithoutTbaM45KirchhoffEvader tbaR25 = 0 ∧
      twoBandAnnulusWithoutTbaM45KirchhoffEvader tbaM45 = red ∧
      twoBandAnnulusWithoutTbaM45KirchhoffEvader ≠ 0 := by
  refine ⟨⟨twoBandAnnulusWithoutTbaM45KirchhoffEvader_mem_kirchhoffSubmodule,
    twoBandAnnulusWithoutTbaM45KirchhoffEvader_mem_planarBoundaryZeroSubmodule⟩,
    by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro hzero
  have hvalue := congrFun hzero tbaM45
  have hred : twoBandAnnulusWithoutTbaM45KirchhoffEvader tbaM45 = red := by
    decide
  rw [hred] at hvalue
  exact red_ne_zero hvalue

theorem twoBandAnnulus_canonicalControl_without_tbaM53_has_boundaryZeroKirchhoff_evader :
    twoBandAnnulusWithoutTbaM53KirchhoffEvader ∈ theorem49BoundaryZeroKirchhoffSubspace
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices ∧
      twoBandAnnulusWithoutTbaM53KirchhoffEvader tbaM34 = 0 ∧
      twoBandAnnulusWithoutTbaM53KirchhoffEvader tbaM45 = 0 ∧
      twoBandAnnulusWithoutTbaM53KirchhoffEvader tbaR03 = 0 ∧
      twoBandAnnulusWithoutTbaM53KirchhoffEvader tbaR14 = 0 ∧
      twoBandAnnulusWithoutTbaM53KirchhoffEvader tbaR25 = 0 ∧
      twoBandAnnulusWithoutTbaM53KirchhoffEvader tbaM53 = red ∧
      twoBandAnnulusWithoutTbaM53KirchhoffEvader ≠ 0 := by
  refine ⟨⟨twoBandAnnulusWithoutTbaM53KirchhoffEvader_mem_kirchhoffSubmodule,
    twoBandAnnulusWithoutTbaM53KirchhoffEvader_mem_planarBoundaryZeroSubmodule⟩,
    by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro hzero
  have hvalue := congrFun hzero tbaM53
  have hred : twoBandAnnulusWithoutTbaM53KirchhoffEvader tbaM53 = red := by
    decide
  rw [hred] at hvalue
  exact red_ne_zero hvalue

theorem twoBandAnnulus_canonicalControl_without_tbaR03_has_boundaryZeroKirchhoff_evader :
    twoBandAnnulusWithoutTbaR03KirchhoffEvader ∈ theorem49BoundaryZeroKirchhoffSubspace
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices ∧
      twoBandAnnulusWithoutTbaR03KirchhoffEvader tbaM34 = 0 ∧
      twoBandAnnulusWithoutTbaR03KirchhoffEvader tbaM45 = 0 ∧
      twoBandAnnulusWithoutTbaR03KirchhoffEvader tbaM53 = 0 ∧
      twoBandAnnulusWithoutTbaR03KirchhoffEvader tbaR14 = 0 ∧
      twoBandAnnulusWithoutTbaR03KirchhoffEvader tbaR25 = 0 ∧
      twoBandAnnulusWithoutTbaR03KirchhoffEvader tbaR03 = red ∧
      twoBandAnnulusWithoutTbaR03KirchhoffEvader ≠ 0 := by
  refine ⟨⟨twoBandAnnulusWithoutTbaR03KirchhoffEvader_mem_kirchhoffSubmodule,
    twoBandAnnulusWithoutTbaR03KirchhoffEvader_mem_planarBoundaryZeroSubmodule⟩,
    by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro hzero
  have hvalue := congrFun hzero tbaR03
  have hred : twoBandAnnulusWithoutTbaR03KirchhoffEvader tbaR03 = red := by
    decide
  rw [hred] at hvalue
  exact red_ne_zero hvalue

theorem twoBandAnnulus_canonicalControl_without_tbaR14_has_boundaryZeroKirchhoff_evader :
    twoBandAnnulusWithoutTbaR14KirchhoffEvader ∈ theorem49BoundaryZeroKirchhoffSubspace
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices ∧
      twoBandAnnulusWithoutTbaR14KirchhoffEvader tbaM34 = 0 ∧
      twoBandAnnulusWithoutTbaR14KirchhoffEvader tbaM45 = 0 ∧
      twoBandAnnulusWithoutTbaR14KirchhoffEvader tbaM53 = 0 ∧
      twoBandAnnulusWithoutTbaR14KirchhoffEvader tbaR03 = 0 ∧
      twoBandAnnulusWithoutTbaR14KirchhoffEvader tbaR25 = 0 ∧
      twoBandAnnulusWithoutTbaR14KirchhoffEvader tbaR14 = red ∧
      twoBandAnnulusWithoutTbaR14KirchhoffEvader ≠ 0 := by
  refine ⟨⟨twoBandAnnulusWithoutTbaR14KirchhoffEvader_mem_kirchhoffSubmodule,
    twoBandAnnulusWithoutTbaR14KirchhoffEvader_mem_planarBoundaryZeroSubmodule⟩,
    by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro hzero
  have hvalue := congrFun hzero tbaR14
  have hred : twoBandAnnulusWithoutTbaR14KirchhoffEvader tbaR14 = red := by
    decide
  rw [hred] at hvalue
  exact red_ne_zero hvalue

theorem twoBandAnnulus_canonicalControl_without_tbaR25_has_boundaryZeroKirchhoff_evader :
    twoBandAnnulusWithoutTbaR25KirchhoffEvader ∈ theorem49BoundaryZeroKirchhoffSubspace
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices ∧
      twoBandAnnulusWithoutTbaR25KirchhoffEvader tbaM34 = 0 ∧
      twoBandAnnulusWithoutTbaR25KirchhoffEvader tbaM45 = 0 ∧
      twoBandAnnulusWithoutTbaR25KirchhoffEvader tbaM53 = 0 ∧
      twoBandAnnulusWithoutTbaR25KirchhoffEvader tbaR03 = 0 ∧
      twoBandAnnulusWithoutTbaR25KirchhoffEvader tbaR14 = 0 ∧
      twoBandAnnulusWithoutTbaR25KirchhoffEvader tbaR25 = red ∧
      twoBandAnnulusWithoutTbaR25KirchhoffEvader ≠ 0 := by
  refine ⟨⟨twoBandAnnulusWithoutTbaR25KirchhoffEvader_mem_kirchhoffSubmodule,
    twoBandAnnulusWithoutTbaR25KirchhoffEvader_mem_planarBoundaryZeroSubmodule⟩,
    by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro hzero
  have hvalue := congrFun hzero tbaR25
  have hred : twoBandAnnulusWithoutTbaR25KirchhoffEvader tbaR25 = red := by
    decide
  rw [hred] at hvalue
  exact red_ne_zero hvalue

noncomputable def twoBandAnnulusScalarConstraintMap
    (control : Finset twoBandAnnulusGraph.edgeSet) :
    (twoBandAnnulusGraph.edgeSet → F2) →ₗ[F2]
      (((e : {e : twoBandAnnulusGraph.edgeSet // e ∈ control}) → F2) ×
        (Fin 6 → F2) × (Fin 3 → F2)) where
  toFun x :=
    (fun e => x e.1,
      (fun i => match i with
        | ⟨0, _⟩ => x tbaO01
        | ⟨1, _⟩ => x tbaO12
        | ⟨2, _⟩ => x tbaO20
        | ⟨3, _⟩ => x tbaI67
        | ⟨4, _⟩ => x tbaI78
        | ⟨5, _⟩ => x tbaI86),
      (fun i => match i with
        | ⟨0, _⟩ => x tbaR03 + x tbaR36 + x tbaM34 + x tbaM53
        | ⟨1, _⟩ => x tbaR14 + x tbaR47 + x tbaM34 + x tbaM45
        | ⟨2, _⟩ => x tbaR25 + x tbaR58 + x tbaM45 + x tbaM53))
  map_add' x y := by
    ext e
    · rfl
    · fin_cases e <;> rfl
    · fin_cases e <;> simp <;> abel_nf
  map_smul' a x := by
    ext e
    · rfl
    · fin_cases e <;> rfl
    · fin_cases e <;> simp <;> ring_nf

theorem twoBandAnnulusScalarConstraintMap_finrank_lt_of_control_card_le_five
    (control : Finset twoBandAnnulusGraph.edgeSet) (hcard : control.card ≤ 5) :
    Module.finrank F2
      ((((e : {e : twoBandAnnulusGraph.edgeSet // e ∈ control}) → F2) ×
        (Fin 6 → F2) × (Fin 3 → F2))) <
      Module.finrank F2 (twoBandAnnulusGraph.edgeSet → F2) := by
  have hdomain : Module.finrank F2 (twoBandAnnulusGraph.edgeSet → F2) = 15 := by
    rw [Module.finrank_pi]
    decide
  have hcodomain : Module.finrank F2
      ((((e : {e : twoBandAnnulusGraph.edgeSet // e ∈ control}) → F2) ×
        (Fin 6 → F2) × (Fin 3 → F2))) ≤ 14 := by
    rw [Module.finrank_prod, Module.finrank_prod]
    simp
    omega
  omega

theorem twoBandAnnulusScalarConstraintMap_exists_kernel_ne_zero_of_control_card_le_five
    (control : Finset twoBandAnnulusGraph.edgeSet) (hcard : control.card ≤ 5) :
    ∃ x : twoBandAnnulusGraph.edgeSet → F2,
      x ∈ LinearMap.ker (twoBandAnnulusScalarConstraintMap control) ∧ x ≠ 0 := by
  refine exists_nonzero_f2ScalarChain_mem_ker_of_finrank_lt_card
    (twoBandAnnulusScalarConstraintMap control) ?_
  have hlt :=
    twoBandAnnulusScalarConstraintMap_finrank_lt_of_control_card_le_five
      control hcard
  have hdomain :
      Module.finrank F2 (twoBandAnnulusGraph.edgeSet → F2) =
        Fintype.card twoBandAnnulusGraph.edgeSet := by
    rw [Module.finrank_pi]
  rwa [hdomain] at hlt

theorem twoBandAnnulusBoundaryZeroKirchhoffScalarConstraintSpace_finrank_lt_of_control_card_le_five
    (control : Finset twoBandAnnulusGraph.edgeSet) (hcard : control.card ≤ 5) :
    Module.finrank F2
      (theorem49BoundaryZeroKirchhoffScalarConstraintSpace
        twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices control) <
      Fintype.card twoBandAnnulusGraph.edgeSet := by
  refine theorem49BoundaryZeroKirchhoffScalarConstraintSpace_finrank_lt_of_card_sum_lt
    twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices control ?_
  have hboundary :
      Fintype.card {e : twoBandAnnulusGraph.edgeSet //
        e ∈ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces} = 6 := by
    rw [twoBandAnnulus_selectedBoundarySupport_eq]
    decide
  have hvertices :
      Fintype.card {v : Fin 9 // v ∈ twoBandAnnulusKirchhoffVertices} = 3 := by
    decide
  have hedge : Fintype.card twoBandAnnulusGraph.edgeSet = 15 := by
    decide
  rw [hboundary, hvertices, hedge]
  omega

def twoBandAnnulusRedScalarChain (x : twoBandAnnulusGraph.edgeSet → F2) :
    twoBandAnnulusGraph.edgeSet → Color :=
  redScalarColorChain x

theorem twoBandAnnulusRedScalarChain_ne_zero_of_ne_zero
    {x : twoBandAnnulusGraph.edgeSet → F2} (hx : x ≠ 0) :
    twoBandAnnulusRedScalarChain x ≠ 0 := by
  simpa [twoBandAnnulusRedScalarChain] using
    (redScalarColorChain_ne_zero_of_ne_zero (E := twoBandAnnulusGraph.edgeSet) hx)

theorem twoBandAnnulusRedScalarChain_vertexKirchhoff_three
    (x : twoBandAnnulusGraph.edgeSet → F2)
    (hk : x tbaR03 + x tbaR36 + x tbaM34 + x tbaM53 = 0) :
    vertexKirchhoffSum twoBandAnnulusGraph
        (twoBandAnnulusRedScalarChain x) (3 : Fin 9) = 0 := by
  unfold vertexKirchhoffSum
  rw [twoBandAnnulus_incidentEdgeFinset_three]
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        ext
        · simpa [twoBandAnnulusRedScalarChain, redScalarColorChain, red, add_assoc] using hk
        · simp [twoBandAnnulusRedScalarChain, redScalarColorChain, red]
      · decide
    · decide
  · decide

theorem twoBandAnnulusRedScalarChain_vertexKirchhoff_four
    (x : twoBandAnnulusGraph.edgeSet → F2)
    (hk : x tbaR14 + x tbaR47 + x tbaM34 + x tbaM45 = 0) :
    vertexKirchhoffSum twoBandAnnulusGraph
        (twoBandAnnulusRedScalarChain x) (4 : Fin 9) = 0 := by
  unfold vertexKirchhoffSum
  rw [twoBandAnnulus_incidentEdgeFinset_four]
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        ext
        · simpa [twoBandAnnulusRedScalarChain, redScalarColorChain, red, add_assoc] using hk
        · simp [twoBandAnnulusRedScalarChain, redScalarColorChain, red]
      · decide
    · decide
  · decide

theorem twoBandAnnulusRedScalarChain_vertexKirchhoff_five
    (x : twoBandAnnulusGraph.edgeSet → F2)
    (hk : x tbaR25 + x tbaR58 + x tbaM45 + x tbaM53 = 0) :
    vertexKirchhoffSum twoBandAnnulusGraph
        (twoBandAnnulusRedScalarChain x) (5 : Fin 9) = 0 := by
  unfold vertexKirchhoffSum
  rw [twoBandAnnulus_incidentEdgeFinset_five]
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        ext
        · simpa [twoBandAnnulusRedScalarChain, redScalarColorChain, red, add_assoc] using hk
        · simp [twoBandAnnulusRedScalarChain, redScalarColorChain, red]
      · decide
    · decide
  · decide

theorem twoBandAnnulus_boundaryZeroKirchhoff_has_evader_of_control_card_le_five
    (control : Finset twoBandAnnulusGraph.edgeSet) (hcard : control.card ≤ 5) :
    ∃ z : twoBandAnnulusGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices ∧
      (∀ e ∈ control, z e = 0) ∧ z ≠ 0 := by
  refine exists_redScalarColorChain_mem_theorem49BoundaryZeroKirchhoffSubspace_of_card_sum_lt
    twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices control ?_
  have hboundary :
      Fintype.card {e : twoBandAnnulusGraph.edgeSet //
        e ∈ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces} = 6 := by
    rw [twoBandAnnulus_selectedBoundarySupport_eq]
    decide
  have hvertices :
      Fintype.card {v : Fin 9 // v ∈ twoBandAnnulusKirchhoffVertices} = 3 := by
    decide
  have hedge : Fintype.card twoBandAnnulusGraph.edgeSet = 15 := by
    decide
  rw [hboundary, hvertices, hedge]
  omega

theorem twoBandAnnulus_boundaryZeroKirchhoff_minimalControl_profile :
    (∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
      (∀ e ∈ twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges, z e = 0) →
      z = 0) ∧
    (∀ control : Finset twoBandAnnulusGraph.edgeSet,
      control.card ≤ 5 →
        ∃ z : twoBandAnnulusGraph.edgeSet → Color,
          z ∈ theorem49BoundaryZeroKirchhoffSubspace
              twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices ∧
          (∀ e ∈ control, z e = 0) ∧ z ≠ 0) := by
  constructor
  · intro z hz hcontrol
    exact twoBandAnnulus_boundaryZeroKirchhoff_no_evader_of_middleOuterRadialControl
      z hz hcontrol
  · exact twoBandAnnulus_boundaryZeroKirchhoff_has_evader_of_control_card_le_five

theorem twoBandAnnulus_boundaryZero_has_evader_of_control_card_le_eight
    (control : Finset twoBandAnnulusGraph.edgeSet) (hcard : control.card ≤ 8) :
    ∃ z : twoBandAnnulusGraph.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding ∧
      (∀ e ∈ control, z e = 0) ∧ z ≠ 0 := by
  refine exists_mem_planarBoundaryZeroSubmodule_of_control_card_add_boundary_card_lt
    twoBandAnnulusEmbedding control ?_
  have hboundary :
      Fintype.card {e : twoBandAnnulusGraph.edgeSet //
        e ∈ selectedBoundarySupport
          twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces
          twoBandAnnulusEmbedding.faces} = 6 := by
    rw [twoBandAnnulus_selectedBoundarySupport_eq]
    decide
  have hedge : Fintype.card twoBandAnnulusGraph.edgeSet = 15 := by
    decide
  rw [hboundary, hedge]
  omega

theorem twoBandAnnulus_boundaryZero_minimalControl_profile :
    (∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
      (∀ e ∈ twoBandAnnulusInteriorEdges, z e = 0) →
      z = 0) ∧
    (∀ control : Finset twoBandAnnulusGraph.edgeSet,
      control.card ≤ 8 →
        ∃ z : twoBandAnnulusGraph.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding ∧
          (∀ e ∈ control, z e = 0) ∧ z ≠ 0) := by
  constructor
  · intro z hzBoundary hcontrol
    exact twoBandAnnulus_boundaryZero_no_evader_of_vanishes_on_interiorEdges
      z hzBoundary hcontrol
  · exact twoBandAnnulus_boundaryZero_has_evader_of_control_card_le_eight

theorem twoBandAnnulus_boundaryZero_exactMinimumControlCard :
    (∃ control : Finset twoBandAnnulusGraph.edgeSet,
      control.card = 9 ∧
        ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
          (∀ e ∈ control, z e = 0) →
          z = 0) ∧
    (∀ control : Finset twoBandAnnulusGraph.edgeSet,
      (∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
        (∀ e ∈ control, z e = 0) →
        z = 0) →
      9 ≤ control.card) := by
  constructor
  · refine ⟨twoBandAnnulusInteriorEdges, ?_, ?_⟩
    · decide
    · intro z hzBoundary hcontrol
      exact twoBandAnnulus_boundaryZero_no_evader_of_vanishes_on_interiorEdges
        z hzBoundary hcontrol
  · intro control hcontrol
    by_contra hnotLower
    have hcard : control.card ≤ 8 := by omega
    rcases twoBandAnnulus_boundaryZero_has_evader_of_control_card_le_eight
        control hcard with
      ⟨z, hzBoundary, hvanish, hzNonzero⟩
    exact hzNonzero (hcontrol hzBoundary hvanish)

theorem twoBandAnnulus_boundaryZero_classifierControl_emittedFinset_card_ge_nine
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 9 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcontrol :
      ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0) :
    9 ≤ classifier.emittedFinset.card :=
  twoBandAnnulus_boundaryZero_exactMinimumControlCard.2
    classifier.emittedFinset hcontrol

theorem twoBandAnnulus_boundaryZero_classifierControl_emittedInterior_card_ge_nine
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 9 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcontrol :
      ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0) :
    9 ≤ (classifier.emittedFinset.filter fun e =>
      e ∈ interiorEdgeSupport
        twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces).card := by
  refine twoBandAnnulus_boundaryZero_exactMinimumControlCard.2
    (classifier.emittedFinset.filter fun e =>
      e ∈ interiorEdgeSupport
        twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces) ?_
  intro z hzBoundary hvanishInterior
  exact hcontrol hzBoundary (by
    intro e heEmitted
    by_cases heInterior :
        e ∈ interiorEdgeSupport
          twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces
    · exact hvanishInterior e (Finset.mem_filter.2 ⟨heEmitted, heInterior⟩)
    · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary e
        (twoBandAnnulus_mem_selectedBoundarySupport_of_not_mem_interiorEdgeSupport
          heInterior))

theorem twoBandAnnulus_boundaryZero_not_classifierControl_of_emittedFinset_card_le_eight
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 9 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard : classifier.emittedFinset.card ≤ 8) :
    ¬ ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
      z = 0 := by
  intro hcontrol
  have hge :=
    twoBandAnnulus_boundaryZero_classifierControl_emittedFinset_card_ge_nine
      classifier hcontrol
  omega

theorem twoBandAnnulus_middleOuterRadialKirchhoffControl_not_boundaryZeroControl :
    ¬ ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
      (∀ e ∈ twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges, z e = 0) →
      z = 0 := by
  intro hcontrol
  have hge :=
    twoBandAnnulus_boundaryZero_exactMinimumControlCard.2
      twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges hcontrol
  have hcard : twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges.card = 6 := by
    decide
  omega

theorem twoBandAnnulus_boundaryZeroKirchhoff_exactMinimumControlCard :
    (∃ control : Finset twoBandAnnulusGraph.edgeSet,
      control.card = 6 ∧
        ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
          z ∈ theorem49BoundaryZeroKirchhoffSubspace
              twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
          (∀ e ∈ control, z e = 0) →
          z = 0) ∧
    (∀ control : Finset twoBandAnnulusGraph.edgeSet,
      (∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
        (∀ e ∈ control, z e = 0) →
        z = 0) →
      6 ≤ control.card) := by
  constructor
  · refine ⟨twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges, ?_, ?_⟩
    · decide
    · intro z hz hcontrol
      exact twoBandAnnulus_boundaryZeroKirchhoff_no_evader_of_middleOuterRadialControl
        z hz hcontrol
  · intro control hcontrol
    by_contra hnotLower
    have hcard : control.card ≤ 5 := by omega
    rcases twoBandAnnulus_boundaryZeroKirchhoff_has_evader_of_control_card_le_five
        control hcard with
      ⟨z, hz, hvanish, hzNonzero⟩
    exact hzNonzero (hcontrol hz hvanish)

theorem twoBandAnnulus_boundaryZeroKirchhoff_classifierControl_emittedFinset_card_ge_six
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 9 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcontrol :
      ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0) :
    6 ≤ classifier.emittedFinset.card :=
  twoBandAnnulus_boundaryZeroKirchhoff_exactMinimumControlCard.2
    classifier.emittedFinset hcontrol

theorem twoBandAnnulus_boundaryZeroKirchhoff_classifierControl_emittedInterior_card_ge_six
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 9 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcontrol :
      ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0) :
    6 ≤ (classifier.emittedFinset.filter fun e =>
      e ∈ interiorEdgeSupport
        twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces).card := by
  refine twoBandAnnulus_boundaryZeroKirchhoff_exactMinimumControlCard.2
    (classifier.emittedFinset.filter fun e =>
      e ∈ interiorEdgeSupport
        twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces) ?_
  intro z hz hvanishInterior
  have hzBoundary : z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding :=
    theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
      twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices hz
  exact hcontrol hz (by
    intro e heEmitted
    by_cases heInterior :
        e ∈ interiorEdgeSupport
          twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces
    · exact hvanishInterior e (Finset.mem_filter.2 ⟨heEmitted, heInterior⟩)
    · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary e
        (twoBandAnnulus_mem_selectedBoundarySupport_of_not_mem_interiorEdgeSupport
          heInterior))

theorem twoBandAnnulus_boundaryZeroKirchhoff_not_classifierControl_of_emittedFinset_card_le_five
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 9 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard : classifier.emittedFinset.card ≤ 5) :
    ¬ ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
      z = 0 := by
  intro hcontrol
  have hge :=
    twoBandAnnulus_boundaryZeroKirchhoff_classifierControl_emittedFinset_card_ge_six
      classifier hcontrol
  omega

/-! ## Generated one-band annulus counterexample shell -/

def oneBandAnnulus3Graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(3, 4), s(0, 3), s(1, 2), s(4, 5), s(1, 4),
        s(2, 0), s(5, 3), s(2, 5)} : Set (Sym2 (Fin 6)))

def obaO01 : oneBandAnnulus3Graph.edgeSet := ⟨s(0, 1), by
  simp [oneBandAnnulus3Graph]⟩

def obaI01 : oneBandAnnulus3Graph.edgeSet := ⟨s(3, 4), by
  simp [oneBandAnnulus3Graph]⟩

def obaR0 : oneBandAnnulus3Graph.edgeSet := ⟨s(0, 3), by
  simp [oneBandAnnulus3Graph]⟩

def obaO12 : oneBandAnnulus3Graph.edgeSet := ⟨s(1, 2), by
  simp [oneBandAnnulus3Graph]⟩

def obaI12 : oneBandAnnulus3Graph.edgeSet := ⟨s(4, 5), by
  simp [oneBandAnnulus3Graph]⟩

def obaR1 : oneBandAnnulus3Graph.edgeSet := ⟨s(1, 4), by
  simp [oneBandAnnulus3Graph]⟩

def obaO20 : oneBandAnnulus3Graph.edgeSet := ⟨s(2, 0), by
  simp [oneBandAnnulus3Graph]⟩

def obaI20 : oneBandAnnulus3Graph.edgeSet := ⟨s(5, 3), by
  simp [oneBandAnnulus3Graph]⟩

def obaR2 : oneBandAnnulus3Graph.edgeSet := ⟨s(2, 5), by
  simp [oneBandAnnulus3Graph]⟩

theorem oneBandAnnulus3_edge_eq
    (e : oneBandAnnulus3Graph.edgeSet) :
    e = obaO01 ∨ e = obaI01 ∨ e = obaR0 ∨ e = obaO12 ∨ e = obaI12 ∨
      e = obaR1 ∨ e = obaO20 ∨ e = obaI20 ∨ e = obaR2 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(3, 4) ∨ e.1 = s(0, 3) ∨
          e.1 = s(1, 2) ∨ e.1 = s(4, 5) ∨ e.1 = s(1, 4) ∨
          e.1 = s(2, 0) ∨ e.1 = s(5, 3) ∨ e.1 = s(2, 5)) ∧
        ¬ e.1.IsDiag := by
    simpa [oneBandAnnulus3Graph] using e.2
  rcases h.1 with hO01 | hI01 | hR0 | hO12 | hI12 | hR1 | hO20 | hI20 | hR2
  · exact Or.inl (Subtype.ext hO01)
  · exact Or.inr <| Or.inl (Subtype.ext hI01)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext hR0)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hO12)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI12)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hR1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hO20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext hI20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr (Subtype.ext hR2)

noncomputable instance oneBandAnnulus3Graph_edgeSet_fintype :
    Fintype oneBandAnnulus3Graph.edgeSet :=
  ⟨{obaO01, obaI01, obaR0, obaO12, obaI12, obaR1, obaO20, obaI20, obaR2}, by
    intro e
    rcases oneBandAnnulus3_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp⟩

abbrev OneBandAnnulus3Face := Fin 3

def oneBandAnnulus3Faces : Finset OneBandAnnulus3Face := Finset.univ

def oneBandAnnulus3FaceBoundary :
    OneBandAnnulus3Face → Finset oneBandAnnulus3Graph.edgeSet
  | ⟨0, _⟩ => {obaO01, obaR1, obaI01, obaR0}
  | ⟨1, _⟩ => {obaO12, obaR2, obaI12, obaR1}
  | ⟨2, _⟩ => {obaO20, obaR0, obaI20, obaR2}

theorem totalIncidenceCount_obaO01 :
    totalIncidenceCount oneBandAnnulus3FaceBoundary
      oneBandAnnulus3Faces obaO01 = 1 := by
  decide

theorem totalIncidenceCount_obaI01 :
    totalIncidenceCount oneBandAnnulus3FaceBoundary
      oneBandAnnulus3Faces obaI01 = 1 := by
  decide

theorem totalIncidenceCount_obaR0 :
    totalIncidenceCount oneBandAnnulus3FaceBoundary
      oneBandAnnulus3Faces obaR0 = 2 := by
  decide

theorem totalIncidenceCount_obaO12 :
    totalIncidenceCount oneBandAnnulus3FaceBoundary
      oneBandAnnulus3Faces obaO12 = 1 := by
  decide

theorem totalIncidenceCount_obaI12 :
    totalIncidenceCount oneBandAnnulus3FaceBoundary
      oneBandAnnulus3Faces obaI12 = 1 := by
  decide

theorem totalIncidenceCount_obaR1 :
    totalIncidenceCount oneBandAnnulus3FaceBoundary
      oneBandAnnulus3Faces obaR1 = 2 := by
  decide

theorem totalIncidenceCount_obaO20 :
    totalIncidenceCount oneBandAnnulus3FaceBoundary
      oneBandAnnulus3Faces obaO20 = 1 := by
  decide

theorem totalIncidenceCount_obaI20 :
    totalIncidenceCount oneBandAnnulus3FaceBoundary
      oneBandAnnulus3Faces obaI20 = 1 := by
  decide

theorem totalIncidenceCount_obaR2 :
    totalIncidenceCount oneBandAnnulus3FaceBoundary
      oneBandAnnulus3Faces obaR2 = 2 := by
  decide

def oneBandAnnulus3Embedding :
    PlaneEmbeddingWithBoundary oneBandAnnulus3Graph where
  Face := OneBandAnnulus3Face
  faceDecidableEq := inferInstance
  faces := oneBandAnnulus3Faces
  faceBoundary := oneBandAnnulus3FaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases oneBandAnnulus3_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases oneBandAnnulus3_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

theorem obaO01_mem_selectedBoundarySupport :
    obaO01 ∈ selectedBoundarySupport
      oneBandAnnulus3Embedding.faceBoundary
      oneBandAnnulus3Embedding.faces
      oneBandAnnulus3Embedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_obaO01⟩

theorem obaI01_mem_selectedBoundarySupport :
    obaI01 ∈ selectedBoundarySupport
      oneBandAnnulus3Embedding.faceBoundary
      oneBandAnnulus3Embedding.faces
      oneBandAnnulus3Embedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_obaI01⟩

theorem obaO12_mem_selectedBoundarySupport :
    obaO12 ∈ selectedBoundarySupport
      oneBandAnnulus3Embedding.faceBoundary
      oneBandAnnulus3Embedding.faces
      oneBandAnnulus3Embedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_obaO12⟩

theorem obaI12_mem_selectedBoundarySupport :
    obaI12 ∈ selectedBoundarySupport
      oneBandAnnulus3Embedding.faceBoundary
      oneBandAnnulus3Embedding.faces
      oneBandAnnulus3Embedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_obaI12⟩

theorem obaO20_mem_selectedBoundarySupport :
    obaO20 ∈ selectedBoundarySupport
      oneBandAnnulus3Embedding.faceBoundary
      oneBandAnnulus3Embedding.faces
      oneBandAnnulus3Embedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_obaO20⟩

theorem obaI20_mem_selectedBoundarySupport :
    obaI20 ∈ selectedBoundarySupport
      oneBandAnnulus3Embedding.faceBoundary
      oneBandAnnulus3Embedding.faces
      oneBandAnnulus3Embedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_obaI20⟩

theorem obaR0_not_mem_selectedBoundarySupport :
    obaR0 ∉ selectedBoundarySupport
      oneBandAnnulus3Embedding.faceBoundary
      oneBandAnnulus3Embedding.faces
      oneBandAnnulus3Embedding.faces := by
  decide

theorem obaR1_not_mem_selectedBoundarySupport :
    obaR1 ∉ selectedBoundarySupport
      oneBandAnnulus3Embedding.faceBoundary
      oneBandAnnulus3Embedding.faces
      oneBandAnnulus3Embedding.faces := by
  decide

theorem obaR2_not_mem_selectedBoundarySupport :
    obaR2 ∉ selectedBoundarySupport
      oneBandAnnulus3Embedding.faceBoundary
      oneBandAnnulus3Embedding.faces
      oneBandAnnulus3Embedding.faces := by
  decide

theorem obaR0_mem_interiorEdgeSupport :
    obaR0 ∈ interiorEdgeSupport
      oneBandAnnulus3Embedding.faceBoundary
      oneBandAnnulus3Embedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_obaR0⟩

theorem obaR1_mem_interiorEdgeSupport :
    obaR1 ∈ interiorEdgeSupport
      oneBandAnnulus3Embedding.faceBoundary
      oneBandAnnulus3Embedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_obaR1⟩

theorem obaR2_mem_interiorEdgeSupport :
    obaR2 ∈ interiorEdgeSupport
      oneBandAnnulus3Embedding.faceBoundary
      oneBandAnnulus3Embedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_obaR2⟩

theorem oneBandAnnulus3_interiorEdgeSupport_eq :
    interiorEdgeSupport
        oneBandAnnulus3Embedding.faceBoundary
        oneBandAnnulus3Embedding.faces =
      ({obaR0, obaR1, obaR2} : Finset oneBandAnnulus3Graph.edgeSet) := by
  ext e
  rcases oneBandAnnulus3_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

def obaFace0 : AmbientFace oneBandAnnulus3Embedding.faces :=
  ⟨(0 : OneBandAnnulus3Face), by decide⟩

def obaFace1 : AmbientFace oneBandAnnulus3Embedding.faces :=
  ⟨(1 : OneBandAnnulus3Face), by decide⟩

def obaFace2 : AmbientFace oneBandAnnulus3Embedding.faces :=
  ⟨(2 : OneBandAnnulus3Face), by decide⟩

theorem oneBandAnnulus3_face_cases
    (f : AmbientFace oneBandAnnulus3Embedding.faces) :
    f = obaFace0 ∨ f = obaFace1 ∨ f = obaFace2 := by
  rcases f with ⟨⟨n, hn⟩, hf⟩
  interval_cases n <;> simp [obaFace0, obaFace1, obaFace2]

theorem obaR0_mem_oneBandAnnulus3_faceBoundary_iff
    (f : AmbientFace oneBandAnnulus3Embedding.faces) :
    obaR0 ∈ oneBandAnnulus3Embedding.faceBoundary f.1 ↔
      f = obaFace0 ∨ f = obaFace2 := by
  rcases oneBandAnnulus3_face_cases f with rfl | rfl | rfl <;>
    decide

theorem obaR1_mem_oneBandAnnulus3_faceBoundary_iff
    (f : AmbientFace oneBandAnnulus3Embedding.faces) :
    obaR1 ∈ oneBandAnnulus3Embedding.faceBoundary f.1 ↔
      f = obaFace0 ∨ f = obaFace1 := by
  rcases oneBandAnnulus3_face_cases f with rfl | rfl | rfl <;>
    decide

theorem obaR2_mem_oneBandAnnulus3_faceBoundary_iff
    (f : AmbientFace oneBandAnnulus3Embedding.faces) :
    obaR2 ∈ oneBandAnnulus3Embedding.faceBoundary f.1 ↔
      f = obaFace1 ∨ f = obaFace2 := by
  rcases oneBandAnnulus3_face_cases f with rfl | rfl | rfl <;>
    decide

theorem oneBandAnnulus3_height_lt_of_nonboundary_rest
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData oneBandAnnulus3Embedding)
    {f g : AmbientFace oneBandAnnulus3Embedding.faces}
    {e : oneBandAnnulus3Graph.edgeSet}
    (hf : f ∈ data.peelFaces)
    (he :
      e ∈ (oneBandAnnulus3Embedding.faceBoundary f.1).erase
        (data.witnessEdge f))
    (heBoundary :
      e ∉ selectedBoundarySupport
        oneBandAnnulus3Embedding.faceBoundary
        oneBandAnnulus3Embedding.faces
        oneBandAnnulus3Embedding.faces)
    (hunique :
      ∀ g' ∈ data.peelFaces, data.witnessEdge g' = e → g' = g) :
    data.height f < data.height g := by
  rcases data.hrest f hf e he with hboundary | ⟨g', hg', hgw, hlt⟩
  · exact False.elim (heBoundary hboundary)
  · have hg : g' = g := hunique g' hg' hgw
    simpa [hg] using hlt

theorem not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_oneBandAnnulus3 :
    ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          oneBandAnnulus3Embedding) := by
  rintro ⟨data⟩
  rcases Finset.mem_image.1 (data.hcover obaR0_mem_interiorEdgeSupport) with
    ⟨fR0, hfR0Peel, hfR0Witness⟩
  rcases Finset.mem_image.1 (data.hcover obaR1_mem_interiorEdgeSupport) with
    ⟨fR1, hfR1Peel, hfR1Witness⟩
  rcases Finset.mem_image.1 (data.hcover obaR2_mem_interiorEdgeSupport) with
    ⟨fR2, hfR2Peel, hfR2Witness⟩
  have hfR0WitnessMem :
      data.witnessEdge fR0 ∈ oneBandAnnulus3Embedding.faceBoundary fR0.1 :=
    data.hwitness fR0 hfR0Peel
  have hfR1WitnessMem :
      data.witnessEdge fR1 ∈ oneBandAnnulus3Embedding.faceBoundary fR1.1 :=
    data.hwitness fR1 hfR1Peel
  have hfR2WitnessMem :
      data.witnessEdge fR2 ∈ oneBandAnnulus3Embedding.faceBoundary fR2.1 :=
    data.hwitness fR2 hfR2Peel
  have hR0Mem :
      obaR0 ∈ oneBandAnnulus3Embedding.faceBoundary fR0.1 := by
    simpa [hfR0Witness] using hfR0WitnessMem
  have hR1Mem :
      obaR1 ∈ oneBandAnnulus3Embedding.faceBoundary fR1.1 := by
    simpa [hfR1Witness] using hfR1WitnessMem
  have hR2Mem :
      obaR2 ∈ oneBandAnnulus3Embedding.faceBoundary fR2.1 := by
    simpa [hfR2Witness] using hfR2WitnessMem
  have hfR0_cases : fR0 = obaFace0 ∨ fR0 = obaFace2 :=
    (obaR0_mem_oneBandAnnulus3_faceBoundary_iff fR0).1 hR0Mem
  have hfR1_cases : fR1 = obaFace0 ∨ fR1 = obaFace1 :=
    (obaR1_mem_oneBandAnnulus3_faceBoundary_iff fR1).1 hR1Mem
  have hfR2_cases : fR2 = obaFace1 ∨ fR2 = obaFace2 :=
    (obaR2_mem_oneBandAnnulus3_faceBoundary_iff fR2).1 hR2Mem
  rcases hfR0_cases with hfR0_eq0 | hfR0_eq2
  · have hface0Peel : obaFace0 ∈ data.peelFaces := by
      simpa [hfR0_eq0] using hfR0Peel
    have hface0Witness : data.witnessEdge obaFace0 = obaR0 := by
      simpa [hfR0_eq0] using hfR0Witness
    have hfR1_eq1 : fR1 = obaFace1 := by
      rcases hfR1_cases with hfR1_eq0 | hfR1_eq1
      · subst fR1
        have hbad : obaR0 = obaR1 := hface0Witness.symm.trans hfR1Witness
        exact False.elim ((by decide : obaR0 ≠ obaR1) hbad)
      · exact hfR1_eq1
    have hface1Peel : obaFace1 ∈ data.peelFaces := by
      simpa [hfR1_eq1] using hfR1Peel
    have hface1Witness : data.witnessEdge obaFace1 = obaR1 := by
      simpa [hfR1_eq1] using hfR1Witness
    have hfR2_eq2 : fR2 = obaFace2 := by
      rcases hfR2_cases with hfR2_eq1 | hfR2_eq2
      · subst fR2
        have hbad : obaR1 = obaR2 := hface1Witness.symm.trans hfR2Witness
        exact False.elim ((by decide : obaR1 ≠ obaR2) hbad)
      · exact hfR2_eq2
    have hface2Peel : obaFace2 ∈ data.peelFaces := by
      simpa [hfR2_eq2] using hfR2Peel
    have hface2Witness : data.witnessEdge obaFace2 = obaR2 := by
      simpa [hfR2_eq2] using hfR2Witness
    have hlt01 : data.height obaFace0 < data.height obaFace1 := by
      refine oneBandAnnulus3_height_lt_of_nonboundary_rest data
        hface0Peel ?_ obaR1_not_mem_selectedBoundarySupport ?_
      · rw [hface0Witness]
        exact Finset.mem_erase.2 ⟨(by decide : obaR1 ≠ obaR0), by decide⟩
      · intro g hg hgw
        have hgwMem :
            obaR1 ∈ oneBandAnnulus3Embedding.faceBoundary g.1 := by
          simpa [hgw] using data.hwitness g hg
        rcases oneBandAnnulus3_face_cases g with rfl | rfl | rfl
        · have hbad : obaR0 = obaR1 := hface0Witness.symm.trans hgw
          exact False.elim ((by decide : obaR0 ≠ obaR1) hbad)
        · rfl
        · have : ¬ obaR1 ∈ oneBandAnnulus3Embedding.faceBoundary obaFace2.1 := by
            decide
          exact False.elim (this hgwMem)
    have hlt12 : data.height obaFace1 < data.height obaFace2 := by
      refine oneBandAnnulus3_height_lt_of_nonboundary_rest data
        hface1Peel ?_ obaR2_not_mem_selectedBoundarySupport ?_
      · rw [hface1Witness]
        exact Finset.mem_erase.2 ⟨(by decide : obaR2 ≠ obaR1), by decide⟩
      · intro g hg hgw
        have hgwMem :
            obaR2 ∈ oneBandAnnulus3Embedding.faceBoundary g.1 := by
          simpa [hgw] using data.hwitness g hg
        rcases oneBandAnnulus3_face_cases g with rfl | rfl | rfl
        · have : ¬ obaR2 ∈ oneBandAnnulus3Embedding.faceBoundary obaFace0.1 := by
            decide
          exact False.elim (this hgwMem)
        · have hbad : obaR1 = obaR2 := hface1Witness.symm.trans hgw
          exact False.elim ((by decide : obaR1 ≠ obaR2) hbad)
        · rfl
    have hlt20 : data.height obaFace2 < data.height obaFace0 := by
      refine oneBandAnnulus3_height_lt_of_nonboundary_rest data
        hface2Peel ?_ obaR0_not_mem_selectedBoundarySupport ?_
      · rw [hface2Witness]
        exact Finset.mem_erase.2 ⟨(by decide : obaR0 ≠ obaR2), by decide⟩
      · intro g hg hgw
        have hgwMem :
            obaR0 ∈ oneBandAnnulus3Embedding.faceBoundary g.1 := by
          simpa [hgw] using data.hwitness g hg
        rcases oneBandAnnulus3_face_cases g with rfl | rfl | rfl
        · rfl
        · have : ¬ obaR0 ∈ oneBandAnnulus3Embedding.faceBoundary obaFace1.1 := by
            decide
          exact False.elim (this hgwMem)
        · have hbad : obaR2 = obaR0 := hface2Witness.symm.trans hgw
          exact False.elim ((by decide : obaR2 ≠ obaR0) hbad)
    exact (Nat.lt_irrefl _ (lt_trans hlt01 (lt_trans hlt12 hlt20))).elim
  · have hface2Peel : obaFace2 ∈ data.peelFaces := by
      simpa [hfR0_eq2] using hfR0Peel
    have hface2Witness : data.witnessEdge obaFace2 = obaR0 := by
      simpa [hfR0_eq2] using hfR0Witness
    have hfR2_eq1 : fR2 = obaFace1 := by
      rcases hfR2_cases with hfR2_eq1 | hfR2_eq2
      · exact hfR2_eq1
      · subst fR2
        have hbad : obaR0 = obaR2 := hface2Witness.symm.trans hfR2Witness
        exact False.elim ((by decide : obaR0 ≠ obaR2) hbad)
    have hface1Peel : obaFace1 ∈ data.peelFaces := by
      simpa [hfR2_eq1] using hfR2Peel
    have hface1Witness : data.witnessEdge obaFace1 = obaR2 := by
      simpa [hfR2_eq1] using hfR2Witness
    have hfR1_eq0 : fR1 = obaFace0 := by
      rcases hfR1_cases with hfR1_eq0 | hfR1_eq1
      · exact hfR1_eq0
      · subst fR1
        have hbad : obaR2 = obaR1 := hface1Witness.symm.trans hfR1Witness
        exact False.elim ((by decide : obaR2 ≠ obaR1) hbad)
    have hface0Peel : obaFace0 ∈ data.peelFaces := by
      simpa [hfR1_eq0] using hfR1Peel
    have hface0Witness : data.witnessEdge obaFace0 = obaR1 := by
      simpa [hfR1_eq0] using hfR1Witness
    have hlt02 : data.height obaFace0 < data.height obaFace2 := by
      refine oneBandAnnulus3_height_lt_of_nonboundary_rest data
        hface0Peel ?_ obaR0_not_mem_selectedBoundarySupport ?_
      · rw [hface0Witness]
        exact Finset.mem_erase.2 ⟨(by decide : obaR0 ≠ obaR1), by decide⟩
      · intro g hg hgw
        have hgwMem :
            obaR0 ∈ oneBandAnnulus3Embedding.faceBoundary g.1 := by
          simpa [hgw] using data.hwitness g hg
        rcases oneBandAnnulus3_face_cases g with rfl | rfl | rfl
        · have hbad : obaR1 = obaR0 := hface0Witness.symm.trans hgw
          exact False.elim ((by decide : obaR1 ≠ obaR0) hbad)
        · have : ¬ obaR0 ∈ oneBandAnnulus3Embedding.faceBoundary obaFace1.1 := by
            decide
          exact False.elim (this hgwMem)
        · rfl
    have hlt21 : data.height obaFace2 < data.height obaFace1 := by
      refine oneBandAnnulus3_height_lt_of_nonboundary_rest data
        hface2Peel ?_ obaR2_not_mem_selectedBoundarySupport ?_
      · rw [hface2Witness]
        exact Finset.mem_erase.2 ⟨(by decide : obaR2 ≠ obaR0), by decide⟩
      · intro g hg hgw
        have hgwMem :
            obaR2 ∈ oneBandAnnulus3Embedding.faceBoundary g.1 := by
          simpa [hgw] using data.hwitness g hg
        rcases oneBandAnnulus3_face_cases g with rfl | rfl | rfl
        · have : ¬ obaR2 ∈ oneBandAnnulus3Embedding.faceBoundary obaFace0.1 := by
            decide
          exact False.elim (this hgwMem)
        · rfl
        · have hbad : obaR0 = obaR2 := hface2Witness.symm.trans hgw
          exact False.elim ((by decide : obaR0 ≠ obaR2) hbad)
    have hlt10 : data.height obaFace1 < data.height obaFace0 := by
      refine oneBandAnnulus3_height_lt_of_nonboundary_rest data
        hface1Peel ?_ obaR1_not_mem_selectedBoundarySupport ?_
      · rw [hface1Witness]
        exact Finset.mem_erase.2 ⟨(by decide : obaR1 ≠ obaR2), by decide⟩
      · intro g hg hgw
        have hgwMem :
            obaR1 ∈ oneBandAnnulus3Embedding.faceBoundary g.1 := by
          simpa [hgw] using data.hwitness g hg
        rcases oneBandAnnulus3_face_cases g with rfl | rfl | rfl
        · rfl
        · have hbad : obaR2 = obaR1 := hface1Witness.symm.trans hgw
          exact False.elim ((by decide : obaR2 ≠ obaR1) hbad)
        · have : ¬ obaR1 ∈ oneBandAnnulus3Embedding.faceBoundary obaFace2.1 := by
            decide
          exact False.elim (this hgwMem)
    exact (Nat.lt_irrefl _ (lt_trans hlt02 (lt_trans hlt21 hlt10))).elim

theorem oneBandAnnulus3_radialEdges_no_boundaryFree_incident_face :
    ∀ e ∈ ({obaR0, obaR1, obaR2} : Finset oneBandAnnulus3Graph.edgeSet),
      ∀ f ∈ oneBandAnnulus3Embedding.faces,
        e ∈ oneBandAnnulus3Embedding.faceBoundary f →
          ∃ b ∈ selectedBoundarySupport
              oneBandAnnulus3Embedding.faceBoundary
              oneBandAnnulus3Embedding.faces
              oneBandAnnulus3Embedding.faces,
            b ∈ oneBandAnnulus3Embedding.faceBoundary f := by
  decide

theorem oneBandAnnulus3_radialEdges_touch_selectedBoundaryEndpoint :
    ∃ e ∈ ({obaR0, obaR1, obaR2} : Finset oneBandAnnulus3Graph.edgeSet),
      ∃ b ∈ selectedBoundarySupport
          oneBandAnnulus3Embedding.faceBoundary
          oneBandAnnulus3Embedding.faces
          oneBandAnnulus3Embedding.faces,
        ∃ v : Fin 6, v ∈ (e : Sym2 (Fin 6)) ∧ v ∈ (b : Sym2 (Fin 6)) := by
  exact ⟨obaR0, by simp, obaO01, obaO01_mem_selectedBoundarySupport,
    0, by decide, by decide⟩

theorem oneBandAnnulus3_purifiedCarrier_empty :
    ∀ v : Fin 6,
      (∃ e ∈ ({obaR0, obaR1, obaR2} : Finset oneBandAnnulus3Graph.edgeSet),
        v ∈ (e : Sym2 (Fin 6))) →
        ∃ b ∈ selectedBoundarySupport
            oneBandAnnulus3Embedding.faceBoundary
            oneBandAnnulus3Embedding.faces
            oneBandAnnulus3Embedding.faces,
          v ∈ (b : Sym2 (Fin 6)) := by
  decide

theorem oneBandAnnulus3_boundaryZero_no_evader_of_vanishes_on_radialEdges
    (z : oneBandAnnulus3Graph.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule oneBandAnnulus3Embedding)
    (hcontrol :
      ∀ e ∈ ({obaR0, obaR1, obaR2} : Finset oneBandAnnulus3Graph.edgeSet), z e = 0) :
    z = 0 := by
  refine eq_zero_of_mem_planarBoundaryZeroSubmodule_of_control_or_boundary
    z hzBoundary ({obaR0, obaR1, obaR2} : Finset oneBandAnnulus3Graph.edgeSet)
    hcontrol ?_
  intro e
  rcases oneBandAnnulus3_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr obaO01_mem_selectedBoundarySupport
  · exact Or.inr obaI01_mem_selectedBoundarySupport
  · exact Or.inl (by simp)
  · exact Or.inr obaO12_mem_selectedBoundarySupport
  · exact Or.inr obaI12_mem_selectedBoundarySupport
  · exact Or.inl (by simp)
  · exact Or.inr obaO20_mem_selectedBoundarySupport
  · exact Or.inr obaI20_mem_selectedBoundarySupport
  · exact Or.inl (by simp)

def oneBandAnnulus3RadialControlEdges : Finset oneBandAnnulus3Graph.edgeSet :=
  {obaR0, obaR1, obaR2}

def oneBandAnnulus3EmptyKirchhoffVertices : Finset (Fin 6) :=
  ∅

theorem oneBandAnnulus3_selectedBoundarySupport_eq :
    selectedBoundarySupport
        oneBandAnnulus3Embedding.faceBoundary
        oneBandAnnulus3Embedding.faces
        oneBandAnnulus3Embedding.faces =
      ({obaO01, obaI01, obaO12, obaI12, obaO20, obaI20} :
        Finset oneBandAnnulus3Graph.edgeSet) := by
  ext e
  rcases oneBandAnnulus3_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem oneBandAnnulus3BoundaryZeroEmptyKirchhoffScalarConstraintSpace_finrank_lt_of_control_card_le_two
    (control : Finset oneBandAnnulus3Graph.edgeSet) (hcard : control.card ≤ 2) :
    Module.finrank F2
      (theorem49BoundaryZeroKirchhoffScalarConstraintSpace
        oneBandAnnulus3Embedding oneBandAnnulus3EmptyKirchhoffVertices control) <
      Fintype.card oneBandAnnulus3Graph.edgeSet := by
  refine theorem49BoundaryZeroKirchhoffScalarConstraintSpace_finrank_lt_of_card_sum_lt
    oneBandAnnulus3Embedding oneBandAnnulus3EmptyKirchhoffVertices control ?_
  have hboundary :
      Fintype.card {e : oneBandAnnulus3Graph.edgeSet //
        e ∈ selectedBoundarySupport
          oneBandAnnulus3Embedding.faceBoundary
          oneBandAnnulus3Embedding.faces
          oneBandAnnulus3Embedding.faces} = 6 := by
    rw [oneBandAnnulus3_selectedBoundarySupport_eq]
    decide
  have hvertices :
      Fintype.card {v : Fin 6 // v ∈ oneBandAnnulus3EmptyKirchhoffVertices} = 0 := by
    decide
  have hedge : Fintype.card oneBandAnnulus3Graph.edgeSet = 9 := by
    decide
  rw [hboundary, hvertices, hedge]
  omega

theorem oneBandAnnulus3_boundaryZeroEmptyKirchhoff_has_evader_of_control_card_le_two
    (control : Finset oneBandAnnulus3Graph.edgeSet) (hcard : control.card ≤ 2) :
    ∃ z : oneBandAnnulus3Graph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          oneBandAnnulus3Embedding oneBandAnnulus3EmptyKirchhoffVertices ∧
      (∀ e ∈ control, z e = 0) ∧ z ≠ 0 := by
  refine exists_redScalarColorChain_mem_theorem49BoundaryZeroKirchhoffSubspace_of_card_sum_lt
    oneBandAnnulus3Embedding oneBandAnnulus3EmptyKirchhoffVertices control ?_
  have hboundary :
      Fintype.card {e : oneBandAnnulus3Graph.edgeSet //
        e ∈ selectedBoundarySupport
          oneBandAnnulus3Embedding.faceBoundary
          oneBandAnnulus3Embedding.faces
          oneBandAnnulus3Embedding.faces} = 6 := by
    rw [oneBandAnnulus3_selectedBoundarySupport_eq]
    decide
  have hvertices :
      Fintype.card {v : Fin 6 // v ∈ oneBandAnnulus3EmptyKirchhoffVertices} = 0 := by
    decide
  have hedge : Fintype.card oneBandAnnulus3Graph.edgeSet = 9 := by
    decide
  rw [hboundary, hvertices, hedge]
  omega

theorem oneBandAnnulus3_boundaryZeroEmptyKirchhoff_no_evader_of_radialControl
    (z : oneBandAnnulus3Graph.edgeSet → Color)
    (hz :
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
        oneBandAnnulus3Embedding oneBandAnnulus3EmptyKirchhoffVertices)
    (hcontrol : ∀ e ∈ oneBandAnnulus3RadialControlEdges, z e = 0) :
    z = 0 := by
  exact oneBandAnnulus3_boundaryZero_no_evader_of_vanishes_on_radialEdges z
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
      oneBandAnnulus3Embedding oneBandAnnulus3EmptyKirchhoffVertices hz)
    (by simpa [oneBandAnnulus3RadialControlEdges] using hcontrol)

theorem oneBandAnnulus3_boundaryZeroEmptyKirchhoff_minimalControl_profile :
    (∀ ⦃z : oneBandAnnulus3Graph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          oneBandAnnulus3Embedding oneBandAnnulus3EmptyKirchhoffVertices →
      (∀ e ∈ oneBandAnnulus3RadialControlEdges, z e = 0) →
      z = 0) ∧
    (∀ control : Finset oneBandAnnulus3Graph.edgeSet,
      control.card ≤ 2 →
        ∃ z : oneBandAnnulus3Graph.edgeSet → Color,
          z ∈ theorem49BoundaryZeroKirchhoffSubspace
              oneBandAnnulus3Embedding oneBandAnnulus3EmptyKirchhoffVertices ∧
          (∀ e ∈ control, z e = 0) ∧ z ≠ 0) := by
  constructor
  · intro z hz hcontrol
    exact oneBandAnnulus3_boundaryZeroEmptyKirchhoff_no_evader_of_radialControl
      z hz hcontrol
  · exact oneBandAnnulus3_boundaryZeroEmptyKirchhoff_has_evader_of_control_card_le_two

/-! ## Boundary-zero forced-edge verdicts -/

/-- In the shared-interior-pair shell, the two interior edges plus the selected boundary support
cover every edge. Hence any selected-boundary-zero chain vanishing on both interior edges is
zero. -/
theorem sharedInteriorPair_boundaryZero_no_evader_of_vanishes_on_interiorEdges
    (z : sharedInteriorPairGraph.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding)
    (hsip01 : z sip01 = 0) (hsip12 : z sip12 = 0) :
    z = 0 := by
  refine eq_zero_of_mem_planarBoundaryZeroSubmodule_of_control_or_boundary
    z hzBoundary ({sip01, sip12} : Finset sharedInteriorPairGraph.edgeSet) ?_ ?_
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hsip01
    · have he12 : e = sip12 := by simpa using he
      subst e
      exact hsip12
  · intro e
    rcases sharedInteriorPair_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inr sip23_mem_selectedBoundarySupport
    · exact Or.inr sip30_mem_selectedBoundarySupport
    · exact Or.inr sip24_mem_selectedBoundarySupport
    · exact Or.inr sip40_mem_selectedBoundarySupport
    · exact Or.inr sip56_mem_selectedBoundarySupport
    · exact Or.inr sip67_mem_selectedBoundarySupport
    · exact Or.inr sip75_mem_selectedBoundarySupport

theorem sharedInteriorPair_boundaryZero_no_evader_of_controlEdges :
    ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
      (∀ e ∈ ({sip01, sip12} : Finset sharedInteriorPairGraph.edgeSet), z e = 0) →
        z = 0 := by
  intro z hzBoundary hcontrol
  exact sharedInteriorPair_boundaryZero_no_evader_of_vanishes_on_interiorEdges z hzBoundary
    (hcontrol sip01 (by simp))
    (hcontrol sip12 (by simp))

/-! ## Boundary-zero forced-edge verdicts retained for shell comparisons -/

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

/-! ## Control-edge forms for the CAP5 detector interface -/

theorem sharedInteriorPair_boundaryZero_controlEdges_interiorEdges :
    ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
      (∀ e ∈ ({sip01, sip12} : Finset sharedInteriorPairGraph.edgeSet), z e = 0) →
        z = 0 :=
  sharedInteriorPair_boundaryZero_no_evader_of_controlEdges

theorem wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges :
    ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
      (∀ e ∈ ({wit01, wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet), z e = 0) →
        z = 0 := by
  intro z hzBoundary hcontrol
  exact wheelWithInnerTriangle_boundaryZero_no_evader_of_vanishes_on_interiorEdges
    z hzBoundary
    (hcontrol wit01 (by simp))
    (hcontrol wit02 (by simp))
    (hcontrol wit03 (by simp))

theorem sharedInteriorPair_boundaryZeroKirchhoff_controlEdges_interiorEdges :
    ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
      (∀ e ∈ ({sip01, sip12} : Finset sharedInteriorPairGraph.edgeSet), z e = 0) →
        z = 0 := by
  intro z hz hcontrol
  refine
    eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport
      z hz ?_
  intro e he
  exact hcontrol e (by simpa [sharedInteriorPair_interiorEdgeSupport_eq] using he)

theorem wheelWithInnerTriangle_boundaryZeroKirchhoff_controlEdges_interiorEdges :
    ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
      (∀ e ∈ ({wit01, wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet),
        z e = 0) →
        z = 0 := by
  intro z hz hcontrol
  refine
    eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport
      z hz ?_
  intro e he
  exact hcontrol e (by
    simpa [wheelWithInnerTriangle_interiorEdgeSupport_eq] using he)

/-! ## Single- and pair-forced boundary regressions -/

/-- The shared-interior-pair shell has a boundary-zero-only evader if only `sip01` is forced:
the unforced interior edge `sip12` can still carry a nonzero chain. -/
theorem sharedInteriorPair_sip01_only_has_boundaryZero_evader :
    sharedInteriorPairSip01OnlyEvader ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
      sharedInteriorPairSip01OnlyEvader sip01 = 0 ∧
      sharedInteriorPairSip01OnlyEvader sip12 = red ∧
      sharedInteriorPairSip01OnlyEvader ≠ 0 := by
  refine ⟨sharedInteriorPairSip01OnlyEvader_mem_planarBoundaryZeroSubmodule,
    by simp [sharedInteriorPairSip01OnlyEvader],
    by simp [sharedInteriorPairSip01OnlyEvader], ?_⟩
  intro hzero
  have h := congrFun hzero sip12
  simp [sharedInteriorPairSip01OnlyEvader] at h

/-- The shared-interior-pair shell has a boundary-zero-only evader if only `sip12` is forced:
the unforced interior edge `sip01` can still carry a nonzero chain. -/
theorem sharedInteriorPair_sip12_only_has_boundaryZero_evader :
    sharedInteriorPairSip12OnlyEvader ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
      sharedInteriorPairSip12OnlyEvader sip12 = 0 ∧
      sharedInteriorPairSip12OnlyEvader sip01 = red ∧
      sharedInteriorPairSip12OnlyEvader ≠ 0 := by
  refine ⟨sharedInteriorPairSip12OnlyEvader_mem_planarBoundaryZeroSubmodule,
    by simp [sharedInteriorPairSip12OnlyEvader],
    by simp [sharedInteriorPairSip12OnlyEvader], ?_⟩
  intro hzero
  have h := congrFun hzero sip01
  simp [sharedInteriorPairSip12OnlyEvader] at h

/-- With no forced interior edge, the shared-interior-pair shell still has a nonzero
boundary-zero/Kirchhoff chain. -/
theorem sharedInteriorPair_emptyControl_has_boundaryZeroKirchhoff_evader :
    sharedInteriorPairNoForceKirchhoffEvader ∈ theorem49BoundaryZeroKirchhoffSubspace
        sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) ∧
      sharedInteriorPairNoForceKirchhoffEvader sip01 = red ∧
      sharedInteriorPairNoForceKirchhoffEvader sip12 = red ∧
      sharedInteriorPairNoForceKirchhoffEvader ≠ 0 := by
  refine ⟨⟨sharedInteriorPairNoForceKirchhoffEvader_mem_kirchhoffSubmodule,
    sharedInteriorPairNoForceKirchhoffEvader_mem_planarBoundaryZeroSubmodule⟩,
    by simp [sharedInteriorPairNoForceKirchhoffEvader],
    by simp [sharedInteriorPairNoForceKirchhoffEvader], ?_⟩
  intro hzero
  have h := congrFun hzero sip01
  simp [sharedInteriorPairNoForceKirchhoffEvader] at h

/-- Kirchhoff parity at vertex `1` removes the shared-interior-pair single-`sip01` evader. -/
theorem sharedInteriorPair_boundaryZeroKirchhoff_no_evader_of_vanishes_on_sip01
    (z : sharedInteriorPairGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)))
    (hsip01 : z sip01 = 0) :
    z = 0 := by
  refine
    eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport_control_or_kirchhoffStar
      z hz ({sip01} : Finset sharedInteriorPairGraph.edgeSet) ?_ ?_
  · intro e he
    have heq : e = sip01 := by simpa using he
    subst e
    exact hsip01
  · intro e heInterior
    have he : e ∈ ({sip01, sip12} : Finset sharedInteriorPairGraph.edgeSet) := by
      simpa [sharedInteriorPair_interiorEdgeSupport_eq] using heInterior
    rcases Finset.mem_insert.1 he with rfl | heTail
    · exact Or.inl (by simp)
    · have he12 : e = sip12 := by simpa using heTail
      subst e
      refine Or.inr ⟨(1 : Fin 8), by simp, ?_, ?_⟩
      · rw [sharedInteriorPair_incidentEdgeFinset_one]
        simp
      · intro e' he' hne
        rw [sharedInteriorPair_incidentEdgeFinset_one] at he'
        rcases Finset.mem_insert.1 he' with h01 | heTail'
        · subst e'
          exact Or.inl (by simp)
        · have h12 : e' = sip12 := by simpa using heTail'
          subst e'
          exact False.elim (hne rfl)

/-- Kirchhoff parity at vertex `1` removes the shared-interior-pair single-`sip12` evader. -/
theorem sharedInteriorPair_boundaryZeroKirchhoff_no_evader_of_vanishes_on_sip12
    (z : sharedInteriorPairGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)))
    (hsip12 : z sip12 = 0) :
    z = 0 := by
  refine
    eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport_control_or_kirchhoffStar
      z hz ({sip12} : Finset sharedInteriorPairGraph.edgeSet) ?_ ?_
  · intro e he
    have heq : e = sip12 := by simpa using he
    subst e
    exact hsip12
  · intro e heInterior
    have he : e ∈ ({sip01, sip12} : Finset sharedInteriorPairGraph.edgeSet) := by
      simpa [sharedInteriorPair_interiorEdgeSupport_eq] using heInterior
    rcases Finset.mem_insert.1 he with rfl | heTail
    · refine Or.inr ⟨(1 : Fin 8), by simp, ?_, ?_⟩
      · rw [sharedInteriorPair_incidentEdgeFinset_one]
        simp
      · intro e' he' hne
        rw [sharedInteriorPair_incidentEdgeFinset_one] at he'
        rcases Finset.mem_insert.1 he' with h01 | heTail'
        · subst e'
          exact False.elim (hne rfl)
        · have h12 : e' = sip12 := by simpa using heTail'
          subst e'
          exact Or.inl (by simp)
    · have he12 : e = sip12 := by simpa using heTail
      subst e
      exact Or.inl (by simp)

/-- The wheel shell has a boundary-zero/Kirchhoff evader if only `wit01` is forced:
the two unforced spokes carry the same nonzero color and cancel at the center. -/
theorem wheelWithInnerTriangle_wit01_only_has_boundaryZeroKirchhoff_evader :
    wheelWithInnerTriangleWit01OnlyEvader ∈ theorem49BoundaryZeroKirchhoffSubspace
        wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
      wheelWithInnerTriangleWit01OnlyEvader wit01 = 0 ∧
      wheelWithInnerTriangleWit01OnlyEvader wit02 = red ∧
      wheelWithInnerTriangleWit01OnlyEvader wit03 = red ∧
      wheelWithInnerTriangleWit01OnlyEvader ≠ 0 := by
  refine ⟨⟨wheelWithInnerTriangleWit01OnlyEvader_mem_kirchhoffSubmodule,
    wheelWithInnerTriangleWit01OnlyEvader_mem_planarBoundaryZeroSubmodule⟩,
    by simp [wheelWithInnerTriangleWit01OnlyEvader],
    by simp [wheelWithInnerTriangleWit01OnlyEvader],
    by simp [wheelWithInnerTriangleWit01OnlyEvader], ?_⟩
  intro hzero
  have h := congrFun hzero wit02
  simp [wheelWithInnerTriangleWit01OnlyEvader] at h

/-- The wheel shell has a boundary-zero/Kirchhoff evader if only `wit02` is forced. -/
theorem wheelWithInnerTriangle_wit02_only_has_boundaryZeroKirchhoff_evader :
    wheelWithInnerTriangleWit02OnlyEvader ∈ theorem49BoundaryZeroKirchhoffSubspace
        wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
      wheelWithInnerTriangleWit02OnlyEvader wit02 = 0 ∧
      wheelWithInnerTriangleWit02OnlyEvader wit01 = red ∧
      wheelWithInnerTriangleWit02OnlyEvader wit03 = red ∧
      wheelWithInnerTriangleWit02OnlyEvader ≠ 0 := by
  refine ⟨⟨wheelWithInnerTriangleWit02OnlyEvader_mem_kirchhoffSubmodule,
    wheelWithInnerTriangleWit02OnlyEvader_mem_planarBoundaryZeroSubmodule⟩,
    by simp [wheelWithInnerTriangleWit02OnlyEvader],
    by simp [wheelWithInnerTriangleWit02OnlyEvader],
    by simp [wheelWithInnerTriangleWit02OnlyEvader], ?_⟩
  intro hzero
  have h := congrFun hzero wit01
  simp [wheelWithInnerTriangleWit02OnlyEvader] at h

/-- The wheel shell has a boundary-zero/Kirchhoff evader if only `wit03` is forced. -/
theorem wheelWithInnerTriangle_wit03_only_has_boundaryZeroKirchhoff_evader :
    wheelWithInnerTriangleWit03OnlyEvader ∈ theorem49BoundaryZeroKirchhoffSubspace
        wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
      wheelWithInnerTriangleWit03OnlyEvader wit03 = 0 ∧
      wheelWithInnerTriangleWit03OnlyEvader wit01 = red ∧
      wheelWithInnerTriangleWit03OnlyEvader wit02 = red ∧
      wheelWithInnerTriangleWit03OnlyEvader ≠ 0 := by
  refine ⟨⟨wheelWithInnerTriangleWit03OnlyEvader_mem_kirchhoffSubmodule,
    wheelWithInnerTriangleWit03OnlyEvader_mem_planarBoundaryZeroSubmodule⟩,
    by simp [wheelWithInnerTriangleWit03OnlyEvader],
    by simp [wheelWithInnerTriangleWit03OnlyEvader],
    by simp [wheelWithInnerTriangleWit03OnlyEvader], ?_⟩
  intro hzero
  have h := congrFun hzero wit01
  simp [wheelWithInnerTriangleWit03OnlyEvader] at h

/-- Without Kirchhoff parity, forcing only the pair `wit01,wit02` still leaves the third spoke as
a boundary-zero evader. -/
theorem wheelWithInnerTriangle_wit01_wit02_only_has_boundaryZero_evader :
    wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader ∈
        planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
      wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader wit01 = 0 ∧
      wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader wit02 = 0 ∧
      wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader wit03 = red ∧
      wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader ≠ 0 := by
  refine
    ⟨wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader_mem_planarBoundaryZeroSubmodule,
      by simp [wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader],
      by simp [wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader],
      by simp [wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader], ?_⟩
  intro hzero
  have h := congrFun hzero wit03
  simp [wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader] at h

/-- Without Kirchhoff parity, forcing only the pair `wit01,wit03` still leaves the third spoke as
a boundary-zero evader. -/
theorem wheelWithInnerTriangle_wit01_wit03_only_has_boundaryZero_evader :
    wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader ∈
        planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
      wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader wit01 = 0 ∧
      wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader wit03 = 0 ∧
      wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader wit02 = red ∧
      wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader ≠ 0 := by
  refine
    ⟨wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader_mem_planarBoundaryZeroSubmodule,
      by simp [wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader],
      by simp [wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader],
      by simp [wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader], ?_⟩
  intro hzero
  have h := congrFun hzero wit02
  simp [wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader] at h

/-- Without Kirchhoff parity, forcing only the pair `wit02,wit03` still leaves the third spoke as
a boundary-zero evader. -/
theorem wheelWithInnerTriangle_wit02_wit03_only_has_boundaryZero_evader :
    wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader ∈
        planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
      wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader wit02 = 0 ∧
      wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader wit03 = 0 ∧
      wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader wit01 = red ∧
      wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader ≠ 0 := by
  refine
    ⟨wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader_mem_planarBoundaryZeroSubmodule,
      by simp [wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader],
      by simp [wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader],
      by simp [wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader], ?_⟩
  intro hzero
  have h := congrFun hzero wit01
  simp [wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader] at h

/-- Kirchhoff parity at the wheel center removes the `wit01,wit02` pair-forced evader. -/
theorem wheelWithInnerTriangle_boundaryZeroKirchhoff_no_evader_of_vanishes_on_wit01_wit02
    (z : wheelWithInnerTriangleGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)))
    (hwit01 : z wit01 = 0) (hwit02 : z wit02 = 0) :
    z = 0 := by
  refine
    eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport_control_or_kirchhoffStar
      z hz ({wit01, wit02} : Finset wheelWithInnerTriangleGraph.edgeSet) ?_ ?_
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | heTail
    · exact hwit01
    · have he02 : e = wit02 := by simpa using heTail
      subst e
      exact hwit02
  · intro e heInterior
    have he :
        e ∈ ({wit01, wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
      simpa [wheelWithInnerTriangle_interiorEdgeSupport_eq] using heInterior
    rcases Finset.mem_insert.1 he with rfl | heTail
    · exact Or.inl (by simp)
    · rcases Finset.mem_insert.1 heTail with rfl | heTail'
      · exact Or.inl (by simp)
      · have he03 : e = wit03 := by simpa using heTail'
        subst e
        refine Or.inr ⟨(0 : Fin 7), by simp, ?_, ?_⟩
        · rw [wheelWithInnerTriangle_incidentEdgeFinset_zero]
          simp
        · intro e' he' hne
          rw [wheelWithInnerTriangle_incidentEdgeFinset_zero] at he'
          rcases Finset.mem_insert.1 he' with h01 | heTail''
          · subst e'
            exact Or.inl (by simp)
          · rcases Finset.mem_insert.1 heTail'' with h02 | heTail'''
            · subst e'
              exact Or.inl (by simp)
            · have h03 : e' = wit03 := by simpa using heTail'''
              subst e'
              exact False.elim (hne rfl)

/-- Kirchhoff parity at the wheel center removes the `wit01,wit03` pair-forced evader. -/
theorem wheelWithInnerTriangle_boundaryZeroKirchhoff_no_evader_of_vanishes_on_wit01_wit03
    (z : wheelWithInnerTriangleGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)))
    (hwit01 : z wit01 = 0) (hwit03 : z wit03 = 0) :
    z = 0 := by
  refine
    eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport_control_or_kirchhoffStar
      z hz ({wit01, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet) ?_ ?_
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | heTail
    · exact hwit01
    · have he03 : e = wit03 := by simpa using heTail
      subst e
      exact hwit03
  · intro e heInterior
    have he :
        e ∈ ({wit01, wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
      simpa [wheelWithInnerTriangle_interiorEdgeSupport_eq] using heInterior
    rcases Finset.mem_insert.1 he with rfl | heTail
    · exact Or.inl (by simp)
    · rcases Finset.mem_insert.1 heTail with rfl | heTail'
      · refine Or.inr ⟨(0 : Fin 7), by simp, ?_, ?_⟩
        · rw [wheelWithInnerTriangle_incidentEdgeFinset_zero]
          simp
        · intro e' he' hne
          rw [wheelWithInnerTriangle_incidentEdgeFinset_zero] at he'
          rcases Finset.mem_insert.1 he' with h01 | heTail''
          · subst e'
            exact Or.inl (by simp)
          · rcases Finset.mem_insert.1 heTail'' with h02 | heTail'''
            · subst e'
              exact False.elim (hne rfl)
            · have h03 : e' = wit03 := by simpa using heTail'''
              subst e'
              exact Or.inl (by simp)
      · have he03 : e = wit03 := by simpa using heTail'
        subst e
        exact Or.inl (by simp)

/-- Kirchhoff parity at the wheel center removes the `wit02,wit03` pair-forced evader. -/
theorem wheelWithInnerTriangle_boundaryZeroKirchhoff_no_evader_of_vanishes_on_wit02_wit03
    (z : wheelWithInnerTriangleGraph.edgeSet → Color)
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace
      wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)))
    (hwit02 : z wit02 = 0) (hwit03 : z wit03 = 0) :
    z = 0 := by
  refine
    eq_zero_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_interiorEdgeSupport_control_or_kirchhoffStar
      z hz ({wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet) ?_ ?_
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | heTail
    · exact hwit02
    · have he03 : e = wit03 := by simpa using heTail
      subst e
      exact hwit03
  · intro e heInterior
    have he :
        e ∈ ({wit01, wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
      simpa [wheelWithInnerTriangle_interiorEdgeSupport_eq] using heInterior
    rcases Finset.mem_insert.1 he with rfl | heTail
    · refine Or.inr ⟨(0 : Fin 7), by simp, ?_, ?_⟩
      · rw [wheelWithInnerTriangle_incidentEdgeFinset_zero]
        simp
      · intro e' he' hne
        rw [wheelWithInnerTriangle_incidentEdgeFinset_zero] at he'
        rcases Finset.mem_insert.1 he' with h01 | heTail''
        · subst e'
          exact False.elim (hne rfl)
        · rcases Finset.mem_insert.1 heTail'' with h02 | heTail'''
          · subst e'
            exact Or.inl (by simp)
          · have h03 : e' = wit03 := by simpa using heTail'''
            subst e'
            exact Or.inl (by simp)
    · rcases Finset.mem_insert.1 heTail with rfl | heTail'
      · exact Or.inl (by simp)
      · have he03 : e = wit03 := by simpa using heTail'
        subst e
        exact Or.inl (by simp)

/-! ## Generic empty-Kirchhoff boundary-zero profiles -/

def sharedInteriorPairInteriorControlEdges : Finset sharedInteriorPairGraph.edgeSet :=
  {sip01, sip12}

def sharedInteriorPairEmptyKirchhoffVertices : Finset (Fin 8) :=
  ∅

theorem sharedInteriorPair_selectedBoundarySupport_eq :
    selectedBoundarySupport
        sharedInteriorPairEmbedding.faceBoundary
        sharedInteriorPairEmbedding.faces
        sharedInteriorPairEmbedding.faces =
      ({sip23, sip30, sip24, sip40, sip56, sip67, sip75} :
        Finset sharedInteriorPairGraph.edgeSet) := by
  ext e
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem sharedInteriorPair_selectedBoundarySupport_induced :
    BoundaryEdgeSetInducedSubgraph
      ({sip23, sip30, sip24, sip40, sip56, sip67, sip75} :
        Finset sharedInteriorPairGraph.edgeSet) := by
  intro e hEndpoints
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    have hbad := hEndpoints (1 : Fin 8) (by decide)
    simp [boundaryEdgeSetEndpointSupport, sip23, sip30, sip24, sip40, sip56, sip67,
      sip75] at hbad
  · exfalso
    have hbad := hEndpoints (1 : Fin 8) (by decide)
    simp [boundaryEdgeSetEndpointSupport, sip23, sip30, sip24, sip40, sip56, sip67,
      sip75] at hbad
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp

theorem sharedInteriorPair_selectedBoundaryInducedSubgraph :
    SelectedBoundaryInducedSubgraph sharedInteriorPairEmbedding := by
  rw [SelectedBoundaryInducedSubgraph, sharedInteriorPair_selectedBoundarySupport_eq]
  exact sharedInteriorPair_selectedBoundarySupport_induced

theorem sharedInteriorPair_interiorEdgesNotSelectedBoundaryChords :
    InteriorEdgesNotSelectedBoundaryChords sharedInteriorPairEmbedding :=
  interiorEdgesNotSelectedBoundaryChords_of_selectedBoundaryInducedSubgraph
    sharedInteriorPair_selectedBoundaryInducedSubgraph

theorem sharedInteriorPair_interiorEdgeSupport_nonempty :
    (interiorEdgeSupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces).Nonempty := by
  refine ⟨sip01, ?_⟩
  rw [sharedInteriorPair_interiorEdgeSupport_eq]
  simp

theorem
    selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair_via_selectedBoundaryInducedSubgraph :
    (selectedBoundaryInteriorEdgeEndpointVertices sharedInteriorPairEmbedding).Nonempty :=
  selectedBoundaryInteriorEdgeEndpointVertices_nonempty_of_selectedBoundaryInducedSubgraph_and_nonempty
    sharedInteriorPair_selectedBoundaryInducedSubgraph
    sharedInteriorPair_interiorEdgeSupport_nonempty

theorem sharedInteriorPair_mem_selectedBoundarySupport_of_not_mem_interiorEdgeSupport
    {e : sharedInteriorPairGraph.edgeSet}
    (hnotInterior :
      e ∉ interiorEdgeSupport
        sharedInteriorPairEmbedding.faceBoundary sharedInteriorPairEmbedding.faces) :
    e ∈ selectedBoundarySupport
      sharedInteriorPairEmbedding.faceBoundary
      sharedInteriorPairEmbedding.faces
      sharedInteriorPairEmbedding.faces := by
  have hnotInterior' :
      e ∉ ({sip01, sip12} : Finset sharedInteriorPairGraph.edgeSet) := by
    simpa [sharedInteriorPair_interiorEdgeSupport_eq] using hnotInterior
  rw [sharedInteriorPair_selectedBoundarySupport_eq]
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (hnotInterior' (by simp))
  · exact False.elim (hnotInterior' (by simp))
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp

theorem sharedInteriorPairBoundaryZeroEmptyKirchhoffScalarConstraintSpace_finrank_lt_of_control_card_le_one
    (control : Finset sharedInteriorPairGraph.edgeSet) (hcard : control.card ≤ 1) :
    Module.finrank F2
      (theorem49BoundaryZeroKirchhoffScalarConstraintSpace
        sharedInteriorPairEmbedding sharedInteriorPairEmptyKirchhoffVertices control) <
      Fintype.card sharedInteriorPairGraph.edgeSet := by
  refine theorem49BoundaryZeroKirchhoffScalarConstraintSpace_finrank_lt_of_card_sum_lt
    sharedInteriorPairEmbedding sharedInteriorPairEmptyKirchhoffVertices control ?_
  have hboundary :
      Fintype.card {e : sharedInteriorPairGraph.edgeSet //
        e ∈ selectedBoundarySupport
          sharedInteriorPairEmbedding.faceBoundary
          sharedInteriorPairEmbedding.faces
          sharedInteriorPairEmbedding.faces} = 7 := by
    rw [sharedInteriorPair_selectedBoundarySupport_eq]
    decide
  have hvertices :
      Fintype.card {v : Fin 8 // v ∈ sharedInteriorPairEmptyKirchhoffVertices} = 0 := by
    decide
  have hedge : Fintype.card sharedInteriorPairGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hvertices, hedge]
  omega

theorem sharedInteriorPair_boundaryZeroEmptyKirchhoff_has_evader_of_control_card_le_one
    (control : Finset sharedInteriorPairGraph.edgeSet) (hcard : control.card ≤ 1) :
    ∃ z : sharedInteriorPairGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding sharedInteriorPairEmptyKirchhoffVertices ∧
      (∀ e ∈ control, z e = 0) ∧ z ≠ 0 := by
  refine exists_redScalarColorChain_mem_theorem49BoundaryZeroKirchhoffSubspace_of_card_sum_lt
    sharedInteriorPairEmbedding sharedInteriorPairEmptyKirchhoffVertices control ?_
  have hboundary :
      Fintype.card {e : sharedInteriorPairGraph.edgeSet //
        e ∈ selectedBoundarySupport
          sharedInteriorPairEmbedding.faceBoundary
          sharedInteriorPairEmbedding.faces
          sharedInteriorPairEmbedding.faces} = 7 := by
    rw [sharedInteriorPair_selectedBoundarySupport_eq]
    decide
  have hvertices :
      Fintype.card {v : Fin 8 // v ∈ sharedInteriorPairEmptyKirchhoffVertices} = 0 := by
    decide
  have hedge : Fintype.card sharedInteriorPairGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hvertices, hedge]
  omega

theorem sharedInteriorPair_boundaryZeroEmptyKirchhoff_no_evader_of_interiorControl
    (z : sharedInteriorPairGraph.edgeSet → Color)
    (hz :
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
        sharedInteriorPairEmbedding sharedInteriorPairEmptyKirchhoffVertices)
    (hcontrol : ∀ e ∈ sharedInteriorPairInteriorControlEdges, z e = 0) :
    z = 0 := by
  exact sharedInteriorPair_boundaryZero_no_evader_of_controlEdges
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
      sharedInteriorPairEmbedding sharedInteriorPairEmptyKirchhoffVertices hz)
    (by simpa [sharedInteriorPairInteriorControlEdges] using hcontrol)

theorem sharedInteriorPair_boundaryZeroEmptyKirchhoff_minimalControl_profile :
    (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding sharedInteriorPairEmptyKirchhoffVertices →
      (∀ e ∈ sharedInteriorPairInteriorControlEdges, z e = 0) →
      z = 0) ∧
    (∀ control : Finset sharedInteriorPairGraph.edgeSet,
      control.card ≤ 1 →
        ∃ z : sharedInteriorPairGraph.edgeSet → Color,
          z ∈ theorem49BoundaryZeroKirchhoffSubspace
              sharedInteriorPairEmbedding sharedInteriorPairEmptyKirchhoffVertices ∧
          (∀ e ∈ control, z e = 0) ∧ z ≠ 0) := by
  constructor
  · intro z hz hcontrol
    exact sharedInteriorPair_boundaryZeroEmptyKirchhoff_no_evader_of_interiorControl
      z hz hcontrol
  · exact sharedInteriorPair_boundaryZeroEmptyKirchhoff_has_evader_of_control_card_le_one

theorem sharedInteriorPair_planarBoundaryZero_has_evader_of_control_card_le_one
    (control : Finset sharedInteriorPairGraph.edgeSet) (hcard : control.card ≤ 1) :
    ∃ z : sharedInteriorPairGraph.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
      (∀ e ∈ control, z e = 0) ∧ z ≠ 0 := by
  refine exists_mem_planarBoundaryZeroSubmodule_of_control_card_add_boundary_card_lt
    sharedInteriorPairEmbedding control ?_
  have hboundary :
      Fintype.card {e : sharedInteriorPairGraph.edgeSet //
        e ∈ selectedBoundarySupport
          sharedInteriorPairEmbedding.faceBoundary
          sharedInteriorPairEmbedding.faces
          sharedInteriorPairEmbedding.faces} = 7 := by
    rw [sharedInteriorPair_selectedBoundarySupport_eq]
    decide
  have hedge : Fintype.card sharedInteriorPairGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hedge]
  omega

theorem sharedInteriorPair_boundaryZero_cardinalityControl_profile :
    (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
      (∀ e ∈ sharedInteriorPairInteriorControlEdges, z e = 0) →
      z = 0) ∧
    (∀ control : Finset sharedInteriorPairGraph.edgeSet,
      control.card ≤ 1 →
        ∃ z : sharedInteriorPairGraph.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
          (∀ e ∈ control, z e = 0) ∧ z ≠ 0) := by
  constructor
  · intro z hz hcontrol
    exact sharedInteriorPair_boundaryZero_controlEdges_interiorEdges
      hz (by simpa [sharedInteriorPairInteriorControlEdges] using hcontrol)
  · exact sharedInteriorPair_planarBoundaryZero_has_evader_of_control_card_le_one

theorem sharedInteriorPair_boundaryZero_control_card_ge_two
    (control : Finset sharedInteriorPairGraph.edgeSet)
    (hcontrol :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        (∀ e ∈ control, z e = 0) →
        z = 0) :
    2 ≤ control.card := by
  have hLower :=
    edge_card_le_control_card_add_boundary_card_of_planarBoundaryZeroSubmodule_control
      sharedInteriorPairEmbedding control hcontrol
  have hboundary :
      Fintype.card {e : sharedInteriorPairGraph.edgeSet //
        e ∈ selectedBoundarySupport
          sharedInteriorPairEmbedding.faceBoundary
          sharedInteriorPairEmbedding.faces
          sharedInteriorPairEmbedding.faces} = 7 := by
    rw [sharedInteriorPair_selectedBoundarySupport_eq]
    decide
  have hedge : Fintype.card sharedInteriorPairGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hedge] at hLower
  omega

/--
Negative-control form for the shared-interior-pair shell.  Any one-edge control set leaves a
nonzero selected-boundary-zero evader, so the boundary-zero detector genuinely needs both
interior coordinates on this shell.
-/
theorem sharedInteriorPair_boundaryZero_has_evader_of_control_card_lt_two
    (control : Finset sharedInteriorPairGraph.edgeSet) (hcard : control.card < 2) :
    ∃ z : sharedInteriorPairGraph.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
        (∀ e ∈ control, z e = 0) ∧ z ≠ 0 :=
  sharedInteriorPair_planarBoundaryZero_has_evader_of_control_card_le_one
    control (by omega)

/-- Singleton-control specialization of the shared-interior-pair negative-control certificate. -/
theorem sharedInteriorPair_boundaryZero_has_evader_of_singleton_control
    (e : sharedInteriorPairGraph.edgeSet) :
    ∃ z : sharedInteriorPairGraph.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧ z e = 0 ∧ z ≠ 0 := by
  rcases sharedInteriorPair_boundaryZero_has_evader_of_control_card_lt_two
      ({e} : Finset sharedInteriorPairGraph.edgeSet) (by simp) with
    ⟨z, hzBoundary, hvanish, hzNonzero⟩
  exact ⟨z, hzBoundary, hvanish e (by simp), hzNonzero⟩

/--
Interior-control lower bound for the shared-interior-pair shell.  Boundary controls are
irrelevant for selected-boundary-zero chains, so any controlling set must contain both interior
support edges.
-/
theorem sharedInteriorPair_boundaryZero_interiorControl_card_ge_two
    (control : Finset sharedInteriorPairGraph.edgeSet)
    (hcontrol :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        (∀ e ∈ control, z e = 0) →
        z = 0) :
    2 ≤ (control.filter fun e =>
      e ∈ interiorEdgeSupport
        sharedInteriorPairEmbedding.faceBoundary sharedInteriorPairEmbedding.faces).card := by
  by_contra hnot
  have hlt :
      (control.filter fun e =>
        e ∈ interiorEdgeSupport
          sharedInteriorPairEmbedding.faceBoundary sharedInteriorPairEmbedding.faces).card < 2 :=
    Nat.lt_of_not_ge hnot
  rcases sharedInteriorPair_boundaryZero_has_evader_of_control_card_lt_two
      (control.filter fun e =>
        e ∈ interiorEdgeSupport
          sharedInteriorPairEmbedding.faceBoundary sharedInteriorPairEmbedding.faces) hlt with
    ⟨z, hzBoundary, hvanishInterior, hzNonzero⟩
  have hvanishControl : ∀ e ∈ control, z e = 0 := by
    intro e heControl
    by_cases heInterior :
        e ∈ interiorEdgeSupport
          sharedInteriorPairEmbedding.faceBoundary sharedInteriorPairEmbedding.faces
    · exact hvanishInterior e (Finset.mem_filter.2 ⟨heControl, heInterior⟩)
    · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary e
        (sharedInteriorPair_mem_selectedBoundarySupport_of_not_mem_interiorEdgeSupport
          heInterior)
  exact hzNonzero (hcontrol hzBoundary hvanishControl)

theorem sharedInteriorPair_boundaryZeroKirchhoff_control_card_ge_one
    (control : Finset sharedInteriorPairGraph.edgeSet)
    (hcontrol :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
        (∀ e ∈ control, z e = 0) →
        z = 0) :
    1 ≤ control.card := by
  have hLower :=
    edge_card_le_control_card_add_boundary_card_add_vertex_card_of_theorem49BoundaryZeroKirchhoffSubspace_control
      sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) control hcontrol
  have hboundary :
      Fintype.card {e : sharedInteriorPairGraph.edgeSet //
        e ∈ selectedBoundarySupport
          sharedInteriorPairEmbedding.faceBoundary
          sharedInteriorPairEmbedding.faces
          sharedInteriorPairEmbedding.faces} = 7 := by
    rw [sharedInteriorPair_selectedBoundarySupport_eq]
    decide
  have hvertices :
      Fintype.card {v : Fin 8 // v ∈ ({(1 : Fin 8)} : Finset (Fin 8))} = 1 := by
    decide
  have hedge : Fintype.card sharedInteriorPairGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hvertices, hedge] at hLower
  omega

def wheelWithInnerTriangleInteriorControlEdges :
    Finset wheelWithInnerTriangleGraph.edgeSet :=
  {wit01, wit02, wit03}

def wheelWithInnerTriangleEmptyKirchhoffVertices : Finset (Fin 7) :=
  ∅

theorem wheelWithInnerTriangle_selectedBoundarySupport_eq :
    selectedBoundarySupport
        wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces
        wheelWithInnerTriangleEmbedding.faces =
      ({wit12, wit23, wit31, wit45, wit56, wit64} :
        Finset wheelWithInnerTriangleGraph.edgeSet) := by
  ext e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem wheelWithInnerTriangle_selectedBoundarySupport_induced :
    BoundaryEdgeSetInducedSubgraph
      ({wit12, wit23, wit31, wit45, wit56, wit64} :
        Finset wheelWithInnerTriangleGraph.edgeSet) := by
  intro e hEndpoints
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    have hbad := hEndpoints (0 : Fin 7) (by decide)
    simp [boundaryEdgeSetEndpointSupport, wit12, wit23, wit31, wit45, wit56,
      wit64] at hbad
  · exfalso
    have hbad := hEndpoints (0 : Fin 7) (by decide)
    simp [boundaryEdgeSetEndpointSupport, wit12, wit23, wit31, wit45, wit56,
      wit64] at hbad
  · exfalso
    have hbad := hEndpoints (0 : Fin 7) (by decide)
    simp [boundaryEdgeSetEndpointSupport, wit12, wit23, wit31, wit45, wit56,
      wit64] at hbad
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp

theorem wheelWithInnerTriangle_selectedBoundaryInducedSubgraph :
    SelectedBoundaryInducedSubgraph wheelWithInnerTriangleEmbedding := by
  rw [SelectedBoundaryInducedSubgraph, wheelWithInnerTriangle_selectedBoundarySupport_eq]
  exact wheelWithInnerTriangle_selectedBoundarySupport_induced

theorem wheelWithInnerTriangle_interiorEdgesNotSelectedBoundaryChords :
    InteriorEdgesNotSelectedBoundaryChords wheelWithInnerTriangleEmbedding :=
  interiorEdgesNotSelectedBoundaryChords_of_selectedBoundaryInducedSubgraph
    wheelWithInnerTriangle_selectedBoundaryInducedSubgraph

theorem wheelWithInnerTriangle_interiorEdgeSupport_nonempty :
    (interiorEdgeSupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces).Nonempty := by
  refine ⟨wit01, ?_⟩
  rw [wheelWithInnerTriangle_interiorEdgeSupport_eq]
  simp

theorem
    selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle_via_selectedBoundaryInducedSubgraph :
    (selectedBoundaryInteriorEdgeEndpointVertices wheelWithInnerTriangleEmbedding).Nonempty :=
  selectedBoundaryInteriorEdgeEndpointVertices_nonempty_of_selectedBoundaryInducedSubgraph_and_nonempty
    wheelWithInnerTriangle_selectedBoundaryInducedSubgraph
    wheelWithInnerTriangle_interiorEdgeSupport_nonempty

theorem wheelWithInnerTriangle_mem_selectedBoundarySupport_of_not_mem_interiorEdgeSupport
    {e : wheelWithInnerTriangleGraph.edgeSet}
    (hnotInterior :
      e ∉ interiorEdgeSupport
        wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces) :
    e ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces := by
  have hnotInterior' :
      e ∉ ({wit01, wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
    simpa [wheelWithInnerTriangle_interiorEdgeSupport_eq] using hnotInterior
  rw [wheelWithInnerTriangle_selectedBoundarySupport_eq]
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (hnotInterior' (by simp))
  · exact False.elim (hnotInterior' (by simp))
  · exact False.elim (hnotInterior' (by simp))
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp

theorem wheelWithInnerTriangleBoundaryZeroEmptyKirchhoffScalarConstraintSpace_finrank_lt_of_control_card_le_two
    (control : Finset wheelWithInnerTriangleGraph.edgeSet) (hcard : control.card ≤ 2) :
    Module.finrank F2
      (theorem49BoundaryZeroKirchhoffScalarConstraintSpace
        wheelWithInnerTriangleEmbedding wheelWithInnerTriangleEmptyKirchhoffVertices control) <
      Fintype.card wheelWithInnerTriangleGraph.edgeSet := by
  refine theorem49BoundaryZeroKirchhoffScalarConstraintSpace_finrank_lt_of_card_sum_lt
    wheelWithInnerTriangleEmbedding wheelWithInnerTriangleEmptyKirchhoffVertices control ?_
  have hboundary :
      Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
        e ∈ selectedBoundarySupport
          wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces
          wheelWithInnerTriangleEmbedding.faces} = 6 := by
    rw [wheelWithInnerTriangle_selectedBoundarySupport_eq]
    decide
  have hvertices :
      Fintype.card {v : Fin 7 // v ∈ wheelWithInnerTriangleEmptyKirchhoffVertices} = 0 := by
    decide
  have hedge : Fintype.card wheelWithInnerTriangleGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hvertices, hedge]
  omega

theorem wheelWithInnerTriangle_boundaryZeroEmptyKirchhoff_has_evader_of_control_card_le_two
    (control : Finset wheelWithInnerTriangleGraph.edgeSet) (hcard : control.card ≤ 2) :
    ∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding wheelWithInnerTriangleEmptyKirchhoffVertices ∧
      (∀ e ∈ control, z e = 0) ∧ z ≠ 0 := by
  refine exists_redScalarColorChain_mem_theorem49BoundaryZeroKirchhoffSubspace_of_card_sum_lt
    wheelWithInnerTriangleEmbedding wheelWithInnerTriangleEmptyKirchhoffVertices control ?_
  have hboundary :
      Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
        e ∈ selectedBoundarySupport
          wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces
          wheelWithInnerTriangleEmbedding.faces} = 6 := by
    rw [wheelWithInnerTriangle_selectedBoundarySupport_eq]
    decide
  have hvertices :
      Fintype.card {v : Fin 7 // v ∈ wheelWithInnerTriangleEmptyKirchhoffVertices} = 0 := by
    decide
  have hedge : Fintype.card wheelWithInnerTriangleGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hvertices, hedge]
  omega

theorem wheelWithInnerTriangle_boundaryZeroEmptyKirchhoff_no_evader_of_interiorControl
    (z : wheelWithInnerTriangleGraph.edgeSet → Color)
    (hz :
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
        wheelWithInnerTriangleEmbedding wheelWithInnerTriangleEmptyKirchhoffVertices)
    (hcontrol : ∀ e ∈ wheelWithInnerTriangleInteriorControlEdges, z e = 0) :
    z = 0 := by
  exact wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
      wheelWithInnerTriangleEmbedding wheelWithInnerTriangleEmptyKirchhoffVertices hz)
    (by simpa [wheelWithInnerTriangleInteriorControlEdges] using hcontrol)

theorem wheelWithInnerTriangle_boundaryZeroEmptyKirchhoff_minimalControl_profile :
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding wheelWithInnerTriangleEmptyKirchhoffVertices →
      (∀ e ∈ wheelWithInnerTriangleInteriorControlEdges, z e = 0) →
      z = 0) ∧
    (∀ control : Finset wheelWithInnerTriangleGraph.edgeSet,
      control.card ≤ 2 →
        ∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
          z ∈ theorem49BoundaryZeroKirchhoffSubspace
              wheelWithInnerTriangleEmbedding wheelWithInnerTriangleEmptyKirchhoffVertices ∧
          (∀ e ∈ control, z e = 0) ∧ z ≠ 0) := by
  constructor
  · intro z hz hcontrol
    exact wheelWithInnerTriangle_boundaryZeroEmptyKirchhoff_no_evader_of_interiorControl
      z hz hcontrol
  · exact wheelWithInnerTriangle_boundaryZeroEmptyKirchhoff_has_evader_of_control_card_le_two

theorem wheelWithInnerTriangle_planarBoundaryZero_has_evader_of_control_card_le_two
    (control : Finset wheelWithInnerTriangleGraph.edgeSet) (hcard : control.card ≤ 2) :
    ∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
      (∀ e ∈ control, z e = 0) ∧ z ≠ 0 := by
  refine exists_mem_planarBoundaryZeroSubmodule_of_control_card_add_boundary_card_lt
    wheelWithInnerTriangleEmbedding control ?_
  have hboundary :
      Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
        e ∈ selectedBoundarySupport
          wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces
          wheelWithInnerTriangleEmbedding.faces} = 6 := by
    rw [wheelWithInnerTriangle_selectedBoundarySupport_eq]
    decide
  have hedge : Fintype.card wheelWithInnerTriangleGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hedge]
  omega

theorem wheelWithInnerTriangle_boundaryZero_cardinalityControl_profile :
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
      (∀ e ∈ wheelWithInnerTriangleInteriorControlEdges, z e = 0) →
      z = 0) ∧
    (∀ control : Finset wheelWithInnerTriangleGraph.edgeSet,
      control.card ≤ 2 →
        ∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
          (∀ e ∈ control, z e = 0) ∧ z ≠ 0) := by
  constructor
  · intro z hz hcontrol
    exact wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges
      hz (by simpa [wheelWithInnerTriangleInteriorControlEdges] using hcontrol)
  · exact wheelWithInnerTriangle_planarBoundaryZero_has_evader_of_control_card_le_two

theorem wheelWithInnerTriangle_boundaryZero_control_card_ge_three
    (control : Finset wheelWithInnerTriangleGraph.edgeSet)
    (hcontrol :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        (∀ e ∈ control, z e = 0) →
        z = 0) :
    3 ≤ control.card := by
  have hLower :=
    edge_card_le_control_card_add_boundary_card_of_planarBoundaryZeroSubmodule_control
      wheelWithInnerTriangleEmbedding control hcontrol
  have hboundary :
      Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
        e ∈ selectedBoundarySupport
          wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces
          wheelWithInnerTriangleEmbedding.faces} = 6 := by
    rw [wheelWithInnerTriangle_selectedBoundarySupport_eq]
    decide
  have hedge : Fintype.card wheelWithInnerTriangleGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hedge] at hLower
  omega

/--
Negative-control form for the wheel-with-inner-triangle shell without Kirchhoff parity.  Any
control set of size at most two leaves a nonzero selected-boundary-zero evader; all three spokes
are needed for boundary-zero-only control.
-/
theorem wheelWithInnerTriangle_boundaryZero_has_evader_of_control_card_lt_three
    (control : Finset wheelWithInnerTriangleGraph.edgeSet) (hcard : control.card < 3) :
    ∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
        (∀ e ∈ control, z e = 0) ∧ z ≠ 0 :=
  wheelWithInnerTriangle_planarBoundaryZero_has_evader_of_control_card_le_two
    control (by omega)

/--
Interior-control lower bound for the wheel-with-inner-triangle shell without Kirchhoff parity.
Boundary controls are automatic under boundary-zero, so any controlling set must contain all
three interior spokes.
-/
theorem wheelWithInnerTriangle_boundaryZero_interiorControl_card_ge_three
    (control : Finset wheelWithInnerTriangleGraph.edgeSet)
    (hcontrol :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        (∀ e ∈ control, z e = 0) →
        z = 0) :
    3 ≤ (control.filter fun e =>
      e ∈ interiorEdgeSupport
        wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces).card := by
  by_contra hnot
  have hlt :
      (control.filter fun e =>
        e ∈ interiorEdgeSupport
          wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces).card < 3 :=
    Nat.lt_of_not_ge hnot
  rcases wheelWithInnerTriangle_boundaryZero_has_evader_of_control_card_lt_three
      (control.filter fun e =>
        e ∈ interiorEdgeSupport
          wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces) hlt with
    ⟨z, hzBoundary, hvanishInterior, hzNonzero⟩
  have hvanishControl : ∀ e ∈ control, z e = 0 := by
    intro e heControl
    by_cases heInterior :
        e ∈ interiorEdgeSupport
          wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces
    · exact hvanishInterior e (Finset.mem_filter.2 ⟨heControl, heInterior⟩)
    · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary e
        (wheelWithInnerTriangle_mem_selectedBoundarySupport_of_not_mem_interiorEdgeSupport
          heInterior)
  exact hzNonzero (hcontrol hzBoundary hvanishControl)

theorem wheelWithInnerTriangle_boundaryZeroKirchhoff_control_card_ge_two
    (control : Finset wheelWithInnerTriangleGraph.edgeSet)
    (hcontrol :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
        (∀ e ∈ control, z e = 0) →
        z = 0) :
    2 ≤ control.card := by
  have hLower :=
    edge_card_le_control_card_add_boundary_card_add_vertex_card_of_theorem49BoundaryZeroKirchhoffSubspace_control
      wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) control hcontrol
  have hboundary :
      Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
        e ∈ selectedBoundarySupport
          wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces
          wheelWithInnerTriangleEmbedding.faces} = 6 := by
    rw [wheelWithInnerTriangle_selectedBoundarySupport_eq]
    decide
  have hvertices :
      Fintype.card {v : Fin 7 // v ∈ ({(0 : Fin 7)} : Finset (Fin 7))} = 1 := by
    decide
  have hedge : Fintype.card wheelWithInnerTriangleGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hvertices, hedge] at hLower
  omega

/--
Negative-control form for the wheel-with-inner-triangle shell with Kirchhoff parity at the
center.  A single forced edge still leaves a nonzero boundary-zero/Kirchhoff evader, so the
Kirchhoff repair lowers the necessary control size from three to two but does not make a
one-edge forced route sufficient.
-/
theorem wheelWithInnerTriangle_boundaryZeroKirchhoff_has_evader_of_control_card_lt_two
    (control : Finset wheelWithInnerTriangleGraph.edgeSet) (hcard : control.card < 2) :
    ∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
        (∀ e ∈ control, z e = 0) ∧ z ≠ 0 := by
  classical
  by_contra hnoEvader
  have hcontrol :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
        (∀ e ∈ control, z e = 0) →
        z = 0 := by
    intro z hz hvanish
    by_contra hzNonzero
    exact hnoEvader ⟨z, hz, hvanish, hzNonzero⟩
  have hge := wheelWithInnerTriangle_boundaryZeroKirchhoff_control_card_ge_two
    control hcontrol
  omega

/--
Singleton-control specialization of the wheel-with-inner-triangle Kirchhoff negative-control
certificate.  This is the finite obstruction to any corrected CAP5 lane that tries to make one
forced spoke control the whole boundary-zero/Kirchhoff kernel.
-/
theorem wheelWithInnerTriangle_boundaryZeroKirchhoff_has_evader_of_singleton_control
    (e : wheelWithInnerTriangleGraph.edgeSet) :
    ∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
        z e = 0 ∧ z ≠ 0 := by
  rcases wheelWithInnerTriangle_boundaryZeroKirchhoff_has_evader_of_control_card_lt_two
      ({e} : Finset wheelWithInnerTriangleGraph.edgeSet) (by simp) with
    ⟨z, hzBoundary, hvanish, hzNonzero⟩
  exact ⟨z, hzBoundary, hvanish e (by simp), hzNonzero⟩

/--
Interior-control lower bound for the Kirchhoff-repaired wheel shell.  Boundary controls still
vanish automatically, and the center Kirchhoff equation reduces the needed interior controls to
two, but one interior spoke remains insufficient.
-/
theorem wheelWithInnerTriangle_boundaryZeroKirchhoff_interiorControl_card_ge_two
    (control : Finset wheelWithInnerTriangleGraph.edgeSet)
    (hcontrol :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
        (∀ e ∈ control, z e = 0) →
        z = 0) :
    2 ≤ (control.filter fun e =>
      e ∈ interiorEdgeSupport
        wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces).card := by
  by_contra hnot
  have hlt :
      (control.filter fun e =>
        e ∈ interiorEdgeSupport
          wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces).card < 2 :=
    Nat.lt_of_not_ge hnot
  rcases wheelWithInnerTriangle_boundaryZeroKirchhoff_has_evader_of_control_card_lt_two
      (control.filter fun e =>
        e ∈ interiorEdgeSupport
          wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces) hlt with
    ⟨z, hz, hvanishInterior, hzNonzero⟩
  have hzBoundary : z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding :=
    theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
      wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) hz
  have hvanishControl : ∀ e ∈ control, z e = 0 := by
    intro e heControl
    by_cases heInterior :
        e ∈ interiorEdgeSupport
          wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces
    · exact hvanishInterior e (Finset.mem_filter.2 ⟨heControl, heInterior⟩)
    · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary e
        (wheelWithInnerTriangle_mem_selectedBoundarySupport_of_not_mem_interiorEdgeSupport
          heInterior)
  exact hzNonzero (hcontrol hz hvanishControl)

/-! ## CAP5 classifier interior-control lower bounds -/

/--
Classifier-facing form of the shared-interior-pair lower bound.  Any CAP5 emitted-edge
classifier that controls the selected-boundary-zero chains on this shell must emit both interior
support edges; boundary emitted edges do not contribute to this count.
-/
theorem sharedInteriorPair_boundaryZero_classifierControl_emittedInterior_card_ge_two
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 8 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcontrol :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0) :
    2 ≤ (classifier.emittedFinset.filter fun e =>
      e ∈ interiorEdgeSupport
        sharedInteriorPairEmbedding.faceBoundary sharedInteriorPairEmbedding.faces).card :=
  sharedInteriorPair_boundaryZero_interiorControl_card_ge_two
    classifier.emittedFinset hcontrol

/--
Classifier-facing form of the wheel boundary-zero lower bound.  A CAP5 emitted-edge classifier
that controls the selected-boundary-zero chains on the wheel-with-inner-triangle shell must emit
all three interior spokes, not merely boundary edges.
-/
theorem wheelWithInnerTriangle_boundaryZero_classifierControl_emittedInterior_card_ge_three
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 7 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcontrol :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0) :
    3 ≤ (classifier.emittedFinset.filter fun e =>
      e ∈ interiorEdgeSupport
        wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces).card :=
  wheelWithInnerTriangle_boundaryZero_interiorControl_card_ge_three
    classifier.emittedFinset hcontrol

/--
Kirchhoff-repaired classifier-facing lower bound for the wheel-with-inner-triangle shell.  The
center Kirchhoff constraint reduces the necessary interior controls from three to two, but a
single emitted spoke still cannot control all boundary-zero Kirchhoff chains.
-/
theorem wheelWithInnerTriangle_boundaryZeroKirchhoff_classifierControl_emittedInterior_card_ge_two
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 7 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcontrol :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0) :
    2 ≤ (classifier.emittedFinset.filter fun e =>
      e ∈ interiorEdgeSupport
        wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces).card :=
  wheelWithInnerTriangle_boundaryZeroKirchhoff_interiorControl_card_ge_two
    classifier.emittedFinset hcontrol

/-! ## Exact finite-control-size certificates -/

theorem sharedInteriorPair_boundaryZero_exactMinimumControlCard :
    (∃ control : Finset sharedInteriorPairGraph.edgeSet,
      control.card = 2 ∧
        ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
          (∀ e ∈ control, z e = 0) →
          z = 0) ∧
    (∀ control : Finset sharedInteriorPairGraph.edgeSet,
      (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        (∀ e ∈ control, z e = 0) →
        z = 0) →
      2 ≤ control.card) := by
  constructor
  · refine ⟨sharedInteriorPairInteriorControlEdges, ?_, ?_⟩
    · simp [sharedInteriorPairInteriorControlEdges]
    · exact sharedInteriorPair_boundaryZero_controlEdges_interiorEdges
  · intro control hcontrol
    exact sharedInteriorPair_boundaryZero_control_card_ge_two control hcontrol

theorem sharedInteriorPair_boundaryZeroKirchhoff_exactMinimumControlCard :
    (∃ control : Finset sharedInteriorPairGraph.edgeSet,
      control.card = 1 ∧
        ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
          z ∈ theorem49BoundaryZeroKirchhoffSubspace
              sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
          (∀ e ∈ control, z e = 0) →
          z = 0) ∧
    (∀ control : Finset sharedInteriorPairGraph.edgeSet,
      (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
        (∀ e ∈ control, z e = 0) →
        z = 0) →
      1 ≤ control.card) := by
  constructor
  · refine ⟨({sip01} : Finset sharedInteriorPairGraph.edgeSet), ?_, ?_⟩
    · simp
    · intro z hz hcontrol
      exact sharedInteriorPair_boundaryZeroKirchhoff_no_evader_of_vanishes_on_sip01
        z hz (hcontrol sip01 (by simp))
  · intro control hcontrol
    exact sharedInteriorPair_boundaryZeroKirchhoff_control_card_ge_one control hcontrol

theorem wheelWithInnerTriangle_boundaryZero_exactMinimumControlCard :
    (∃ control : Finset wheelWithInnerTriangleGraph.edgeSet,
      control.card = 3 ∧
        ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
          (∀ e ∈ control, z e = 0) →
          z = 0) ∧
    (∀ control : Finset wheelWithInnerTriangleGraph.edgeSet,
      (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        (∀ e ∈ control, z e = 0) →
        z = 0) →
      3 ≤ control.card) := by
  constructor
  · refine ⟨wheelWithInnerTriangleInteriorControlEdges, ?_, ?_⟩
    · simp [wheelWithInnerTriangleInteriorControlEdges]
    · exact wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges
  · intro control hcontrol
    exact wheelWithInnerTriangle_boundaryZero_control_card_ge_three control hcontrol

theorem wheelWithInnerTriangle_boundaryZeroKirchhoff_exactMinimumControlCard :
    (∃ control : Finset wheelWithInnerTriangleGraph.edgeSet,
      control.card = 2 ∧
        ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
          z ∈ theorem49BoundaryZeroKirchhoffSubspace
              wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
          (∀ e ∈ control, z e = 0) →
          z = 0) ∧
    (∀ control : Finset wheelWithInnerTriangleGraph.edgeSet,
      (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
        (∀ e ∈ control, z e = 0) →
        z = 0) →
      2 ≤ control.card) := by
  constructor
  · refine ⟨({wit01, wit02} : Finset wheelWithInnerTriangleGraph.edgeSet), ?_, ?_⟩
    · simp
    · intro z hz hcontrol
      exact wheelWithInnerTriangle_boundaryZeroKirchhoff_no_evader_of_vanishes_on_wit01_wit02
        z hz (hcontrol wit01 (by simp)) (hcontrol wit02 (by simp))
  · intro control hcontrol
    exact wheelWithInnerTriangle_boundaryZeroKirchhoff_control_card_ge_two control hcontrol

/-! ## Minimal-control F2 profiles -/

/-- Lab-confirmed boundary-zero-only profile for the shared-interior-pair shell: both interior
edges force zero, while either single forced edge leaves an explicit nonzero evader. -/
theorem sharedInteriorPair_boundaryZero_minimalControl_profile :
    (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
      z sip01 = 0 → z sip12 = 0 → z = 0) ∧
    (∃ z : sharedInteriorPairGraph.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
      z sip01 = 0 ∧ z sip12 ≠ 0) ∧
    (∃ z : sharedInteriorPairGraph.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
      z sip12 = 0 ∧ z sip01 ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hzBoundary hsip01 hsip12
    exact sharedInteriorPair_boundaryZero_no_evader_of_vanishes_on_interiorEdges
      z hzBoundary hsip01 hsip12
  · refine ⟨sharedInteriorPairSip01OnlyEvader,
      sharedInteriorPairSip01OnlyEvader_mem_planarBoundaryZeroSubmodule,
      by simp [sharedInteriorPairSip01OnlyEvader], ?_⟩
    simp [sharedInteriorPairSip01OnlyEvader]
  · refine ⟨sharedInteriorPairSip12OnlyEvader,
      sharedInteriorPairSip12OnlyEvader_mem_planarBoundaryZeroSubmodule,
      by simp [sharedInteriorPairSip12OnlyEvader], ?_⟩
    simp [sharedInteriorPairSip12OnlyEvader]

/-- Lab-confirmed boundary-zero-plus-Kirchhoff profile for the shared-interior-pair shell:
no forced edge still has a nonzero evader, while either one of the two interior edges forces
zero once Kirchhoff parity at the shared vertex is imposed. -/
theorem sharedInteriorPair_boundaryZeroKirchhoff_minimalControl_profile :
    (∃ z : sharedInteriorPairGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) ∧
      z ≠ 0) ∧
    (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
      z sip01 = 0 → z = 0) ∧
    (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
      z sip12 = 0 → z = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨sharedInteriorPairNoForceKirchhoffEvader,
      ⟨sharedInteriorPairNoForceKirchhoffEvader_mem_kirchhoffSubmodule,
        sharedInteriorPairNoForceKirchhoffEvader_mem_planarBoundaryZeroSubmodule⟩, ?_⟩
    intro hzero
    have h := congrFun hzero sip01
    simp [sharedInteriorPairNoForceKirchhoffEvader] at h
  · intro z hz hsip01
    exact sharedInteriorPair_boundaryZeroKirchhoff_no_evader_of_vanishes_on_sip01
      z hz hsip01
  · intro z hz hsip12
    exact sharedInteriorPair_boundaryZeroKirchhoff_no_evader_of_vanishes_on_sip12
      z hz hsip12

/-- Combined lab-to-Lean packet for the shared-interior-pair focus shell.  The shell satisfies
the selected-boundary induced/chord-free carrier condition, and its boundary-zero detector has
the exact minimal-control behavior computed by the F2 lab. -/
theorem sharedInteriorPair_selectedBoundaryInduced_carrier_and_F2MinimalControl_profile :
    SelectedBoundaryInducedSubgraph sharedInteriorPairEmbedding ∧
      InteriorEdgesNotSelectedBoundaryChords sharedInteriorPairEmbedding ∧
      (selectedBoundaryInteriorEdgeEndpointVertices sharedInteriorPairEmbedding).Nonempty ∧
      ((∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        z sip01 = 0 → z sip12 = 0 → z = 0) ∧
      (∃ z : sharedInteriorPairGraph.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
        z sip01 = 0 ∧ z sip12 ≠ 0) ∧
      (∃ z : sharedInteriorPairGraph.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
        z sip12 = 0 ∧ z sip01 ≠ 0)) ∧
      ((∃ z : sharedInteriorPairGraph.edgeSet → Color,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) ∧
        z ≠ 0) ∧
      (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
        z sip01 = 0 → z = 0) ∧
      (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
        z sip12 = 0 → z = 0)) :=
  ⟨sharedInteriorPair_selectedBoundaryInducedSubgraph,
    sharedInteriorPair_interiorEdgesNotSelectedBoundaryChords,
    selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair_via_selectedBoundaryInducedSubgraph,
    sharedInteriorPair_boundaryZero_minimalControl_profile,
    sharedInteriorPair_boundaryZeroKirchhoff_minimalControl_profile⟩

/-- Lab-confirmed boundary-zero-only profile for the wheel-with-inner-triangle shell: all three
interior spokes force zero, while any pair still leaves the third spoke as a nonzero evader. -/
theorem wheelWithInnerTriangle_boundaryZero_minimalControl_profile :
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
      z wit01 = 0 → z wit02 = 0 → z wit03 = 0 → z = 0) ∧
    (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
      z wit01 = 0 ∧ z wit02 = 0 ∧ z wit03 ≠ 0) ∧
    (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
      z wit01 = 0 ∧ z wit03 = 0 ∧ z wit02 ≠ 0) ∧
    (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
      z wit02 = 0 ∧ z wit03 = 0 ∧ z wit01 ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hzBoundary hwit01 hwit02 hwit03
    exact wheelWithInnerTriangle_boundaryZero_no_evader_of_vanishes_on_interiorEdges
      z hzBoundary hwit01 hwit02 hwit03
  · refine ⟨wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader,
      wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader_mem_planarBoundaryZeroSubmodule,
      by simp [wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader],
      by simp [wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader], ?_⟩
    simp [wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader]
  · refine ⟨wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader,
      wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader_mem_planarBoundaryZeroSubmodule,
      by simp [wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader],
      by simp [wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader], ?_⟩
    simp [wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader]
  · refine ⟨wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader,
      wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader_mem_planarBoundaryZeroSubmodule,
      by simp [wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader],
      by simp [wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader], ?_⟩
    simp [wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader]

/-- Lab-confirmed boundary-zero-plus-Kirchhoff profile for the wheel-with-inner-triangle shell:
any pair of spokes forces zero, while any single forced spoke leaves a nonzero Kirchhoff evader. -/
theorem wheelWithInnerTriangle_boundaryZeroKirchhoff_minimalControl_profile :
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
      z wit01 = 0 → z wit02 = 0 → z = 0) ∧
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
      z wit01 = 0 → z wit03 = 0 → z = 0) ∧
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
      z wit02 = 0 → z wit03 = 0 → z = 0) ∧
    (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
      z wit01 = 0 ∧ z ≠ 0) ∧
    (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
      z wit02 = 0 ∧ z ≠ 0) ∧
    (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
      z wit03 = 0 ∧ z ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz hwit01 hwit02
    exact wheelWithInnerTriangle_boundaryZeroKirchhoff_no_evader_of_vanishes_on_wit01_wit02
      z hz hwit01 hwit02
  · intro z hz hwit01 hwit03
    exact wheelWithInnerTriangle_boundaryZeroKirchhoff_no_evader_of_vanishes_on_wit01_wit03
      z hz hwit01 hwit03
  · intro z hz hwit02 hwit03
    exact wheelWithInnerTriangle_boundaryZeroKirchhoff_no_evader_of_vanishes_on_wit02_wit03
      z hz hwit02 hwit03
  · refine ⟨wheelWithInnerTriangleWit01OnlyEvader,
      ⟨wheelWithInnerTriangleWit01OnlyEvader_mem_kirchhoffSubmodule,
        wheelWithInnerTriangleWit01OnlyEvader_mem_planarBoundaryZeroSubmodule⟩,
      by simp [wheelWithInnerTriangleWit01OnlyEvader], ?_⟩
    intro hzero
    have h := congrFun hzero wit02
    simp [wheelWithInnerTriangleWit01OnlyEvader] at h
  · refine ⟨wheelWithInnerTriangleWit02OnlyEvader,
      ⟨wheelWithInnerTriangleWit02OnlyEvader_mem_kirchhoffSubmodule,
        wheelWithInnerTriangleWit02OnlyEvader_mem_planarBoundaryZeroSubmodule⟩,
      by simp [wheelWithInnerTriangleWit02OnlyEvader], ?_⟩
    intro hzero
    have h := congrFun hzero wit01
    simp [wheelWithInnerTriangleWit02OnlyEvader] at h
  · refine ⟨wheelWithInnerTriangleWit03OnlyEvader,
      ⟨wheelWithInnerTriangleWit03OnlyEvader_mem_kirchhoffSubmodule,
        wheelWithInnerTriangleWit03OnlyEvader_mem_planarBoundaryZeroSubmodule⟩,
      by simp [wheelWithInnerTriangleWit03OnlyEvader], ?_⟩
    intro hzero
    have h := congrFun hzero wit01
    simp [wheelWithInnerTriangleWit03OnlyEvader] at h

/-- Combined lab-to-Lean packet for the wheel-with-inner-triangle focus shell.  The shell
satisfies the selected-boundary induced/chord-free carrier condition, and its boundary-zero
detector has the exact minimal-control behavior computed by the F2 lab. -/
theorem wheelWithInnerTriangle_selectedBoundaryInduced_carrier_and_F2MinimalControl_profile :
    SelectedBoundaryInducedSubgraph wheelWithInnerTriangleEmbedding ∧
      InteriorEdgesNotSelectedBoundaryChords wheelWithInnerTriangleEmbedding ∧
      (selectedBoundaryInteriorEdgeEndpointVertices wheelWithInnerTriangleEmbedding).Nonempty ∧
      ((∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        z wit01 = 0 → z wit02 = 0 → z wit03 = 0 → z = 0) ∧
      (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
        z wit01 = 0 ∧ z wit02 = 0 ∧ z wit03 ≠ 0) ∧
      (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
        z wit01 = 0 ∧ z wit03 = 0 ∧ z wit02 ≠ 0) ∧
      (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
        z wit02 = 0 ∧ z wit03 = 0 ∧ z wit01 ≠ 0)) ∧
      ((∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
        z wit01 = 0 → z wit02 = 0 → z = 0) ∧
      (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
        z wit01 = 0 → z wit03 = 0 → z = 0) ∧
      (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
        z wit02 = 0 → z wit03 = 0 → z = 0) ∧
      (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
        z wit01 = 0 ∧ z ≠ 0) ∧
      (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
        z wit02 = 0 ∧ z ≠ 0) ∧
      (∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) ∧
        z wit03 = 0 ∧ z ≠ 0)) :=
  ⟨wheelWithInnerTriangle_selectedBoundaryInducedSubgraph,
    wheelWithInnerTriangle_interiorEdgesNotSelectedBoundaryChords,
    selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle_via_selectedBoundaryInducedSubgraph,
    wheelWithInnerTriangle_boundaryZero_minimalControl_profile,
    wheelWithInnerTriangle_boundaryZeroKirchhoff_minimalControl_profile⟩

/-! ## Focus F2 nonzero-coverage verdicts -/

/--
Shared-interior-pair nonzero-coverage form of the lab verdict.  The declared forced edges
`sip01,sip12` meet every nonzero selected-boundary-zero chain, exactly in the shape consumed by
the CAP5 pairing-kernel shell constructors.
-/
theorem sharedInteriorPair_boundaryZero_declaredForcedEdges_nonzeroCoverage :
    ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
      z ≠ 0 →
        ∃ e : sharedInteriorPairGraph.edgeSet,
          e ∈ sharedInteriorPairInteriorControlEdges ∧ z e ≠ 0 := by
  classical
  intro z hzBoundary hzNonzero
  by_contra hnone
  have hvanish :
      ∀ e ∈ sharedInteriorPairInteriorControlEdges, z e = 0 := by
    intro e he
    by_contra hze
    exact hnone ⟨e, he, hze⟩
  exact hzNonzero
    (sharedInteriorPair_boundaryZero_no_evader_of_controlEdges hzBoundary hvanish)

/--
Wheel-with-inner-triangle nonzero-coverage form of the lab verdict.  All three declared forced
spokes meet every nonzero selected-boundary-zero chain.
-/
theorem wheelWithInnerTriangle_boundaryZero_declaredForcedEdges_nonzeroCoverage :
    ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
      z ≠ 0 →
        ∃ e : wheelWithInnerTriangleGraph.edgeSet,
          e ∈ wheelWithInnerTriangleInteriorControlEdges ∧ z e ≠ 0 := by
  classical
  intro z hzBoundary hzNonzero
  by_contra hnone
  have hvanish :
      ∀ e ∈ wheelWithInnerTriangleInteriorControlEdges, z e = 0 := by
    intro e he
    by_contra hze
    exact hnone ⟨e, he, hze⟩
  exact hzNonzero
    (wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges hzBoundary hvanish)

/--
Two-band nonzero-coverage form of the lab verdict.  The nine interior edges meet every nonzero
selected-boundary-zero chain.
-/
theorem twoBandAnnulus_boundaryZero_declaredForcedEdges_nonzeroCoverage :
    ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
      z ≠ 0 →
        ∃ e : twoBandAnnulusGraph.edgeSet,
          e ∈ twoBandAnnulusInteriorEdges ∧ z e ≠ 0 := by
  classical
  intro z hzBoundary hzNonzero
  by_contra hnone
  have hvanish :
      ∀ e ∈ twoBandAnnulusInteriorEdges, z e = 0 := by
    intro e he
    by_contra hze
    exact hnone ⟨e, he, hze⟩
  exact hzNonzero
    (twoBandAnnulus_boundaryZero_no_evader_of_vanishes_on_interiorEdges
      z hzBoundary hvanish)

/--
Combined finite F2 verdict for the two focus shells.  Declared forced edges catch every nonzero
selected-boundary-zero chain on both shells, while any strictly smaller control set leaves a
nonzero evader.  This is the Lean form of the lab's `synthesis_no_evader` answer for the declared
forced-edge rows, together with the minimality obstruction rows.
-/
theorem focusF2BoundaryZero_declaredForcedEdges_nonzeroCoverage_and_minimality :
    (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
      z ≠ 0 →
        ∃ e : sharedInteriorPairGraph.edgeSet,
          e ∈ sharedInteriorPairInteriorControlEdges ∧ z e ≠ 0) ∧
    (∀ control : Finset sharedInteriorPairGraph.edgeSet,
      control.card < sharedInteriorPairInteriorControlEdges.card →
        ∃ z : sharedInteriorPairGraph.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
            (∀ e ∈ control, z e = 0) ∧ z ≠ 0) ∧
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
      z ≠ 0 →
        ∃ e : wheelWithInnerTriangleGraph.edgeSet,
          e ∈ wheelWithInnerTriangleInteriorControlEdges ∧ z e ≠ 0) ∧
    (∀ control : Finset wheelWithInnerTriangleGraph.edgeSet,
      control.card < wheelWithInnerTriangleInteriorControlEdges.card →
        ∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
            (∀ e ∈ control, z e = 0) ∧ z ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sharedInteriorPair_boundaryZero_declaredForcedEdges_nonzeroCoverage
  · intro control hcard
    exact sharedInteriorPair_boundaryZero_has_evader_of_control_card_lt_two
      control (by simpa [sharedInteriorPairInteriorControlEdges] using hcard)
  · exact wheelWithInnerTriangle_boundaryZero_declaredForcedEdges_nonzeroCoverage
  · intro control hcard
    exact wheelWithInnerTriangle_boundaryZero_has_evader_of_control_card_lt_three
      control (by simpa [wheelWithInnerTriangleInteriorControlEdges] using hcard)

/-! ## Focus F2 verdicts as shell and synthesis producers -/

/--
Closed-walk shell producer for the shared-interior-pair focus verdict.  Once a concrete generator
family supplies red and blue probes on the declared forced edges, the finite nonzero-coverage
certificate is exactly a pairing-kernel shell.
-/
noncomputable def sharedInteriorPair_closedWalkNeighborhoodPairingKernelShell_of_declaredForcedEdgeWitnesses
    (shell : ClosedWalkExactShell sharedInteriorPairEmbedding)
    (colorings : Set (sharedInteriorPairGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ sharedInteriorPairGraph.EdgeKempeClosure shell.tait.coloring)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings)
    (hwitnessRed :
      ∀ e ∈ sharedInteriorPairInteriorControlEdges,
        ∃ i : κ,
          ((family i :
              projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings) :
              sharedInteriorPairGraph.edgeSet → Color) =
            Pi.single e red)
    (hwitnessBlue :
      ∀ e ∈ sharedInteriorPairInteriorControlEdges,
        ∃ i : κ,
          ((family i :
              projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings) :
              sharedInteriorPairGraph.edgeSet → Color) =
            Pi.single e blue) :
    ClosedWalkNeighborhoodPairingKernelShell sharedInteriorPairEmbedding :=
  ClosedWalkNeighborhoodPairingKernelShell.of_controlEdgeNonzeroWitnesses
    shell colorings hsubset family sharedInteriorPairInteriorControlEdges
    sharedInteriorPair_boundaryZero_declaredForcedEdges_nonzeroCoverage
    hwitnessRed hwitnessBlue

/-- Boundary-root synthesis form of the shared-interior-pair focus F₂ verdict. -/
theorem sharedInteriorPair_theorem49BoundaryRootSynthesis_of_declaredForcedEdgeWitnesses
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (colorings : Set (sharedInteriorPairGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ sharedInteriorPairGraph.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings)
    (hwitnessRed :
      ∀ e ∈ sharedInteriorPairInteriorControlEdges,
        ∃ i : κ,
          ((family i :
              projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings) :
              sharedInteriorPairGraph.edgeSet → Color) =
            Pi.single e red)
    (hwitnessBlue :
      ∀ e ∈ sharedInteriorPairInteriorControlEdges,
        ∃ i : κ,
          ((family i :
              projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings) :
              sharedInteriorPairGraph.edgeSet → Color) =
            Pi.single e blue) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀ :=
  theorem49BoundaryRootSynthesis_of_controlEdgeNonzeroWitnesses
    sharedInteriorPairEmbedding C₀ colorings hsubset family
    sharedInteriorPairInteriorControlEdges
    sharedInteriorPair_boundaryZero_declaredForcedEdges_nonzeroCoverage
    hwitnessRed hwitnessBlue

instance sharedInteriorPairGraph_lineGraph_adj_decidable :
    DecidableRel sharedInteriorPairGraph.lineGraph.Adj := by
  intro e f
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  infer_instance

def sharedInteriorPairCertificateColorA
    (e : sharedInteriorPairGraph.edgeSet) : Color :=
  if e = sip01 ∨ e = sip23 ∨ e = sip56 then red
  else if e = sip12 ∨ e = sip40 ∨ e = sip67 then blue
  else purple

def sharedInteriorPairCertificateColorB
    (e : sharedInteriorPairGraph.edgeSet) : Color :=
  if e = sip12 ∨ e = sip40 ∨ e = sip56 then red
  else if e = sip01 ∨ e = sip23 ∨ e = sip67 then blue
  else purple

theorem sharedInteriorPairCertificateColorA_ne_of_adj
    {e f : sharedInteriorPairGraph.edgeSet}
    (hadj : sharedInteriorPairGraph.lineGraph.Adj e f) :
    sharedInteriorPairCertificateColorA e ≠ sharedInteriorPairCertificateColorA f := by
  decide +revert

theorem sharedInteriorPairCertificateColorB_ne_of_adj
    {e f : sharedInteriorPairGraph.edgeSet}
    (hadj : sharedInteriorPairGraph.lineGraph.Adj e f) :
    sharedInteriorPairCertificateColorB e ≠ sharedInteriorPairCertificateColorB f := by
  decide +revert

def sharedInteriorPairCertificateColoringA :
    sharedInteriorPairGraph.EdgeColoring Color :=
  Coloring.mk sharedInteriorPairCertificateColorA (by
    intro e f hadj
    exact sharedInteriorPairCertificateColorA_ne_of_adj hadj)

def sharedInteriorPairCertificateColoringB :
    sharedInteriorPairGraph.EdgeColoring Color :=
  Coloring.mk sharedInteriorPairCertificateColorB (by
    intro e f hadj
    exact sharedInteriorPairCertificateColorB_ne_of_adj hadj)

@[simp] theorem sharedInteriorPairCertificateColoringA_apply
    (e : sharedInteriorPairGraph.edgeSet) :
    sharedInteriorPairCertificateColoringA e =
      sharedInteriorPairCertificateColorA e := rfl

@[simp] theorem sharedInteriorPairCertificateColoringB_apply
    (e : sharedInteriorPairGraph.edgeSet) :
    sharedInteriorPairCertificateColoringB e =
      sharedInteriorPairCertificateColorB e := rfl

def sharedInteriorPairProjectedGeneratorCertificateColorings :
    Set (sharedInteriorPairGraph.EdgeColoring Color) :=
  {C | C = sharedInteriorPairCertificateColoringA ∨
      C = sharedInteriorPairCertificateColoringB}

private theorem sharedInteriorPairCertificateColoringA_unique_sip01_redPurple :
    ∀ e : sharedInteriorPairGraph.edgeSet,
      e ≠ sip01 →
      e ∉ selectedBoundarySupport
        sharedInteriorPairEmbedding.faceBoundary
        sharedInteriorPairEmbedding.faces
        sharedInteriorPairEmbedding.faces →
      e ∈ sharedInteriorPairEmbedding.faceBoundary (0 : Fin 3) →
        ¬ (sharedInteriorPairCertificateColoringA e = red ∨
          sharedInteriorPairCertificateColoringA e = purple) := by
  intro e hne hnotBoundary hface
  rw [sharedInteriorPair_selectedBoundarySupport_eq] at hnotBoundary
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairEmbedding, sharedInteriorPairFaceBoundary,
      sharedInteriorPairCertificateColorA] at hne hnotBoundary hface ⊢;
    decide

private theorem sharedInteriorPairCertificateColoringA_unique_sip12_bluePurple :
    ∀ e : sharedInteriorPairGraph.edgeSet,
      e ≠ sip12 →
      e ∉ selectedBoundarySupport
        sharedInteriorPairEmbedding.faceBoundary
        sharedInteriorPairEmbedding.faces
        sharedInteriorPairEmbedding.faces →
      e ∈ sharedInteriorPairEmbedding.faceBoundary (0 : Fin 3) →
        ¬ (sharedInteriorPairCertificateColoringA e = blue ∨
          sharedInteriorPairCertificateColoringA e = purple) := by
  intro e hne hnotBoundary hface
  rw [sharedInteriorPair_selectedBoundarySupport_eq] at hnotBoundary
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairEmbedding, sharedInteriorPairFaceBoundary,
      sharedInteriorPairCertificateColorA] at hne hnotBoundary hface ⊢

private theorem sharedInteriorPairCertificateColoringB_unique_sip01_bluePurple :
    ∀ e : sharedInteriorPairGraph.edgeSet,
      e ≠ sip01 →
      e ∉ selectedBoundarySupport
        sharedInteriorPairEmbedding.faceBoundary
        sharedInteriorPairEmbedding.faces
        sharedInteriorPairEmbedding.faces →
      e ∈ sharedInteriorPairEmbedding.faceBoundary (0 : Fin 3) →
        ¬ (sharedInteriorPairCertificateColoringB e = blue ∨
          sharedInteriorPairCertificateColoringB e = purple) := by
  intro e hne hnotBoundary hface
  rw [sharedInteriorPair_selectedBoundarySupport_eq] at hnotBoundary
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairEmbedding, sharedInteriorPairFaceBoundary,
      sharedInteriorPairCertificateColorB] at hne hnotBoundary hface ⊢

private theorem sharedInteriorPairCertificateColoringB_unique_sip12_redPurple :
    ∀ e : sharedInteriorPairGraph.edgeSet,
      e ≠ sip12 →
      e ∉ selectedBoundarySupport
        sharedInteriorPairEmbedding.faceBoundary
        sharedInteriorPairEmbedding.faces
        sharedInteriorPairEmbedding.faces →
      e ∈ sharedInteriorPairEmbedding.faceBoundary (0 : Fin 3) →
        ¬ (sharedInteriorPairCertificateColoringB e = red ∨
          sharedInteriorPairCertificateColoringB e = purple) := by
  intro e hne hnotBoundary hface
  rw [sharedInteriorPair_selectedBoundarySupport_eq] at hnotBoundary
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairEmbedding, sharedInteriorPairFaceBoundary,
      sharedInteriorPairCertificateColorB] at hne hnotBoundary hface ⊢;
    decide

theorem sharedInteriorPair_uniqueProjectedBicoloredCertificates :
    (∀ e ∈ sharedInteriorPairInteriorControlEdges,
      ∃ C ∈ sharedInteriorPairProjectedGeneratorCertificateColorings,
        ∃ f : sharedInteriorPairEmbedding.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            a + b = red ∧
              e ∈ sharedInteriorPairEmbedding.faceBoundary f ∧
                e ∉ selectedBoundarySupport
                  sharedInteriorPairEmbedding.faceBoundary
                  sharedInteriorPairEmbedding.faces
                  sharedInteriorPairEmbedding.faces ∧
                  (C e = a ∨ C e = b) ∧
                    ∀ e' : sharedInteriorPairGraph.edgeSet,
                      e' ≠ e →
                      e' ∉ selectedBoundarySupport
                        sharedInteriorPairEmbedding.faceBoundary
                        sharedInteriorPairEmbedding.faces
                        sharedInteriorPairEmbedding.faces →
                      e' ∈ sharedInteriorPairEmbedding.faceBoundary f →
                        ¬ (C e' = a ∨ C e' = b)) ∧
    (∀ e ∈ sharedInteriorPairInteriorControlEdges,
      ∃ C ∈ sharedInteriorPairProjectedGeneratorCertificateColorings,
        ∃ f : sharedInteriorPairEmbedding.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            a + b = blue ∧
              e ∈ sharedInteriorPairEmbedding.faceBoundary f ∧
                e ∉ selectedBoundarySupport
                  sharedInteriorPairEmbedding.faceBoundary
                  sharedInteriorPairEmbedding.faces
                  sharedInteriorPairEmbedding.faces ∧
                  (C e = a ∨ C e = b) ∧
                    ∀ e' : sharedInteriorPairGraph.edgeSet,
                      e' ≠ e →
                      e' ∉ selectedBoundarySupport
                        sharedInteriorPairEmbedding.faceBoundary
                        sharedInteriorPairEmbedding.faces
                        sharedInteriorPairEmbedding.faces →
                      e' ∈ sharedInteriorPairEmbedding.faceBoundary f →
                        ¬ (C e' = a ∨ C e' = b)) := by
  constructor
  · intro e he
    have heCases : e = sip01 ∨ e = sip12 := by
      simpa [sharedInteriorPairInteriorControlEdges] using he
    rcases heCases with rfl | rfl
    · refine ⟨sharedInteriorPairCertificateColoringB, Or.inr rfl,
        (0 : Fin 3), blue, purple, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [ValidColorPair]
      · simp
      · decide
      · exact sip01_not_mem_selectedBoundarySupport
      · left
        simp [sharedInteriorPairCertificateColorB]
        decide
      · exact sharedInteriorPairCertificateColoringB_unique_sip01_bluePurple
    · refine ⟨sharedInteriorPairCertificateColoringA, Or.inl rfl,
        (0 : Fin 3), blue, purple, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [ValidColorPair]
      · simp
      · decide
      · exact sip12_not_mem_selectedBoundarySupport
      · left
        simp [sharedInteriorPairCertificateColorA]
        decide
      · exact sharedInteriorPairCertificateColoringA_unique_sip12_bluePurple
  · intro e he
    have heCases : e = sip01 ∨ e = sip12 := by
      simpa [sharedInteriorPairInteriorControlEdges] using he
    rcases heCases with rfl | rfl
    · refine ⟨sharedInteriorPairCertificateColoringA, Or.inl rfl,
        (0 : Fin 3), red, purple, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [ValidColorPair]
      · simp
      · decide
      · exact sip01_not_mem_selectedBoundarySupport
      · left
        simp [sharedInteriorPairCertificateColorA]
      · exact sharedInteriorPairCertificateColoringA_unique_sip01_redPurple
    · refine ⟨sharedInteriorPairCertificateColoringB, Or.inr rfl,
        (0 : Fin 3), red, purple, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [ValidColorPair]
      · simp
      · decide
      · exact sip12_not_mem_selectedBoundarySupport
      · left
        simp [sharedInteriorPairCertificateColorB]
      · exact sharedInteriorPairCertificateColoringB_unique_sip12_redPurple

theorem sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates :
    (∀ e ∈ sharedInteriorPairInteriorControlEdges,
        Pi.single e red ∈
          projectedColoringGeneratorSubspace sharedInteriorPairEmbedding
            sharedInteriorPairProjectedGeneratorCertificateColorings) ∧
      (∀ e ∈ sharedInteriorPairInteriorControlEdges,
        Pi.single e blue ∈
          projectedColoringGeneratorSubspace sharedInteriorPairEmbedding
            sharedInteriorPairProjectedGeneratorCertificateColorings) :=
  redBlueSingleCoordinateMemberships_of_uniqueProjectedBicoloredCertificates
    sharedInteriorPairInteriorControlEdges
    sharedInteriorPair_uniqueProjectedBicoloredCertificates.1
    sharedInteriorPair_uniqueProjectedBicoloredCertificates.2

/-- Boundary-root synthesis from the explicit shared-interior-pair certificate family.  The
finite F2 verdict supplies complete nonzero coverage on the two shared interior controls, and
the unique projected-bicolored certificates supply both red and blue probes there. -/
theorem sharedInteriorPair_theorem49BoundaryRootSynthesis_of_uniqueCertificates
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (hsubset :
      sharedInteriorPairProjectedGeneratorCertificateColorings ⊆
        sharedInteriorPairGraph.EdgeKempeClosure C₀) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀ :=
  theorem49BoundaryRootSynthesis_of_redBlueSingleCoordinateMemberships
    sharedInteriorPairEmbedding C₀ sharedInteriorPairProjectedGeneratorCertificateColorings
    hsubset sharedInteriorPairInteriorControlEdges
    sharedInteriorPair_boundaryZero_controlEdges_interiorEdges
    sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
    sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2

private def sharedInteriorPairOuterEdgeRegion (e : sharedInteriorPairGraph.edgeSet) : Bool :=
  if e = sip56 ∨ e = sip67 ∨ e = sip75 then true else false

private theorem sharedInteriorPairOuterEdgeRegion_eq_of_lineGraph_adj
    {e f : sharedInteriorPairGraph.edgeSet}
    (hadj : sharedInteriorPairGraph.lineGraph.Adj e f) :
    sharedInteriorPairOuterEdgeRegion e = sharedInteriorPairOuterEdgeRegion f := by
  decide +revert

private theorem sharedInteriorPairOuterEdgeRegion_eq_of_bicoloredWalk
    {a b : Color}
    {C : sharedInteriorPairGraph.EdgeColoring Color}
    {u v : ↥(C.bicoloredSet a b)}
    (p : (C.bicoloredSubgraph a b).Walk u v) :
    sharedInteriorPairOuterEdgeRegion u.1 = sharedInteriorPairOuterEdgeRegion v.1 := by
  induction p with
  | nil => rfl
  | cons hadj p ih =>
      exact (sharedInteriorPairOuterEdgeRegion_eq_of_lineGraph_adj (by simpa using hadj)).trans ih

private theorem sharedInteriorPairOuterEdgeRegion_eq_of_bicoloredReachable
    {a b : Color}
    {C : sharedInteriorPairGraph.EdgeColoring Color}
    {e f : sharedInteriorPairGraph.edgeSet}
    {he : e ∈ C.bicoloredSet a b} {hf : f ∈ C.bicoloredSet a b}
    (hreach : (C.bicoloredSubgraph a b).Reachable ⟨e, he⟩ ⟨f, hf⟩) :
    sharedInteriorPairOuterEdgeRegion e = sharedInteriorPairOuterEdgeRegion f := by
  refine hreach.elim ?_
  intro p
  exact sharedInteriorPairOuterEdgeRegion_eq_of_bicoloredWalk p

private theorem sharedInteriorPair_not_mem_kempeComponentSet_of_ne_left_ne_right
    {x y : Color}
    {C : sharedInteriorPairGraph.EdgeColoring Color}
    {K : (C.bicoloredSubgraph x y).ConnectedComponent}
    {e : sharedInteriorPairGraph.edgeSet}
    (hx : C e ≠ x) (hy : C e ≠ y) :
    e ∉ C.kempeComponentSet x y K := by
  intro hmem
  rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hmem with h | h
  · exact hx h
  · exact hy h

private theorem sharedInteriorPair_not_mem_component_containing_sip01_of_outerRegion_true
    {x y : Color}
    {C : sharedInteriorPairGraph.EdgeColoring Color}
    {K : (C.bicoloredSubgraph x y).ConnectedComponent}
    {e : sharedInteriorPairGraph.edgeSet}
    (h01 : sip01 ∈ C.kempeComponentSet x y K)
    (hregion : sharedInteriorPairOuterEdgeRegion e = true) :
    e ∉ C.kempeComponentSet x y K := by
  intro hmem
  rcases hmem with ⟨he', hec⟩
  rcases h01 with ⟨h01', h01c⟩
  have hcomp' :
      (C.bicoloredSubgraph x y).connectedComponentMk ⟨e, he'⟩ =
      (C.bicoloredSubgraph x y).connectedComponentMk ⟨sip01, h01'⟩ :=
    hec.trans h01c.symm
  have hreach : (C.bicoloredSubgraph x y).Reachable ⟨e, he'⟩ ⟨sip01, h01'⟩ :=
    ConnectedComponent.eq.mp hcomp'
  have hregion' := sharedInteriorPairOuterEdgeRegion_eq_of_bicoloredReachable hreach
  have hsip01 : sharedInteriorPairOuterEdgeRegion sip01 = false := by decide
  rw [hregion, hsip01] at hregion'
  cases hregion'

private theorem sharedInteriorPairCertificateColoringA_sip01_mem_bicoloredSet_red_blue :
    sip01 ∈ sharedInteriorPairCertificateColoringA.bicoloredSet red blue := by
  left
  simp [sharedInteriorPairCertificateColorA]

private noncomputable def sharedInteriorPairCertificateColoringA_redBlueComponent :
    (sharedInteriorPairCertificateColoringA.bicoloredSubgraph red blue).ConnectedComponent :=
  (sharedInteriorPairCertificateColoringA.bicoloredSubgraph red blue).connectedComponentMk
    ⟨sip01, sharedInteriorPairCertificateColoringA_sip01_mem_bicoloredSet_red_blue⟩

private theorem sip01_mem_sharedInteriorPairCertificateColoringA_redBlueComponent :
    sip01 ∈ sharedInteriorPairCertificateColoringA.kempeComponentSet red blue
      sharedInteriorPairCertificateColoringA_redBlueComponent := by
  exact sharedInteriorPairCertificateColoringA.mem_kempeComponentSet_self
    sharedInteriorPairCertificateColoringA_sip01_mem_bicoloredSet_red_blue

private theorem sip12_mem_sharedInteriorPairCertificateColoringA_redBlueComponent :
    sip12 ∈ sharedInteriorPairCertificateColoringA.kempeComponentSet red blue
      sharedInteriorPairCertificateColoringA_redBlueComponent := by
  exact sharedInteriorPairCertificateColoringA.mem_kempeComponentSet_of_adj
    sip01_mem_sharedInteriorPairCertificateColoringA_redBlueComponent (by decide) (by
      right
      simp [sharedInteriorPairCertificateColorA]
      decide)

private theorem sip23_mem_sharedInteriorPairCertificateColoringA_redBlueComponent :
    sip23 ∈ sharedInteriorPairCertificateColoringA.kempeComponentSet red blue
      sharedInteriorPairCertificateColoringA_redBlueComponent := by
  exact sharedInteriorPairCertificateColoringA.mem_kempeComponentSet_of_adj
    sip12_mem_sharedInteriorPairCertificateColoringA_redBlueComponent (by decide) (by
      left
      simp [sharedInteriorPairCertificateColorA])

private theorem sip40_mem_sharedInteriorPairCertificateColoringA_redBlueComponent :
    sip40 ∈ sharedInteriorPairCertificateColoringA.kempeComponentSet red blue
      sharedInteriorPairCertificateColoringA_redBlueComponent := by
  exact sharedInteriorPairCertificateColoringA.mem_kempeComponentSet_of_adj
    sip01_mem_sharedInteriorPairCertificateColoringA_redBlueComponent (by decide) (by
      right
      simp [sharedInteriorPairCertificateColorA]
      decide)

private theorem sip30_not_mem_sharedInteriorPairCertificateColoringA_redBlueComponent :
    sip30 ∉ sharedInteriorPairCertificateColoringA.kempeComponentSet red blue
      sharedInteriorPairCertificateColoringA_redBlueComponent := by
  exact sharedInteriorPair_not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := sharedInteriorPairCertificateColoringA)
    (K := sharedInteriorPairCertificateColoringA_redBlueComponent)
    (e := sip30)
    (by simp [sharedInteriorPairCertificateColorA]; decide)
    (by simp [sharedInteriorPairCertificateColorA]; decide)

private theorem sip24_not_mem_sharedInteriorPairCertificateColoringA_redBlueComponent :
    sip24 ∉ sharedInteriorPairCertificateColoringA.kempeComponentSet red blue
      sharedInteriorPairCertificateColoringA_redBlueComponent := by
  exact sharedInteriorPair_not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := sharedInteriorPairCertificateColoringA)
    (K := sharedInteriorPairCertificateColoringA_redBlueComponent)
    (e := sip24)
    (by simp [sharedInteriorPairCertificateColorA]; decide)
    (by simp [sharedInteriorPairCertificateColorA]; decide)

private theorem sip75_not_mem_sharedInteriorPairCertificateColoringA_redBlueComponent :
    sip75 ∉ sharedInteriorPairCertificateColoringA.kempeComponentSet red blue
      sharedInteriorPairCertificateColoringA_redBlueComponent := by
  exact sharedInteriorPair_not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := sharedInteriorPairCertificateColoringA)
    (K := sharedInteriorPairCertificateColoringA_redBlueComponent)
    (e := sip75)
    (by simp [sharedInteriorPairCertificateColorA]; decide)
    (by simp [sharedInteriorPairCertificateColorA]; decide)

private theorem sip56_not_mem_sharedInteriorPairCertificateColoringA_redBlueComponent :
    sip56 ∉ sharedInteriorPairCertificateColoringA.kempeComponentSet red blue
      sharedInteriorPairCertificateColoringA_redBlueComponent := by
  exact sharedInteriorPair_not_mem_component_containing_sip01_of_outerRegion_true
    sip01_mem_sharedInteriorPairCertificateColoringA_redBlueComponent (by decide)

private theorem sip67_not_mem_sharedInteriorPairCertificateColoringA_redBlueComponent :
    sip67 ∉ sharedInteriorPairCertificateColoringA.kempeComponentSet red blue
      sharedInteriorPairCertificateColoringA_redBlueComponent := by
  exact sharedInteriorPair_not_mem_component_containing_sip01_of_outerRegion_true
    sip01_mem_sharedInteriorPairCertificateColoringA_redBlueComponent (by decide)

private theorem sharedInteriorPairCertificateColoringA_swap_redBlueComponent_eq_B :
    sharedInteriorPairCertificateColoringA.swapOnKempeComponent red blue
        sharedInteriorPairCertificateColoringA_redBlueComponent =
      sharedInteriorPairCertificateColoringB := by
  apply DFunLike.ext
  intro e
  rcases sharedInteriorPair_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · simp [sharedInteriorPairCertificateColorA, sharedInteriorPairCertificateColorB]
      decide
    · exact sip01_mem_sharedInteriorPairCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · simp [sharedInteriorPairCertificateColorA, sharedInteriorPairCertificateColorB]
      decide
    · exact sip12_mem_sharedInteriorPairCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · simp [sharedInteriorPairCertificateColorA, sharedInteriorPairCertificateColorB]
      decide
    · exact sip23_mem_sharedInteriorPairCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · simp [sharedInteriorPairCertificateColorA, sharedInteriorPairCertificateColorB]
      decide
    · exact sip30_not_mem_sharedInteriorPairCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · simp [sharedInteriorPairCertificateColorA, sharedInteriorPairCertificateColorB]
      decide
    · exact sip24_not_mem_sharedInteriorPairCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · simp [sharedInteriorPairCertificateColorA, sharedInteriorPairCertificateColorB]
      decide
    · exact sip40_mem_sharedInteriorPairCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · simp [sharedInteriorPairCertificateColorA, sharedInteriorPairCertificateColorB]
    · exact sip56_not_mem_sharedInteriorPairCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · simp [sharedInteriorPairCertificateColorA, sharedInteriorPairCertificateColorB]
      decide
    · exact sip67_not_mem_sharedInteriorPairCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · simp [sharedInteriorPairCertificateColorA, sharedInteriorPairCertificateColorB]
      decide
    · exact sip75_not_mem_sharedInteriorPairCertificateColoringA_redBlueComponent

theorem sharedInteriorPairCertificateColoringB_mem_edgeKempeClosure_certificateColoringA :
    sharedInteriorPairCertificateColoringB ∈
      sharedInteriorPairGraph.EdgeKempeClosure sharedInteriorPairCertificateColoringA := by
  rw [← sharedInteriorPairCertificateColoringA_swap_redBlueComponent_eq_B]
  exact sharedInteriorPairGraph.mem_edgeKempeClosure_of_mem_of_step
    (sharedInteriorPairGraph.mem_edgeKempeClosure_self sharedInteriorPairCertificateColoringA)
    red blue sharedInteriorPairCertificateColoringA_redBlueComponent

theorem sharedInteriorPairProjectedGeneratorCertificateColorings_subset_edgeKempeClosure_certificateColoringA :
    sharedInteriorPairProjectedGeneratorCertificateColorings ⊆
      sharedInteriorPairGraph.EdgeKempeClosure sharedInteriorPairCertificateColoringA := by
  intro C hC
  rcases hC with rfl | rfl
  · exact sharedInteriorPairGraph.mem_edgeKempeClosure_self sharedInteriorPairCertificateColoringA
  · exact sharedInteriorPairCertificateColoringB_mem_edgeKempeClosure_certificateColoringA

/-- Boundary-root synthesis for the shared shell using certificate A as the root.  The second
certificate is reached from A by one red/blue Kempe swap on the component through `sip01`. -/
theorem sharedInteriorPair_theorem49BoundaryRootSynthesis_certificateColoringA
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)] :
    Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding
      sharedInteriorPairCertificateColoringA :=
  sharedInteriorPair_theorem49BoundaryRootSynthesis_of_uniqueCertificates
    sharedInteriorPairCertificateColoringA
    sharedInteriorPairProjectedGeneratorCertificateColorings_subset_edgeKempeClosure_certificateColoringA

theorem sharedInteriorPair_boundaryZeroProjectedColoringGeneratorDetector_of_uniqueCertificates :
    BoundaryZeroProjectedColoringGeneratorDetector sharedInteriorPairEmbedding
      sharedInteriorPairProjectedGeneratorCertificateColorings := by
  exact
    BoundaryZeroProjectedColoringGeneratorDetector.of_uniqueProjectedBicoloredCertificates
      sharedInteriorPairInteriorControlEdges
      sharedInteriorPair_boundaryZero_controlEdges_interiorEdges
      sharedInteriorPair_uniqueProjectedBicoloredCertificates.1
      sharedInteriorPair_uniqueProjectedBicoloredCertificates.2

/-- Canonical finite family for the shared focus shell: red and blue single-coordinate probes on
the two lab-certified controlling edges, realized by the unique projected-bicolored certificate
colorings. -/
noncomputable def sharedInteriorPairUniqueCertificateRedBlueFamily :
    ({e : sharedInteriorPairGraph.edgeSet // e ∈ sharedInteriorPairInteriorControlEdges} × Bool) →
      projectedColoringGeneratorSubspace sharedInteriorPairEmbedding
        sharedInteriorPairProjectedGeneratorCertificateColorings :=
  redBlueSingleCoordinateFamily sharedInteriorPairInteriorControlEdges
    sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
    sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2

/-- Family-pairing kernel form of the shared focus-shell F₂ verdict.  The canonical red/blue
certificate family has trivial selected-boundary-zero pairing kernel. -/
theorem sharedInteriorPair_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificateRedBlueFamily_eq_bot :
    LinearMap.ker
        (planarBoundaryZeroFamilyPairingMap
          sharedInteriorPairUniqueCertificateRedBlueFamily) = ⊥ :=
  ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_edgePredicateNonzeroWitnesses
    sharedInteriorPairUniqueCertificateRedBlueFamily
    (fun e => e ∈ sharedInteriorPairInteriorControlEdges)
    sharedInteriorPair_boundaryZero_declaredForcedEdges_nonzeroCoverage
    (redBlueSingleCoordinateFamily_witnessRed sharedInteriorPairInteriorControlEdges
      sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
      sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2)
    (redBlueSingleCoordinateFamily_witnessBlue sharedInteriorPairInteriorControlEdges
      sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
      sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2)

/-- Projected-face-generator certificate form of the shared-interior-pair focus verdict.  This
is the direct active Lean consumer for finite-lab certificates saying that the red and blue
single-coordinate probes on the declared forced edges are literal projected face generators. -/
theorem sharedInteriorPair_boundaryZeroProjectedColoringGeneratorDetector_of_projectedFaceGeneratorEqualities
    (colorings : Set (sharedInteriorPairGraph.EdgeColoring Color))
    (hred :
      ∀ e ∈ sharedInteriorPairInteriorControlEdges,
        ∃ C ∈ colorings, ∃ f : sharedInteriorPairEmbedding.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            boundaryZeroProjection
                (selectedBoundarySupport
                  sharedInteriorPairEmbedding.faceBoundary
                  sharedInteriorPairEmbedding.faces
                  sharedInteriorPairEmbedding.faces)
                (polarizedFaceGenerator C a b
                  (sharedInteriorPairEmbedding.faceBoundary f)) =
              Pi.single e red)
    (hblue :
      ∀ e ∈ sharedInteriorPairInteriorControlEdges,
        ∃ C ∈ colorings, ∃ f : sharedInteriorPairEmbedding.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            boundaryZeroProjection
                (selectedBoundarySupport
                  sharedInteriorPairEmbedding.faceBoundary
                  sharedInteriorPairEmbedding.faces
                  sharedInteriorPairEmbedding.faces)
                (polarizedFaceGenerator C a b
                  (sharedInteriorPairEmbedding.faceBoundary f)) =
              Pi.single e blue) :
    BoundaryZeroProjectedColoringGeneratorDetector sharedInteriorPairEmbedding colorings :=
  BoundaryZeroProjectedColoringGeneratorDetector.of_projectedFaceGeneratorEqualities
    sharedInteriorPairInteriorControlEdges
    sharedInteriorPair_boundaryZero_controlEdges_interiorEdges
    hred hblue

/-- Boundary-root synthesis form for shared-interior-pair projected-face-generator certificates. -/
theorem sharedInteriorPair_theorem49BoundaryRootSynthesis_of_projectedFaceGeneratorEqualities
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (colorings : Set (sharedInteriorPairGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ sharedInteriorPairGraph.EdgeKempeClosure C₀)
    (hred :
      ∀ e ∈ sharedInteriorPairInteriorControlEdges,
        ∃ C ∈ colorings, ∃ f : sharedInteriorPairEmbedding.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            boundaryZeroProjection
                (selectedBoundarySupport
                  sharedInteriorPairEmbedding.faceBoundary
                  sharedInteriorPairEmbedding.faces
                  sharedInteriorPairEmbedding.faces)
                (polarizedFaceGenerator C a b
                  (sharedInteriorPairEmbedding.faceBoundary f)) =
              Pi.single e red)
    (hblue :
      ∀ e ∈ sharedInteriorPairInteriorControlEdges,
        ∃ C ∈ colorings, ∃ f : sharedInteriorPairEmbedding.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            boundaryZeroProjection
                (selectedBoundarySupport
                  sharedInteriorPairEmbedding.faceBoundary
                  sharedInteriorPairEmbedding.faces
                  sharedInteriorPairEmbedding.faces)
                (polarizedFaceGenerator C a b
                  (sharedInteriorPairEmbedding.faceBoundary f)) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀ :=
  theorem49BoundaryRootSynthesis_of_projectedFaceGeneratorEqualities
    sharedInteriorPairEmbedding C₀ colorings hsubset
    sharedInteriorPairInteriorControlEdges
    sharedInteriorPair_boundaryZero_controlEdges_interiorEdges
    hred hblue

/--
Closed-walk shell producer for the wheel-with-inner-triangle focus verdict.  The three declared
spokes are a complete finite nonzero-coverage set for selected-boundary-zero chains.
-/
noncomputable def wheelWithInnerTriangle_closedWalkNeighborhoodPairingKernelShell_of_declaredForcedEdgeWitnesses
    (shell : ClosedWalkExactShell wheelWithInnerTriangleEmbedding)
    (colorings : Set (wheelWithInnerTriangleGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ wheelWithInnerTriangleGraph.EdgeKempeClosure shell.tait.coloring)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings)
    (hwitnessRed :
      ∀ e ∈ wheelWithInnerTriangleInteriorControlEdges,
        ∃ i : κ,
          ((family i :
              projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings) :
              wheelWithInnerTriangleGraph.edgeSet → Color) =
            Pi.single e red)
    (hwitnessBlue :
      ∀ e ∈ wheelWithInnerTriangleInteriorControlEdges,
        ∃ i : κ,
          ((family i :
              projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings) :
              wheelWithInnerTriangleGraph.edgeSet → Color) =
            Pi.single e blue) :
    ClosedWalkNeighborhoodPairingKernelShell wheelWithInnerTriangleEmbedding :=
  ClosedWalkNeighborhoodPairingKernelShell.of_controlEdgeNonzeroWitnesses
    shell colorings hsubset family wheelWithInnerTriangleInteriorControlEdges
    wheelWithInnerTriangle_boundaryZero_declaredForcedEdges_nonzeroCoverage
    hwitnessRed hwitnessBlue

/-- Boundary-root synthesis form of the wheel-with-inner-triangle focus F₂ verdict. -/
theorem wheelWithInnerTriangle_theorem49BoundaryRootSynthesis_of_declaredForcedEdgeWitnesses
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (colorings : Set (wheelWithInnerTriangleGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings)
    (hwitnessRed :
      ∀ e ∈ wheelWithInnerTriangleInteriorControlEdges,
        ∃ i : κ,
          ((family i :
              projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings) :
              wheelWithInnerTriangleGraph.edgeSet → Color) =
            Pi.single e red)
    (hwitnessBlue :
      ∀ e ∈ wheelWithInnerTriangleInteriorControlEdges,
        ∃ i : κ,
          ((family i :
              projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings) :
              wheelWithInnerTriangleGraph.edgeSet → Color) =
            Pi.single e blue) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀ :=
  theorem49BoundaryRootSynthesis_of_controlEdgeNonzeroWitnesses
    wheelWithInnerTriangleEmbedding C₀ colorings hsubset family
    wheelWithInnerTriangleInteriorControlEdges
    wheelWithInnerTriangle_boundaryZero_declaredForcedEdges_nonzeroCoverage
    hwitnessRed hwitnessBlue

instance wheelWithInnerTriangleGraph_lineGraph_adj_decidable :
    DecidableRel wheelWithInnerTriangleGraph.lineGraph.Adj := by
  intro e f
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  infer_instance

def wheelWithInnerTriangleCertificateColorA
    (e : wheelWithInnerTriangleGraph.edgeSet) : Color :=
  if e = wit01 ∨ e = wit23 ∨ e = wit45 then red
  else if e = wit02 ∨ e = wit31 ∨ e = wit56 then blue
  else purple

def wheelWithInnerTriangleCertificateColorB
    (e : wheelWithInnerTriangleGraph.edgeSet) : Color :=
  if e = wit02 ∨ e = wit31 ∨ e = wit45 then red
  else if e = wit01 ∨ e = wit23 ∨ e = wit56 then blue
  else purple

def wheelWithInnerTriangleCertificateColorC
    (e : wheelWithInnerTriangleGraph.edgeSet) : Color :=
  if e = wit01 ∨ e = wit23 ∨ e = wit45 then red
  else if e = wit03 ∨ e = wit12 ∨ e = wit56 then blue
  else purple

theorem wheelWithInnerTriangleCertificateColorA_ne_of_adj
    {e f : wheelWithInnerTriangleGraph.edgeSet}
    (hadj : wheelWithInnerTriangleGraph.lineGraph.Adj e f) :
    wheelWithInnerTriangleCertificateColorA e ≠
      wheelWithInnerTriangleCertificateColorA f := by
  decide +revert

theorem wheelWithInnerTriangleCertificateColorB_ne_of_adj
    {e f : wheelWithInnerTriangleGraph.edgeSet}
    (hadj : wheelWithInnerTriangleGraph.lineGraph.Adj e f) :
    wheelWithInnerTriangleCertificateColorB e ≠
      wheelWithInnerTriangleCertificateColorB f := by
  decide +revert

theorem wheelWithInnerTriangleCertificateColorC_ne_of_adj
    {e f : wheelWithInnerTriangleGraph.edgeSet}
    (hadj : wheelWithInnerTriangleGraph.lineGraph.Adj e f) :
    wheelWithInnerTriangleCertificateColorC e ≠
      wheelWithInnerTriangleCertificateColorC f := by
  decide +revert

def wheelWithInnerTriangleCertificateColoringA :
    wheelWithInnerTriangleGraph.EdgeColoring Color :=
  Coloring.mk wheelWithInnerTriangleCertificateColorA (by
    intro e f hadj
    exact wheelWithInnerTriangleCertificateColorA_ne_of_adj hadj)

def wheelWithInnerTriangleCertificateColoringB :
    wheelWithInnerTriangleGraph.EdgeColoring Color :=
  Coloring.mk wheelWithInnerTriangleCertificateColorB (by
    intro e f hadj
    exact wheelWithInnerTriangleCertificateColorB_ne_of_adj hadj)

def wheelWithInnerTriangleCertificateColoringC :
    wheelWithInnerTriangleGraph.EdgeColoring Color :=
  Coloring.mk wheelWithInnerTriangleCertificateColorC (by
    intro e f hadj
    exact wheelWithInnerTriangleCertificateColorC_ne_of_adj hadj)

@[simp] theorem wheelWithInnerTriangleCertificateColoringA_apply
    (e : wheelWithInnerTriangleGraph.edgeSet) :
    wheelWithInnerTriangleCertificateColoringA e =
      wheelWithInnerTriangleCertificateColorA e := rfl

@[simp] theorem wheelWithInnerTriangleCertificateColoringB_apply
    (e : wheelWithInnerTriangleGraph.edgeSet) :
    wheelWithInnerTriangleCertificateColoringB e =
      wheelWithInnerTriangleCertificateColorB e := rfl

@[simp] theorem wheelWithInnerTriangleCertificateColoringC_apply
    (e : wheelWithInnerTriangleGraph.edgeSet) :
    wheelWithInnerTriangleCertificateColoringC e =
      wheelWithInnerTriangleCertificateColorC e := rfl

@[simp] theorem wheelWithInnerTriangleCertificateColorA_wit01 :
    wheelWithInnerTriangleCertificateColorA wit01 = red := by
  decide

@[simp] theorem wheelWithInnerTriangleCertificateColorA_wit02 :
    wheelWithInnerTriangleCertificateColorA wit02 = blue := by
  decide

@[simp] theorem wheelWithInnerTriangleCertificateColorA_wit03 :
    wheelWithInnerTriangleCertificateColorA wit03 = purple := by
  decide

@[simp] theorem wheelWithInnerTriangleCertificateColorB_wit01 :
    wheelWithInnerTriangleCertificateColorB wit01 = blue := by
  decide

@[simp] theorem wheelWithInnerTriangleCertificateColorB_wit02 :
    wheelWithInnerTriangleCertificateColorB wit02 = red := by
  decide

@[simp] theorem wheelWithInnerTriangleCertificateColorC_wit02 :
    wheelWithInnerTriangleCertificateColorC wit02 = purple := by
  decide

@[simp] theorem wheelWithInnerTriangleCertificateColorC_wit03 :
    wheelWithInnerTriangleCertificateColorC wit03 = blue := by
  decide

@[simp] theorem wheelWithInnerTriangleCertificateColoringA_wit01 :
    wheelWithInnerTriangleCertificateColoringA wit01 = red := by
  simp

@[simp] theorem wheelWithInnerTriangleCertificateColoringA_wit02 :
    wheelWithInnerTriangleCertificateColoringA wit02 = blue := by
  simp

@[simp] theorem wheelWithInnerTriangleCertificateColoringA_wit03 :
    wheelWithInnerTriangleCertificateColoringA wit03 = purple := by
  simp

@[simp] theorem wheelWithInnerTriangleCertificateColoringB_wit01 :
    wheelWithInnerTriangleCertificateColoringB wit01 = blue := by
  simp

@[simp] theorem wheelWithInnerTriangleCertificateColoringB_wit02 :
    wheelWithInnerTriangleCertificateColoringB wit02 = red := by
  simp

@[simp] theorem wheelWithInnerTriangleCertificateColoringC_wit02 :
    wheelWithInnerTriangleCertificateColoringC wit02 = purple := by
  simp

@[simp] theorem wheelWithInnerTriangleCertificateColoringC_wit03 :
    wheelWithInnerTriangleCertificateColoringC wit03 = blue := by
  simp

def wheelWithInnerTriangleProjectedGeneratorCertificateColorings :
    Set (wheelWithInnerTriangleGraph.EdgeColoring Color) :=
  {C | C = wheelWithInnerTriangleCertificateColoringA ∨
      C = wheelWithInnerTriangleCertificateColoringB ∨
        C = wheelWithInnerTriangleCertificateColoringC}

private theorem wheelWithInnerTriangleCertificateColoringA_unique_wit01_redPurple :
    ∀ e : wheelWithInnerTriangleGraph.edgeSet,
      e ≠ wit01 →
      e ∉ selectedBoundarySupport
        wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces
        wheelWithInnerTriangleEmbedding.faces →
      e ∈ wheelWithInnerTriangleEmbedding.faceBoundary (0 : Fin 4) →
        ¬ (wheelWithInnerTriangleCertificateColoringA e = red ∨
          wheelWithInnerTriangleCertificateColoringA e = purple) := by
  intro e hne hnotBoundary hface
  have hfaceCases : e = wit01 ∨ e = wit02 ∨ e = wit12 := by
    simpa [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary]
      using hface
  rcases hfaceCases with rfl | rfl | rfl
  · exact False.elim (hne rfl)
  · decide
  · exact False.elim (hnotBoundary wit12_mem_selectedBoundarySupport)

private theorem wheelWithInnerTriangleCertificateColoringA_unique_wit02_bluePurple :
    ∀ e : wheelWithInnerTriangleGraph.edgeSet,
      e ≠ wit02 →
      e ∉ selectedBoundarySupport
        wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces
        wheelWithInnerTriangleEmbedding.faces →
      e ∈ wheelWithInnerTriangleEmbedding.faceBoundary (0 : Fin 4) →
        ¬ (wheelWithInnerTriangleCertificateColoringA e = blue ∨
          wheelWithInnerTriangleCertificateColoringA e = purple) := by
  intro e hne hnotBoundary hface
  have hfaceCases : e = wit01 ∨ e = wit02 ∨ e = wit12 := by
    simpa [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary]
      using hface
  rcases hfaceCases with rfl | rfl | rfl
  · decide
  · exact False.elim (hne rfl)
  · exact False.elim (hnotBoundary wit12_mem_selectedBoundarySupport)

private theorem wheelWithInnerTriangleCertificateColoringA_unique_wit03_bluePurple_face2 :
    ∀ e : wheelWithInnerTriangleGraph.edgeSet,
      e ≠ wit03 →
      e ∉ selectedBoundarySupport
        wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces
        wheelWithInnerTriangleEmbedding.faces →
      e ∈ wheelWithInnerTriangleEmbedding.faceBoundary (2 : Fin 4) →
        ¬ (wheelWithInnerTriangleCertificateColoringA e = blue ∨
          wheelWithInnerTriangleCertificateColoringA e = purple) := by
  intro e hne hnotBoundary hface
  have hfaceCases : e = wit03 ∨ e = wit01 ∨ e = wit31 := by
    simpa [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary]
      using hface
  rcases hfaceCases with rfl | rfl | rfl
  · exact False.elim (hne rfl)
  · decide
  · exact False.elim (hnotBoundary wit31_mem_selectedBoundarySupport)

private theorem wheelWithInnerTriangleCertificateColoringA_unique_wit03_redPurple_face1 :
    ∀ e : wheelWithInnerTriangleGraph.edgeSet,
      e ≠ wit03 →
      e ∉ selectedBoundarySupport
        wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces
        wheelWithInnerTriangleEmbedding.faces →
      e ∈ wheelWithInnerTriangleEmbedding.faceBoundary (1 : Fin 4) →
        ¬ (wheelWithInnerTriangleCertificateColoringA e = red ∨
          wheelWithInnerTriangleCertificateColoringA e = purple) := by
  intro e hne hnotBoundary hface
  have hfaceCases : e = wit02 ∨ e = wit03 ∨ e = wit23 := by
    simpa [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary]
      using hface
  rcases hfaceCases with rfl | rfl | rfl
  · decide
  · exact False.elim (hne rfl)
  · exact False.elim (hnotBoundary wit23_mem_selectedBoundarySupport)

private theorem wheelWithInnerTriangleCertificateColoringB_unique_wit01_bluePurple :
    ∀ e : wheelWithInnerTriangleGraph.edgeSet,
      e ≠ wit01 →
      e ∉ selectedBoundarySupport
        wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces
        wheelWithInnerTriangleEmbedding.faces →
      e ∈ wheelWithInnerTriangleEmbedding.faceBoundary (0 : Fin 4) →
        ¬ (wheelWithInnerTriangleCertificateColoringB e = blue ∨
          wheelWithInnerTriangleCertificateColoringB e = purple) := by
  intro e hne hnotBoundary hface
  have hfaceCases : e = wit01 ∨ e = wit02 ∨ e = wit12 := by
    simpa [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary]
      using hface
  rcases hfaceCases with rfl | rfl | rfl
  · exact False.elim (hne rfl)
  · decide
  · exact False.elim (hnotBoundary wit12_mem_selectedBoundarySupport)

private theorem wheelWithInnerTriangleCertificateColoringC_unique_wit02_redPurple :
    ∀ e : wheelWithInnerTriangleGraph.edgeSet,
      e ≠ wit02 →
      e ∉ selectedBoundarySupport
        wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces
        wheelWithInnerTriangleEmbedding.faces →
      e ∈ wheelWithInnerTriangleEmbedding.faceBoundary (1 : Fin 4) →
        ¬ (wheelWithInnerTriangleCertificateColoringC e = red ∨
          wheelWithInnerTriangleCertificateColoringC e = purple) := by
  intro e hne hnotBoundary hface
  have hfaceCases : e = wit02 ∨ e = wit03 ∨ e = wit23 := by
    simpa [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary]
      using hface
  rcases hfaceCases with rfl | rfl | rfl
  · exact False.elim (hne rfl)
  · decide
  · exact False.elim (hnotBoundary wit23_mem_selectedBoundarySupport)

theorem wheelWithInnerTriangle_uniqueProjectedBicoloredCertificates :
    (∀ e ∈ wheelWithInnerTriangleInteriorControlEdges,
      ∃ C ∈ wheelWithInnerTriangleProjectedGeneratorCertificateColorings,
        ∃ f : wheelWithInnerTriangleEmbedding.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            a + b = red ∧
              e ∈ wheelWithInnerTriangleEmbedding.faceBoundary f ∧
                e ∉ selectedBoundarySupport
                  wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces
                  wheelWithInnerTriangleEmbedding.faces ∧
                  (C e = a ∨ C e = b) ∧
                    ∀ e' : wheelWithInnerTriangleGraph.edgeSet,
                      e' ≠ e →
                      e' ∉ selectedBoundarySupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces
                        wheelWithInnerTriangleEmbedding.faces →
                      e' ∈ wheelWithInnerTriangleEmbedding.faceBoundary f →
                        ¬ (C e' = a ∨ C e' = b)) ∧
    (∀ e ∈ wheelWithInnerTriangleInteriorControlEdges,
      ∃ C ∈ wheelWithInnerTriangleProjectedGeneratorCertificateColorings,
        ∃ f : wheelWithInnerTriangleEmbedding.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            a + b = blue ∧
              e ∈ wheelWithInnerTriangleEmbedding.faceBoundary f ∧
                e ∉ selectedBoundarySupport
                  wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces
                  wheelWithInnerTriangleEmbedding.faces ∧
                  (C e = a ∨ C e = b) ∧
                    ∀ e' : wheelWithInnerTriangleGraph.edgeSet,
                      e' ≠ e →
                      e' ∉ selectedBoundarySupport
                        wheelWithInnerTriangleEmbedding.faceBoundary
                        wheelWithInnerTriangleEmbedding.faces
                        wheelWithInnerTriangleEmbedding.faces →
                      e' ∈ wheelWithInnerTriangleEmbedding.faceBoundary f →
                        ¬ (C e' = a ∨ C e' = b)) := by
  constructor
  · intro e he
    have heCases : e = wit01 ∨ e = wit02 ∨ e = wit03 := by
      simpa [wheelWithInnerTriangleInteriorControlEdges] using he
    rcases heCases with rfl | rfl | rfl
    · refine ⟨wheelWithInnerTriangleCertificateColoringB, Or.inr (Or.inl rfl),
        (0 : Fin 4), blue, purple, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [ValidColorPair]
      · simp
      · decide
      · exact wit01_not_mem_selectedBoundarySupport
      · left
        simp
      · exact wheelWithInnerTriangleCertificateColoringB_unique_wit01_bluePurple
    · refine ⟨wheelWithInnerTriangleCertificateColoringA, Or.inl rfl,
        (0 : Fin 4), blue, purple, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [ValidColorPair]
      · simp
      · decide
      · exact wit02_not_mem_selectedBoundarySupport
      · left
        simp
      · exact wheelWithInnerTriangleCertificateColoringA_unique_wit02_bluePurple
    · refine ⟨wheelWithInnerTriangleCertificateColoringA, Or.inl rfl,
        (2 : Fin 4), blue, purple, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [ValidColorPair]
      · simp
      · decide
      · exact wit03_not_mem_selectedBoundarySupport
      · right
        simp
      · exact wheelWithInnerTriangleCertificateColoringA_unique_wit03_bluePurple_face2
  · intro e he
    have heCases : e = wit01 ∨ e = wit02 ∨ e = wit03 := by
      simpa [wheelWithInnerTriangleInteriorControlEdges] using he
    rcases heCases with rfl | rfl | rfl
    · refine ⟨wheelWithInnerTriangleCertificateColoringA, Or.inl rfl,
        (0 : Fin 4), red, purple, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [ValidColorPair]
      · simp
      · decide
      · exact wit01_not_mem_selectedBoundarySupport
      · left
        simp
      · exact wheelWithInnerTriangleCertificateColoringA_unique_wit01_redPurple
    · refine ⟨wheelWithInnerTriangleCertificateColoringC, Or.inr (Or.inr rfl),
        (1 : Fin 4), red, purple, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [ValidColorPair]
      · simp
      · decide
      · exact wit02_not_mem_selectedBoundarySupport
      · right
        simp
      · exact wheelWithInnerTriangleCertificateColoringC_unique_wit02_redPurple
    · refine ⟨wheelWithInnerTriangleCertificateColoringA, Or.inl rfl,
        (1 : Fin 4), red, purple, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [ValidColorPair]
      · simp
      · decide
      · exact wit03_not_mem_selectedBoundarySupport
      · right
        simp
      · exact wheelWithInnerTriangleCertificateColoringA_unique_wit03_redPurple_face1

theorem wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates :
    (∀ e ∈ wheelWithInnerTriangleInteriorControlEdges,
        Pi.single e red ∈
          projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding
            wheelWithInnerTriangleProjectedGeneratorCertificateColorings) ∧
      (∀ e ∈ wheelWithInnerTriangleInteriorControlEdges,
        Pi.single e blue ∈
          projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding
            wheelWithInnerTriangleProjectedGeneratorCertificateColorings) :=
  redBlueSingleCoordinateMemberships_of_uniqueProjectedBicoloredCertificates
    wheelWithInnerTriangleInteriorControlEdges
    wheelWithInnerTriangle_uniqueProjectedBicoloredCertificates.1
    wheelWithInnerTriangle_uniqueProjectedBicoloredCertificates.2

/-- Boundary-root synthesis from the explicit wheel-with-inner-triangle certificate family.  The
finite F2 verdict supplies complete nonzero coverage on the three spoke controls, and the unique
projected-bicolored certificates supply both red and blue probes there. -/
theorem wheelWithInnerTriangle_theorem49BoundaryRootSynthesis_of_uniqueCertificates
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hsubset :
      wheelWithInnerTriangleProjectedGeneratorCertificateColorings ⊆
        wheelWithInnerTriangleGraph.EdgeKempeClosure C₀) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀ :=
  theorem49BoundaryRootSynthesis_of_redBlueSingleCoordinateMemberships
    wheelWithInnerTriangleEmbedding C₀
    wheelWithInnerTriangleProjectedGeneratorCertificateColorings hsubset
    wheelWithInnerTriangleInteriorControlEdges
    wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges
    wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
    wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2

private def wheelWithInnerTriangleOuterEdgeCluster
    (e : wheelWithInnerTriangleGraph.edgeSet) : Bool :=
  if e = wit45 ∨ e = wit56 ∨ e = wit64 then true else false

private theorem wheelWithInnerTriangleOuterEdgeCluster_eq_of_lineGraph_adj
    {e f : wheelWithInnerTriangleGraph.edgeSet}
    (hadj : wheelWithInnerTriangleGraph.lineGraph.Adj e f) :
    wheelWithInnerTriangleOuterEdgeCluster e = wheelWithInnerTriangleOuterEdgeCluster f := by
  decide +revert

private theorem wheelWithInnerTriangleOuterEdgeCluster_eq_of_bicoloredWalk
    {a b : Color}
    {C : wheelWithInnerTriangleGraph.EdgeColoring Color}
    {u v : ↥(C.bicoloredSet a b)}
    (p : (C.bicoloredSubgraph a b).Walk u v) :
    wheelWithInnerTriangleOuterEdgeCluster u.1 = wheelWithInnerTriangleOuterEdgeCluster v.1 := by
  induction p with
  | nil => rfl
  | cons hadj p ih =>
      exact (wheelWithInnerTriangleOuterEdgeCluster_eq_of_lineGraph_adj
        (by simpa using hadj)).trans ih

private theorem wheelWithInnerTriangleOuterEdgeCluster_eq_of_bicoloredReachable
    {a b : Color}
    {C : wheelWithInnerTriangleGraph.EdgeColoring Color}
    {e f : wheelWithInnerTriangleGraph.edgeSet}
    {he : e ∈ C.bicoloredSet a b} {hf : f ∈ C.bicoloredSet a b}
    (hreach : (C.bicoloredSubgraph a b).Reachable ⟨e, he⟩ ⟨f, hf⟩) :
    wheelWithInnerTriangleOuterEdgeCluster e = wheelWithInnerTriangleOuterEdgeCluster f := by
  refine hreach.elim ?_
  intro p
  exact wheelWithInnerTriangleOuterEdgeCluster_eq_of_bicoloredWalk p

private theorem wheelWithInnerTriangle_not_mem_kempeComponentSet_of_ne_left_ne_right
    {x y : Color}
    {C : wheelWithInnerTriangleGraph.EdgeColoring Color}
    {K : (C.bicoloredSubgraph x y).ConnectedComponent}
    {e : wheelWithInnerTriangleGraph.edgeSet}
    (hx : C e ≠ x) (hy : C e ≠ y) :
    e ∉ C.kempeComponentSet x y K := by
  intro hmem
  rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hmem with h | h
  · exact hx h
  · exact hy h

private theorem wheelWithInnerTriangle_not_mem_component_of_outerCluster_ne
    {x y : Color}
    {C : wheelWithInnerTriangleGraph.EdgeColoring Color}
    {K : (C.bicoloredSubgraph x y).ConnectedComponent}
    {root e : wheelWithInnerTriangleGraph.edgeSet}
    (hroot : root ∈ C.kempeComponentSet x y K)
    (hrootCluster : wheelWithInnerTriangleOuterEdgeCluster root = false)
    (hedgeCluster : wheelWithInnerTriangleOuterEdgeCluster e = true) :
    e ∉ C.kempeComponentSet x y K := by
  intro hmem
  rcases hmem with ⟨he', hec⟩
  rcases hroot with ⟨hroot', hrootc⟩
  have hcomp' :
      (C.bicoloredSubgraph x y).connectedComponentMk ⟨e, he'⟩ =
      (C.bicoloredSubgraph x y).connectedComponentMk ⟨root, hroot'⟩ :=
    hec.trans hrootc.symm
  have hreach : (C.bicoloredSubgraph x y).Reachable ⟨e, he'⟩ ⟨root, hroot'⟩ :=
    ConnectedComponent.eq.mp hcomp'
  have hcluster := wheelWithInnerTriangleOuterEdgeCluster_eq_of_bicoloredReachable hreach
  rw [hedgeCluster, hrootCluster] at hcluster
  cases hcluster

private theorem wheelWithInnerTriangleCertificateColoringA_wit01_mem_bicoloredSet_red_blue :
    wit01 ∈ wheelWithInnerTriangleCertificateColoringA.bicoloredSet red blue := by
  left
  decide

private noncomputable def wheelWithInnerTriangleCertificateColoringA_redBlueComponent :
    (wheelWithInnerTriangleCertificateColoringA.bicoloredSubgraph red blue).ConnectedComponent :=
  (wheelWithInnerTriangleCertificateColoringA.bicoloredSubgraph red blue).connectedComponentMk
    ⟨wit01, wheelWithInnerTriangleCertificateColoringA_wit01_mem_bicoloredSet_red_blue⟩

private theorem wit01_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent :
    wit01 ∈ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet red blue
      wheelWithInnerTriangleCertificateColoringA_redBlueComponent := by
  exact wheelWithInnerTriangleCertificateColoringA.mem_kempeComponentSet_self
    wheelWithInnerTriangleCertificateColoringA_wit01_mem_bicoloredSet_red_blue

private theorem wit02_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent :
    wit02 ∈ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet red blue
      wheelWithInnerTriangleCertificateColoringA_redBlueComponent := by
  exact wheelWithInnerTriangleCertificateColoringA.mem_kempeComponentSet_of_adj
    wit01_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent (by decide) (by
      right
      decide)

private theorem wit23_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent :
    wit23 ∈ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet red blue
      wheelWithInnerTriangleCertificateColoringA_redBlueComponent := by
  exact wheelWithInnerTriangleCertificateColoringA.mem_kempeComponentSet_of_adj
    wit02_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent (by decide) (by
      left
      decide)

private theorem wit31_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent :
    wit31 ∈ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet red blue
      wheelWithInnerTriangleCertificateColoringA_redBlueComponent := by
  exact wheelWithInnerTriangleCertificateColoringA.mem_kempeComponentSet_of_adj
    wit01_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent (by decide) (by
      right
      decide)

private theorem wit03_not_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent :
    wit03 ∉ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet red blue
      wheelWithInnerTriangleCertificateColoringA_redBlueComponent := by
  exact wheelWithInnerTriangle_not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := wheelWithInnerTriangleCertificateColoringA)
    (K := wheelWithInnerTriangleCertificateColoringA_redBlueComponent)
    (e := wit03) (by decide) (by decide)

private theorem wit12_not_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent :
    wit12 ∉ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet red blue
      wheelWithInnerTriangleCertificateColoringA_redBlueComponent := by
  exact wheelWithInnerTriangle_not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := wheelWithInnerTriangleCertificateColoringA)
    (K := wheelWithInnerTriangleCertificateColoringA_redBlueComponent)
    (e := wit12) (by decide) (by decide)

private theorem wit64_not_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent :
    wit64 ∉ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet red blue
      wheelWithInnerTriangleCertificateColoringA_redBlueComponent := by
  exact wheelWithInnerTriangle_not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := wheelWithInnerTriangleCertificateColoringA)
    (K := wheelWithInnerTriangleCertificateColoringA_redBlueComponent)
    (e := wit64) (by decide) (by decide)

private theorem wit45_not_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent :
    wit45 ∉ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet red blue
      wheelWithInnerTriangleCertificateColoringA_redBlueComponent := by
  exact wheelWithInnerTriangle_not_mem_component_of_outerCluster_ne
    wit01_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent (by decide) (by decide)

private theorem wit56_not_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent :
    wit56 ∉ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet red blue
      wheelWithInnerTriangleCertificateColoringA_redBlueComponent := by
  exact wheelWithInnerTriangle_not_mem_component_of_outerCluster_ne
    wit01_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent (by decide) (by decide)

private theorem wheelWithInnerTriangleCertificateColoringA_swap_redBlueComponent_eq_B :
    wheelWithInnerTriangleCertificateColoringA.swapOnKempeComponent red blue
        wheelWithInnerTriangleCertificateColoringA_redBlueComponent =
      wheelWithInnerTriangleCertificateColoringB := by
  apply DFunLike.ext
  intro e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · decide
    · exact wit01_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · decide
    · exact wit02_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · decide
    · exact wit03_not_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · decide
    · exact wit12_not_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · decide
    · exact wit23_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · decide
    · exact wit31_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · decide
    · exact wit45_not_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · decide
    · exact wit56_not_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · decide
    · exact wit64_not_mem_wheelWithInnerTriangleCertificateColoringA_redBlueComponent

private theorem wheelWithInnerTriangleCertificateColoringA_wit02_mem_bicoloredSet_blue_purple :
    wit02 ∈ wheelWithInnerTriangleCertificateColoringA.bicoloredSet blue purple := by
  left
  decide

private noncomputable def wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent :
    (wheelWithInnerTriangleCertificateColoringA.bicoloredSubgraph blue purple).ConnectedComponent :=
  (wheelWithInnerTriangleCertificateColoringA.bicoloredSubgraph blue purple).connectedComponentMk
    ⟨wit02, wheelWithInnerTriangleCertificateColoringA_wit02_mem_bicoloredSet_blue_purple⟩

private theorem wit02_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent :
    wit02 ∈ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet blue purple
      wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent := by
  exact wheelWithInnerTriangleCertificateColoringA.mem_kempeComponentSet_self
    wheelWithInnerTriangleCertificateColoringA_wit02_mem_bicoloredSet_blue_purple

private theorem wit03_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent :
    wit03 ∈ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet blue purple
      wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent := by
  exact wheelWithInnerTriangleCertificateColoringA.mem_kempeComponentSet_of_adj
    wit02_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent (by decide) (by
      right
      decide)

private theorem wit12_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent :
    wit12 ∈ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet blue purple
      wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent := by
  exact wheelWithInnerTriangleCertificateColoringA.mem_kempeComponentSet_of_adj
    wit02_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent (by decide) (by
      right
      decide)

private theorem wit31_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent :
    wit31 ∈ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet blue purple
      wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent := by
  exact wheelWithInnerTriangleCertificateColoringA.mem_kempeComponentSet_of_adj
    wit03_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent (by decide) (by
      left
      decide)

private theorem wit01_not_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent :
    wit01 ∉ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet blue purple
      wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent := by
  exact wheelWithInnerTriangle_not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := wheelWithInnerTriangleCertificateColoringA)
    (K := wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent)
    (e := wit01) (by decide) (by decide)

private theorem wit23_not_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent :
    wit23 ∉ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet blue purple
      wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent := by
  exact wheelWithInnerTriangle_not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := wheelWithInnerTriangleCertificateColoringA)
    (K := wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent)
    (e := wit23) (by decide) (by decide)

private theorem wit45_not_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent :
    wit45 ∉ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet blue purple
      wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent := by
  exact wheelWithInnerTriangle_not_mem_kempeComponentSet_of_ne_left_ne_right
    (C := wheelWithInnerTriangleCertificateColoringA)
    (K := wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent)
    (e := wit45) (by decide) (by decide)

private theorem wit56_not_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent :
    wit56 ∉ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet blue purple
      wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent := by
  exact wheelWithInnerTriangle_not_mem_component_of_outerCluster_ne
    wit02_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent (by decide) (by decide)

private theorem wit64_not_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent :
    wit64 ∉ wheelWithInnerTriangleCertificateColoringA.kempeComponentSet blue purple
      wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent := by
  exact wheelWithInnerTriangle_not_mem_component_of_outerCluster_ne
    wit02_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent (by decide) (by decide)

private theorem wheelWithInnerTriangleCertificateColoringA_swap_bluePurpleComponent_eq_C :
    wheelWithInnerTriangleCertificateColoringA.swapOnKempeComponent blue purple
        wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent =
      wheelWithInnerTriangleCertificateColoringC := by
  apply DFunLike.ext
  intro e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · decide
    · exact wit01_not_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · decide
    · exact wit02_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · decide
    · exact wit03_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · decide
    · exact wit12_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · decide
    · exact wit23_not_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_mem]
    · decide
    · exact wit31_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · decide
    · exact wit45_not_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · decide
    · exact wit56_not_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent
  · rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
    · decide
    · exact wit64_not_mem_wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent

theorem wheelWithInnerTriangleCertificateColoringB_mem_edgeKempeClosure_certificateColoringA :
    wheelWithInnerTriangleCertificateColoringB ∈
      wheelWithInnerTriangleGraph.EdgeKempeClosure wheelWithInnerTriangleCertificateColoringA := by
  rw [← wheelWithInnerTriangleCertificateColoringA_swap_redBlueComponent_eq_B]
  exact wheelWithInnerTriangleGraph.mem_edgeKempeClosure_of_mem_of_step
    (wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self wheelWithInnerTriangleCertificateColoringA)
    red blue wheelWithInnerTriangleCertificateColoringA_redBlueComponent

theorem wheelWithInnerTriangleCertificateColoringC_mem_edgeKempeClosure_certificateColoringA :
    wheelWithInnerTriangleCertificateColoringC ∈
      wheelWithInnerTriangleGraph.EdgeKempeClosure wheelWithInnerTriangleCertificateColoringA := by
  rw [← wheelWithInnerTriangleCertificateColoringA_swap_bluePurpleComponent_eq_C]
  exact wheelWithInnerTriangleGraph.mem_edgeKempeClosure_of_mem_of_step
    (wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self wheelWithInnerTriangleCertificateColoringA)
    blue purple wheelWithInnerTriangleCertificateColoringA_bluePurpleComponent

theorem wheelWithInnerTriangleProjectedGeneratorCertificateColorings_subset_edgeKempeClosure_certificateColoringA :
    wheelWithInnerTriangleProjectedGeneratorCertificateColorings ⊆
      wheelWithInnerTriangleGraph.EdgeKempeClosure wheelWithInnerTriangleCertificateColoringA := by
  intro C hC
  rcases hC with rfl | hC
  · exact wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self
      wheelWithInnerTriangleCertificateColoringA
  · rcases hC with rfl | rfl
    · exact wheelWithInnerTriangleCertificateColoringB_mem_edgeKempeClosure_certificateColoringA
    · exact wheelWithInnerTriangleCertificateColoringC_mem_edgeKempeClosure_certificateColoringA

/-- Boundary-root synthesis for the wheel focus shell using certificate A as the root.  The
other two certificate colorings are reached from A by single Kempe swaps on the K₄ component. -/
theorem wheelWithInnerTriangle_theorem49BoundaryRootSynthesis_certificateColoringA
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleCertificateColoringA :=
  wheelWithInnerTriangle_theorem49BoundaryRootSynthesis_of_uniqueCertificates
    wheelWithInnerTriangleCertificateColoringA
    wheelWithInnerTriangleProjectedGeneratorCertificateColorings_subset_edgeKempeClosure_certificateColoringA

theorem wheelWithInnerTriangle_boundaryZeroProjectedColoringGeneratorDetector_of_uniqueCertificates :
    BoundaryZeroProjectedColoringGeneratorDetector wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleProjectedGeneratorCertificateColorings := by
  exact
    BoundaryZeroProjectedColoringGeneratorDetector.of_uniqueProjectedBicoloredCertificates
      wheelWithInnerTriangleInteriorControlEdges
      wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges
      wheelWithInnerTriangle_uniqueProjectedBicoloredCertificates.1
      wheelWithInnerTriangle_uniqueProjectedBicoloredCertificates.2

/-- Canonical finite family for the wheel focus shell: red and blue single-coordinate probes on
the three lab-certified spoke controls, realized by the unique projected-bicolored certificate
colorings. -/
noncomputable def wheelWithInnerTriangleUniqueCertificateRedBlueFamily :
    ({e : wheelWithInnerTriangleGraph.edgeSet // e ∈ wheelWithInnerTriangleInteriorControlEdges} ×
        Bool) →
      projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding
        wheelWithInnerTriangleProjectedGeneratorCertificateColorings :=
  redBlueSingleCoordinateFamily wheelWithInnerTriangleInteriorControlEdges
    wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
    wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2

/-- Family-pairing kernel form of the wheel focus-shell F₂ verdict.  The canonical red/blue
certificate family has trivial selected-boundary-zero pairing kernel. -/
theorem wheelWithInnerTriangle_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificateRedBlueFamily_eq_bot :
    LinearMap.ker
        (planarBoundaryZeroFamilyPairingMap
          wheelWithInnerTriangleUniqueCertificateRedBlueFamily) = ⊥ :=
  ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_edgePredicateNonzeroWitnesses
    wheelWithInnerTriangleUniqueCertificateRedBlueFamily
    (fun e => e ∈ wheelWithInnerTriangleInteriorControlEdges)
    wheelWithInnerTriangle_boundaryZero_declaredForcedEdges_nonzeroCoverage
    (redBlueSingleCoordinateFamily_witnessRed wheelWithInnerTriangleInteriorControlEdges
      wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
      wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2)
    (redBlueSingleCoordinateFamily_witnessBlue wheelWithInnerTriangleInteriorControlEdges
      wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
      wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2)

/-- Combined kernel-check form of the finite F₂ verdict for the two focus shells. -/
theorem focusF2BoundaryZero_uniqueCertificateRedBlueFamilyPairingKernels_eq_bot :
    LinearMap.ker
        (planarBoundaryZeroFamilyPairingMap
          sharedInteriorPairUniqueCertificateRedBlueFamily) = ⊥ ∧
      LinearMap.ker
        (planarBoundaryZeroFamilyPairingMap
          wheelWithInnerTriangleUniqueCertificateRedBlueFamily) = ⊥ :=
  ⟨sharedInteriorPair_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificateRedBlueFamily_eq_bot,
    wheelWithInnerTriangle_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificateRedBlueFamily_eq_bot⟩

/-- Projected-face-generator certificate form of the wheel focus verdict.  The finite lab can
feed this theorem with literal projected face-generator equalities for red and blue probes on the
three declared spoke controls. -/
theorem wheelWithInnerTriangle_boundaryZeroProjectedColoringGeneratorDetector_of_projectedFaceGeneratorEqualities
    (colorings : Set (wheelWithInnerTriangleGraph.EdgeColoring Color))
    (hred :
      ∀ e ∈ wheelWithInnerTriangleInteriorControlEdges,
        ∃ C ∈ colorings, ∃ f : wheelWithInnerTriangleEmbedding.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            boundaryZeroProjection
                (selectedBoundarySupport
                  wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces
                  wheelWithInnerTriangleEmbedding.faces)
                (polarizedFaceGenerator C a b
                  (wheelWithInnerTriangleEmbedding.faceBoundary f)) =
              Pi.single e red)
    (hblue :
      ∀ e ∈ wheelWithInnerTriangleInteriorControlEdges,
        ∃ C ∈ colorings, ∃ f : wheelWithInnerTriangleEmbedding.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            boundaryZeroProjection
                (selectedBoundarySupport
                  wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces
                  wheelWithInnerTriangleEmbedding.faces)
                (polarizedFaceGenerator C a b
                  (wheelWithInnerTriangleEmbedding.faceBoundary f)) =
              Pi.single e blue) :
    BoundaryZeroProjectedColoringGeneratorDetector wheelWithInnerTriangleEmbedding colorings :=
  BoundaryZeroProjectedColoringGeneratorDetector.of_projectedFaceGeneratorEqualities
    wheelWithInnerTriangleInteriorControlEdges
    wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges
    hred hblue

/-- Boundary-root synthesis form for wheel projected-face-generator certificates. -/
theorem wheelWithInnerTriangle_theorem49BoundaryRootSynthesis_of_projectedFaceGeneratorEqualities
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (colorings : Set (wheelWithInnerTriangleGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    (hred :
      ∀ e ∈ wheelWithInnerTriangleInteriorControlEdges,
        ∃ C ∈ colorings, ∃ f : wheelWithInnerTriangleEmbedding.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            boundaryZeroProjection
                (selectedBoundarySupport
                  wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces
                  wheelWithInnerTriangleEmbedding.faces)
                (polarizedFaceGenerator C a b
                  (wheelWithInnerTriangleEmbedding.faceBoundary f)) =
              Pi.single e red)
    (hblue :
      ∀ e ∈ wheelWithInnerTriangleInteriorControlEdges,
        ∃ C ∈ colorings, ∃ f : wheelWithInnerTriangleEmbedding.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            boundaryZeroProjection
                (selectedBoundarySupport
                  wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces
                  wheelWithInnerTriangleEmbedding.faces)
                (polarizedFaceGenerator C a b
                  (wheelWithInnerTriangleEmbedding.faceBoundary f)) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀ :=
  theorem49BoundaryRootSynthesis_of_projectedFaceGeneratorEqualities
    wheelWithInnerTriangleEmbedding C₀ colorings hsubset
    wheelWithInnerTriangleInteriorControlEdges
    wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges
    hred hblue

theorem sharedInteriorPair_remainingRedSingleCoordinateMembership_of_uniqueCertificates
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 8 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    ∀ e ∈ classifier.remainingControlEdges sharedInteriorPairInteriorControlEdges,
      Pi.single e red ∈
        projectedColoringGeneratorSubspace sharedInteriorPairEmbedding
          sharedInteriorPairProjectedGeneratorCertificateColorings := by
  intro e he
  exact sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1 e
    ((classifier.mem_remainingControlEdges_iff sharedInteriorPairInteriorControlEdges e).1 he).1

theorem sharedInteriorPair_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 8 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    ∀ e ∈ classifier.remainingControlEdges sharedInteriorPairInteriorControlEdges,
      Pi.single e blue ∈
        projectedColoringGeneratorSubspace sharedInteriorPairEmbedding
          sharedInteriorPairProjectedGeneratorCertificateColorings := by
  intro e he
  exact sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2 e
    ((classifier.mem_remainingControlEdges_iff sharedInteriorPairInteriorControlEdges e).1 he).1

theorem wheelWithInnerTriangle_remainingRedSingleCoordinateMembership_of_uniqueCertificates
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 7 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    ∀ e ∈ classifier.remainingControlEdges wheelWithInnerTriangleInteriorControlEdges,
      Pi.single e red ∈
        projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding
          wheelWithInnerTriangleProjectedGeneratorCertificateColorings := by
  intro e he
  exact wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1 e
    ((classifier.mem_remainingControlEdges_iff wheelWithInnerTriangleInteriorControlEdges e).1 he).1

theorem wheelWithInnerTriangle_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : Fin 7 → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    ∀ e ∈ classifier.remainingControlEdges wheelWithInnerTriangleInteriorControlEdges,
      Pi.single e blue ∈
        projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding
          wheelWithInnerTriangleProjectedGeneratorCertificateColorings := by
  intro e he
  exact wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2 e
    ((classifier.mem_remainingControlEdges_iff wheelWithInnerTriangleInteriorControlEdges e).1 he).1

theorem sharedInteriorPair_CAP5_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_uniqueCertificates_of_emittedFinset_card_lt_two
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : Fin 8 → Prop) (hcyclic : CyclicallyFiveEdgeConnected sharedInteriorPairGraph)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide sharedInteriorPairGraph side (boundaryEdge i))
    (hcycles : HasCycleOnSide sharedInteriorPairGraph side ∧
      HasCycleOnSide sharedInteriorPairGraph (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard : classifier.emittedFinset.card < 2) :
    let hred :=
      sharedInteriorPair_remainingRedSingleCoordinateMembership_of_uniqueCertificates
        classifier
    let hblue :=
      sharedInteriorPair_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
        classifier
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
      ∃ z : sharedInteriorPairGraph.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
          z ≠ 0 ∧
            (∀ e : sharedInteriorPairGraph.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ e : sharedInteriorPairGraph.edgeSet,
                (e ∈ classifier.crossingExtensionFinset sharedInteriorPairInteriorControlEdges ∨
                  e ∈ classifier.noncrossingExtensionFinset
                    sharedInteriorPairInteriorControlEdges) ∧
                  e ∈ classifier.remainingControlEdges sharedInteriorPairInteriorControlEdges ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧
                        ((classifier.remainingControlEdges
                            sharedInteriorPairInteriorControlEdges).erase e).card <
                          (classifier.remainingControlEdges
                            sharedInteriorPairInteriorControlEdges).card ∧
                          ∃ i :
                            ({e : sharedInteriorPairGraph.edgeSet //
                              e ∈ classifier.remainingControlEdges
                                sharedInteriorPairInteriorControlEdges} × Bool),
                            chainDotBilinForm sharedInteriorPairGraph.edgeSet
                                (redBlueSingleCoordinateFamily
                                  (classifier.remainingControlEdges
                                    sharedInteriorPairInteriorControlEdges)
                                  hred hblue i :
                                  sharedInteriorPairGraph.edgeSet → Color) z ≠ 0 := by
  have hcard' :
      classifier.emittedFinset.card +
          Fintype.card {e : sharedInteriorPairGraph.edgeSet //
            e ∈ selectedBoundarySupport sharedInteriorPairEmbedding.faceBoundary
              sharedInteriorPairEmbedding.faces sharedInteriorPairEmbedding.faces} <
        Fintype.card sharedInteriorPairGraph.edgeSet := by
    have hboundary :
        Fintype.card {e : sharedInteriorPairGraph.edgeSet //
          e ∈ selectedBoundarySupport sharedInteriorPairEmbedding.faceBoundary
            sharedInteriorPairEmbedding.faces sharedInteriorPairEmbedding.faces} = 7 := by
      rw [sharedInteriorPair_selectedBoundarySupport_eq]
      decide
    have hedge : Fintype.card sharedInteriorPairGraph.edgeSet = 9 := by
      decide
    rw [hboundary, hedge]
    omega
  let hred :=
    sharedInteriorPair_remainingRedSingleCoordinateMembership_of_uniqueCertificates
      classifier
  let hblue :=
    sharedInteriorPair_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
      classifier
  exact
    data.forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      sharedInteriorPairEmbedding sharedInteriorPairProjectedGeneratorCertificateColorings
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      sharedInteriorPairInteriorControlEdges hcard'
      sharedInteriorPair_boundaryZero_controlEdges_interiorEdges
      hred hblue

theorem wheelWithInnerTriangle_CAP5_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_uniqueCertificates_of_emittedFinset_card_lt_three
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : Fin 7 → Prop) (hcyclic : CyclicallyFiveEdgeConnected wheelWithInnerTriangleGraph)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide wheelWithInnerTriangleGraph side (boundaryEdge i))
    (hcycles : HasCycleOnSide wheelWithInnerTriangleGraph side ∧
      HasCycleOnSide wheelWithInnerTriangleGraph (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard : classifier.emittedFinset.card < 3) :
    let hred :=
      wheelWithInnerTriangle_remainingRedSingleCoordinateMembership_of_uniqueCertificates
        classifier
    let hblue :=
      wheelWithInnerTriangle_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
        classifier
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
      ∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
          z ≠ 0 ∧
            (∀ e : wheelWithInnerTriangleGraph.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ e : wheelWithInnerTriangleGraph.edgeSet,
                (e ∈ classifier.crossingExtensionFinset
                    wheelWithInnerTriangleInteriorControlEdges ∨
                  e ∈ classifier.noncrossingExtensionFinset
                    wheelWithInnerTriangleInteriorControlEdges) ∧
                  e ∈ classifier.remainingControlEdges
                    wheelWithInnerTriangleInteriorControlEdges ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧
                        ((classifier.remainingControlEdges
                            wheelWithInnerTriangleInteriorControlEdges).erase e).card <
                          (classifier.remainingControlEdges
                            wheelWithInnerTriangleInteriorControlEdges).card ∧
                          ∃ i :
                            ({e : wheelWithInnerTriangleGraph.edgeSet //
                              e ∈ classifier.remainingControlEdges
                                wheelWithInnerTriangleInteriorControlEdges} × Bool),
                            chainDotBilinForm wheelWithInnerTriangleGraph.edgeSet
                                (redBlueSingleCoordinateFamily
                                  (classifier.remainingControlEdges
                                    wheelWithInnerTriangleInteriorControlEdges)
                                  hred hblue i :
                                  wheelWithInnerTriangleGraph.edgeSet → Color) z ≠ 0 := by
  have hcard' :
      classifier.emittedFinset.card +
          Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
            e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
              wheelWithInnerTriangleEmbedding.faces
              wheelWithInnerTriangleEmbedding.faces} <
        Fintype.card wheelWithInnerTriangleGraph.edgeSet := by
    have hboundary :
        Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
          e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
            wheelWithInnerTriangleEmbedding.faces
            wheelWithInnerTriangleEmbedding.faces} = 6 := by
      rw [wheelWithInnerTriangle_selectedBoundarySupport_eq]
      decide
    have hedge : Fintype.card wheelWithInnerTriangleGraph.edgeSet = 9 := by
      decide
    rw [hboundary, hedge]
    omega
  let hred :=
    wheelWithInnerTriangle_remainingRedSingleCoordinateMembership_of_uniqueCertificates
      classifier
  let hblue :=
    wheelWithInnerTriangle_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
      classifier
  exact
    data.forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleProjectedGeneratorCertificateColorings
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      wheelWithInnerTriangleInteriorControlEdges hcard'
      wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges
      hred hblue

theorem sharedInteriorPair_CAP5_ofDecidableChecks_missingCheckerEvidence_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_uniqueCertificates_of_emittedFinset_card_lt_two
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : Fin 8 → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected sharedInteriorPairGraph)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide sharedInteriorPairGraph side (boundaryEdge i))
    (hcycles : HasCycleOnSide sharedInteriorPairGraph side ∧
      HasCycleOnSide sharedInteriorPairGraph (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard : classifier.emittedFinset.card < 2) :
    let hred :=
      sharedInteriorPair_remainingRedSingleCoordinateMembership_of_uniqueCertificates
        classifier
    let hblue :=
      sharedInteriorPair_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
        classifier
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingCheckerEvidence) ∨
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
          ∃ z : sharedInteriorPairGraph.edgeSet → Color,
            z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding ∧
              z ≠ 0 ∧
                (∀ e : sharedInteriorPairGraph.edgeSet,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                    z e = 0) ∧
                  ∃ e : sharedInteriorPairGraph.edgeSet,
                    (e ∈ classifier.crossingExtensionFinset
                        sharedInteriorPairInteriorControlEdges ∨
                      e ∈ classifier.noncrossingExtensionFinset
                        sharedInteriorPairInteriorControlEdges) ∧
                      e ∈ classifier.remainingControlEdges
                        sharedInteriorPairInteriorControlEdges ∧
                        ¬ data.EnumeratedExceptionalAnnulusForcedEdge
                          p0Inside p4Inside side e ∧
                          z e ≠ 0 ∧
                            ((classifier.remainingControlEdges
                                sharedInteriorPairInteriorControlEdges).erase e).card <
                              (classifier.remainingControlEdges
                                sharedInteriorPairInteriorControlEdges).card ∧
                              ∃ i :
                                ({e : sharedInteriorPairGraph.edgeSet //
                                  e ∈ classifier.remainingControlEdges
                                    sharedInteriorPairInteriorControlEdges} × Bool),
                                chainDotBilinForm sharedInteriorPairGraph.edgeSet
                                    (redBlueSingleCoordinateFamily
                                      (classifier.remainingControlEdges
                                        sharedInteriorPairInteriorControlEdges)
                                      hred hblue i :
                                      sharedInteriorPairGraph.edgeSet → Color) z ≠ 0 := by
  have hcard' :
      classifier.emittedFinset.card +
          Fintype.card {e : sharedInteriorPairGraph.edgeSet //
            e ∈ selectedBoundarySupport sharedInteriorPairEmbedding.faceBoundary
              sharedInteriorPairEmbedding.faces sharedInteriorPairEmbedding.faces} <
        Fintype.card sharedInteriorPairGraph.edgeSet := by
    have hboundary :
        Fintype.card {e : sharedInteriorPairGraph.edgeSet //
          e ∈ selectedBoundarySupport sharedInteriorPairEmbedding.faceBoundary
            sharedInteriorPairEmbedding.faces sharedInteriorPairEmbedding.faces} = 7 := by
      rw [sharedInteriorPair_selectedBoundarySupport_eq]
      decide
    have hedge : Fintype.card sharedInteriorPairGraph.edgeSet = 9 := by
      decide
    rw [hboundary, hedge]
    omega
  let hred :=
    sharedInteriorPair_remainingRedSingleCoordinateMembership_of_uniqueCertificates
      classifier
  let hblue :=
    sharedInteriorPair_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
      classifier
  exact
    data.ofDecidableChecks_missingCheckerEvidence_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      sharedInteriorPairEmbedding sharedInteriorPairProjectedGeneratorCertificateColorings
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      sharedInteriorPairInteriorControlEdges hcard'
      sharedInteriorPair_boundaryZero_controlEdges_interiorEdges
      hred hblue

theorem wheelWithInnerTriangle_CAP5_ofDecidableChecks_missingCheckerEvidence_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_uniqueCertificates_of_emittedFinset_card_lt_three
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : Fin 7 → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected wheelWithInnerTriangleGraph)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide wheelWithInnerTriangleGraph side (boundaryEdge i))
    (hcycles : HasCycleOnSide wheelWithInnerTriangleGraph side ∧
      HasCycleOnSide wheelWithInnerTriangleGraph (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard : classifier.emittedFinset.card < 3) :
    let hred :=
      wheelWithInnerTriangle_remainingRedSingleCoordinateMembership_of_uniqueCertificates
        classifier
    let hblue :=
      wheelWithInnerTriangle_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
        classifier
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingCheckerEvidence) ∨
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
          ∃ z : wheelWithInnerTriangleGraph.edgeSet → Color,
            z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding ∧
              z ≠ 0 ∧
                (∀ e : wheelWithInnerTriangleGraph.edgeSet,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                    z e = 0) ∧
                  ∃ e : wheelWithInnerTriangleGraph.edgeSet,
                    (e ∈ classifier.crossingExtensionFinset
                        wheelWithInnerTriangleInteriorControlEdges ∨
                      e ∈ classifier.noncrossingExtensionFinset
                        wheelWithInnerTriangleInteriorControlEdges) ∧
                      e ∈ classifier.remainingControlEdges
                        wheelWithInnerTriangleInteriorControlEdges ∧
                        ¬ data.EnumeratedExceptionalAnnulusForcedEdge
                          p0Inside p4Inside side e ∧
                          z e ≠ 0 ∧
                            ((classifier.remainingControlEdges
                                wheelWithInnerTriangleInteriorControlEdges).erase e).card <
                              (classifier.remainingControlEdges
                                wheelWithInnerTriangleInteriorControlEdges).card ∧
                              ∃ i :
                                ({e : wheelWithInnerTriangleGraph.edgeSet //
                                  e ∈ classifier.remainingControlEdges
                                    wheelWithInnerTriangleInteriorControlEdges} × Bool),
                                chainDotBilinForm wheelWithInnerTriangleGraph.edgeSet
                                    (redBlueSingleCoordinateFamily
                                      (classifier.remainingControlEdges
                                        wheelWithInnerTriangleInteriorControlEdges)
                                      hred hblue i :
                                      wheelWithInnerTriangleGraph.edgeSet → Color) z ≠ 0 := by
  have hcard' :
      classifier.emittedFinset.card +
          Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
            e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
              wheelWithInnerTriangleEmbedding.faces
              wheelWithInnerTriangleEmbedding.faces} <
        Fintype.card wheelWithInnerTriangleGraph.edgeSet := by
    have hboundary :
        Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
          e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
            wheelWithInnerTriangleEmbedding.faces
            wheelWithInnerTriangleEmbedding.faces} = 6 := by
      rw [wheelWithInnerTriangle_selectedBoundarySupport_eq]
      decide
    have hedge : Fintype.card wheelWithInnerTriangleGraph.edgeSet = 9 := by
      decide
    rw [hboundary, hedge]
    omega
  let hred :=
    wheelWithInnerTriangle_remainingRedSingleCoordinateMembership_of_uniqueCertificates
      classifier
  let hblue :=
    wheelWithInnerTriangle_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
      classifier
  exact
    data.ofDecidableChecks_missingCheckerEvidence_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleProjectedGeneratorCertificateColorings
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      wheelWithInnerTriangleInteriorControlEdges hcard'
      wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges
      hred hblue

/-- No-missing-evidence form of the shared focus-shell obstruction.  If CAP5 emits fewer than
the two lab-required shared-interior controls, its enumerated forced edges do not cover all
nonzero selected-boundary-zero chains. -/
theorem sharedInteriorPair_CAP5_emittedFinset_card_lt_two_refutes_forcedEdgeCoverage_of_uniqueCertificates
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : Fin 8 → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected sharedInteriorPairGraph)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide sharedInteriorPairGraph side (boundaryEdge i))
    (hcycles : HasCycleOnSide sharedInteriorPairGraph side ∧
      HasCycleOnSide sharedInteriorPairGraph (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard : classifier.emittedFinset.card < 2)
    (hnoMissing :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge →
          ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
            boundaryEdge side latent).MissingCheckerEvidence) :
    ¬ (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
      z ≠ 0 →
        ∃ e : sharedInteriorPairGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) := by
  have hcard' :
      classifier.emittedFinset.card +
          Fintype.card {e : sharedInteriorPairGraph.edgeSet //
            e ∈ selectedBoundarySupport sharedInteriorPairEmbedding.faceBoundary
              sharedInteriorPairEmbedding.faces sharedInteriorPairEmbedding.faces} <
        Fintype.card sharedInteriorPairGraph.edgeSet := by
    have hboundary :
        Fintype.card {e : sharedInteriorPairGraph.edgeSet //
          e ∈ selectedBoundarySupport sharedInteriorPairEmbedding.faceBoundary
            sharedInteriorPairEmbedding.faces sharedInteriorPairEmbedding.faces} = 7 := by
      rw [sharedInteriorPair_selectedBoundarySupport_eq]
      decide
    have hedge : Fintype.card sharedInteriorPairGraph.edgeSet = 9 := by
      decide
    rw [hboundary, hedge]
    omega
  let hred :=
    sharedInteriorPair_remainingRedSingleCoordinateMembership_of_uniqueCertificates
      classifier
  let hblue :=
    sharedInteriorPair_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
      classifier
  exact
    data.noMissingCheckerEvidence_refutes_forcedEdgeCoverage_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      sharedInteriorPairEmbedding sharedInteriorPairProjectedGeneratorCertificateColorings
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      sharedInteriorPairInteriorControlEdges hcard'
      sharedInteriorPair_boundaryZero_controlEdges_interiorEdges hred hblue hnoMissing

/-- No-missing-evidence form of the wheel focus-shell obstruction.  If CAP5 emits fewer than
the three lab-required spoke controls, its enumerated forced edges do not cover all nonzero
selected-boundary-zero chains. -/
theorem wheelWithInnerTriangle_CAP5_emittedFinset_card_lt_three_refutes_forcedEdgeCoverage_of_uniqueCertificates
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : Fin 7 → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected wheelWithInnerTriangleGraph)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide wheelWithInnerTriangleGraph side (boundaryEdge i))
    (hcycles : HasCycleOnSide wheelWithInnerTriangleGraph side ∧
      HasCycleOnSide wheelWithInnerTriangleGraph (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard : classifier.emittedFinset.card < 3)
    (hnoMissing :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge →
          ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
            boundaryEdge side latent).MissingCheckerEvidence) :
    ¬ (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
      z ≠ 0 →
        ∃ e : wheelWithInnerTriangleGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) := by
  have hcard' :
      classifier.emittedFinset.card +
          Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
            e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
              wheelWithInnerTriangleEmbedding.faces
              wheelWithInnerTriangleEmbedding.faces} <
        Fintype.card wheelWithInnerTriangleGraph.edgeSet := by
    have hboundary :
        Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
          e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
            wheelWithInnerTriangleEmbedding.faces
            wheelWithInnerTriangleEmbedding.faces} = 6 := by
      rw [wheelWithInnerTriangle_selectedBoundarySupport_eq]
      decide
    have hedge : Fintype.card wheelWithInnerTriangleGraph.edgeSet = 9 := by
      decide
    rw [hboundary, hedge]
    omega
  let hred :=
    wheelWithInnerTriangle_remainingRedSingleCoordinateMembership_of_uniqueCertificates
      classifier
  let hblue :=
    wheelWithInnerTriangle_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
      classifier
  exact
    data.noMissingCheckerEvidence_refutes_forcedEdgeCoverage_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleProjectedGeneratorCertificateColorings
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      wheelWithInnerTriangleInteriorControlEdges hcard'
      wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges hred hblue hnoMissing

/-- Lower-bound form of the shared focus-shell obstruction.  With no missing checker evidence,
any CAP5 run whose enumerated forced edges cover every nonzero selected-boundary-zero chain must
emit both shared-interior controls. -/
theorem sharedInteriorPair_CAP5_emittedFinset_card_ge_two_of_forcedEdgeCoverage_of_uniqueCertificates
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : Fin 8 → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected sharedInteriorPairGraph)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide sharedInteriorPairGraph side (boundaryEdge i))
    (hcycles : HasCycleOnSide sharedInteriorPairGraph side ∧
      HasCycleOnSide sharedInteriorPairGraph (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hnoMissing :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge →
          ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
            boundaryEdge side latent).MissingCheckerEvidence)
    (hcoverage :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        z ≠ 0 →
          ∃ e : sharedInteriorPairGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    2 ≤ classifier.emittedFinset.card := by
  let hred :=
    sharedInteriorPair_remainingRedSingleCoordinateMembership_of_uniqueCertificates
      classifier
  let hblue :=
    sharedInteriorPair_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
      classifier
  have hge :=
    data.forcedEdgeCoverage_emittedFinset_card_add_boundary_card_ge_of_noMissingCheckerEvidence_of_finsetControl
      sharedInteriorPairEmbedding sharedInteriorPairProjectedGeneratorCertificateColorings
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      sharedInteriorPairInteriorControlEdges
      sharedInteriorPair_boundaryZero_controlEdges_interiorEdges hred hblue hnoMissing
      hcoverage
  have hboundary :
      Fintype.card {e : sharedInteriorPairGraph.edgeSet //
        e ∈ selectedBoundarySupport sharedInteriorPairEmbedding.faceBoundary
          sharedInteriorPairEmbedding.faces sharedInteriorPairEmbedding.faces} = 7 := by
    rw [sharedInteriorPair_selectedBoundarySupport_eq]
    decide
  have hedge : Fintype.card sharedInteriorPairGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hedge] at hge
  omega

/-- Lower-bound form of the wheel focus-shell obstruction.  With no missing checker evidence,
any CAP5 run whose enumerated forced edges cover every nonzero selected-boundary-zero chain must
emit all three spoke controls. -/
theorem wheelWithInnerTriangle_CAP5_emittedFinset_card_ge_three_of_forcedEdgeCoverage_of_uniqueCertificates
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : Fin 7 → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected wheelWithInnerTriangleGraph)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide wheelWithInnerTriangleGraph side (boundaryEdge i))
    (hcycles : HasCycleOnSide wheelWithInnerTriangleGraph side ∧
      HasCycleOnSide wheelWithInnerTriangleGraph (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hnoMissing :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge →
          ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
            boundaryEdge side latent).MissingCheckerEvidence)
    (hcoverage :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        z ≠ 0 →
          ∃ e : wheelWithInnerTriangleGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    3 ≤ classifier.emittedFinset.card := by
  let hred :=
    wheelWithInnerTriangle_remainingRedSingleCoordinateMembership_of_uniqueCertificates
      classifier
  let hblue :=
    wheelWithInnerTriangle_remainingBlueSingleCoordinateMembership_of_uniqueCertificates
      classifier
  have hge :=
    data.forcedEdgeCoverage_emittedFinset_card_add_boundary_card_ge_of_noMissingCheckerEvidence_of_finsetControl
      wheelWithInnerTriangleEmbedding wheelWithInnerTriangleProjectedGeneratorCertificateColorings
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      wheelWithInnerTriangleInteriorControlEdges
      wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges hred hblue hnoMissing
      hcoverage
  have hboundary :
      Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
        e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces} = 6 := by
    rw [wheelWithInnerTriangle_selectedBoundarySupport_eq]
    decide
  have hedge : Fintype.card wheelWithInnerTriangleGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hedge] at hge
  omega

private theorem edge_eq_of_indicatorChain_singleton_ne_zero
    {E : Type*} [DecidableEq E] {γ : Color} {target e : E}
    (he : indicatorChain γ ({target} : Finset E) e ≠ 0) :
    e = target := by
  by_contra hne
  have hnotMem : e ∉ ({target} : Finset E) := by
    intro hmem
    exact hne (by simpa using hmem)
  exact he (indicatorChain_apply_of_not_mem (γ := γ) hnotMem)

private theorem edge_mem_of_indicatorChain_pair_ne_zero
    {E : Type*} [DecidableEq E] {γ : Color} {a b e : E}
    (he : indicatorChain γ ({a, b} : Finset E) e ≠ 0) :
    e = a ∨ e = b := by
  by_contra hnot
  have hneA : e ≠ a := by
    intro heq
    exact hnot (Or.inl heq)
  have hneB : e ≠ b := by
    intro heq
    exact hnot (Or.inr heq)
  have hnotMem : e ∉ ({a, b} : Finset E) := by
    intro hmem
    rcases Finset.mem_insert.1 hmem with heqA | htail
    · exact hneA heqA
    · have heqB : e = b := by simpa using htail
      exact hneB heqB
  exact he (indicatorChain_apply_of_not_mem (γ := γ) hnotMem)

/-- Exact forced-edge form of the shared focus-shell obstruction.  Any CAP5 coverage predicate
for all nonzero selected-boundary-zero chains must enumerate both shared-interior controls. -/
theorem sharedInteriorPair_CAP5_forcedEdgeCoverage_forces_sip01_and_sip12
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (hcoverage :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        z ≠ 0 →
          ∃ e : sharedInteriorPairGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side sip01 ∧
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side sip12 := by
  constructor
  · exact
      data.forcedEdgeCoverage_forces_edge_of_boundaryZero_singletonSupport
        sharedInteriorPairEmbedding p0Inside p4Inside side sip01
        sharedInteriorPairSip12OnlyEvader
        sharedInteriorPairSip12OnlyEvader_mem_planarBoundaryZeroSubmodule
        (by simp [sharedInteriorPairSip12OnlyEvader])
        (by
          intro e he
          exact
            edge_eq_of_indicatorChain_singleton_ne_zero
              (γ := red) (target := sip01) (e := e)
              (by simpa [sharedInteriorPairSip12OnlyEvader] using he))
        hcoverage
  · exact
      data.forcedEdgeCoverage_forces_edge_of_boundaryZero_singletonSupport
        sharedInteriorPairEmbedding p0Inside p4Inside side sip12
        sharedInteriorPairSip01OnlyEvader
        sharedInteriorPairSip01OnlyEvader_mem_planarBoundaryZeroSubmodule
        (by simp [sharedInteriorPairSip01OnlyEvader])
        (by
          intro e he
          exact
            edge_eq_of_indicatorChain_singleton_ne_zero
              (γ := red) (target := sip12) (e := e)
              (by simpa [sharedInteriorPairSip01OnlyEvader] using he))
        hcoverage

/-- Exact forced-edge form of the wheel focus-shell obstruction.  Any CAP5 coverage predicate
for all nonzero selected-boundary-zero chains must enumerate all three interior spokes. -/
theorem wheelWithInnerTriangle_CAP5_forcedEdgeCoverage_forces_wit01_wit02_wit03
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (hcoverage :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        z ≠ 0 →
          ∃ e : wheelWithInnerTriangleGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit01 ∧
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit02 ∧
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit03 := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      data.forcedEdgeCoverage_forces_edge_of_boundaryZero_singletonSupport
        wheelWithInnerTriangleEmbedding p0Inside p4Inside side wit01
        wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader
        wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader_mem_planarBoundaryZeroSubmodule
        (by simp [wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader])
        (by
          intro e he
          exact
            edge_eq_of_indicatorChain_singleton_ne_zero
              (γ := red) (target := wit01) (e := e)
              (by
                simpa [wheelWithInnerTriangleWit02Wit03OnlyBoundaryZeroEvader]
                  using he))
        hcoverage
  · exact
      data.forcedEdgeCoverage_forces_edge_of_boundaryZero_singletonSupport
        wheelWithInnerTriangleEmbedding p0Inside p4Inside side wit02
        wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader
        wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader_mem_planarBoundaryZeroSubmodule
        (by simp [wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader])
        (by
          intro e he
          exact
            edge_eq_of_indicatorChain_singleton_ne_zero
              (γ := red) (target := wit02) (e := e)
              (by
                simpa [wheelWithInnerTriangleWit01Wit03OnlyBoundaryZeroEvader]
                  using he))
        hcoverage
  · exact
      data.forcedEdgeCoverage_forces_edge_of_boundaryZero_singletonSupport
        wheelWithInnerTriangleEmbedding p0Inside p4Inside side wit03
        wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader
        wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader_mem_planarBoundaryZeroSubmodule
        (by simp [wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader])
        (by
          intro e he
          exact
            edge_eq_of_indicatorChain_singleton_ne_zero
              (γ := red) (target := wit03) (e := e)
              (by
                simpa [wheelWithInnerTriangleWit01Wit02OnlyBoundaryZeroEvader]
                  using he))
        hcoverage

/-- Kirchhoff-repaired forced-edge form for the shared focus shell.  Coverage of all nonzero
boundary-zero Kirchhoff chains must enumerate at least one of the two shared-interior controls. -/
theorem sharedInteriorPair_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_forces_some_interiorControlEdge
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (hcoverage :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
        z ≠ 0 →
          ∃ e : sharedInteriorPairGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side sip01 ∨
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side sip12 := by
  rcases sharedInteriorPair_emptyControl_has_boundaryZeroKirchhoff_evader with
    ⟨hz, _, _, hzNonzero⟩
  rcases hcoverage hz hzNonzero with ⟨e, heForced, hze⟩
  have heSupport : e = sip01 ∨ e = sip12 :=
    edge_mem_of_indicatorChain_pair_ne_zero
      (γ := red) (a := sip01) (b := sip12) (e := e)
      (by simpa [sharedInteriorPairNoForceKirchhoffEvader] using hze)
  rcases heSupport with rfl | rfl
  · exact Or.inl heForced
  · exact Or.inr heForced

/-- Kirchhoff-repaired forced-edge form for the wheel focus shell.  Coverage of all nonzero
boundary-zero Kirchhoff chains must enumerate two of the three spoke controls. -/
theorem wheelWithInnerTriangle_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_forces_two_spokes
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (hcoverage :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
        z ≠ 0 →
          ∃ e : wheelWithInnerTriangleGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit01 ∧
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit02) ∨
      (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit01 ∧
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit03) ∨
      (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit02 ∧
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit03) := by
  have h23 :
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit02 ∨
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit03 := by
    rcases wheelWithInnerTriangle_wit01_only_has_boundaryZeroKirchhoff_evader with
      ⟨hz, _, _, _, hzNonzero⟩
    rcases hcoverage hz hzNonzero with ⟨e, heForced, hze⟩
    have heSupport : e = wit02 ∨ e = wit03 :=
      edge_mem_of_indicatorChain_pair_ne_zero
        (γ := red) (a := wit02) (b := wit03) (e := e)
        (by simpa [wheelWithInnerTriangleWit01OnlyEvader] using hze)
    rcases heSupport with rfl | rfl
    · exact Or.inl heForced
    · exact Or.inr heForced
  have h13 :
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit01 ∨
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit03 := by
    rcases wheelWithInnerTriangle_wit02_only_has_boundaryZeroKirchhoff_evader with
      ⟨hz, _, _, _, hzNonzero⟩
    rcases hcoverage hz hzNonzero with ⟨e, heForced, hze⟩
    have heSupport : e = wit01 ∨ e = wit03 :=
      edge_mem_of_indicatorChain_pair_ne_zero
        (γ := red) (a := wit01) (b := wit03) (e := e)
        (by simpa [wheelWithInnerTriangleWit02OnlyEvader] using hze)
    rcases heSupport with rfl | rfl
    · exact Or.inl heForced
    · exact Or.inr heForced
  have h12 :
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit01 ∨
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side wit02 := by
    rcases wheelWithInnerTriangle_wit03_only_has_boundaryZeroKirchhoff_evader with
      ⟨hz, _, _, _, hzNonzero⟩
    rcases hcoverage hz hzNonzero with ⟨e, heForced, hze⟩
    have heSupport : e = wit01 ∨ e = wit02 :=
      edge_mem_of_indicatorChain_pair_ne_zero
        (γ := red) (a := wit01) (b := wit02) (e := e)
        (by simpa [wheelWithInnerTriangleWit03OnlyEvader] using hze)
    rcases heSupport with rfl | rfl
    · exact Or.inl heForced
    · exact Or.inr heForced
  rcases h23 with h2 | h3
  · rcases h13 with h1 | h3'
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inr ⟨h2, h3'⟩)
  · rcases h12 with h1 | h2
    · exact Or.inr (Or.inl ⟨h1, h3⟩)
    · exact Or.inr (Or.inr ⟨h2, h3⟩)

/-- Classifier-facing exact form for the shared focus shell: exact CAP5 coverage emits every
canonical shared-interior control edge. -/
theorem sharedInteriorPair_CAP5_forcedEdgeCoverage_emits_interiorControlEdges
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        z ≠ 0 →
          ∃ e : sharedInteriorPairGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    sharedInteriorPairInteriorControlEdges ⊆ classifier.emittedFinset := by
  have hforced :=
    sharedInteriorPair_CAP5_forcedEdgeCoverage_forces_sip01_and_sip12
      p0Inside p4Inside side hcoverage
  intro e he
  have he' : e ∈ ({sip01, sip12} : Finset sharedInteriorPairGraph.edgeSet) := by
    simpa [sharedInteriorPairInteriorControlEdges] using he
  rcases Finset.mem_insert.1 he' with rfl | heTail
  · exact (classifier.emittedFinset_spec sip01).2 hforced.1
  · have he12 : e = sip12 := by simpa using heTail
    subst e
    exact (classifier.emittedFinset_spec sip12).2 hforced.2

/-- Converse finite-lab handoff for the shared focus shell: if the CAP5 classifier emits both
lab-certified shared-interior controls, then its enumerated forced-edge predicate covers every
nonzero selected-boundary-zero chain. -/
theorem sharedInteriorPair_CAP5_forcedEdgeCoverage_of_emits_interiorControlEdges
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : sharedInteriorPairInteriorControlEdges ⊆ classifier.emittedFinset) :
    ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
      z ≠ 0 →
        ∃ e : sharedInteriorPairGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 :=
  data.forcedEdgeCoverage_of_controlEdges_subset_emittedFinset
    sharedInteriorPairEmbedding classifier sharedInteriorPairInteriorControlEdges
    sharedInteriorPair_boundaryZero_declaredForcedEdges_nonzeroCoverage hemits

/-- Classifier-facing Kirchhoff-repaired exact form for the shared focus shell: coverage of all
nonzero boundary-zero Kirchhoff chains is equivalent to emitting at least one shared control. -/
theorem sharedInteriorPair_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_emits_some_interiorControlEdge
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
        z ≠ 0 →
          ∃ e : sharedInteriorPairGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    sip01 ∈ classifier.emittedFinset ∨ sip12 ∈ classifier.emittedFinset := by
  rcases
      sharedInteriorPair_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_forces_some_interiorControlEdge
        p0Inside p4Inside side hcoverage with h01 | h12
  · exact Or.inl ((classifier.emittedFinset_spec sip01).2 h01)
  · exact Or.inr ((classifier.emittedFinset_spec sip12).2 h12)

/-- Converse Kirchhoff handoff for the shared focus shell: emitting either shared control covers
every nonzero boundary-zero Kirchhoff chain. -/
theorem sharedInteriorPair_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_of_emits_some_interiorControlEdge
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : sip01 ∈ classifier.emittedFinset ∨ sip12 ∈ classifier.emittedFinset) :
    ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
      z ≠ 0 →
        ∃ e : sharedInteriorPairGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 := by
  intro z hz hzNonzero
  rcases hemits with h01 | h12
  · refine ⟨sip01, (classifier.emittedFinset_spec sip01).1 h01, ?_⟩
    intro hsip01
    exact hzNonzero
      (sharedInteriorPair_boundaryZeroKirchhoff_no_evader_of_vanishes_on_sip01
        z hz hsip01)
  · refine ⟨sip12, (classifier.emittedFinset_spec sip12).1 h12, ?_⟩
    intro hsip12
    exact hzNonzero
      (sharedInteriorPair_boundaryZeroKirchhoff_no_evader_of_vanishes_on_sip12
        z hz hsip12)

/-- Exact Kirchhoff-repaired classifier form for the shared focus-shell F2 verdict.  CAP5 covers
all nonzero boundary-zero Kirchhoff chains exactly when it emits at least one shared control. -/
theorem sharedInteriorPair_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_iff_emits_some_interiorControlEdge
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
      z ≠ 0 →
        ∃ e : sharedInteriorPairGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      sip01 ∈ classifier.emittedFinset ∨ sip12 ∈ classifier.emittedFinset := by
  constructor
  · exact
      sharedInteriorPair_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_emits_some_interiorControlEdge
        p0Inside p4Inside side classifier
  · exact
      sharedInteriorPair_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_of_emits_some_interiorControlEdge
        p0Inside p4Inside side classifier

/-- Exact classifier-facing form of the shared focus-shell F₂ verdict.  The CAP5 forced-edge
predicate covers all nonzero selected-boundary-zero chains exactly when the classifier emits the
two lab-certified shared-interior controls. -/
theorem sharedInteriorPair_CAP5_forcedEdgeCoverage_iff_emits_interiorControlEdges
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
      z ≠ 0 →
        ∃ e : sharedInteriorPairGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      sharedInteriorPairInteriorControlEdges ⊆ classifier.emittedFinset := by
  constructor
  · exact sharedInteriorPair_CAP5_forcedEdgeCoverage_emits_interiorControlEdges
      p0Inside p4Inside side classifier
  · exact sharedInteriorPair_CAP5_forcedEdgeCoverage_of_emits_interiorControlEdges
      p0Inside p4Inside side classifier

/-- Runner-facing exact form for the shared focus shell: exact CAP5 coverage leaves no
unprocessed canonical shared-interior control edge. -/
theorem sharedInteriorPair_CAP5_forcedEdgeCoverage_remainingInteriorControlEdges_eq_empty
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        z ≠ 0 →
          ∃ e : sharedInteriorPairGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    classifier.remainingControlEdges sharedInteriorPairInteriorControlEdges = ∅ := by
  have hsubset :
      sharedInteriorPairInteriorControlEdges ⊆ classifier.emittedFinset :=
    sharedInteriorPair_CAP5_forcedEdgeCoverage_emits_interiorControlEdges
      p0Inside p4Inside side classifier hcoverage
  ext e
  constructor
  · intro he
    have he' :=
      (classifier.mem_remainingControlEdges_iff sharedInteriorPairInteriorControlEdges e).1 he
    exact False.elim (he'.2 (hsubset he'.1))
  · intro he
    simp at he

/-- Classifier-facing exact form for the wheel focus shell: exact CAP5 coverage emits every
canonical spoke control edge. -/
theorem wheelWithInnerTriangle_CAP5_forcedEdgeCoverage_emits_interiorControlEdges
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        z ≠ 0 →
          ∃ e : wheelWithInnerTriangleGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    wheelWithInnerTriangleInteriorControlEdges ⊆ classifier.emittedFinset := by
  have hforced :=
    wheelWithInnerTriangle_CAP5_forcedEdgeCoverage_forces_wit01_wit02_wit03
      p0Inside p4Inside side hcoverage
  intro e he
  have he' :
      e ∈ ({wit01, wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
    simpa [wheelWithInnerTriangleInteriorControlEdges] using he
  rcases Finset.mem_insert.1 he' with rfl | heTail
  · exact (classifier.emittedFinset_spec wit01).2 hforced.1
  · rcases Finset.mem_insert.1 heTail with rfl | heTail'
    · exact (classifier.emittedFinset_spec wit02).2 hforced.2.1
    · have he03 : e = wit03 := by simpa using heTail'
      subst e
      exact (classifier.emittedFinset_spec wit03).2 hforced.2.2

/-- Converse finite-lab handoff for the wheel focus shell: if the CAP5 classifier emits the
three lab-certified spoke controls, then its enumerated forced-edge predicate covers every
nonzero selected-boundary-zero chain. -/
theorem wheelWithInnerTriangle_CAP5_forcedEdgeCoverage_of_emits_interiorControlEdges
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : wheelWithInnerTriangleInteriorControlEdges ⊆ classifier.emittedFinset) :
    ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
      z ≠ 0 →
        ∃ e : wheelWithInnerTriangleGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 :=
  data.forcedEdgeCoverage_of_controlEdges_subset_emittedFinset
    wheelWithInnerTriangleEmbedding classifier wheelWithInnerTriangleInteriorControlEdges
    wheelWithInnerTriangle_boundaryZero_declaredForcedEdges_nonzeroCoverage hemits

/-- Classifier-facing Kirchhoff-repaired exact form for the wheel focus shell: coverage of all
nonzero boundary-zero Kirchhoff chains emits two of the three spoke controls. -/
theorem wheelWithInnerTriangle_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_emits_two_spokes
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
        z ≠ 0 →
          ∃ e : wheelWithInnerTriangleGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    (wit01 ∈ classifier.emittedFinset ∧ wit02 ∈ classifier.emittedFinset) ∨
      (wit01 ∈ classifier.emittedFinset ∧ wit03 ∈ classifier.emittedFinset) ∨
      (wit02 ∈ classifier.emittedFinset ∧ wit03 ∈ classifier.emittedFinset) := by
  have hforced :=
    wheelWithInnerTriangle_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_forces_two_spokes
      p0Inside p4Inside side hcoverage
  rcases hforced with h12 | hrest
  · exact Or.inl
      ⟨(classifier.emittedFinset_spec wit01).2 h12.1,
        (classifier.emittedFinset_spec wit02).2 h12.2⟩
  · rcases hrest with h13 | h23
    · exact Or.inr (Or.inl
        ⟨(classifier.emittedFinset_spec wit01).2 h13.1,
          (classifier.emittedFinset_spec wit03).2 h13.2⟩)
    · exact Or.inr (Or.inr
        ⟨(classifier.emittedFinset_spec wit02).2 h23.1,
          (classifier.emittedFinset_spec wit03).2 h23.2⟩)

/-- Converse Kirchhoff handoff for the wheel focus shell: emitting any two spokes covers every
nonzero boundary-zero Kirchhoff chain. -/
theorem wheelWithInnerTriangle_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_of_emits_two_spokes
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits :
      (wit01 ∈ classifier.emittedFinset ∧ wit02 ∈ classifier.emittedFinset) ∨
        (wit01 ∈ classifier.emittedFinset ∧ wit03 ∈ classifier.emittedFinset) ∨
        (wit02 ∈ classifier.emittedFinset ∧ wit03 ∈ classifier.emittedFinset)) :
    ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
      z ≠ 0 →
        ∃ e : wheelWithInnerTriangleGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 := by
  intro z hz hzNonzero
  rcases hemits with h12 | hrest
  · by_cases h01 : z wit01 = 0
    · refine ⟨wit02, (classifier.emittedFinset_spec wit02).1 h12.2, ?_⟩
      intro h02
      exact hzNonzero
        (wheelWithInnerTriangle_boundaryZeroKirchhoff_no_evader_of_vanishes_on_wit01_wit02
          z hz h01 h02)
    · exact ⟨wit01, (classifier.emittedFinset_spec wit01).1 h12.1, h01⟩
  · rcases hrest with h13 | h23
    · by_cases h01 : z wit01 = 0
      · refine ⟨wit03, (classifier.emittedFinset_spec wit03).1 h13.2, ?_⟩
        intro h03
        exact hzNonzero
          (wheelWithInnerTriangle_boundaryZeroKirchhoff_no_evader_of_vanishes_on_wit01_wit03
            z hz h01 h03)
      · exact ⟨wit01, (classifier.emittedFinset_spec wit01).1 h13.1, h01⟩
    · by_cases h02 : z wit02 = 0
      · refine ⟨wit03, (classifier.emittedFinset_spec wit03).1 h23.2, ?_⟩
        intro h03
        exact hzNonzero
          (wheelWithInnerTriangle_boundaryZeroKirchhoff_no_evader_of_vanishes_on_wit02_wit03
            z hz h02 h03)
      · exact ⟨wit02, (classifier.emittedFinset_spec wit02).1 h23.1, h02⟩

/-- Exact Kirchhoff-repaired classifier form for the wheel focus-shell F2 verdict.  CAP5 covers
all nonzero boundary-zero Kirchhoff chains exactly when it emits two spoke controls. -/
theorem wheelWithInnerTriangle_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_iff_emits_two_spokes
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
      z ≠ 0 →
        ∃ e : wheelWithInnerTriangleGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      (wit01 ∈ classifier.emittedFinset ∧ wit02 ∈ classifier.emittedFinset) ∨
        (wit01 ∈ classifier.emittedFinset ∧ wit03 ∈ classifier.emittedFinset) ∨
        (wit02 ∈ classifier.emittedFinset ∧ wit03 ∈ classifier.emittedFinset) := by
  constructor
  · exact
      wheelWithInnerTriangle_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_emits_two_spokes
        p0Inside p4Inside side classifier
  · exact
      wheelWithInnerTriangle_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_of_emits_two_spokes
        p0Inside p4Inside side classifier

/-- Cardinality form of the shared Kirchhoff-repaired focus-shell detector threshold. -/
theorem sharedInteriorPair_emittedInterior_card_ge_one_iff
    (emitted : Finset sharedInteriorPairGraph.edgeSet) :
    1 ≤ (emitted.filter fun e => e ∈ sharedInteriorPairInteriorControlEdges).card ↔
      sip01 ∈ emitted ∨ sip12 ∈ emitted := by
  classical
  constructor
  · intro hcard
    have hnonempty :
        (emitted.filter fun e => e ∈ sharedInteriorPairInteriorControlEdges).Nonempty :=
      Finset.card_pos.1 (by omega)
    rcases hnonempty with ⟨e, he⟩
    rcases Finset.mem_filter.1 he with ⟨heEmitted, heControl⟩
    have hcases : e = sip01 ∨ e = sip12 := by
      simpa [sharedInteriorPairInteriorControlEdges] using heControl
    rcases hcases with rfl | rfl
    · exact Or.inl heEmitted
    · exact Or.inr heEmitted
  · intro hemits
    rcases hemits with h01 | h12
    · have hmem :
          sip01 ∈ emitted.filter fun e => e ∈ sharedInteriorPairInteriorControlEdges :=
        Finset.mem_filter.2 ⟨h01, by simp [sharedInteriorPairInteriorControlEdges]⟩
      have hpos :
          0 < (emitted.filter fun e => e ∈ sharedInteriorPairInteriorControlEdges).card :=
        Finset.card_pos.2 ⟨sip01, hmem⟩
      omega
    · have hmem :
          sip12 ∈ emitted.filter fun e => e ∈ sharedInteriorPairInteriorControlEdges :=
        Finset.mem_filter.2 ⟨h12, by simp [sharedInteriorPairInteriorControlEdges]⟩
      have hpos :
          0 < (emitted.filter fun e => e ∈ sharedInteriorPairInteriorControlEdges).card :=
        Finset.card_pos.2 ⟨sip12, hmem⟩
      omega

/-- Cardinality form of the wheel Kirchhoff-repaired focus-shell detector threshold. -/
theorem wheelWithInnerTriangle_emittedInterior_card_ge_two_iff
    (emitted : Finset wheelWithInnerTriangleGraph.edgeSet) :
    2 ≤ (emitted.filter fun e => e ∈ wheelWithInnerTriangleInteriorControlEdges).card ↔
      (wit01 ∈ emitted ∧ wit02 ∈ emitted) ∨
        (wit01 ∈ emitted ∧ wit03 ∈ emitted) ∨
        (wit02 ∈ emitted ∧ wit03 ∈ emitted) := by
  classical
  constructor
  · intro hcard
    by_cases h01 : wit01 ∈ emitted
    · by_cases h02 : wit02 ∈ emitted
      · exact Or.inl ⟨h01, h02⟩
      · by_cases h03 : wit03 ∈ emitted
        · exact Or.inr (Or.inl ⟨h01, h03⟩)
        · have hle :
              (emitted.filter fun e => e ∈ wheelWithInnerTriangleInteriorControlEdges).card ≤ 1 := by
            have hsubset :
                (emitted.filter fun e =>
                  e ∈ wheelWithInnerTriangleInteriorControlEdges) ⊆
                  ({wit01} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
              intro e he
              rcases Finset.mem_filter.1 he with ⟨heEmitted, heControl⟩
              have hcases : e = wit01 ∨ e = wit02 ∨ e = wit03 := by
                simpa [wheelWithInnerTriangleInteriorControlEdges] using heControl
              rcases hcases with rfl | rfl | rfl
              · simp
              · exact False.elim (h02 heEmitted)
              · exact False.elim (h03 heEmitted)
            simpa using Finset.card_le_card hsubset
          omega
    · by_cases h02 : wit02 ∈ emitted
      · by_cases h03 : wit03 ∈ emitted
        · exact Or.inr (Or.inr ⟨h02, h03⟩)
        · have hle :
              (emitted.filter fun e => e ∈ wheelWithInnerTriangleInteriorControlEdges).card ≤ 1 := by
            have hsubset :
                (emitted.filter fun e =>
                  e ∈ wheelWithInnerTriangleInteriorControlEdges) ⊆
                  ({wit02} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
              intro e he
              rcases Finset.mem_filter.1 he with ⟨heEmitted, heControl⟩
              have hcases : e = wit01 ∨ e = wit02 ∨ e = wit03 := by
                simpa [wheelWithInnerTriangleInteriorControlEdges] using heControl
              rcases hcases with rfl | rfl | rfl
              · exact False.elim (h01 heEmitted)
              · simp
              · exact False.elim (h03 heEmitted)
            simpa using Finset.card_le_card hsubset
          omega
      · by_cases h03 : wit03 ∈ emitted
        · have hle :
              (emitted.filter fun e => e ∈ wheelWithInnerTriangleInteriorControlEdges).card ≤ 1 := by
            have hsubset :
                (emitted.filter fun e =>
                  e ∈ wheelWithInnerTriangleInteriorControlEdges) ⊆
                  ({wit03} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
              intro e he
              rcases Finset.mem_filter.1 he with ⟨heEmitted, heControl⟩
              have hcases : e = wit01 ∨ e = wit02 ∨ e = wit03 := by
                simpa [wheelWithInnerTriangleInteriorControlEdges] using heControl
              rcases hcases with rfl | rfl | rfl
              · exact False.elim (h01 heEmitted)
              · exact False.elim (h02 heEmitted)
              · simp
            simpa using Finset.card_le_card hsubset
          omega
        · have hle :
              (emitted.filter fun e => e ∈ wheelWithInnerTriangleInteriorControlEdges).card ≤ 0 := by
            have hsubset :
                (emitted.filter fun e =>
                  e ∈ wheelWithInnerTriangleInteriorControlEdges) ⊆
                  (∅ : Finset wheelWithInnerTriangleGraph.edgeSet) := by
              intro e he
              rcases Finset.mem_filter.1 he with ⟨heEmitted, heControl⟩
              have hcases : e = wit01 ∨ e = wit02 ∨ e = wit03 := by
                simpa [wheelWithInnerTriangleInteriorControlEdges] using heControl
              rcases hcases with rfl | rfl | rfl
              · exact False.elim (h01 heEmitted)
              · exact False.elim (h02 heEmitted)
              · exact False.elim (h03 heEmitted)
            simpa using Finset.card_le_card hsubset
          omega
  · intro hemits
    rcases hemits with h12 | hrest
    · have hsubset :
          ({wit01, wit02} : Finset wheelWithInnerTriangleGraph.edgeSet) ⊆
            emitted.filter fun e => e ∈ wheelWithInnerTriangleInteriorControlEdges := by
        intro e he
        have hcases : e = wit01 ∨ e = wit02 := by
          simpa using he
        rcases hcases with rfl | rfl
        · exact Finset.mem_filter.2 ⟨h12.1, by simp [wheelWithInnerTriangleInteriorControlEdges]⟩
        · exact Finset.mem_filter.2 ⟨h12.2, by simp [wheelWithInnerTriangleInteriorControlEdges]⟩
      have hle := Finset.card_le_card hsubset
      have hcard : ({wit01, wit02} : Finset wheelWithInnerTriangleGraph.edgeSet).card = 2 := by
        decide
      omega
    · rcases hrest with h13 | h23
      · have hsubset :
            ({wit01, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet) ⊆
              emitted.filter fun e => e ∈ wheelWithInnerTriangleInteriorControlEdges := by
          intro e he
          have hcases : e = wit01 ∨ e = wit03 := by
            simpa using he
          rcases hcases with rfl | rfl
          · exact Finset.mem_filter.2 ⟨h13.1, by simp [wheelWithInnerTriangleInteriorControlEdges]⟩
          · exact Finset.mem_filter.2 ⟨h13.2, by simp [wheelWithInnerTriangleInteriorControlEdges]⟩
        have hle := Finset.card_le_card hsubset
        have hcard : ({wit01, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet).card = 2 := by
          decide
        omega
      · have hsubset :
            ({wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet) ⊆
              emitted.filter fun e => e ∈ wheelWithInnerTriangleInteriorControlEdges := by
          intro e he
          have hcases : e = wit02 ∨ e = wit03 := by
            simpa using he
          rcases hcases with rfl | rfl
          · exact Finset.mem_filter.2 ⟨h23.1, by simp [wheelWithInnerTriangleInteriorControlEdges]⟩
          · exact Finset.mem_filter.2 ⟨h23.2, by simp [wheelWithInnerTriangleInteriorControlEdges]⟩
        have hle := Finset.card_le_card hsubset
        have hcard : ({wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet).card = 2 := by
          decide
        omega

/--
Runner-facing exact Kirchhoff threshold for the shared focus shell.  CAP5 covers every nonzero
boundary-zero Kirchhoff chain exactly when the emitted classifier has at least one emitted edge in
the two lab-certified shared-interior controls.
-/
theorem sharedInteriorPair_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_iff_emittedInterior_card_ge_one
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
      z ≠ 0 →
        ∃ e : sharedInteriorPairGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      1 ≤ (classifier.emittedFinset.filter fun e =>
        e ∈ sharedInteriorPairInteriorControlEdges).card :=
  (sharedInteriorPair_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_iff_emits_some_interiorControlEdge
    p0Inside p4Inside side classifier).trans
    (sharedInteriorPair_emittedInterior_card_ge_one_iff classifier.emittedFinset).symm

/--
Runner-facing exact Kirchhoff threshold for the wheel focus shell.  CAP5 covers every nonzero
boundary-zero Kirchhoff chain exactly when the emitted classifier has at least two emitted edges
among the three lab-certified spokes.
-/
theorem wheelWithInnerTriangle_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_iff_emittedInterior_card_ge_two
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
      z ≠ 0 →
        ∃ e : wheelWithInnerTriangleGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      2 ≤ (classifier.emittedFinset.filter fun e =>
        e ∈ wheelWithInnerTriangleInteriorControlEdges).card :=
  (wheelWithInnerTriangle_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_iff_emits_two_spokes
    p0Inside p4Inside side classifier).trans
    (wheelWithInnerTriangle_emittedInterior_card_ge_two_iff classifier.emittedFinset).symm

/-- Shell-specialized detector bound for the shared focus shell.  The generic Kirchhoff target
dimension inequality reduces here to the lab minimum: Kirchhoff coverage must emit at least one
edge. -/
theorem sharedInteriorPair_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_emittedFinset_card_ge_one
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
        z ≠ 0 →
          ∃ e : sharedInteriorPairGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    1 ≤ classifier.emittedFinset.card := by
  have hge :=
    data.edge_card_le_emittedFinset_card_add_boundary_card_add_vertex_card_of_forcedEdgeKirchhoffCoverage
      sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8))
      p0Inside p4Inside side classifier hcoverage
  have hboundary :
      Fintype.card {e : sharedInteriorPairGraph.edgeSet //
        e ∈ selectedBoundarySupport sharedInteriorPairEmbedding.faceBoundary
          sharedInteriorPairEmbedding.faces sharedInteriorPairEmbedding.faces} = 7 := by
    rw [sharedInteriorPair_selectedBoundarySupport_eq]
    decide
  have hvertices : Fintype.card {v : Fin 8 // v ∈ ({(1 : Fin 8)} : Finset (Fin 8))} = 1 := by
    decide
  have hedge : Fintype.card sharedInteriorPairGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hvertices, hedge] at hge
  omega

/-- Low-cardinality refutation for the shared Kirchhoff detector: an empty emitted CAP5
classifier cannot cover every nonzero boundary-zero Kirchhoff chain. -/
theorem sharedInteriorPair_CAP5_boundaryZeroKirchhoff_not_forcedEdgeCoverage_of_emittedFinset_card_eq_zero
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard : classifier.emittedFinset.card = 0) :
    ¬ ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          sharedInteriorPairEmbedding ({(1 : Fin 8)} : Finset (Fin 8)) →
      z ≠ 0 →
        ∃ e : sharedInteriorPairGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 := by
  intro hcoverage
  have hge :=
    sharedInteriorPair_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_emittedFinset_card_ge_one
      p0Inside p4Inside side classifier hcoverage
  omega

/-- Shell-specialized detector bound for the wheel focus shell.  Kirchhoff coverage on the
centered wheel target must emit at least two spoke coordinates. -/
theorem wheelWithInnerTriangle_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_emittedFinset_card_ge_two
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
        z ≠ 0 →
          ∃ e : wheelWithInnerTriangleGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    2 ≤ classifier.emittedFinset.card := by
  have hge :=
    data.edge_card_le_emittedFinset_card_add_boundary_card_add_vertex_card_of_forcedEdgeKirchhoffCoverage
      wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7))
      p0Inside p4Inside side classifier hcoverage
  have hboundary :
      Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
        e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces} = 6 := by
    rw [wheelWithInnerTriangle_selectedBoundarySupport_eq]
    decide
  have hvertices : Fintype.card {v : Fin 7 // v ∈ ({(0 : Fin 7)} : Finset (Fin 7))} = 1 := by
    decide
  have hedge : Fintype.card wheelWithInnerTriangleGraph.edgeSet = 9 := by
    decide
  rw [hboundary, hvertices, hedge] at hge
  omega

/-- Low-cardinality refutation for the wheel Kirchhoff detector: one emitted edge is still
insufficient to cover every nonzero boundary-zero Kirchhoff chain. -/
theorem wheelWithInnerTriangle_CAP5_boundaryZeroKirchhoff_not_forcedEdgeCoverage_of_emittedFinset_card_le_one
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard : classifier.emittedFinset.card ≤ 1) :
    ¬ ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          wheelWithInnerTriangleEmbedding ({(0 : Fin 7)} : Finset (Fin 7)) →
      z ≠ 0 →
        ∃ e : wheelWithInnerTriangleGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 := by
  intro hcoverage
  have hge :=
    wheelWithInnerTriangle_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_emittedFinset_card_ge_two
      p0Inside p4Inside side classifier hcoverage
  omega

/-- Two-band boundary-zero detector bound with boundary emissions trimmed away.  Forced-edge
coverage must emit all nine interior coordinates; selected-boundary emissions do not contribute
to the lower bound. -/
theorem twoBandAnnulus_CAP5_forcedEdgeCoverage_emittedInterior_card_ge_nine
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 9 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
        z ≠ 0 →
          ∃ e : twoBandAnnulusGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    9 ≤ (classifier.emittedFinset.filter fun e =>
      e ∈ interiorEdgeSupport
        twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces).card := by
  exact
    twoBandAnnulus_boundaryZero_classifierControl_emittedInterior_card_ge_nine
      classifier
      (data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_forcedEdgeCoverage
        twoBandAnnulusEmbedding classifier hcoverage)

/-- Low-interior-emission refutation for the two-band boundary-zero detector. -/
theorem twoBandAnnulus_CAP5_not_forcedEdgeCoverage_of_emittedInterior_card_le_eight
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 9 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard :
      (classifier.emittedFinset.filter fun e =>
        e ∈ interiorEdgeSupport
          twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces).card ≤ 8) :
    ¬ ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
      z ≠ 0 →
        ∃ e : twoBandAnnulusGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 := by
  intro hcoverage
  have hge :=
    twoBandAnnulus_CAP5_forcedEdgeCoverage_emittedInterior_card_ge_nine
      p0Inside p4Inside side classifier hcoverage
  omega

/-- Cardinality form of the two-band boundary-zero detector threshold.  Since the interior
support has exactly nine edges, reaching the lower bound is equivalent to emitting every
two-band interior edge. -/
theorem twoBandAnnulus_emittedInterior_card_ge_nine_iff
    (emitted : Finset twoBandAnnulusGraph.edgeSet) :
    9 ≤ (emitted.filter fun e =>
        e ∈ interiorEdgeSupport
          twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces).card ↔
      twoBandAnnulusInteriorEdges ⊆ emitted := by
  classical
  constructor
  · intro hcard e heInterior
    by_contra hnotEmitted
    have hsubset :
        (emitted.filter fun x =>
          x ∈ interiorEdgeSupport
            twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces) ⊆
          twoBandAnnulusInteriorEdges.erase e := by
      intro x hx
      rcases Finset.mem_filter.1 hx with ⟨hxEmitted, hxInteriorSupport⟩
      have hxInterior : x ∈ twoBandAnnulusInteriorEdges := by
        simpa [twoBandAnnulus_interiorEdgeSupport_eq] using hxInteriorSupport
      have hxne : x ≠ e := by
        intro hxe
        subst x
        exact hnotEmitted hxEmitted
      exact Finset.mem_erase.2 ⟨hxne, hxInterior⟩
    have hle :=
      Finset.card_le_card hsubset
    have herase : (twoBandAnnulusInteriorEdges.erase e).card = 8 := by
      have hcardInterior : twoBandAnnulusInteriorEdges.card = 9 := by
        decide
      rw [Finset.card_erase_of_mem heInterior, hcardInterior]
    rw [herase] at hle
    omega
  · intro hsubset
    have hsubsetFilter :
        twoBandAnnulusInteriorEdges ⊆
          emitted.filter fun e =>
            e ∈ interiorEdgeSupport
              twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces := by
      intro e heInterior
      exact Finset.mem_filter.2
        ⟨hsubset heInterior,
          by simpa [twoBandAnnulus_interiorEdgeSupport_eq] using heInterior⟩
    have hle :=
      Finset.card_le_card hsubsetFilter
    have hcardInterior : twoBandAnnulusInteriorEdges.card = 9 := by
      decide
    simpa [hcardInterior] using hle

/-- Exact classifier-facing form of the two-band F2 verdict.  Boundary-zero CAP5 coverage
occurs exactly when the classifier emits all nine interior controls. -/
theorem twoBandAnnulus_CAP5_forcedEdgeCoverage_emits_interiorEdges
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 9 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
        z ≠ 0 →
          ∃ e : twoBandAnnulusGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    twoBandAnnulusInteriorEdges ⊆ classifier.emittedFinset :=
  (twoBandAnnulus_emittedInterior_card_ge_nine_iff classifier.emittedFinset).1
    (twoBandAnnulus_CAP5_forcedEdgeCoverage_emittedInterior_card_ge_nine
      p0Inside p4Inside side classifier hcoverage)

/-- Converse finite-lab handoff for the two-band shell: if the CAP5 classifier emits every
interior edge, then its enumerated forced-edge predicate covers every nonzero boundary-zero
chain. -/
theorem twoBandAnnulus_CAP5_forcedEdgeCoverage_of_emits_interiorEdges
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 9 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : twoBandAnnulusInteriorEdges ⊆ classifier.emittedFinset) :
    ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
      z ≠ 0 →
        ∃ e : twoBandAnnulusGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 :=
  data.forcedEdgeCoverage_of_controlEdges_subset_emittedFinset
    twoBandAnnulusEmbedding classifier twoBandAnnulusInteriorEdges
    twoBandAnnulus_boundaryZero_declaredForcedEdges_nonzeroCoverage hemits

/-- Exact two-band boundary-zero F2 detector verdict.  CAP5 covers every nonzero boundary-zero
chain exactly when all nine interior controls have been emitted. -/
theorem twoBandAnnulus_CAP5_forcedEdgeCoverage_iff_emits_interiorEdges
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 9 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
      z ≠ 0 →
        ∃ e : twoBandAnnulusGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      twoBandAnnulusInteriorEdges ⊆ classifier.emittedFinset := by
  constructor
  · exact twoBandAnnulus_CAP5_forcedEdgeCoverage_emits_interiorEdges
      p0Inside p4Inside side classifier
  · exact twoBandAnnulus_CAP5_forcedEdgeCoverage_of_emits_interiorEdges
      p0Inside p4Inside side classifier

/-- Runner-facing exact two-band threshold: boundary-zero coverage is equivalent to reaching
the nine-edge emitted-interior count. -/
theorem twoBandAnnulus_CAP5_forcedEdgeCoverage_iff_emittedInterior_card_ge_nine
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 9 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
      z ≠ 0 →
        ∃ e : twoBandAnnulusGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      9 ≤ (classifier.emittedFinset.filter fun e =>
        e ∈ interiorEdgeSupport
          twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces).card :=
  (twoBandAnnulus_CAP5_forcedEdgeCoverage_iff_emits_interiorEdges
    p0Inside p4Inside side classifier).trans
    (twoBandAnnulus_emittedInterior_card_ge_nine_iff classifier.emittedFinset).symm

/-- Runner-facing exact form for the two-band shell: exact boundary-zero CAP5 coverage leaves
no unprocessed interior-support control edge. -/
theorem twoBandAnnulus_CAP5_forcedEdgeCoverage_remainingInteriorEdges_eq_empty
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 9 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule twoBandAnnulusEmbedding →
        z ≠ 0 →
          ∃ e : twoBandAnnulusGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    classifier.remainingControlEdges twoBandAnnulusInteriorEdges = ∅ := by
  have hsubset :
      twoBandAnnulusInteriorEdges ⊆ classifier.emittedFinset :=
    twoBandAnnulus_CAP5_forcedEdgeCoverage_emits_interiorEdges
      p0Inside p4Inside side classifier hcoverage
  ext e
  constructor
  · intro he
    have he' :=
      (classifier.mem_remainingControlEdges_iff twoBandAnnulusInteriorEdges e).1 he
    exact False.elim (he'.2 (hsubset he'.1))
  · intro he
    simp at he

/-- Shell-specialized detector bound for the two-band stress shell.  Kirchhoff coverage on the
three middle vertices must emit at least six coordinates. -/
theorem twoBandAnnulus_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_emittedFinset_card_ge_six
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 9 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
        z ≠ 0 →
          ∃ e : twoBandAnnulusGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    6 ≤ classifier.emittedFinset.card := by
  have hge :=
    data.edge_card_le_emittedFinset_card_add_boundary_card_add_vertex_card_of_forcedEdgeKirchhoffCoverage
      twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices
      p0Inside p4Inside side classifier hcoverage
  have hboundary :
      Fintype.card {e : twoBandAnnulusGraph.edgeSet //
        e ∈ selectedBoundarySupport twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces} = 6 := by
    rw [twoBandAnnulus_selectedBoundarySupport_eq]
    decide
  have hvertices :
      Fintype.card {v : Fin 9 // v ∈ twoBandAnnulusKirchhoffVertices} = 3 := by
    decide
  have hedge : Fintype.card twoBandAnnulusGraph.edgeSet = 15 := by
    decide
  rw [hboundary, hvertices, hedge] at hge
  omega

/-- Two-band Kirchhoff detector bound with boundary emissions trimmed away.  Kirchhoff coverage
must emit at least six interior coordinates; selected-boundary emissions vanish automatically for
boundary-zero chains. -/
theorem twoBandAnnulus_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_emittedInterior_card_ge_six
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 9 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace
            twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
        z ≠ 0 →
          ∃ e : twoBandAnnulusGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    6 ≤ (classifier.emittedFinset.filter fun e =>
      e ∈ interiorEdgeSupport
        twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces).card := by
  refine
    twoBandAnnulus_boundaryZeroKirchhoff_classifierControl_emittedInterior_card_ge_six
      classifier ?_
  intro z hz hvanishEmitted
  by_contra hzNonzero
  rcases hcoverage hz hzNonzero with ⟨e, hforced, hze⟩
  exact hze (hvanishEmitted e ((classifier.emittedFinset_spec e).2 hforced))

/-- Positive Kirchhoff handoff for one lab-certified two-band minimum control set.  Emitting the
three middle chords and three outer radials closes coverage of every nonzero boundary-zero
Kirchhoff chain. -/
theorem twoBandAnnulus_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_of_emits_middleOuterRadialControl
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 9 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits :
      twoBandAnnulusMiddleOuterRadialKirchhoffControlEdges ⊆ classifier.emittedFinset) :
    ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
      z ≠ 0 →
        ∃ e : twoBandAnnulusGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 :=
  (data.forcedEdgeKirchhoffCoverage_iff_enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl
    twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices classifier).2
    (by
      intro z hz hvanishEmitted
      exact twoBandAnnulus_boundaryZeroKirchhoff_no_evader_of_middleOuterRadialControl
        z hz (by
          intro e heControl
          exact hvanishEmitted e (hemits heControl)))

/-- Low-cardinality refutation for the two-band Kirchhoff detector: five emitted coordinates do
not cover the boundary-zero Kirchhoff target. -/
theorem twoBandAnnulus_CAP5_boundaryZeroKirchhoff_not_forcedEdgeCoverage_of_emittedFinset_card_le_five
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 9 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard : classifier.emittedFinset.card ≤ 5) :
    ¬ ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
      z ≠ 0 →
        ∃ e : twoBandAnnulusGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 := by
  intro hcoverage
  have hge :=
    twoBandAnnulus_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_emittedFinset_card_ge_six
      p0Inside p4Inside side classifier hcoverage
  omega

/-- Low-interior-emission refutation for the two-band Kirchhoff detector. -/
theorem twoBandAnnulus_CAP5_boundaryZeroKirchhoff_not_forcedEdgeCoverage_of_emittedInterior_card_le_five
    {boundaryEdge : Fin 5 → twoBandAnnulusGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 9 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard :
      (classifier.emittedFinset.filter fun e =>
        e ∈ interiorEdgeSupport
          twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces).card ≤ 5) :
    ¬ ∀ ⦃z : twoBandAnnulusGraph.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace
          twoBandAnnulusEmbedding twoBandAnnulusKirchhoffVertices →
      z ≠ 0 →
        ∃ e : twoBandAnnulusGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 := by
  intro hcoverage
  have hge :=
    twoBandAnnulus_CAP5_boundaryZeroKirchhoff_forcedEdgeCoverage_emittedInterior_card_ge_six
      p0Inside p4Inside side classifier hcoverage
  omega

/-- Exact classifier-facing form of the wheel focus-shell F₂ verdict.  The CAP5 forced-edge
predicate covers all nonzero selected-boundary-zero chains exactly when the classifier emits the
three lab-certified spoke controls. -/
theorem wheelWithInnerTriangle_CAP5_forcedEdgeCoverage_iff_emits_interiorControlEdges
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
      z ≠ 0 →
        ∃ e : wheelWithInnerTriangleGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      wheelWithInnerTriangleInteriorControlEdges ⊆ classifier.emittedFinset := by
  constructor
  · exact wheelWithInnerTriangle_CAP5_forcedEdgeCoverage_emits_interiorControlEdges
      p0Inside p4Inside side classifier
  · exact wheelWithInnerTriangle_CAP5_forcedEdgeCoverage_of_emits_interiorControlEdges
      p0Inside p4Inside side classifier

/-- Runner-facing exact form for the wheel focus shell: exact CAP5 coverage leaves no
unprocessed canonical spoke control edge. -/
theorem wheelWithInnerTriangle_CAP5_forcedEdgeCoverage_remainingInteriorControlEdges_eq_empty
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        z ≠ 0 →
          ∃ e : wheelWithInnerTriangleGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    classifier.remainingControlEdges wheelWithInnerTriangleInteriorControlEdges = ∅ := by
  have hsubset :
      wheelWithInnerTriangleInteriorControlEdges ⊆ classifier.emittedFinset :=
    wheelWithInnerTriangle_CAP5_forcedEdgeCoverage_emits_interiorControlEdges
      p0Inside p4Inside side classifier hcoverage
  ext e
  constructor
  · intro he
    have he' :=
      (classifier.mem_remainingControlEdges_iff wheelWithInnerTriangleInteriorControlEdges e).1 he
    exact False.elim (he'.2 (hsubset he'.1))
  · intro he
    simp at he

/-- Path-xor cardinality branch obstruction for the shared focus shell.  Exact CAP5 coverage
emits every canonical shared-interior control edge, so the emitted classifier cannot still be
below the selected-boundary-zero dimension threshold. -/
theorem sharedInteriorPair_CAP5_forcedEdgeCoverage_no_emittedFinset_card_add_boundary_card_lt
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        z ≠ 0 →
          ∃ e : sharedInteriorPairGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    ¬ (classifier.emittedFinset.card +
        Fintype.card {e : sharedInteriorPairGraph.edgeSet //
          e ∈ selectedBoundarySupport sharedInteriorPairEmbedding.faceBoundary
            sharedInteriorPairEmbedding.faces sharedInteriorPairEmbedding.faces} <
      Fintype.card sharedInteriorPairGraph.edgeSet) := by
  intro hcard
  have hnonempty :
      (classifier.remainingControlEdges sharedInteriorPairInteriorControlEdges).Nonempty :=
    data.remainingControlEdges_nonempty_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      sharedInteriorPairEmbedding p0Inside p4Inside side classifier
      sharedInteriorPairInteriorControlEdges hcard
      sharedInteriorPair_boundaryZero_controlEdges_interiorEdges
  have hempty :
      classifier.remainingControlEdges sharedInteriorPairInteriorControlEdges = ∅ :=
    sharedInteriorPair_CAP5_forcedEdgeCoverage_remainingInteriorControlEdges_eq_empty
      p0Inside p4Inside side classifier hcoverage
  rw [hempty] at hnonempty
  simp at hnonempty

/-- Path-xor cardinality branch obstruction for the wheel focus shell.  Exact CAP5 coverage
emits every canonical spoke control edge, so the emitted classifier cannot still be below the
selected-boundary-zero dimension threshold. -/
theorem wheelWithInnerTriangle_CAP5_forcedEdgeCoverage_no_emittedFinset_card_add_boundary_card_lt
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        z ≠ 0 →
          ∃ e : wheelWithInnerTriangleGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    ¬ (classifier.emittedFinset.card +
        Fintype.card {e : wheelWithInnerTriangleGraph.edgeSet //
          e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
            wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces} <
      Fintype.card wheelWithInnerTriangleGraph.edgeSet) := by
  intro hcard
  have hnonempty :
      (classifier.remainingControlEdges wheelWithInnerTriangleInteriorControlEdges).Nonempty :=
    data.remainingControlEdges_nonempty_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      wheelWithInnerTriangleEmbedding p0Inside p4Inside side classifier
      wheelWithInnerTriangleInteriorControlEdges hcard
      wheelWithInnerTriangle_boundaryZero_controlEdges_interiorEdges
  have hempty :
      classifier.remainingControlEdges wheelWithInnerTriangleInteriorControlEdges = ∅ :=
    wheelWithInnerTriangle_CAP5_forcedEdgeCoverage_remainingInteriorControlEdges_eq_empty
      p0Inside p4Inside side classifier hcoverage
  rw [hempty] at hnonempty
  simp at hnonempty

/-- Classifier-control form for the shared focus shell: exact CAP5 forced-edge coverage makes the
emitted classifier output control every selected-boundary-zero chain. -/
theorem sharedInteriorPair_CAP5_classifierControl_of_forcedEdgeCoverage
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        z ≠ 0 →
          ∃ e : sharedInteriorPairGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0 :=
  data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_forcedEdgeCoverage
    sharedInteriorPairEmbedding classifier hcoverage

/-- Classifier-control form for the shared focus shell with the F₂ lab verdict discharged:
emitting the two lab-certified shared-interior controls makes the classifier output control every
selected-boundary-zero chain. -/
theorem sharedInteriorPair_CAP5_classifierControl_of_emits_interiorControlEdges
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : sharedInteriorPairInteriorControlEdges ⊆ classifier.emittedFinset) :
    ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0 :=
  data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_controlEdges_nonzeroCoverage_subset_emittedFinset
    sharedInteriorPairEmbedding classifier sharedInteriorPairInteriorControlEdges
    sharedInteriorPair_boundaryZero_declaredForcedEdges_nonzeroCoverage hemits

/-- Boundary-root synthesis endpoint for the shared focus shell.  Exact CAP5 forced-edge coverage,
together with projected red/blue witnesses on every emitted classifier edge, closes the Theorem
4.9 boundary-root synthesis route. -/
theorem sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (colorings : Set (sharedInteriorPairGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ sharedInteriorPairGraph.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings)
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        z ≠ 0 →
          ∃ e : sharedInteriorPairGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
    (hwitnessRed :
      ∀ e : sharedInteriorPairGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i :
                projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings) :
                sharedInteriorPairGraph.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : sharedInteriorPairGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i :
                projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings) :
                sharedInteriorPairGraph.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀ :=
  data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage
    sharedInteriorPairEmbedding C₀ colorings hsubset family p0Inside p4Inside side
    classifier hcoverage hwitnessRed hwitnessBlue

/-- Boundary-root synthesis endpoint for the shared focus shell with the finite F₂ verdict
discharged: once the classifier emits both lab-certified shared-interior controls, only red/blue
single-coordinate witnesses on the classifier output remain. -/
theorem sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_of_emits_interiorControlEdges
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (colorings : Set (sharedInteriorPairGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ sharedInteriorPairGraph.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings)
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : sharedInteriorPairInteriorControlEdges ⊆ classifier.emittedFinset)
    (hwitnessRed :
      ∀ e : sharedInteriorPairGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i :
                projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings) :
                sharedInteriorPairGraph.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : sharedInteriorPairGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i :
                projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings) :
                sharedInteriorPairGraph.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀ :=
  data.theorem49BoundaryRootSynthesis_of_controlEdges_nonzeroCoverage_subset_emittedFinset
    sharedInteriorPairEmbedding C₀ colorings hsubset family p0Inside p4Inside side
    classifier sharedInteriorPairInteriorControlEdges
    sharedInteriorPair_boundaryZero_declaredForcedEdges_nonzeroCoverage hemits
    hwitnessRed hwitnessBlue

/-- Concrete certificate-family endpoint for the shared focus shell.  If the CAP5 classifier
emits exactly within the two lab-certified controls, the unique projected-bicolored certificate
family supplies all red/blue witnesses needed by the emitted-control synthesis endpoint. -/
theorem sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_of_exact_interiorControlEdges_uniqueCertificates
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (hsubset :
      sharedInteriorPairProjectedGeneratorCertificateColorings ⊆
        sharedInteriorPairGraph.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : sharedInteriorPairInteriorControlEdges ⊆ classifier.emittedFinset)
    (honlyEmits : classifier.emittedFinset ⊆ sharedInteriorPairInteriorControlEdges) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀ :=
  sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_of_emits_interiorControlEdges
    C₀ sharedInteriorPairProjectedGeneratorCertificateColorings hsubset
    sharedInteriorPairUniqueCertificateRedBlueFamily p0Inside p4Inside side classifier hemits
    (by
      intro e he
      exact (redBlueSingleCoordinateFamily_witnessRed sharedInteriorPairInteriorControlEdges
        sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
        sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2)
        e (honlyEmits he))
    (by
      intro e he
      exact (redBlueSingleCoordinateFamily_witnessBlue sharedInteriorPairInteriorControlEdges
        sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
        sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2)
        e (honlyEmits he))

/-- Finite-checker success endpoint for the shared focus shell.  If the extension bins are empty
for the two lab-certified controls, and the classifier emits no edge outside those controls, the
unique certificate family closes Theorem 4.9 synthesis. -/
theorem sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_of_extensionFinsets_eq_empty_uniqueCertificates
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (hsubset :
      sharedInteriorPairProjectedGeneratorCertificateColorings ⊆
        sharedInteriorPairGraph.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcrossingEmpty :
      classifier.crossingExtensionFinset sharedInteriorPairInteriorControlEdges = ∅)
    (hnoncrossingEmpty :
      classifier.noncrossingExtensionFinset sharedInteriorPairInteriorControlEdges = ∅)
    (honlyEmits : classifier.emittedFinset ⊆ sharedInteriorPairInteriorControlEdges) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀ := by
  have hemits : sharedInteriorPairInteriorControlEdges ⊆ classifier.emittedFinset :=
    (classifier.controlEdges_subset_emittedFinset_iff_extensionFinsets_eq_empty
      sharedInteriorPairInteriorControlEdges).2
      ⟨hcrossingEmpty, hnoncrossingEmpty⟩
  exact
    sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_of_exact_interiorControlEdges_uniqueCertificates
      C₀ hsubset p0Inside p4Inside side classifier hemits honlyEmits

/--
Finite-checker success endpoint for the shared focus shell with extra emissions.  Empty
extension bins make the two lab-certified controls available; the canonical certificate family
covers those controls, and the supplied extra family covers every emitted edge outside them.
-/
theorem sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_of_extensionFinsets_eq_empty_uniqueCertificates_extraWitnesses
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (hsubset :
      sharedInteriorPairProjectedGeneratorCertificateColorings ⊆
        sharedInteriorPairGraph.EdgeKempeClosure C₀)
    {κextra : Type*}
    (extraFamily :
      κextra → projectedColoringGeneratorSubspace sharedInteriorPairEmbedding
        sharedInteriorPairProjectedGeneratorCertificateColorings)
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcrossingEmpty :
      classifier.crossingExtensionFinset sharedInteriorPairInteriorControlEdges = ∅)
    (hnoncrossingEmpty :
      classifier.noncrossingExtensionFinset sharedInteriorPairInteriorControlEdges = ∅)
    (hwitnessExtraRed :
      ∀ e : sharedInteriorPairGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          e ∉ sharedInteriorPairInteriorControlEdges →
            ∃ i : κextra,
              ((extraFamily i :
                  projectedColoringGeneratorSubspace sharedInteriorPairEmbedding
                    sharedInteriorPairProjectedGeneratorCertificateColorings) :
                  sharedInteriorPairGraph.edgeSet → Color) =
                Pi.single e red)
    (hwitnessExtraBlue :
      ∀ e : sharedInteriorPairGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          e ∉ sharedInteriorPairInteriorControlEdges →
            ∃ i : κextra,
              ((extraFamily i :
                  projectedColoringGeneratorSubspace sharedInteriorPairEmbedding
                    sharedInteriorPairProjectedGeneratorCertificateColorings) :
                  sharedInteriorPairGraph.edgeSet → Color) =
                Pi.single e blue) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀ :=
  data.theorem49BoundaryRootSynthesis_of_controlEdges_nonzeroCoverage_extensionFinsets_eq_empty_splitWitnesses
    sharedInteriorPairEmbedding C₀ sharedInteriorPairProjectedGeneratorCertificateColorings
    hsubset sharedInteriorPairUniqueCertificateRedBlueFamily extraFamily
    p0Inside p4Inside side classifier sharedInteriorPairInteriorControlEdges
    sharedInteriorPair_boundaryZero_declaredForcedEdges_nonzeroCoverage
    hcrossingEmpty hnoncrossingEmpty
    (by
      intro e he
      rcases redBlueSingleCoordinateFamily_witnessRed sharedInteriorPairInteriorControlEdges
          sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
          sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2
          e he with
        ⟨i, hi⟩
      exact ⟨i, by simpa [sharedInteriorPairUniqueCertificateRedBlueFamily] using hi⟩)
    (by
      intro e he
      rcases redBlueSingleCoordinateFamily_witnessBlue sharedInteriorPairInteriorControlEdges
          sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
          sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2
          e he with
        ⟨i, hi⟩
      exact ⟨i, by simpa [sharedInteriorPairUniqueCertificateRedBlueFamily] using hi⟩)
    hwitnessExtraRed hwitnessExtraBlue

/--
Boundary-trimmed kernel endpoint for the shared focus shell.  Once CAP5 emits the two
lab-certified controls, the canonical red/blue certificate family has trivial selected-
boundary-zero pairing kernel; selected-boundary-only extra emissions require no probes.
-/
theorem sharedInteriorPair_CAP5_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificates_of_emits_interiorControlEdges_boundaryTrimmed
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : sharedInteriorPairInteriorControlEdges ⊆ classifier.emittedFinset) :
    LinearMap.ker
        (planarBoundaryZeroFamilyPairingMap
          sharedInteriorPairUniqueCertificateRedBlueFamily) = ⊥ :=
  ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_controlEdges_nonBoundaryWitnesses
    sharedInteriorPairUniqueCertificateRedBlueFamily classifier.emittedFinset
    (sharedInteriorPair_CAP5_classifierControl_of_emits_interiorControlEdges
      p0Inside p4Inside side classifier hemits)
    (by
      intro e _heEmitted heNotBoundary
      have heInteriorSupport :
          e ∈ interiorEdgeSupport
            sharedInteriorPairEmbedding.faceBoundary sharedInteriorPairEmbedding.faces := by
        by_contra hnotInterior
        exact heNotBoundary
          (sharedInteriorPair_mem_selectedBoundarySupport_of_not_mem_interiorEdgeSupport
            hnotInterior)
      have heControl : e ∈ sharedInteriorPairInteriorControlEdges := by
        simpa [sharedInteriorPairInteriorControlEdges, sharedInteriorPair_interiorEdgeSupport_eq]
          using heInteriorSupport
      rcases redBlueSingleCoordinateFamily_witnessRed sharedInteriorPairInteriorControlEdges
          sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
          sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2
          e heControl with
        ⟨i, hi⟩
      exact ⟨i, by simpa [sharedInteriorPairUniqueCertificateRedBlueFamily] using hi⟩)
    (by
      intro e _heEmitted heNotBoundary
      have heInteriorSupport :
          e ∈ interiorEdgeSupport
            sharedInteriorPairEmbedding.faceBoundary sharedInteriorPairEmbedding.faces := by
        by_contra hnotInterior
        exact heNotBoundary
          (sharedInteriorPair_mem_selectedBoundarySupport_of_not_mem_interiorEdgeSupport
            hnotInterior)
      have heControl : e ∈ sharedInteriorPairInteriorControlEdges := by
        simpa [sharedInteriorPairInteriorControlEdges, sharedInteriorPair_interiorEdgeSupport_eq]
          using heInteriorSupport
      rcases redBlueSingleCoordinateFamily_witnessBlue sharedInteriorPairInteriorControlEdges
          sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
          sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2
          e heControl with
        ⟨i, hi⟩
      exact ⟨i, by simpa [sharedInteriorPairUniqueCertificateRedBlueFamily] using hi⟩)

/--
Boundary-trimmed finite-checker endpoint for the shared focus shell.  Once CAP5 emits the two
lab-certified controls, extra emitted edges on the selected boundary need no projected-generator
certificates: every selected-boundary-zero chain is already zero there.
-/
theorem sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_of_emits_interiorControlEdges_uniqueCertificates_boundaryTrimmed
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (hsubset :
      sharedInteriorPairProjectedGeneratorCertificateColorings ⊆
        sharedInteriorPairGraph.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : sharedInteriorPairInteriorControlEdges ⊆ classifier.emittedFinset) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀ :=
  theorem49BoundaryRootSynthesis_of_familyPairingKerEqBot
    sharedInteriorPairEmbedding C₀ sharedInteriorPairProjectedGeneratorCertificateColorings
    hsubset sharedInteriorPairUniqueCertificateRedBlueFamily
    (sharedInteriorPair_CAP5_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificates_of_emits_interiorControlEdges_boundaryTrimmed
      p0Inside p4Inside side classifier hemits)

/--
Boundary-trimmed fixed-point kernel endpoint for the shared focus shell.  Empty extension bins
make the two lab-certified controls emitted, and the canonical certificate family already has a
trivial selected-boundary-zero pairing kernel.
-/
theorem sharedInteriorPair_CAP5_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificates_of_extensionFinsets_eq_empty_boundaryTrimmed
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcrossingEmpty :
      classifier.crossingExtensionFinset sharedInteriorPairInteriorControlEdges = ∅)
    (hnoncrossingEmpty :
      classifier.noncrossingExtensionFinset sharedInteriorPairInteriorControlEdges = ∅) :
    LinearMap.ker
        (planarBoundaryZeroFamilyPairingMap
          sharedInteriorPairUniqueCertificateRedBlueFamily) = ⊥ := by
  have hemits : sharedInteriorPairInteriorControlEdges ⊆ classifier.emittedFinset :=
    (classifier.controlEdges_subset_emittedFinset_iff_extensionFinsets_eq_empty
      sharedInteriorPairInteriorControlEdges).2
      ⟨hcrossingEmpty, hnoncrossingEmpty⟩
  exact
    sharedInteriorPair_CAP5_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificates_of_emits_interiorControlEdges_boundaryTrimmed
      p0Inside p4Inside side classifier hemits

/--
Boundary-trimmed fixed-point endpoint for the shared focus shell.  Empty extension bins make the
two lab-certified controls emitted; any additional emitted edge is selected-boundary-only and
therefore invisible to boundary-zero chains.
-/
theorem sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_of_extensionFinsets_eq_empty_uniqueCertificates_boundaryTrimmed
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (hsubset :
      sharedInteriorPairProjectedGeneratorCertificateColorings ⊆
        sharedInteriorPairGraph.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcrossingEmpty :
      classifier.crossingExtensionFinset sharedInteriorPairInteriorControlEdges = ∅)
    (hnoncrossingEmpty :
      classifier.noncrossingExtensionFinset sharedInteriorPairInteriorControlEdges = ∅) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀ :=
  theorem49BoundaryRootSynthesis_of_familyPairingKerEqBot
    sharedInteriorPairEmbedding C₀ sharedInteriorPairProjectedGeneratorCertificateColorings
    hsubset sharedInteriorPairUniqueCertificateRedBlueFamily
    (sharedInteriorPair_CAP5_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificates_of_extensionFinsets_eq_empty_boundaryTrimmed
      p0Inside p4Inside side classifier hcrossingEmpty hnoncrossingEmpty)

/-- Failed finite-checker diagnostic for the shared focus shell.  Once the extension bins are
empty for the two lab-certified controls, a failed unique-certificate synthesis run must expose
an extra emitted classifier edge outside the certified control set. -/
theorem sharedInteriorPair_CAP5_exists_extra_emittedEdge_of_not_theorem49BoundaryRootSynthesis_of_extensionFinsets_eq_empty_uniqueCertificates
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (hsubset :
      sharedInteriorPairProjectedGeneratorCertificateColorings ⊆
        sharedInteriorPairGraph.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcrossingEmpty :
      classifier.crossingExtensionFinset sharedInteriorPairInteriorControlEdges = ∅)
    (hnoncrossingEmpty :
      classifier.noncrossingExtensionFinset sharedInteriorPairInteriorControlEdges = ∅)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀) :
    ∃ e : sharedInteriorPairGraph.edgeSet,
      e ∈ classifier.emittedFinset ∧ e ∉ sharedInteriorPairInteriorControlEdges := by
  classical
  by_contra hnoExtra
  have honlyEmits : classifier.emittedFinset ⊆ sharedInteriorPairInteriorControlEdges := by
    intro e he
    by_contra hnotControl
    exact hnoExtra ⟨e, he, hnotControl⟩
  exact hnotSynthesis
    (sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_of_extensionFinsets_eq_empty_uniqueCertificates
      C₀ hsubset p0Inside p4Inside side classifier hcrossingEmpty hnoncrossingEmpty
      honlyEmits)

/-- Certificate-facing failed finite-checker diagnostic for the shared focus shell.  Under empty
extension bins, a failed unique-certificate synthesis run must expose an emitted edge outside the
lab-certified controls that is missing a red or blue probe in the unique certificate family. -/
theorem sharedInteriorPair_CAP5_exists_extra_emittedEdge_missing_red_or_blue_uniqueCertificateWitness_of_not_theorem49BoundaryRootSynthesis_of_extensionFinsets_eq_empty
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (hsubset :
      sharedInteriorPairProjectedGeneratorCertificateColorings ⊆
        sharedInteriorPairGraph.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcrossingEmpty :
      classifier.crossingExtensionFinset sharedInteriorPairInteriorControlEdges = ∅)
    (hnoncrossingEmpty :
      classifier.noncrossingExtensionFinset sharedInteriorPairInteriorControlEdges = ∅)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀) :
    (∃ e : sharedInteriorPairGraph.edgeSet,
      e ∈ classifier.emittedFinset ∧ e ∉ sharedInteriorPairInteriorControlEdges ∧
        ¬ ∃ i : ({e : sharedInteriorPairGraph.edgeSet //
            e ∈ sharedInteriorPairInteriorControlEdges} × Bool),
          ((sharedInteriorPairUniqueCertificateRedBlueFamily i :
              projectedColoringGeneratorSubspace sharedInteriorPairEmbedding
                sharedInteriorPairProjectedGeneratorCertificateColorings) :
              sharedInteriorPairGraph.edgeSet → Color) =
            Pi.single e red) ∨
      ∃ e : sharedInteriorPairGraph.edgeSet,
        e ∈ classifier.emittedFinset ∧ e ∉ sharedInteriorPairInteriorControlEdges ∧
          ¬ ∃ i : ({e : sharedInteriorPairGraph.edgeSet //
              e ∈ sharedInteriorPairInteriorControlEdges} × Bool),
            ((sharedInteriorPairUniqueCertificateRedBlueFamily i :
                projectedColoringGeneratorSubspace sharedInteriorPairEmbedding
                  sharedInteriorPairProjectedGeneratorCertificateColorings) :
                sharedInteriorPairGraph.edgeSet → Color) =
              Pi.single e blue := by
  classical
  by_contra hnoGap
  have hemits : sharedInteriorPairInteriorControlEdges ⊆ classifier.emittedFinset :=
    (classifier.controlEdges_subset_emittedFinset_iff_extensionFinsets_eq_empty
      sharedInteriorPairInteriorControlEdges).2
      ⟨hcrossingEmpty, hnoncrossingEmpty⟩
  have hred :
      ∀ e : sharedInteriorPairGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : ({e : sharedInteriorPairGraph.edgeSet //
              e ∈ sharedInteriorPairInteriorControlEdges} × Bool),
            ((sharedInteriorPairUniqueCertificateRedBlueFamily i :
                projectedColoringGeneratorSubspace sharedInteriorPairEmbedding
                  sharedInteriorPairProjectedGeneratorCertificateColorings) :
                sharedInteriorPairGraph.edgeSet → Color) =
              Pi.single e red := by
    intro e he
    by_cases heControl : e ∈ sharedInteriorPairInteriorControlEdges
    · exact (redBlueSingleCoordinateFamily_witnessRed sharedInteriorPairInteriorControlEdges
        sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
        sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2)
        e heControl
    · by_contra hmissing
      exact hnoGap (Or.inl ⟨e, he, heControl, hmissing⟩)
  have hblue :
      ∀ e : sharedInteriorPairGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : ({e : sharedInteriorPairGraph.edgeSet //
              e ∈ sharedInteriorPairInteriorControlEdges} × Bool),
            ((sharedInteriorPairUniqueCertificateRedBlueFamily i :
                projectedColoringGeneratorSubspace sharedInteriorPairEmbedding
                  sharedInteriorPairProjectedGeneratorCertificateColorings) :
                sharedInteriorPairGraph.edgeSet → Color) =
              Pi.single e blue := by
    intro e he
    by_cases heControl : e ∈ sharedInteriorPairInteriorControlEdges
    · exact (redBlueSingleCoordinateFamily_witnessBlue sharedInteriorPairInteriorControlEdges
        sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
        sharedInteriorPair_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2)
        e heControl
    · by_contra hmissing
      exact hnoGap (Or.inr ⟨e, he, heControl, hmissing⟩)
  exact hnotSynthesis
    (sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_of_emits_interiorControlEdges
      C₀ sharedInteriorPairProjectedGeneratorCertificateColorings hsubset
      sharedInteriorPairUniqueCertificateRedBlueFamily p0Inside p4Inside side classifier
      hemits hred hblue)

/-- Classifier-control form for the wheel focus shell: exact CAP5 forced-edge coverage makes the
emitted classifier output control every selected-boundary-zero chain. -/
theorem wheelWithInnerTriangle_CAP5_classifierControl_of_forcedEdgeCoverage
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        z ≠ 0 →
          ∃ e : wheelWithInnerTriangleGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0 :=
  data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_forcedEdgeCoverage
    wheelWithInnerTriangleEmbedding classifier hcoverage

/-- Classifier-control form for the wheel focus shell with the F₂ lab verdict discharged:
emitting the three lab-certified spoke controls makes the classifier output control every
selected-boundary-zero chain. -/
theorem wheelWithInnerTriangle_CAP5_classifierControl_of_emits_interiorControlEdges
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : wheelWithInnerTriangleInteriorControlEdges ⊆ classifier.emittedFinset) :
    ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0 :=
  data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_controlEdges_nonzeroCoverage_subset_emittedFinset
    wheelWithInnerTriangleEmbedding classifier wheelWithInnerTriangleInteriorControlEdges
    wheelWithInnerTriangle_boundaryZero_declaredForcedEdges_nonzeroCoverage hemits

/-- Boundary-root synthesis endpoint for the wheel focus shell.  Exact CAP5 forced-edge coverage,
together with projected red/blue witnesses on every emitted classifier edge, closes the Theorem
4.9 boundary-root synthesis route. -/
theorem wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (colorings : Set (wheelWithInnerTriangleGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings)
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        z ≠ 0 →
          ∃ e : wheelWithInnerTriangleGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
    (hwitnessRed :
      ∀ e : wheelWithInnerTriangleGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i :
                projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings) :
                wheelWithInnerTriangleGraph.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : wheelWithInnerTriangleGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i :
                projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings) :
                wheelWithInnerTriangleGraph.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀ :=
  data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage
    wheelWithInnerTriangleEmbedding C₀ colorings hsubset family p0Inside p4Inside side
    classifier hcoverage hwitnessRed hwitnessBlue

/-- Boundary-root synthesis endpoint for the wheel focus shell with the finite F₂ verdict
discharged: once the classifier emits all three lab-certified spoke controls, only red/blue
single-coordinate witnesses on the classifier output remain. -/
theorem wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_of_emits_interiorControlEdges
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (colorings : Set (wheelWithInnerTriangleGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings)
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : wheelWithInnerTriangleInteriorControlEdges ⊆ classifier.emittedFinset)
    (hwitnessRed :
      ∀ e : wheelWithInnerTriangleGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i :
                projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings) :
                wheelWithInnerTriangleGraph.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : wheelWithInnerTriangleGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i :
                projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings) :
                wheelWithInnerTriangleGraph.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀ :=
  data.theorem49BoundaryRootSynthesis_of_controlEdges_nonzeroCoverage_subset_emittedFinset
    wheelWithInnerTriangleEmbedding C₀ colorings hsubset family p0Inside p4Inside side
    classifier wheelWithInnerTriangleInteriorControlEdges
    wheelWithInnerTriangle_boundaryZero_declaredForcedEdges_nonzeroCoverage hemits
    hwitnessRed hwitnessBlue

/-- Concrete certificate-family endpoint for the wheel focus shell.  If the CAP5 classifier emits
exactly within the three lab-certified spokes, the unique projected-bicolored certificate family
supplies all red/blue witnesses needed by the emitted-control synthesis endpoint. -/
theorem wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_of_exact_interiorControlEdges_uniqueCertificates
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hsubset :
      wheelWithInnerTriangleProjectedGeneratorCertificateColorings ⊆
        wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : wheelWithInnerTriangleInteriorControlEdges ⊆ classifier.emittedFinset)
    (honlyEmits : classifier.emittedFinset ⊆ wheelWithInnerTriangleInteriorControlEdges) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀ :=
  wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_of_emits_interiorControlEdges
    C₀ wheelWithInnerTriangleProjectedGeneratorCertificateColorings hsubset
    wheelWithInnerTriangleUniqueCertificateRedBlueFamily p0Inside p4Inside side classifier hemits
    (by
      intro e he
      exact (redBlueSingleCoordinateFamily_witnessRed wheelWithInnerTriangleInteriorControlEdges
        wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
        wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2)
        e (honlyEmits he))
    (by
      intro e he
      exact (redBlueSingleCoordinateFamily_witnessBlue wheelWithInnerTriangleInteriorControlEdges
        wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
        wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2)
        e (honlyEmits he))

/-- Finite-checker success endpoint for the wheel focus shell.  If the extension bins are empty
for the three lab-certified spoke controls, and the classifier emits no edge outside those
controls, the unique certificate family closes Theorem 4.9 synthesis. -/
theorem wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_of_extensionFinsets_eq_empty_uniqueCertificates
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hsubset :
      wheelWithInnerTriangleProjectedGeneratorCertificateColorings ⊆
        wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcrossingEmpty :
      classifier.crossingExtensionFinset wheelWithInnerTriangleInteriorControlEdges = ∅)
    (hnoncrossingEmpty :
      classifier.noncrossingExtensionFinset wheelWithInnerTriangleInteriorControlEdges = ∅)
    (honlyEmits : classifier.emittedFinset ⊆ wheelWithInnerTriangleInteriorControlEdges) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀ := by
  have hemits : wheelWithInnerTriangleInteriorControlEdges ⊆ classifier.emittedFinset :=
    (classifier.controlEdges_subset_emittedFinset_iff_extensionFinsets_eq_empty
      wheelWithInnerTriangleInteriorControlEdges).2
      ⟨hcrossingEmpty, hnoncrossingEmpty⟩
  exact
    wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_of_exact_interiorControlEdges_uniqueCertificates
      C₀ hsubset p0Inside p4Inside side classifier hemits honlyEmits

/--
Finite-checker success endpoint for the wheel focus shell with extra emissions.  Empty extension
bins make the three lab-certified spokes available; the canonical certificate family covers those
spokes, and the supplied extra family covers every emitted edge outside them.
-/
theorem wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_of_extensionFinsets_eq_empty_uniqueCertificates_extraWitnesses
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hsubset :
      wheelWithInnerTriangleProjectedGeneratorCertificateColorings ⊆
        wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    {κextra : Type*}
    (extraFamily :
      κextra → projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding
        wheelWithInnerTriangleProjectedGeneratorCertificateColorings)
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcrossingEmpty :
      classifier.crossingExtensionFinset wheelWithInnerTriangleInteriorControlEdges = ∅)
    (hnoncrossingEmpty :
      classifier.noncrossingExtensionFinset wheelWithInnerTriangleInteriorControlEdges = ∅)
    (hwitnessExtraRed :
      ∀ e : wheelWithInnerTriangleGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          e ∉ wheelWithInnerTriangleInteriorControlEdges →
            ∃ i : κextra,
              ((extraFamily i :
                  projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding
                    wheelWithInnerTriangleProjectedGeneratorCertificateColorings) :
                  wheelWithInnerTriangleGraph.edgeSet → Color) =
                Pi.single e red)
    (hwitnessExtraBlue :
      ∀ e : wheelWithInnerTriangleGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          e ∉ wheelWithInnerTriangleInteriorControlEdges →
            ∃ i : κextra,
              ((extraFamily i :
                  projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding
                    wheelWithInnerTriangleProjectedGeneratorCertificateColorings) :
                  wheelWithInnerTriangleGraph.edgeSet → Color) =
                Pi.single e blue) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀ :=
  data.theorem49BoundaryRootSynthesis_of_controlEdges_nonzeroCoverage_extensionFinsets_eq_empty_splitWitnesses
    wheelWithInnerTriangleEmbedding C₀
    wheelWithInnerTriangleProjectedGeneratorCertificateColorings hsubset
    wheelWithInnerTriangleUniqueCertificateRedBlueFamily extraFamily
    p0Inside p4Inside side classifier wheelWithInnerTriangleInteriorControlEdges
    wheelWithInnerTriangle_boundaryZero_declaredForcedEdges_nonzeroCoverage
    hcrossingEmpty hnoncrossingEmpty
    (by
      intro e he
      rcases redBlueSingleCoordinateFamily_witnessRed wheelWithInnerTriangleInteriorControlEdges
          wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
          wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2
          e he with
        ⟨i, hi⟩
      exact ⟨i, by simpa [wheelWithInnerTriangleUniqueCertificateRedBlueFamily] using hi⟩)
    (by
      intro e he
      rcases redBlueSingleCoordinateFamily_witnessBlue wheelWithInnerTriangleInteriorControlEdges
          wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
          wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2
          e he with
        ⟨i, hi⟩
      exact ⟨i, by simpa [wheelWithInnerTriangleUniqueCertificateRedBlueFamily] using hi⟩)
    hwitnessExtraRed hwitnessExtraBlue

/--
Boundary-trimmed kernel endpoint for the wheel focus shell.  Once CAP5 emits the three
lab-certified spokes, the canonical red/blue certificate family has trivial selected-boundary-zero
pairing kernel; selected-boundary-only extra emissions require no probes.
-/
theorem wheelWithInnerTriangle_CAP5_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificates_of_emits_interiorControlEdges_boundaryTrimmed
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : wheelWithInnerTriangleInteriorControlEdges ⊆ classifier.emittedFinset) :
    LinearMap.ker
        (planarBoundaryZeroFamilyPairingMap
          wheelWithInnerTriangleUniqueCertificateRedBlueFamily) = ⊥ :=
  ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_controlEdges_nonBoundaryWitnesses
    wheelWithInnerTriangleUniqueCertificateRedBlueFamily classifier.emittedFinset
    (wheelWithInnerTriangle_CAP5_classifierControl_of_emits_interiorControlEdges
      p0Inside p4Inside side classifier hemits)
    (by
      intro e _heEmitted heNotBoundary
      have heInteriorSupport :
          e ∈ interiorEdgeSupport
            wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces := by
        by_contra hnotInterior
        exact heNotBoundary
          (wheelWithInnerTriangle_mem_selectedBoundarySupport_of_not_mem_interiorEdgeSupport
            hnotInterior)
      have heControl : e ∈ wheelWithInnerTriangleInteriorControlEdges := by
        simpa [wheelWithInnerTriangleInteriorControlEdges,
          wheelWithInnerTriangle_interiorEdgeSupport_eq] using heInteriorSupport
      rcases redBlueSingleCoordinateFamily_witnessRed wheelWithInnerTriangleInteriorControlEdges
          wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
          wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2
          e heControl with
        ⟨i, hi⟩
      exact ⟨i, by simpa [wheelWithInnerTriangleUniqueCertificateRedBlueFamily] using hi⟩)
    (by
      intro e _heEmitted heNotBoundary
      have heInteriorSupport :
          e ∈ interiorEdgeSupport
            wheelWithInnerTriangleEmbedding.faceBoundary wheelWithInnerTriangleEmbedding.faces := by
        by_contra hnotInterior
        exact heNotBoundary
          (wheelWithInnerTriangle_mem_selectedBoundarySupport_of_not_mem_interiorEdgeSupport
            hnotInterior)
      have heControl : e ∈ wheelWithInnerTriangleInteriorControlEdges := by
        simpa [wheelWithInnerTriangleInteriorControlEdges,
          wheelWithInnerTriangle_interiorEdgeSupport_eq] using heInteriorSupport
      rcases redBlueSingleCoordinateFamily_witnessBlue wheelWithInnerTriangleInteriorControlEdges
          wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
          wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2
          e heControl with
        ⟨i, hi⟩
      exact ⟨i, by simpa [wheelWithInnerTriangleUniqueCertificateRedBlueFamily] using hi⟩)

/--
Boundary-trimmed finite-checker endpoint for the wheel focus shell.  Once CAP5 emits the three
lab-certified spokes, extra emitted edges on the selected boundary need no projected-generator
certificates: every selected-boundary-zero chain is already zero there.
-/
theorem wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_of_emits_interiorControlEdges_uniqueCertificates_boundaryTrimmed
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hsubset :
      wheelWithInnerTriangleProjectedGeneratorCertificateColorings ⊆
        wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hemits : wheelWithInnerTriangleInteriorControlEdges ⊆ classifier.emittedFinset) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀ :=
  theorem49BoundaryRootSynthesis_of_familyPairingKerEqBot
    wheelWithInnerTriangleEmbedding C₀
    wheelWithInnerTriangleProjectedGeneratorCertificateColorings hsubset
    wheelWithInnerTriangleUniqueCertificateRedBlueFamily
    (wheelWithInnerTriangle_CAP5_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificates_of_emits_interiorControlEdges_boundaryTrimmed
      p0Inside p4Inside side classifier hemits)

/--
Boundary-trimmed fixed-point kernel endpoint for the wheel focus shell.  Empty extension bins
make the three lab-certified spokes emitted, and the canonical certificate family already has a
trivial selected-boundary-zero pairing kernel.
-/
theorem wheelWithInnerTriangle_CAP5_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificates_of_extensionFinsets_eq_empty_boundaryTrimmed
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcrossingEmpty :
      classifier.crossingExtensionFinset wheelWithInnerTriangleInteriorControlEdges = ∅)
    (hnoncrossingEmpty :
      classifier.noncrossingExtensionFinset wheelWithInnerTriangleInteriorControlEdges = ∅) :
    LinearMap.ker
        (planarBoundaryZeroFamilyPairingMap
          wheelWithInnerTriangleUniqueCertificateRedBlueFamily) = ⊥ := by
  have hemits : wheelWithInnerTriangleInteriorControlEdges ⊆ classifier.emittedFinset :=
    (classifier.controlEdges_subset_emittedFinset_iff_extensionFinsets_eq_empty
      wheelWithInnerTriangleInteriorControlEdges).2
      ⟨hcrossingEmpty, hnoncrossingEmpty⟩
  exact
    wheelWithInnerTriangle_CAP5_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificates_of_emits_interiorControlEdges_boundaryTrimmed
      p0Inside p4Inside side classifier hemits

/--
Boundary-trimmed fixed-point endpoint for the wheel focus shell.  Empty extension bins make the
three lab-certified spokes emitted; any additional emitted edge is selected-boundary-only and
therefore invisible to boundary-zero chains.
-/
theorem wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_of_extensionFinsets_eq_empty_uniqueCertificates_boundaryTrimmed
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hsubset :
      wheelWithInnerTriangleProjectedGeneratorCertificateColorings ⊆
        wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcrossingEmpty :
      classifier.crossingExtensionFinset wheelWithInnerTriangleInteriorControlEdges = ∅)
    (hnoncrossingEmpty :
      classifier.noncrossingExtensionFinset wheelWithInnerTriangleInteriorControlEdges = ∅) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀ :=
  theorem49BoundaryRootSynthesis_of_familyPairingKerEqBot
    wheelWithInnerTriangleEmbedding C₀
    wheelWithInnerTriangleProjectedGeneratorCertificateColorings hsubset
    wheelWithInnerTriangleUniqueCertificateRedBlueFamily
    (wheelWithInnerTriangle_CAP5_ker_planarBoundaryZeroFamilyPairingMap_uniqueCertificates_of_extensionFinsets_eq_empty_boundaryTrimmed
      p0Inside p4Inside side classifier hcrossingEmpty hnoncrossingEmpty)

/-- Failed finite-checker diagnostic for the wheel focus shell.  Once the extension bins are
empty for the three lab-certified spoke controls, a failed unique-certificate synthesis run must
expose an extra emitted classifier edge outside the certified control set. -/
theorem wheelWithInnerTriangle_CAP5_exists_extra_emittedEdge_of_not_theorem49BoundaryRootSynthesis_of_extensionFinsets_eq_empty_uniqueCertificates
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hsubset :
      wheelWithInnerTriangleProjectedGeneratorCertificateColorings ⊆
        wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcrossingEmpty :
      classifier.crossingExtensionFinset wheelWithInnerTriangleInteriorControlEdges = ∅)
    (hnoncrossingEmpty :
      classifier.noncrossingExtensionFinset wheelWithInnerTriangleInteriorControlEdges = ∅)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀) :
    ∃ e : wheelWithInnerTriangleGraph.edgeSet,
      e ∈ classifier.emittedFinset ∧ e ∉ wheelWithInnerTriangleInteriorControlEdges := by
  classical
  by_contra hnoExtra
  have honlyEmits : classifier.emittedFinset ⊆ wheelWithInnerTriangleInteriorControlEdges := by
    intro e he
    by_contra hnotControl
    exact hnoExtra ⟨e, he, hnotControl⟩
  exact hnotSynthesis
    (wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_of_extensionFinsets_eq_empty_uniqueCertificates
      C₀ hsubset p0Inside p4Inside side classifier hcrossingEmpty hnoncrossingEmpty
      honlyEmits)

/-- Certificate-facing failed finite-checker diagnostic for the wheel focus shell.  Under empty
extension bins, a failed unique-certificate synthesis run must expose an emitted edge outside the
lab-certified controls that is missing a red or blue probe in the unique certificate family. -/
theorem wheelWithInnerTriangle_CAP5_exists_extra_emittedEdge_missing_red_or_blue_uniqueCertificateWitness_of_not_theorem49BoundaryRootSynthesis_of_extensionFinsets_eq_empty
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (hsubset :
      wheelWithInnerTriangleProjectedGeneratorCertificateColorings ⊆
        wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcrossingEmpty :
      classifier.crossingExtensionFinset wheelWithInnerTriangleInteriorControlEdges = ∅)
    (hnoncrossingEmpty :
      classifier.noncrossingExtensionFinset wheelWithInnerTriangleInteriorControlEdges = ∅)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀) :
    (∃ e : wheelWithInnerTriangleGraph.edgeSet,
      e ∈ classifier.emittedFinset ∧ e ∉ wheelWithInnerTriangleInteriorControlEdges ∧
        ¬ ∃ i : ({e : wheelWithInnerTriangleGraph.edgeSet //
            e ∈ wheelWithInnerTriangleInteriorControlEdges} × Bool),
          ((wheelWithInnerTriangleUniqueCertificateRedBlueFamily i :
              projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding
                wheelWithInnerTriangleProjectedGeneratorCertificateColorings) :
              wheelWithInnerTriangleGraph.edgeSet → Color) =
            Pi.single e red) ∨
      ∃ e : wheelWithInnerTriangleGraph.edgeSet,
        e ∈ classifier.emittedFinset ∧ e ∉ wheelWithInnerTriangleInteriorControlEdges ∧
          ¬ ∃ i : ({e : wheelWithInnerTriangleGraph.edgeSet //
              e ∈ wheelWithInnerTriangleInteriorControlEdges} × Bool),
            ((wheelWithInnerTriangleUniqueCertificateRedBlueFamily i :
                projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding
                  wheelWithInnerTriangleProjectedGeneratorCertificateColorings) :
                wheelWithInnerTriangleGraph.edgeSet → Color) =
              Pi.single e blue := by
  classical
  by_contra hnoGap
  have hemits : wheelWithInnerTriangleInteriorControlEdges ⊆ classifier.emittedFinset :=
    (classifier.controlEdges_subset_emittedFinset_iff_extensionFinsets_eq_empty
      wheelWithInnerTriangleInteriorControlEdges).2
      ⟨hcrossingEmpty, hnoncrossingEmpty⟩
  have hred :
      ∀ e : wheelWithInnerTriangleGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : ({e : wheelWithInnerTriangleGraph.edgeSet //
              e ∈ wheelWithInnerTriangleInteriorControlEdges} × Bool),
            ((wheelWithInnerTriangleUniqueCertificateRedBlueFamily i :
                projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding
                  wheelWithInnerTriangleProjectedGeneratorCertificateColorings) :
                wheelWithInnerTriangleGraph.edgeSet → Color) =
              Pi.single e red := by
    intro e he
    by_cases heControl : e ∈ wheelWithInnerTriangleInteriorControlEdges
    · exact (redBlueSingleCoordinateFamily_witnessRed wheelWithInnerTriangleInteriorControlEdges
        wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
        wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2)
        e heControl
    · by_contra hmissing
      exact hnoGap (Or.inl ⟨e, he, heControl, hmissing⟩)
  have hblue :
      ∀ e : wheelWithInnerTriangleGraph.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : ({e : wheelWithInnerTriangleGraph.edgeSet //
              e ∈ wheelWithInnerTriangleInteriorControlEdges} × Bool),
            ((wheelWithInnerTriangleUniqueCertificateRedBlueFamily i :
                projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding
                  wheelWithInnerTriangleProjectedGeneratorCertificateColorings) :
                wheelWithInnerTriangleGraph.edgeSet → Color) =
              Pi.single e blue := by
    intro e he
    by_cases heControl : e ∈ wheelWithInnerTriangleInteriorControlEdges
    · exact (redBlueSingleCoordinateFamily_witnessBlue wheelWithInnerTriangleInteriorControlEdges
        wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.1
        wheelWithInnerTriangle_redBlueSingleCoordinateMemberships_of_uniqueCertificates.2)
        e heControl
    · by_contra hmissing
      exact hnoGap (Or.inr ⟨e, he, heControl, hmissing⟩)
  exact hnotSynthesis
    (wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_of_emits_interiorControlEdges
      C₀ wheelWithInnerTriangleProjectedGeneratorCertificateColorings hsubset
      wheelWithInnerTriangleUniqueCertificateRedBlueFamily p0Inside p4Inside side classifier
      hemits hred hblue)

/-- Failed-synthesis diagnostic for the shared focus shell.  Once exact CAP5 forced-edge coverage
holds, a failure of Theorem 4.9 synthesis must expose a forced edge missing a red or blue
single-coordinate projected-generator witness. -/
theorem sharedInteriorPair_CAP5_exists_forcedEdge_missing_red_or_blue_singleCoordinateWitness
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (colorings : Set (sharedInteriorPairGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ sharedInteriorPairGraph.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings)
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (hcoverage :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        z ≠ 0 →
          ∃ e : sharedInteriorPairGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀) :
    (∃ e : sharedInteriorPairGraph.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
        ¬ ∃ i : κ,
          ((family i :
              projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings) :
              sharedInteriorPairGraph.edgeSet → Color) =
            Pi.single e red) ∨
      ∃ e : sharedInteriorPairGraph.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
          ¬ ∃ i : κ,
            ((family i :
                projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings) :
                sharedInteriorPairGraph.edgeSet → Color) =
              Pi.single e blue :=
  data.exists_forcedEdge_missing_red_or_blue_singleCoordinateWitness_of_forcedEdgeCoverage_of_not_theorem49BoundaryRootSynthesis
    sharedInteriorPairEmbedding C₀ colorings hsubset family p0Inside p4Inside side
    hcoverage hnotSynthesis

/-- Failed-synthesis diagnostic for the wheel focus shell.  Once exact CAP5 forced-edge coverage
holds, a failure of Theorem 4.9 synthesis must expose a forced edge missing a red or blue
single-coordinate projected-generator witness. -/
theorem wheelWithInnerTriangle_CAP5_exists_forcedEdge_missing_red_or_blue_singleCoordinateWitness
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (colorings : Set (wheelWithInnerTriangleGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings)
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (hcoverage :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        z ≠ 0 →
          ∃ e : wheelWithInnerTriangleGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀) :
    (∃ e : wheelWithInnerTriangleGraph.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
        ¬ ∃ i : κ,
          ((family i :
              projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings) :
              wheelWithInnerTriangleGraph.edgeSet → Color) =
            Pi.single e red) ∨
      ∃ e : wheelWithInnerTriangleGraph.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
          ¬ ∃ i : κ,
            ((family i :
                projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings) :
                wheelWithInnerTriangleGraph.edgeSet → Color) =
              Pi.single e blue :=
  data.exists_forcedEdge_missing_red_or_blue_singleCoordinateWitness_of_forcedEdgeCoverage_of_not_theorem49BoundaryRootSynthesis
    wheelWithInnerTriangleEmbedding C₀ colorings hsubset family p0Inside p4Inside side
    hcoverage hnotSynthesis

/-- Exact CAP5 coverage dichotomy for the shared focus shell.  Coverage either closes Theorem
4.9 synthesis or exposes a concrete forced edge missing a red or blue projected single-coordinate
witness. -/
theorem sharedInteriorPair_CAP5_theorem49BoundaryRootSynthesis_or_forcedEdge_missing_red_or_blue_singleCoordinateWitness
    {boundaryEdge : Fin 5 → sharedInteriorPairGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (sharedInteriorPairGraph.edgeSet → Color)]
    (C₀ : sharedInteriorPairGraph.EdgeColoring Color)
    (colorings : Set (sharedInteriorPairGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ sharedInteriorPairGraph.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings)
    (p0Inside p4Inside : Bool) (side : Fin 8 → Prop)
    (hcoverage :
      ∀ ⦃z : sharedInteriorPairGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule sharedInteriorPairEmbedding →
        z ≠ 0 →
          ∃ e : sharedInteriorPairGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    Theorem49BoundaryRootSynthesis sharedInteriorPairEmbedding C₀ ∨
      (∃ e : sharedInteriorPairGraph.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
          ¬ ∃ i : κ,
            ((family i :
                projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings) :
                sharedInteriorPairGraph.edgeSet → Color) =
              Pi.single e red) ∨
        ∃ e : sharedInteriorPairGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            ¬ ∃ i : κ,
              ((family i :
                  projectedColoringGeneratorSubspace sharedInteriorPairEmbedding colorings) :
                  sharedInteriorPairGraph.edgeSet → Color) =
                Pi.single e blue :=
  data.theorem49BoundaryRootSynthesis_or_forcedEdge_missing_red_or_blue_singleCoordinateWitness_of_forcedEdgeCoverage
    sharedInteriorPairEmbedding C₀ colorings hsubset family p0Inside p4Inside side
    hcoverage

/-- Exact CAP5 coverage dichotomy for the wheel focus shell.  Coverage either closes Theorem
4.9 synthesis or exposes a concrete forced edge missing a red or blue projected single-coordinate
witness. -/
theorem wheelWithInnerTriangle_CAP5_theorem49BoundaryRootSynthesis_or_forcedEdge_missing_red_or_blue_singleCoordinateWitness
    {boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)]
    (C₀ : wheelWithInnerTriangleGraph.EdgeColoring Color)
    (colorings : Set (wheelWithInnerTriangleGraph.EdgeColoring Color))
    (hsubset : colorings ⊆ wheelWithInnerTriangleGraph.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings)
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop)
    (hcoverage :
      ∀ ⦃z : wheelWithInnerTriangleGraph.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding →
        z ≠ 0 →
          ∃ e : wheelWithInnerTriangleGraph.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding C₀ ∨
      (∃ e : wheelWithInnerTriangleGraph.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
          ¬ ∃ i : κ,
            ((family i :
                projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings) :
                wheelWithInnerTriangleGraph.edgeSet → Color) =
              Pi.single e red) ∨
        ∃ e : wheelWithInnerTriangleGraph.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            ¬ ∃ i : κ,
              ((family i :
                  projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding colorings) :
                  wheelWithInnerTriangleGraph.edgeSet → Color) =
                Pi.single e blue :=
  data.theorem49BoundaryRootSynthesis_or_forcedEdge_missing_red_or_blue_singleCoordinateWitness_of_forcedEdgeCoverage
    wheelWithInnerTriangleEmbedding C₀ colorings hsubset family p0Inside p4Inside side
    hcoverage

end Theorem49BoundaryZeroForcedEdgeRegression

end Mettapedia.GraphTheory.FourColor
