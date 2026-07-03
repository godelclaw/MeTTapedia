import Mettapedia.GraphTheory.FourColor.CAP5RoutePayoff

/-!
# Dodecahedral strict-incidence CAP5 F2 witness

This module records the concrete cyclic-five/Tait dodecahedral six-cut candidate used by the
strict-incidence Gate-2 lab run.  It does not claim a full `CAP5FiniteNoGapRouteInput`: the
remaining route obligations are the primitive no-gap checker evidence and the projected-generator
memberships.  The checked Lean payload here is the finite graph/embedding/Tait data and the
explicit unit red-scalar kernel-map evader for the strict incidence matrix emitted by the lab.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace DodecahedralCAP5RouteData

def dodecahedralGraph : SimpleGraph (Fin 20) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(0, 10), s(0, 19), s(1, 2), s(1, 8), s(2, 3), s(2, 6),
        s(3, 4), s(3, 19), s(4, 5), s(4, 17), s(5, 6), s(5, 15), s(6, 7),
        s(7, 8), s(7, 14), s(8, 9), s(9, 10), s(9, 13), s(10, 11),
        s(11, 12), s(11, 18), s(12, 13), s(12, 16), s(13, 14), s(14, 15),
        s(15, 16), s(16, 17), s(17, 18), s(18, 19)} :
      Set (Sym2 (Fin 20)))

def dod0_1 : dodecahedralGraph.edgeSet := by
  exact ⟨s(0, 1), by simp [dodecahedralGraph]⟩

def dod0_10 : dodecahedralGraph.edgeSet := by
  exact ⟨s(0, 10), by simp [dodecahedralGraph]⟩

def dod0_19 : dodecahedralGraph.edgeSet := by
  exact ⟨s(0, 19), by simp [dodecahedralGraph]⟩

def dod1_2 : dodecahedralGraph.edgeSet := by
  exact ⟨s(1, 2), by simp [dodecahedralGraph]⟩

def dod1_8 : dodecahedralGraph.edgeSet := by
  exact ⟨s(1, 8), by simp [dodecahedralGraph]⟩

def dod2_3 : dodecahedralGraph.edgeSet := by
  exact ⟨s(2, 3), by simp [dodecahedralGraph]⟩

def dod2_6 : dodecahedralGraph.edgeSet := by
  exact ⟨s(2, 6), by simp [dodecahedralGraph]⟩

def dod3_4 : dodecahedralGraph.edgeSet := by
  exact ⟨s(3, 4), by simp [dodecahedralGraph]⟩

def dod3_19 : dodecahedralGraph.edgeSet := by
  exact ⟨s(3, 19), by simp [dodecahedralGraph]⟩

def dod4_5 : dodecahedralGraph.edgeSet := by
  exact ⟨s(4, 5), by simp [dodecahedralGraph]⟩

def dod4_17 : dodecahedralGraph.edgeSet := by
  exact ⟨s(4, 17), by simp [dodecahedralGraph]⟩

def dod5_6 : dodecahedralGraph.edgeSet := by
  exact ⟨s(5, 6), by simp [dodecahedralGraph]⟩

def dod5_15 : dodecahedralGraph.edgeSet := by
  exact ⟨s(5, 15), by simp [dodecahedralGraph]⟩

def dod6_7 : dodecahedralGraph.edgeSet := by
  exact ⟨s(6, 7), by simp [dodecahedralGraph]⟩

def dod7_8 : dodecahedralGraph.edgeSet := by
  exact ⟨s(7, 8), by simp [dodecahedralGraph]⟩

def dod7_14 : dodecahedralGraph.edgeSet := by
  exact ⟨s(7, 14), by simp [dodecahedralGraph]⟩

def dod8_9 : dodecahedralGraph.edgeSet := by
  exact ⟨s(8, 9), by simp [dodecahedralGraph]⟩

def dod9_10 : dodecahedralGraph.edgeSet := by
  exact ⟨s(9, 10), by simp [dodecahedralGraph]⟩

def dod9_13 : dodecahedralGraph.edgeSet := by
  exact ⟨s(9, 13), by simp [dodecahedralGraph]⟩

def dod10_11 : dodecahedralGraph.edgeSet := by
  exact ⟨s(10, 11), by simp [dodecahedralGraph]⟩

def dod11_12 : dodecahedralGraph.edgeSet := by
  exact ⟨s(11, 12), by simp [dodecahedralGraph]⟩

def dod11_18 : dodecahedralGraph.edgeSet := by
  exact ⟨s(11, 18), by simp [dodecahedralGraph]⟩

def dod12_13 : dodecahedralGraph.edgeSet := by
  exact ⟨s(12, 13), by simp [dodecahedralGraph]⟩

def dod12_16 : dodecahedralGraph.edgeSet := by
  exact ⟨s(12, 16), by simp [dodecahedralGraph]⟩

def dod13_14 : dodecahedralGraph.edgeSet := by
  exact ⟨s(13, 14), by simp [dodecahedralGraph]⟩

def dod14_15 : dodecahedralGraph.edgeSet := by
  exact ⟨s(14, 15), by simp [dodecahedralGraph]⟩

def dod15_16 : dodecahedralGraph.edgeSet := by
  exact ⟨s(15, 16), by simp [dodecahedralGraph]⟩

def dod16_17 : dodecahedralGraph.edgeSet := by
  exact ⟨s(16, 17), by simp [dodecahedralGraph]⟩

def dod17_18 : dodecahedralGraph.edgeSet := by
  exact ⟨s(17, 18), by simp [dodecahedralGraph]⟩

def dod18_19 : dodecahedralGraph.edgeSet := by
  exact ⟨s(18, 19), by simp [dodecahedralGraph]⟩

theorem dodecahedral_edge_eq (e : dodecahedralGraph.edgeSet) :
    e = dod0_1 ∨ e = dod0_10 ∨ e = dod0_19 ∨ e = dod1_2 ∨ e = dod1_8 ∨
      e = dod2_3 ∨ e = dod2_6 ∨ e = dod3_4 ∨ e = dod3_19 ∨ e = dod4_5 ∨
      e = dod4_17 ∨ e = dod5_6 ∨ e = dod5_15 ∨ e = dod6_7 ∨ e = dod7_8 ∨
      e = dod7_14 ∨ e = dod8_9 ∨ e = dod9_10 ∨ e = dod9_13 ∨
      e = dod10_11 ∨ e = dod11_12 ∨ e = dod11_18 ∨ e = dod12_13 ∨
      e = dod12_16 ∨ e = dod13_14 ∨ e = dod14_15 ∨ e = dod15_16 ∨
      e = dod16_17 ∨ e = dod17_18 ∨ e = dod18_19 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(0, 10) ∨ e.1 = s(0, 19) ∨
        e.1 = s(1, 2) ∨ e.1 = s(1, 8) ∨ e.1 = s(2, 3) ∨
        e.1 = s(2, 6) ∨ e.1 = s(3, 4) ∨ e.1 = s(3, 19) ∨
        e.1 = s(4, 5) ∨ e.1 = s(4, 17) ∨ e.1 = s(5, 6) ∨
        e.1 = s(5, 15) ∨ e.1 = s(6, 7) ∨ e.1 = s(7, 8) ∨
        e.1 = s(7, 14) ∨ e.1 = s(8, 9) ∨ e.1 = s(9, 10) ∨
        e.1 = s(9, 13) ∨ e.1 = s(10, 11) ∨ e.1 = s(11, 12) ∨
        e.1 = s(11, 18) ∨ e.1 = s(12, 13) ∨ e.1 = s(12, 16) ∨
        e.1 = s(13, 14) ∨ e.1 = s(14, 15) ∨ e.1 = s(15, 16) ∨
        e.1 = s(16, 17) ∨ e.1 = s(17, 18) ∨ e.1 = s(18, 19)) ∧
        ¬ e.1.IsDiag := by
    simpa [dodecahedralGraph] using e.2
  rcases h.1 with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 |
    h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 |
    h23 | h24 | h25 | h26 | h27 | h28 | h29
  · left; exact Subtype.ext h0
  · right; left; exact Subtype.ext h1
  · right; right; left; exact Subtype.ext h2
  · right; right; right; left; exact Subtype.ext h3
  · right; right; right; right; left; exact Subtype.ext h4
  · right; right; right; right; right; left; exact Subtype.ext h5
  · right; right; right; right; right; right; left; exact Subtype.ext h6
  · right; right; right; right; right; right; right; left; exact Subtype.ext h7
  · right; right; right; right; right; right; right; right; left; exact Subtype.ext h8
  · right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h9
  · right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h10
  · right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h11
  · right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h12
  · right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h13
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h14
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h15
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h16
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h17
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h18
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h19
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h20
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h21
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h22
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h23
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h24
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h25
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h26
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h27
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h28
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; exact Subtype.ext h29

noncomputable instance dodecahedralGraph_edgeSet_fintype :
    Fintype dodecahedralGraph.edgeSet :=
  ⟨{dod0_1, dod0_10, dod0_19, dod1_2, dod1_8, dod2_3, dod2_6, dod3_4,
      dod3_19, dod4_5, dod4_17, dod5_6, dod5_15, dod6_7, dod7_8, dod7_14,
      dod8_9, dod9_10, dod9_13, dod10_11, dod11_12, dod11_18, dod12_13,
      dod12_16, dod13_14, dod14_15, dod15_16, dod16_17, dod17_18, dod18_19},
    by
      intro e
      rcases dodecahedral_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide⟩

instance dodecahedralGraph_lineGraph_adj_decidable :
    DecidableRel dodecahedralGraph.lineGraph.Adj := by
  intro e f
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  infer_instance

abbrev DodecahedralFace := Fin 12

def dodecahedralFaces : Finset DodecahedralFace := Finset.univ

def dodecahedralFaceBoundary :
    DodecahedralFace → Finset dodecahedralGraph.edgeSet
  | ⟨0, _⟩ => {dod0_19, dod3_19, dod2_3, dod1_2, dod0_1}
  | ⟨1, _⟩ => {dod0_10, dod10_11, dod11_18, dod18_19, dod0_19}
  | ⟨2, _⟩ => {dod0_1, dod1_8, dod8_9, dod9_10, dod0_10}
  | ⟨3, _⟩ => {dod1_2, dod2_6, dod6_7, dod7_8, dod1_8}
  | ⟨4, _⟩ => {dod2_3, dod3_4, dod4_5, dod5_6, dod2_6}
  | ⟨5, _⟩ => {dod3_19, dod18_19, dod17_18, dod4_17, dod3_4}
  | ⟨6, _⟩ => {dod4_17, dod16_17, dod15_16, dod5_15, dod4_5}
  | ⟨7, _⟩ => {dod5_15, dod14_15, dod7_14, dod6_7, dod5_6}
  | ⟨8, _⟩ => {dod7_14, dod13_14, dod9_13, dod8_9, dod7_8}
  | ⟨9, _⟩ => {dod9_13, dod12_13, dod11_12, dod10_11, dod9_10}
  | ⟨10, _⟩ => {dod11_12, dod12_16, dod16_17, dod17_18, dod11_18}
  | ⟨11, _⟩ => {dod12_13, dod13_14, dod14_15, dod15_16, dod12_16}

theorem dodecahedral_totalIncidenceCount_eq_two
    (e : dodecahedralGraph.edgeSet) :
    totalIncidenceCount dodecahedralFaceBoundary dodecahedralFaces e = 2 := by
  rcases dodecahedral_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def dodecahedralEmbedding : PlaneEmbeddingWithBoundary dodecahedralGraph where
  Face := DodecahedralFace
  faceDecidableEq := inferInstance
  faces := dodecahedralFaces
  faceBoundary := dodecahedralFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases dodecahedral_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  edge_one_or_two_faces := by
    intro e _he
    exact Or.inr (dodecahedral_totalIncidenceCount_eq_two e)

theorem dodecahedral_selectedBoundarySupport_eq_empty :
    selectedBoundarySupport dodecahedralEmbedding.faceBoundary dodecahedralEmbedding.faces
      dodecahedralEmbedding.faces = ∅ := by
  ext e
  constructor
  · intro he
    have hcount :=
      (mem_selectedBoundarySupport_iff dodecahedralEmbedding.faceBoundary
        dodecahedralEmbedding.faces dodecahedralEmbedding.faces).1 he |>.2
    have htwo :
        totalIncidenceCount dodecahedralEmbedding.faceBoundary
          dodecahedralEmbedding.faces e = 2 := by
      simpa [dodecahedralEmbedding] using dodecahedral_totalIncidenceCount_eq_two e
    omega
  · intro hfalse
    simp at hfalse

theorem dod0_1_mem_interiorEdgeSupport :
    dod0_1 ∈ interiorEdgeSupport dodecahedralEmbedding.faceBoundary
      dodecahedralEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, dodecahedral_totalIncidenceCount_eq_two dod0_1⟩

def dodecahedralEdgeColor (e : dodecahedralGraph.edgeSet) : Color :=
  if e = dod0_1 then red else
  if e = dod0_10 then blue else
  if e = dod0_19 then purple else
  if e = dod1_2 then blue else
  if e = dod1_8 then purple else
  if e = dod2_3 then red else
  if e = dod2_6 then purple else
  if e = dod3_4 then purple else
  if e = dod3_19 then blue else
  if e = dod4_5 then blue else
  if e = dod4_17 then red else
  if e = dod5_6 then red else
  if e = dod5_15 then purple else
  if e = dod6_7 then blue else
  if e = dod7_8 then red else
  if e = dod7_14 then purple else
  if e = dod8_9 then blue else
  if e = dod9_10 then red else
  if e = dod9_13 then purple else
  if e = dod10_11 then purple else
  if e = dod11_12 then red else
  if e = dod11_18 then blue else
  if e = dod12_13 then blue else
  if e = dod12_16 then purple else
  if e = dod13_14 then red else
  if e = dod14_15 then blue else
  if e = dod15_16 then red else
  if e = dod16_17 then blue else
  if e = dod17_18 then purple else
  red

theorem dodecahedralEdgeColor_ne_of_lineGraph_adj
    {e f : dodecahedralGraph.edgeSet}
    (hadj : dodecahedralGraph.lineGraph.Adj e f) :
    dodecahedralEdgeColor e ≠ dodecahedralEdgeColor f := by
  decide +revert

def dodecahedralTaitEdgeColoring : dodecahedralGraph.EdgeColoring Color :=
  Coloring.mk dodecahedralEdgeColor (by
    intro e f hadj
    exact dodecahedralEdgeColor_ne_of_lineGraph_adj hadj)

theorem dodecahedralEdgeColor_ne_zero (e : dodecahedralGraph.edgeSet) :
    dodecahedralEdgeColor e ≠ 0 := by
  decide +revert

theorem dodecahedralTaitEdgeColoring_isTait :
    IsTaitEdgeColoring dodecahedralGraph dodecahedralTaitEdgeColoring := by
  rw [IsTaitEdgeColoring]
  intro e
  exact dodecahedralEdgeColor_ne_zero e

theorem exists_taitEdgeColoring_dodecahedralGraph :
    ∃ C : dodecahedralGraph.EdgeColoring Color,
      IsTaitEdgeColoring dodecahedralGraph C := by
  exact ⟨dodecahedralTaitEdgeColoring, dodecahedralTaitEdgeColoring_isTait⟩

def dodecahedralCAP5BoundaryEdge : Fin 5 → dodecahedralGraph.edgeSet
  | ⟨0, _⟩ => dod0_10
  | ⟨1, _⟩ => dod1_8
  | ⟨2, _⟩ => dod2_6
  | ⟨3, _⟩ => dod4_5
  | ⟨4, _⟩ => dod4_17

def dodecahedralCAP5RedBlueEdge₁ : Finset dodecahedralGraph.edgeSet :=
  {dod0_10, dod4_5}

def dodecahedralCAP5RedBlueEdge₂ : Finset dodecahedralGraph.edgeSet :=
  {dod1_8, dod2_6}

def dodecahedralCAP5RedPurpleEdge₁ : Finset dodecahedralGraph.edgeSet :=
  {dod0_10, dod4_17}

def dodecahedralCAP5RedPurpleEdge₂ : Finset dodecahedralGraph.edgeSet :=
  {dod1_8, dod4_5}

theorem dodecahedralCAP5RedBlueEdge₁_support :
    cap5BoundarySupportOfEdges dodecahedralCAP5BoundaryEdge
      dodecahedralCAP5RedBlueEdge₁ = ({0, 3} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, dodecahedralCAP5BoundaryEdge,
      dodecahedralCAP5RedBlueEdge₁, dod0_10, dod1_8, dod2_6, dod4_5, dod4_17]

theorem dodecahedralCAP5RedBlueEdge₂_support :
    cap5BoundarySupportOfEdges dodecahedralCAP5BoundaryEdge
      dodecahedralCAP5RedBlueEdge₂ = ({1, 2} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, dodecahedralCAP5BoundaryEdge,
      dodecahedralCAP5RedBlueEdge₂, dod0_10, dod1_8, dod2_6, dod4_5, dod4_17]

theorem dodecahedralCAP5RedPurpleEdge₁_support :
    cap5BoundarySupportOfEdges dodecahedralCAP5BoundaryEdge
      dodecahedralCAP5RedPurpleEdge₁ = ({0, 4} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, dodecahedralCAP5BoundaryEdge,
      dodecahedralCAP5RedPurpleEdge₁, dod0_10, dod1_8, dod2_6, dod4_5, dod4_17]

theorem dodecahedralCAP5RedPurpleEdge₂_support :
    cap5BoundarySupportOfEdges dodecahedralCAP5BoundaryEdge
      dodecahedralCAP5RedPurpleEdge₂ = ({1, 3} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, dodecahedralCAP5BoundaryEdge,
      dodecahedralCAP5RedPurpleEdge₂, dod0_10, dod1_8, dod2_6, dod4_5, dod4_17]

def dodecahedralCAP5ComponentCoverCore :
    CAP5TransportedEdgeComponentCoverCore dodecahedralCAP5BoundaryEdge 0 where
  redBlueEdge₁ := dodecahedralCAP5RedBlueEdge₁
  redBlueEdge₂ := dodecahedralCAP5RedBlueEdge₂
  redPurpleEdge₁ := dodecahedralCAP5RedPurpleEdge₁
  redPurpleEdge₂ := dodecahedralCAP5RedPurpleEdge₂
  redBlue₁ := {0, 3}
  redBlue₂ := {1, 2}
  redPurple₁ := {0, 4}
  redPurple₂ := {1, 3}
  hredBlue₁ := by
    simpa [cap5RotateBoundarySupportN] using dodecahedralCAP5RedBlueEdge₁_support
  hredBlue₂ := by
    simpa [cap5RotateBoundarySupportN] using dodecahedralCAP5RedBlueEdge₂_support
  hredPurple₁ := by
    simpa [cap5RotateBoundarySupportN] using dodecahedralCAP5RedPurpleEdge₁_support
  hredPurple₂ := by
    simpa [cap5RotateBoundarySupportN] using dodecahedralCAP5RedPurpleEdge₂_support
  hredBlue := by
    rw [CAP5BadRedBlueComponentCover]
    refine ⟨by simp, by simp, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      fin_cases i <;> simp at hi₁ hi₂
    · ext i
      fin_cases i <;> simp
  hredPurple := by
    rw [CAP5BadRedPurpleComponentCover]
    refine ⟨by simp, by simp, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      fin_cases i <;> simp at hi₁ hi₂
    · ext i
      fin_cases i <;> simp

theorem dodecahedralCAP5ComponentCoverCore_isExceptional :
    dodecahedralCAP5ComponentCoverCore.IsExceptional := by
  change CAP5BadExceptionalPairingPattern
    ({0, 3} : Finset (Fin 5)) ({1, 2} : Finset (Fin 5))
      ({0, 4} : Finset (Fin 5)) ({1, 3} : Finset (Fin 5))
  rw [CAP5BadExceptionalPairingPattern, CAP5BadRedBlueExceptionalPairing,
    CAP5BadRedPurpleExceptionalPairing]
  exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

def dodecahedralSixCutSide (v : Fin 20) : Prop :=
  v ∈ ({0, 1, 2, 3, 4, 19} : Finset (Fin 20))

theorem dod0_10_crosses_dodecahedralSixCutSide :
    EdgeCrossesVertexSide dodecahedralGraph dodecahedralSixCutSide dod0_10 := by
  refine ⟨0, 10, ?_, ?_, ?_, ?_⟩ <;> simp [dod0_10, dodecahedralSixCutSide]

theorem dod1_8_crosses_dodecahedralSixCutSide :
    EdgeCrossesVertexSide dodecahedralGraph dodecahedralSixCutSide dod1_8 := by
  refine ⟨1, 8, ?_, ?_, ?_, ?_⟩ <;> simp [dod1_8, dodecahedralSixCutSide]

theorem dod2_6_crosses_dodecahedralSixCutSide :
    EdgeCrossesVertexSide dodecahedralGraph dodecahedralSixCutSide dod2_6 := by
  refine ⟨2, 6, ?_, ?_, ?_, ?_⟩ <;> simp [dod2_6, dodecahedralSixCutSide]

theorem dod4_5_crosses_dodecahedralSixCutSide :
    EdgeCrossesVertexSide dodecahedralGraph dodecahedralSixCutSide dod4_5 := by
  refine ⟨4, 5, ?_, ?_, ?_, ?_⟩ <;> simp [dod4_5, dodecahedralSixCutSide]

theorem dod4_17_crosses_dodecahedralSixCutSide :
    EdgeCrossesVertexSide dodecahedralGraph dodecahedralSixCutSide dod4_17 := by
  refine ⟨4, 17, ?_, ?_, ?_, ?_⟩ <;> simp [dod4_17, dodecahedralSixCutSide]

theorem dod18_19_crosses_dodecahedralSixCutSide :
    EdgeCrossesVertexSide dodecahedralGraph dodecahedralSixCutSide dod18_19 := by
  refine ⟨19, 18, ?_, ?_, ?_, ?_⟩ <;> simp [dod18_19, dodecahedralSixCutSide]

def dodecahedralStrictEmittedFinset : Finset dodecahedralGraph.edgeSet :=
  {dod18_19, dod4_17}

def dodecahedralStrictRemainingControls : Finset dodecahedralGraph.edgeSet :=
  interiorEdgeSupport dodecahedralEmbedding.faceBoundary dodecahedralEmbedding.faces \
    dodecahedralStrictEmittedFinset

def dodecahedralUnitDod0_1 : dodecahedralGraph.edgeSet → Color :=
  Pi.single dod0_1 red

theorem dodecahedralUnitDod0_1_mem_planarBoundaryZeroSubmodule :
    dodecahedralUnitDod0_1 ∈ planarBoundaryZeroSubmodule dodecahedralEmbedding := by
  intro e he
  rw [dodecahedral_selectedBoundarySupport_eq_empty] at he
  simp at he

def dodecahedralBoundaryZeroUnitDod0_1 :
    planarBoundaryZeroSubmodule dodecahedralEmbedding :=
  ⟨dodecahedralUnitDod0_1, dodecahedralUnitDod0_1_mem_planarBoundaryZeroSubmodule⟩

theorem dodecahedralUnitDod0_1_ne_zero :
    dodecahedralUnitDod0_1 ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero dod0_1
  simp [dodecahedralUnitDod0_1] at hvalue

theorem dodecahedralUnitDod0_1_zero_on_strictEmitted :
    ∀ e ∈ dodecahedralStrictEmittedFinset, dodecahedralUnitDod0_1 e = 0 := by
  intro e he
  have he' : e = dod18_19 ∨ e = dod4_17 := by
    simpa [dodecahedralStrictEmittedFinset] using he
  rcases he' with rfl | rfl <;>
    simp [dodecahedralUnitDod0_1, dod0_1, dod18_19, dod4_17]

theorem dod0_1_mem_dodecahedralStrictRemainingControls :
    dod0_1 ∈ dodecahedralStrictRemainingControls := by
  refine Finset.mem_sdiff.2 ⟨dod0_1_mem_interiorEdgeSupport, ?_⟩
  simp [dodecahedralStrictEmittedFinset, dod0_1, dod18_19, dod4_17]

theorem dodecahedralUnitDod0_1_detects_remaining :
    dod0_1 ∈ dodecahedralStrictRemainingControls ∧
      dodecahedralUnitDod0_1 dod0_1 = red := by
  exact ⟨dod0_1_mem_dodecahedralStrictRemainingControls,
    by simp [dodecahedralUnitDod0_1]⟩

def dodecahedralStrictEmittedRowWord : Fin 2 → Nat
  | ⟨0, _⟩ => 536870912
  | _ => 1024

def dodecahedralStrictRREFRowWord : Fin 2 → Nat
  | ⟨0, _⟩ => 1024
  | _ => 536870912

def dodecahedralStrictF2Rank : Nat := 2

def dodecahedralStrictF2KernelDimension : Nat := 28

/--
Checked Lean form of the strict-incidence lab BREAK witness.  The row words record the exact
two emitted scalar constraints from the lab artifact; the mathematical witness here is the unit
red scalar on `dod0_1`, which is boundary-zero, vanishes on both emitted constraints, and is
detected on a remaining interior control edge.
-/
structure DodecahedralStrictF2KernelEvaderCertificate : Prop where
  emittedRows :
    dodecahedralStrictEmittedRowWord 0 = 536870912 ∧
      dodecahedralStrictEmittedRowWord 1 = 1024
  rrefRows :
    dodecahedralStrictRREFRowWord 0 = 1024 ∧
      dodecahedralStrictRREFRowWord 1 = 536870912
  rank : dodecahedralStrictF2Rank = 2
  kernelDimension : dodecahedralStrictF2KernelDimension = 28
  boundaryZero :
    dodecahedralUnitDod0_1 ∈ planarBoundaryZeroSubmodule dodecahedralEmbedding
  nonzero : dodecahedralUnitDod0_1 ≠ 0
  vanishesOnEmitted :
    ∀ e ∈ dodecahedralStrictEmittedFinset, dodecahedralUnitDod0_1 e = 0
  detectedRemaining :
    dod0_1 ∈ dodecahedralStrictRemainingControls ∧
      dodecahedralUnitDod0_1 dod0_1 = red

theorem dodecahedralStrictF2KernelEvaderCertificate :
    DodecahedralStrictF2KernelEvaderCertificate where
  emittedRows := by decide
  rrefRows := by decide
  rank := rfl
  kernelDimension := rfl
  boundaryZero := dodecahedralUnitDod0_1_mem_planarBoundaryZeroSubmodule
  nonzero := dodecahedralUnitDod0_1_ne_zero
  vanishesOnEmitted := dodecahedralUnitDod0_1_zero_on_strictEmitted
  detectedRemaining := dodecahedralUnitDod0_1_detects_remaining

end DodecahedralCAP5RouteData

end Mettapedia.GraphTheory.FourColor
