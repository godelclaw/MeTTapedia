import Mettapedia.GraphTheory.FourColor.CAP5RoutePayoff

/-!
# GP(12,2) CAP5 finite Gate-2 BREAK witness

This module records the concrete GP(12,2) route candidate from the finite F2 lab and the
explicit unit red-coordinate kernel-map evaders for the four CAP5 side cases.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace GP12CAP5RouteData

def gp12Graph : SimpleGraph (Fin 24) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(0, 11), s(0, 12), s(1, 2), s(1, 13), s(2, 3), s(2, 14), s(3, 4), s(3, 15), s(4, 5), s(4, 16), s(5, 6), s(5, 17), s(6, 7), s(6, 18), s(7, 8), s(7, 19), s(8, 9), s(8, 20), s(9, 10), s(9, 21), s(10, 11), s(10, 22), s(11, 23), s(12, 14), s(12, 22), s(13, 15), s(13, 23), s(14, 16), s(15, 17), s(16, 18), s(17, 19), s(18, 20), s(19, 21), s(20, 22), s(21, 23)} :
      Set (Sym2 (Fin 24)))

def gp12_e0_1 : gp12Graph.edgeSet := by
  exact ⟨s(0, 1), by simp [gp12Graph]⟩

def gp12_e0_11 : gp12Graph.edgeSet := by
  exact ⟨s(0, 11), by simp [gp12Graph]⟩

def gp12_e0_12 : gp12Graph.edgeSet := by
  exact ⟨s(0, 12), by simp [gp12Graph]⟩

def gp12_e1_2 : gp12Graph.edgeSet := by
  exact ⟨s(1, 2), by simp [gp12Graph]⟩

def gp12_e1_13 : gp12Graph.edgeSet := by
  exact ⟨s(1, 13), by simp [gp12Graph]⟩

def gp12_e2_3 : gp12Graph.edgeSet := by
  exact ⟨s(2, 3), by simp [gp12Graph]⟩

def gp12_e2_14 : gp12Graph.edgeSet := by
  exact ⟨s(2, 14), by simp [gp12Graph]⟩

def gp12_e3_4 : gp12Graph.edgeSet := by
  exact ⟨s(3, 4), by simp [gp12Graph]⟩

def gp12_e3_15 : gp12Graph.edgeSet := by
  exact ⟨s(3, 15), by simp [gp12Graph]⟩

def gp12_e4_5 : gp12Graph.edgeSet := by
  exact ⟨s(4, 5), by simp [gp12Graph]⟩

def gp12_e4_16 : gp12Graph.edgeSet := by
  exact ⟨s(4, 16), by simp [gp12Graph]⟩

def gp12_e5_6 : gp12Graph.edgeSet := by
  exact ⟨s(5, 6), by simp [gp12Graph]⟩

def gp12_e5_17 : gp12Graph.edgeSet := by
  exact ⟨s(5, 17), by simp [gp12Graph]⟩

def gp12_e6_7 : gp12Graph.edgeSet := by
  exact ⟨s(6, 7), by simp [gp12Graph]⟩

def gp12_e6_18 : gp12Graph.edgeSet := by
  exact ⟨s(6, 18), by simp [gp12Graph]⟩

def gp12_e7_8 : gp12Graph.edgeSet := by
  exact ⟨s(7, 8), by simp [gp12Graph]⟩

def gp12_e7_19 : gp12Graph.edgeSet := by
  exact ⟨s(7, 19), by simp [gp12Graph]⟩

def gp12_e8_9 : gp12Graph.edgeSet := by
  exact ⟨s(8, 9), by simp [gp12Graph]⟩

def gp12_e8_20 : gp12Graph.edgeSet := by
  exact ⟨s(8, 20), by simp [gp12Graph]⟩

def gp12_e9_10 : gp12Graph.edgeSet := by
  exact ⟨s(9, 10), by simp [gp12Graph]⟩

def gp12_e9_21 : gp12Graph.edgeSet := by
  exact ⟨s(9, 21), by simp [gp12Graph]⟩

def gp12_e10_11 : gp12Graph.edgeSet := by
  exact ⟨s(10, 11), by simp [gp12Graph]⟩

def gp12_e10_22 : gp12Graph.edgeSet := by
  exact ⟨s(10, 22), by simp [gp12Graph]⟩

def gp12_e11_23 : gp12Graph.edgeSet := by
  exact ⟨s(11, 23), by simp [gp12Graph]⟩

def gp12_e12_14 : gp12Graph.edgeSet := by
  exact ⟨s(12, 14), by simp [gp12Graph]⟩

def gp12_e12_22 : gp12Graph.edgeSet := by
  exact ⟨s(12, 22), by simp [gp12Graph]⟩

def gp12_e13_15 : gp12Graph.edgeSet := by
  exact ⟨s(13, 15), by simp [gp12Graph]⟩

def gp12_e13_23 : gp12Graph.edgeSet := by
  exact ⟨s(13, 23), by simp [gp12Graph]⟩

def gp12_e14_16 : gp12Graph.edgeSet := by
  exact ⟨s(14, 16), by simp [gp12Graph]⟩

def gp12_e15_17 : gp12Graph.edgeSet := by
  exact ⟨s(15, 17), by simp [gp12Graph]⟩

def gp12_e16_18 : gp12Graph.edgeSet := by
  exact ⟨s(16, 18), by simp [gp12Graph]⟩

def gp12_e17_19 : gp12Graph.edgeSet := by
  exact ⟨s(17, 19), by simp [gp12Graph]⟩

def gp12_e18_20 : gp12Graph.edgeSet := by
  exact ⟨s(18, 20), by simp [gp12Graph]⟩

def gp12_e19_21 : gp12Graph.edgeSet := by
  exact ⟨s(19, 21), by simp [gp12Graph]⟩

def gp12_e20_22 : gp12Graph.edgeSet := by
  exact ⟨s(20, 22), by simp [gp12Graph]⟩

def gp12_e21_23 : gp12Graph.edgeSet := by
  exact ⟨s(21, 23), by simp [gp12Graph]⟩

theorem gp12_edge_eq (e : gp12Graph.edgeSet) :
    e = gp12_e0_1 ∨ e = gp12_e0_11 ∨ e = gp12_e0_12 ∨ e = gp12_e1_2 ∨ e = gp12_e1_13 ∨ e = gp12_e2_3 ∨ e = gp12_e2_14 ∨ e = gp12_e3_4 ∨ e = gp12_e3_15 ∨ e = gp12_e4_5 ∨ e = gp12_e4_16 ∨ e = gp12_e5_6 ∨ e = gp12_e5_17 ∨ e = gp12_e6_7 ∨ e = gp12_e6_18 ∨ e = gp12_e7_8 ∨ e = gp12_e7_19 ∨ e = gp12_e8_9 ∨ e = gp12_e8_20 ∨ e = gp12_e9_10 ∨ e = gp12_e9_21 ∨ e = gp12_e10_11 ∨ e = gp12_e10_22 ∨ e = gp12_e11_23 ∨ e = gp12_e12_14 ∨ e = gp12_e12_22 ∨ e = gp12_e13_15 ∨ e = gp12_e13_23 ∨ e = gp12_e14_16 ∨ e = gp12_e15_17 ∨ e = gp12_e16_18 ∨ e = gp12_e17_19 ∨ e = gp12_e18_20 ∨ e = gp12_e19_21 ∨ e = gp12_e20_22 ∨ e = gp12_e21_23 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(0, 11) ∨ e.1 = s(0, 12) ∨ e.1 = s(1, 2) ∨ e.1 = s(1, 13) ∨ e.1 = s(2, 3) ∨ e.1 = s(2, 14) ∨ e.1 = s(3, 4) ∨ e.1 = s(3, 15) ∨ e.1 = s(4, 5) ∨ e.1 = s(4, 16) ∨ e.1 = s(5, 6) ∨ e.1 = s(5, 17) ∨ e.1 = s(6, 7) ∨ e.1 = s(6, 18) ∨ e.1 = s(7, 8) ∨ e.1 = s(7, 19) ∨ e.1 = s(8, 9) ∨ e.1 = s(8, 20) ∨ e.1 = s(9, 10) ∨ e.1 = s(9, 21) ∨ e.1 = s(10, 11) ∨ e.1 = s(10, 22) ∨ e.1 = s(11, 23) ∨ e.1 = s(12, 14) ∨ e.1 = s(12, 22) ∨ e.1 = s(13, 15) ∨ e.1 = s(13, 23) ∨ e.1 = s(14, 16) ∨ e.1 = s(15, 17) ∨ e.1 = s(16, 18) ∨ e.1 = s(17, 19) ∨ e.1 = s(18, 20) ∨ e.1 = s(19, 21) ∨ e.1 = s(20, 22) ∨ e.1 = s(21, 23)) ∧ ¬ e.1.IsDiag := by
    simpa [gp12Graph] using e.2
  rcases h.1 with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35
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
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h29
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h30
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h31
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h32
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h33
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact Subtype.ext h34
  · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; exact Subtype.ext h35

noncomputable instance gp12Graph_edgeSet_fintype : Fintype gp12Graph.edgeSet :=
  ⟨{gp12_e0_1, gp12_e0_11, gp12_e0_12, gp12_e1_2, gp12_e1_13, gp12_e2_3, gp12_e2_14, gp12_e3_4, gp12_e3_15, gp12_e4_5, gp12_e4_16, gp12_e5_6, gp12_e5_17, gp12_e6_7, gp12_e6_18, gp12_e7_8, gp12_e7_19, gp12_e8_9, gp12_e8_20, gp12_e9_10, gp12_e9_21, gp12_e10_11, gp12_e10_22, gp12_e11_23, gp12_e12_14, gp12_e12_22, gp12_e13_15, gp12_e13_23, gp12_e14_16, gp12_e15_17, gp12_e16_18, gp12_e17_19, gp12_e18_20, gp12_e19_21, gp12_e20_22, gp12_e21_23},
    by
      intro e
      rcases gp12_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide⟩

instance gp12Graph_lineGraph_adj_decidable : DecidableRel gp12Graph.lineGraph.Adj := by
  intro e f
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  infer_instance

abbrev GP12Face := Fin 14

def gp12Faces : Finset GP12Face := Finset.univ

def gp12FaceBoundary : GP12Face → Finset gp12Graph.edgeSet
  | ⟨0, _⟩ => {gp12_e0_1, gp12_e1_2, gp12_e2_14, gp12_e12_14, gp12_e0_12}
  | ⟨1, _⟩ => {gp12_e0_11, gp12_e11_23, gp12_e13_23, gp12_e1_13, gp12_e0_1}
  | ⟨2, _⟩ => {gp12_e0_12, gp12_e12_22, gp12_e10_22, gp12_e10_11, gp12_e0_11}
  | ⟨3, _⟩ => {gp12_e1_13, gp12_e13_15, gp12_e3_15, gp12_e2_3, gp12_e1_2}
  | ⟨4, _⟩ => {gp12_e2_3, gp12_e3_4, gp12_e4_16, gp12_e14_16, gp12_e2_14}
  | ⟨5, _⟩ => {gp12_e3_15, gp12_e15_17, gp12_e5_17, gp12_e4_5, gp12_e3_4}
  | ⟨6, _⟩ => {gp12_e4_5, gp12_e5_6, gp12_e6_18, gp12_e16_18, gp12_e4_16}
  | ⟨7, _⟩ => {gp12_e5_17, gp12_e17_19, gp12_e7_19, gp12_e6_7, gp12_e5_6}
  | ⟨8, _⟩ => {gp12_e6_7, gp12_e7_8, gp12_e8_20, gp12_e18_20, gp12_e6_18}
  | ⟨9, _⟩ => {gp12_e7_19, gp12_e19_21, gp12_e9_21, gp12_e8_9, gp12_e7_8}
  | ⟨10, _⟩ => {gp12_e8_9, gp12_e9_10, gp12_e10_22, gp12_e20_22, gp12_e8_20}
  | ⟨11, _⟩ => {gp12_e9_21, gp12_e21_23, gp12_e11_23, gp12_e10_11, gp12_e9_10}
  | ⟨12, _⟩ => {gp12_e12_14, gp12_e14_16, gp12_e16_18, gp12_e18_20, gp12_e20_22, gp12_e12_22}
  | ⟨13, _⟩ => {gp12_e13_23, gp12_e21_23, gp12_e19_21, gp12_e17_19, gp12_e15_17, gp12_e13_15}

theorem gp12_totalIncidenceCount_eq_two (e : gp12Graph.edgeSet) :
    totalIncidenceCount gp12FaceBoundary gp12Faces e = 2 := by
  rcases gp12_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def gp12Embedding : PlaneEmbeddingWithBoundary gp12Graph where
  Face := GP12Face
  faceDecidableEq := inferInstance
  faces := gp12Faces
  faceBoundary := gp12FaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases gp12_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  edge_one_or_two_faces := by
    intro e _he
    exact Or.inr (gp12_totalIncidenceCount_eq_two e)

theorem gp12_selectedBoundarySupport_eq_empty :
    selectedBoundarySupport gp12Embedding.faceBoundary gp12Embedding.faces
      gp12Embedding.faces = ∅ := by
  ext e
  constructor
  · intro he
    have hcount :=
      (mem_selectedBoundarySupport_iff gp12Embedding.faceBoundary
        gp12Embedding.faces gp12Embedding.faces).1 he |>.2
    have htwo :
        totalIncidenceCount gp12Embedding.faceBoundary gp12Embedding.faces e = 2 := by
      simpa [gp12Embedding] using gp12_totalIncidenceCount_eq_two e
    omega
  · intro hfalse
    simp at hfalse

theorem gp12_e0_1_mem_interiorEdgeSupport :
    gp12_e0_1 ∈ interiorEdgeSupport gp12Embedding.faceBoundary gp12Embedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, gp12_totalIncidenceCount_eq_two gp12_e0_1⟩

theorem gp12_e0_11_mem_interiorEdgeSupport :
    gp12_e0_11 ∈ interiorEdgeSupport gp12Embedding.faceBoundary gp12Embedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, gp12_totalIncidenceCount_eq_two gp12_e0_11⟩

def gp12EdgeColor (e : gp12Graph.edgeSet) : Color :=
  if e = gp12_e0_1 then red else
  if e = gp12_e0_11 then blue else
  if e = gp12_e0_12 then purple else
  if e = gp12_e1_2 then blue else
  if e = gp12_e1_13 then purple else
  if e = gp12_e2_3 then red else
  if e = gp12_e2_14 then purple else
  if e = gp12_e3_4 then blue else
  if e = gp12_e3_15 then purple else
  if e = gp12_e4_5 then red else
  if e = gp12_e4_16 then purple else
  if e = gp12_e5_6 then blue else
  if e = gp12_e5_17 then purple else
  if e = gp12_e6_7 then red else
  if e = gp12_e6_18 then purple else
  if e = gp12_e7_8 then purple else
  if e = gp12_e7_19 then blue else
  if e = gp12_e8_9 then red else
  if e = gp12_e8_20 then blue else
  if e = gp12_e9_10 then purple else
  if e = gp12_e9_21 then blue else
  if e = gp12_e10_11 then red else
  if e = gp12_e10_22 then blue else
  if e = gp12_e11_23 then purple else
  if e = gp12_e12_14 then blue else
  if e = gp12_e12_22 then red else
  if e = gp12_e13_15 then red else
  if e = gp12_e13_23 then blue else
  if e = gp12_e14_16 then red else
  if e = gp12_e15_17 then blue else
  if e = gp12_e16_18 then blue else
  if e = gp12_e17_19 then red else
  if e = gp12_e18_20 then red else
  if e = gp12_e19_21 then purple else
  if e = gp12_e20_22 then purple else
  if e = gp12_e21_23 then red else
  red

set_option maxRecDepth 10000 in
theorem gp12EdgeColor_ne_of_lineGraph_adj
    {e f : gp12Graph.edgeSet}
    (hadj : gp12Graph.lineGraph.Adj e f) :
    gp12EdgeColor e ≠ gp12EdgeColor f := by
  decide +revert

def gp12TaitEdgeColoring : gp12Graph.EdgeColoring Color :=
  Coloring.mk gp12EdgeColor (by
    intro e f hadj
    exact gp12EdgeColor_ne_of_lineGraph_adj hadj)

theorem gp12EdgeColor_ne_zero (e : gp12Graph.edgeSet) :
    gp12EdgeColor e ≠ 0 := by
  decide +revert

theorem gp12TaitEdgeColoring_isTait :
    IsTaitEdgeColoring gp12Graph gp12TaitEdgeColoring := by
  rw [IsTaitEdgeColoring]
  intro e
  exact gp12EdgeColor_ne_zero e

theorem exists_taitEdgeColoring_gp12Graph :
    ∃ C : gp12Graph.EdgeColoring Color, IsTaitEdgeColoring gp12Graph C := by
  exact ⟨gp12TaitEdgeColoring, gp12TaitEdgeColoring_isTait⟩

def gp12CAP5BoundaryEdge : Fin 5 → gp12Graph.edgeSet
  | ⟨0, _⟩ => gp12_e0_1
  | ⟨1, _⟩ => gp12_e2_14
  | ⟨2, _⟩ => gp12_e3_4
  | ⟨3, _⟩ => gp12_e13_23
  | ⟨4, _⟩ => gp12_e15_17

def gp12CAP5RedBlueEdge₁ : Finset gp12Graph.edgeSet :=
  {gp12_e0_1, gp12_e13_23}

def gp12CAP5RedBlueEdge₂ : Finset gp12Graph.edgeSet :=
  {gp12_e2_14, gp12_e3_4}

def gp12CAP5RedPurpleEdge₁ : Finset gp12Graph.edgeSet :=
  {gp12_e0_1, gp12_e15_17}

def gp12CAP5RedPurpleEdge₂ : Finset gp12Graph.edgeSet :=
  {gp12_e2_14, gp12_e13_23}

theorem gp12CAP5RedBlueEdge₁_support :
    cap5BoundarySupportOfEdges gp12CAP5BoundaryEdge gp12CAP5RedBlueEdge₁ =
      ({0, 3} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, gp12CAP5BoundaryEdge, gp12CAP5RedBlueEdge₁,
      gp12_e0_1, gp12_e2_14, gp12_e3_4, gp12_e13_23, gp12_e15_17]

theorem gp12CAP5RedBlueEdge₂_support :
    cap5BoundarySupportOfEdges gp12CAP5BoundaryEdge gp12CAP5RedBlueEdge₂ =
      ({1, 2} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, gp12CAP5BoundaryEdge, gp12CAP5RedBlueEdge₂,
      gp12_e0_1, gp12_e2_14, gp12_e3_4, gp12_e13_23, gp12_e15_17]

theorem gp12CAP5RedPurpleEdge₁_support :
    cap5BoundarySupportOfEdges gp12CAP5BoundaryEdge gp12CAP5RedPurpleEdge₁ =
      ({0, 4} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, gp12CAP5BoundaryEdge, gp12CAP5RedPurpleEdge₁,
      gp12_e0_1, gp12_e2_14, gp12_e3_4, gp12_e13_23, gp12_e15_17]

theorem gp12CAP5RedPurpleEdge₂_support :
    cap5BoundarySupportOfEdges gp12CAP5BoundaryEdge gp12CAP5RedPurpleEdge₂ =
      ({1, 3} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, gp12CAP5BoundaryEdge, gp12CAP5RedPurpleEdge₂,
      gp12_e0_1, gp12_e2_14, gp12_e3_4, gp12_e13_23, gp12_e15_17]

def gp12CAP5ComponentCoverCore :
    CAP5TransportedEdgeComponentCoverCore gp12CAP5BoundaryEdge 0 where
  redBlueEdge₁ := gp12CAP5RedBlueEdge₁
  redBlueEdge₂ := gp12CAP5RedBlueEdge₂
  redPurpleEdge₁ := gp12CAP5RedPurpleEdge₁
  redPurpleEdge₂ := gp12CAP5RedPurpleEdge₂
  redBlue₁ := {0, 3}
  redBlue₂ := {1, 2}
  redPurple₁ := {0, 4}
  redPurple₂ := {1, 3}
  hredBlue₁ := by
    simpa [cap5RotateBoundarySupportN] using gp12CAP5RedBlueEdge₁_support
  hredBlue₂ := by
    simpa [cap5RotateBoundarySupportN] using gp12CAP5RedBlueEdge₂_support
  hredPurple₁ := by
    simpa [cap5RotateBoundarySupportN] using gp12CAP5RedPurpleEdge₁_support
  hredPurple₂ := by
    simpa [cap5RotateBoundarySupportN] using gp12CAP5RedPurpleEdge₂_support
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

theorem gp12CAP5ComponentCoverCore_isExceptional :
    gp12CAP5ComponentCoverCore.IsExceptional := by
  change CAP5BadExceptionalPairingPattern
    ({0, 3} : Finset (Fin 5)) ({1, 2} : Finset (Fin 5))
      ({0, 4} : Finset (Fin 5)) ({1, 3} : Finset (Fin 5))
  rw [CAP5BadExceptionalPairingPattern, CAP5BadRedBlueExceptionalPairing,
    CAP5BadRedPurpleExceptionalPairing]
  exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

def gp12FiveCutSide (v : Fin 24) : Prop :=
  v ∈ ({1, 2, 3, 13, 15} : Finset (Fin 24))

theorem gp12_e0_1_crosses_gp12FiveCutSide :
    EdgeCrossesVertexSide gp12Graph gp12FiveCutSide gp12_e0_1 := by
  refine ⟨1, 0, ?_, ?_, ?_, ?_⟩ <;> simp [gp12_e0_1, gp12FiveCutSide]

theorem gp12_e2_14_crosses_gp12FiveCutSide :
    EdgeCrossesVertexSide gp12Graph gp12FiveCutSide gp12_e2_14 := by
  refine ⟨2, 14, ?_, ?_, ?_, ?_⟩ <;> simp [gp12_e2_14, gp12FiveCutSide]

theorem gp12_e3_4_crosses_gp12FiveCutSide :
    EdgeCrossesVertexSide gp12Graph gp12FiveCutSide gp12_e3_4 := by
  refine ⟨3, 4, ?_, ?_, ?_, ?_⟩ <;> simp [gp12_e3_4, gp12FiveCutSide]

theorem gp12_e13_23_crosses_gp12FiveCutSide :
    EdgeCrossesVertexSide gp12Graph gp12FiveCutSide gp12_e13_23 := by
  refine ⟨13, 23, ?_, ?_, ?_, ?_⟩ <;> simp [gp12_e13_23, gp12FiveCutSide]

theorem gp12_e15_17_crosses_gp12FiveCutSide :
    EdgeCrossesVertexSide gp12Graph gp12FiveCutSide gp12_e15_17 := by
  refine ⟨15, 17, ?_, ?_, ?_, ?_⟩ <;> simp [gp12_e15_17, gp12FiveCutSide]

def gp12P0InsideP4OutsideEmittedFinset : Finset gp12Graph.edgeSet :=
  {gp12_e15_17}

def gp12P0InsideP4OutsideRemainingControls : Finset gp12Graph.edgeSet :=
  interiorEdgeSupport gp12Embedding.faceBoundary gp12Embedding.faces \
    gp12P0InsideP4OutsideEmittedFinset

def gp12P0InsideP4OutsideUnitEvader : gp12Graph.edgeSet → Color :=
  Pi.single gp12_e0_1 red

theorem gp12P0InsideP4OutsideUnitEvader_mem_planarBoundaryZeroSubmodule :
    gp12P0InsideP4OutsideUnitEvader ∈ planarBoundaryZeroSubmodule gp12Embedding := by
  intro e he
  rw [gp12_selectedBoundarySupport_eq_empty] at he
  simp at he

theorem gp12P0InsideP4OutsideUnitEvader_ne_zero :
    gp12P0InsideP4OutsideUnitEvader ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero gp12_e0_1
  simp [gp12P0InsideP4OutsideUnitEvader] at hvalue

theorem gp12P0InsideP4OutsideUnitEvader_zero_on_emitted :
    ∀ e ∈ gp12P0InsideP4OutsideEmittedFinset, gp12P0InsideP4OutsideUnitEvader e = 0 := by
  intro e he
  have heq : e = gp12_e15_17 := by
    simpa [gp12P0InsideP4OutsideEmittedFinset] using he
  rcases heq with rfl
  simp [gp12P0InsideP4OutsideUnitEvader, gp12_e0_1, gp12_e15_17]

theorem gp12_e0_1_mem_gp12P0InsideP4OutsideRemainingControls :
    gp12_e0_1 ∈ gp12P0InsideP4OutsideRemainingControls := by
  refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
  · exact gp12_e0_1_mem_interiorEdgeSupport
  · simp [gp12P0InsideP4OutsideEmittedFinset, gp12_e0_1, gp12_e15_17]

def gp12P0InsideP4OutsideF2Rank : Nat := 2
def gp12P0InsideP4OutsideF2KernelDimension : Nat := 70

structure GP12P0InsideP4OutsideKernelEvaderCertificate : Prop where
  rank : gp12P0InsideP4OutsideF2Rank = 2
  kernelDimension : gp12P0InsideP4OutsideF2KernelDimension = 70
  boundaryZero : gp12P0InsideP4OutsideUnitEvader ∈ planarBoundaryZeroSubmodule gp12Embedding
  nonzero : gp12P0InsideP4OutsideUnitEvader ≠ 0
  vanishesOnEmitted : ∀ e ∈ gp12P0InsideP4OutsideEmittedFinset, gp12P0InsideP4OutsideUnitEvader e = 0
  detectedRemaining : gp12_e0_1 ∈ gp12P0InsideP4OutsideRemainingControls ∧
    gp12P0InsideP4OutsideUnitEvader gp12_e0_1 = red

theorem gp12P0InsideP4OutsideKernelEvaderCertificate :
    GP12P0InsideP4OutsideKernelEvaderCertificate where
  rank := rfl
  kernelDimension := rfl
  boundaryZero := gp12P0InsideP4OutsideUnitEvader_mem_planarBoundaryZeroSubmodule
  nonzero := gp12P0InsideP4OutsideUnitEvader_ne_zero
  vanishesOnEmitted := gp12P0InsideP4OutsideUnitEvader_zero_on_emitted
  detectedRemaining := ⟨gp12_e0_1_mem_gp12P0InsideP4OutsideRemainingControls, by simp [gp12P0InsideP4OutsideUnitEvader]⟩

def gp12P0OutsideP4InsideEmittedFinset : Finset gp12Graph.edgeSet :=
  {gp12_e0_1}

def gp12P0OutsideP4InsideRemainingControls : Finset gp12Graph.edgeSet :=
  interiorEdgeSupport gp12Embedding.faceBoundary gp12Embedding.faces \
    gp12P0OutsideP4InsideEmittedFinset

def gp12P0OutsideP4InsideUnitEvader : gp12Graph.edgeSet → Color :=
  Pi.single gp12_e0_11 red

theorem gp12P0OutsideP4InsideUnitEvader_mem_planarBoundaryZeroSubmodule :
    gp12P0OutsideP4InsideUnitEvader ∈ planarBoundaryZeroSubmodule gp12Embedding := by
  intro e he
  rw [gp12_selectedBoundarySupport_eq_empty] at he
  simp at he

theorem gp12P0OutsideP4InsideUnitEvader_ne_zero :
    gp12P0OutsideP4InsideUnitEvader ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero gp12_e0_11
  simp [gp12P0OutsideP4InsideUnitEvader] at hvalue

theorem gp12P0OutsideP4InsideUnitEvader_zero_on_emitted :
    ∀ e ∈ gp12P0OutsideP4InsideEmittedFinset, gp12P0OutsideP4InsideUnitEvader e = 0 := by
  intro e he
  have heq : e = gp12_e0_1 := by
    simpa [gp12P0OutsideP4InsideEmittedFinset] using he
  rcases heq with rfl
  simp [gp12P0OutsideP4InsideUnitEvader, gp12_e0_11, gp12_e0_1]

theorem gp12_e0_11_mem_gp12P0OutsideP4InsideRemainingControls :
    gp12_e0_11 ∈ gp12P0OutsideP4InsideRemainingControls := by
  refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
  · exact gp12_e0_11_mem_interiorEdgeSupport
  · simp [gp12P0OutsideP4InsideEmittedFinset, gp12_e0_11, gp12_e0_1]

def gp12P0OutsideP4InsideF2Rank : Nat := 2
def gp12P0OutsideP4InsideF2KernelDimension : Nat := 70

structure GP12P0OutsideP4InsideKernelEvaderCertificate : Prop where
  rank : gp12P0OutsideP4InsideF2Rank = 2
  kernelDimension : gp12P0OutsideP4InsideF2KernelDimension = 70
  boundaryZero : gp12P0OutsideP4InsideUnitEvader ∈ planarBoundaryZeroSubmodule gp12Embedding
  nonzero : gp12P0OutsideP4InsideUnitEvader ≠ 0
  vanishesOnEmitted : ∀ e ∈ gp12P0OutsideP4InsideEmittedFinset, gp12P0OutsideP4InsideUnitEvader e = 0
  detectedRemaining : gp12_e0_11 ∈ gp12P0OutsideP4InsideRemainingControls ∧
    gp12P0OutsideP4InsideUnitEvader gp12_e0_11 = red

theorem gp12P0OutsideP4InsideKernelEvaderCertificate :
    GP12P0OutsideP4InsideKernelEvaderCertificate where
  rank := rfl
  kernelDimension := rfl
  boundaryZero := gp12P0OutsideP4InsideUnitEvader_mem_planarBoundaryZeroSubmodule
  nonzero := gp12P0OutsideP4InsideUnitEvader_ne_zero
  vanishesOnEmitted := gp12P0OutsideP4InsideUnitEvader_zero_on_emitted
  detectedRemaining := ⟨gp12_e0_11_mem_gp12P0OutsideP4InsideRemainingControls, by simp [gp12P0OutsideP4InsideUnitEvader]⟩

def gp12P0InsideP4InsideEmittedFinset : Finset gp12Graph.edgeSet :=
  {gp12_e15_17, gp12_e3_4}

def gp12P0InsideP4InsideRemainingControls : Finset gp12Graph.edgeSet :=
  interiorEdgeSupport gp12Embedding.faceBoundary gp12Embedding.faces \
    gp12P0InsideP4InsideEmittedFinset

def gp12P0InsideP4InsideUnitEvader : gp12Graph.edgeSet → Color :=
  Pi.single gp12_e0_1 red

theorem gp12P0InsideP4InsideUnitEvader_mem_planarBoundaryZeroSubmodule :
    gp12P0InsideP4InsideUnitEvader ∈ planarBoundaryZeroSubmodule gp12Embedding := by
  intro e he
  rw [gp12_selectedBoundarySupport_eq_empty] at he
  simp at he

theorem gp12P0InsideP4InsideUnitEvader_ne_zero :
    gp12P0InsideP4InsideUnitEvader ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero gp12_e0_1
  simp [gp12P0InsideP4InsideUnitEvader] at hvalue

theorem gp12P0InsideP4InsideUnitEvader_zero_on_emitted :
    ∀ e ∈ gp12P0InsideP4InsideEmittedFinset, gp12P0InsideP4InsideUnitEvader e = 0 := by
  intro e he
  have heq : e = gp12_e15_17 ∨ e = gp12_e3_4 := by
    simpa [gp12P0InsideP4InsideEmittedFinset] using he
  rcases heq with rfl | rfl <;> simp [gp12P0InsideP4InsideUnitEvader, gp12_e0_1, gp12_e15_17, gp12_e3_4]

theorem gp12_e0_1_mem_gp12P0InsideP4InsideRemainingControls :
    gp12_e0_1 ∈ gp12P0InsideP4InsideRemainingControls := by
  refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
  · exact gp12_e0_1_mem_interiorEdgeSupport
  · simp [gp12P0InsideP4InsideEmittedFinset, gp12_e0_1, gp12_e15_17, gp12_e3_4]

def gp12P0InsideP4InsideF2Rank : Nat := 4
def gp12P0InsideP4InsideF2KernelDimension : Nat := 68

structure GP12P0InsideP4InsideKernelEvaderCertificate : Prop where
  rank : gp12P0InsideP4InsideF2Rank = 4
  kernelDimension : gp12P0InsideP4InsideF2KernelDimension = 68
  boundaryZero : gp12P0InsideP4InsideUnitEvader ∈ planarBoundaryZeroSubmodule gp12Embedding
  nonzero : gp12P0InsideP4InsideUnitEvader ≠ 0
  vanishesOnEmitted : ∀ e ∈ gp12P0InsideP4InsideEmittedFinset, gp12P0InsideP4InsideUnitEvader e = 0
  detectedRemaining : gp12_e0_1 ∈ gp12P0InsideP4InsideRemainingControls ∧
    gp12P0InsideP4InsideUnitEvader gp12_e0_1 = red

theorem gp12P0InsideP4InsideKernelEvaderCertificate :
    GP12P0InsideP4InsideKernelEvaderCertificate where
  rank := rfl
  kernelDimension := rfl
  boundaryZero := gp12P0InsideP4InsideUnitEvader_mem_planarBoundaryZeroSubmodule
  nonzero := gp12P0InsideP4InsideUnitEvader_ne_zero
  vanishesOnEmitted := gp12P0InsideP4InsideUnitEvader_zero_on_emitted
  detectedRemaining := ⟨gp12_e0_1_mem_gp12P0InsideP4InsideRemainingControls, by simp [gp12P0InsideP4InsideUnitEvader]⟩

def gp12P0OutsideP4OutsideEmittedFinset : Finset gp12Graph.edgeSet :=
  {gp12_e13_23}

def gp12P0OutsideP4OutsideRemainingControls : Finset gp12Graph.edgeSet :=
  interiorEdgeSupport gp12Embedding.faceBoundary gp12Embedding.faces \
    gp12P0OutsideP4OutsideEmittedFinset

def gp12P0OutsideP4OutsideUnitEvader : gp12Graph.edgeSet → Color :=
  Pi.single gp12_e0_1 red

theorem gp12P0OutsideP4OutsideUnitEvader_mem_planarBoundaryZeroSubmodule :
    gp12P0OutsideP4OutsideUnitEvader ∈ planarBoundaryZeroSubmodule gp12Embedding := by
  intro e he
  rw [gp12_selectedBoundarySupport_eq_empty] at he
  simp at he

theorem gp12P0OutsideP4OutsideUnitEvader_ne_zero :
    gp12P0OutsideP4OutsideUnitEvader ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero gp12_e0_1
  simp [gp12P0OutsideP4OutsideUnitEvader] at hvalue

theorem gp12P0OutsideP4OutsideUnitEvader_zero_on_emitted :
    ∀ e ∈ gp12P0OutsideP4OutsideEmittedFinset, gp12P0OutsideP4OutsideUnitEvader e = 0 := by
  intro e he
  have heq : e = gp12_e13_23 := by
    simpa [gp12P0OutsideP4OutsideEmittedFinset] using he
  rcases heq with rfl
  simp [gp12P0OutsideP4OutsideUnitEvader, gp12_e0_1, gp12_e13_23]

theorem gp12_e0_1_mem_gp12P0OutsideP4OutsideRemainingControls :
    gp12_e0_1 ∈ gp12P0OutsideP4OutsideRemainingControls := by
  refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
  · exact gp12_e0_1_mem_interiorEdgeSupport
  · simp [gp12P0OutsideP4OutsideEmittedFinset, gp12_e0_1, gp12_e13_23]

def gp12P0OutsideP4OutsideF2Rank : Nat := 2
def gp12P0OutsideP4OutsideF2KernelDimension : Nat := 70

structure GP12P0OutsideP4OutsideKernelEvaderCertificate : Prop where
  rank : gp12P0OutsideP4OutsideF2Rank = 2
  kernelDimension : gp12P0OutsideP4OutsideF2KernelDimension = 70
  boundaryZero : gp12P0OutsideP4OutsideUnitEvader ∈ planarBoundaryZeroSubmodule gp12Embedding
  nonzero : gp12P0OutsideP4OutsideUnitEvader ≠ 0
  vanishesOnEmitted : ∀ e ∈ gp12P0OutsideP4OutsideEmittedFinset, gp12P0OutsideP4OutsideUnitEvader e = 0
  detectedRemaining : gp12_e0_1 ∈ gp12P0OutsideP4OutsideRemainingControls ∧
    gp12P0OutsideP4OutsideUnitEvader gp12_e0_1 = red

theorem gp12P0OutsideP4OutsideKernelEvaderCertificate :
    GP12P0OutsideP4OutsideKernelEvaderCertificate where
  rank := rfl
  kernelDimension := rfl
  boundaryZero := gp12P0OutsideP4OutsideUnitEvader_mem_planarBoundaryZeroSubmodule
  nonzero := gp12P0OutsideP4OutsideUnitEvader_ne_zero
  vanishesOnEmitted := gp12P0OutsideP4OutsideUnitEvader_zero_on_emitted
  detectedRemaining := ⟨gp12_e0_1_mem_gp12P0OutsideP4OutsideRemainingControls, by simp [gp12P0OutsideP4OutsideUnitEvader]⟩

theorem gp12_mem_remainingControlEdges_of_emittedFinset_eq
    {colorings : Set (gp12Graph.EdgeColoring Color)}
    {p0Inside p4Inside : Bool} {emitted : Finset gp12Graph.edgeSet}
    {e : gp12Graph.edgeSet}
    (input :
      CAP5FiniteNoGapRouteInput gp12CAP5ComponentCoverCore
        gp12Embedding gp12TaitEdgeColoring colorings p0Inside p4Inside
        gp12FiveCutSide)
    (heInterior : e ∈ interiorEdgeSupport gp12Embedding.faceBoundary gp12Embedding.faces)
    (hemitted : input.classifier.emittedFinset = emitted)
    (heNotEmitted : e ∉ emitted) :
    e ∈ input.classifier.remainingControlEdges
      (interiorEdgeSupport gp12Embedding.faceBoundary gp12Embedding.faces) :=
  (input.classifier.mem_remainingControlEdges_iff
    (interiorEdgeSupport gp12Embedding.faceBoundary gp12Embedding.faces) e).2
    ⟨heInterior, by
      rw [hemitted]
      exact heNotEmitted⟩

noncomputable def gp12P0InsideP4OutsideUnifiedKernelMapEvaderWitness
    {colorings : Set (gp12Graph.EdgeColoring Color)}
    (input :
      CAP5FiniteNoGapRouteInput gp12CAP5ComponentCoverCore
        gp12Embedding gp12TaitEdgeColoring colorings true false gp12FiveCutSide)
    (hemitted :
      input.classifier.emittedFinset = gp12P0InsideP4OutsideEmittedFinset) :
    CAP5FiniteUnifiedKernelMapEvaderWitness gp12CAP5ComponentCoverCore
      gp12Embedding gp12TaitEdgeColoring colorings true false gp12FiveCutSide :=
  input.toUnifiedKernelMapEvaderWitness_of_mem_remainingControlEdges
    (gp12_mem_remainingControlEdges_of_emittedFinset_eq input
      gp12_e0_1_mem_interiorEdgeSupport hemitted
      (by simp [gp12P0InsideP4OutsideEmittedFinset, gp12_e0_1, gp12_e15_17]))

noncomputable def gp12P0OutsideP4InsideUnifiedKernelMapEvaderWitness
    {colorings : Set (gp12Graph.EdgeColoring Color)}
    (input :
      CAP5FiniteNoGapRouteInput gp12CAP5ComponentCoverCore
        gp12Embedding gp12TaitEdgeColoring colorings false true gp12FiveCutSide)
    (hemitted :
      input.classifier.emittedFinset = gp12P0OutsideP4InsideEmittedFinset) :
    CAP5FiniteUnifiedKernelMapEvaderWitness gp12CAP5ComponentCoverCore
      gp12Embedding gp12TaitEdgeColoring colorings false true gp12FiveCutSide :=
  input.toUnifiedKernelMapEvaderWitness_of_mem_remainingControlEdges
    (gp12_mem_remainingControlEdges_of_emittedFinset_eq input
      gp12_e0_11_mem_interiorEdgeSupport hemitted
      (by simp [gp12P0OutsideP4InsideEmittedFinset, gp12_e0_11, gp12_e0_1]))

noncomputable def gp12P0InsideP4InsideUnifiedKernelMapEvaderWitness
    {colorings : Set (gp12Graph.EdgeColoring Color)}
    (input :
      CAP5FiniteNoGapRouteInput gp12CAP5ComponentCoverCore
        gp12Embedding gp12TaitEdgeColoring colorings true true gp12FiveCutSide)
    (hemitted :
      input.classifier.emittedFinset = gp12P0InsideP4InsideEmittedFinset) :
    CAP5FiniteUnifiedKernelMapEvaderWitness gp12CAP5ComponentCoverCore
      gp12Embedding gp12TaitEdgeColoring colorings true true gp12FiveCutSide :=
  input.toUnifiedKernelMapEvaderWitness_of_mem_remainingControlEdges
    (gp12_mem_remainingControlEdges_of_emittedFinset_eq input
      gp12_e0_1_mem_interiorEdgeSupport hemitted
      (by simp [gp12P0InsideP4InsideEmittedFinset, gp12_e0_1, gp12_e15_17, gp12_e3_4]))

noncomputable def gp12P0OutsideP4OutsideUnifiedKernelMapEvaderWitness
    {colorings : Set (gp12Graph.EdgeColoring Color)}
    (input :
      CAP5FiniteNoGapRouteInput gp12CAP5ComponentCoverCore
        gp12Embedding gp12TaitEdgeColoring colorings false false gp12FiveCutSide)
    (hemitted :
      input.classifier.emittedFinset = gp12P0OutsideP4OutsideEmittedFinset) :
    CAP5FiniteUnifiedKernelMapEvaderWitness gp12CAP5ComponentCoverCore
      gp12Embedding gp12TaitEdgeColoring colorings false false gp12FiveCutSide :=
  input.toUnifiedKernelMapEvaderWitness_of_mem_remainingControlEdges
    (gp12_mem_remainingControlEdges_of_emittedFinset_eq input
      gp12_e0_1_mem_interiorEdgeSupport hemitted
      (by simp [gp12P0OutsideP4OutsideEmittedFinset, gp12_e0_1, gp12_e13_23]))

end GP12CAP5RouteData

end Mettapedia.GraphTheory.FourColor
