import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

noncomputable section

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- Named vertices and edges of the triangle-contraction rotor. Structural
validity is kept in the separate computed predicate `WellFormed`. -/
structure FacialTriangleData where
  x : V
  y : V
  z : V
  xy : E
  xz : E
  yz : E
  outerX : E
  outerY : E
  outerZ : E

namespace FacialTriangleData

/-- Computed rotation-system conditions saying that the data are a facial
triangle with one outer edge at each cubic corner. -/
def WellFormed (T : @FacialTriangleData V E) : Prop :=
  ({T.x, T.y, T.z} : Finset V).card = 3 ∧
  RS.incidentEdges T.x = {T.outerX, T.xy, T.xz} ∧
  RS.incidentEdges T.y = {T.outerY, T.xy, T.yz} ∧
  RS.incidentEdges T.z = {T.outerZ, T.xz, T.yz} ∧
  ({T.xy, T.xz, T.yz} : Finset E) ∈ RS.internalFaces

end FacialTriangleData

private theorem pairwise_ne_of_triple_card_eq_three
    {a b c : E} (hcard : ({a, b, c} : Finset E).card = 3) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  constructor
  · intro hab
    subst b
    have hcard' : ({a, c} : Finset E).card = 3 := by simpa using hcard
    have hle : ({a, c} : Finset E).card ≤ 2 := Finset.card_le_two
    omega
  · constructor
    · intro hac
      subst c
      have hcard' : ({b, a} : Finset E).card = 3 := by simpa using hcard
      have hle : ({b, a} : Finset E).card ≤ 2 := Finset.card_le_two
      omega
    · intro hbc
      subst c
      have hcard' : ({a, b} : Finset E).card = 3 := by simpa using hcard
      have hle : ({a, b} : Finset E).card ≤ 2 := Finset.card_le_two
      omega

private theorem eq_add_of_three_distinct_nonzero {a b c : Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c = a + b := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    simp at hab hac hbc ⊢

/-- The three explicitly listed incident edges at each rotor corner are
pairwise distinct. This is derived from cubicity and the stored incidence
equalities, rather than assumed in the rotor data. -/
theorem facialTriangle_incidentEdgeDistinctness
    (T : @FacialTriangleData V E) (hT : T.WellFormed RS)
    (hCubic : RS.IsCubic) :
    (T.outerX ≠ T.xy ∧ T.outerX ≠ T.xz ∧ T.xy ≠ T.xz) ∧
    (T.outerY ≠ T.xy ∧ T.outerY ≠ T.yz ∧ T.xy ≠ T.yz) ∧
    (T.outerZ ≠ T.xz ∧ T.outerZ ≠ T.yz ∧ T.xz ≠ T.yz) := by
  have hxCard : ({T.outerX, T.xy, T.xz} : Finset E).card = 3 := by
    rw [← hT.2.1]
    exact RS.incidentEdges_card_eq_three_of_isCubic hCubic T.x
  have hyCard : ({T.outerY, T.xy, T.yz} : Finset E).card = 3 := by
    rw [← hT.2.2.1]
    exact RS.incidentEdges_card_eq_three_of_isCubic hCubic T.y
  have hzCard : ({T.outerZ, T.xz, T.yz} : Finset E).card = 3 := by
    rw [← hT.2.2.2.1]
    exact RS.incidentEdges_card_eq_three_of_isCubic hCubic T.z
  exact ⟨pairwise_ne_of_triple_card_eq_three hxCard,
    pairwise_ne_of_triple_card_eq_three hyCard,
    pairwise_ne_of_triple_card_eq_three hzCard⟩

/-- Local color forcing in the Rotor Lemma: each outer edge has the color of
the opposite triangle edge. -/
theorem rotor_outerColors_eq_oppositeTriangleEdges
    (T : @FacialTriangleData V E) (hT : T.WellFormed RS)
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    C T.outerX = C T.yz ∧
    C T.outerY = C T.xz ∧
    C T.outerZ = C T.xy := by
  have hdistinct := RS.facialTriangle_incidentEdgeDistinctness T hT hCubic
  have hxOuterMem : T.outerX ∈ RS.incidentEdges T.x := by rw [hT.2.1]; simp
  have hxXYMem : T.xy ∈ RS.incidentEdges T.x := by rw [hT.2.1]; simp
  have hxXZMem : T.xz ∈ RS.incidentEdges T.x := by rw [hT.2.1]; simp
  have hyOuterMem : T.outerY ∈ RS.incidentEdges T.y := by rw [hT.2.2.1]; simp
  have hyXYMem : T.xy ∈ RS.incidentEdges T.y := by rw [hT.2.2.1]; simp
  have hyYZMem : T.yz ∈ RS.incidentEdges T.y := by rw [hT.2.2.1]; simp
  have hzOuterMem : T.outerZ ∈ RS.incidentEdges T.z := by rw [hT.2.2.2.1]; simp
  have hzXZMem : T.xz ∈ RS.incidentEdges T.z := by rw [hT.2.2.2.1]; simp
  have hzYZMem : T.yz ∈ RS.incidentEdges T.z := by rw [hT.2.2.2.1]; simp
  have hXY_XZ : C T.xy ≠ C T.xz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.1.2.2 hxXYMem hxXZMem)
  have hXY_YZ : C T.xy ≠ C T.yz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.2.1.2.2 hyXYMem hyYZMem)
  have hXZ_YZ : C T.xz ≠ C T.yz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.2.2.2.2 hzXZMem hzYZMem)
  have hOuterX_XY : C T.outerX ≠ C T.xy := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.1.1 hxOuterMem hxXYMem)
  have hOuterX_XZ : C T.outerX ≠ C T.xz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.1.2.1 hxOuterMem hxXZMem)
  have hOuterY_XY : C T.outerY ≠ C T.xy := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.2.1.1 hyOuterMem hyXYMem)
  have hOuterY_YZ : C T.outerY ≠ C T.yz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.2.1.2.1 hyOuterMem hyYZMem)
  have hOuterZ_XZ : C T.outerZ ≠ C T.xz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.2.2.1 hzOuterMem hzXZMem)
  have hOuterZ_YZ : C T.outerZ ≠ C T.yz := C.valid
    (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hdistinct.2.2.2.1 hzOuterMem hzYZMem)
  constructor
  · have hOuter := eq_add_of_three_distinct_nonzero
      (hC T.xy) (hC T.xz) (hC T.outerX) hXY_XZ
      (Ne.symm hOuterX_XY) (Ne.symm hOuterX_XZ)
    have hOpposite := eq_add_of_three_distinct_nonzero
      (hC T.xy) (hC T.xz) (hC T.yz) hXY_XZ hXY_YZ hXZ_YZ
    exact hOuter.trans hOpposite.symm
  · constructor
    · have hOuter := eq_add_of_three_distinct_nonzero
        (hC T.xy) (hC T.yz) (hC T.outerY) hXY_YZ
        (Ne.symm hOuterY_XY) (Ne.symm hOuterY_YZ)
      have hOpposite := eq_add_of_three_distinct_nonzero
        (hC T.xy) (hC T.yz) (hC T.xz) hXY_YZ hXY_XZ hXZ_YZ.symm
      exact hOuter.trans hOpposite.symm
    · have hOuter := eq_add_of_three_distinct_nonzero
        (hC T.xz) (hC T.yz) (hC T.outerZ) hXZ_YZ
        (Ne.symm hOuterZ_XZ) (Ne.symm hOuterZ_YZ)
      have hOpposite := eq_add_of_three_distinct_nonzero
        (hC T.xz) (hC T.yz) (hC T.xy) hXZ_YZ
        (Ne.symm hXY_XZ) (Ne.symm hXY_YZ)
      exact hOuter.trans hOpposite.symm

/-- An alternating four-edge segment gives a concrete path in the selected
bicolored edge graph. -/
theorem bicolored_reachable_of_alternating_four_edge_segment
    (C : RS.EdgeColoring Color) {a b : Color}
    {e0 e1 e2 e3 : E}
    (h0 : C e0 = a) (h1 : C e1 = b)
    (h2 : C e2 = a) (h3 : C e3 = b)
    (h01 : RS.edgeAdjacencyGraph.Adj e0 e1)
    (h12 : RS.edgeAdjacencyGraph.Adj e1 e2)
    (h23 : RS.edgeAdjacencyGraph.Adj e2 e3) :
    (C.bicoloredSubgraph a b).Reachable
      ⟨e0, Or.inl h0⟩ ⟨e3, Or.inr h3⟩ := by
  let v0 : C.bicoloredSet a b := ⟨e0, Or.inl h0⟩
  let v1 : C.bicoloredSet a b := ⟨e1, Or.inr h1⟩
  let v2 : C.bicoloredSet a b := ⟨e2, Or.inl h2⟩
  let v3 : C.bicoloredSet a b := ⟨e3, Or.inr h3⟩
  exact ⟨Walk.cons (show (C.bicoloredSubgraph a b).Adj v0 v1 from h01)
    (Walk.cons (show (C.bicoloredSubgraph a b).Adj v1 v2 from h12)
      (Walk.cons (show (C.bicoloredSubgraph a b).Adj v2 v3 from h23)
        Walk.nil))⟩

/-- Rotor through-paths: each of the three two-color passages through a
contracted cubic vertex has the manuscript's explicit lifted route through
the facial triangle. -/
theorem rotor_three_bicoloredThroughPaths
    (T : @FacialTriangleData V E) (hT : T.WellFormed RS)
    (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    (C.bicoloredSubgraph (C T.outerX) (C T.outerY)).Reachable
        ⟨T.outerX, Or.inl rfl⟩ ⟨T.outerY, Or.inr rfl⟩ ∧
    (C.bicoloredSubgraph (C T.outerX) (C T.outerZ)).Reachable
        ⟨T.outerX, Or.inl rfl⟩ ⟨T.outerZ, Or.inr rfl⟩ ∧
    (C.bicoloredSubgraph (C T.outerY) (C T.outerZ)).Reachable
        ⟨T.outerY, Or.inl rfl⟩ ⟨T.outerZ, Or.inr rfl⟩ := by
  have hdistinct := RS.facialTriangle_incidentEdgeDistinctness T hT hCubic
  have hcolors := RS.rotor_outerColors_eq_oppositeTriangleEdges T hT hCubic C hC
  have hxOuterMem : T.outerX ∈ RS.incidentEdges T.x := by rw [hT.2.1]; simp
  have hxXYMem : T.xy ∈ RS.incidentEdges T.x := by rw [hT.2.1]; simp
  have hxXZMem : T.xz ∈ RS.incidentEdges T.x := by rw [hT.2.1]; simp
  have hyOuterMem : T.outerY ∈ RS.incidentEdges T.y := by rw [hT.2.2.1]; simp
  have hyXYMem : T.xy ∈ RS.incidentEdges T.y := by rw [hT.2.2.1]; simp
  have hyYZMem : T.yz ∈ RS.incidentEdges T.y := by rw [hT.2.2.1]; simp
  have hzOuterMem : T.outerZ ∈ RS.incidentEdges T.z := by rw [hT.2.2.2.1]; simp
  have hzXZMem : T.xz ∈ RS.incidentEdges T.z := by rw [hT.2.2.2.1]; simp
  have hzYZMem : T.yz ∈ RS.incidentEdges T.z := by rw [hT.2.2.2.1]; simp
  constructor
  · apply RS.bicolored_reachable_of_alternating_four_edge_segment C
      rfl hcolors.2.1.symm hcolors.1.symm rfl
    · exact RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
        hdistinct.1.2.1 hxOuterMem hxXZMem
    · exact RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
        hdistinct.2.2.2.2 hzXZMem hzYZMem
    · exact RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
        hdistinct.2.1.2.1.symm hyYZMem hyOuterMem
  · constructor
    · apply RS.bicolored_reachable_of_alternating_four_edge_segment C
        rfl hcolors.2.2.symm hcolors.1.symm rfl
      · exact RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
          hdistinct.1.1 hxOuterMem hxXYMem
      · exact RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
          hdistinct.2.1.2.2 hyXYMem hyYZMem
      · exact RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
          hdistinct.2.2.2.1.symm hzYZMem hzOuterMem
    · apply RS.bicolored_reachable_of_alternating_four_edge_segment C
        rfl hcolors.2.2.symm hcolors.2.1.symm rfl
      · exact RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
          hdistinct.2.1.1 hyOuterMem hyXYMem
      · exact RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
          hdistinct.1.2.2 hxXYMem hxXZMem
      · exact RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
          hdistinct.2.2.1.symm hzXZMem hzOuterMem

end RotationSystem

end

end Mettapedia.GraphTheory.FourColor
