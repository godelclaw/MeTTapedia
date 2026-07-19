import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphTaitBridge

/-!
# Six-vertex four-cycle reducibility

A cubic simple graph on six vertices containing the cycle `0-1-2-3-0`
has no freedom beyond choosing which two cycle vertices meet vertex `4`;
vertex `5` meets the complementary pair.  The six possible pairs are
`01`, `02`, `03`, `12`, `13`, and `23`.  Each resulting graph is split
below into three explicit perfect matchings, which give its Tait coloring.

The final theorem transports this six-pattern argument across an arbitrary
vertex equivalence.  Thus the certificate is a local graph theorem rather
than a classification assumption about a minimal counterexample.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SixVertexFourCycle

open SimpleGraph

local instance sixVertexLocallyFinite
    {W : Type*} [Fintype W] {H : SimpleGraph W}
    [decidableAdjacency : DecidableRel H.Adj] : H.LocallyFinite :=
  fun vertex =>
    @Subtype.fintype W (Membership.mem (H.neighborSet vertex))
      (decidableAdjacency vertex) inferInstance

local instance (G : SimpleGraph (Fin 6)) : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance (G : SimpleGraph (Fin 6)) :
    DecidableRel G.lineGraph.Adj := fun first second =>
  decidable_of_iff'
    (first ≠ second ∧ ∃ vertex : Fin 6,
      vertex ∈ (first : Sym2 (Fin 6)) ∧
        vertex ∈ (second : Sym2 (Fin 6)))
    SimpleGraph.lineGraph_adj_iff_exists

/-- Color two disjoint perfect matchings red and blue; all remaining edges
receive purple. -/
def matchingPairColor (first second : Finset (Sym2 (Fin 6)))
    {G : SimpleGraph (Fin 6)} (edge : G.edgeSet) : Color :=
  if edge.1 ∈ first then red else if edge.1 ∈ second then blue else purple

theorem matchingPairColor_ne_zero
    (first second : Finset (Sym2 (Fin 6)))
    {G : SimpleGraph (Fin 6)} (edge : G.edgeSet) :
    matchingPairColor first second edge ≠ 0 := by
  unfold matchingPairColor
  split
  · simp
  · split <;> simp

/-- The six attachment graphs.  The suffix records the two cycle vertices
adjacent to vertex `4`; vertex `5` is adjacent to the complementary pair. -/
def sixCycleGraph01 : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet
  {s(0, 1), s(1, 2), s(2, 3), s(0, 3), s(4, 5),
   s(0, 4), s(1, 4), s(2, 5), s(3, 5)}

instance : DecidableRel sixCycleGraph01.Adj := by
  unfold sixCycleGraph01
  infer_instance

def sixCycleGraph01Coloring : sixCycleGraph01.EdgeColoring Color :=
  SimpleGraph.Coloring.mk
    (matchingPairColor
      {s(0, 1), s(2, 3), s(4, 5)}
      {s(0, 3), s(1, 4), s(2, 5)}) (by decide)

theorem sixCycleGraph01Coloring_isTait :
    IsTaitEdgeColoring sixCycleGraph01 sixCycleGraph01Coloring := by
  intro edge
  change matchingPairColor
    {s(0, 1), s(2, 3), s(4, 5)}
    {s(0, 3), s(1, 4), s(2, 5)} edge ≠ 0
  exact matchingPairColor_ne_zero _ _ edge


def sixCycleGraph02 : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet
  {s(0, 1), s(1, 2), s(2, 3), s(0, 3), s(4, 5),
   s(0, 4), s(2, 4), s(1, 5), s(3, 5)}

instance : DecidableRel sixCycleGraph02.Adj := by
  unfold sixCycleGraph02
  infer_instance

def sixCycleGraph02Coloring : sixCycleGraph02.EdgeColoring Color :=
  SimpleGraph.Coloring.mk
    (matchingPairColor
      {s(0, 1), s(2, 3), s(4, 5)}
      {s(0, 3), s(1, 5), s(2, 4)}) (by decide)

theorem sixCycleGraph02Coloring_isTait :
    IsTaitEdgeColoring sixCycleGraph02 sixCycleGraph02Coloring :=
  fun edge => matchingPairColor_ne_zero _ _ edge

def sixCycleGraph03 : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet
  {s(0, 1), s(1, 2), s(2, 3), s(0, 3), s(4, 5),
   s(0, 4), s(3, 4), s(1, 5), s(2, 5)}

instance : DecidableRel sixCycleGraph03.Adj := by
  unfold sixCycleGraph03
  infer_instance

def sixCycleGraph03Coloring : sixCycleGraph03.EdgeColoring Color :=
  SimpleGraph.Coloring.mk
    (matchingPairColor
      {s(0, 1), s(2, 5), s(3, 4)}
      {s(0, 3), s(1, 2), s(4, 5)}) (by decide)

theorem sixCycleGraph03Coloring_isTait :
    IsTaitEdgeColoring sixCycleGraph03 sixCycleGraph03Coloring :=
  fun edge => matchingPairColor_ne_zero _ _ edge

def sixCycleGraph12 : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet
  {s(0, 1), s(1, 2), s(2, 3), s(0, 3), s(4, 5),
   s(1, 4), s(2, 4), s(0, 5), s(3, 5)}

instance : DecidableRel sixCycleGraph12.Adj := by
  unfold sixCycleGraph12
  infer_instance

def sixCycleGraph12Coloring : sixCycleGraph12.EdgeColoring Color :=
  SimpleGraph.Coloring.mk
    (matchingPairColor
      {s(0, 1), s(2, 4), s(3, 5)}
      {s(0, 3), s(1, 2), s(4, 5)}) (by decide)

theorem sixCycleGraph12Coloring_isTait :
    IsTaitEdgeColoring sixCycleGraph12 sixCycleGraph12Coloring :=
  fun edge => matchingPairColor_ne_zero _ _ edge

def sixCycleGraph13 : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet
  {s(0, 1), s(1, 2), s(2, 3), s(0, 3), s(4, 5),
   s(1, 4), s(3, 4), s(0, 5), s(2, 5)}

instance : DecidableRel sixCycleGraph13.Adj := by
  unfold sixCycleGraph13
  infer_instance

def sixCycleGraph13Coloring : sixCycleGraph13.EdgeColoring Color :=
  SimpleGraph.Coloring.mk
    (matchingPairColor
      {s(0, 1), s(2, 3), s(4, 5)}
      {s(0, 3), s(1, 4), s(2, 5)}) (by decide)

theorem sixCycleGraph13Coloring_isTait :
    IsTaitEdgeColoring sixCycleGraph13 sixCycleGraph13Coloring :=
  fun edge => matchingPairColor_ne_zero _ _ edge

def sixCycleGraph23 : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet
  {s(0, 1), s(1, 2), s(2, 3), s(0, 3), s(4, 5),
   s(2, 4), s(3, 4), s(0, 5), s(1, 5)}

instance : DecidableRel sixCycleGraph23.Adj := by
  unfold sixCycleGraph23
  infer_instance

def sixCycleGraph23Coloring : sixCycleGraph23.EdgeColoring Color :=
  SimpleGraph.Coloring.mk
    (matchingPairColor
      {s(0, 1), s(2, 3), s(4, 5)}
      {s(0, 3), s(1, 5), s(2, 4)}) (by decide)

theorem sixCycleGraph23Coloring_isTait :
    IsTaitEdgeColoring sixCycleGraph23 sixCycleGraph23Coloring :=
  fun edge => matchingPairColor_ne_zero _ _ edge

theorem graph_eq_sixCycleGraph01
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (h01 : G.Adj 0 1) (h12 : G.Adj 1 2)
    (h23 : G.Adj 2 3) (h30 : G.Adj 3 0)
    (h02 : ¬ G.Adj 0 2) (h13 : ¬ G.Adj 1 3)
    (h45 : G.Adj 4 5)
    (h04 : G.Adj 0 4) (h14 : G.Adj 1 4)
    (h24 : ¬ G.Adj 2 4) (h34 : ¬ G.Adj 3 4)
    (h05 : ¬ G.Adj 0 5) (h15 : ¬ G.Adj 1 5)
    (h25 : G.Adj 2 5) (h35 : G.Adj 3 5) :
    G = sixCycleGraph01 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp_all [sixCycleGraph01]
  all_goals
    rw [G.adj_comm]
    assumption

/-- At each vertex of the distinguished four-cycle, cubicity forces exactly
one of the two outside vertices to be adjacent. -/
theorem finSix_adjacent_four_iff_not_adjacent_five_of_degree_three_at_zero
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hdegree : G.degree 0 = 3)
    (h01 : G.Adj 0 1) (h02 : ¬ G.Adj 0 2) (h03 : G.Adj 0 3) :
    G.Adj 0 4 ↔ ¬ G.Adj 0 5 := by
  have hneighbors : (G.neighborFinset 0).card = 3 := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree
  have hneighborFilter : G.neighborFinset 0 =
      Finset.univ.filter fun vertex => G.Adj 0 vertex := by
    ext vertex
    simp
  rw [hneighborFilter] at hneighbors
  have huniv6 : (Finset.univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} := by
    decide
  rw [huniv6] at hneighbors
  have h00 : ¬ G.Adj 0 0 := G.loopless.irrefl 0
  by_cases h04 : G.Adj 0 4 <;> by_cases h05 : G.Adj 0 5
  all_goals
    simp only [Finset.filter_insert, Finset.filter_singleton,
      h00, h01, h02, h03, h04, h05, if_pos] at hneighbors
  all_goals try
    exfalso
    revert hneighbors
    decide
  all_goals simp [h04, h05]

theorem finSix_adjacent_four_iff_not_adjacent_five_of_degree_three_at_one
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hdegree : G.degree 1 = 3)
    (h10 : G.Adj 1 0) (h12 : G.Adj 1 2) (h13 : ¬ G.Adj 1 3) :
    G.Adj 1 4 ↔ ¬ G.Adj 1 5 := by
  have hneighbors : (G.neighborFinset 1).card = 3 := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree
  have hneighborFilter : G.neighborFinset 1 =
      Finset.univ.filter fun vertex => G.Adj 1 vertex := by
    ext vertex
    simp
  rw [hneighborFilter] at hneighbors
  have huniv6 : (Finset.univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} := by
    decide
  rw [huniv6] at hneighbors
  have h11 : ¬ G.Adj 1 1 := G.loopless.irrefl 1
  by_cases h14 : G.Adj 1 4 <;> by_cases h15 : G.Adj 1 5
  all_goals
    simp only [Finset.filter_insert, Finset.filter_singleton,
      h10, h11, h12, h13, h14, h15, if_pos] at hneighbors
  all_goals try
    exfalso
    revert hneighbors
    decide
  all_goals simp [h14, h15]

theorem finSix_adjacent_four_iff_not_adjacent_five_of_degree_three_at_two
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hdegree : G.degree 2 = 3)
    (h20 : ¬ G.Adj 2 0) (h21 : G.Adj 2 1) (h23 : G.Adj 2 3) :
    G.Adj 2 4 ↔ ¬ G.Adj 2 5 := by
  have hneighbors : (G.neighborFinset 2).card = 3 := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree
  have hneighborFilter : G.neighborFinset 2 =
      Finset.univ.filter fun vertex => G.Adj 2 vertex := by
    ext vertex
    simp
  rw [hneighborFilter] at hneighbors
  have huniv6 : (Finset.univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} := by
    decide
  rw [huniv6] at hneighbors
  have h22 : ¬ G.Adj 2 2 := G.loopless.irrefl 2
  by_cases h24 : G.Adj 2 4 <;> by_cases h25 : G.Adj 2 5
  all_goals
    simp only [Finset.filter_insert, Finset.filter_singleton,
      h20, h21, h22, h23, h24, h25, if_pos] at hneighbors
  all_goals try
    exfalso
    revert hneighbors
    decide
  all_goals simp [h24, h25]

theorem finSix_adjacent_four_iff_not_adjacent_five_of_degree_three_at_three
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hdegree : G.degree 3 = 3)
    (h30 : G.Adj 3 0) (h31 : ¬ G.Adj 3 1) (h32 : G.Adj 3 2) :
    G.Adj 3 4 ↔ ¬ G.Adj 3 5 := by
  have hneighbors : (G.neighborFinset 3).card = 3 := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree
  have hneighborFilter : G.neighborFinset 3 =
      Finset.univ.filter fun vertex => G.Adj 3 vertex := by
    ext vertex
    simp
  rw [hneighborFilter] at hneighbors
  have huniv6 : (Finset.univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} := by
    decide
  rw [huniv6] at hneighbors
  have h33 : ¬ G.Adj 3 3 := G.loopless.irrefl 3
  by_cases h34 : G.Adj 3 4 <;> by_cases h35 : G.Adj 3 5
  all_goals
    simp only [Finset.filter_insert, Finset.filter_singleton,
      h30, h31, h32, h33, h34, h35, if_pos] at hneighbors
  all_goals try
    exfalso
    revert hneighbors
    decide
  all_goals simp [h34, h35]

/-- Cubicity at the two outside vertices forces their connecting edge and
exactly two attachments from vertex `4` to the four-cycle. -/
theorem finSix_edge_four_five_and_two_attachments_of_degree_three
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hdegree4 : G.degree 4 = 3) (hdegree5 : G.degree 5 = 3)
    (hcross0 : G.Adj 0 4 ↔ ¬ G.Adj 0 5)
    (hcross1 : G.Adj 1 4 ↔ ¬ G.Adj 1 5)
    (hcross2 : G.Adj 2 4 ↔ ¬ G.Adj 2 5)
    (hcross3 : G.Adj 3 4 ↔ ¬ G.Adj 3 5) :
    G.Adj 4 5 ∧
      (({0, 1, 2, 3} : Finset (Fin 6)).filter fun vertex =>
        G.Adj vertex 4).card = 2 := by
  have hneighbors4 : (G.neighborFinset 4).card = 3 := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree4
  have hneighbors5 : (G.neighborFinset 5).card = 3 := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree5
  have hneighborFilter4 : G.neighborFinset 4 =
      Finset.univ.filter fun vertex => G.Adj 4 vertex := by
    ext vertex
    simp
  have hneighborFilter5 : G.neighborFinset 5 =
      Finset.univ.filter fun vertex => G.Adj 5 vertex := by
    ext vertex
    simp
  rw [hneighborFilter4] at hneighbors4
  rw [hneighborFilter5] at hneighbors5
  have huniv6 : (Finset.univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} := by
    decide
  rw [huniv6] at hneighbors4 hneighbors5
  have h40 : G.Adj 4 0 ↔ G.Adj 0 4 := G.adj_comm 4 0
  have h41 : G.Adj 4 1 ↔ G.Adj 1 4 := G.adj_comm 4 1
  have h42 : G.Adj 4 2 ↔ G.Adj 2 4 := G.adj_comm 4 2
  have h43 : G.Adj 4 3 ↔ G.Adj 3 4 := G.adj_comm 4 3
  have h44 : ¬ G.Adj 4 4 := G.loopless.irrefl 4
  have h50 : G.Adj 5 0 ↔ ¬ G.Adj 0 4 := by
    rw [G.adj_comm]
    constructor
    · intro h05 h04
      exact (hcross0.mp h04) h05
    · intro h04
      by_contra h05
      exact h04 (hcross0.mpr h05)
  have h51 : G.Adj 5 1 ↔ ¬ G.Adj 1 4 := by
    rw [G.adj_comm]
    constructor
    · intro h15 h14
      exact (hcross1.mp h14) h15
    · intro h14
      by_contra h15
      exact h14 (hcross1.mpr h15)
  have h52 : G.Adj 5 2 ↔ ¬ G.Adj 2 4 := by
    rw [G.adj_comm]
    constructor
    · intro h25 h24
      exact (hcross2.mp h24) h25
    · intro h24
      by_contra h25
      exact h24 (hcross2.mpr h25)
  have h53 : G.Adj 5 3 ↔ ¬ G.Adj 3 4 := by
    rw [G.adj_comm]
    constructor
    · intro h35 h34
      exact (hcross3.mp h34) h35
    · intro h34
      by_contra h35
      exact h34 (hcross3.mpr h35)
  have h54 : G.Adj 5 4 ↔ G.Adj 4 5 := G.adj_comm 5 4
  have h55 : ¬ G.Adj 5 5 := G.loopless.irrefl 5
  by_cases h04 : G.Adj 0 4 <;>
    by_cases h14 : G.Adj 1 4 <;>
    by_cases h24 : G.Adj 2 4 <;>
    by_cases h34 : G.Adj 3 4 <;>
    by_cases h45 : G.Adj 4 5
  all_goals
    simp only [Finset.filter_insert, Finset.filter_singleton,
      h40, h41, h42, h43, h44, h04, h14, h24, h34, h45,
      if_pos] at hneighbors4
  all_goals try
    exfalso
    revert hneighbors4
    decide
  all_goals
    simp only [Finset.filter_insert, Finset.filter_singleton,
      h50, h51, h52, h53, h54, h55, h04, h14, h24, h34, h45,
      not_true_eq_false, not_false_eq_true, if_pos] at hneighbors5
  all_goals try
    exfalso
    revert hneighbors5
    decide
  all_goals
    constructor
    · exact h45
    · simp only [Finset.filter_insert, Finset.filter_singleton,
        h04, h14, h24, h34, if_pos]
      decide

set_option maxHeartbeats 600000 in
/-- The six attachment patterns exhaust every graph with the displayed
local incidence data, and every pattern has the explicit matching coloring
above. -/
theorem six_cycle_attachment_tait_colorable
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (h01 : G.Adj 0 1) (h12 : G.Adj 1 2)
    (h23 : G.Adj 2 3) (h30 : G.Adj 3 0)
    (h02 : ¬ G.Adj 0 2) (h13 : ¬ G.Adj 1 3)
    (h45 : G.Adj 4 5)
    (hcross : ∀ vertex : Fin 4,
      G.Adj (Fin.castLE (by omega) vertex) 4 ↔
        ¬ G.Adj (Fin.castLE (by omega) vertex) 5)
    (hcount : (({0, 1, 2, 3} : Finset (Fin 6)).filter fun vertex =>
      G.Adj vertex 4).card = 2) :
    ∃ coloring : G.EdgeColoring Color,
      IsTaitEdgeColoring G coloring := by
  have hcross0 : G.Adj 0 4 ↔ ¬ G.Adj 0 5 := by
    simpa using hcross 0
  have hcross1 : G.Adj 1 4 ↔ ¬ G.Adj 1 5 := by
    simpa using hcross 1
  have hcross2 : G.Adj 2 4 ↔ ¬ G.Adj 2 5 := by
    simpa using hcross 2
  have hcross3 : G.Adj 3 4 ↔ ¬ G.Adj 3 5 := by
    simpa using hcross 3
  by_cases h04 : G.Adj 0 4 <;>
    by_cases h14 : G.Adj 1 4 <;>
    by_cases h24 : G.Adj 2 4 <;>
    by_cases h34 : G.Adj 3 4
  all_goals
    simp only [Finset.filter_insert, Finset.filter_singleton,
      h04, h14, h24, h34, if_pos] at hcount
  all_goals try
    exfalso
    revert hcount
    decide
  · have hgraph : G = sixCycleGraph01 := by
      apply graph_eq_sixCycleGraph01 G h01 h12 h23 h30 h02 h13 h45
        h04 h14 h24 h34
      · exact hcross0.mp h04
      · exact hcross1.mp h14
      · by_contra hnot
        exact h24 (hcross2.mpr hnot)
      · by_contra hnot
        exact h34 (hcross3.mpr hnot)
    rw [hgraph]
    exact ⟨sixCycleGraph01Coloring, sixCycleGraph01Coloring_isTait⟩
  · have hgraph : G = sixCycleGraph02 := by
      have h05 : ¬ G.Adj 0 5 := hcross0.mp h04
      have h15 : G.Adj 1 5 := by
        by_contra hnot
        exact h14 (hcross1.mpr hnot)
      have h25 : ¬ G.Adj 2 5 := hcross2.mp h24
      have h35 : G.Adj 3 5 := by
        by_contra hnot
        exact h34 (hcross3.mpr hnot)
      clear hcross0 hcross1 hcross2 hcross3 hcross hcount
      ext first second
      fin_cases first <;> fin_cases second <;>
        simp_all [sixCycleGraph02]
      all_goals
        rw [G.adj_comm]
        assumption
    rw [hgraph]
    exact ⟨sixCycleGraph02Coloring, sixCycleGraph02Coloring_isTait⟩
  · have hgraph : G = sixCycleGraph03 := by
      have h05 : ¬ G.Adj 0 5 := hcross0.mp h04
      have h15 : G.Adj 1 5 := by
        by_contra hnot
        exact h14 (hcross1.mpr hnot)
      have h25 : G.Adj 2 5 := by
        by_contra hnot
        exact h24 (hcross2.mpr hnot)
      have h35 : ¬ G.Adj 3 5 := hcross3.mp h34
      clear hcross0 hcross1 hcross2 hcross3 hcross hcount
      ext first second
      fin_cases first <;> fin_cases second <;>
        simp_all [sixCycleGraph03]
      all_goals
        rw [G.adj_comm]
        assumption
    rw [hgraph]
    exact ⟨sixCycleGraph03Coloring, sixCycleGraph03Coloring_isTait⟩
  · have hgraph : G = sixCycleGraph12 := by
      have h05 : G.Adj 0 5 := by
        by_contra hnot
        exact h04 (hcross0.mpr hnot)
      have h15 : ¬ G.Adj 1 5 := hcross1.mp h14
      have h25 : ¬ G.Adj 2 5 := hcross2.mp h24
      have h35 : G.Adj 3 5 := by
        by_contra hnot
        exact h34 (hcross3.mpr hnot)
      clear hcross0 hcross1 hcross2 hcross3 hcross hcount
      ext first second
      fin_cases first <;> fin_cases second <;>
        simp_all [sixCycleGraph12]
      all_goals
        rw [G.adj_comm]
        assumption
    rw [hgraph]
    exact ⟨sixCycleGraph12Coloring, sixCycleGraph12Coloring_isTait⟩
  · have hgraph : G = sixCycleGraph13 := by
      have h05 : G.Adj 0 5 := by
        by_contra hnot
        exact h04 (hcross0.mpr hnot)
      have h15 : ¬ G.Adj 1 5 := hcross1.mp h14
      have h25 : G.Adj 2 5 := by
        by_contra hnot
        exact h24 (hcross2.mpr hnot)
      have h35 : ¬ G.Adj 3 5 := hcross3.mp h34
      clear hcross0 hcross1 hcross2 hcross3 hcross hcount
      ext first second
      fin_cases first <;> fin_cases second <;>
        simp_all [sixCycleGraph13]
      all_goals
        rw [G.adj_comm]
        assumption
    rw [hgraph]
    exact ⟨sixCycleGraph13Coloring, sixCycleGraph13Coloring_isTait⟩
  · have hgraph : G = sixCycleGraph23 := by
      have h05 : G.Adj 0 5 := by
        by_contra hnot
        exact h04 (hcross0.mpr hnot)
      have h15 : G.Adj 1 5 := by
        by_contra hnot
        exact h14 (hcross1.mpr hnot)
      have h25 : ¬ G.Adj 2 5 := hcross2.mp h24
      have h35 : ¬ G.Adj 3 5 := hcross3.mp h34
      clear hcross0 hcross1 hcross2 hcross3 hcross hcount
      ext first second
      fin_cases first <;> fin_cases second <;>
        simp_all [sixCycleGraph23]
      all_goals
        rw [G.adj_comm]
        assumption
    rw [hgraph]
    exact ⟨sixCycleGraph23Coloring, sixCycleGraph23Coloring_isTait⟩

/-- Every cubic graph on `Fin 6` containing the distinguished chordless
four-cycle is Tait colorable. -/
theorem finSix_fourCycle_tait_colorable_of_cubic
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hregular : G.IsRegularOfDegree 3)
    (h01 : G.Adj 0 1) (h12 : G.Adj 1 2)
    (h23 : G.Adj 2 3) (h30 : G.Adj 3 0)
    (h02 : ¬ G.Adj 0 2) (h13 : ¬ G.Adj 1 3) :
    ∃ coloring : G.EdgeColoring Color,
      IsTaitEdgeColoring G coloring := by
  have h20 : ¬ G.Adj 2 0 := fun hadj => h02 hadj.symm
  have h31 : ¬ G.Adj 3 1 := fun hadj => h13 hadj.symm
  have hcross0 :=
    finSix_adjacent_four_iff_not_adjacent_five_of_degree_three_at_zero
      G (hregular.degree_eq 0) h01 h02 h30.symm
  have hcross1 :=
    finSix_adjacent_four_iff_not_adjacent_five_of_degree_three_at_one
      G (hregular.degree_eq 1) h01.symm h12 h13
  have hcross2 :=
    finSix_adjacent_four_iff_not_adjacent_five_of_degree_three_at_two
      G (hregular.degree_eq 2) h20 h12.symm h23
  have hcross3 :=
    finSix_adjacent_four_iff_not_adjacent_five_of_degree_three_at_three
      G (hregular.degree_eq 3) h30 h31 h23.symm
  obtain ⟨h45, hcount⟩ :=
    finSix_edge_four_five_and_two_attachments_of_degree_three
      G (hregular.degree_eq 4) (hregular.degree_eq 5)
        hcross0 hcross1 hcross2 hcross3
  apply six_cycle_attachment_tait_colorable G
    h01 h12 h23 h30 h02 h13 h45
  · intro vertex
    fin_cases vertex
    · simpa using hcross0
    · simpa using hcross1
    · simpa using hcross2
    · simpa using hcross3
  · exact hcount

/-- A six-element carrier can be labeled so that any four named distinct
vertices receive labels `0,1,2,3` in the prescribed order. -/
theorem exists_finSix_label_mapping_four
    {V : Type*} [Fintype V] [DecidableEq V]
    {first second third fourth : V}
    (hcard : Fintype.card V = 6)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hfirstFourth : first ≠ fourth)
    (hsecondThird : second ≠ third)
    (hsecondFourth : second ≠ fourth)
    (hthirdFourth : third ≠ fourth) :
    ∃ label : V ≃ Fin 6,
      label first = 0 ∧ label second = 1 ∧
        label third = 2 ∧ label fourth = 3 := by
  classical
  let side : Finset V := {first, second, third, fourth}
  let partialLabel : V → Fin 6 := fun vertex =>
    if vertex = first then 0
    else if vertex = second then 1
    else if vertex = third then 2
    else 3
  have hmaps : Finset.image partialLabel side ⊆
      (Finset.univ : Finset (Fin 6)) := by
    intro value _
    simp
  have hsecondFirst : second ≠ first := hfirstSecond.symm
  have hthirdFirst : third ≠ first := hfirstThird.symm
  have hfourthFirst : fourth ≠ first := hfirstFourth.symm
  have hthirdSecond : third ≠ second := hsecondThird.symm
  have hfourthSecond : fourth ≠ second := hsecondFourth.symm
  have hfourthThird : fourth ≠ third := hthirdFourth.symm
  have hinjective : Set.InjOn partialLabel side := by
    intro left hleft right hright heq
    simp only [side, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hleft hright
    rcases hleft with rfl | rfl | rfl | rfl <;>
      rcases hright with rfl | rfl | rfl | rfl <;>
      simp_all [partialLabel]
  have htargetCard : Fintype.card V =
      (Finset.univ : Finset (Fin 6)).card := by
    simpa using hcard
  obtain ⟨labelToUniv, hlabel⟩ :=
    Finset.exists_equiv_extend_of_card_eq htargetCard hmaps hinjective
  let univEquiv : (Finset.univ : Finset (Fin 6)) ≃ Fin 6 :=
    { toFun := Subtype.val
      invFun := fun value => ⟨value, Finset.mem_univ value⟩
      left_inv := fun value => Subtype.ext rfl
      right_inv := fun _ => rfl }
  let label : V ≃ Fin 6 := labelToUniv.trans univEquiv
  refine ⟨label, ?_, ?_, ?_, ?_⟩
  · simpa [label, univEquiv, partialLabel] using
      hlabel first (by simp [side])
  · simpa [label, univEquiv, partialLabel,
      hfirstSecond.symm] using hlabel second (by simp [side])
  · simpa [label, univEquiv, partialLabel,
      hfirstThird.symm, hsecondThird.symm] using
        hlabel third (by simp [side])
  · simpa [label, univEquiv, partialLabel,
      hfirstFourth.symm, hsecondFourth.symm, hthirdFourth.symm] using
        hlabel fourth (by simp [side])

/-- A cubic six-vertex graph containing a chordless four-cycle is Tait
colorable, on an arbitrary finite vertex carrier. -/
theorem exists_taitEdgeColoring_of_card_eq_six_and_four_cycle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hregular : G.IsRegularOfDegree 3)
    {first second third fourth : V}
    (hfirstSecond : G.Adj first second)
    (hsecondThird : G.Adj second third)
    (hthirdFourth : G.Adj third fourth)
    (hfourthFirst : G.Adj fourth first)
    (hfirstThirdNe : first ≠ third)
    (hsecondFourthNe : second ≠ fourth)
    (hfirstThird : ¬ G.Adj first third)
    (hsecondFourth : ¬ G.Adj second fourth)
    (hcard : Fintype.card V = 6) :
    ∃ coloring : G.EdgeColoring Color,
      IsTaitEdgeColoring G coloring := by
  classical
  have hfirstSecondNe : first ≠ second := hfirstSecond.ne
  have hfirstFourthNe : first ≠ fourth := hfourthFirst.ne.symm
  have hsecondThirdNe : second ≠ third := hsecondThird.ne
  have hthirdFourthNe : third ≠ fourth := hthirdFourth.ne
  obtain ⟨label, hlabelFirst, hlabelSecond, hlabelThird, hlabelFourth⟩ :=
    exists_finSix_label_mapping_four hcard
      hfirstSecondNe hfirstThirdNe hfirstFourthNe
      hsecondThirdNe hsecondFourthNe hthirdFourthNe
  let H : SimpleGraph (Fin 6) := G.map label.toEmbedding
  let iso : G ≃g H := SimpleGraph.Iso.map label G
  letI : DecidableRel H.Adj := Classical.decRel _
  have hregularH : H.IsRegularOfDegree 3 := by
    intro vertex
    obtain ⟨source, rfl⟩ := label.surjective vertex
    have hdegree := iso.degree_eq source
    change H.degree (label source) = G.degree source at hdegree
    rw [hdegree]
    exact hregular.degree_eq source
  have h01 : H.Adj 0 1 := by
    have hadj := iso.map_adj_iff.mpr hfirstSecond
    change H.Adj (label first) (label second) at hadj
    simpa [hlabelFirst, hlabelSecond] using hadj
  have h12 : H.Adj 1 2 := by
    have hadj := iso.map_adj_iff.mpr hsecondThird
    change H.Adj (label second) (label third) at hadj
    simpa [hlabelSecond, hlabelThird] using hadj
  have h23 : H.Adj 2 3 := by
    have hadj := iso.map_adj_iff.mpr hthirdFourth
    change H.Adj (label third) (label fourth) at hadj
    simpa [hlabelThird, hlabelFourth] using hadj
  have h30 : H.Adj 3 0 := by
    have hadj := iso.map_adj_iff.mpr hfourthFirst
    change H.Adj (label fourth) (label first) at hadj
    simpa [hlabelFourth, hlabelFirst] using hadj
  have h02 : ¬ H.Adj 0 2 := by
    have hnonadj := (not_congr iso.map_adj_iff).mpr hfirstThird
    change ¬ H.Adj (label first) (label third) at hnonadj
    simpa [hlabelFirst, hlabelThird] using hnonadj
  have h13 : ¬ H.Adj 1 3 := by
    have hnonadj := (not_congr iso.map_adj_iff).mpr hsecondFourth
    change ¬ H.Adj (label second) (label fourth) at hnonadj
    simpa [hlabelSecond, hlabelFourth] using hnonadj
  obtain ⟨coloring, hcoloring⟩ :=
    finSix_fourCycle_tait_colorable_of_cubic H hregularH
      h01 h12 h23 h30 h02 h13
  let pulled : G.EdgeColoring Color :=
    coloring.comp iso.lineGraph.toHom
  refine ⟨pulled, ?_⟩
  intro edge
  change coloring (iso.lineGraph edge) ≠ 0
  exact hcoloring (iso.lineGraph edge)

end GoertzelV24SixVertexFourCycle

end Mettapedia.GraphTheory.FourColor
