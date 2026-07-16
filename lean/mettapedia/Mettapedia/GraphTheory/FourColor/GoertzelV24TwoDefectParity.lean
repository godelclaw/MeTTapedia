import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedEdgeTrail

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoDefectParity

open SimpleGraph
open scoped BigOperators
open GoertzelV24DeletedEdgeTrail
open GoertzelV24FramedTrail

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- In a finite simple graph, the sum over all vertex-incidence color sums is
zero over `F₂ × F₂`: every unoriented edge occurs at its two endpoints. -/
theorem sum_vertexKirchhoffSum_eq_zero (color : G.edgeSet → Color) :
    (∑ vertex : V, vertexKirchhoffSum G color vertex) = 0 := by
  classical
  calc
    (∑ vertex : V, vertexKirchhoffSum G color vertex) =
        ∑ vertex : V, ∑ edge : G.edgeSet,
          if vertex ∈ (edge.1 : Sym2 V) then color edge else 0 := by
      apply Finset.sum_congr rfl
      intro vertex _
      unfold vertexKirchhoffSum incidentEdgeFinset
      rw [← Finset.sum_filter]
    _ = ∑ edge : G.edgeSet, ∑ vertex : V,
          if vertex ∈ (edge.1 : Sym2 V) then color edge else 0 := by
      rw [Finset.sum_comm]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro edge _
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.univ.filter fun vertex : V => vertex ∈ (edge.1 : Sym2 V)) =
            edge.1.toFinset := by
        ext vertex
        simp [Sym2.mem_toFinset]
      rw [hfilter, Finset.sum_const]
      have hnondiag : ¬edge.1.IsDiag :=
        G.not_isDiag_of_mem_edgeSet edge.2
      rw [Sym2.card_toFinset_of_not_isDiag edge.1 hnondiag]
      simp [two_mul]

/-- If every vertex outside a selected boundary has zero Kirchhoff sum,
then the total Kirchhoff sum on that boundary is zero. -/
theorem sum_vertexKirchhoffSum_on_boundary_eq_zero
    (color : G.edgeSet → Color) (boundary : Finset V)
    (hinterior : ∀ vertex ∉ boundary,
      vertexKirchhoffSum G color vertex = 0) :
    ∑ vertex ∈ boundary, vertexKirchhoffSum G color vertex = 0 := by
  calc
    ∑ vertex ∈ boundary, vertexKirchhoffSum G color vertex =
        ∑ vertex : V, vertexKirchhoffSum G color vertex := by
      apply Finset.sum_subset (by simp)
      intro vertex _huniv hvertex
      exact hinterior vertex hvertex
    _ = 0 := sum_vertexKirchhoffSum_eq_zero color

private theorem three_distinct_nonzero_sum_eq_zero
    {first second third : Color}
    (hfirst : first ≠ 0) (hsecond : second ≠ 0) (hthird : third ≠ 0)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    first + second + third = 0 := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero first hfirst with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero second hsecond with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero third hthird with
      rfl | rfl | rfl <;>
    simp at hfirstSecond hfirstThird hsecondThird ⊢

/-- At a vertex with exactly three incident edges, a proper nonzero
three-edge coloring has zero `F₂ × F₂` incidence sum. -/
theorem vertexKirchhoffSum_eq_zero_of_card_three
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (vertex : V) (hcard : (incidentEdgeFinset G vertex).card = 3) :
    vertexKirchhoffSum G C vertex = 0 := by
  rcases Finset.card_eq_three.mp hcard with
    ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hset⟩
  have hfirstVertex : vertex ∈ (first.1 : Sym2 V) := by
    have : first ∈ incidentEdgeFinset G vertex := by
      rw [hset]
      simp
    simpa [incidentEdgeFinset] using this
  have hsecondVertex : vertex ∈ (second.1 : Sym2 V) := by
    have : second ∈ incidentEdgeFinset G vertex := by
      rw [hset]
      simp
    simpa [incidentEdgeFinset] using this
  have hthirdVertex : vertex ∈ (third.1 : Sym2 V) := by
    have : third ∈ incidentEdgeFinset G vertex := by
      rw [hset]
      simp
    simpa [incidentEdgeFinset] using this
  have hcolorFirstSecond : C first ≠ C second :=
    C.valid ((SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hfirstSecond, vertex, hfirstVertex, hsecondVertex⟩)
  have hcolorFirstThird : C first ≠ C third :=
    C.valid ((SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hfirstThird, vertex, hfirstVertex, hthirdVertex⟩)
  have hcolorSecondThird : C second ≠ C third :=
    C.valid ((SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hsecondThird, vertex, hsecondVertex, hthirdVertex⟩)
  unfold vertexKirchhoffSum
  rw [hset]
  simpa [hfirstSecond, hfirstThird, hsecondThird, add_assoc] using
    three_distinct_nonzero_sum_eq_zero
      (hC first) (hC second) (hC third)
      hcolorFirstSecond hcolorFirstThird hcolorSecondThird

/-- Two-defect parity. In a finite graph with exactly two degree-two defects
and cubicity elsewhere, every proper nonzero three-edge coloring requests the
same missing color at both defects. -/
theorem FramedTrailData.hasMatchingDefectColors_of_wellFormed
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    data.HasMatchingDefectColors C := by
  let localSum : V → Color := fun vertex => vertexKirchhoffSum G C vertex
  have hother : ∀ vertex : V,
      vertex ≠ data.defectVertex 0 →
      vertex ≠ data.defectVertex 1 → localSum vertex = 0 := by
    intro vertex hzero hone
    apply vertexKirchhoffSum_eq_zero_of_card_three C hC
    exact hdata.2.2.1 vertex (by
      intro i
      fin_cases i
      · exact hzero
      · exact hone)
  have hdefectsNe : data.defectVertex 0 ≠ data.defectVertex 1 := by
    intro heq
    have : (0 : Fin 2) = 1 := hdata.1 heq
    omega
  have hpairSubset :
      ({data.defectVertex 0, data.defectVertex 1} : Finset V) ⊆
        Finset.univ := by
    simp
  have hpairSum :
      (∑ vertex ∈ ({data.defectVertex 0, data.defectVertex 1} : Finset V),
          localSum vertex) =
        ∑ vertex : V, localSum vertex := by
    apply Finset.sum_subset hpairSubset
    intro vertex _huniv hnotPair
    apply hother vertex
    · simpa using fun heq => hnotPair (by simp [heq])
    · simpa using fun heq => hnotPair (by simp [heq])
  have htwoSum :
      localSum (data.defectVertex 0) +
          localSum (data.defectVertex 1) = 0 := by
    calc
      localSum (data.defectVertex 0) + localSum (data.defectVertex 1) =
          ∑ vertex ∈
            ({data.defectVertex 0, data.defectVertex 1} : Finset V),
              localSum vertex := by
        simp [hdefectsNe]
      _ = ∑ vertex : V, localSum vertex := hpairSum
      _ = 0 := sum_vertexKirchhoffSum_eq_zero C
  apply (add_eq_zero_iff_eq _ _).1
  simpa [FramedTrailData.HasMatchingDefectColors,
    FramedTrailData.missingColorAt, localSum, vertexKirchhoffSum] using htwoSum

/-- Under the current two-defect well-formedness predicate, framed Trail
Completability is immediate: the starting coloring already extends. -/
theorem FramedTrailData.framedTangleCompletable_of_wellFormed
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    FramedTangleCompletable data C := by
  exact ⟨C, Relation.ReflTransGen.refl,
    FramedTrailData.hasMatchingDefectColors_of_wellFormed data hdata C hC⟩

/-- The same parity observation in the Kauffman-facing completion language. -/
theorem FramedTrailData.kauffmanBetweenRegionCompletable_of_wellFormed
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    KauffmanBetweenRegionCompletable data C := by
  rw [L10_kauffmanBetweenRegionCompletable_iff_framedTangleCompletable]
  exact FramedTrailData.framedTangleCompletable_of_wellFormed data hdata C hC

/-- In particular, a Tait coloring of a one-edge deletion of a cubic graph
always extends back across that edge; no Kempe move is needed. -/
theorem exists_taitColoring_of_deletedEdgeColoring {u v : V}
    (huv : G.Adj u v)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (hC : IsTaitEdgeColoring (DeletedEdgeGraph G u v) C) :
    ∃ ambientColoring : G.EdgeColoring Color,
      IsTaitEdgeColoring G ambientColoring := by
  apply exists_taitColoring_of_unrestrictedDeletedEdgeCompletable
    huv hcubic C hC
  exact
    FramedTrailData.framedTangleCompletable_of_wellFormed
      (unrestrictedDeletedEdgeFrame G u v)
      (unrestrictedDeletedEdgeFrame_wellFormed huv hcubic) C hC

end

end GoertzelV24TwoDefectParity

end Mettapedia.GraphTheory.FourColor
