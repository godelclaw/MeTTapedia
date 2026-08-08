import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedEdgeTrail
import Mettapedia.GraphTheory.FourColor.VertexKirchhoff

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

/-- The total color exposed at the frozen outward interface.  At a
well-formed degree-one stub, its summand is the color of the unique frozen
interface edge incident there. -/
def frozenInterfaceColorSum
    (data : FramedTrailData G) (C : G.EdgeColoring Color) : Color :=
  ∑ vertex ∈ data.frozenInterfaceStubVertices,
    vertexKirchhoffSum G C vertex

/-- Exact framed-boundary parity: the two defect requests together with the
frozen-interface color sum vanish.  Thus the outward interface, absent from
the old two-defect model, carries precisely the possible completion defect. -/
theorem defectSum_add_frozenInterfaceColorSum_eq_zero
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    data.missingColorAt C 0 + data.missingColorAt C 1 +
        frozenInterfaceColorSum data C = 0 := by
  let defects : Finset V :=
    {data.defectVertex 0, data.defectVertex 1}
  have hdefectsNe : data.defectVertex 0 ≠ data.defectVertex 1 := by
    intro heq
    have : (0 : Fin 2) = 1 := hdata.defectVertex_injective heq
    omega
  have hdisjoint :
      Disjoint defects data.frozenInterfaceStubVertices := by
    rw [Finset.disjoint_left]
    intro vertex hvertex hstub
    have hcases :
        vertex = data.defectVertex 0 ∨
          vertex = data.defectVertex 1 := by
      simpa [defects] using hvertex
    rcases hcases with hzero | hone
    · exact hdata.defectVertex_not_stub 0 (hzero ▸ hstub)
    · exact hdata.defectVertex_not_stub 1 (hone ▸ hstub)
  have hinterior : ∀ vertex ∉
      defects ∪ data.frozenInterfaceStubVertices,
      vertexKirchhoffSum G C vertex = 0 := by
    intro vertex hnotBoundary
    apply vertexKirchhoffSum_eq_zero_of_card_three C hC
    apply hdata.cubic_elsewhere vertex
    · intro i
      fin_cases i
      · intro hzero
        apply hnotBoundary
        simp [defects, hzero]
      · intro hone
        apply hnotBoundary
        simp [defects, hone]
    · intro hstub
      apply hnotBoundary
      exact Finset.mem_union_right defects hstub
  have hboundary :=
    sum_vertexKirchhoffSum_on_boundary_eq_zero C
      (defects ∪ data.frozenInterfaceStubVertices) hinterior
  rw [Finset.sum_union hdisjoint] at hboundary
  simpa [defects, FramedTrailData.missingColorAt,
    frozenInterfaceColorSum, vertexKirchhoffSum,
    hdefectsNe] using hboundary

/-- If the frozen interface has zero total color, the two defect requests
match. -/
theorem hasMatchingDefectColors_of_frozenInterfaceColorSum_eq_zero
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hfrozen : frozenInterfaceColorSum data C = 0) :
    data.HasMatchingDefectColors C := by
  have hsum :=
    defectSum_add_frozenInterfaceColorSum_eq_zero data hdata C hC
  rw [hfrozen, add_zero] at hsum
  exact (add_eq_zero_iff_eq _ _).1 hsum

/-- Two-defect parity for an empty frozen boundary.  This specialization
applies to a bare one-edge deletion, not to the genuine framed trail with
outward interface stubs. -/
theorem FramedTrailData.hasMatchingDefectColors_of_wellFormed
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (hnoFrozenBoundary : data.frozenInterfaceStubVertices = ∅)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    data.HasMatchingDefectColors C := by
  apply hasMatchingDefectColors_of_frozenInterfaceColorSum_eq_zero
    data hdata C hC
  simp [frozenInterfaceColorSum, hnoFrozenBoundary]

/-- With an empty frozen boundary, framed completion is immediate: the
starting coloring already extends. -/
theorem FramedTrailData.framedTangleCompletable_of_wellFormed
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (hnoFrozenBoundary : data.frozenInterfaceStubVertices = ∅)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    FramedTangleCompletable data C := by
  exact ⟨C, Relation.ReflTransGen.refl,
    FramedTrailData.hasMatchingDefectColors_of_wellFormed
      data hdata hnoFrozenBoundary C hC⟩

/-- The same parity observation in the internal movable-support completion
language. -/
theorem FramedTrailData.movableSupportCompletable_of_wellFormed
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (hnoFrozenBoundary : data.frozenInterfaceStubVertices = ∅)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    MovableSupportCompletable data C := by
  rw [movableSupportCompletable_iff_framedTangleCompletable]
  exact FramedTrailData.framedTangleCompletable_of_wellFormed
    data hdata hnoFrozenBoundary C hC

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
      (unrestrictedDeletedEdgeFrame_wellFormed huv hcubic) rfl C hC

/-- Consequently, a non-Tait-colorable finite cubic graph has no
Tait-colorable one-edge deletion. -/
theorem deletedEdge_not_taitColorable_of_not_taitColorable {u v : V}
    (huv : G.Adj u v)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring) :
    ¬ ∃ C : (DeletedEdgeGraph G u v).EdgeColoring Color,
        IsTaitEdgeColoring (DeletedEdgeGraph G u v) C := by
  rintro ⟨C, hC⟩
  exact hnotColorable
    (exists_taitColoring_of_deletedEdgeColoring huv hcubic C hC)

end

end GoertzelV24TwoDefectParity

end Mettapedia.GraphTheory.FourColor
