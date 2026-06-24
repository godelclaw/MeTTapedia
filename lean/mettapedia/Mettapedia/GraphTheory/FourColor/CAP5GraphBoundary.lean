import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord
import Mettapedia.GraphTheory.FourColor.BoundaryChains
import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48

open scoped BigOperators

open SimpleGraph

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*}

/-!
Graph-facing CAP5 boundary bridges.

This file connects the local CAP5 boundary-word layer to the manuscript's Tait edge-coloring
interface, without adding graph geometry assumptions.
-/

/-- Restricting a Tait edge-coloring to five CAP5 boundary edges gives a nonzero CAP5 boundary
word. -/
theorem cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring
    {G : SimpleGraph V} (boundaryEdge : Fin 5 → G.edgeSet)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordOfEdges_isNonzero_of_forall_nonzero boundaryEdge C
    (fun i => hC (boundaryEdge i))

/-- If the five CAP5 boundary edges enumerate a zero-boundary incidence set, the restricted
CAP5 boundary word has zero total color sum.  This is the graph-side cut equation in the
boundary-word language. -/
theorem cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at
    {U E : Type*} {D : ZeroBoundaryData U E} {v : U}
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C) :
    (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0 := by
  have hv := hzero v
  rw [hincident] at hv
  simpa [cap5BoundaryWordOfEdges] using hv

/-- Membership in the full zero-boundary set gives the CAP5 cut equation whenever the five
boundary edges enumerate a vertex-incidence set. -/
theorem cap5BoundaryWordOfEdges_sum_eq_zero_of_mem_zeroBoundarySet_at
    {U E : Type*} {D : ZeroBoundaryData U E} {v : U}
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : C ∈ D.zeroBoundarySet) :
    (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0 :=
  cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at boundaryEdge C hinj
    hincident hzero.1

/-- If a CAP5 boundary edge is one of the distinguished zero-boundary edges, its boundary-word
color is forced to zero by membership in the full zero-boundary set. -/
theorem cap5BoundaryWordOfEdges_eq_zero_of_mem_zeroBoundarySet_boundaryEdge
    {U E : Type*} {D : ZeroBoundaryData U E}
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hzero : C ∈ D.zeroBoundarySet) {i : Fin 5}
    (hi : boundaryEdge i ∈ D.boundaryEdges) :
    cap5BoundaryWordOfEdges boundaryEdge C i = 0 :=
  hzero.2 (boundaryEdge i) hi

/-- A Tait-colored CAP5 boundary cannot put all five boundary edges into the distinguished
zero-boundary edge set. -/
theorem not_forall_boundaryEdge_mem_boundaryEdges_of_isTaitEdgeColoring_of_mem_zeroBoundarySet
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C) (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    ¬ ∀ i : Fin 5, boundaryEdge i ∈ D.boundaryEdges := by
  intro hboundary
  have hzero0 :
      cap5BoundaryWordOfEdges boundaryEdge C 0 = 0 :=
    cap5BoundaryWordOfEdges_eq_zero_of_mem_zeroBoundarySet_boundaryEdge boundaryEdge
      (C : G.edgeSet → Color) hzero (hboundary 0)
  have hnonzero : cap5BoundaryWordOfEdges boundaryEdge C 0 ≠ 0 :=
    cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC 0
  exact hnonzero hzero0

end Mettapedia.GraphTheory.FourColor
