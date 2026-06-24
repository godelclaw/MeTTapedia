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

end Mettapedia.GraphTheory.FourColor
