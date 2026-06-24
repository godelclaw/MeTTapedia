import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord
import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48

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

end Mettapedia.GraphTheory.FourColor
