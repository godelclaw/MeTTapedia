import Mettapedia.GraphTheory.EdgeColoring

namespace SimpleGraph

variable {V W α : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Pull a proper edge coloring back along a graph embedding. -/
def EdgeColoring.pullbackEmbedding
    (C : G.EdgeColoring α) (embedding : H ↪g G) :
    H.EdgeColoring α :=
  C.comp embedding.toCopy.toLineGraphEmbedding.toHom

@[simp]
theorem EdgeColoring.pullbackEmbedding_apply
    (C : G.EdgeColoring α) (embedding : H ↪g G)
    (edge : H.edgeSet) :
    C.pullbackEmbedding embedding edge = C (embedding.mapEdgeSet edge) :=
  rfl

end SimpleGraph
