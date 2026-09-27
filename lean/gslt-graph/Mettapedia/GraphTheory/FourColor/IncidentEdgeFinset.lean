import Mettapedia.GraphTheory.EdgeColoring

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The finite set of graph edges incident to a vertex, viewed in the
current `edgeSet` type.  This lightweight definition is shared by the
Goertzel framed-trail route and the older boundary-chain algebra. -/
def incidentEdgeFinset (G : SimpleGraph V) [Fintype G.edgeSet] (v : V) :
    Finset G.edgeSet :=
  Finset.univ.filter fun e => v ∈ (e : Sym2 V)

end Mettapedia.GraphTheory.FourColor
