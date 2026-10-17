import Mettapedia.GraphTheory.EdgeColoring

/-!
# Two-coloured components, and completing an edge colouring across an empty edge

For a colouring `C` and colours `a, b`, two vertices lie in one *Kempe component* when they
are joined inside the subgraph induced by the vertices coloured `a` or `b`
(`Coloring.SameKempeComponent`).  For an edge colouring, a colouring of the line graph,
the Kempe components are the two-coloured paths and cycles of edges.

Delete an edge `uv` of a cubic graph and suppress `u` and `v`; the two edges through the
suppressed vertices are the remaining ends of the deleted edge.  Following L. H. Kauffman
(*Reformulating the map color theorem*, §4), a colouring of the smaller graph is
*completable across* those two edges when one two-coloured component contains both of
them (`EdgeColoring.CompletableAcross`): that two-coloured pathway is what lets the
deleted edge be restored and coloured after one switch.  It is *completable by simple
operations* when some colouring reachable from it by Kempe switches is completable
(`EdgeColoring.KempeCompletableAcross`).  The restoration step itself is not formalized
here; these are the definitions of the two notions.
-/

namespace SimpleGraph

variable {V α : Type*} {G : SimpleGraph V}

namespace Coloring

/-- `x` and `y` lie in one connected component of the subgraph induced by the colours `a`
and `b`. -/
def SameKempeComponent (C : G.Coloring α) (a b : α) (x y : V) : Prop :=
  ∃ (hx : x ∈ C.bicoloredSet a b) (hy : y ∈ C.bicoloredSet a b),
    (C.bicoloredSubgraph a b).Reachable ⟨x, hx⟩ ⟨y, hy⟩

/-- Lying in the Kempe component of `x` is lying in its connected component of the
two-coloured subgraph. -/
theorem sameKempeComponent_iff_mem_kempeComponentSet (C : G.Coloring α) (a b : α) {x y : V}
    (hx : x ∈ C.bicoloredSet a b) :
    C.SameKempeComponent a b x y ↔
      y ∈ C.kempeComponentSet a b ((C.bicoloredSubgraph a b).connectedComponentMk ⟨x, hx⟩) := by
  constructor
  · rintro ⟨hx', hy, hreach⟩
    exact ⟨hy, ConnectedComponent.eq.mpr hreach.symm⟩
  · rintro ⟨hy, hK⟩
    exact ⟨hx, hy, (ConnectedComponent.eq.mp hK).symm⟩

end Coloring

namespace EdgeColoring

variable [DecidableEq α]

/-- An edge colouring is completable across the edges `e` and `f` when one two-coloured
component contains both. -/
def CompletableAcross (C : G.EdgeColoring α) (e f : G.edgeSet) : Prop :=
  ∃ a b, Coloring.SameKempeComponent C a b e f

/-- Some edge colouring reachable by Kempe switches is completable across `e` and `f`. -/
def KempeCompletableAcross (C : G.EdgeColoring α) (e f : G.edgeSet) : Prop :=
  ∃ C' ∈ G.EdgeKempeClosure C, CompletableAcross C' e f

end EdgeColoring

end SimpleGraph
