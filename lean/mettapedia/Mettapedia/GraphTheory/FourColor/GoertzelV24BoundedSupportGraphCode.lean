import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

/-!
# Finite codes for graphs with bounded support

A local transfer morphism may be presented on a large ambient carrier even
when only finitely many vertices participate in an edge.  This module removes
that irrelevant ambient carrier: a graph whose support has cardinality at
most `bound` is transported to a graph on `Fin vertexCount`, where
`vertexCount ≤ bound`.

The construction retains an explicit graph isomorphism from the induced
support graph.  It therefore preserves adjacency and reachability on the
participating vertices.  No source-corridor geometry or profile quotient is
asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BoundedSupportGraphCode

universe u

noncomputable section

noncomputable local instance supportFintype
    {Vertex : Type u} [Fintype Vertex]
    (graph : SimpleGraph Vertex) : Fintype graph.support :=
  Fintype.ofFinite graph.support

/-- A graph on at most `bound` vertices, with its actual carrier size kept in
the code. -/
structure BoundedSupportGraphCode (bound : Nat) where
  vertexCount : Fin (bound + 1)
  graph : SimpleGraph (Fin vertexCount.val)

instance (bound : Nat) : DecidableEq (BoundedSupportGraphCode bound) :=
  Classical.decEq _

private def boundedSupportGraphCodeEquiv (bound : Nat) :
    BoundedSupportGraphCode bound ≃
      Σ vertexCount : Fin (bound + 1), SimpleGraph (Fin vertexCount.val) where
  toFun code := ⟨code.vertexCount, code.graph⟩
  invFun code := ⟨code.1, code.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (bound : Nat) :
    Fintype (BoundedSupportGraphCode bound) :=
  Fintype.ofEquiv _ (boundedSupportGraphCodeEquiv bound).symm

/-- Canonical finite coordinate on the non-isolated vertices of a finite
ambient graph. -/
noncomputable def supportCoordinate
    {Vertex : Type u} [Fintype Vertex]
    (graph : SimpleGraph Vertex) :
    graph.support ≃ Fin (Fintype.card graph.support) :=
  Fintype.equivFin graph.support

/-- Transport the induced support graph to its canonical finite coordinate.
The proof argument records the uniform bound but does not enter the graph
data. -/
noncomputable def boundedSupportCode
    {Vertex : Type u} [Fintype Vertex]
    (graph : SimpleGraph Vertex) (bound : Nat)
    (hsupport : graph.support.ncard ≤ bound) :
    BoundedSupportGraphCode bound where
  vertexCount :=
    ⟨Fintype.card graph.support, by
      rw [Set.fintypeCard_eq_ncard]
      exact Nat.lt_succ_of_le hsupport⟩
  graph :=
    (graph.induce graph.support).map (supportCoordinate graph).toEmbedding

/-- The carrier size stored in the code is exactly the number of participating
ambient vertices. -/
theorem boundedSupportCode_vertexCount_eq_ncard
    {Vertex : Type u} [Fintype Vertex]
    (graph : SimpleGraph Vertex) (bound : Nat)
    (hsupport : graph.support.ncard ≤ bound) :
    (boundedSupportCode graph bound hsupport).vertexCount.val =
      graph.support.ncard := by
  simp [boundedSupportCode, Set.fintypeCard_eq_ncard]

/-- The coded carrier satisfies the requested uniform bound. -/
theorem boundedSupportCode_vertexCount_le
    {Vertex : Type u} [Fintype Vertex]
    (graph : SimpleGraph Vertex) (bound : Nat)
    (hsupport : graph.support.ncard ≤ bound) :
    (boundedSupportCode graph bound hsupport).vertexCount.val ≤ bound := by
  rw [boundedSupportCode_vertexCount_eq_ncard]
  exact hsupport

/-- The original support-induced graph is isomorphic to its bounded finite
code. -/
noncomputable def boundedSupportCodeIso
    {Vertex : Type u} [Fintype Vertex]
    (graph : SimpleGraph Vertex) (bound : Nat)
    (hsupport : graph.support.ncard ≤ bound) :
    graph.induce graph.support ≃g
      (boundedSupportCode graph bound hsupport).graph := by
  simpa [boundedSupportCode] using
    (SimpleGraph.Iso.map (supportCoordinate graph)
      (graph.induce graph.support))

/-- Adjacency of participating ambient vertices is exactly adjacency in the
finite code. -/
theorem boundedSupportCode_adj_iff
    {Vertex : Type u} [Fintype Vertex]
    (graph : SimpleGraph Vertex) (bound : Nat)
    (hsupport : graph.support.ncard ≤ bound)
    (first second : graph.support) :
    (boundedSupportCode graph bound hsupport).graph.Adj
        (supportCoordinate graph first) (supportCoordinate graph second) ↔
      graph.Adj first.1 second.1 := by
  change
    ((graph.induce graph.support).map
      (supportCoordinate graph).toEmbedding).Adj
        ((supportCoordinate graph).toEmbedding first)
        ((supportCoordinate graph).toEmbedding second) ↔ _
  rw [SimpleGraph.map_adj_apply]
  rfl

/-- Reachability inside the participating carrier is exactly reachability in
the finite code. -/
theorem boundedSupportCode_reachable_iff
    {Vertex : Type u} [Fintype Vertex]
    (graph : SimpleGraph Vertex) (bound : Nat)
    (hsupport : graph.support.ncard ≤ bound)
    (first second : graph.support) :
    (boundedSupportCode graph bound hsupport).graph.Reachable
        (supportCoordinate graph first) (supportCoordinate graph second) ↔
      (graph.induce graph.support).Reachable first second := by
  exact SimpleGraph.Iso.reachable_iff
    (φ := boundedSupportCodeIso graph bound hsupport)

end

end GoertzelV24BoundedSupportGraphCode

end Mettapedia.GraphTheory.FourColor
