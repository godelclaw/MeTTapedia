import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionRotationSplice

/-!
# Manuscript-side deleted-region slit graph

The current Fable manuscript opens a pentagon cap by deleting its cap vertices
and retaining every crossing spoke as a fresh degree-one stub.  This file gives
that operation directly as a simple graph: old vertices are exactly the
vertices outside the deleted region, and a boundary port is a directed ambient
edge from one such old vertex into the deleted region.

`GoertzelV24PentagonCapOpening` formalizes the supplied toolchain's other
presentation, which retains the cap vertices and deletes the cap-cycle edges.
Neither presentation is discarded and this file makes no claim that they are
definitionally equal.  The next comparison must give an isomorphism preserving
the *ordered* five boundary ports; a bare graph isomorphism is insufficient for
the source's boundary-word semantics.

This is intentionally the simple-graph counterpart of the existing generic
open-region rotation construction, not a second open-region theorem tower.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DeletedRegionSlitGraph

open SimpleGraph
open GoertzelV24DeletedRegionRotationSplice

variable {V : Type*} [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- A directed ambient boundary edge, oriented from a retained vertex toward a
deleted one.  Each such edge becomes one fresh degree-one stub. -/
structure DeletedRegionBoundaryPort (G : SimpleGraph V) (deleted : Finset V) where
  dart : G.Dart
  retained : dart.fst ∉ deleted
  removed : dart.snd ∈ deleted

namespace DeletedRegionBoundaryPort

/-- The retained endpoint to which this fresh stub is attached. -/
def retainedVertex {deleted : Finset V}
    (port : DeletedRegionBoundaryPort G deleted) : {v // v ∉ deleted} :=
  ⟨port.dart.fst, port.retained⟩

end DeletedRegionBoundaryPort

/-- The literal vertex carrier after deleting a region: retained ambient
vertices plus one new vertex for every exposed boundary port. -/
abbrev DeletedRegionSlitVertex (G : SimpleGraph V) (deleted : Finset V) :=
  {v // v ∉ deleted} ⊕ DeletedRegionBoundaryPort G deleted

namespace DeletedRegionSlitVertex

/-- Embed an old retained vertex. -/
def old {deleted : Finset V} (vertex : {v // v ∉ deleted}) :
    DeletedRegionSlitVertex G deleted :=
  Sum.inl vertex

/-- Embed a newly created boundary stub. -/
def stub {deleted : Finset V} (port : DeletedRegionBoundaryPort G deleted) :
    DeletedRegionSlitVertex G deleted :=
  Sum.inr port

end DeletedRegionSlitVertex

/-- The manuscript-side open tangle as a literal graph.  Old retained vertices
keep all their ambient edges; each exposed edge instead ends at its own fresh
degree-one boundary stub. -/
def deletedRegionSlitGraph (deleted : Finset V) :
    SimpleGraph (DeletedRegionSlitVertex G deleted) where
  Adj first second :=
    match first, second with
    | Sum.inl oldFirst, Sum.inl oldSecond => G.Adj oldFirst.1 oldSecond.1
    | Sum.inl oldVertex, Sum.inr port => oldVertex.1 = port.dart.fst
    | Sum.inr port, Sum.inl oldVertex => port.dart.fst = oldVertex.1
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro first second hadj
    rcases first with oldFirst | portFirst <;>
      rcases second with oldSecond | portSecond
    · exact G.adj_symm hadj
    · exact hadj.symm
    · exact hadj.symm
    · exact hadj⟩
  loopless := ⟨by
    intro vertex hloop
    rcases vertex with oldVertex | port
    · exact G.loopless.1 oldVertex.1 hloop
    · exact hloop⟩

namespace DeletedRegionBoundaryPort

theorem stub_adj_retainedVertex {deleted : Finset V}
    (port : DeletedRegionBoundaryPort G deleted) :
    (deletedRegionSlitGraph deleted).Adj
      (DeletedRegionSlitVertex.stub port)
      (DeletedRegionSlitVertex.old port.retainedVertex) :=
  rfl

theorem stub_adj_iff {deleted : Finset V}
    (port : DeletedRegionBoundaryPort G deleted) (vertex : {v // v ∉ deleted}) :
    (deletedRegionSlitGraph deleted).Adj
      (DeletedRegionSlitVertex.stub port) (DeletedRegionSlitVertex.old vertex) ↔
      vertex.1 = port.dart.fst :=
  eq_comm

theorem stub_not_adj_stub {deleted : Finset V}
    (first second : DeletedRegionBoundaryPort G deleted) :
    ¬ (deletedRegionSlitGraph deleted).Adj
      (DeletedRegionSlitVertex.stub first) (DeletedRegionSlitVertex.stub second) :=
  id

/-- A fresh manuscript-side stub has exactly one neighbour. -/
theorem stub_unique_adj {deleted : Finset V}
    (port : DeletedRegionBoundaryPort G deleted)
    (vertex : DeletedRegionSlitVertex G deleted)
    (hadj : (deletedRegionSlitGraph deleted).Adj
      (DeletedRegionSlitVertex.stub port) vertex) :
    vertex = DeletedRegionSlitVertex.old port.retainedVertex := by
  rcases vertex with oldVertex | otherPort
  · have hvertex : oldVertex = port.retainedVertex :=
      Subtype.ext hadj.symm
    exact congrArg
      (fun vertex : {v // v ∉ deleted} =>
        (Sum.inl vertex : DeletedRegionSlitVertex G deleted)) hvertex
  · exact False.elim hadj

end DeletedRegionBoundaryPort

end

end GoertzelV24DeletedRegionSlitGraph

end Mettapedia.GraphTheory.FourColor
