import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedEdgeStructure

/-!
# Annular boundary data for the v24 closed-web cell

Cell 3 of the source proof concerns a cubic annular tangle with an ordered
five-stub inner interface and a variable-size outer interface.  This is not
the Cell-4 framed trail: there are no missing-edge defect vertices here.

The structure below records only the two interfaces.  Its well-formedness
predicate says that their vertices have degree one and every other vertex is
cubic.  In particular it does not assume total closure, radial strands, path
components, a good word, or any planar-sector conclusion.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebBoundaryData

open SimpleGraph
open GoertzelV24ClosedWebLocalExactness
open GoertzelV24ClosedWebSelectedEdgeStructure

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Ordered inner and outer interfaces of a Cell-3 annular tangle.  The
embeddings make both the boundary stubs and their incident boundary edges
duplicate-free on each boundary. -/
structure AnnularBoundaryData (G : SimpleGraph V) (outerCount : Nat) where
  innerStub : Fin 5 ↪ V
  outerStub : Fin outerCount ↪ V
  innerBoundaryEdge : Fin 5 ↪ G.edgeSet
  outerBoundaryEdge : Fin outerCount ↪ G.edgeSet

namespace AnnularBoundaryData

variable {outerCount : Nat}

/-- The finite set of inner stub vertices. -/
def innerStubVertices (data : AnnularBoundaryData G outerCount) : Finset V :=
  Finset.univ.map data.innerStub

/-- The finite set of outer stub vertices. -/
def outerStubVertices (data : AnnularBoundaryData G outerCount) : Finset V :=
  Finset.univ.map data.outerStub

/-- Both boundary interfaces, as a set of degree-one vertices. -/
def boundaryStubVertices (data : AnnularBoundaryData G outerCount) : Finset V :=
  data.innerStubVertices ∪ data.outerStubVertices

/-- Every vertex away from the two interfaces. -/
def interiorVertices (data : AnnularBoundaryData G outerCount) : Finset V :=
  Finset.univ \ data.boundaryStubVertices

/-- Graph-level validity of the two-boundary interface. -/
structure WellFormed (data : AnnularBoundaryData G outerCount) : Prop where
  inner_outer_stub_disjoint :
    ∀ inner outer, data.innerStub inner ≠ data.outerStub outer
  inner_outer_edge_disjoint :
    ∀ inner outer,
      data.innerBoundaryEdge inner ≠ data.outerBoundaryEdge outer
  innerBoundaryEdge_incident :
    ∀ inner,
      data.innerBoundaryEdge inner ∈
        incidentEdgeFinset G (data.innerStub inner)
  outerBoundaryEdge_incident :
    ∀ outer,
      data.outerBoundaryEdge outer ∈
        incidentEdgeFinset G (data.outerStub outer)
  inner_stub_degree_one :
    ∀ inner,
      (incidentEdgeFinset G (data.innerStub inner)).card = 1
  outer_stub_degree_one :
    ∀ outer,
      (incidentEdgeFinset G (data.outerStub outer)).card = 1
  cubic_elsewhere :
    ∀ vertex,
      (∀ inner, vertex ≠ data.innerStub inner) →
      (∀ outer, vertex ≠ data.outerStub outer) →
      (incidentEdgeFinset G vertex).card = 3

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem mem_innerStubVertices_iff
    (data : AnnularBoundaryData G outerCount) (vertex : V) :
    vertex ∈ data.innerStubVertices ↔
      ∃ inner : Fin 5, data.innerStub inner = vertex := by
  simp [innerStubVertices]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem mem_outerStubVertices_iff
    (data : AnnularBoundaryData G outerCount) (vertex : V) :
    vertex ∈ data.outerStubVertices ↔
      ∃ outer : Fin outerCount, data.outerStub outer = vertex := by
  simp [outerStubVertices]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem innerStubVertices_card
    (data : AnnularBoundaryData G outerCount) :
    data.innerStubVertices.card = 5 := by
  simp [innerStubVertices]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem outerStubVertices_card
    (data : AnnularBoundaryData G outerCount) :
    data.outerStubVertices.card = outerCount := by
  simp [outerStubVertices]

theorem innerStubVertices_disjoint_outerStubVertices
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed) :
    Disjoint data.innerStubVertices data.outerStubVertices := by
  rw [Finset.disjoint_left]
  intro vertex hinner houter
  rcases (mem_innerStubVertices_iff data vertex).1 hinner with
    ⟨inner, rfl⟩
  rcases (mem_outerStubVertices_iff data (data.innerStub inner)).1 houter with
    ⟨outer, houter⟩
  exact hdata.inner_outer_stub_disjoint inner outer houter.symm

@[simp] theorem boundaryStubVertices_card
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed) :
    data.boundaryStubVertices.card = 5 + outerCount := by
  rw [boundaryStubVertices,
    Finset.card_union_of_disjoint
      (innerStubVertices_disjoint_outerStubVertices data hdata)]
  simp

/-- The ordered color word read from the five actual inner boundary edges. -/
def innerBoundaryWord (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) : CAP5BoundaryWord :=
  cap5BoundaryWordOfEdges data.innerBoundaryEdge C

/-- The color word read from the variable-size outer interface. -/
def outerBoundaryWord (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) : Fin outerCount → Color :=
  fun outer => C (data.outerBoundaryEdge outer)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Tait nonzeroness passes directly to the source's CAP5 inner word. -/
theorem innerBoundaryWord_isNonzero
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    CAP5BoundaryWordIsNonzero (data.innerBoundaryWord C) := by
  exact cap5BoundaryWordOfEdges_isNonzero_of_forall_nonzero
    data.innerBoundaryEdge C (fun inner => hC (data.innerBoundaryEdge inner))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Tait nonzeroness also holds pointwise on the outer word. -/
theorem outerBoundaryWord_ne_zero
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (outer : Fin outerCount) :
    data.outerBoundaryWord C outer ≠ 0 := by
  exact hC (data.outerBoundaryEdge outer)

private theorem incidentEdgeFinset_eq_singleton_of_card_one_of_mem
    (vertex : V) (edge : G.edgeSet)
    (hcard : (incidentEdgeFinset G vertex).card = 1)
    (hmem : edge ∈ incidentEdgeFinset G vertex) :
    incidentEdgeFinset G vertex = {edge} := by
  rcases Finset.card_eq_one.mp hcard with ⟨unique, hunique⟩
  have hedge : edge = unique := by
    simpa [hunique] using hmem
  subst unique
  exact hunique

/-- The named inner boundary edge is the unique edge at its stub. -/
theorem innerStub_incidentEdgeFinset_eq_singleton
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (inner : Fin 5) :
    incidentEdgeFinset G (data.innerStub inner) =
      {data.innerBoundaryEdge inner} := by
  exact incidentEdgeFinset_eq_singleton_of_card_one_of_mem
    (data.innerStub inner) (data.innerBoundaryEdge inner)
    (hdata.inner_stub_degree_one inner)
    (hdata.innerBoundaryEdge_incident inner)

/-- The named outer boundary edge is the unique edge at its stub. -/
theorem outerStub_incidentEdgeFinset_eq_singleton
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (outer : Fin outerCount) :
    incidentEdgeFinset G (data.outerStub outer) =
      {data.outerBoundaryEdge outer} := by
  exact incidentEdgeFinset_eq_singleton_of_card_one_of_mem
    (data.outerStub outer) (data.outerBoundaryEdge outer)
    (hdata.outer_stub_degree_one outer)
    (hdata.outerBoundaryEdge_incident outer)

section SelectedPairDegrees

noncomputable local instance colorPairGraphNeighborSetFintype
    (C : G.EdgeColoring Color) (first second : Color) (vertex : V) :
    Fintype ((colorPairGraph C first second).neighborSet vertex) := by
  classical
  exact Subtype.fintype _

/-- A selected color pair has degree one at an inner stub exactly when the
stub's boundary-edge color belongs to that pair. -/
theorem colorPairGraph_degree_innerStub
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (first second : Color) (inner : Fin 5) :
    (colorPairGraph C first second).degree (data.innerStub inner) =
      if C (data.innerBoundaryEdge inner) = first ∨
          C (data.innerBoundaryEdge inner) = second then 1 else 0 := by
  rw [colorPairGraph_degree_eq_card_incidentEdges,
    incidentEdgesOfColorPair]
  rw [innerStub_incidentEdgeFinset_eq_singleton data hdata inner]
  by_cases hselected : C (data.innerBoundaryEdge inner) = first ∨
      C (data.innerBoundaryEdge inner) = second
  · rcases hselected with hfirst | hsecond
    · have hfilter :
          {edge ∈ ({data.innerBoundaryEdge inner} : Finset G.edgeSet) |
              C edge = first ∨ C edge = second} =
            {data.innerBoundaryEdge inner} := by
        apply Finset.filter_eq_self.2
        intro edge hedge
        have hedgeEq : edge = data.innerBoundaryEdge inner := by
          simpa using hedge
        subst edge
        exact Or.inl hfirst
      rw [hfilter]
      simp [hfirst]
    · have hfilter :
          {edge ∈ ({data.innerBoundaryEdge inner} : Finset G.edgeSet) |
              C edge = first ∨ C edge = second} =
            {data.innerBoundaryEdge inner} := by
        apply Finset.filter_eq_self.2
        intro edge hedge
        have hedgeEq : edge = data.innerBoundaryEdge inner := by
          simpa using hedge
        subst edge
        exact Or.inr hsecond
      rw [hfilter]
      simp [hsecond]
  · have hfirst : C (data.innerBoundaryEdge inner) ≠ first :=
      fun h => hselected (Or.inl h)
    have hsecond : C (data.innerBoundaryEdge inner) ≠ second :=
      fun h => hselected (Or.inr h)
    simp [hfirst, hsecond]

/-- The corresponding exact endpoint calculation on the outer boundary. -/
theorem colorPairGraph_degree_outerStub
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (first second : Color)
    (outer : Fin outerCount) :
    (colorPairGraph C first second).degree (data.outerStub outer) =
      if C (data.outerBoundaryEdge outer) = first ∨
          C (data.outerBoundaryEdge outer) = second then 1 else 0 := by
  rw [colorPairGraph_degree_eq_card_incidentEdges,
    incidentEdgesOfColorPair]
  rw [outerStub_incidentEdgeFinset_eq_singleton data hdata outer]
  by_cases hselected : C (data.outerBoundaryEdge outer) = first ∨
      C (data.outerBoundaryEdge outer) = second
  · rcases hselected with hfirst | hsecond
    · have hfilter :
          {edge ∈ ({data.outerBoundaryEdge outer} : Finset G.edgeSet) |
              C edge = first ∨ C edge = second} =
            {data.outerBoundaryEdge outer} := by
        apply Finset.filter_eq_self.2
        intro edge hedge
        have hedgeEq : edge = data.outerBoundaryEdge outer := by
          simpa using hedge
        subst edge
        exact Or.inl hfirst
      rw [hfilter]
      simp [hfirst]
    · have hfilter :
          {edge ∈ ({data.outerBoundaryEdge outer} : Finset G.edgeSet) |
              C edge = first ∨ C edge = second} =
            {data.outerBoundaryEdge outer} := by
        apply Finset.filter_eq_self.2
        intro edge hedge
        have hedgeEq : edge = data.outerBoundaryEdge outer := by
          simpa using hedge
        subst edge
        exact Or.inr hsecond
      rw [hfilter]
      simp [hsecond]
  · have hfirst : C (data.outerBoundaryEdge outer) ≠ first :=
      fun h => hselected (Or.inl h)
    have hsecond : C (data.outerBoundaryEdge outer) ≠ second :=
      fun h => hselected (Or.inr h)
    simp [hfirst, hsecond]

/-- Well-formed Cell-3 data supplies the exact cubic degree away from both
interfaces. -/
theorem interior_incidentEdgeFinset_card_eq_three
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    {vertex : V} (hvertex : vertex ∈ data.interiorVertices) :
    (incidentEdgeFinset G vertex).card = 3 := by
  have hnotBoundary := (Finset.mem_sdiff.mp hvertex).2
  apply hdata.cubic_elsewhere vertex
  · intro inner heq
    apply hnotBoundary
    apply Finset.mem_union_left
    exact (mem_innerStubVertices_iff data vertex).2 ⟨inner, heq.symm⟩
  · intro outer heq
    apply hnotBoundary
    apply Finset.mem_union_right
    exact (mem_outerStubVertices_iff data vertex).2 ⟨outer, heq.symm⟩

/-- At every Cell-3 interior vertex, the graph selected by a valid Tait-color
pair has degree exactly two. -/
theorem colorPairGraph_degree_interior_eq_two
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    {vertex : V} (hvertex : vertex ∈ data.interiorVertices) :
    (colorPairGraph C first second).degree vertex = 2 := by
  exact colorPairGraph_degree_eq_two_of_cubic_tait C hC vertex
    (interior_incidentEdgeFinset_card_eq_three data hdata hvertex) hpair

end SelectedPairDegrees

end AnnularBoundaryData

end GoertzelV24ClosedWebBoundaryData

end Mettapedia.GraphTheory.FourColor
