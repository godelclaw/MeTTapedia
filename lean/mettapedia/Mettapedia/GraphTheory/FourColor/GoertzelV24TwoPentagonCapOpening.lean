import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapOpeningWellFormed

/-!
# A literal two-cap annular opening

Cell 1 starts with an annular frontier tangle: it has the five ordered stubs
left by an inner pentagon cap and a nonempty free outer interface.  Opening
only one cap cannot manufacture that second interface.  The source's annular
laboratory instead removes two separated pentagon caps.

This file implements exactly that graph operation.  Given two vertex-separated
literal pentagon-cap presentations in a closed graph, it deletes both cap cycles,
retains both ordered spoke families as degree-one vertices, and exposes the
resulting `5 + 5` boundary datum.  It deliberately does *not* select the two
caps in a minimal counterexample or construct their annular embedding: those
are the source-specific formation and geometry obligations, respectively.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoPentagonCapOpening

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedBoundaryCounts
open GoertzelV24PentagonCapOpening

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  Fintype.ofFinite _

/-- Two literal pentagon caps with separated cap neighborhoods.  Vertex
disjointness alone would still allow a spoke joining the two caps, which would
make one edge serve as both interfaces; the two spoke conditions rule out that
degenerate boundary contact without assuming planar separation. -/
structure PentagonCapPair (G : SimpleGraph V) where
  inner : PentagonCap G
  outer : PentagonCap G
  vertexSupport_disjoint : Disjoint inner.vertexSupport outer.vertexSupport
  inner_spokeOuter_not_mem_outerSupport :
    ∀ step, inner.spokeOuter step ∉ outer.vertexSupport
  outer_spokeOuter_not_mem_innerSupport :
    ∀ step, outer.spokeOuter step ∉ inner.vertexSupport

namespace PentagonCapPair

/-- The ten cap-cycle edges removed by the literal two-cap opening. -/
def cycleSupport (caps : PentagonCapPair G) : Finset G.edgeSet :=
  caps.inner.cycleSupport ∪ caps.outer.cycleSupport

/-- The graph that retains both cap vertices as the two ordered stub families
and deletes exactly both cap cycles. -/
def openGraph (caps : PentagonCapPair G) : SimpleGraph V :=
  G.deleteEdges (edgeFinsetValueSet caps.cycleSupport)

local instance openGraphDecidableRel (caps : PentagonCapPair G) :
    DecidableRel caps.openGraph.Adj :=
  Classical.decRel _

local instance openGraphEdgeSetFintype (caps : PentagonCapPair G) :
    Fintype caps.openGraph.edgeSet :=
  caps.openGraph.fintypeEdgeSet

/-- Every edge of the simultaneous opening was already an edge of the closed
source graph. -/
theorem openGraph_edgeSet_subset (caps : PentagonCapPair G) :
    caps.openGraph.edgeSet ⊆ G.edgeSet := by
  intro edge hedge
  induction edge using Sym2.inductionOn with
  | _ first second =>
      change (G.deleteEdges (edgeFinsetValueSet caps.cycleSupport)).Adj first second at hedge
      change G.Adj first second
      exact (SimpleGraph.deleteEdges_adj.mp hedge).1

/-- Membership in the two-cap opening is just ambient edge membership plus
avoidance of the two deleted cycle supports. -/
theorem mem_openGraph_edgeSet_iff (caps : PentagonCapPair G)
    (edge : Sym2 V) (hG : edge ∈ G.edgeSet) :
    edge ∈ caps.openGraph.edgeSet ↔ edge ∉ edgeFinsetValueSet caps.cycleSupport := by
  induction edge using Sym2.inductionOn with
  | _ first second =>
      change (G.deleteEdges (edgeFinsetValueSet caps.cycleSupport)).Adj first second ↔ _
      rw [SimpleGraph.deleteEdges_adj]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨hG, h⟩

/-- A vertex from the inner cap cannot be a vertex from the outer cap. -/
theorem inner_vertex_not_mem_outerSupport (caps : PentagonCapPair G)
    (step : Fin 5) : caps.inner.vertex step ∉ caps.outer.vertexSupport := by
  intro houter
  exact (Finset.disjoint_left.mp caps.vertexSupport_disjoint)
    ((caps.inner.mem_vertexSupport_iff _).mpr ⟨step, rfl⟩) houter

/-- A vertex from the outer cap cannot be a vertex from the inner cap. -/
theorem outer_vertex_not_mem_innerSupport (caps : PentagonCapPair G)
    (step : Fin 5) : caps.outer.vertex step ∉ caps.inner.vertexSupport := by
  intro hinner
  exact (Finset.disjoint_left.mp caps.vertexSupport_disjoint)
    hinner ((caps.outer.mem_vertexSupport_iff _).mpr ⟨step, rfl⟩)

/-- An inner spoke is not deleted as a cycle edge of the outer cap. -/
theorem inner_spoke_not_mem_outerCycleSupport (caps : PentagonCapPair G)
    (step : Fin 5) :
    (caps.inner.spokeEdge step).1 ∉ edgeFinsetValueSet caps.outer.cycleSupport := by
  intro hremoved
  rcases (mem_edgeFinsetValueSet_iff caps.outer.cycleSupport _).mp hremoved with
    ⟨edge, hedge, hvalue⟩
  rcases Finset.mem_map.mp hedge with ⟨cycle, -, hcycle⟩
  have hcycleValue : (caps.outer.cycleEdge cycle).1 = (caps.inner.spokeEdge step).1 := by
    calc
      (caps.outer.cycleEdge cycle).1 = edge.1 := congrArg Subtype.val hcycle
      _ = (caps.inner.spokeEdge step).1 := hvalue
  have hinnerVertex : caps.inner.vertex step ∈ (caps.outer.cycleEdge cycle).1 := by
    rw [hcycleValue]
    exact caps.inner.spokeEdge_incident step
  rcases caps.outer.cycleEdge_endpoint_eq_vertex cycle _ hinnerVertex with
    ⟨outerStep, houterStep⟩
  exact caps.inner_vertex_not_mem_outerSupport step
    ((caps.outer.mem_vertexSupport_iff _).mpr ⟨outerStep, houterStep⟩)

/-- An outer spoke is not deleted as a cycle edge of the inner cap. -/
theorem outer_spoke_not_mem_innerCycleSupport (caps : PentagonCapPair G)
    (step : Fin 5) :
    (caps.outer.spokeEdge step).1 ∉ edgeFinsetValueSet caps.inner.cycleSupport := by
  intro hremoved
  rcases (mem_edgeFinsetValueSet_iff caps.inner.cycleSupport _).mp hremoved with
    ⟨edge, hedge, hvalue⟩
  rcases Finset.mem_map.mp hedge with ⟨cycle, -, hcycle⟩
  have hcycleValue : (caps.inner.cycleEdge cycle).1 = (caps.outer.spokeEdge step).1 := by
    calc
      (caps.inner.cycleEdge cycle).1 = edge.1 := congrArg Subtype.val hcycle
      _ = (caps.outer.spokeEdge step).1 := hvalue
  have houterVertex : caps.outer.vertex step ∈ (caps.inner.cycleEdge cycle).1 := by
    rw [hcycleValue]
    exact caps.outer.spokeEdge_incident step
  rcases caps.inner.cycleEdge_endpoint_eq_vertex cycle _ houterVertex with
    ⟨innerStep, hinnerStep⟩
  exact caps.outer_vertex_not_mem_innerSupport step
    ((caps.inner.mem_vertexSupport_iff _).mpr ⟨innerStep, hinnerStep⟩)

/-- The inner cap spoke survives the simultaneous opening. -/
theorem inner_spoke_not_mem_removed (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.inner.spokeEdge step).1 ∉ edgeFinsetValueSet caps.cycleSupport := by
  intro hremoved
  rcases (mem_edgeFinsetValueSet_iff caps.cycleSupport _).mp hremoved with
    ⟨edge, hedge, hvalue⟩
  change edge ∈ caps.inner.cycleSupport ∪ caps.outer.cycleSupport at hedge
  rw [Finset.mem_union] at hedge
  rcases hedge with hinner | houter
  · apply caps.inner.spokeEdge_not_mem_removed step
    apply (mem_edgeFinsetValueSet_iff caps.inner.cycleSupport _).mpr
    exact ⟨edge, hinner, hvalue⟩
  · apply caps.inner_spoke_not_mem_outerCycleSupport step
    apply (mem_edgeFinsetValueSet_iff caps.outer.cycleSupport _).mpr
    exact ⟨edge, houter, hvalue⟩

/-- The outer cap spoke survives the simultaneous opening. -/
theorem outer_spoke_not_mem_removed (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.outer.spokeEdge step).1 ∉ edgeFinsetValueSet caps.cycleSupport := by
  intro hremoved
  rcases (mem_edgeFinsetValueSet_iff caps.cycleSupport _).mp hremoved with
    ⟨edge, hedge, hvalue⟩
  change edge ∈ caps.inner.cycleSupport ∪ caps.outer.cycleSupport at hedge
  rw [Finset.mem_union] at hedge
  rcases hedge with hinner | houter
  · apply caps.outer_spoke_not_mem_innerCycleSupport step
    apply (mem_edgeFinsetValueSet_iff caps.inner.cycleSupport _).mpr
    exact ⟨edge, hinner, hvalue⟩
  · apply caps.outer.spokeEdge_not_mem_removed step
    apply (mem_edgeFinsetValueSet_iff caps.outer.cycleSupport _).mpr
    exact ⟨edge, houter, hvalue⟩

/-- An inner cap-cycle edge is deleted by the simultaneous opening. -/
theorem inner_cycleEdge_mem_removed (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.inner.cycleEdge step).1 ∈ edgeFinsetValueSet caps.cycleSupport := by
  apply (mem_edgeFinsetValueSet_iff caps.cycleSupport _).mpr
  refine ⟨caps.inner.cycleEdge step, ?_, rfl⟩
  change caps.inner.cycleEdge step ∈ caps.inner.cycleSupport ∪ caps.outer.cycleSupport
  exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨step, Finset.mem_univ step, rfl⟩)

/-- An outer cap-cycle edge is deleted by the simultaneous opening. -/
theorem outer_cycleEdge_mem_removed (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.outer.cycleEdge step).1 ∈ edgeFinsetValueSet caps.cycleSupport := by
  apply (mem_edgeFinsetValueSet_iff caps.cycleSupport _).mpr
  refine ⟨caps.outer.cycleEdge step, ?_, rfl⟩
  change caps.outer.cycleEdge step ∈ caps.inner.cycleSupport ∪ caps.outer.cycleSupport
  exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨step, Finset.mem_univ step, rfl⟩)

/-- The `step`-th inner boundary edge in the simultaneous opening. -/
def innerOpenSpokeEdge (caps : PentagonCapPair G) (step : Fin 5) :
    caps.openGraph.edgeSet :=
  ⟨(caps.inner.spokeEdge step).1,
    (caps.mem_openGraph_edgeSet_iff (caps.inner.spokeEdge step).1
      (caps.inner.spokeEdge step).2).mpr (caps.inner_spoke_not_mem_removed step)⟩

/-- The `step`-th outer boundary edge in the simultaneous opening. -/
def outerOpenSpokeEdge (caps : PentagonCapPair G) (step : Fin 5) :
    caps.openGraph.edgeSet :=
  ⟨(caps.outer.spokeEdge step).1,
    (caps.mem_openGraph_edgeSet_iff (caps.outer.spokeEdge step).1
      (caps.outer.spokeEdge step).2).mpr (caps.outer_spoke_not_mem_removed step)⟩

@[simp] theorem innerOpenSpokeEdge_val (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.innerOpenSpokeEdge step).1 = (caps.inner.spokeEdge step).1 :=
  rfl

@[simp] theorem outerOpenSpokeEdge_val (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.outerOpenSpokeEdge step).1 = (caps.outer.spokeEdge step).1 :=
  rfl

/-- The inner cap vertex has only its named spoke left in the simultaneous
opening. -/
theorem openGraph_incidentEdgeFinset_innerVertex_eq_singleton
    (caps : PentagonCapPair G) (step : Fin 5) :
    incidentEdgeFinset caps.openGraph (caps.inner.vertex step) =
      {caps.innerOpenSpokeEdge step} := by
  ext openEdge
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hincident
    let ambientEdge : G.edgeSet :=
      ⟨openEdge.1, caps.openGraph_edgeSet_subset openEdge.2⟩
    have hambientIncident : ambientEdge ∈
        incidentEdgeFinset G (caps.inner.vertex step) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincident⟩
    rw [caps.inner.incident_eq step] at hambientIncident
    simp only [Finset.mem_insert, Finset.mem_singleton] at hambientIncident
    rcases hambientIncident with hcycle | hcycle | hspoke
    · exfalso
      have hdeleted : openEdge.1 ∉ edgeFinsetValueSet caps.cycleSupport :=
        (caps.mem_openGraph_edgeSet_iff openEdge.1
          (caps.openGraph_edgeSet_subset openEdge.2)).mp openEdge.2
      apply hdeleted
      have hvalue : openEdge.1 = (caps.inner.cycleEdge step).1 := by
        exact congrArg Subtype.val hcycle
      simpa [hvalue] using caps.inner_cycleEdge_mem_removed step
    · exfalso
      have hdeleted : openEdge.1 ∉ edgeFinsetValueSet caps.cycleSupport :=
        (caps.mem_openGraph_edgeSet_iff openEdge.1
          (caps.openGraph_edgeSet_subset openEdge.2)).mp openEdge.2
      apply hdeleted
      have hvalue : openEdge.1 = (caps.inner.cycleEdge (caps.inner.cycleMate step)).1 := by
        exact congrArg Subtype.val hcycle
      simpa [hvalue] using caps.inner_cycleEdge_mem_removed (caps.inner.cycleMate step)
    · apply Subtype.ext
      simpa [innerOpenSpokeEdge_val] using congrArg Subtype.val hspoke
  · intro hopenSpoke
    subst openEdge
    simpa [innerOpenSpokeEdge_val, caps.inner.spokeEdge_eq step] using
      caps.inner.spokeEdge_incident step

/-- The outer cap vertex has only its named spoke left in the simultaneous
opening. -/
theorem openGraph_incidentEdgeFinset_outerVertex_eq_singleton
    (caps : PentagonCapPair G) (step : Fin 5) :
    incidentEdgeFinset caps.openGraph (caps.outer.vertex step) =
      {caps.outerOpenSpokeEdge step} := by
  ext openEdge
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hincident
    let ambientEdge : G.edgeSet :=
      ⟨openEdge.1, caps.openGraph_edgeSet_subset openEdge.2⟩
    have hambientIncident : ambientEdge ∈
        incidentEdgeFinset G (caps.outer.vertex step) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincident⟩
    rw [caps.outer.incident_eq step] at hambientIncident
    simp only [Finset.mem_insert, Finset.mem_singleton] at hambientIncident
    rcases hambientIncident with hcycle | hcycle | hspoke
    · exfalso
      have hdeleted : openEdge.1 ∉ edgeFinsetValueSet caps.cycleSupport :=
        (caps.mem_openGraph_edgeSet_iff openEdge.1
          (caps.openGraph_edgeSet_subset openEdge.2)).mp openEdge.2
      apply hdeleted
      have hvalue : openEdge.1 = (caps.outer.cycleEdge step).1 := by
        exact congrArg Subtype.val hcycle
      simpa [hvalue] using caps.outer_cycleEdge_mem_removed step
    · exfalso
      have hdeleted : openEdge.1 ∉ edgeFinsetValueSet caps.cycleSupport :=
        (caps.mem_openGraph_edgeSet_iff openEdge.1
          (caps.openGraph_edgeSet_subset openEdge.2)).mp openEdge.2
      apply hdeleted
      have hvalue : openEdge.1 = (caps.outer.cycleEdge (caps.outer.cycleMate step)).1 := by
        exact congrArg Subtype.val hcycle
      simpa [hvalue] using caps.outer_cycleEdge_mem_removed (caps.outer.cycleMate step)
    · apply Subtype.ext
      simpa [outerOpenSpokeEdge_val] using congrArg Subtype.val hspoke
  · intro hopenSpoke
    subst openEdge
    simpa [outerOpenSpokeEdge_val, caps.outer.spokeEdge_eq step] using
      caps.outer.spokeEdge_incident step

/-- Both cap stub families are genuinely degree one in the simultaneous
opening. -/
theorem openGraph_incidentEdgeFinset_card_innerVertex_eq_one
    (caps : PentagonCapPair G) (step : Fin 5) :
    (incidentEdgeFinset caps.openGraph (caps.inner.vertex step)).card = 1 := by
  rw [caps.openGraph_incidentEdgeFinset_innerVertex_eq_singleton step]
  simp

theorem openGraph_incidentEdgeFinset_card_outerVertex_eq_one
    (caps : PentagonCapPair G) (step : Fin 5) :
    (incidentEdgeFinset caps.openGraph (caps.outer.vertex step)).card = 1 := by
  rw [caps.openGraph_incidentEdgeFinset_outerVertex_eq_singleton step]
  simp

/-- The ordered inner opening spoke is incident with its named stub. -/
theorem innerOpenSpokeEdge_incident (caps : PentagonCapPair G) (step : Fin 5) :
    caps.innerOpenSpokeEdge step ∈
      incidentEdgeFinset caps.openGraph (caps.inner.vertex step) := by
  rw [caps.openGraph_incidentEdgeFinset_innerVertex_eq_singleton step]
  simp

/-- The ordered outer opening spoke is incident with its named stub. -/
theorem outerOpenSpokeEdge_incident (caps : PentagonCapPair G) (step : Fin 5) :
    caps.outerOpenSpokeEdge step ∈
      incidentEdgeFinset caps.openGraph (caps.outer.vertex step) := by
  rw [caps.openGraph_incidentEdgeFinset_outerVertex_eq_singleton step]
  simp

/-- The named spoke endpoint is the unique neighbour of an inner cap vertex
after the simultaneous cap opening. -/
theorem eq_inner_spokeOuter_of_openGraph_adj_vertex
    (caps : PentagonCapPair G) (step : Fin 5) {outside : V}
    (hadj : caps.openGraph.Adj outside (caps.inner.vertex step)) :
    outside = caps.inner.spokeOuter step := by
  let openEdge : caps.openGraph.edgeSet :=
    ⟨s(outside, caps.inner.vertex step), by simpa using hadj⟩
  have hincident : openEdge ∈
      incidentEdgeFinset caps.openGraph (caps.inner.vertex step) := by
    simp [openEdge, incidentEdgeFinset, Sym2.mem_iff]
  rw [caps.openGraph_incidentEdgeFinset_innerVertex_eq_singleton step] at hincident
  have hedge : openEdge = caps.innerOpenSpokeEdge step :=
    Finset.mem_singleton.mp hincident
  have hpairs : s(outside, caps.inner.vertex step) =
      s(caps.inner.vertex step, caps.inner.spokeOuter step) := by
    calc
      s(outside, caps.inner.vertex step) = openEdge.1 := rfl
      _ = (caps.innerOpenSpokeEdge step).1 := congrArg Subtype.val hedge
      _ = (caps.inner.spokeEdge step).1 := by simp
      _ = s(caps.inner.vertex step, caps.inner.spokeOuter step) :=
        caps.inner.spokeEdge_eq step
  rcases Sym2.eq_iff.mp hpairs with hstraight | hswapped
  · exact False.elim (caps.inner.spokeOuter_ne_vertex step step hstraight.2.symm)
  · exact hswapped.1

/-- The named spoke endpoint is the unique neighbour of an outer cap vertex
after the simultaneous cap opening. -/
theorem eq_outer_spokeOuter_of_openGraph_adj_vertex
    (caps : PentagonCapPair G) (step : Fin 5) {outside : V}
    (hadj : caps.openGraph.Adj outside (caps.outer.vertex step)) :
    outside = caps.outer.spokeOuter step := by
  let openEdge : caps.openGraph.edgeSet :=
    ⟨s(outside, caps.outer.vertex step), by simpa using hadj⟩
  have hincident : openEdge ∈
      incidentEdgeFinset caps.openGraph (caps.outer.vertex step) := by
    simp [openEdge, incidentEdgeFinset, Sym2.mem_iff]
  rw [caps.openGraph_incidentEdgeFinset_outerVertex_eq_singleton step] at hincident
  have hedge : openEdge = caps.outerOpenSpokeEdge step :=
    Finset.mem_singleton.mp hincident
  have hpairs : s(outside, caps.outer.vertex step) =
      s(caps.outer.vertex step, caps.outer.spokeOuter step) := by
    calc
      s(outside, caps.outer.vertex step) = openEdge.1 := rfl
      _ = (caps.outerOpenSpokeEdge step).1 := congrArg Subtype.val hedge
      _ = (caps.outer.spokeEdge step).1 := by simp
      _ = s(caps.outer.vertex step, caps.outer.spokeOuter step) :=
        caps.outer.spokeEdge_eq step
  rcases Sym2.eq_iff.mp hpairs with hstraight | hswapped
  · exact False.elim (caps.outer.spokeOuter_ne_vertex step step hstraight.2.symm)
  · exact hswapped.1

theorem openGraph_adj_spokeOuter_innerVertex (caps : PentagonCapPair G)
    (step : Fin 5) :
    caps.openGraph.Adj (caps.inner.spokeOuter step) (caps.inner.vertex step) := by
  have hmem := (caps.innerOpenSpokeEdge step).2
  simpa [SimpleGraph.mem_edgeSet, caps.inner.spokeEdge_eq step, Sym2.eq_swap] using hmem

theorem openGraph_adj_spokeOuter_outerVertex (caps : PentagonCapPair G)
    (step : Fin 5) :
    caps.openGraph.Adj (caps.outer.spokeOuter step) (caps.outer.vertex step) := by
  have hmem := (caps.outerOpenSpokeEdge step).2
  simpa [SimpleGraph.mem_edgeSet, caps.outer.spokeEdge_eq step, Sym2.eq_swap] using hmem

/-- No two inner toolchain stub vertices are adjacent after both cap cycles
are opened. -/
theorem not_openGraph_adj_innerVertices (caps : PentagonCapPair G)
    (first second : Fin 5) :
    ¬ caps.openGraph.Adj (caps.inner.vertex first) (caps.inner.vertex second) := by
  intro hadj
  have hspoke := caps.eq_inner_spokeOuter_of_openGraph_adj_vertex first
    (caps.openGraph.adj_symm hadj)
  exact caps.inner.spokeOuter_not_mem_vertexSupport first
    ((caps.inner.mem_vertexSupport_iff _).mpr ⟨second, hspoke⟩)

/-- No two outer toolchain stub vertices are adjacent after both cap cycles
are opened. -/
theorem not_openGraph_adj_outerVertices (caps : PentagonCapPair G)
    (first second : Fin 5) :
    ¬ caps.openGraph.Adj (caps.outer.vertex first) (caps.outer.vertex second) := by
  intro hadj
  have hspoke := caps.eq_outer_spokeOuter_of_openGraph_adj_vertex first
    (caps.openGraph.adj_symm hadj)
  exact caps.outer.spokeOuter_not_mem_vertexSupport first
    ((caps.outer.mem_vertexSupport_iff _).mpr ⟨second, hspoke⟩)

/-- The two separated cap families remain non-adjacent in the toolchain
opening.  This is exactly where the no-spoke contact condition is used. -/
theorem not_openGraph_adj_inner_outerVertices (caps : PentagonCapPair G)
    (innerStep outerStep : Fin 5) :
    ¬ caps.openGraph.Adj (caps.inner.vertex innerStep) (caps.outer.vertex outerStep) := by
  intro hadj
  have hspoke := caps.eq_inner_spokeOuter_of_openGraph_adj_vertex innerStep
    (caps.openGraph.adj_symm hadj)
  exact caps.inner_spokeOuter_not_mem_outerSupport innerStep
    ((caps.outer.mem_vertexSupport_iff _).mpr ⟨outerStep, hspoke⟩)

/-- Simultaneously deleting the two cap cycles changes no neighbour outside
either cap support. -/
theorem openGraph_neighborFinset_eq_of_not_mem_supports
    (caps : PentagonCapPair G) {vertex : V}
    (hinner : vertex ∉ caps.inner.vertexSupport)
    (houter : vertex ∉ caps.outer.vertexSupport) :
    caps.openGraph.neighborFinset vertex = G.neighborFinset vertex := by
  ext neighbor
  simp only [SimpleGraph.mem_neighborFinset]
  change (G.deleteEdges (edgeFinsetValueSet caps.cycleSupport)).Adj vertex neighbor ↔
    G.Adj vertex neighbor
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · exact And.left
  · intro hadj
    refine ⟨hadj, ?_⟩
    intro hremoved
    rcases (mem_edgeFinsetValueSet_iff caps.cycleSupport _).mp hremoved with
      ⟨edge, hedge, hedgeValue⟩
    change edge ∈ caps.inner.cycleSupport ∪ caps.outer.cycleSupport at hedge
    rw [Finset.mem_union] at hedge
    rcases hedge with hinnerCycle | houterCycle
    · rcases Finset.mem_map.mp hinnerCycle with ⟨cycle, -, hcycle⟩
      have hcycleValue : (caps.inner.cycleEdge cycle).1 = s(vertex, neighbor) := by
        calc
          (caps.inner.cycleEdge cycle).1 = edge.1 := congrArg Subtype.val hcycle
          _ = s(vertex, neighbor) := hedgeValue
      have hvertexOnCycle : vertex ∈ (caps.inner.cycleEdge cycle).1 := by
        rw [hcycleValue]
        simp
      rcases caps.inner.cycleEdge_endpoint_eq_vertex cycle vertex hvertexOnCycle with
        ⟨step, hstep⟩
      exact hinner ((caps.inner.mem_vertexSupport_iff _).mpr ⟨step, hstep⟩)
    · rcases Finset.mem_map.mp houterCycle with ⟨cycle, -, hcycle⟩
      have hcycleValue : (caps.outer.cycleEdge cycle).1 = s(vertex, neighbor) := by
        calc
          (caps.outer.cycleEdge cycle).1 = edge.1 := congrArg Subtype.val hcycle
          _ = s(vertex, neighbor) := hedgeValue
      have hvertexOnCycle : vertex ∈ (caps.outer.cycleEdge cycle).1 := by
        rw [hcycleValue]
        simp
      rcases caps.outer.cycleEdge_endpoint_eq_vertex cycle vertex hvertexOnCycle with
        ⟨step, hstep⟩
      exact houter ((caps.outer.mem_vertexSupport_iff _).mpr ⟨step, hstep⟩)

/-- Away from both cap interfaces, simultaneous cap opening preserves the
cubic degree of the closed source graph. -/
theorem openGraph_incidentEdgeFinset_card_eq_three_of_not_mem_supports
    (caps : PentagonCapPair G) (hregular : G.IsRegularOfDegree 3)
    {vertex : V} (hinner : vertex ∉ caps.inner.vertexSupport)
    (houter : vertex ∉ caps.outer.vertexSupport) :
    (incidentEdgeFinset caps.openGraph vertex).card = 3 := by
  calc
    (incidentEdgeFinset caps.openGraph vertex).card = caps.openGraph.degree vertex :=
      incidentEdgeFinset_card_eq_degree (G := caps.openGraph) vertex
    _ = 3 := by
      change (caps.openGraph.neighborFinset vertex).card = 3
      rw [caps.openGraph_neighborFinset_eq_of_not_mem_supports hinner houter]
      exact hregular vertex

/-- The source order is injective on the five inner opening spokes. -/
def innerOpenSpokeEmbedding (caps : PentagonCapPair G) : Fin 5 ↪ caps.openGraph.edgeSet :=
  ⟨caps.innerOpenSpokeEdge, by
    intro first second heq
    apply caps.inner.spokeEdge.injective
    apply Subtype.ext
    simpa only [innerOpenSpokeEdge_val] using congrArg Subtype.val heq⟩

/-- The source order is injective on the five outer opening spokes. -/
def outerOpenSpokeEmbedding (caps : PentagonCapPair G) : Fin 5 ↪ caps.openGraph.edgeSet :=
  ⟨caps.outerOpenSpokeEdge, by
    intro first second heq
    apply caps.outer.spokeEdge.injective
    apply Subtype.ext
    simpa only [outerOpenSpokeEdge_val] using congrArg Subtype.val heq⟩

/-- The literal two-cap graph carries five ordered inner and five ordered
outer stubs.  This is a real graph construction, but it does not by itself
prove that the two openings bound an annulus in the ambient rotation system. -/
def boundaryData (caps : PentagonCapPair G) : AnnularBoundaryData caps.openGraph 5 where
  innerStub := caps.inner.vertex
  outerStub := caps.outer.vertex
  innerBoundaryEdge := caps.innerOpenSpokeEmbedding
  outerBoundaryEdge := caps.outerOpenSpokeEmbedding

/-- The two named boundary families use disjoint edges.  The two no-spoke
contact fields in `PentagonCapPair` are exactly what excludes the otherwise
possible edge shared by an inner and outer cap vertex. -/
theorem innerOpenSpokeEdge_ne_outerOpenSpokeEdge
    (caps : PentagonCapPair G) (innerStep outerStep : Fin 5) :
    caps.innerOpenSpokeEdge innerStep ≠ caps.outerOpenSpokeEdge outerStep := by
  intro heq
  have hedge : (caps.inner.spokeEdge innerStep).1 =
      (caps.outer.spokeEdge outerStep).1 := by
    simpa only [innerOpenSpokeEdge_val, outerOpenSpokeEdge_val] using
      congrArg Subtype.val heq
  have hpairs : s(caps.inner.vertex innerStep, caps.inner.spokeOuter innerStep) =
      s(caps.outer.vertex outerStep, caps.outer.spokeOuter outerStep) := by
    simpa [caps.inner.spokeEdge_eq innerStep,
      caps.outer.spokeEdge_eq outerStep] using hedge
  rcases Sym2.eq_iff.mp hpairs with hstraight | hswapped
  · exact caps.inner_vertex_not_mem_outerSupport innerStep
      ((caps.outer.mem_vertexSupport_iff _).mpr ⟨outerStep, hstraight.1.symm⟩)
  · exact caps.inner_spokeOuter_not_mem_outerSupport innerStep
      ((caps.outer.mem_vertexSupport_iff _).mpr ⟨outerStep, hswapped.2.symm⟩)

/-- A cubic closed graph opened at a separated pair of literal pentagon caps
is a well-formed annular boundary graph with five stubs on each side.  This
proves the graph/interface half of the source's two-cap model; it does not
yet supply the annular rotation-system embedding or select such a pair from a
minimal counterexample. -/
theorem boundaryData_wellFormed_of_isRegularOfDegree_three
    (caps : PentagonCapPair G) (hregular : G.IsRegularOfDegree 3) :
    (caps.boundaryData).WellFormed := by
  refine {
    inner_outer_stub_disjoint := ?_,
    inner_outer_edge_disjoint := ?_,
    innerBoundaryEdge_incident := ?_,
    outerBoundaryEdge_incident := ?_,
    inner_stub_degree_one := ?_,
    outer_stub_degree_one := ?_,
    cubic_elsewhere := ?_ }
  · intro innerStep outerStep heq
    exact caps.inner_vertex_not_mem_outerSupport innerStep
      ((caps.outer.mem_vertexSupport_iff _).mpr ⟨outerStep, heq.symm⟩)
  · intro innerStep outerStep
    exact caps.innerOpenSpokeEdge_ne_outerOpenSpokeEdge innerStep outerStep
  · intro innerStep
    exact caps.innerOpenSpokeEdge_incident innerStep
  · intro outerStep
    exact caps.outerOpenSpokeEdge_incident outerStep
  · intro innerStep
    exact caps.openGraph_incidentEdgeFinset_card_innerVertex_eq_one innerStep
  · intro outerStep
    exact caps.openGraph_incidentEdgeFinset_card_outerVertex_eq_one outerStep
  · intro vertex hinner houter
    apply caps.openGraph_incidentEdgeFinset_card_eq_three_of_not_mem_supports hregular
    · intro hmem
      rcases (caps.inner.mem_vertexSupport_iff _).mp hmem with ⟨innerStep, hstep⟩
      exact hinner innerStep hstep.symm
    · intro hmem
      rcases (caps.outer.mem_vertexSupport_iff _).mp hmem with ⟨outerStep, hstep⟩
      exact houter outerStep hstep.symm

end PentagonCapPair

end

end GoertzelV24TwoPentagonCapOpening

end Mettapedia.GraphTheory.FourColor
