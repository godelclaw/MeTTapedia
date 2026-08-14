import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebBoundaryData
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteDeletionCyclicCut

/-!
# Toolchain realization of a pentagon cap opening

The Cell--3 manuscript describes deleting the five vertices of a pentagon cap
while retaining its spokes as stubs.  The supplied Fable toolchain realizes
that intended tangle by retaining those five vertices and deleting the five
cap-cycle edges, which makes the original cap vertices degree-one spoke stubs.
This file formalizes the toolchain's concrete graph operation.  It does not
claim the two presentations are definitionally equal: any later use that
needs their identification must provide the corresponding graph isomorphism.

Given an actual cap presentation, its toolchain graph and its ordered
five-stub inner boundary are computed; no annular carrier is postulated.

The later source-specific formation theorem still has to obtain this cap from
the closed normal-form map, retain the desired Cell--3 corridor, and build the
outer annular boundary.  Those are deliberately not hidden in the definition
below.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PentagonCapOpening

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FiniteDeletionCyclicCut

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  Fintype.ofFinite _

/-- The graph data of one literal pentagon cap.  `cycleEdge i` and
`cycleEdge (cycleMate i)` are the two cap-cycle edges at `vertex i`; the
third incident edge is its outward spoke. -/
structure PentagonCap (G : SimpleGraph V) where
  vertex : Fin 5 ↪ V
  cycleEdge : Fin 5 ↪ G.edgeSet
  spokeEdge : Fin 5 ↪ G.edgeSet
  /-- The retained endpoint of each ordered cap spoke.  This is source data,
  not a choice made by the opening construction. -/
  spokeOuter : Fin 5 → V
  cycleMate : Equiv.Perm (Fin 5)
  cycleMate_noFixed : ∀ step, cycleMate step ≠ step
  cycle_spoke_ne : ∀ cycle spoke, cycleEdge cycle ≠ spokeEdge spoke
  /-- Each named spoke joins its cap vertex to its named retained endpoint. -/
  spokeEdge_eq : ∀ step,
    (spokeEdge step).1 = s(vertex step, spokeOuter step)
  /-- The retained endpoint of a spoke is outside the five cap vertices. -/
  spokeOuter_ne_vertex : ∀ spoke capStep,
    spokeOuter spoke ≠ vertex capStep
  /-- Both endpoints of a cycle edge are cap vertices.  This distinguishes
  deleted cap-cycle edges from the five retained boundary spokes. -/
  cycleEdge_endpoint_eq_vertex : ∀ cycle endpoint,
    endpoint ∈ (cycleEdge cycle).1 → ∃ capStep, vertex capStep = endpoint
  incident_eq : ∀ step : Fin 5,
    incidentEdgeFinset G (vertex step) =
      {cycleEdge step, cycleEdge (cycleMate step), spokeEdge step}

namespace PentagonCap

/-- The five vertices deleted in the manuscript-side opening. -/
def vertexSupport (cap : PentagonCap G) : Finset V :=
  Finset.univ.map cap.vertex

@[simp] theorem mem_vertexSupport_iff (cap : PentagonCap G) (vertex : V) :
    vertex ∈ cap.vertexSupport ↔ ∃ step : Fin 5, cap.vertex step = vertex := by
  simp [vertexSupport]

/-- A named retained spoke endpoint really lies outside the deleted cap. -/
theorem spokeOuter_not_mem_vertexSupport (cap : PentagonCap G) (step : Fin 5) :
    cap.spokeOuter step ∉ cap.vertexSupport := by
  intro hmem
  rcases (cap.mem_vertexSupport_iff _).mp hmem with ⟨capStep, hcapStep⟩
  exact cap.spokeOuter_ne_vertex step capStep hcapStep.symm

/-- The five cap-cycle edges to remove. -/
def cycleSupport (cap : PentagonCap G) : Finset G.edgeSet :=
  Finset.univ.map cap.cycleEdge

/-- The literal tangle graph used by the supplied toolchain: only the cap-cycle
edges are removed.  The five cap vertices themselves remain as inner stubs. -/
def openGraph (cap : PentagonCap G) : SimpleGraph V :=
  G.deleteEdges (edgeFinsetValueSet cap.cycleSupport)

/-- Every edge of the cap opening was already an edge of the closed graph. -/
theorem openGraph_edgeSet_subset (cap : PentagonCap G) :
    cap.openGraph.edgeSet ⊆ G.edgeSet := by
  intro edge hedge
  induction edge using Sym2.inductionOn with
  | _ first second =>
      change (G.deleteEdges (edgeFinsetValueSet cap.cycleSupport)).Adj first second at hedge
      change G.Adj first second
      exact (SimpleGraph.deleteEdges_adj.mp hedge).1

/-- An edge of the cap opening is not one of the deleted cap-cycle edges. -/
theorem openGraph_edge_not_mem_removed (cap : PentagonCap G)
    {edge : Sym2 V} (hedge : edge ∈ cap.openGraph.edgeSet) :
    edge ∉ edgeFinsetValueSet cap.cycleSupport := by
  induction edge using Sym2.inductionOn with
  | _ first second =>
      change (G.deleteEdges (edgeFinsetValueSet cap.cycleSupport)).Adj first second at hedge
      exact (SimpleGraph.deleteEdges_adj.mp hedge).2

/-- On an original graph edge, membership in the cap opening says exactly
that the edge was not one of the five deleted cycle edges. -/
theorem mem_openGraph_edgeSet_iff (cap : PentagonCap G)
    (edge : Sym2 V) (hG : edge ∈ G.edgeSet) :
    edge ∈ cap.openGraph.edgeSet ↔ edge ∉ edgeFinsetValueSet cap.cycleSupport := by
  induction edge using Sym2.inductionOn with
  | _ first second =>
      change (G.deleteEdges (edgeFinsetValueSet cap.cycleSupport)).Adj first second ↔ _
      rw [SimpleGraph.deleteEdges_adj]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨hG, h⟩

/-- Every cap-cycle edge is removed in `openGraph`. -/
theorem cycleEdge_mem_removed (cap : PentagonCap G) (step : Fin 5) :
    (cap.cycleEdge step).1 ∈ edgeFinsetValueSet cap.cycleSupport := by
  apply (mem_edgeFinsetValueSet_iff cap.cycleSupport _).mpr
  refine ⟨cap.cycleEdge step, ?_, rfl⟩
  exact Finset.mem_map.mpr ⟨step, Finset.mem_univ step, rfl⟩

/-- A cap spoke is not among the five removed cycle edges. -/
theorem spokeEdge_not_mem_removed (cap : PentagonCap G) (step : Fin 5) :
    (cap.spokeEdge step).1 ∉ edgeFinsetValueSet cap.cycleSupport := by
  intro hremoved
  rcases (mem_edgeFinsetValueSet_iff cap.cycleSupport _).mp hremoved with
    ⟨edge, hedge, hedgeValue⟩
  rcases Finset.mem_map.mp hedge with ⟨cycle, -, hcycle⟩
  apply cap.cycle_spoke_ne cycle step
  apply Subtype.ext
  calc
    (cap.cycleEdge cycle).1 = edge.1 := congrArg Subtype.val hcycle
    _ = (cap.spokeEdge step).1 := hedgeValue

/-- The cap spoke at this position survives as an edge of the literal open
tangle. -/
def openSpokeEdge (cap : PentagonCap G) (step : Fin 5) :
    cap.openGraph.edgeSet :=
  ⟨(cap.spokeEdge step).1, by
    exact (cap.mem_openGraph_edgeSet_iff (cap.spokeEdge step).1
      (cap.spokeEdge step).2).mpr (cap.spokeEdge_not_mem_removed step)⟩

theorem openSpokeEdge_val (cap : PentagonCap G) (step : Fin 5) :
    (cap.openSpokeEdge step).1 = (cap.spokeEdge step).1 :=
  rfl

/-- The five surviving spokes retain their source order without collisions. -/
def openSpokeEmbedding (cap : PentagonCap G) : Fin 5 ↪ cap.openGraph.edgeSet :=
  ⟨cap.openSpokeEdge, by
    intro first second heq
    apply cap.spokeEdge.injective
    apply Subtype.ext
    simpa only [openSpokeEdge_val] using congrArg Subtype.val heq⟩

/-- The source's inner five-stub interface after opening the cap.  There is
not yet an outer interface here, so it is represented by `Fin 0` rather than
silently inventing one. -/
def innerBoundaryData (cap : PentagonCap G) :
    AnnularBoundaryData cap.openGraph 0 where
  innerStub := cap.vertex
  outerStub := ⟨Fin.elim0, by
    intro first
    exact Fin.elim0 first⟩
  innerBoundaryEdge := cap.openSpokeEmbedding
  outerBoundaryEdge := ⟨Fin.elim0, by
    intro first
    exact Fin.elim0 first⟩

/-- The literal cap spoke is incident with its named cap vertex in the closed
graph. -/
theorem spokeEdge_incident (cap : PentagonCap G) (step : Fin 5) :
    cap.vertex step ∈ (cap.spokeEdge step).1 := by
  have hmem : cap.spokeEdge step ∈
      incidentEdgeFinset G (cap.vertex step) := by
    rw [cap.incident_eq step]
    simp
  exact (Finset.mem_filter.mp hmem).2

/-- The opened cap vertex has no edge other than its retained spoke.  This is
the exact finite-set form of the source's degree-one-stub assertion. -/
theorem openGraph_incidentEdgeFinset_capVertex_eq_singleton
    (cap : PentagonCap G) (step : Fin 5) :
    incidentEdgeFinset cap.openGraph (cap.vertex step) =
      {cap.openSpokeEdge step} := by
  ext openEdge
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hincident
    let ambientEdge : G.edgeSet :=
      ⟨openEdge.1, cap.openGraph_edgeSet_subset openEdge.2⟩
    have hambientIncident : ambientEdge ∈
        incidentEdgeFinset G (cap.vertex step) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincident⟩
    rw [cap.incident_eq step] at hambientIncident
    simp only [Finset.mem_insert, Finset.mem_singleton] at hambientIncident
    rcases hambientIncident with hcycle | hcycle | hspoke
    · exfalso
      have hdeleted := cap.openGraph_edge_not_mem_removed openEdge.2
      apply hdeleted
      have hvalue : openEdge.1 = (cap.cycleEdge step).1 := by
        exact congrArg Subtype.val hcycle
      simpa [hvalue] using cap.cycleEdge_mem_removed step
    · exfalso
      have hdeleted := cap.openGraph_edge_not_mem_removed openEdge.2
      apply hdeleted
      have hvalue : openEdge.1 = (cap.cycleEdge (cap.cycleMate step)).1 := by
        exact congrArg Subtype.val hcycle
      simpa [hvalue] using cap.cycleEdge_mem_removed (cap.cycleMate step)
    · apply Subtype.ext
      change openEdge.1 = (cap.openSpokeEdge step).1
      simpa [openSpokeEdge_val] using congrArg Subtype.val hspoke
  · intro hopenSpoke
    subst openEdge
    simpa [openSpokeEdge_val] using cap.spokeEdge_incident step

/-- Every named cap stub has degree one in the literal opening. -/
theorem openGraph_incidentEdgeFinset_card_capVertex_eq_one
    (cap : PentagonCap G) (step : Fin 5) :
    (incidentEdgeFinset cap.openGraph (cap.vertex step)).card = 1 := by
  rw [cap.openGraph_incidentEdgeFinset_capVertex_eq_singleton step]
  simp

/-- The cap opening supplies the inner-degree part of the Cell--3 annular
boundary contract by construction. -/
theorem innerBoundaryData_inner_stub_degree_one
    (cap : PentagonCap G) (step : Fin 5) :
    (incidentEdgeFinset cap.openGraph
      ((cap.innerBoundaryData).innerStub step)).card = 1 := by
  exact cap.openGraph_incidentEdgeFinset_card_capVertex_eq_one step

end PentagonCap

end

end GoertzelV24PentagonCapOpening

end Mettapedia.GraphTheory.FourColor
