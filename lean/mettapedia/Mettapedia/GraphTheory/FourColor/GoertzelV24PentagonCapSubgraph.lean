import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapOpening

/-!
# L1: restrict a literal pentagon cap to a subgraph

A pentagon-cap datum survives passage to a subgraph when all five cycle
edges and all five spokes survive.  This module performs that dependent
edge-subtype transport and proves the local incidence equation in the
smaller graph.

The construction is generic graph plumbing.  It does not select a cap or
assert that a particular deletion preserves its edges.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PentagonCapSubgraph

open GoertzelV24PentagonCapOpening
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

noncomputable section

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  Fintype.ofFinite _

local instance subgraphEdgeSetFintype : Fintype H.edgeSet :=
  Fintype.ofFinite _

namespace PentagonCap

/-- Restrict a literal pentagon cap to a subgraph containing all ten of its
named edges. -/
def restrictToSubgraph
    (cap : PentagonCap G) (hle : H ≤ G)
    (hcycle : ∀ step : Fin 5, (cap.cycleEdge step).1 ∈ H.edgeSet)
    (hspoke : ∀ step : Fin 5, (cap.spokeEdge step).1 ∈ H.edgeSet) :
    PentagonCap H where
  vertex := cap.vertex
  cycleEdge :=
    ⟨fun step => ⟨(cap.cycleEdge step).1, hcycle step⟩, by
      intro first second heq
      apply cap.cycleEdge.injective
      apply Subtype.ext
      exact congrArg (fun edge : H.edgeSet => edge.1) heq⟩
  spokeEdge :=
    ⟨fun step => ⟨(cap.spokeEdge step).1, hspoke step⟩, by
      intro first second heq
      apply cap.spokeEdge.injective
      apply Subtype.ext
      exact congrArg (fun edge : H.edgeSet => edge.1) heq⟩
  spokeOuter := cap.spokeOuter
  cycleMate := cap.cycleMate
  cycleMate_noFixed := cap.cycleMate_noFixed
  cycle_spoke_ne := by
    intro cycle spoke heq
    apply cap.cycle_spoke_ne cycle spoke
    apply Subtype.ext
    exact congrArg (fun edge : H.edgeSet => edge.1) heq
  spokeEdge_eq := cap.spokeEdge_eq
  spokeOuter_ne_vertex := cap.spokeOuter_ne_vertex
  cycleEdge_endpoint_eq_vertex := cap.cycleEdge_endpoint_eq_vertex
  incident_eq := by
    intro step
    ext edge
    let ambientEdge : G.edgeSet :=
      ⟨edge.1, SimpleGraph.edgeSet_mono hle edge.2⟩
    constructor
    · intro hedge
      have hambient : ambientEdge ∈
          incidentEdgeFinset G (cap.vertex step) := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hedge).2⟩
      rw [cap.incident_eq step] at hambient
      simp only [Finset.mem_insert, Finset.mem_singleton] at hambient ⊢
      rcases hambient with hfirst | hsecond | hspoke
      · apply Or.inl
        apply Subtype.ext
        simpa [ambientEdge] using
          congrArg (fun named : G.edgeSet => named.1) hfirst
      · apply Or.inr
        apply Or.inl
        apply Subtype.ext
        simpa [ambientEdge] using
          congrArg (fun named : G.edgeSet => named.1) hsecond
      · apply Or.inr
        apply Or.inr
        apply Subtype.ext
        simpa [ambientEdge] using
          congrArg (fun named : G.edgeSet => named.1) hspoke
    · intro hedge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
      rcases hedge with hfirst | hsecond | hspokeEq
      · subst edge
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact (Finset.mem_filter.mp (by
          rw [cap.incident_eq step]
          simp : cap.cycleEdge step ∈
            incidentEdgeFinset G (cap.vertex step))).2
      · subst edge
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact (Finset.mem_filter.mp (by
          rw [cap.incident_eq step]
          simp : cap.cycleEdge (cap.cycleMate step) ∈
            incidentEdgeFinset G (cap.vertex step))).2
      · subst edge
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact (Finset.mem_filter.mp (by
          rw [cap.incident_eq step]
          simp : cap.spokeEdge step ∈
            incidentEdgeFinset G (cap.vertex step))).2

omit [DecidableRel G.Adj] [DecidableRel H.Adj] in
@[simp]
theorem restrictToSubgraph_vertex
    (cap : PentagonCap G) (hle : H ≤ G)
    (hcycle : ∀ step : Fin 5, (cap.cycleEdge step).1 ∈ H.edgeSet)
    (hspoke : ∀ step : Fin 5, (cap.spokeEdge step).1 ∈ H.edgeSet)
    (step : Fin 5) :
    (restrictToSubgraph cap hle hcycle hspoke).vertex step = cap.vertex step :=
  rfl

omit [DecidableRel G.Adj] [DecidableRel H.Adj] in
@[simp]
theorem restrictToSubgraph_cycleEdge_val
    (cap : PentagonCap G) (hle : H ≤ G)
    (hcycle : ∀ step : Fin 5, (cap.cycleEdge step).1 ∈ H.edgeSet)
    (hspoke : ∀ step : Fin 5, (cap.spokeEdge step).1 ∈ H.edgeSet)
    (step : Fin 5) :
    ((restrictToSubgraph cap hle hcycle hspoke).cycleEdge step).1 =
      (cap.cycleEdge step).1 :=
  rfl

omit [DecidableRel G.Adj] [DecidableRel H.Adj] in
@[simp]
theorem restrictToSubgraph_spokeEdge_val
    (cap : PentagonCap G) (hle : H ≤ G)
    (hcycle : ∀ step : Fin 5, (cap.cycleEdge step).1 ∈ H.edgeSet)
    (hspoke : ∀ step : Fin 5, (cap.spokeEdge step).1 ∈ H.edgeSet)
    (step : Fin 5) :
    ((restrictToSubgraph cap hle hcycle hspoke).spokeEdge step).1 =
      (cap.spokeEdge step).1 :=
  rfl

end PentagonCap

end


end GoertzelV24PentagonCapSubgraph

end Mettapedia.GraphTheory.FourColor
