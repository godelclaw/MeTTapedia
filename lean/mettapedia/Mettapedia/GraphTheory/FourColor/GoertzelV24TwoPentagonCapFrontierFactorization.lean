import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpening
import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapSubgraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpening

/-!
# L1: factor a two-cap opening through an Addendum-V frontier

For a separated pair of pentagon caps, open the outer cap first.  The result
is a literal frontier graph with five ordered outer stubs.  Separation proves
that all ten edges of the inner cap survive in that graph, so the inner cap
restricts to an actual interior `PentagonCap` of the frontier.

This constructs the intermediate carrier in the source's order

```
closed graph -> frontier with outer stubs -> annulus with inner and outer stubs.
```

It does not claim that every abstract Addendum-V frontier arises this way,
and it does not yet identify the second opening with the existing simultaneous
two-cap opening.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoPentagonCapFrontierFactorization

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FrontierPentagonCapOpening
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24PentagonCapOpening
open GoertzelV24PentagonCapOpeningWellFormed
open GoertzelV24PentagonCapSubgraph
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  Fintype.ofFinite _

namespace PentagonCapPair

local instance outerOpenGraphDecidableRel (caps : PentagonCapPair G) :
    DecidableRel caps.outer.openGraph.Adj :=
  Classical.decRel _

/-- An inner cap-cycle edge cannot be deleted by opening the disjoint outer
cap: both endpoints of the former lie in the inner cap vertex set. -/
theorem inner_cycleEdge_not_mem_outerCycleSupport
    (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.inner.cycleEdge step).1 ∉
      edgeFinsetValueSet caps.outer.cycleSupport := by
  intro hremoved
  rcases (mem_edgeFinsetValueSet_iff caps.outer.cycleSupport _).mp hremoved with
    ⟨outerEdge, houterEdge, hvalue⟩
  rcases Finset.mem_map.mp houterEdge with
    ⟨outerStep, -, houterStep⟩
  have hedge : (caps.outer.cycleEdge outerStep).1 =
      (caps.inner.cycleEdge step).1 := by
    calc
      (caps.outer.cycleEdge outerStep).1 = outerEdge.1 :=
        congrArg Subtype.val houterStep
      _ = (caps.inner.cycleEdge step).1 := hvalue
  have hinnerVertex : caps.inner.vertex step ∈
      (caps.outer.cycleEdge outerStep).1 := by
    rw [hedge]
    exact (Finset.mem_filter.mp (by
      rw [caps.inner.incident_eq step]
      simp : caps.inner.cycleEdge step ∈
        incidentEdgeFinset G (caps.inner.vertex step))).2
  rcases caps.outer.cycleEdge_endpoint_eq_vertex outerStep
      (caps.inner.vertex step) hinnerVertex with ⟨capStep, hcapStep⟩
  exact caps.inner_vertex_not_mem_outerSupport step
    ((caps.outer.mem_vertexSupport_iff _).mpr ⟨capStep, hcapStep⟩)

/-- Every inner cap-cycle edge survives the outer opening. -/
theorem inner_cycleEdge_mem_outerOpenGraph
    (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.inner.cycleEdge step).1 ∈ caps.outer.openGraph.edgeSet := by
  exact (caps.outer.mem_openGraph_edgeSet_iff
    (caps.inner.cycleEdge step).1 (caps.inner.cycleEdge step).2).mpr
      (inner_cycleEdge_not_mem_outerCycleSupport caps step)

/-- Every inner spoke survives the outer opening. -/
theorem inner_spokeEdge_mem_outerOpenGraph
    (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.inner.spokeEdge step).1 ∈ caps.outer.openGraph.edgeSet := by
  exact (caps.outer.mem_openGraph_edgeSet_iff
    (caps.inner.spokeEdge step).1 (caps.inner.spokeEdge step).2).mpr
      (caps.inner_spoke_not_mem_outerCycleSupport step)

/-- The inner cap transported as a literal cap of the outer-open frontier. -/
def innerInOuterOpenGraph (caps : PentagonCapPair G) :
    PentagonCap caps.outer.openGraph :=
  GoertzelV24PentagonCapSubgraph.PentagonCap.restrictToSubgraph caps.inner
    (SimpleGraph.deleteEdges_le
      (edgeFinsetValueSet caps.outer.cycleSupport))
    (inner_cycleEdge_mem_outerOpenGraph caps)
    (inner_spokeEdge_mem_outerOpenGraph caps)

@[simp]
theorem innerInOuterOpenGraph_vertex
    (caps : PentagonCapPair G) (step : Fin 5) :
    (innerInOuterOpenGraph caps).vertex step = caps.inner.vertex step :=
  rfl

@[simp]
theorem innerInOuterOpenGraph_cycleEdge_val
    (caps : PentagonCapPair G) (step : Fin 5) :
    ((innerInOuterOpenGraph caps).cycleEdge step).1 =
      (caps.inner.cycleEdge step).1 :=
  rfl

@[simp]
theorem innerInOuterOpenGraph_spokeEdge_val
    (caps : PentagonCapPair G) (step : Fin 5) :
    ((innerInOuterOpenGraph caps).spokeEdge step).1 =
      (caps.inner.spokeEdge step).1 :=
  rfl

/-- Opening the outer cap constructs the ordered outer-only boundary of the
intermediate frontier. -/
def outerFrontier (caps : PentagonCapPair G) :
    FrontierBoundaryData caps.outer.openGraph 5 where
  outerStub := caps.outer.vertex
  outerBoundaryEdge := caps.outer.openSpokeEmbedding

/-- A cubic closed carrier makes the intermediate outer-open frontier
well-formed. -/
theorem outerFrontier_wellFormed_of_isRegularOfDegree_three
    (caps : PentagonCapPair G) (hregular : G.IsRegularOfDegree 3) :
    (outerFrontier caps).WellFormed := by
  have hopen :=
    GoertzelV24PentagonCapOpeningWellFormed.PentagonCap.innerBoundaryData_wellFormed_of_isRegularOfDegree_three
      caps.outer hregular
  refine {
    outerBoundaryEdge_incident := ?_,
    outer_stub_degree_one := ?_,
    cubic_elsewhere := ?_ }
  · exact hopen.innerBoundaryEdge_incident
  · exact hopen.inner_stub_degree_one
  · intro vertex houter
    exact hopen.cubic_elsewhere vertex houter (fun impossible => Fin.elim0 impossible)

/-- The transported inner cap is interior to the constructed frontier: its
vertices miss the outer stubs and its spokes miss the outer boundary edges. -/
theorem innerInOuterOpenGraph_interior
    (caps : PentagonCapPair G) :
    (outerFrontier caps).InteriorPentagonCap (innerInOuterOpenGraph caps) := by
  refine {
    capVertex_ne_outerStub := ?_,
    spokeEdge_ne_outerBoundaryEdge := ?_ }
  · intro innerStep outerStep heq
    exact caps.inner_vertex_not_mem_outerSupport innerStep
      ((caps.outer.mem_vertexSupport_iff _).mpr ⟨outerStep, heq.symm⟩)
  · intro innerStep outerStep heq
    apply caps.innerOpenSpokeEdge_ne_outerOpenSpokeEdge innerStep outerStep
    apply Subtype.ext
    simpa [outerFrontier, PentagonCap.openSpokeEmbedding,
      PentagonCap.openSpokeEdge_val] using congrArg
        (fun edge : caps.outer.openGraph.edgeSet => edge.1) heq

end PentagonCapPair

end


end GoertzelV24TwoPentagonCapFrontierFactorization

end Mettapedia.GraphTheory.FourColor
