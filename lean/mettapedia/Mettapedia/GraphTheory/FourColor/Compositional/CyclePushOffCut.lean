import Mettapedia.GraphTheory.Embedding.FaceCutCycleVertexSide
import Mettapedia.GraphTheory.FourColor.CyclicEdgeCut
import Mettapedia.GraphTheory.FourColor.IncidentEdgeFinset

/-!
# The edge cut obtained by pushing a primal cycle to one face side

The exact face cut of a simple primal cycle canonically determines a filled
vertex side.  This module records the graph-theoretic boundary of that side.
Every crossing edge is off the original cycle and is incident to a cycle
vertex; edges wholly away from the cycle preserve the side by exact face-cut
transport.

This is the semantic bridge from a face separator to a physical transversal.
It contains no reducibility or configuration data.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.CyclePushOffCut

open Mettapedia.GraphTheory.Embedding
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The finite physical edge boundary obtained from one selected facial side
of an exact cycle cut. -/
def edges
    (data : Data G) {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) : Finset G.edgeSet :=
  by
    classical
    exact Finset.univ.filter
      (EdgeCrossesVertexSide G (cut.filledCycleSide data cycle selected))

@[simp]
theorem mem_edges_iff
    (data : Data G) {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) (edge : G.edgeSet) :
    edge ∈ edges data cycle cut selected ↔
      EdgeCrossesVertexSide G
        (cut.filledCycleSide data cycle selected) edge := by
  simp [edges]

/-- An edge of the original cycle cannot cross the filled side, because both
of its endpoints are filled into that side. -/
theorem not_edgeCrosses_filledCycleSide_of_mem_cycle_edges
    (data : Data G) {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) (edge : G.edgeSet)
    (hedge : edge.1 ∈ cycle.edges) :
    ¬EdgeCrossesVertexSide G
      (cut.filledCycleSide data cycle selected) edge := by
  rw [not_edgeCrossesVertexSide_iff_forall_side_iff]
  intro first second hfirst hsecond
  have hfirstSupport : first ∈ cycle.support :=
    cycle.mem_support_of_mem_edges hedge hfirst
  have hsecondSupport : second ∈ cycle.support :=
    cycle.mem_support_of_mem_edges hedge hsecond
  constructor <;> intro _
  · exact cut.mem_filledCycleSide_of_mem_support data cycle selected
      hsecondSupport
  · exact cut.mem_filledCycleSide_of_mem_support data cycle selected
      hfirstSupport

/-- Every edge crossing the filled cycle side is incident to the original
cycle.  If both endpoints were off the cycle, exact face-cut transport along
that edge would put them on the same side. -/
theorem exists_cycle_endpoint_of_edgeCrosses_filledCycleSide
    (data : Data G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G
      (cut.filledCycleSide data cycle selected) edge) :
    ∃ vertex : V, vertex ∈ (edge : Sym2 V) ∧ vertex ∈ cycle.support := by
  by_contra hnone
  push Not at hnone
  have hnotCross : ¬EdgeCrossesVertexSide G
      (cut.filledCycleSide data cycle selected) edge := by
    rintro ⟨first, second, hfirst, hsecond, hfirstSide, hsecondSide⟩
    have hne : first ≠ second := by
      intro heq
      exact hsecondSide (heq ▸ hfirstSide)
    have hedgePair : (edge : Sym2 V) = s(first, second) :=
      (Sym2.mem_and_mem_iff hne).1 ⟨hfirst, hsecond⟩
    have hadj : G.Adj first second := by
      rw [← G.mem_edgeSet, ← hedgePair]
      exact edge.property
    let dart : G.Dart := ⟨(first, second), hadj⟩
    have hfirstOff : data.toRotationSystem.vertOf dart ∉ cycle.support := by
      simpa [dart] using hnone first hfirst
    have hsecondOff : data.toRotationSystem.vertOf
        (data.toRotationSystem.alpha dart) ∉ cycle.support := by
      simpa [dart] using hnone second hsecond
    have hpreserve :=
      cut.filledCycleSide_iff_of_edge_endpoints_not_mem_support
        data hrotation cycle selected dart hfirstOff hsecondOff
    have hpreserve' :
        cut.filledCycleSide data cycle selected first ↔
          cut.filledCycleSide data cycle selected second := by
      simpa [dart] using hpreserve
    exact hsecondSide (hpreserve'.1 hfirstSide)
  exact hnotCross hcross

/-- A physical push-off edge is an off-cycle attachment at a cycle vertex.
This is the exact support statement needed before bounding the transversal
width by local degree. -/
theorem mem_edges_implies_off_cycle_and_incident
    (data : Data G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) (edge : G.edgeSet)
    (hedge : edge ∈ edges data cycle cut selected) :
    edge.1 ∉ cycle.edges ∧
      ∃ vertex : V, vertex ∈ (edge : Sym2 V) ∧ vertex ∈ cycle.support := by
  have hcross := (mem_edges_iff data cycle cut selected edge).1 hedge
  constructor
  · intro hcycleEdge
    exact (not_edgeCrosses_filledCycleSide_of_mem_cycle_edges
      data cycle cut selected edge hcycleEdge) hcross
  · exact exists_cycle_endpoint_of_edgeCrosses_filledCycleSide
      data hrotation cycle cut selected edge hcross

/-- If every vertex of the cycle has at most `degreeBound` incident edges,
the pushed-off transversal has width at most the number of cycle vertices
times `degreeBound`.  This deliberately uses a robust incidence-union bound;
a later cubic refinement can improve the factor from three to one by using
the two cycle edges already consumed at each cycle vertex. -/
theorem card_edges_le_support_mul_degreeBound
    (data : Data G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) (degreeBound : Nat)
    (hdegree : ∀ vertex ∈ cycle.support.toFinset,
      (incidentEdgeFinset G vertex).card ≤ degreeBound) :
    (edges data cycle cut selected).card ≤
      cycle.support.toFinset.card * degreeBound := by
  let incidentCarrier : Finset G.edgeSet :=
    cycle.support.toFinset.biUnion (incidentEdgeFinset G)
  have hsubset : edges data cycle cut selected ⊆ incidentCarrier := by
    intro edge hedge
    rcases (mem_edges_implies_off_cycle_and_incident
        data hrotation cycle cut selected edge hedge).2 with
      ⟨vertex, hvertexEdge, hvertexCycle⟩
    apply Finset.mem_biUnion.2
    refine ⟨vertex, List.mem_toFinset.2 hvertexCycle, ?_⟩
    simp [incidentEdgeFinset, hvertexEdge]
  calc
    (edges data cycle cut selected).card ≤ incidentCarrier.card :=
      Finset.card_le_card hsubset
    _ ≤ cycle.support.toFinset.card * degreeBound :=
      Finset.card_biUnion_le_card_mul _ _ _ hdegree

/-- The filled side contains the original simple cycle. -/
theorem hasCycleOnSide_filledCycleSide
    (data : Data G) {base : V} (cycle : G.Walk base base)
    (hcycle : cycle.IsCycle)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) :
    HasCycleOnSide G (cut.filledCycleSide data cycle selected) := by
  refine ⟨base, ?_, cycle, hcycle, ?_⟩
  · exact cut.mem_filledCycleSide_of_mem_support data cycle selected (by simp)
  · intro vertex hvertex
    exact cut.mem_filledCycleSide_of_mem_support data cycle selected hvertex

/-- The pushed-off interface is a cyclic edge cut as soon as the opposite
filled side contains a cycle.  All edge-classification and the positive-side
cycle are already canonical; the single hypothesis is precisely the
remaining geometric content. -/
def cyclicEdgeCutRealization_of_complement_cycle
    (data : Data G) {base : V} (cycle : G.Walk base base)
    (hcycle : cycle.IsCycle)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2)
    (hcomplement : HasCycleOnSide G
      (fun vertex => ¬cut.filledCycleSide data cycle selected vertex)) :
    CyclicEdgeCutRealization G (edges data cycle cut selected) where
  side := cut.filledCycleSide data cycle selected
  hcut_eq := mem_edges_iff data cycle cut selected
  hinside_cycle := hasCycleOnSide_filledCycleSide
    data cycle hcycle cut selected
  houtside_cycle := hcomplement

end

end Mettapedia.GraphTheory.FourColor.Compositional.CyclePushOffCut
