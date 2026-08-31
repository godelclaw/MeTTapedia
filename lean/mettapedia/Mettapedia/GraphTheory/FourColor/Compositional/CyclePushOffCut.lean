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

/-- A walk disjoint from the bounding cycle stays on one filled side.  This
is the pathwise form of the local off-cycle edge transport theorem. -/
theorem filledCycleSide_iff_of_walk_avoids_support
    (data : Data G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) {start finish : V} (walk : G.Walk start finish)
    (havoid : ∀ vertex ∈ walk.support, vertex ∉ cycle.support) :
    cut.filledCycleSide data cycle selected start ↔
      cut.filledCycleSide data cycle selected finish := by
  induction walk with
  | nil => exact Iff.rfl
  | @cons current next finish hadj tail ih =>
      let dart : G.Dart := ⟨(current, next), hadj⟩
      have hcurrent : data.toRotationSystem.vertOf dart ∉ cycle.support := by
        simpa [dart] using havoid current (by simp)
      have hnext : data.toRotationSystem.vertOf
          (data.toRotationSystem.alpha dart) ∉ cycle.support := by
        simpa [dart] using havoid next (by simp)
      have hstep :=
        cut.filledCycleSide_iff_of_edge_endpoints_not_mem_support
          data hrotation cycle selected dart hcurrent hnext
      have hstep' :
          cut.filledCycleSide data cycle selected current ↔
            cut.filledCycleSide data cycle selected next := by
        simpa [dart] using hstep
      have htail : ∀ vertex ∈ tail.support, vertex ∉ cycle.support := by
        intro vertex hvertex
        exact havoid vertex (by simp [hvertex])
      exact hstep'.trans (ih htail)

/-- A simple cycle disjoint from the bounding cycle lies wholly on one of
the two vertex sides determined by any selected exact-cut label.  No Jordan
curve theorem is used here: local exact-cut transport and a walk induction
give the dichotomy. -/
theorem hasCycleOnSide_or_complement_of_disjoint_cycle
    (data : Data G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    (selected : F2) {otherBase : V} (other : G.Walk otherBase otherBase)
    (hother : other.IsCycle)
    (hdisjoint : other.support.Disjoint cycle.support) :
    HasCycleOnSide G (cut.filledCycleSide data cycle selected) ∨
      HasCycleOnSide G
        (fun vertex => ¬cut.filledCycleSide data cycle selected vertex) := by
  have havoid : ∀ vertex ∈ other.support, vertex ∉ cycle.support := by
    intro vertex hvertex hcycle
    exact (List.disjoint_left.mp hdisjoint) hvertex hcycle
  by_cases hbaseSide : cut.filledCycleSide data cycle selected otherBase
  · left
    refine ⟨otherBase, hbaseSide, other, hother, ?_⟩
    intro vertex hvertex
    have hpathAvoid : ∀ point ∈ (other.takeUntil vertex hvertex).support,
        point ∉ cycle.support := by
      intro point hpoint
      exact havoid point (other.support_takeUntil_subset_support hvertex hpoint)
    exact (filledCycleSide_iff_of_walk_avoids_support data hrotation cycle cut
      selected (other.takeUntil vertex hvertex) hpathAvoid).1 hbaseSide
  · right
    refine ⟨otherBase, hbaseSide, other, hother, ?_⟩
    intro vertex hvertex hvertexSide
    have hpathAvoid : ∀ point ∈ (other.takeUntil vertex hvertex).support,
        point ∉ cycle.support := by
      intro point hpoint
      exact havoid point (other.support_takeUntil_subset_support hvertex hpoint)
    exact hbaseSide
      ((filledCycleSide_iff_of_walk_avoids_support data hrotation cycle cut
        selected (other.takeUntil vertex hvertex) hpathAvoid).2 hvertexSide)

/-- A cycle disjoint from the bounding cycle canonically supplies the
opposite-side witness needed for a cyclic edge cut.  Read the exact-cut label
at the disjoint cycle's first dart and select the other binary label.  The
base vertex is then outside the filled side, and local transport propagates
that fact around the whole cycle. -/
theorem exists_selected_with_complement_cycle_of_disjoint_cycle
    (data : Data G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {base : V} (cycle : G.Walk base base)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈ cycle.edges) F2)
    {otherBase : V} (other : G.Walk otherBase otherBase)
    (hother : other.IsCycle)
    (hdisjoint : other.support.Disjoint cycle.support) :
    ∃ selected : F2,
      HasCycleOnSide G
        (fun vertex =>
          ¬cut.filledCycleSide data cycle selected vertex) := by
  let dart : data.toRotationSystem.D := other.firstDart hother.not_nil
  let selected : F2 :=
    cut.label (dartOrbitFace data.toRotationSystem dart) + 1
  have havoid : ∀ vertex ∈ other.support, vertex ∉ cycle.support := by
    intro vertex hvertex hcycle
    exact (List.disjoint_left.mp hdisjoint) hvertex hcycle
  have hbaseOff : data.toRotationSystem.vertOf dart ∉ cycle.support := by
    simpa [dart] using havoid otherBase (by simp)
  have hlabelNe :
      cut.label (dartOrbitFace data.toRotationSystem dart) ≠ selected := by
    dsimp only [selected]
    intro heq
    generalize cut.label (dartOrbitFace data.toRotationSystem dart) = label at heq
    fin_cases label <;> simp at heq
  have hbaseOutside :
      ¬cut.filledCycleSide data cycle selected otherBase := by
    have hread := cut.filledCycleSide_iff_label_of_not_mem_support
      data hrotation cycle selected dart hbaseOff
    simpa [dart] using (fun hside => hlabelNe (hread.mp hside))
  refine ⟨selected, otherBase, hbaseOutside, other, hother, ?_⟩
  intro vertex hvertex hvertexSide
  have hpathAvoid : ∀ point ∈ (other.takeUntil vertex hvertex).support,
      point ∉ cycle.support := by
    intro point hpoint
    exact havoid point (other.support_takeUntil_subset_support hvertex hpoint)
  exact hbaseOutside
    ((filledCycleSide_iff_of_walk_avoids_support data hrotation cycle cut
      selected (other.takeUntil vertex hvertex) hpathAvoid).2 hvertexSide)

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
