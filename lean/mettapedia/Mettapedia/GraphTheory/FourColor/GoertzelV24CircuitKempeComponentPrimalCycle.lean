import Mettapedia.GraphTheory.FourColor.GoertzelV24DegreeTwoBoundaryKempeLiftClassification
import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCoherentCircuitExtraction
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Primal cycles carried by circuit-shaped Kempe components

A circuit-shaped two-colour component is defined in the line graph: its
selected edges form a connected 2-regular graph.  This file supplies the
geometric bridge needed by the compositional route.  A simple cycle in that
component is primal-coherent because proper edge colouring forbids two
same-coloured edges from meeting at one primal vertex.  The canonical primal
lift therefore contains a genuine simple cycle of the original graph, and
every edge of that cycle belongs to the selected Kempe component.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CircuitKempeComponentPrimalCycle

open SimpleGraph
open SimpleGraph.Walk
open GoertzelV24FourDefectBoundary
open GoertzelV24FramedTrail

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

/-- A simple closed line-graph walk using only two colours is
primal-coherent.  The internal and closing cases are the same local fact:
the two edges on either side of the middle edge have the same selected
colour, so properness prevents them from sharing the same primal endpoint. -/
theorem isPrimalCoherentClosed_of_isCycle_of_bicolored
    (C : G.EdgeColoring Color) {a b : Color} {edge : G.edgeSet}
    (walk : G.lineGraph.Walk edge edge) (hcycle : walk.IsCycle)
    (hcolors : ∀ current ∈ walk.support,
      C current = a ∨ C current = b) :
    walk.IsPrimalCoherentClosed := by
  have hthree : 3 ≤ walk.length := hcycle.three_le_length
  constructor
  · intro position hposition
    let previousEdge : G.edgeSet := walk.getVert position
    let middleEdge : G.edgeSet := walk.getVert (position + 1)
    let nextEdge : G.edgeSet := walk.getVert (position + 2)
    have hpreviousMiddle : G.lineGraph.Adj previousEdge middleEdge := by
      exact walk.adj_getVert_succ (by omega)
    have hmiddleNext : G.lineGraph.Adj middleEdge nextEdge := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        walk.adj_getVert_succ (i := position + 1) hposition
    have hpreviousColor :=
      hcolors previousEdge (walk.getVert_mem_support position)
    have hmiddleColor :=
      hcolors middleEdge (walk.getVert_mem_support (position + 1))
    have hnextColor :=
      hcolors nextEdge (walk.getVert_mem_support (position + 2))
    have hpreviousMiddleColor : C previousEdge ≠ C middleEdge :=
      C.valid hpreviousMiddle
    have hmiddleNextColor : C middleEdge ≠ C nextEdge :=
      C.valid hmiddleNext
    have hpreviousNextColor : C previousEdge = C nextEdge := by
      rcases hpreviousColor with hpa | hpb <;>
        rcases hmiddleColor with hma | hmb <;>
        rcases hnextColor with hna | hnb
      all_goals aesop
    have hpreviousNext : previousEdge ≠ nextEdge := by
      intro hedge
      by_cases hbefore : position + 2 ≤ walk.length - 1
      · have hindices := hcycle.getVert_injOn'
          (show position ∈ {index | index ≤ walk.length - 1} by
            simp only [Set.mem_setOf_eq]
            omega)
          (show position + 2 ∈ {index | index ≤ walk.length - 1} by
            simpa only [Set.mem_setOf_eq] using hbefore)
          hedge
        omega
      · have hlast : position + 2 = walk.length := by omega
        have hpreviousFirst : walk.getVert position = walk.getVert 0 := by
          calc
            walk.getVert position = walk.getVert (position + 2) := hedge
            _ = walk.getVert walk.length := by rw [hlast]
            _ = walk.getVert 0 := by simp
        have hindices := hcycle.getVert_injOn'
          (show position ∈ {index | index ≤ walk.length - 1} by
            simp only [Set.mem_setOf_eq]
            omega)
          (show 0 ∈ {index | index ≤ walk.length - 1} by
            simp only [Set.mem_setOf_eq]
            omega)
          hpreviousFirst
        omega
    intro hjunction
    have hpreviousMem :
        walk.lineGraphJunctionAt ⟨position, by omega⟩ ∈
          (previousEdge.1 : Sym2 V) :=
      walk.lineGraphJunctionAt_mem_left ⟨position, by omega⟩
    have hnextMem :
        walk.lineGraphJunctionAt ⟨position, by omega⟩ ∈
          (nextEdge.1 : Sym2 V) := by
      rw [hjunction]
      exact walk.lineGraphJunctionAt_mem_right
        ⟨position + 1, hposition⟩
    have hpreviousNextAdj : G.lineGraph.Adj previousEdge nextEdge :=
      (SimpleGraph.lineGraph_adj_iff_exists).2
        ⟨hpreviousNext,
          walk.lineGraphJunctionAt ⟨position, by omega⟩,
          hpreviousMem, hnextMem⟩
    exact C.valid hpreviousNextAdj hpreviousNextColor
  · intro hpositive
    let previousEdge : G.edgeSet := walk.getVert (walk.length - 1)
    let middleEdge : G.edgeSet := walk.getVert walk.length
    let nextEdge : G.edgeSet := walk.getVert 1
    have hpreviousMiddle : G.lineGraph.Adj previousEdge middleEdge := by
      simpa only [previousEdge, middleEdge,
        Nat.sub_add_cancel (by omega : 1 ≤ walk.length)] using
          walk.adj_getVert_succ (i := walk.length - 1) (by omega)
    have hmiddleNext : G.lineGraph.Adj middleEdge nextEdge := by
      simpa only [middleEdge, nextEdge, walk.getVert_length,
        walk.getVert_zero, Nat.zero_add] using
        walk.adj_getVert_succ (i := 0) (by omega)
    have hpreviousColor := hcolors previousEdge
      (walk.getVert_mem_support (walk.length - 1))
    have hmiddleColor := hcolors middleEdge
      (walk.getVert_mem_support walk.length)
    have hnextColor := hcolors nextEdge (walk.getVert_mem_support 1)
    have hpreviousMiddleColor : C previousEdge ≠ C middleEdge :=
      C.valid hpreviousMiddle
    have hmiddleNextColor : C middleEdge ≠ C nextEdge :=
      C.valid hmiddleNext
    have hpreviousNextColor : C previousEdge = C nextEdge := by
      rcases hpreviousColor with hpa | hpb <;>
        rcases hmiddleColor with hma | hmb <;>
        rcases hnextColor with hna | hnb
      all_goals aesop
    have hpreviousNext : previousEdge ≠ nextEdge := by
      intro hedge
      have hindices := hcycle.getVert_injOn'
        (show walk.length - 1 ∈
            {index | index ≤ walk.length - 1} by simp)
        (show 1 ∈ {index | index ≤ walk.length - 1} by
          simp only [Set.mem_setOf_eq]
          omega)
        hedge
      omega
    intro hjunction
    let finalPosition : Fin walk.length :=
      ⟨walk.length - 1, Nat.sub_lt hpositive Nat.zero_lt_one⟩
    let firstPosition : Fin walk.length := ⟨0, hpositive⟩
    have hpreviousMem :
        walk.lineGraphJunctionAt finalPosition ∈
          (previousEdge.1 : Sym2 V) :=
      walk.lineGraphJunctionAt_mem_left finalPosition
    have hnextMem :
        walk.lineGraphJunctionAt finalPosition ∈
          (nextEdge.1 : Sym2 V) := by
      rw [hjunction]
      exact walk.lineGraphJunctionAt_mem_right firstPosition
    have hpreviousNextAdj : G.lineGraph.Adj previousEdge nextEdge :=
      (SimpleGraph.lineGraph_adj_iff_exists).2
        ⟨hpreviousNext, walk.lineGraphJunctionAt finalPosition,
          hpreviousMem, hnextMem⟩
    exact C.valid hpreviousNextAdj hpreviousNextColor

/-- A circuit-shaped selected component carries a genuine primal simple
cycle.  Every edge of the output cycle remains in that exact Kempe component;
the construction does not merely find an unrelated cycle elsewhere in the
graph. -/
theorem exists_primalCycle_of_isCircuitKempeComponent
    (C : G.EdgeColoring Color) {a b : Color}
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hcircuit : IsCircuitKempeComponent C a b K) :
    ∃ (start : V) (cycle : G.Walk start start),
      cycle.IsCycle ∧
        ∀ edge : G.edgeSet, edge.1 ∈ cycle.edges →
          edge ∈ C.kempeComponentSet a b K := by
  classical
  let componentGraph := K.toSimpleGraph
  have hcycles : componentGraph.IsCycles := by
    intro edge _hneighbors
    exact hcircuit edge
  rcases K.nonempty_supp with ⟨root, hroot⟩
  let rootInComponent : K := ⟨root, hroot⟩
  have hrootNeighbors :
      (componentGraph.neighborSet rootInComponent).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hcircuit rootInComponent]
    norm_num
  rcases hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := componentGraph.connectedComponentMk rootInComponent)
      (v := rootInComponent) rfl hrootNeighbors with
    ⟨componentCycle, hcomponentCycle, _hcomponentSupport⟩
  let selectedCycle :=
    (componentCycle.map K.toSimpleGraph_hom).copy rfl rfl
  have hselectedCycle : selectedCycle.IsCycle := by
    simpa only [selectedCycle, SimpleGraph.Walk.isCycle_copy] using
      hcomponentCycle.map Subtype.val_injective
  let inclusion :=
    (SimpleGraph.Embedding.induce (G := G.lineGraph)
      (C.bicoloredSet a b)).toHom
  let ambientCycle := (selectedCycle.map inclusion).copy rfl rfl
  have hambientCycle : ambientCycle.IsCycle := by
    simpa only [ambientCycle, SimpleGraph.Walk.isCycle_copy] using
      hselectedCycle.map
        (SimpleGraph.Embedding.induce (G := G.lineGraph)
          (C.bicoloredSet a b)).injective
  have hambientColors : ∀ edge ∈ ambientCycle.support,
      C edge = a ∨ C edge = b := by
    intro edge hedge
    simp only [ambientCycle, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map] at hedge
    rcases List.mem_map.1 hedge with ⟨selectedEdge, _hselected, rfl⟩
    exact selectedEdge.2
  have hcoherent : ambientCycle.IsPrimalCoherentClosed :=
    isPrimalCoherentClosed_of_isCycle_of_bicolored
      C ambientCycle hambientCycle hambientColors
  have hpositive : 0 < ambientCycle.length := by
    have := hambientCycle.three_le_length
    omega
  rcases
      ambientCycle.exists_primal_isCycle_length_le_edges_subset_of_primalCoherentClosed
        hpositive hcoherent with
    ⟨start, cycle, hcycle, _hlength, hedgeSubset⟩
  refine ⟨start, cycle, hcycle, ?_⟩
  intro edge hedge
  have hlineEdge : edge.1 ∈
      ambientCycle.support.tail.map Subtype.val := hedgeSubset hedge
  rcases List.mem_map.1 hlineEdge with
    ⟨ambientEdge, hambientTail, hambientValue⟩
  have hambientSupport : ambientEdge ∈ ambientCycle.support :=
    List.mem_of_mem_tail hambientTail
  simp only [ambientCycle, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_map] at hambientSupport
  rcases List.mem_map.1 hambientSupport with
    ⟨selectedEdge, hselectedSupport, hselectedValue⟩
  simp only [selectedCycle, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_map] at hselectedSupport
  rcases List.mem_map.1 hselectedSupport with
    ⟨componentEdge, _hcomponentSupport, hcomponentValue⟩
  subst selectedEdge
  subst ambientEdge
  change (componentEdge.1.1 : Sym2 V) = edge.1 at hambientValue
  have hedgeValue : componentEdge.1.1 = edge := by
    apply Subtype.ext
    exact hambientValue
  subst edge
  exact ⟨componentEdge.1.2, componentEdge.2⟩

end

end GoertzelV24CircuitKempeComponentPrimalCycle

end Mettapedia.GraphTheory.FourColor
