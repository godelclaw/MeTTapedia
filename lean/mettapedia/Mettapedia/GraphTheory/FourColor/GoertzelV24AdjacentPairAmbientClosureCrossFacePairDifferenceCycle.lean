import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceProfile
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance supportCycleGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A color chain whose zero edges are exactly the nonzero support of a
binary edge chain. -/
def scalarSupportComplementChain (f : G.edgeSet → F2) : G.edgeSet → Color :=
  fun edge => if f edge = 0 then red else 0

/-- The spanning subgraph consisting exactly of the nonzero support of a
binary edge chain. -/
abbrev scalarSupportGraph (f : G.edgeSet → F2) : SimpleGraph V :=
  zeroEdgeGraph G (scalarSupportComplementChain f)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem scalarSupportComplementChain_eq_zero_iff
    (f : G.edgeSet → F2) (edge : G.edgeSet) :
    scalarSupportComplementChain f edge = 0 ↔ f edge ≠ 0 := by
  by_cases h : f edge = 0
  · simp [scalarSupportComplementChain, h, red]
  · simp [scalarSupportComplementChain, h]

omit [DecidableEq V] in
@[simp]
theorem ambientEdge_mem_scalarSupportGraph_edgeSet_iff
    (f : G.edgeSet → F2) (edge : G.edgeSet) :
    (edge : Sym2 V) ∈ (scalarSupportGraph f).edgeSet ↔ f edge ≠ 0 := by
  rw [zeroEdgeGraph_edgeSet]
  simp [zeroEdgeSym2Finset, zeroEdgeFinset]

theorem scalarSupportGraph_incidentEdgeFinset_card
    (f : G.edgeSet → F2) (vertex : V) :
    (incidentEdgeFinset (scalarSupportGraph f) vertex).card =
      ((incidentEdgeFinset G vertex).filter fun edge => f edge ≠ 0).card := by
  rw [zeroEdgeGraph_incidentEdgeFinset_card]
  simp only [zeroIncidentEdgeCount, zeroIncidentEdgeFinset]
  congr 1
  ext edge
  simp

omit [DecidableEq V] in
/-- The scalar support graph uses only edges of the ambient graph. -/
theorem scalarSupportGraph_le (f : G.edgeSet → F2) :
    scalarSupportGraph f ≤ G := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet]
  intro edge hedge
  rw [zeroEdgeGraph_edgeSet] at hedge
  rw [zeroEdgeSym2Finset] at hedge
  rcases Finset.mem_map.mp hedge with ⟨ambient, _hzero, rfl⟩
  exact ambient.2

private theorem f2_eq_zero_or_one (value : F2) :
    value = 0 ∨ value = 1 := by
  fin_cases value
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

/-- A binary chain with zero total weight has even support. -/
theorem filter_ne_zero_card_even_of_f2_sum_eq_zero
    {E : Type*} [DecidableEq E] (edges : Finset E) (f : E → F2)
    (hsum : (∑ edge ∈ edges, f edge) = 0) :
    Even ((edges.filter fun edge => f edge ≠ 0).card) := by
  have hsumSupport :
      (∑ edge ∈ edges, f edge) =
        ∑ edge ∈ edges.filter (fun edge => f edge ≠ 0), f edge := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro edge _hedge
    by_cases hzero : f edge = 0 <;> simp [hzero]
  have hone : ∀ edge ∈ edges.filter (fun edge => f edge ≠ 0),
      f edge = 1 := by
    intro edge hedge
    have hne : f edge ≠ 0 := by simpa using (Finset.mem_filter.mp hedge).2
    exact (f2_eq_zero_or_one (f edge)).resolve_left hne
  have hsumCard :
      (∑ edge ∈ edges.filter (fun edge => f edge ≠ 0), f edge) =
        (((edges.filter fun edge => f edge ≠ 0).card : Nat) : F2) := by
    calc
      (∑ edge ∈ edges.filter (fun edge => f edge ≠ 0), f edge) =
          ∑ _edge ∈ edges.filter (fun edge => f edge ≠ 0), (1 : F2) := by
            apply Finset.sum_congr rfl
            intro edge hedge
            exact hone edge hedge
      _ = (((edges.filter fun edge => f edge ≠ 0).card : Nat) : F2) := by
        simp
  rw [hsumSupport, hsumCard] at hsum
  rw [even_iff_two_dvd]
  exact (ZMod.natCast_eq_zero_iff _ 2).mp hsum

/-- In a cubic graph, the support of a binary Kirchhoff flow is a disjoint
union of cycles. -/
theorem scalarSupportGraph_isCycles
    (f : G.edgeSet → F2)
    (hflow : ∀ vertex : V, scalarVertexKirchhoffSum G f vertex = 0)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    (scalarSupportGraph f).IsCycles := by
  intro vertex hnonempty
  have heven : Even
      (((incidentEdgeFinset G vertex).filter fun edge => f edge ≠ 0).card) := by
    apply filter_ne_zero_card_even_of_f2_sum_eq_zero
    exact hflow vertex
  have hle :
      ((incidentEdgeFinset G vertex).filter fun edge => f edge ≠ 0).card ≤ 3 := by
    calc
      ((incidentEdgeFinset G vertex).filter fun edge => f edge ≠ 0).card ≤
          (incidentEdgeFinset G vertex).card := Finset.card_filter_le _ _
      _ = 3 := hcubic vertex
  have hpositive :
      0 < ((incidentEdgeFinset G vertex).filter fun edge => f edge ≠ 0).card := by
    rw [← scalarSupportGraph_incidentEdgeFinset_card]
    rw [incidentEdgeFinset_card_eq_degree]
    exact SimpleGraph.degree_pos_iff_nonempty.mpr hnonempty
  have hcard :
      ((incidentEdgeFinset G vertex).filter fun edge => f edge ≠ 0).card = 2 := by
    rcases heven with ⟨k, hk⟩
    omega
  have hdegree : (scalarSupportGraph f).degree vertex = 2 := by
    rw [← incidentEdgeFinset_card_eq_degree,
      scalarSupportGraph_incidentEdgeFinset_card]
    exact hcard
  rw [Set.ncard_eq_toFinset_card']
  exact hdegree

/-- Every nonzero edge of a binary Kirchhoff flow on a finite cubic graph
lies on an ambient simple cycle entirely contained in that coordinate's
support. -/
theorem exists_isCycle_through_of_scalar_ne_zero
    (f : G.edgeSet → F2)
    (hflow : ∀ vertex : V, scalarVertexKirchhoffSum G f vertex = 0)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (edge : G.edgeSet) (hedge : f edge ≠ 0) :
    ∃ (root : V) (cycle : G.Walk root root),
      cycle.IsCycle ∧
        (edge : Sym2 V) ∈ cycle.edges ∧
        ∀ other : G.edgeSet,
          (other : Sym2 V) ∈ cycle.edges → f other ≠ 0 := by
  have hedgeSupport :
      (edge : Sym2 V) ∈ (scalarSupportGraph f).edgeSet :=
    (ambientEdge_mem_scalarSupportGraph_edgeSet_iff f edge).2 hedge
  rcases Sym2.mk_surjective (edge : Sym2 V) with ⟨⟨left, right⟩, hedgerepr⟩
  have hedgerepr' : s(left, right) = (edge : Sym2 V) := by
    exact hedgerepr
  have hadj : (scalarSupportGraph f).Adj left right := by
    exact (SimpleGraph.mem_edgeSet (G := scalarSupportGraph f)).mp
      (hedgerepr'.symm ▸ hedgeSupport)
  have hcycles := scalarSupportGraph_isCycles f hflow hcubic
  have hreachable := hcycles.reachable_deleteEdges hadj
  rcases SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
      ⟨hadj, hreachable⟩ with ⟨root, supportCycle, hcycle, hmem⟩
  let ambientCycle := supportCycle.mapLe (scalarSupportGraph_le f)
  refine ⟨root, ambientCycle, hcycle.mapLe (scalarSupportGraph_le f), ?_, ?_⟩
  · change (edge : Sym2 V) ∈
      (supportCycle.mapLe (scalarSupportGraph_le f)).edges
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
    exact hedgerepr' ▸ hmem
  · intro other hother
    have hotherSupport :
        (other : Sym2 V) ∈ (scalarSupportGraph f).edgeSet := by
      apply supportCycle.edges_subset_edgeSet
      change (other : Sym2 V) ∈
        (supportCycle.mapLe (scalarSupportGraph_le f)).edges at hother
      rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hother
      exact hother
    exact (ambientEdge_mem_scalarSupportGraph_edgeSet_iff f other).1
      hotherSupport

end

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24MinimalFaceIntersections
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Every nonzero edge of the cross-face difference profile lies on a
simple profile-support cycle that omits the retained cross. -/
theorem CrossCentralExactFaceCutPair.exists_difference_cycle_through_avoiding_retainedCross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (edge : G.edgeSet)
    (hedge : pair.crossFaceDifferenceProfile edge ≠ 0) :
    ∃ (root : V) (cycle : G.Walk root root),
      cycle.IsCycle ∧
        (edge : Sym2 V) ∈ cycle.edges ∧
        (retainedEdgeToAmbientEdge data cross : Sym2 V) ∉ cycle.edges := by
  let difference : G.edgeSet → Color := pair.crossFaceDifferenceProfile
  have hdifference : IsGraphFlow G difference :=
    pair.crossFaceDifferenceProfile_isGraphFlow minimal
  have hfirstFlow : ∀ vertex : V,
      scalarVertexKirchhoffSum G (fun edge => (difference edge).1) vertex = 0 := by
    intro vertex
    rw [scalarVertexKirchhoffSum_fst]
    have hzero := hdifference vertex
    exact congrArg Prod.fst hzero
  have hsecondFlow : ∀ vertex : V,
      scalarVertexKirchhoffSum G (fun edge => (difference edge).2) vertex = 0 := by
    intro vertex
    rw [scalarVertexKirchhoffSum_snd]
    have hzero := hdifference vertex
    exact congrArg Prod.snd hzero
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hcross : difference (retainedEdgeToAmbientEdge data cross) = 0 :=
    pair.crossFaceDifferenceProfile_retainedCross minimal
  have hedgeDifference : difference edge ≠ 0 := hedge
  by_cases hfirst : (difference edge).1 = 0
  · have hsecond : (difference edge).2 ≠ 0 := by
      intro hzero
      apply hedgeDifference
      exact Prod.ext hfirst hzero
    rcases exists_isCycle_through_of_scalar_ne_zero
        (fun edge => (difference edge).2) hsecondFlow hcubic
        edge hsecond with
      ⟨root, cycle, hcycle, hedgeMem, hsupport⟩
    refine ⟨root, cycle, hcycle, hedgeMem, ?_⟩
    intro hcrossMem
    have hnonzero := hsupport (retainedEdgeToAmbientEdge data cross) hcrossMem
    exact hnonzero (congrArg Prod.snd hcross)
  · rcases exists_isCycle_through_of_scalar_ne_zero
        (fun edge => (difference edge).1) hfirstFlow hcubic
        edge hfirst with
      ⟨root, cycle, hcycle, hedgeMem, hsupport⟩
    refine ⟨root, cycle, hcycle, hedgeMem, ?_⟩
    intro hcrossMem
    have hnonzero := hsupport (retainedEdgeToAmbientEdge data cross) hcrossMem
    exact hnonzero (congrArg Prod.fst hcross)

/-- In particular, one scalar coordinate supplies a simple cycle through
the restored central edge that omits the retained cross. -/
theorem CrossCentralExactFaceCutPair.exists_central_cycle_avoiding_retainedCross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    ∃ (root : V) (cycle : G.Walk root root),
      cycle.IsCycle ∧
        (centralEdge data : Sym2 V) ∈ cycle.edges ∧
        (retainedEdgeToAmbientEdge data cross : Sym2 V) ∉ cycle.edges :=
  pair.exists_difference_cycle_through_avoiding_retainedCross
    minimal (centralEdge data)
      (pair.crossFaceDifferenceProfile_centralEdge_ne_zero minimal)

/-- Every residual zero of the paired repair away from the restored edge
lies on a simple difference-profile cycle that avoids the retained cross. -/
theorem CrossCentralExactFaceCutPair.exists_repaired_zero_cycle_avoiding_retainedCross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (first second : Color) (edge : G.edgeSet)
    (hedge : edge ≠ centralEdge data)
    (hzero : pair.oneZeroCrossFacePairPerturbation C first second edge = 0) :
    ∃ (root : V) (cycle : G.Walk root root),
      cycle.IsCycle ∧
        (edge : Sym2 V) ∈ cycle.edges ∧
        (retainedEdgeToAmbientEdge data cross : Sym2 V) ∉ cycle.edges :=
  pair.exists_difference_cycle_through_avoiding_retainedCross minimal edge
    (pair.crossFaceDifferenceProfile_ne_zero_of_repaired_zero
      minimal C hC first second edge hedge hzero)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
