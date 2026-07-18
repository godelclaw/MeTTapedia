import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutNormalization

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalCyclicThreeEdgeConnected

open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoEdgeCutNormalization
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A cyclic cut in a connected graph contains a crossing edge. -/
theorem edgeCut_nonempty_of_connected
    (cut : SmallCyclicEdgeCut G) (hconnected : G.Connected) :
    cut.edgeCut.Nonempty := by
  rcases cut.hinside_cycle with ⟨inside, hinside, _⟩
  rcases cut.houtside_cycle with ⟨outside, houtside, _⟩
  rcases hconnected inside outside with ⟨walk⟩
  rcases cut.exists_mem_edgeCut_of_walk_endpoint_sides
      walk hinside houtside with ⟨edge, hedge, _⟩
  exact ⟨edge, hedge⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The inside cycle supplies an ambient edge not belonging to the cyclic
cut. -/
theorem exists_internalEdge_not_mem_edgeCut
    (cut : SmallCyclicEdgeCut G) :
    ∃ edge : G.edgeSet, edge ∉ cut.edgeCut := by
  rcases cut.hinside_cycle with
    ⟨start, hstart, walk, hcycle, hsupport⟩
  cases walk with
  | nil => exact (hcycle.ne_nil rfl).elim
  | @cons _ next _ hadj tail =>
      let edge : G.edgeSet := ⟨s(start, next), hadj⟩
      have hnext : cut.side next := hsupport next (by simp)
      refine ⟨edge, ?_⟩
      intro hedge
      have hcross : EdgeCrossesVertexSide G cut.side edge :=
        (cut.edge_mem_iff edge).1 hedge
      exact
        (not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
          (side := cut.side) (a := start) (b := next) (e := edge)
          rfl hcross) ⟨fun _ => hnext, fun _ => hstart⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- A nonempty cut of size at most two fits inside a pair of distinct
ambient edges. For a singleton cut, an inside-cycle edge supplies the
second edge. -/
theorem exists_distinct_pair_cover_of_connected_of_card_le_two
    (cut : SmallCyclicEdgeCut G) (hconnected : G.Connected)
    (hcard : cut.edgeCut.card ≤ 2) :
    ∃ first second : G.edgeSet,
      first ≠ second ∧
        cut.edgeCut ⊆ ({first, second} : Finset G.edgeSet) := by
  have hpositive : 0 < cut.edgeCut.card :=
    Finset.card_pos.mpr (edgeCut_nonempty_of_connected cut hconnected)
  have hcases : cut.edgeCut.card = 1 ∨ cut.edgeCut.card = 2 := by
    omega
  rcases hcases with hone | htwo
  · rcases Finset.card_eq_one.mp hone with ⟨first, hcut⟩
    rcases exists_internalEdge_not_mem_edgeCut cut with
      ⟨second, hsecond⟩
    have hne : first ≠ second := by
      intro heq
      apply hsecond
      rw [hcut, ← heq]
      simp
    exact ⟨first, second, hne, by
      rw [hcut]
      exact Finset.singleton_subset_iff.mpr (by simp)⟩
  · rcases Finset.card_eq_two.mp htwo with
      ⟨first, second, hne, hcut⟩
    exact ⟨first, second, hne, by rw [hcut]⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- Deleting any distinct pair that covers a cyclic cut disconnects the
inside-cycle root from the outside-cycle root. -/
theorem not_connected_deleteEdges_of_subset_pair
    (cut : SmallCyclicEdgeCut G)
    (first second : G.edgeSet)
    (hcover : cut.edgeCut ⊆ ({first, second} : Finset G.edgeSet)) :
    ¬ (G.deleteEdges
      ({first.1, second.1} : Set (Sym2 V))).Connected := by
  intro hconnected
  rcases cut.hinside_cycle with ⟨inside, hinside, _⟩
  rcases cut.houtside_cycle with ⟨outside, houtside, _⟩
  rcases hconnected inside outside with ⟨deletedWalk⟩
  let ambientWalk : G.Walk inside outside :=
    deletedWalk.mapLe
      (G.deleteEdges_le ({first.1, second.1} : Set (Sym2 V)))
  have hambientEdges : ambientWalk.edges = deletedWalk.edges :=
    deletedWalk.edges_mapLe_eq_edges
      (G.deleteEdges_le ({first.1, second.1} : Set (Sym2 V)))
  rcases cut.exists_mem_edgeCut_of_walk_endpoint_sides
      ambientWalk hinside houtside with
    ⟨crossing, hcrossingCut, hcrossingWalk⟩
  have hcrossingPair := hcover hcrossingCut
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcrossingPair
  rcases hcrossingPair with hfirst | hsecond
  · have havoidsFirst : first.1 ∉ ambientWalk.edges := by
      intro hmem
      have hdeleted := deletedWalk.edges_subset_edgeSet
        (by simpa [hambientEdges] using hmem)
      simp at hdeleted
    exact havoidsFirst (by simpa [hfirst] using hcrossingWalk)
  · have havoidsSecond : second.1 ∉ ambientWalk.edges := by
      intro hmem
      have hdeleted := deletedWalk.edges_subset_edgeSet
        (by simpa [hambientEdges] using hmem)
      simp at hdeleted
    exact havoidsSecond (by simpa [hsecond] using hcrossingWalk)

/-- Every cyclic edge cut in a graph-backed vertex-minimal Tait
counterexample has at least three edges. This packages bridge-freeness and
the exact two-edge cap reduction into the first cyclic-connectivity rung. -/
theorem smallCyclicEdgeCut_card_three_le_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) :
    3 ≤ cut.edgeCut.card := by
  by_contra hnot
  have hcard : cut.edgeCut.card ≤ 2 := by omega
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  rcases exists_distinct_pair_cover_of_connected_of_card_le_two
      cut hconnected hcard with ⟨first, second, hne, hcover⟩
  have hdelete := not_connected_deleteEdges_of_subset_pair
    cut first second hcover
  exact hdelete
    (deleteEdges_pair_connected_of_vertexMinimalTaitCounterexample
      graphData minimal first second hne)

/-- Graph-backed vertex minimality implies cyclic edge-connectivity at
least three. -/
theorem cyclicEdgeConnectivityAtLeast_three_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) :
    CyclicEdgeConnectivityAtLeast G 3 := by
  intro cut
  exact smallCyclicEdgeCut_card_three_le_of_vertexMinimalTaitCounterexample
    graphData minimal cut

/-- After the one- and two-edge reductions, every remaining small cyclic
cut has exactly three or four edges. -/
theorem smallCyclicEdgeCut_card_eq_three_or_four_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) :
    cut.edgeCut.card = 3 ∨ cut.edgeCut.card = 4 := by
  have hthree :=
    smallCyclicEdgeCut_card_three_le_of_vertexMinimalTaitCounterexample
      graphData minimal cut
  have hfour := cut.card_le_four
  omega

/-- Excluding the exact three- and four-edge cases is sufficient to prove
cyclic five-edge-connectivity of a graph-backed vertex-minimal Tait
counterexample. -/
theorem cyclicallyFiveEdgeConnected_of_no_three_or_four_cyclicEdgeCut
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hthree : ∀ cut : SmallCyclicEdgeCut G, cut.edgeCut.card ≠ 3)
    (hfour : ∀ cut : SmallCyclicEdgeCut G, cut.edgeCut.card ≠ 4) :
    CyclicallyFiveEdgeConnected G := by
  apply NoCyclicEdgeCutOfSizeAtMostFour.cyclicallyFiveEdgeConnected
  intro hcut
  rcases hcut with ⟨cut, _⟩
  rcases
      smallCyclicEdgeCut_card_eq_three_or_four_of_vertexMinimalTaitCounterexample
        graphData minimal cut with hcard | hcard
  · exact hthree cut hcard
  · exact hfour cut hcard

/-- For a graph-backed vertex-minimal Tait counterexample, cyclic
five-edge-connectivity is exactly the absence of cyclic cuts of cardinality
three and four. -/
theorem cyclicallyFiveEdgeConnected_iff_no_three_and_no_four_cyclicEdgeCut
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) :
    CyclicallyFiveEdgeConnected G ↔
      (∀ cut : SmallCyclicEdgeCut G, cut.edgeCut.card ≠ 3) ∧
      (∀ cut : SmallCyclicEdgeCut G, cut.edgeCut.card ≠ 4) := by
  constructor
  · intro hfive
    constructor
    · intro cut hcard
      have := hfive cut
      omega
    · intro cut hcard
      have := hfive cut
      omega
  · rintro ⟨hthree, hfour⟩
    exact cyclicallyFiveEdgeConnected_of_no_three_or_four_cyclicEdgeCut
      graphData minimal hthree hfour

end

end GoertzelV24MinimalCyclicThreeEdgeConnected

end Mettapedia.GraphTheory.FourColor
