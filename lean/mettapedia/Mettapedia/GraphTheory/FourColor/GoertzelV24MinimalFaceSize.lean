import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalTriangleFree
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceBoundaryCycleRigidity
import Mettapedia.GraphTheory.FourColor.GoertzelV24SixVertexFourCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24WeightedOrbitFaceCorridor

/-!
# Minimum face size in a vertex-minimal Tait counterexample

Cyclic five-edge-connectivity makes a four-cycle nearly spanning: its
complement is an acyclic cubic side behind a cut of size at most four, hence
has at most two vertices.  The resulting carriers of size four, five, and six
are eliminated respectively by direct Tait coloring, degree parity, and the
six-vertex four-cycle classification.

Consequently a vertex-minimal counterexample has no cycle of length at most
four.  Since every two-sided cubic facial boundary is realized by a simple
cycle with exactly the boundary length, every actual quotient face has length
at least five.  This supplies the face-size premise required by weighted
curvature directly from minimality.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalFaceSize

open GoertzelV24FourEdgeCutGluing
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalTriangleFree
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrbitFaceWalk
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24SixVertexFourCycle
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WeightedOrbitFaceCorridor
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

local instance minimalFaceSizeLocallyFinite : G.LocallyFinite :=
  fun vertex =>
    @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
      (inferInstance : DecidablePred (Membership.mem (G.neighborSet vertex)))
      inferInstance

/-- Cubic degree counting on an arbitrary vertex side: boundary edges plus
twice the internal edges equal three times the number of side vertices. -/
theorem card_crossing_add_twice_internal_eq_three_mul
    (hregular : G.IsRegularOfDegree 3) (side : V → Prop) :
    (crossingEdgeFinset G side).card +
        2 * Nat.card (G.induce {vertex | side vertex}).edgeSet =
      3 * Nat.card {vertex : V // side vertex} := by
  let sideFintype : Fintype {vertex : V // side vertex} :=
    Fintype.ofInjective (fun vertex => vertex.1) Subtype.val_injective
  letI sideSubtypeFintype : Fintype {vertex : V // side vertex} :=
    sideFintype
  letI sideSetFintype : Fintype ↑({vertex | side vertex} : Set V) :=
    sideFintype
  have hpartition := Fintype.card_congr
    (sideDartEquivInternalSumCrossing G side)
  rw [Fintype.card_sum] at hpartition
  have hside := card_sideDart_eq_three_mul hregular side
  have hinternal := card_internalSideDart_eq_twice_card_edges
    (G := G) side
  have hcrossing := card_crossingEdgeFinset_eq_card_crossingSideDart
    (G := G) side
  have hnatCard : Nat.card {vertex : V // side vertex} =
      Fintype.card {vertex : V // side vertex} :=
    Nat.card_eq_fintype_card
  have hnatInternal :
      Nat.card (G.induce {vertex | side vertex}).edgeSet =
        Fintype.card (G.induce {vertex | side vertex}).edgeSet :=
    Nat.card_eq_fintype_card
  calc
    (crossingEdgeFinset G side).card +
          2 * Nat.card (G.induce {vertex | side vertex}).edgeSet =
        Fintype.card (CrossingSideDart G side) +
          Fintype.card (InternalSideDart G side) := by
      rw [hcrossing, hnatInternal,
        ← (G.induce {vertex | side vertex}).edgeFinset_card, hinternal]
    _ = Fintype.card (SideDart G side) := by omega
    _ = 3 * Fintype.card {vertex : V // side vertex} := hside
    _ = 3 * Nat.card {vertex : V // side vertex} := by rw [hnatCard]

omit [Fintype V] in
/-- Four pairwise distinct named vertices form a four-element subtype. -/
theorem natCard_fourCycleSide_eq_four
    {first second third fourth : V}
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hfirstFourth : first ≠ fourth)
    (hsecondThird : second ≠ third)
    (hsecondFourth : second ≠ fourth)
    (hthirdFourth : third ≠ fourth) :
    Nat.card {vertex : V //
      vertex ∈ ({first, second, third, fourth} : Finset V)} = 4 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card ↑({first, second, third, fourth} : Finset V) = 4
  rw [Fintype.card_coe]
  simp [hfirstSecond, hfirstThird, hfirstFourth,
    hsecondThird, hsecondFourth, hthirdFourth]

omit [Fintype V] in
/-- The four perimeter edges of a simple four-cycle are distinct internal
edges of its vertex side. -/
theorem four_le_fourCycle_induced_edgeFinset_card
    {first second third fourth : V}
    (hfirstSecond : G.Adj first second)
    (hsecondThird : G.Adj second third)
    (hthirdFourth : G.Adj third fourth)
    (hfourthFirst : G.Adj fourth first)
    (hfirstThird : first ≠ third)
    (hsecondFourth : second ≠ fourth) :
    4 ≤ Nat.card (G.induce {vertex | vertex ∈
      ({first, second, third, fourth} : Finset V)}).edgeSet := by
  let inside : Finset V := {first, second, third, fourth}
  let H := G.induce {vertex | vertex ∈ inside}
  let firstVertex : {vertex : V // vertex ∈ inside} :=
    ⟨first, by simp [inside]⟩
  let secondVertex : {vertex : V // vertex ∈ inside} :=
    ⟨second, by simp [inside]⟩
  let thirdVertex : {vertex : V // vertex ∈ inside} :=
    ⟨third, by simp [inside]⟩
  let fourthVertex : {vertex : V // vertex ∈ inside} :=
    ⟨fourth, by simp [inside]⟩
  let cycleEdge : Fin 4 → H.edgeSet
    | 0 => ⟨s(firstVertex, secondVertex), hfirstSecond⟩
    | 1 => ⟨s(secondVertex, thirdVertex), hsecondThird⟩
    | 2 => ⟨s(thirdVertex, fourthVertex), hthirdFourth⟩
    | 3 => ⟨s(fourthVertex, firstVertex), hfourthFirst⟩
  have hzeroOne : cycleEdge 0 ≠ cycleEdge 1 := by
    intro heq
    have hvalue := congrArg Subtype.val heq
    change s(firstVertex, secondVertex) =
      s(secondVertex, thirdVertex) at hvalue
    rw [Sym2.eq_iff] at hvalue
    rcases hvalue with hvalue | hvalue
    · exact hfirstSecond.ne
        (congrArg Subtype.val hvalue.1)
    · exact hfirstThird (congrArg Subtype.val hvalue.1)
  have hzeroTwo : cycleEdge 0 ≠ cycleEdge 2 := by
    intro heq
    have hvalue := congrArg Subtype.val heq
    change s(firstVertex, secondVertex) =
      s(thirdVertex, fourthVertex) at hvalue
    rw [Sym2.eq_iff] at hvalue
    rcases hvalue with hvalue | hvalue
    · exact hfirstThird (congrArg Subtype.val hvalue.1)
    · exact hfourthFirst.ne.symm
        (congrArg Subtype.val hvalue.1)
  have hzeroThree : cycleEdge 0 ≠ cycleEdge 3 := by
    intro heq
    have hvalue := congrArg Subtype.val heq
    change s(firstVertex, secondVertex) =
      s(fourthVertex, firstVertex) at hvalue
    rw [Sym2.eq_iff] at hvalue
    rcases hvalue with hvalue | hvalue
    · exact hfourthFirst.ne.symm
        (congrArg Subtype.val hvalue.1)
    · exact hsecondFourth (congrArg Subtype.val hvalue.2)
  have honeTwo : cycleEdge 1 ≠ cycleEdge 2 := by
    intro heq
    have hvalue := congrArg Subtype.val heq
    change s(secondVertex, thirdVertex) =
      s(thirdVertex, fourthVertex) at hvalue
    rw [Sym2.eq_iff] at hvalue
    rcases hvalue with hvalue | hvalue
    · exact hsecondThird.ne
        (congrArg Subtype.val hvalue.1)
    · exact hsecondFourth (congrArg Subtype.val hvalue.1)
  have honeThree : cycleEdge 1 ≠ cycleEdge 3 := by
    intro heq
    have hvalue := congrArg Subtype.val heq
    change s(secondVertex, thirdVertex) =
      s(fourthVertex, firstVertex) at hvalue
    rw [Sym2.eq_iff] at hvalue
    rcases hvalue with hvalue | hvalue
    · exact hsecondFourth (congrArg Subtype.val hvalue.1)
    · exact hfirstSecond.ne.symm
        (congrArg Subtype.val hvalue.1)
  have htwoThree : cycleEdge 2 ≠ cycleEdge 3 := by
    intro heq
    have hvalue := congrArg Subtype.val heq
    change s(thirdVertex, fourthVertex) =
      s(fourthVertex, firstVertex) at hvalue
    rw [Sym2.eq_iff] at hvalue
    rcases hvalue with hvalue | hvalue
    · exact hthirdFourth.ne
        (congrArg Subtype.val hvalue.1)
    · exact hfirstThird.symm
        (congrArg Subtype.val hvalue.1)
  have hinjective : Function.Injective cycleEdge := by
    intro left right heq
    fin_cases left <;> fin_cases right
    · rfl
    · exact False.elim (hzeroOne heq)
    · exact False.elim (hzeroTwo heq)
    · exact False.elim (hzeroThree heq)
    · exact False.elim (hzeroOne heq.symm)
    · rfl
    · exact False.elim (honeTwo heq)
    · exact False.elim (honeThree heq)
    · exact False.elim (hzeroTwo heq.symm)
    · exact False.elim (honeTwo heq.symm)
    · rfl
    · exact False.elim (htwoThree heq)
    · exact False.elim (hzeroThree heq.symm)
    · exact False.elim (honeThree heq.symm)
    · exact False.elim (htwoThree heq.symm)
    · rfl
  calc
    4 = Fintype.card (Fin 4) := by simp
    _ ≤ Fintype.card H.edgeSet :=
      Fintype.card_le_of_injective cycleEdge hinjective
    _ = Nat.card H.edgeSet := Nat.card_eq_fintype_card.symm

/-- A four-cycle in a cubic graph has at most four edges leaving its four
vertices. -/
theorem card_fourCycle_crossingEdgeFinset_le_four
    (hregular : G.IsRegularOfDegree 3)
    {first second third fourth : V}
    (hfirstSecond : G.Adj first second)
    (hsecondThird : G.Adj second third)
    (hthirdFourth : G.Adj third fourth)
    (hfourthFirst : G.Adj fourth first)
    (hfirstThird : first ≠ third)
    (hsecondFourth : second ≠ fourth) :
    (crossingEdgeFinset G (fun vertex => vertex ∈
      ({first, second, third, fourth} : Finset V))).card ≤ 4 := by
  let side : V → Prop := fun vertex => vertex ∈
    ({first, second, third, fourth} : Finset V)
  have hvertices : Nat.card {vertex : V // side vertex} = 4 := by
    simpa [side] using natCard_fourCycleSide_eq_four
      hfirstSecond.ne hfirstThird hfourthFirst.ne.symm
      hsecondThird.ne hsecondFourth hthirdFourth.ne
  have hinternal :
      4 ≤ Nat.card (G.induce {vertex | side vertex}).edgeSet := by
    simpa [side] using four_le_fourCycle_induced_edgeFinset_card
      hfirstSecond hsecondThird hthirdFourth hfourthFirst
      hfirstThird hsecondFourth
  have hcount :=
    card_crossing_add_twice_internal_eq_three_mul
      hregular side
  rw [hvertices] at hcount
  simpa [side] using (show (crossingEdgeFinset G side).card ≤ 4 by omega)

omit [Fintype V] [DecidableRel G.Adj] in
/-- The four-cycle itself witnesses a cycle on its vertex side. -/
theorem hasCycleOnSide_fourCycle
    {first second third fourth : V}
    (hfirstSecond : G.Adj first second)
    (hsecondThird : G.Adj second third)
    (hthirdFourth : G.Adj third fourth)
    (hfourthFirst : G.Adj fourth first)
    (hfirstThird : first ≠ third)
    (hsecondFourth : second ≠ fourth) :
    HasCycleOnSide G (fun vertex => vertex ∈
      ({first, second, third, fourth} : Finset V)) := by
  let cycleWalk : G.Walk first first :=
    SimpleGraph.Walk.cons hfirstSecond
      (SimpleGraph.Walk.cons hsecondThird
        (SimpleGraph.Walk.cons hthirdFourth
          (SimpleGraph.Walk.cons hfourthFirst SimpleGraph.Walk.nil)))
  have hcycle : cycleWalk.IsCycle := by
    simp [cycleWalk, SimpleGraph.Walk.cons_isCycle_iff,
      SimpleGraph.Walk.cons_isPath_iff,
      hfirstSecond.ne, hsecondThird.ne, hthirdFourth.ne,
      hfourthFirst.ne, hfirstSecond.ne.symm,
      hfirstThird, hfirstThird.symm, hsecondFourth]
  refine ⟨first, by simp, cycleWalk, hcycle, ?_⟩
  intro vertex hvertex
  have hvertex' :
      vertex = first ∨ vertex = second ∨ vertex = third ∨
        vertex = fourth ∨ vertex = first := by
    simpa [cycleWalk] using hvertex
  rcases hvertex' with rfl | rfl | rfl | rfl | rfl <;> simp

/-- In a cyclically five-edge-connected cubic graph, the complement of a
four-cycle is acyclic and contains at most two vertices. -/
theorem natCard_complement_fourCycle_le_two_of_cyclicallyFive
    (graphData : Data G)
    (hregular : G.IsRegularOfDegree 3)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {first second third fourth : V}
    (hfirstSecond : G.Adj first second)
    (hsecondThird : G.Adj second third)
    (hthirdFourth : G.Adj third fourth)
    (hfourthFirst : G.Adj fourth first)
    (hfirstThird : first ≠ third)
    (hsecondFourth : second ≠ fourth) :
    Nat.card {vertex : V //
      vertex ∉ ({first, second, third, fourth} : Finset V)} ≤ 2 := by
  let inside : Finset V := {first, second, third, fourth}
  let outsideSide : V → Prop := fun vertex => vertex ∉ inside
  have hboundaryLe :
      (crossingEdgeFinset G (fun vertex => vertex ∈ inside)).card ≤ 4 := by
    simpa [inside] using card_fourCycle_crossingEdgeFinset_le_four
      hregular hfirstSecond hsecondThird hthirdFourth hfourthFirst
      hfirstThird hsecondFourth
  have hinsideCycle :
      HasCycleOnSide G (fun vertex => vertex ∈ inside) := by
    simpa [inside] using hasCycleOnSide_fourCycle
      hfirstSecond hsecondThird hthirdFourth hfourthFirst
      hfirstThird hsecondFourth
  have houtsideNoCycle : ¬ HasCycleOnSide G outsideSide := by
    intro houtsideCycle
    have hfive := five_le_card_vertexSetCrossingEdges_of_cycles
      graphData inside hcyclic hinsideCycle (by
        simpa [outsideSide] using houtsideCycle)
    have hcrossingEq :
        vertexSetCrossingEdges graphData.toRotationSystem inside =
          crossingEdgeFinset G (fun vertex => vertex ∈ inside) := by
      ext edge
      rw [mem_simpleGraph_vertexSetCrossingEdges_iff,
        mem_crossingEdgeFinset_iff]
    rw [hcrossingEq] at hfive
    omega
  have houtsideAcyclic :
      (G.induce {vertex | outsideSide vertex}).IsAcyclic := by
    intro vertex cycle hcycle
    apply houtsideNoCycle
    let inclusion :=
      (SimpleGraph.Embedding.induce (G := G)
        {vertex | outsideSide vertex}).toHom
    refine ⟨vertex.1, vertex.2, cycle.map inclusion, ?_, ?_⟩
    · exact hcycle.map (fun _ _ heq => Subtype.ext heq)
    · intro other hother
      have hother' : other ∈ cycle.support.map inclusion := by
        exact SimpleGraph.Walk.support_map inclusion cycle ▸ hother
      rcases List.mem_map.mp hother' with
        ⟨source, _hsource, hsource⟩
      rw [← hsource]
      exact source.2
  by_cases hnonempty : Nonempty {vertex : V // outsideSide vertex}
  · let outsideCarrierEquiv :
        ↑({vertex | outsideSide vertex} : Set V) ≃
          {vertex : V // outsideSide vertex} :=
      { toFun := fun vertex => ⟨vertex.1, vertex.2⟩
        invFun := fun vertex => ⟨vertex.1, vertex.2⟩
        left_inv := fun vertex => by cases vertex; rfl
        right_inv := fun vertex => by cases vertex; rfl }
    have houtsideCarrierCard :
        Nat.card ↑({vertex | outsideSide vertex} : Set V) =
          Nat.card {vertex : V // outsideSide vertex} :=
      Nat.card_congr outsideCarrierEquiv
    have hedgeBound :
        Nat.card (G.induce {vertex | outsideSide vertex}).edgeSet + 1 ≤
          Nat.card {vertex : V // outsideSide vertex} := by
      rw [← houtsideCarrierCard]
      exact natCard_edgeSet_add_one_le_of_isAcyclic
        (G.induce {vertex | outsideSide vertex})
        (Nonempty.map outsideCarrierEquiv.symm hnonempty)
        houtsideAcyclic
    have hboundaryEq :
        crossingEdgeFinset G outsideSide =
          crossingEdgeFinset G (fun vertex => vertex ∈ inside) := by
      ext edge
      rw [mem_crossingEdgeFinset_iff, mem_crossingEdgeFinset_iff]
      simpa [outsideSide] using
        (edgeCrossesVertexSide_compl G
          (fun vertex => vertex ∈ inside) edge)
    have houtsideBoundaryLe :
        (crossingEdgeFinset G outsideSide).card ≤ 4 := by
      rw [hboundaryEq]
      exact hboundaryLe
    have hcount := card_crossing_add_twice_internal_eq_three_mul
      hregular outsideSide
    have houtsideCard :
        Nat.card {vertex : V // outsideSide vertex} ≤ 2 := by
      omega
    simpa [outsideSide, inside] using houtsideCard
  · haveI : IsEmpty {vertex : V // outsideSide vertex} :=
      not_nonempty_iff.mp hnonempty
    have houtsideCard :
        Nat.card {vertex : V // outsideSide vertex} = 0 :=
      Finite.card_eq_zero_iff.mpr inferInstance
    have : Nat.card {vertex : V // outsideSide vertex} ≤ 2 := by
      omega
    simpa [outsideSide, inside] using this

/-- Partitioning the carrier by four distinct named vertices gives the exact
four-plus-complement cardinality formula. -/
theorem fintype_card_eq_four_add_complement_fourCycle
    {first second third fourth : V}
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hfirstFourth : first ≠ fourth)
    (hsecondThird : second ≠ third)
    (hsecondFourth : second ≠ fourth)
    (hthirdFourth : third ≠ fourth) :
    Fintype.card V = 4 + Nat.card {vertex : V //
      vertex ∉ ({first, second, third, fourth} : Finset V)} := by
  let inside : Finset V := {first, second, third, fourth}
  have hinsideCard :
      Fintype.card {vertex : V // vertex ∈ inside} = 4 := by
    rw [← Nat.card_eq_fintype_card]
    simpa [inside] using natCard_fourCycleSide_eq_four
      hfirstSecond hfirstThird hfirstFourth hsecondThird
      hsecondFourth hthirdFourth
  have houtsideCard :
      Fintype.card {vertex : V // vertex ∉ inside} =
        Nat.card {vertex : V // vertex ∉ inside} :=
    Nat.card_eq_fintype_card.symm
  have hpartition :
      Fintype.card {vertex : V // vertex ∈ inside} +
          Fintype.card {vertex : V // vertex ∉ inside} =
        Fintype.card V := by
    calc
      Fintype.card {vertex : V // vertex ∈ inside} +
            Fintype.card {vertex : V // vertex ∉ inside} =
          Fintype.card
            ({vertex : V // vertex ∈ inside} ⊕
              {vertex : V // vertex ∉ inside}) :=
        Fintype.card_sum.symm
      _ = Fintype.card V :=
        Fintype.card_congr (Equiv.sumCompl (fun vertex => vertex ∈ inside))
  rw [hinsideCard, houtsideCard] at hpartition
  simpa [inside] using hpartition.symm

/-- A graph-backed vertex-minimal Tait counterexample contains no simple
four-cycle. -/
theorem no_fourCycle_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {first second third fourth : V}
    (hfirstSecond : G.Adj first second)
    (hsecondThird : G.Adj second third)
    (hthirdFourth : G.Adj third fourth)
    (hfourthFirst : G.Adj fourth first)
    (hfirstThird : first ≠ third)
    (hsecondFourth : second ≠ fourth) : False := by
  have hregular : G.IsRegularOfDegree 3 :=
    graphData.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have hcyclic : CyclicallyFiveEdgeConnected G :=
    cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
      graphData minimal
  have houtside :=
    natCard_complement_fourCycle_le_two_of_cyclicallyFive
      graphData hregular hcyclic hfirstSecond hsecondThird
      hthirdFourth hfourthFirst hfirstThird hsecondFourth
  have hcardPartition :=
    fintype_card_eq_four_add_complement_fourCycle
      hfirstSecond.ne hfirstThird hfourthFirst.ne.symm
      hsecondThird.ne hsecondFourth hthirdFourth.ne
  let outsideCard := Nat.card {vertex : V //
    vertex ∉ ({first, second, third, fourth} : Finset V)}
  have houtsideCard : outsideCard ≤ 2 := by
    simpa [outsideCard] using houtside
  have hcard : Fintype.card V = 4 + outsideCard := by
    simpa [outsideCard] using hcardPartition
  have hcases : outsideCard = 0 ∨ outsideCard = 1 ∨ outsideCard = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · have hfour : Fintype.card V = 4 := by omega
    exact
      (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
        graphData minimal)
      (exists_taitEdgeColoring_of_card_eq_four G hfour)
  · have hfive : Fintype.card V = 5 := by omega
    have hdegreeSum := G.sum_degrees_eq_twice_card_edges
    have hsum : ∑ vertex : V, G.degree vertex =
        3 * Fintype.card V := by
      simp [hregular.degree_eq, mul_comm]
    rw [hsum, hfive] at hdegreeSum
    omega
  · have hsix : Fintype.card V = 6 := by omega
    have hnoFirstThird : ¬ G.Adj first third := by
      intro hadj
      exact no_common_neighbor_of_vertexMinimalTaitCounterexample
        graphData minimal hfirstSecond third hadj hsecondThird
    have hnoSecondFourth : ¬ G.Adj second fourth := by
      intro hadj
      exact no_common_neighbor_of_vertexMinimalTaitCounterexample
        graphData minimal hsecondThird fourth hadj hthirdFourth
    exact
      (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
        graphData minimal)
      (exists_taitEdgeColoring_of_card_eq_six_and_four_cycle
        hregular hfirstSecond hsecondThird hthirdFourth hfourthFirst
        hfirstThird hsecondFourth hnoFirstThird hnoSecondFourth hsix)

/-- Every simple cycle in a graph-backed vertex-minimal Tait counterexample
has length at least five. -/
theorem not_isCycle_length_le_four_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {root : V} (cycle : G.Walk root root) (hcycle : cycle.IsCycle) :
    ¬ cycle.length ≤ 4 := by
  intro hshort
  have hthree : 3 ≤ cycle.length := hcycle.three_le_length
  have hlength : cycle.length = 3 ∨ cycle.length = 4 := by omega
  rcases hlength with hlength | hlength
  · let first := cycle.getVert 0
    let second := cycle.getVert 1
    let third := cycle.getVert 2
    have hfirstSecond : G.Adj first second := by
      simpa [first, second] using
        cycle.adj_getVert_succ (i := 0) (by omega)
    have hsecondThird : G.Adj second third := by
      simpa [second, third] using
        cycle.adj_getVert_succ (i := 1) (by omega)
    have hthirdFirst : G.Adj third first := by
      have hadj := cycle.adj_getVert_succ (i := 2) (by omega)
      have hwrap : cycle.getVert 3 = cycle.getVert 0 := by
        rw [← hlength, cycle.getVert_length, cycle.getVert_zero]
      simpa [first, third, hwrap] using hadj
    exact no_common_neighbor_of_vertexMinimalTaitCounterexample
      graphData minimal hfirstSecond third hthirdFirst.symm hsecondThird
  · let first := cycle.getVert 0
    let second := cycle.getVert 1
    let third := cycle.getVert 2
    let fourth := cycle.getVert 3
    have hfirstSecond : G.Adj first second := by
      simpa [first, second] using
        cycle.adj_getVert_succ (i := 0) (by omega)
    have hsecondThird : G.Adj second third := by
      simpa [second, third] using
        cycle.adj_getVert_succ (i := 1) (by omega)
    have hthirdFourth : G.Adj third fourth := by
      simpa [third, fourth] using
        cycle.adj_getVert_succ (i := 2) (by omega)
    have hfourthFirst : G.Adj fourth first := by
      have hadj := cycle.adj_getVert_succ (i := 3) (by omega)
      have hwrap : cycle.getVert 4 = cycle.getVert 0 := by
        rw [← hlength, cycle.getVert_length, cycle.getVert_zero]
      simpa [first, fourth, hwrap] using hadj
    have hfirstThird : first ≠ third := by
      intro heq
      have : (0 : Nat) = 2 := hcycle.getVert_injOn'
        (by simp [hlength]) (by simp [hlength]) heq
      omega
    have hsecondFourth : second ≠ fourth := by
      intro heq
      have : (1 : Nat) = 3 := hcycle.getVert_injOn'
        (by simp [hlength]) (by simp [hlength]) heq
      omega
    exact no_fourCycle_of_vertexMinimalTaitCounterexample graphData minimal
      hfirstSecond hsecondThird hthirdFourth hfourthFirst
      hfirstThird hsecondFourth

/-- Every quotient face of a graph-backed vertex-minimal Tait counterexample
has boundary length at least five. -/
theorem orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) :
    OrbitFaceMinimumFive graphData.toRotationSystem := by
  intro face
  rcases exists_dartOrbitFace_eq graphData.toRotationSystem face with
    ⟨root, rfl⟩
  rcases exists_rootedFaceCycle graphData minimal.spherical.cubic
      minimal.facesTwoSided root with
    ⟨cycle, hcycle, hdarts, _hedges⟩
  have hsimple := orbitFaceBoundarySimple_of_twoSided
    graphData.toRotationSystem minimal.facesTwoSided
  have hlength : cycle.length =
      (orbitFaceBoundary graphData.toRotationSystem
        (dartOrbitFace graphData.toRotationSystem root)).card := by
    calc
      cycle.length = cycle.darts.length := cycle.length_darts.symm
      _ = (faceOrbitDarts graphData root).length :=
        congrArg List.length hdarts
      _ = (graphData.toRotationSystem.faceOrbit root).card :=
        length_faceOrbitDarts graphData root
      _ = (orbitFaceDarts graphData.toRotationSystem
          (dartOrbitFace graphData.toRotationSystem root)).card :=
        congrArg Finset.card
          (orbitFaceDarts_dartOrbitFace_eq_faceOrbit
            graphData.toRotationSystem root).symm
      _ = (orbitFaceBoundary graphData.toRotationSystem
          (dartOrbitFace graphData.toRotationSystem root)).card :=
        (hsimple (dartOrbitFace graphData.toRotationSystem root)).symm
  by_contra hminimum
  exact not_isCycle_length_le_four_of_vertexMinimalTaitCounterexample
    graphData minimal cycle hcycle (by omega)

end

end GoertzelV24MinimalFaceSize

end Mettapedia.GraphTheory.FourColor
