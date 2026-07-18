import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutAttachment
import Mettapedia.GraphTheory.FourColor.GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphTaitBridge

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalTriangleFree

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FaceDualConnectedness
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [decidableAdjacency : DecidableRel G.Adj]

noncomputable section

local instance minimalTriangleEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance minimalTriangleLocallyFinite : G.LocallyFinite :=
  fun vertex =>
    @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
      (decidableAdjacency vertex) inferInstance

/-- Cubic degree counting across an arbitrary finite vertex side: three
darts per side vertex split into twice the internal edges and one dart per
crossing edge. -/
theorem card_crossingEdgeFinset_add_twice_internal_eq_three_mul
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

/-- A nonempty finite acyclic graph has at most one fewer edge than
vertices, obtained by extending it to a spanning tree of the complete
graph on the same carrier. -/
theorem natCard_edgeSet_add_one_le_of_isAcyclic
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hnonempty : Nonempty W) (hacyclic : H.IsAcyclic) :
    Nat.card H.edgeSet + 1 ≤ Nat.card W := by
  letI : Nonempty W := hnonempty
  obtain ⟨tree, hHtree, _htreeTop, htree⟩ :=
    SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic
      (G := (⊤ : SimpleGraph W))
      (SimpleGraph.connected_top : (⊤ : SimpleGraph W).Connected)
      (show H ≤ ⊤ from le_top) hacyclic
  calc
    Nat.card H.edgeSet + 1 = H.edgeFinset.card + 1 := by
      rw [Nat.card_eq_fintype_card, ← H.edgeFinset_card]
    _ ≤ tree.edgeFinset.card + 1 :=
      Nat.add_le_add_right
        (Finset.card_le_card (SimpleGraph.edgeFinset_mono hHtree)) 1
    _ = Fintype.card W := htree.card_edgeFinset
    _ = Nat.card W := Nat.card_eq_fintype_card.symm

/-- Labeling four vertices by the Klein four color group and coloring an
edge by the sum of its endpoint labels gives a proper edge coloring. -/
def xorEdgeColor (label : V ≃ Color) (edge : G.edgeSet) : Color :=
  Sym2.lift
    ⟨fun first second => label first + label second,
      fun _first _second => add_comm _ _⟩ edge.1

/-- The xor endpoint rule is proper on the line graph of every simple graph
whose vertex labels inject into the color group. -/
def xorEdgeColoring (label : V ≃ Color) : G.EdgeColoring Color :=
  SimpleGraph.Coloring.mk (xorEdgeColor (G := G) label) (by
    intro first second hadj
    rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
    rcases hadj with ⟨hne, vertex, hfirst, hsecond⟩
    intro hcolor
    have hcolor' :
        label vertex + label (Sym2.Mem.other' hfirst) =
          label vertex + label (Sym2.Mem.other' hsecond) := by
      unfold xorEdgeColor at hcolor
      rw [← Sym2.other_spec' hfirst, ← Sym2.other_spec' hsecond] at hcolor
      simpa only [Sym2.lift_mk] using hcolor
    have hother : Sym2.Mem.other' hfirst = Sym2.Mem.other' hsecond :=
      label.injective (add_left_cancel hcolor')
    apply hne
    apply Subtype.ext
    rw [← Sym2.other_spec' hfirst, ← Sym2.other_spec' hsecond,
      hother])

/-- Every simple graph on four vertices has a proper nonzero edge coloring
by the three nonzero elements of the Klein four group. -/
theorem exists_taitEdgeColoring_of_card_eq_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 4) :
    ∃ coloring : G.EdgeColoring Color,
      IsTaitEdgeColoring G coloring := by
  let label : V ≃ Color := Fintype.equivOfCardEq (by
    rw [hcard]
    decide)
  let coloring := xorEdgeColoring (G := G) label
  refine ⟨coloring, ?_⟩
  rintro ⟨edge, hedge⟩
  induction edge using Sym2.ind with
  | _ first second =>
      have hadj : G.Adj first second :=
        (SimpleGraph.mem_edgeSet G).1 hedge
      change label first + label second ≠ 0
      intro hzero
      exact hadj.ne
        (label.injective ((add_eq_zero_iff_eq _ _).1 hzero))

/-- Three pairwise distinct named vertices give a three-element side. -/
theorem natCard_triangleSide_eq_three
    {first second third : V}
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    Nat.card {vertex : V //
      vertex ∈ ({first, second, third} : Finset V)} = 3 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card ↑({first, second, third} : Finset V) = 3
  rw [Fintype.card_coe]
  simp [hfirstSecond, hfirstThird, hsecondThird]

/-- The three edges of a graph triangle are three distinct internal edges
of its induced three-vertex side. -/
theorem three_le_triangle_induced_edgeFinset_card
    {first second third : V}
    (hfirstSecond : G.Adj first second)
    (hfirstThird : G.Adj first third)
    (hsecondThird : G.Adj second third) :
    3 ≤ Nat.card (G.induce {vertex | vertex ∈
      ({first, second, third} : Finset V)}).edgeSet := by
  let inside : Finset V := {first, second, third}
  let H := G.induce {vertex | vertex ∈ inside}
  let firstVertex : {vertex : V // vertex ∈ inside} :=
    ⟨first, by simp [inside]⟩
  let secondVertex : {vertex : V // vertex ∈ inside} :=
    ⟨second, by simp [inside]⟩
  let thirdVertex : {vertex : V // vertex ∈ inside} :=
    ⟨third, by simp [inside]⟩
  let triangleEdge : Fin 3 → H.edgeSet
    | 0 => ⟨s(firstVertex, secondVertex), hfirstSecond⟩
    | 1 => ⟨s(firstVertex, thirdVertex), hfirstThird⟩
    | 2 => ⟨s(secondVertex, thirdVertex), hsecondThird⟩
  have hzeroOne : triangleEdge 0 ≠ triangleEdge 1 := by
    intro heq
    have hvalue := congrArg Subtype.val heq
    change s(firstVertex, secondVertex) =
      s(firstVertex, thirdVertex) at hvalue
    have hvertices : secondVertex = thirdVertex :=
      Sym2.congr_right.mp hvalue
    exact hsecondThird.ne (congrArg Subtype.val hvertices)
  have hzeroTwo : triangleEdge 0 ≠ triangleEdge 2 := by
    intro heq
    have hvalue := congrArg Subtype.val heq
    change s(firstVertex, secondVertex) =
      s(secondVertex, thirdVertex) at hvalue
    rw [Sym2.eq_iff] at hvalue
    rcases hvalue with ⟨hfirstEqSecond, _⟩ | ⟨hfirstEqThird, _⟩
    · exact hfirstSecond.ne (congrArg Subtype.val hfirstEqSecond)
    · exact hfirstThird.ne (congrArg Subtype.val hfirstEqThird)
  have honeTwo : triangleEdge 1 ≠ triangleEdge 2 := by
    intro heq
    have hvalue := congrArg Subtype.val heq
    change s(firstVertex, thirdVertex) =
      s(secondVertex, thirdVertex) at hvalue
    rw [Sym2.eq_iff] at hvalue
    rcases hvalue with ⟨hfirstEqSecond, _⟩ | ⟨hfirstEqThird, _⟩
    · exact hfirstSecond.ne (congrArg Subtype.val hfirstEqSecond)
    · exact hfirstThird.ne (congrArg Subtype.val hfirstEqThird)
  have hinjective : Function.Injective triangleEdge := by
    intro left right heq
    fin_cases left <;> fin_cases right
    · rfl
    · exact False.elim (hzeroOne heq)
    · exact False.elim (hzeroTwo heq)
    · exact False.elim (hzeroOne heq.symm)
    · rfl
    · exact False.elim (honeTwo heq)
    · exact False.elim (hzeroTwo heq.symm)
    · exact False.elim (honeTwo heq.symm)
    · rfl
  calc
    3 = Fintype.card (Fin 3) := by simp
    _ ≤ Fintype.card H.edgeSet :=
      Fintype.card_le_of_injective triangleEdge hinjective
    _ = Nat.card H.edgeSet := Nat.card_eq_fintype_card.symm

/-- A cubic graph triangle has at most three edges leaving its three
vertices. -/
theorem card_triangle_crossingEdgeFinset_le_three
    (hregular : G.IsRegularOfDegree 3)
    {first second third : V}
    (hfirstSecond : G.Adj first second)
    (hfirstThird : G.Adj first third)
    (hsecondThird : G.Adj second third) :
    (crossingEdgeFinset G (fun vertex => vertex ∈
      ({first, second, third} : Finset V))).card ≤ 3 := by
  let side : V → Prop := fun vertex => vertex ∈
    ({first, second, third} : Finset V)
  have hvertices : Nat.card {vertex : V // side vertex} = 3 := by
    simpa [side] using natCard_triangleSide_eq_three
      hfirstSecond.ne hfirstThird.ne hsecondThird.ne
  have hinternal :
      3 ≤ Nat.card (G.induce {vertex | side vertex}).edgeSet := by
    simpa [side] using three_le_triangle_induced_edgeFinset_card
      hfirstSecond hfirstThird hsecondThird
  have hcount :
      (crossingEdgeFinset G side).card +
          2 * Nat.card (G.induce {vertex | side vertex}).edgeSet =
        3 * Nat.card {vertex : V // side vertex} :=
    card_crossingEdgeFinset_add_twice_internal_eq_three_mul
      hregular side
  rw [hvertices] at hcount
  simpa [side] using (show (crossingEdgeFinset G side).card ≤ 3 by omega)

/-- The three named edges of a graph triangle give a cycle entirely on its
three-vertex side. -/
theorem hasCycleOnSide_triangle
    {first second third : V}
    (hfirstSecond : G.Adj first second)
    (hfirstThird : G.Adj first third)
    (hsecondThird : G.Adj second third) :
    HasCycleOnSide G (fun vertex => vertex ∈
      ({first, second, third} : Finset V)) := by
  let triangleWalk : G.Walk first first :=
    SimpleGraph.Walk.cons hfirstSecond
      (SimpleGraph.Walk.cons hsecondThird
        (SimpleGraph.Walk.cons hfirstThird.symm SimpleGraph.Walk.nil))
  have hcycle : triangleWalk.IsCycle := by
    simp [triangleWalk, SimpleGraph.Walk.cons_isCycle_iff,
      SimpleGraph.Walk.cons_isPath_iff,
      hfirstSecond.ne, hfirstThird.ne, hsecondThird.ne,
      hfirstSecond.ne.symm, hfirstThird.ne.symm]
  refine ⟨first, by simp, triangleWalk, hcycle, ?_⟩
  intro vertex hvertex
  have hvertex' :
      vertex = first ∨ vertex = second ∨ vertex = third ∨
        vertex = first := by
    simpa [triangleWalk] using hvertex
  rcases hvertex' with rfl | rfl | rfl | rfl <;> simp

/-- A cubic graph cannot have only the three vertices of one triangle. -/
theorem exists_vertex_outside_triangle_of_cubic
    (hregular : G.IsRegularOfDegree 3)
    {first second third : V}
    (hfirstSecond : G.Adj first second)
    (hfirstThird : G.Adj first third)
    (hsecondThird : G.Adj second third) :
    ∃ vertex : V,
      vertex ∉ ({first, second, third} : Finset V) := by
  by_contra houtside
  push Not at houtside
  have hsubset : G.neighborFinset first ⊆
      ({second, third} : Finset V) := by
    intro vertex hneighbor
    have hinside := houtside vertex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hinside
    rcases hinside with rfl | rfl | rfl
    · exact False.elim (G.loopless.irrefl vertex (by simpa using hneighbor))
    · simp
    · simp
  have hcardLe := Finset.card_le_card hsubset
  have hdegree : (G.neighborFinset first).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hregular.degree_eq]
  rw [hdegree] at hcardLe
  have hsecondThird : second ≠ third := hsecondThird.ne
  simp [hsecondThird] at hcardLe

/-- In a cyclically five-edge-connected cubic graph, the complement of a
triangle consists of exactly one vertex.  If the complement contained a
cycle, the triangle cut would have at least five edges; if it is acyclic,
cubic degree counting bounds it by one vertex. -/
theorem natCard_complement_triangle_eq_one_of_cyclicallyFive
    (graphData : Data G)
    (hregular : G.IsRegularOfDegree 3)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {first second third : V}
    (hfirstSecond : G.Adj first second)
    (hfirstThird : G.Adj first third)
    (hsecondThird : G.Adj second third) :
    Nat.card {vertex : V //
      vertex ∉ ({first, second, third} : Finset V)} = 1 := by
  let inside : Finset V := {first, second, third}
  let outsideSide : V → Prop := fun vertex => vertex ∉ inside
  have hboundaryLe :
      (crossingEdgeFinset G (fun vertex => vertex ∈ inside)).card ≤ 3 := by
    simpa [inside] using card_triangle_crossingEdgeFinset_le_three
      hregular hfirstSecond hfirstThird hsecondThird
  have hinsideCycle :
      HasCycleOnSide G (fun vertex => vertex ∈ inside) := by
    simpa [inside] using hasCycleOnSide_triangle
      hfirstSecond hfirstThird hsecondThird
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
  rcases exists_vertex_outside_triangle_of_cubic hregular
      hfirstSecond hfirstThird hsecondThird with
    ⟨outside, houtside⟩
  have hnonempty : Nonempty {vertex : V // outsideSide vertex} :=
    ⟨⟨outside, by simpa [outsideSide, inside] using houtside⟩⟩
  let outsideCarrierEquiv :
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
      (crossingEdgeFinset G outsideSide).card ≤ 3 := by
    rw [hboundaryEq]
    exact hboundaryLe
  have hcount :=
    card_crossingEdgeFinset_add_twice_internal_eq_three_mul
      hregular outsideSide
  have hpositive : 0 < Nat.card {vertex : V // outsideSide vertex} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr hnonempty
  have houtsideCard :
      Nat.card {vertex : V // outsideSide vertex} = 1 := by
    omega
  simpa [outsideSide, inside] using houtsideCard

/-- A three-vertex triangle with a one-vertex complement exhausts a
four-vertex finite carrier. -/
theorem fintype_card_eq_four_of_triangle_complement_natCard_eq_one
    {first second third : V}
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hcomplement : Nat.card {vertex : V //
      vertex ∉ ({first, second, third} : Finset V)} = 1) :
    Fintype.card V = 4 := by
  let inside : Finset V := {first, second, third}
  have hinsideCard :
      Fintype.card {vertex : V // vertex ∈ inside} = 3 := by
    rw [← Nat.card_eq_fintype_card]
    simpa [inside] using natCard_triangleSide_eq_three
      hfirstSecond hfirstThird hsecondThird
  have houtsideCard :
      Fintype.card {vertex : V // vertex ∉ inside} = 1 := by
    rw [← Nat.card_eq_fintype_card]
    simpa [inside] using hcomplement
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
  omega

/-- A cyclically five-edge-connected graph-backed minimal Tait
counterexample is triangle-free.  A common neighbor of adjacent vertices
would form a triangle whose complement is one vertex, while every simple
graph on four vertices has the endpoint-xor Tait coloring above. -/
theorem no_common_neighbor_of_cyclicallyFive
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {first second : V} (hfirstSecond : G.Adj first second) :
    ∀ common, G.Adj first common → G.Adj second common → False := by
  intro common hfirstCommon hsecondCommon
  have hregular : G.IsRegularOfDegree 3 :=
    graphData.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic
  have hcomplement :=
    natCard_complement_triangle_eq_one_of_cyclicallyFive
      graphData hregular hcyclic hfirstSecond hfirstCommon hsecondCommon
  have hcard : Fintype.card V = 4 :=
    fintype_card_eq_four_of_triangle_complement_natCard_eq_one
      hfirstSecond.ne hfirstCommon.ne hsecondCommon.ne hcomplement
  exact (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
    graphData minimal) (exists_taitEdgeColoring_of_card_eq_four G hcard)

/-- Cyclic five-edge-connectivity discharges the final simplicity premise
of the canonical recovered adjacent-pair boundary, yielding its planar
cyclic order and compatible deleted Tait coloring from minimality alone. -/
theorem exists_cyclicallyOrdered_deletedColoring_of_cyclicallyFive
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {first second : V} (hadj : G.Adj first second) :
    HasCyclicallyOrderedCompatibleDeletedColoring
      graphData first second := by
  exact exists_cyclicallyOrdered_deletedColoring_of_no_common_neighbor
    graphData minimal hadj
      (no_common_neighbor_of_cyclicallyFive graphData minimal hcyclic hadj)

/-- Every adjacent pair in cyclic five-edge-connected minimal normal form
therefore carries the complete finite cyclic Kempe profile used by the
fusion-chain transfer system. -/
theorem exists_cyclicKempeTransferProfile_of_cyclicallyFive
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {first second : V} (hadj : G.Adj first second) :
    HasCyclicKempeTransferProfile graphData first second := by
  exact (exists_cyclicallyOrdered_deletedColoring_of_cyclicallyFive
    graphData minimal hcyclic hadj).hasCyclicKempeTransferProfile
      graphData minimal

/-- Every adjacent pair in cyclic five-edge-connected minimal normal form
therefore reaches the complete rotation-ordered fusion-chain resolution:
a strict primal circuit, disjoint fusion supports, or the certified
single-cross rebase-pumping residual. -/
theorem exists_rotationOrderedCyclicKempeFusionChainNormalForm_of_cyclicallyFive
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {first second : V} (hadj : G.Adj first second) :
    HasRotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal first second := by
  exact hasRotationOrderedFusionChainNormalForm_of_cyclicKempeTransferProfile
    graphData minimal
      (exists_cyclicKempeTransferProfile_of_cyclicallyFive
        graphData minimal hcyclic hadj)

end

end GoertzelV24MinimalTriangleFree

end Mettapedia.GraphTheory.FourColor
