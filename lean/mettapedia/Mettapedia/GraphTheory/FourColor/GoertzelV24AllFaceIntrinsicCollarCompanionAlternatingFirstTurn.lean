import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingResolution

/-! First-change normalization for coordinate-generic closed support routes. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

/-- In a triangle-free simple graph, three pairwise adjacent edges have one
common endpoint. -/
theorem lineGraphCommonVertex_mem_third_of_no_triangle
    {W : Type*} {H : SimpleGraph W}
    {first second third : H.edgeSet}
    (hfirstSecond : H.lineGraph.Adj first second)
    (hfirstThird : H.lineGraph.Adj first third)
    (hsecondThird : H.lineGraph.Adj second third)
    (hnoTriangle : ∀ firstVertex secondVertex thirdVertex : W,
      H.Adj firstVertex secondVertex →
        H.Adj firstVertex thirdVertex →
          H.Adj secondVertex thirdVertex → False) :
    SimpleGraph.lineGraphCommonVertex hfirstSecond ∈
      (third.1 : Sym2 W) := by
  let firstSecondVertex :=
    SimpleGraph.lineGraphCommonVertex hfirstSecond
  let firstThirdVertex :=
    SimpleGraph.lineGraphCommonVertex hfirstThird
  let secondThirdVertex :=
    SimpleGraph.lineGraphCommonVertex hsecondThird
  by_contra hnotThird
  change firstSecondVertex ∉ (third.1 : Sym2 W) at hnotThird
  have hfirstSecond_ne_firstThird :
      firstSecondVertex ≠ firstThirdVertex := by
    intro heq
    apply hnotThird
    rw [heq]
    exact SimpleGraph.lineGraphCommonVertex_mem_right hfirstThird
  have hfirstSecond_ne_secondThird :
      firstSecondVertex ≠ secondThirdVertex := by
    intro heq
    apply hnotThird
    rw [heq]
    exact SimpleGraph.lineGraphCommonVertex_mem_right hsecondThird
  have hfirstThird_ne_secondThird :
      firstThirdVertex ≠ secondThirdVertex := by
    intro heq
    have hfirstThird_mem_second : firstThirdVertex ∈
        (second.1 : Sym2 W) := by
      rw [heq]
      exact SimpleGraph.lineGraphCommonVertex_mem_left hsecondThird
    have hcommon : firstThirdVertex = firstSecondVertex :=
      SimpleGraph.lineGraphCommonVertex_unique hfirstSecond
        (SimpleGraph.lineGraphCommonVertex_mem_left hfirstThird)
        hfirstThird_mem_second
    exact hfirstSecond_ne_firstThird hcommon.symm
  have hfirstEdge : H.Adj firstSecondVertex firstThirdVertex := by
    have hedge : first.1 = s(firstSecondVertex, firstThirdVertex) :=
      (Sym2.mem_and_mem_iff hfirstSecond_ne_firstThird).1 ⟨
        SimpleGraph.lineGraphCommonVertex_mem_left hfirstSecond,
        SimpleGraph.lineGraphCommonVertex_mem_left hfirstThird⟩
    have hadj := first.2
    rw [hedge] at hadj
    exact hadj
  have hsecondEdge : H.Adj firstSecondVertex secondThirdVertex := by
    have hedge : second.1 = s(firstSecondVertex, secondThirdVertex) :=
      (Sym2.mem_and_mem_iff hfirstSecond_ne_secondThird).1 ⟨
        SimpleGraph.lineGraphCommonVertex_mem_right hfirstSecond,
        SimpleGraph.lineGraphCommonVertex_mem_left hsecondThird⟩
    have hadj := second.2
    rw [hedge] at hadj
    exact hadj
  have hthirdEdge : H.Adj firstThirdVertex secondThirdVertex := by
    have hedge : third.1 = s(firstThirdVertex, secondThirdVertex) :=
      (Sym2.mem_and_mem_iff hfirstThird_ne_secondThird).1 ⟨
        SimpleGraph.lineGraphCommonVertex_mem_right hfirstThird,
        SimpleGraph.lineGraphCommonVertex_mem_right hsecondThird⟩
    have hadj := third.2
    rw [hedge] at hadj
    exact hadj
  exact hnoTriangle firstSecondVertex firstThirdVertex secondThirdVertex
    hfirstEdge hsecondEdge hthirdEdge

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- A chain for `primary` is either also a chain for `preferred`, or its
first failed preferred step has a preferred prefix. -/
theorem isChain_or_exists_first_adjacent_not
    {State : Type*} {primary preferred : State → State → Prop}
    {states : List State} (hprimary : states.IsChain primary) :
    states.IsChain preferred ∨
      ∃ (before : List State) (first second : State) (after : List State),
        states = before ++ first :: second :: after ∧
          primary first second ∧
          ¬preferred first second ∧
          (before ++ [first]).IsChain preferred := by
  classical
  induction hprimary with
  | nil => exact Or.inl .nil
  | singleton state => exact Or.inl (.singleton state)
  | @cons_cons first second rest hstep htail ih =>
      by_cases hpreferred : preferred first second
      · rcases ih with htailPreferred |
          ⟨before, changedFirst, changedSecond, after,
            htailEq, hchangedStep, hchangedPreferred, hprefix⟩
        · exact Or.inl (.cons_cons hpreferred htailPreferred)
        · refine Or.inr ⟨first :: before, changedFirst, changedSecond,
            after, ?_, hchangedStep, hchangedPreferred, ?_⟩
          · simp [htailEq]
          · cases before with
            | nil =>
                simp only [List.nil_append, List.cons.injEq] at htailEq
                rcases htailEq with ⟨hfirst, _hrest⟩
                subst changedFirst
                exact .cons_cons hpreferred (.singleton second)
            | cons head before =>
                simp only [List.cons_append, List.cons.injEq] at htailEq
                have hhead : second = head := htailEq.1
                subst head
                exact .cons_cons hpreferred hprefix
      · exact Or.inr
          ⟨[], first, second, rest, rfl, hstep, hpreferred,
            .singleton first⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}
  {collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge}
  {sourceEscape : sourceNormal.KempeOrbitAdjacentEscape}
  {coordinate : Bool}
  {turn : collar.ScalarCompanionTurn sourceEscape coordinate}

namespace ScalarCompanionTurn

variable (turn : collar.ScalarCompanionTurn sourceEscape coordinate)

/-- Canonical primal junction of a signed turn. -/
noncomputable def junction : collar.commonCoreVertex :=
  SimpleGraph.lineGraphCommonVertex turn.firstSecond

theorem junction_mem_first :
    turn.junction ∈ (turn.first.1 : Sym2 collar.commonCoreVertex) :=
  SimpleGraph.lineGraphCommonVertex_mem_left turn.firstSecond

theorem junction_mem_second :
    turn.junction ∈ (turn.second.1 : Sym2 collar.commonCoreVertex) :=
  SimpleGraph.lineGraphCommonVertex_mem_right turn.firstSecond

/-- Triangle-freeness of a minimal counterexample makes the canonical
junction incident to the transverse edge as well. -/
theorem junction_mem_third :
    turn.junction ∈ (turn.third.1 : Sym2 collar.commonCoreVertex) := by
  apply lineGraphCommonVertex_mem_third_of_no_triangle
    turn.firstSecond turn.firstThird turn.secondThird
  intro firstVertex secondVertex thirdVertex
    hfirstSecond hfirstThird hsecondThird
  exact
    GoertzelV24MinimalTriangleFree.no_common_neighbor_of_vertexMinimalTaitCounterexample
      graphData minimal hfirstSecond thirdVertex hfirstThird hsecondThird

end ScalarCompanionTurn

namespace ScalarCompanionTurn.ComplementarySupportCorner

variable (corner : turn.ComplementarySupportCorner)

/-- The support route launches at the canonical primal junction of its
signed turn. -/
theorem complementarySupportJunction_eq_junction :
    corner.complementarySupportJunction = turn.junction := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
    corner.incoming_transverse_adj
  · change turn.junction ∈
      (corner.incoming.1 : Sym2 collar.commonCoreVertex)
    rcases corner.orientation with ⟨hincoming, _hbypassed⟩ |
        ⟨hincoming, _hbypassed⟩
    · rw [hincoming]
      exact turn.junction_mem_first
    · rw [hincoming]
      exact turn.junction_mem_second
  · change turn.junction ∈
      (turn.third.1 : Sym2 collar.commonCoreVertex)
    exact turn.junction_mem_third

end ScalarCompanionTurn.ComplementarySupportCorner

namespace ScalarCompanionTurn.ComplementarySupportCorner.ClosedSupportRoute

variable {corner : turn.ComplementarySupportCorner}

/-- The first companion change after linearizing a rooted closed support
cycle, together with the straight prefix leading to it. -/
structure FirstInteriorTransverseTurn (route : corner.ClosedSupportRoute) where
  interior : route.InteriorTransverseTurn
  prefixStraight : (interior.before ++ [interior.first]).IsChain
    (fun first second =>
      (corner.supportEdgeColorState first).companionColor =
        (corner.supportEdgeColorState second).companionColor)

namespace FirstInteriorTransverseTurn

variable {route : corner.ClosedSupportRoute}
  (firstTurn : route.FirstInteriorTransverseTurn)

/-- The normalized first change emits the same full next turn as its
underlying interior event. -/
noncomputable def toScalarCompanionTurn :
    collar.ScalarCompanionTurn sourceEscape (!coordinate) :=
  firstTurn.interior.toScalarCompanionTurn

/-- Oriented support-cycle edge word from the rooted launch through the
last edge before the first companion change. -/
def straightEdgeWord :
    List corner.complementarySupportGraph.edgeSet :=
  firstTurn.interior.before ++ [firstTurn.interior.first]

theorem straightEdgeWord_ne_nil : firstTurn.straightEdgeWord ≠ [] := by
  unfold straightEdgeWord
  exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)

/-- The straight word is literally an initial segment of the rooted support
cycle, not only a list of edges with matching colors. -/
theorem straightEdgeWord_isPrefix :
    firstTurn.straightEdgeWord <+:
      route.rootedAtLaunch.cycle.edgeSubtypeSupport := by
  refine ⟨firstTurn.interior.second :: firstTurn.interior.after, ?_⟩
  rw [firstTurn.interior.word_eq]
  simp only [straightEdgeWord, List.append_assoc, List.singleton_append]

/-- No earlier adjacent pair on the selected arc changes companion. -/
theorem straightEdgeWord_isChain :
    firstTurn.straightEdgeWord.IsChain (fun first second =>
      (corner.supportEdgeColorState first).companionColor =
        (corner.supportEdgeColorState second).companionColor) :=
  firstTurn.prefixStraight

/-- Primal junction at which the first later companion change occurs. -/
noncomputable def finishJunction : collar.commonCoreVertex :=
  SimpleGraph.lineGraphCommonVertex firstTurn.interior.firstSecond

/-- The emitted turn is based exactly at the finish of the normalized
straight arc. -/
theorem toScalarCompanionTurn_junction_eq_finishJunction :
    firstTurn.toScalarCompanionTurn.junction =
      firstTurn.finishJunction := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
    firstTurn.toScalarCompanionTurn.firstSecond
  · change firstTurn.finishJunction ∈
      ((corner.supportEdgeAmbientEdge firstTurn.interior.first).1 :
        Sym2 collar.commonCoreVertex)
    rw [supportEdgeAmbientEdge_val]
    exact SimpleGraph.lineGraphCommonVertex_mem_left
      firstTurn.interior.firstSecond
  · change firstTurn.finishJunction ∈
      ((corner.supportEdgeAmbientEdge firstTurn.interior.second).1 :
        Sym2 collar.commonCoreVertex)
    rw [supportEdgeAmbientEdge_val]
    exact SimpleGraph.lineGraphCommonVertex_mem_right
      firstTurn.interior.firstSecond

/-- The selected finish is a strictly internal vertex of the rooted simple
support cycle and therefore differs from the launch junction. -/
theorem finishJunction_eq_getVert_and_ne_launch :
    firstTurn.finishJunction =
        route.rootedAtLaunch.cycle.getVert
          (firstTurn.interior.before.length + 1) ∧
      firstTurn.finishJunction ≠ corner.complementarySupportJunction := by
  classical
  let strand := route.rootedAtLaunch
  let supportCycle := strand.cycle
  have hlength := congrArg List.length firstTurn.interior.word_eq
  rw [supportCycle.edgeSubtypeSupport_length] at hlength
  simp only [List.length_append, List.length_cons] at hlength
  have hpositive : 0 < supportCycle.length :=
    lt_of_lt_of_le (by omega) strand.cycle_isCycle.three_le_length
  let lineWalk := supportCycle.lineGraphWalkOfTrail hpositive
    strand.cycle_isCycle.isTrail
  have hlineLength : lineWalk.length = supportCycle.length - 1 :=
    supportCycle.lineGraphWalkOfTrail_length hpositive
      strand.cycle_isCycle.isTrail
  have hlineSupport : lineWalk.support =
      firstTurn.interior.before ++
        firstTurn.interior.first :: firstTurn.interior.second ::
          firstTurn.interior.after := by
    calc
      lineWalk.support = supportCycle.edgeSubtypeSupport := by
        dsimp only [lineWalk]
        exact supportCycle.lineGraphWalkOfTrail_support hpositive
          strand.cycle_isCycle.isTrail
      _ = firstTurn.interior.before ++
          firstTurn.interior.first :: firstTurn.interior.second ::
            firstTurn.interior.after := firstTurn.interior.word_eq
  have hposition : firstTurn.interior.before.length < lineWalk.length := by
    rw [hlineLength]
    omega
  let position : Fin lineWalk.length :=
    ⟨firstTurn.interior.before.length, hposition⟩
  have hfirstValue : lineWalk.getVert position.val =
      firstTurn.interior.first := by
    rw [lineWalk.getVert_eq_support_getElem (by omega)]
    have hoption : lineWalk.support[position.val]? =
        some firstTurn.interior.first := by
      rw [hlineSupport]
      change (firstTurn.interior.before ++
        firstTurn.interior.first :: firstTurn.interior.second ::
          firstTurn.interior.after)[firstTurn.interior.before.length]? =
            some firstTurn.interior.first
      rw [List.getElem?_append]
      rw [if_neg (Nat.lt_irrefl _)]
      rw [Nat.sub_self, List.getElem?_cons_zero]
    rcases List.getElem?_eq_some_iff.mp hoption with ⟨_hindex, heq⟩
    exact heq
  have hsecondValue : lineWalk.getVert (position.val + 1) =
      firstTurn.interior.second := by
    rw [lineWalk.getVert_eq_support_getElem (by omega)]
    have hoption : lineWalk.support[position.val + 1]? =
        some firstTurn.interior.second := by
      rw [hlineSupport]
      change (firstTurn.interior.before ++
        firstTurn.interior.first :: firstTurn.interior.second ::
          firstTurn.interior.after)[firstTurn.interior.before.length + 1]? =
            some firstTurn.interior.second
      rw [List.getElem?_append]
      rw [if_neg (by omega)]
      have hsub : firstTurn.interior.before.length + 1 -
          firstTurn.interior.before.length = 1 := by omega
      rw [hsub, List.getElem?_cons_succ, List.getElem?_cons_zero]
    rcases List.getElem?_eq_some_iff.mp hoption with ⟨_hindex, heq⟩
    exact heq
  have hjunction : firstTurn.finishJunction =
      lineWalk.lineGraphJunctionAt position := by
    apply SimpleGraph.lineGraphCommonVertex_unique
      (lineWalk.adj_getVert_succ position.isLt)
    · rw [hfirstValue]
      exact SimpleGraph.lineGraphCommonVertex_mem_left
        firstTurn.interior.firstSecond
    · rw [hsecondValue]
      exact SimpleGraph.lineGraphCommonVertex_mem_right
        firstTurn.interior.firstSecond
  have hvertex : firstTurn.finishJunction =
      supportCycle.getVert (firstTurn.interior.before.length + 1) := by
    rw [hjunction]
    exact supportCycle.lineGraphWalkOfTrail_lineGraphJunctionAt_eq_getVert
      hpositive strand.cycle_isCycle.isTrail position
  have hvertex' : firstTurn.finishJunction =
      strand.cycle.getVert (firstTurn.interior.before.length + 1) := by
    simpa only [supportCycle] using hvertex
  have hpositionLt : firstTurn.interior.before.length + 1 <
      strand.cycle.length := by
    dsimp only [supportCycle] at hlength
    omega
  refine ⟨hvertex', ?_⟩
  rw [hvertex']
  intro heq
  have hendpoint :=
    (strand.cycle_isCycle.getVert_endpoint_iff
      (Nat.le_of_lt hpositionLt)).1 heq
  omega

/-- A normalized interior transition moves to a genuinely different
primal junction. -/
theorem toScalarCompanionTurn_junction_ne_source :
    firstTurn.toScalarCompanionTurn.junction ≠ turn.junction := by
  rw [firstTurn.toScalarCompanionTurn_junction_eq_finishJunction]
  have hne := firstTurn.finishJunction_eq_getVert_and_ne_launch.2
  rw [corner.complementarySupportJunction_eq_junction] at hne
  exact hne

end FirstInteriorTransverseTurn

/-- A rooted closed route is consumed at its first companion change by a
boundary Kempe action, or that first change is an interior transverse turn
with a certified straight prefix. -/
theorem kempeAction_and_sameBaseReentry_or_firstInteriorTransverseTurn
    (route : corner.ClosedSupportRoute) :
    (∃ representative : IntrinsicCollarTerminalRepresentative
        collar.intrinsicCollarPortOverlapProfile,
      ChargedTerminalKempeAction collar sourceEscape coordinate
          representative ∧
        (sourceNormal.SameBaseKempeReentry sourceEscape ∨
          collar.targetNormal.SameBaseKempeReentry collar.targetEscape)) ∨
      Nonempty route.FirstInteriorTransverseTurn := by
  let strand := route.rootedAtLaunch
  have hchain : strand.cycle.edgeSubtypeSupport.IsChain
      corner.complementarySupportGraph.lineGraph.Adj :=
    strand.cycle_isCycle.isTrail.edgeSubtypeSupport_isChain
  rcases isChain_or_exists_first_adjacent_not
      (preferred := fun first second =>
        (corner.supportEdgeColorState first).companionColor =
          (corner.supportEdgeColorState second).companionColor)
      hchain with hstraight |
      ⟨before, first, second, after, hword, hadjacent,
        hcompanion, hprefix⟩
  · have heq := map_eq_of_mem_of_isChain hstraight
      (List.head_mem strand.cycleEdgeWord_ne_nil)
      (List.getLast_mem strand.cycleEdgeWord_ne_nil)
    exact False.elim (strand.rootCompanionColor_ne heq)
  · rcases corner.changedSupportEdges_boundaryPort_or_transverseEmission
        first second hadjacent hcompanion with
      hsource | htarget | hinterior
    · rcases hsource with ⟨sourcePort, hvertex⟩
      rcases corner.changedSupportEdges_sourcePort_kempeAction_and_sameBaseReentry
          first second hadjacent hcompanion sourcePort hvertex with
        ⟨action, hreentry⟩
      exact Or.inl ⟨Sum.inl sourcePort, action, hreentry⟩
    · rcases htarget with ⟨targetPort, hvertex⟩
      let hnoOverlap :=
        corner.no_portOverlap_of_supportEdge_adjacent_at_targetPort
          first second hadjacent targetPort hvertex
      let unmatched :=
        corner.unmatchedTargetPortOfNoOverlap targetPort hnoOverlap
      have haction :=
        corner.changedSupportEdges_targetPort_kempeAction_and_sameBaseReentry
          first second hadjacent hcompanion targetPort hvertex
      exact Or.inl ⟨Sum.inr unmatched, haction⟩
    · rcases hinterior with
        ⟨thirdEdge, hfirstThird, hsecondThird, hdiscrepancy, _hsupport⟩
      let interior : route.InteriorTransverseTurn := {
        before := before
        first := first
        second := second
        after := after
        firstSecond := hadjacent
        thirdEdge := thirdEdge
        word_eq := hword
        companion_ne := hcompanion
        firstThird := hfirstThird
        secondThird := hsecondThird
        discrepancy := hdiscrepancy }
      exact Or.inr ⟨{
        interior := interior
        prefixStraight := hprefix }⟩

end ScalarCompanionTurn.ComplementarySupportCorner.ClosedSupportRoute
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
