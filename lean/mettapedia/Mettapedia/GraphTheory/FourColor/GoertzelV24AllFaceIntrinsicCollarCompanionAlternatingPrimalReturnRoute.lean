import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingPrimalReturnCorner

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CorridorPumping
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

namespace GoertzelV24AlternatingPrimalReturn

variable {W : Type*} {H : SimpleGraph W}

@[simp]
theorem edgeSubtypeSupport_copy
    {start finish start' finish' : W}
    (walk : H.Walk start finish)
    (hstart : start = start') (hfinish : finish = finish') :
    (walk.copy hstart hfinish).edgeSubtypeSupport =
      walk.edgeSubtypeSupport := by
  unfold SimpleGraph.Walk.edgeSubtypeSupport
  rw [SimpleGraph.Walk.darts_copy]

@[simp]
theorem edgeSubtypeSupport_append
    {start middle finish : W}
    (first : H.Walk start middle) (second : H.Walk middle finish) :
    (first.append second).edgeSubtypeSupport =
      first.edgeSubtypeSupport ++ second.edgeSubtypeSupport := by
  unfold SimpleGraph.Walk.edgeSubtypeSupport
  rw [SimpleGraph.Walk.darts_append, List.map_append]

@[simp]
theorem edgeSubtypeSupport_reverse
    {start finish : W} (walk : H.Walk start finish) :
    walk.reverse.edgeSubtypeSupport =
      walk.edgeSubtypeSupport.reverse := by
  apply (List.map_injective_iff.mpr Subtype.val_injective)
  simp only [SimpleGraph.Walk.edgeSubtypeSupport_map_val,
    SimpleGraph.Walk.edges_reverse, List.map_reverse]

end GoertzelV24AlternatingPrimalReturn

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

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

namespace ScalarCompanionTurn.NextTurnWitness

/-- Transporting an exact next-turn witness across equality of its source
turn does not change the finite state emitted by the witness. -/
theorem ofTurn_nextTurn_transport
    {coordinate : Bool}
    {source target : collar.ScalarCompanionTurn sourceEscape coordinate}
    (hsource : source = target)
    (witness : target.NextTurnWitness) :
    ScalarCompanionTurnState.ofTurn
        (hsource.symm ▸ witness).nextTurn =
      ScalarCompanionTurnState.ofTurn witness.nextTurn := by
  cases hsource
  rfl

end ScalarCompanionTurn.NextTurnWitness

namespace ScalarCompanionTurnState.ImmediateReturnBoundary

variable (boundary : ScalarCompanionTurnState.ImmediateReturnBoundary
  (collar := collar) (sourceEscape := sourceEscape))

theorem ScalarCompanionTurn.eq_of_fields_eq
    {coordinate : Bool}
    (left right : collar.ScalarCompanionTurn sourceEscape coordinate)
    (hfirst : left.first = right.first)
    (hsecond : left.second = right.second)
    (hthird : left.third = right.third) : left = right := by
  cases left
  cases right
  simp only [ScalarCompanionTurn.mk.injEq]
  exact ⟨hfirst, hsecond, hthird⟩

abbrev returnCorner :=
  boundary.departure.witness.corner.returnCorner

theorem returnSupportGraph_eq_arrivalSupportGraph :
    boundary.returnCorner.complementarySupportGraph =
      boundary.arrival.witness.corner.complementarySupportGraph := by
  change collar.coordinateDiscrepancySupportGraph sourceEscape
      (!(!boundary.middle.1.coordinate)) =
    collar.coordinateDiscrepancySupportGraph sourceEscape
      (!boundary.before.1.coordinate)
  rw [boundary.middle_coordinate_eq_not_before]
  cases boundary.before.1.coordinate <;> rfl

theorem returnCorner_junction_eq_middle :
    boundary.returnCorner.complementarySupportJunction =
      boundary.middle.junction := by
  rw [ScalarCompanionTurn.ComplementarySupportCorner.complementarySupportJunction_eq_junction]
  exact boundary.departure.witness.corner.toggleTurn_junction_eq

/-- The identity-on-ambient-edges transport from the arrival scalar support
graph to the canonically equal return scalar support graph. -/
def arrivalSupportEdgeInReturnGraph
    (edge : boundary.arrival.witness.corner.complementarySupportGraph.edgeSet) :
    boundary.returnCorner.complementarySupportGraph.edgeSet :=
  ⟨edge.1, by
    rw [boundary.returnSupportGraph_eq_arrivalSupportGraph]
    exact edge.2⟩

@[simp]
theorem arrivalSupportEdgeInReturnGraph_val
    (edge : boundary.arrival.witness.corner.complementarySupportGraph.edgeSet) :
    (boundary.arrivalSupportEdgeInReturnGraph edge).1 = edge.1 := rfl

theorem arrivalSupportEdgeInReturnGraph_lineGraph_adj
    {first second :
      boundary.arrival.witness.corner.complementarySupportGraph.edgeSet}
    (hadjacent :
      boundary.arrival.witness.corner.complementarySupportGraph.lineGraph.Adj
        first second) :
    boundary.returnCorner.complementarySupportGraph.lineGraph.Adj
      (boundary.arrivalSupportEdgeInReturnGraph first)
      (boundary.arrivalSupportEdgeInReturnGraph second) := by
  rcases SimpleGraph.lineGraph_adj_iff_exists.mp hadjacent with
    ⟨hne, vertex, hfirst, hsecond⟩
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  refine ⟨?_, vertex, ?_, ?_⟩
  · intro heq
    apply hne
    apply Subtype.ext
    have hvalue := congrArg
      (fun edge : boundary.returnCorner.complementarySupportGraph.edgeSet =>
        edge.1) heq
    simpa only [arrivalSupportEdgeInReturnGraph_val] using hvalue
  · exact hfirst
  · exact hsecond

theorem arrival_finishJunction_eq_middle :
    boundary.arrival.witness.interior.finishJunction =
      boundary.middle.junction := by
  calc
    boundary.arrival.witness.interior.finishJunction =
        boundary.arrival.witness.interior.toScalarCompanionTurn.junction :=
      boundary.arrival.witness.interior.toScalarCompanionTurn_junction_eq_finishJunction.symm
    _ = boundary.arrival.witness.nextTurn.junction := rfl
    _ = (ScalarCompanionTurnState.ofTurn
          boundary.arrival.witness.nextTurn).junction :=
      (ScalarCompanionTurnState.ofTurn_junction _).symm
    _ = boundary.middle.junction := congrArg
      ScalarCompanionTurnState.junction
      boundary.arrival.target_eq_ofTurn.symm

noncomputable def arrivalCycleInReturnGraph :
    boundary.returnCorner.complementarySupportGraph.Walk
      boundary.arrival.witness.corner.complementarySupportJunction
      boundary.arrival.witness.corner.complementarySupportJunction :=
  boundary.arrival.witness.route.rootedAtLaunch.cycle.mapLe (by
    rw [boundary.returnSupportGraph_eq_arrivalSupportGraph])

theorem arrivalCycleInReturnGraph_isCycle :
    boundary.arrivalCycleInReturnGraph.IsCycle := by
  unfold arrivalCycleInReturnGraph
  exact boundary.arrival.witness.route.rootedAtLaunch.cycle_isCycle.mapLe _

theorem middle_mem_arrivalCycleInReturnGraph_support :
    boundary.middle.junction ∈
      boundary.arrivalCycleInReturnGraph.support := by
  rw [arrivalCycleInReturnGraph,
    SimpleGraph.Walk.support_mapLe_eq_support]
  rw [← boundary.arrival_finishJunction_eq_middle]
  rw [boundary.arrival.witness.interior.finishJunction_eq_getVert_and_ne_launch.1]
  exact SimpleGraph.Walk.getVert_mem_support _ _

@[simp]
theorem arrivalCycleInReturnGraph_length :
    boundary.arrivalCycleInReturnGraph.length =
      boundary.arrival.witness.route.rootedAtLaunch.cycle.length := by
  calc
    boundary.arrivalCycleInReturnGraph.length =
        boundary.arrivalCycleInReturnGraph.edges.length :=
      boundary.arrivalCycleInReturnGraph.length_edges.symm
    _ = boundary.arrival.witness.route.rootedAtLaunch.cycle.edges.length := by
      exact congrArg List.length
        (SimpleGraph.Walk.edges_mapLe_eq_edges
          (by rw [boundary.returnSupportGraph_eq_arrivalSupportGraph])
          boundary.arrival.witness.route.rootedAtLaunch.cycle)
    _ = boundary.arrival.witness.route.rootedAtLaunch.cycle.length :=
      boundary.arrival.witness.route.rootedAtLaunch.cycle.length_edges

@[simp]
theorem arrivalCycleInReturnGraph_support :
    boundary.arrivalCycleInReturnGraph.support =
      boundary.arrival.witness.route.rootedAtLaunch.cycle.support := by
  unfold arrivalCycleInReturnGraph
  exact SimpleGraph.Walk.support_mapLe_eq_support _ _

theorem arrivalCycleInReturnGraph_edgeSubtypeSupport :
    boundary.arrivalCycleInReturnGraph.edgeSubtypeSupport =
      boundary.arrival.witness.route.rootedAtLaunch.cycle.edgeSubtypeSupport.map
        boundary.arrivalSupportEdgeInReturnGraph := by
  apply (List.map_injective_iff.mpr Subtype.val_injective)
  calc
    boundary.arrivalCycleInReturnGraph.edgeSubtypeSupport.map Subtype.val =
        boundary.arrivalCycleInReturnGraph.edges :=
      boundary.arrivalCycleInReturnGraph.edgeSubtypeSupport_map_val
    _ = boundary.arrival.witness.route.rootedAtLaunch.cycle.edges :=
      SimpleGraph.Walk.edges_mapLe_eq_edges _ _
    _ = (boundary.arrival.witness.route.rootedAtLaunch.cycle
          |>.edgeSubtypeSupport.map Subtype.val) :=
      (boundary.arrival.witness.route.rootedAtLaunch.cycle
        |>.edgeSubtypeSupport_map_val).symm
    _ = (boundary.arrival.witness.route.rootedAtLaunch.cycle
          |>.edgeSubtypeSupport.map
            boundary.arrivalSupportEdgeInReturnGraph).map Subtype.val := by
      rw [List.map_map]
      apply List.map_congr_left
      intro edge _hedge
      rfl

theorem arrivalCycleInReturnGraph_getVert_turnPosition :
    boundary.arrivalCycleInReturnGraph.getVert
        boundary.arrival.witness.interior.turnPosition =
      boundary.middle.junction := by
  calc
    boundary.arrivalCycleInReturnGraph.getVert
        boundary.arrival.witness.interior.turnPosition =
        boundary.arrival.witness.route.rootedAtLaunch.cycle.getVert
          boundary.arrival.witness.interior.turnPosition := by
      have hposition : boundary.arrival.witness.interior.turnPosition ≤
          boundary.arrivalCycleInReturnGraph.length := by
        rw [boundary.arrivalCycleInReturnGraph_length]
        exact Nat.le_of_lt
          boundary.arrival.witness.interior.turnPosition_lt_cycleLength
      apply Option.some.inj
      calc
        some (boundary.arrivalCycleInReturnGraph.getVert
            boundary.arrival.witness.interior.turnPosition) =
            boundary.arrivalCycleInReturnGraph.support[
              boundary.arrival.witness.interior.turnPosition]? :=
          boundary.arrivalCycleInReturnGraph.getVert_eq_support_getElem?
            hposition
        _ = boundary.arrival.witness.route.rootedAtLaunch.cycle.support[
              boundary.arrival.witness.interior.turnPosition]? :=
          congrArg
            (fun word => word[
              boundary.arrival.witness.interior.turnPosition]?)
            boundary.arrivalCycleInReturnGraph_support
        _ = some
            (boundary.arrival.witness.route.rootedAtLaunch.cycle.getVert
              boundary.arrival.witness.interior.turnPosition) :=
          (boundary.arrival.witness.route.rootedAtLaunch.cycle
            |>.getVert_eq_support_getElem? (Nat.le_of_lt
              boundary.arrival.witness.interior.turnPosition_lt_cycleLength)).symm
    _ = boundary.arrival.witness.interior.finishJunction :=
      boundary.arrival.witness.interior.finishJunction_eq_getVert_and_ne_launch.1.symm
    _ = boundary.middle.junction := boundary.arrival_finishJunction_eq_middle

theorem arrivalCycleInReturnGraph_takeUntil_middle_length :
    (boundary.arrivalCycleInReturnGraph.takeUntil boundary.middle.junction
      boundary.middle_mem_arrivalCycleInReturnGraph_support).length =
        boundary.arrival.witness.interior.turnPosition := by
  let supportCycle := boundary.arrivalCycleInReturnGraph
  let turnPosition := boundary.arrival.witness.interior.turnPosition
  let middleMem := boundary.middle_mem_arrivalCycleInReturnGraph_support
  apply boundary.arrivalCycleInReturnGraph_isCycle.getVert_injOn
  · simp only [Set.mem_setOf_eq]
    have hne : boundary.middle.junction ≠
        boundary.arrival.witness.corner.complementarySupportJunction := by
      rw [← boundary.arrival_finishJunction_eq_middle]
      exact boundary.arrival.witness.interior
        |>.finishJunction_eq_getVert_and_ne_launch.2
    have hpositive : 0 <
        (supportCycle.takeUntil boundary.middle.junction middleMem).length := by
      apply Nat.pos_of_ne_zero
      intro hzero
      have hget := supportCycle.getVert_length_takeUntil middleMem
      rw [hzero, SimpleGraph.Walk.getVert_zero] at hget
      exact hne hget.symm
    exact ⟨hpositive,
      supportCycle.length_takeUntil_le_length middleMem⟩
  · simp only [Set.mem_setOf_eq]
    constructor
    · change 1 ≤
        boundary.arrival.witness.interior.interior.before.length + 1
      omega
    · rw [show supportCycle.length =
          boundary.arrival.witness.route.rootedAtLaunch.cycle.length by
        exact boundary.arrivalCycleInReturnGraph_length]
      exact Nat.le_of_lt
        boundary.arrival.witness.interior.turnPosition_lt_cycleLength
  · calc
      supportCycle.getVert
          (supportCycle.takeUntil boundary.middle.junction middleMem).length =
          boundary.middle.junction :=
        supportCycle.getVert_length_takeUntil middleMem
      _ = supportCycle.getVert turnPosition := by
        exact boundary.arrivalCycleInReturnGraph_getVert_turnPosition.symm

theorem arrivalCycleInReturnGraph_takeUntil_edgeSubtypeSupport :
    (boundary.arrivalCycleInReturnGraph.takeUntil boundary.middle.junction
      boundary.middle_mem_arrivalCycleInReturnGraph_support
        ).edgeSubtypeSupport =
      boundary.arrival.witness.interior.straightEdgeWord.map
        boundary.arrivalSupportEdgeInReturnGraph := by
  let supportCycle := boundary.arrivalCycleInReturnGraph
  let middleMem := boundary.middle_mem_arrivalCycleInReturnGraph_support
  have hidx :=
    (supportCycle.length_takeUntil middleMem).symm.trans
      boundary.arrivalCycleInReturnGraph_takeUntil_middle_length
  have hprefix :
      (boundary.arrival.witness.route.rootedAtLaunch.cycle
          |>.edgeSubtypeSupport.take
            boundary.arrival.witness.interior.turnPosition) =
        boundary.arrival.witness.interior.straightEdgeWord := by
    have hword :=
      boundary.arrival.witness.interior.supportArc_edgeSubtypeSupport
    simpa only [ScalarCompanionTurn.ComplementarySupportCorner.ClosedSupportRoute.FirstInteriorTransverseTurn.supportArc,
      SimpleGraph.Walk.edgeSubtypeSupport, SimpleGraph.Walk.darts_copy,
      SimpleGraph.Walk.darts_take, List.map_take] using hword
  rw [supportCycle.takeUntil_eq_take middleMem]
  simp only [SimpleGraph.Walk.edgeSubtypeSupport,
    SimpleGraph.Walk.darts_copy, SimpleGraph.Walk.darts_take,
    List.map_take]
  rw [hidx]
  change supportCycle.edgeSubtypeSupport.take
      boundary.arrival.witness.interior.turnPosition =
    boundary.arrival.witness.interior.straightEdgeWord.map
      boundary.arrivalSupportEdgeInReturnGraph
  rw [boundary.arrivalCycleInReturnGraph_edgeSubtypeSupport,
    ← List.map_take, hprefix]

theorem returnCorner_transport_companionColor
    (edge : boundary.arrival.witness.corner.complementarySupportGraph.edgeSet) :
    (boundary.returnCorner.supportEdgeColorState
        (boundary.arrivalSupportEdgeInReturnGraph edge)).companionColor =
      (boundary.arrival.witness.corner.supportEdgeColorState edge
        ).companionColor := by
  rw [ScalarCompanionTurn.ComplementarySupportCorner.supportEdgeColorState_companionColor,
    ScalarCompanionTurn.ComplementarySupportCorner.supportEdgeColorState_companionColor]
  have hcoordinate : Bool.not (Bool.not boundary.middle.1.coordinate) =
      Bool.not boundary.before.1.coordinate := by
    rw [boundary.middle_coordinate_eq_not_before]
    cases boundary.before.1.coordinate <;> rfl
  have hedge : boundary.returnCorner.supportEdgeAmbientEdge
        (boundary.arrivalSupportEdgeInReturnGraph edge) =
      boundary.arrival.witness.corner.supportEdgeAmbientEdge edge := by
    apply Subtype.ext
    rfl
  rw [hcoordinate, hedge]

theorem returnCorner_supportEdgeAmbientEdge_transport
    (edge : boundary.arrival.witness.corner.complementarySupportGraph.edgeSet) :
    boundary.returnCorner.supportEdgeAmbientEdge
        (boundary.arrivalSupportEdgeInReturnGraph edge) =
      boundary.arrival.witness.corner.supportEdgeAmbientEdge edge := by
  apply Subtype.ext
  rfl

/-- The reverse of the arrival straight word is still companion-straight
for the canonical return corner. -/
theorem reversedArrivalStraightWord_isChain :
    ((boundary.arrivalCycleInReturnGraph.takeUntil boundary.middle.junction
      boundary.middle_mem_arrivalCycleInReturnGraph_support
      ).edgeSubtypeSupport.reverse).IsChain
      (fun first second =>
        (boundary.returnCorner.supportEdgeColorState first).companionColor =
          (boundary.returnCorner.supportEdgeColorState second
            ).companionColor) := by
  rw [boundary.arrivalCycleInReturnGraph_takeUntil_edgeSubtypeSupport]
  apply List.isChain_reverse.mpr
  rw [List.isChain_map]
  apply boundary.arrival.witness.interior.prefixStraight.imp
  intro first second heq
  rw [boundary.returnCorner_transport_companionColor,
    boundary.returnCorner_transport_companionColor]
  exact heq.symm

abbrev arrivalForwardPrefix :
    List (boundary.returnCorner.complementarySupportGraph.edgeSet) :=
  (boundary.arrivalCycleInReturnGraph.takeUntil boundary.middle.junction
    boundary.middle_mem_arrivalCycleInReturnGraph_support
    ).edgeSubtypeSupport

abbrev arrivalForwardSuffix :
    List (boundary.returnCorner.complementarySupportGraph.edgeSet) :=
  (boundary.arrivalCycleInReturnGraph.dropUntil boundary.middle.junction
    boundary.middle_mem_arrivalCycleInReturnGraph_support
    ).edgeSubtypeSupport

theorem arrivalForwardPrefix_ne_nil :
    boundary.arrivalForwardPrefix ≠ [] := by
  apply edgeSubtypeSupport_ne_nil_of_length_pos
  rw [boundary.arrivalCycleInReturnGraph_takeUntil_middle_length]
  change 0 < boundary.arrival.witness.interior.interior.before.length + 1
  omega

theorem arrivalForwardSuffix_positive :
    0 < (boundary.arrivalCycleInReturnGraph.dropUntil
      boundary.middle.junction
      boundary.middle_mem_arrivalCycleInReturnGraph_support).length := by
  rw [SimpleGraph.Walk.length_dropUntil]
  have hidx := (boundary.arrivalCycleInReturnGraph.length_takeUntil
    boundary.middle_mem_arrivalCycleInReturnGraph_support).symm.trans
      boundary.arrivalCycleInReturnGraph_takeUntil_middle_length
  rw [hidx]
  exact Nat.sub_pos_of_lt <| by
    rw [boundary.arrivalCycleInReturnGraph_length]
    exact boundary.arrival.witness.interior.turnPosition_lt_cycleLength

theorem arrivalForwardSuffix_ne_nil :
    boundary.arrivalForwardSuffix ≠ [] :=
  edgeSubtypeSupport_ne_nil_of_length_pos _
    boundary.arrivalForwardSuffix_positive

theorem arrivalForwardPrefix_head?_val_eq_rootFirst :
    boundary.arrivalForwardPrefix.head?.map
        (fun edge : boundary.returnCorner.complementarySupportGraph.edgeSet =>
          (edge.1 : Sym2 collar.commonCoreVertex)) =
      some (@Subtype.val (Sym2 collar.commonCoreVertex)
        boundary.arrival.witness.corner.complementarySupportGraph.edgeSet
        boundary.arrival.witness.route.rootedAtLaunch.rootFirstSupportEdge) := by
  let forwardPrefix :=
    (boundary.arrivalCycleInReturnGraph.takeUntil boundary.middle.junction
      boundary.middle_mem_arrivalCycleInReturnGraph_support
      ).edgeSubtypeSupport
  let straight := boundary.arrival.witness.interior.straightEdgeWord
  let strand := boundary.arrival.witness.route.rootedAtLaunch
  have hword := boundary.arrivalCycleInReturnGraph_takeUntil_edgeSubtypeSupport
  have hroot : straight.head? = some strand.rootFirstSupportEdge := by
    rcases boundary.arrival.witness.interior.straightEdgeWord_isPrefix with
      ⟨suffix, heq⟩
    calc
      straight.head? = (straight ++ suffix).head? :=
        (List.head?_append_of_ne_nil _
          boundary.arrival.witness.interior.straightEdgeWord_ne_nil).symm
      _ = strand.cycle.edgeSubtypeSupport.head? := congrArg List.head? heq
      _ = some strand.rootFirstSupportEdge :=
        List.head?_eq_some_head _
  calc
    forwardPrefix.head?.map Subtype.val =
        (straight.map boundary.arrivalSupportEdgeInReturnGraph
          ).head?.map Subtype.val :=
      congrArg (fun word => word.head?.map Subtype.val) hword
    _ = straight.head?.map Subtype.val := by
      rw [List.head?_map, Option.map_map]
      rfl
    _ = some strand.rootFirstSupportEdge.1 := by
      rw [hroot]
      rfl

theorem arrivalForwardPrefix_headOption_eq_rootFirst :
    boundary.arrivalForwardPrefix.head? =
      some (boundary.arrivalSupportEdgeInReturnGraph
        boundary.arrival.witness.route.rootedAtLaunch.rootFirstSupportEdge) := by
  have hvalue := boundary.arrivalForwardPrefix_head?_val_eq_rootFirst
  apply Option.map_injective
    (f := fun edge : boundary.returnCorner.complementarySupportGraph.edgeSet =>
      edge.1) Subtype.val_injective
  exact hvalue

theorem arrivalTakeDrop_edgeSubtypeSupport :
    boundary.arrivalForwardPrefix ++ boundary.arrivalForwardSuffix =
      boundary.arrivalCycleInReturnGraph.edgeSubtypeSupport := by
  have hwalk := boundary.arrivalCycleInReturnGraph.take_spec
    boundary.middle_mem_arrivalCycleInReturnGraph_support
  have hword := congrArg SimpleGraph.Walk.edgeSubtypeSupport hwalk
  simpa only [GoertzelV24AlternatingPrimalReturn.edgeSubtypeSupport_append]
    using hword

theorem arrivalForwardSuffix_getLast?_val_eq_rootLast :
    boundary.arrivalForwardSuffix.getLast?.map
        (fun edge : boundary.returnCorner.complementarySupportGraph.edgeSet =>
          (edge.1 : Sym2 collar.commonCoreVertex)) =
      some (@Subtype.val (Sym2 collar.commonCoreVertex)
        boundary.arrival.witness.corner.complementarySupportGraph.edgeSet
        boundary.arrival.witness.route.rootedAtLaunch.rootLastSupportEdge) := by
  let forwardPrefix :=
    (boundary.arrivalCycleInReturnGraph.takeUntil boundary.middle.junction
      boundary.middle_mem_arrivalCycleInReturnGraph_support
      ).edgeSubtypeSupport
  let forwardSuffix :=
    (boundary.arrivalCycleInReturnGraph.dropUntil boundary.middle.junction
      boundary.middle_mem_arrivalCycleInReturnGraph_support
      ).edgeSubtypeSupport
  let strand := boundary.arrival.witness.route.rootedAtLaunch
  have hsuffix : forwardSuffix ≠ [] := boundary.arrivalForwardSuffix_ne_nil
  have hor : forwardSuffix.getLast?.or forwardPrefix.getLast? =
      forwardSuffix.getLast? := by
    cases hlast : forwardSuffix.getLast? with
    | none =>
        exact False.elim <| hsuffix <|
          List.getLast?_eq_none_iff.mp hlast
    | some edge => rfl
  calc
    forwardSuffix.getLast?.map Subtype.val =
        (forwardPrefix ++ forwardSuffix).getLast?.map Subtype.val := by
      rw [List.getLast?_append, hor]
    _ = boundary.arrivalCycleInReturnGraph.edgeSubtypeSupport.getLast?.map
          Subtype.val :=
      congrArg (fun word => word.getLast?.map Subtype.val)
        boundary.arrivalTakeDrop_edgeSubtypeSupport
    _ = (strand.cycle.edgeSubtypeSupport.map
          boundary.arrivalSupportEdgeInReturnGraph).getLast?.map
            Subtype.val :=
      congrArg (fun word => word.getLast?.map Subtype.val)
        boundary.arrivalCycleInReturnGraph_edgeSubtypeSupport
    _ = strand.cycle.edgeSubtypeSupport.getLast?.map Subtype.val := by
      rw [List.getLast?_map, Option.map_map]
      rfl
    _ = some strand.rootLastSupportEdge.1 := by
      rw [List.getLast?_eq_some_getLast strand.cycleEdgeWord_ne_nil]
      rfl

theorem arrivalForwardSuffix_lastOption_eq_rootLast :
    boundary.arrivalForwardSuffix.getLast? =
      some (boundary.arrivalSupportEdgeInReturnGraph
        boundary.arrival.witness.route.rootedAtLaunch.rootLastSupportEdge) := by
  have hvalue := boundary.arrivalForwardSuffix_getLast?_val_eq_rootLast
  apply Option.map_injective
    (f := fun edge : boundary.returnCorner.complementarySupportGraph.edgeSet =>
      edge.1) Subtype.val_injective
  exact hvalue

abbrev reverseRootFirst :
    boundary.returnCorner.complementarySupportGraph.edgeSet :=
  boundary.arrivalSupportEdgeInReturnGraph
    boundary.arrival.witness.route.rootedAtLaunch.rootFirstSupportEdge

abbrev reverseRootLast :
    boundary.returnCorner.complementarySupportGraph.edgeSet :=
  boundary.arrivalSupportEdgeInReturnGraph
    boundary.arrival.witness.route.rootedAtLaunch.rootLastSupportEdge

theorem reverseRootFirstSecond :
    boundary.returnCorner.complementarySupportGraph.lineGraph.Adj
      boundary.reverseRootFirst boundary.reverseRootLast := by
  apply boundary.arrivalSupportEdgeInReturnGraph_lineGraph_adj
  exact (isCycle_edgeSubtypeSupport_closingAdj
    boundary.arrival.witness.route.rootedAtLaunch.cycle_isCycle).symm

theorem reverseRoot_companionColor_ne :
    (boundary.returnCorner.supportEdgeColorState
        boundary.reverseRootFirst).companionColor ≠
      (boundary.returnCorner.supportEdgeColorState
        boundary.reverseRootLast).companionColor := by
  rw [boundary.returnCorner_transport_companionColor,
    boundary.returnCorner_transport_companionColor]
  exact boundary.arrival.witness.route.rootedAtLaunch.rootCompanionColor_ne

theorem arrivalRootFirst_eq_incoming_or_transverse :
    boundary.arrival.witness.route.rootedAtLaunch.rootFirstSupportEdge =
        boundary.arrival.witness.corner.incomingSupportEdge ∨
      boundary.arrival.witness.route.rootedAtLaunch.rootFirstSupportEdge =
        boundary.arrival.witness.corner.transverseSupportEdge := by
  have hmem : boundary.arrival.witness.route.rootedAtLaunch.rootFirstSupportEdge ∈
      ({boundary.arrival.witness.route.rootedAtLaunch.rootFirstSupportEdge,
        boundary.arrival.witness.route.rootedAtLaunch.rootLastSupportEdge} :
        Finset boundary.arrival.witness.corner.complementarySupportGraph.edgeSet) :=
    Finset.mem_insert_self _ _
  rw [boundary.arrival.witness.route.rootedAtLaunch.rootEdges_pair_eq_launchEdges]
    at hmem
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

theorem arrivalRootLast_eq_incoming_or_transverse :
    boundary.arrival.witness.route.rootedAtLaunch.rootLastSupportEdge =
        boundary.arrival.witness.corner.incomingSupportEdge ∨
      boundary.arrival.witness.route.rootedAtLaunch.rootLastSupportEdge =
        boundary.arrival.witness.corner.transverseSupportEdge := by
  have hmem : boundary.arrival.witness.route.rootedAtLaunch.rootLastSupportEdge ∈
      ({boundary.arrival.witness.route.rootedAtLaunch.rootFirstSupportEdge,
        boundary.arrival.witness.route.rootedAtLaunch.rootLastSupportEdge} :
        Finset boundary.arrival.witness.corner.complementarySupportGraph.edgeSet) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [boundary.arrival.witness.route.rootedAtLaunch.rootEdges_pair_eq_launchEdges]
    at hmem
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

theorem reverseRootFirst_bypassed_adj :
    collar.commonCore.lineGraph.Adj
      (boundary.returnCorner.supportEdgeAmbientEdge
        boundary.reverseRootFirst)
      boundary.arrival.witness.corner.bypassed := by
  rw [boundary.returnCorner_supportEdgeAmbientEdge_transport]
  rcases boundary.arrivalRootFirst_eq_incoming_or_transverse with
    hroot | hroot
  · rw [hroot]
    exact boundary.arrival.witness.corner.incoming_bypassed_adj
  · rw [hroot]
    exact boundary.arrival.witness.corner.third_bypassed_adj

theorem reverseRootLast_bypassed_adj :
    collar.commonCore.lineGraph.Adj
      (boundary.returnCorner.supportEdgeAmbientEdge
        boundary.reverseRootLast)
      boundary.arrival.witness.corner.bypassed := by
  rw [boundary.returnCorner_supportEdgeAmbientEdge_transport]
  rcases boundary.arrivalRootLast_eq_incoming_or_transverse with
    hroot | hroot
  · rw [hroot]
    exact boundary.arrival.witness.corner.incoming_bypassed_adj
  · rw [hroot]
    exact boundary.arrival.witness.corner.third_bypassed_adj

theorem arrivalBypassed_discrepancy_eq_returnZeroColor :
    collar.commonDiscrepancy sourceEscape
        boundary.arrival.witness.corner.bypassed =
      crossFaceZeroColor (!(!boundary.middle.1.coordinate)) := by
  have hcoordinate : Bool.not (Bool.not boundary.middle.1.coordinate) =
      Bool.not boundary.before.1.coordinate := by
    rw [boundary.middle_coordinate_eq_not_before]
    cases boundary.before.1.coordinate <;> rfl
  rw [hcoordinate]
  exact boundary.arrival.witness.corner.bypassedDiscrepancy_eq_zeroColor

theorem reversedArrivalPrefix_lastOption_eq_rootFirst :
    boundary.arrivalForwardPrefix.reverse.getLast? =
      some boundary.reverseRootFirst := by
  rw [List.getLast?_reverse,
    boundary.arrivalForwardPrefix_headOption_eq_rootFirst]

theorem reversedArrivalSuffix_headOption_eq_rootLast :
    boundary.arrivalForwardSuffix.reverse.head? =
      some boundary.reverseRootLast := by
  rw [List.head?_reverse,
    boundary.arrivalForwardSuffix_lastOption_eq_rootLast]

/-- Arrival support cycle rerooted at the returning middle junction and
given the reverse orientation. -/
noncomputable def reversedArrivalCycle :
    boundary.returnCorner.complementarySupportGraph.Walk
      boundary.returnCorner.complementarySupportJunction
      boundary.returnCorner.complementarySupportJunction :=
  ((boundary.arrivalCycleInReturnGraph.rotate boundary.middle.junction
      boundary.middle_mem_arrivalCycleInReturnGraph_support).reverse).copy
    boundary.returnCorner_junction_eq_middle.symm
    boundary.returnCorner_junction_eq_middle.symm

theorem reversedArrivalCycle_edgeSubtypeSupport :
    boundary.reversedArrivalCycle.edgeSubtypeSupport =
      (boundary.arrivalCycleInReturnGraph.takeUntil boundary.middle.junction
          boundary.middle_mem_arrivalCycleInReturnGraph_support
          ).edgeSubtypeSupport.reverse ++
        (boundary.arrivalCycleInReturnGraph.dropUntil boundary.middle.junction
          boundary.middle_mem_arrivalCycleInReturnGraph_support
          ).edgeSubtypeSupport.reverse := by
  unfold reversedArrivalCycle
  rw [GoertzelV24AlternatingPrimalReturn.edgeSubtypeSupport_copy,
    GoertzelV24AlternatingPrimalReturn.edgeSubtypeSupport_reverse]
  unfold SimpleGraph.Walk.rotate
  rw [GoertzelV24AlternatingPrimalReturn.edgeSubtypeSupport_append,
    List.reverse_append]

theorem reversedArrivalStraightWord_isPrefix :
    (boundary.arrivalCycleInReturnGraph.takeUntil boundary.middle.junction
      boundary.middle_mem_arrivalCycleInReturnGraph_support
      ).edgeSubtypeSupport.reverse <+:
        boundary.reversedArrivalCycle.edgeSubtypeSupport := by
  refine ⟨(boundary.arrivalCycleInReturnGraph.dropUntil
    boundary.middle.junction
    boundary.middle_mem_arrivalCycleInReturnGraph_support
    ).edgeSubtypeSupport.reverse, ?_⟩
  exact boundary.reversedArrivalCycle_edgeSubtypeSupport.symm

theorem reversedArrivalStraightWord_length :
    (boundary.arrivalCycleInReturnGraph.takeUntil boundary.middle.junction
      boundary.middle_mem_arrivalCycleInReturnGraph_support
      ).edgeSubtypeSupport.reverse.length =
        boundary.arrival.witness.interior.turnPosition := by
  rw [List.length_reverse,
    SimpleGraph.Walk.edgeSubtypeSupport_length,
    boundary.arrivalCycleInReturnGraph_takeUntil_middle_length]

@[simp]
theorem reversedArrivalCycle_length :
    boundary.reversedArrivalCycle.length =
      boundary.arrivalCycleInReturnGraph.length := by
  unfold reversedArrivalCycle
  rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.length_rotate]

theorem reversedArrivalCycle_isCycle :
    boundary.reversedArrivalCycle.IsCycle := by
  rw [reversedArrivalCycle, SimpleGraph.Walk.isCycle_copy]
  exact (boundary.arrivalCycleInReturnGraph_isCycle.rotate
    boundary.middle_mem_arrivalCycleInReturnGraph_support).reverse

/-- The reversed arrival cycle is a closed strand for the canonical return
corner. -/
noncomputable def reversedArrivalStrand :
    boundary.returnCorner.ClosedSupportStrand := by
  let reversed := boundary.reversedArrivalCycle
  have hcycle : reversed.IsCycle := boundary.reversedArrivalCycle_isCycle
  have hjunctionDegree : boundary.returnCorner.complementarySupportGraph.degree
      boundary.returnCorner.complementarySupportJunction = 2 := by
    rw [← incidentEdgeFinset_card_eq_degree]
    exact boundary.returnCorner.supportJunction_degree_eq_two
  refine {
    cycle := reversed
    cycle_isCycle := hcycle
    incoming_mem := ?_
    transverse_mem := ?_ }
  · apply edge_mem_rooted_isCycle_of_degree_eq_two
      hcycle hjunctionDegree boundary.returnCorner.incomingSupportEdge
    exact SimpleGraph.lineGraphCommonVertex_mem_left
      boundary.returnCorner.incoming_transverse_adj
  · apply edge_mem_rooted_isCycle_of_degree_eq_two
      hcycle hjunctionDegree boundary.returnCorner.transverseSupportEdge
    exact SimpleGraph.lineGraphCommonVertex_mem_right
      boundary.returnCorner.incoming_transverse_adj

/-- Closed route obtained by returning along the arrival support cycle. -/
noncomputable def reversedArrivalRoute :
    boundary.returnCorner.ClosedSupportRoute :=
  .direct boundary.reversedArrivalStrand

/-- The reverse arrival cycle carries an explicit first transverse turn at
the old launch. Its straight prefix has exactly the arrival length and ends
at the predecessor junction. -/
theorem exists_reversedArrivalFirstTurn_finish_eq_before :
    ∃ firstTurn :
        boundary.reversedArrivalRoute.FirstInteriorTransverseTurn,
      firstTurn.finishJunction = boundary.before.junction ∧
      firstTurn.turnPosition =
          boundary.arrival.witness.interior.turnPosition ∧
        firstTurn.straightEdgeWord =
          boundary.arrivalForwardPrefix.reverse ∧
        firstTurn.interior.first = boundary.reverseRootFirst ∧
        firstTurn.interior.second = boundary.reverseRootLast ∧
        firstTurn.interior.thirdEdge =
          boundary.arrival.witness.corner.bypassed := by
  rcases List.getLast?_eq_some_iff.mp
      boundary.reversedArrivalPrefix_lastOption_eq_rootFirst with
    ⟨beforeEdges, hbeforeEdges⟩
  rcases List.head?_eq_some_iff.mp
      boundary.reversedArrivalSuffix_headOption_eq_rootLast with
    ⟨afterEdges, hafterEdges⟩
  let interior :
      boundary.reversedArrivalRoute.InteriorTransverseTurn := {
    before := beforeEdges
    first := boundary.reverseRootFirst
    second := boundary.reverseRootLast
    after := afterEdges
    firstSecond := boundary.reverseRootFirstSecond
    thirdEdge := boundary.arrival.witness.corner.bypassed
    word_eq := by
      change boundary.reversedArrivalCycle.edgeSubtypeSupport =
        beforeEdges ++
          boundary.reverseRootFirst :: boundary.reverseRootLast :: afterEdges
      rw [boundary.reversedArrivalCycle_edgeSubtypeSupport]
      change boundary.arrivalForwardPrefix.reverse ++
          boundary.arrivalForwardSuffix.reverse =
        beforeEdges ++
          boundary.reverseRootFirst :: boundary.reverseRootLast :: afterEdges
      rw [hbeforeEdges, hafterEdges]
      simp only [List.append_assoc, List.singleton_append]
    companion_ne := boundary.reverseRoot_companionColor_ne
    firstThird := boundary.reverseRootFirst_bypassed_adj
    secondThird := boundary.reverseRootLast_bypassed_adj
    discrepancy := boundary.arrivalBypassed_discrepancy_eq_returnZeroColor }
  let firstTurn :
      boundary.reversedArrivalRoute.FirstInteriorTransverseTurn := {
    interior := interior
    prefixStraight := by
      change (beforeEdges ++ [boundary.reverseRootFirst]).IsChain
        (fun first second =>
          (boundary.returnCorner.supportEdgeColorState first).companionColor =
            (boundary.returnCorner.supportEdgeColorState second
              ).companionColor)
      rw [← hbeforeEdges]
      exact boundary.reversedArrivalStraightWord_isChain }
  have hstraight : firstTurn.straightEdgeWord =
      boundary.arrivalForwardPrefix.reverse := by
    change beforeEdges ++ [boundary.reverseRootFirst] =
      boundary.arrivalForwardPrefix.reverse
    exact hbeforeEdges.symm
  refine ⟨firstTurn, ?_, ?_, hstraight, rfl, rfl, rfl⟩
  · change SimpleGraph.lineGraphCommonVertex
        boundary.reverseRootFirstSecond = boundary.before.junction
    symm
    apply SimpleGraph.lineGraphCommonVertex_unique
      boundary.reverseRootFirstSecond
    ·
      have hincident := boundary.arrival.witness.route.rootedAtLaunch
        |>.rootFirstSupportEdge_mem_incident
      have hvertex :
          boundary.arrival.witness.corner.complementarySupportJunction ∈
            (boundary.arrival.witness.route.rootedAtLaunch
              |>.rootFirstSupportEdge.1 : Sym2 collar.commonCoreVertex) := by
        simpa only [incidentEdgeFinset, Finset.mem_filter,
          Finset.mem_univ, true_and] using hincident
      rw [boundary.arrival.witness.corner
        |>.complementarySupportJunction_eq_junction] at hvertex
      exact hvertex
    ·
      have hincident := boundary.arrival.witness.route.rootedAtLaunch
        |>.rootLastSupportEdge_mem_incident
      have hvertex :
          boundary.arrival.witness.corner.complementarySupportJunction ∈
            (boundary.arrival.witness.route.rootedAtLaunch
              |>.rootLastSupportEdge.1 : Sym2 collar.commonCoreVertex) := by
        simpa only [incidentEdgeFinset, Finset.mem_filter,
          Finset.mem_univ, true_and] using hincident
      rw [boundary.arrival.witness.corner
        |>.complementarySupportJunction_eq_junction] at hvertex
      exact hvertex
  · calc
      firstTurn.turnPosition = firstTurn.straightEdgeWord.length := by
        simp only [ScalarCompanionTurn.ComplementarySupportCorner.ClosedSupportRoute.FirstInteriorTransverseTurn.turnPosition,
          ScalarCompanionTurn.ComplementarySupportCorner.ClosedSupportRoute.FirstInteriorTransverseTurn.straightEdgeWord,
          List.length_append, List.length_singleton]
      _ = boundary.arrivalForwardPrefix.reverse.length :=
        congrArg List.length hstraight
      _ = boundary.arrival.witness.interior.turnPosition :=
        boundary.reversedArrivalStraightWord_length

theorem returnState_realizedTurn_eq_returnTurn :
    boundary.returnState.realizedTurn = boundary.returnTurn := by
  apply ScalarCompanionTurn.eq_of_fields_eq
  · calc
      boundary.returnState.realizedTurn.first =
          boundary.returnState.1.first :=
        boundary.returnState.realizedTurn_first
      _ = boundary.returnTurn.first := by
        rw [returnState, ScalarCompanionTurnState.ofTurn_first]
  · calc
      boundary.returnState.realizedTurn.second =
          boundary.returnState.1.second :=
        boundary.returnState.realizedTurn_second
      _ = boundary.returnTurn.second := by
        rw [returnState, ScalarCompanionTurnState.ofTurn_second]
  · calc
      boundary.returnState.realizedTurn.third =
          boundary.returnState.1.third :=
        boundary.returnState.realizedTurn_third
      _ = boundary.returnTurn.third := by
        rw [returnState, ScalarCompanionTurnState.ofTurn_third]

/-- The reversed arrival route is either consumed by a charged Kempe
reentry or emits its first reverse interior turn. -/
theorem hasChargedKempeReentry_or_reversedArrivalFirstTurn :
    collar.HasChargedKempeReentry sourceEscape ∨
      Nonempty boundary.reversedArrivalRoute.FirstInteriorTransverseTurn := by
  rcases boundary.reversedArrivalRoute
      |>.kempeAction_and_sameBaseReentry_or_firstInteriorTransverseTurn with
    haction | hturn
  · rcases haction with ⟨representative, action, reentry⟩
    exact Or.inl ⟨_, representative, action, reentry⟩
  · exact Or.inr hturn

noncomputable def returnNextTurnWitness
    (firstTurn : boundary.reversedArrivalRoute.FirstInteriorTransverseTurn) :
    boundary.returnTurn.NextTurnWitness where
  corner := boundary.returnCorner
  route := boundary.reversedArrivalRoute
  interior := firstTurn

noncomputable def returnStateNextTurnWitness
    (firstTurn : boundary.reversedArrivalRoute.FirstInteriorTransverseTurn) :
    boundary.returnState.realizedTurn.NextTurnWitness :=
  boundary.returnState_realizedTurn_eq_returnTurn.symm ▸
    boundary.returnNextTurnWitness firstTurn

theorem returnStateNextTurnWitness_target_eq
    (firstTurn : boundary.reversedArrivalRoute.FirstInteriorTransverseTurn) :
    ScalarCompanionTurnState.ofTurn
        (boundary.returnStateNextTurnWitness firstTurn).nextTurn =
      ScalarCompanionTurnState.ofTurn
        (boundary.returnNextTurnWitness firstTurn).nextTurn := by
  exact ScalarCompanionTurn.NextTurnWitness.ofTurn_nextTurn_transport
    boundary.returnState_realizedTurn_eq_returnTurn
    (boundary.returnNextTurnWitness firstTurn)

noncomputable def reverseTargetState
    (firstTurn : boundary.reversedArrivalRoute.FirstInteriorTransverseTurn) :
    collar.ScalarCompanionTurnState sourceEscape :=
  ScalarCompanionTurnState.ofTurn
    (boundary.returnNextTurnWitness firstTurn).nextTurn

theorem returnState_isExactNext_reverseTargetState
    (firstTurn : boundary.reversedArrivalRoute.FirstInteriorTransverseTurn) :
    boundary.returnState.IsExactNext
      (boundary.reverseTargetState firstTurn) := by
  refine ⟨boundary.returnStateNextTurnWitness firstTurn, ?_⟩
  exact (boundary.returnStateNextTurnWitness_target_eq firstTurn).symm

theorem reverseTargetState_junction_eq_finish
    (firstTurn : boundary.reversedArrivalRoute.FirstInteriorTransverseTurn) :
    (boundary.reverseTargetState firstTurn).junction =
      firstTurn.finishJunction := by
  rw [reverseTargetState, ScalarCompanionTurnState.ofTurn_junction]
  exact firstTurn.toScalarCompanionTurn_junction_eq_finishJunction

/-- An immediate return therefore supplies an exact reverse transition of
the same geometric length back to the predecessor junction. -/
theorem exists_reverseExactNext_to_before :
    ∃ firstTurn :
        boundary.reversedArrivalRoute.FirstInteriorTransverseTurn,
      boundary.returnState.IsExactNext
          (boundary.reverseTargetState firstTurn) ∧
        (boundary.reverseTargetState firstTurn).junction =
          boundary.before.junction ∧
        firstTurn.turnPosition =
          boundary.arrival.witness.interior.turnPosition := by
  rcases boundary.exists_reversedArrivalFirstTurn_finish_eq_before with
    ⟨firstTurn, hfinish, hposition, _hstraight,
      _hfirst, _hsecond, _hthird⟩
  refine ⟨firstTurn,
    boundary.returnState_isExactNext_reverseTargetState firstTurn,
    ?_, hposition⟩
  exact (boundary.reverseTargetState_junction_eq_finish firstTurn).trans
    hfinish

end ScalarCompanionTurnState.ImmediateReturnBoundary
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
