import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingPrimalReduction
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Support-graph reduction of exact alternating primal-arc transfers. -/

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

namespace GoertzelV24AlternatingPrimalReduction

variable {W : Type*}
  {H : SimpleGraph W} {root : W}

/-- A nonempty closed walk whose consecutive unoriented edges are distinct
contains a simple cycle in its own edge support. -/
theorem exists_supportedCycle_of_edgeSubtypeSupport_isChain_ne
    (walk : H.Walk root root) (hnil : ¬ walk.Nil)
    (hchain : walk.edgeSubtypeSupport.IsChain (· ≠ ·)) :
    ∃ (cycleRoot : W) (cycle : H.Walk cycleRoot cycleRoot),
      cycle.IsCycle ∧ cycle.edges ⊆ walk.edges := by
  classical
  have hrawChain : walk.edges.IsChain (· ≠ ·) := by
    rw [← walk.edgeSubtypeSupport_map_val, List.isChain_map]
    exact hchain.imp fun first second hne hval =>
      hne (Subtype.ext hval)
  have hnotAcyclic : ¬ walk.toSubgraph.coe.IsAcyclic := by
    intro hacyclic
    let supportedWalk := walk.mapToSubgraph
    have hmappedEdges :
        supportedWalk.edges.map
            (Sym2.map walk.toSubgraph.hom) = walk.edges := by
      calc
        supportedWalk.edges.map (Sym2.map walk.toSubgraph.hom) =
            (supportedWalk.map walk.toSubgraph.hom).edges := by
          rw [SimpleGraph.Walk.edges_map]
        _ = walk.edges := congrArg SimpleGraph.Walk.edges
          walk.map_mapToSubgraph_hom
    have hmappedChain :
        (supportedWalk.edges.map
          (Sym2.map walk.toSubgraph.hom)).IsChain (· ≠ ·) := by
      rw [hmappedEdges]
      exact hrawChain
    have hsupportedChain : supportedWalk.edges.IsChain (· ≠ ·) := by
      rw [List.isChain_map] at hmappedChain
      exact hmappedChain.imp fun first second hne heq =>
        hne (congrArg (Sym2.map walk.toSubgraph.hom) heq)
    have hsupportedPath : supportedWalk.IsPath :=
      (hacyclic.isPath_iff_isChain supportedWalk).2 hsupportedChain
    have hsupportedNil : supportedWalk.Nil :=
      SimpleGraph.Walk.isPath_iff_nil.mp hsupportedPath
    have hsameLength : supportedWalk.length = walk.length := by
      calc
        supportedWalk.length =
            (supportedWalk.map walk.toSubgraph.hom).length :=
          (SimpleGraph.Walk.length_map walk.toSubgraph.hom supportedWalk).symm
        _ = walk.length := congrArg SimpleGraph.Walk.length
          walk.map_mapToSubgraph_hom
    have hwalkZero : walk.length = 0 := by
      rw [← hsameLength]
      exact SimpleGraph.Walk.length_eq_zero_iff.mpr hsupportedNil
    exact hnil (SimpleGraph.Walk.length_eq_zero_iff.mp hwalkZero)
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hnotAcyclic
  rcases hnotAcyclic with ⟨subroot, subcycle, hsubcycle⟩
  let cycle : H.Walk subroot.1 subroot.1 :=
    subcycle.map walk.toSubgraph.hom
  have hcycle : cycle.IsCycle :=
    (SimpleGraph.Walk.map_isCycle_iff_of_injective
      walk.toSubgraph.hom_injective).2 hsubcycle
  refine ⟨subroot.1, cycle, hcycle, ?_⟩
  intro edge hedge
  dsimp only [cycle] at hedge
  have hedge' : edge ∈
      subcycle.edges.map (Sym2.map walk.toSubgraph.hom) := by
    rw [← SimpleGraph.Walk.edges_map walk.toSubgraph.hom subcycle]
    exact hedge
  rcases List.mem_map.mp hedge' with ⟨subedge, hsubedge, rfl⟩
  have hsubedgeGraph := subcycle.edges_subset_edgeSet hsubedge
  rw [SimpleGraph.Subgraph.edgeSet_coe] at hsubedgeGraph
  exact walk.mem_edges_toSubgraph.mp hsubedgeGraph

end GoertzelV24AlternatingPrimalReduction

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

namespace ScalarCompanionTurnState

@[simp]
theorem edgeSubtypeSupport_append
    {start middle finish : collar.commonCoreVertex}
    (first : collar.commonCore.Walk start middle)
    (second : collar.commonCore.Walk middle finish) :
    (first.append second).edgeSubtypeSupport =
      first.edgeSubtypeSupport ++ second.edgeSubtypeSupport := by
  apply (List.map_injective_iff.mpr Subtype.val_injective)
  simp only [SimpleGraph.Walk.edgeSubtypeSupport_map_val,
    List.map_append, SimpleGraph.Walk.edges_append]

theorem ExactPrimalArc.edgeWord_isChain_ne
    {source target : collar.ScalarCompanionTurnState sourceEscape}
    (arc : ExactPrimalArc source target) :
    arc.path.edgeSubtypeSupport.IsChain (· ≠ ·) := by
  have hedgesNodup : arc.path.edges.Nodup :=
    (SimpleGraph.Walk.isTrail_def arc.path).1 arc.path_isPath.isTrail
  have hwordNodup : arc.path.edgeSubtypeSupport.Nodup :=
    (List.nodup_map_iff Subtype.val_injective).1 <| by
      simpa only [arc.path.edgeSubtypeSupport_map_val] using hedgesNodup
  exact (List.nodup_iff_pairwise_ne.mp hwordNodup).isChain

/-- A walk realizing an exact primal-arc transfer by literal concatenation. -/
inductive ExactPrimalArcTransfer.RealizesWalk :
    {length : Nat} →
      {start finish : collar.ScalarCompanionTurnState sourceEscape} →
      ExactPrimalArcTransfer length start finish →
      (walk : collar.commonCore.Walk start.junction finish.junction) →
      Prop where
  | zero (state : collar.ScalarCompanionTurnState sourceEscape) :
      RealizesWalk (.zero state) SimpleGraph.Walk.nil
  | succ {length : Nat}
      {start next finish : collar.ScalarCompanionTurnState sourceEscape}
      (first : ExactPrimalArc start next)
      (rest : ExactPrimalArcTransfer length next finish)
      {tail : collar.commonCore.Walk next.junction finish.junction} :
      RealizesWalk rest tail →
      RealizesWalk (.succ first rest) (first.path.append tail)

/-- An actual reversal between the terminal edge of one exact arc and the
initial edge of the immediately following arc. -/
inductive ExactPrimalArcTransfer.ContainsImmediateReversal :
    {length : Nat} →
      {start finish : collar.ScalarCompanionTurnState sourceEscape} →
      ExactPrimalArcTransfer length start finish → Prop where
  | head {length : Nat}
      {start middle next finish :
        collar.ScalarCompanionTurnState sourceEscape}
      (first : ExactPrimalArc start middle)
      (second : ExactPrimalArc middle next)
      (rest : ExactPrimalArcTransfer length next finish)
      (reversal : first.path.edgeSubtypeSupport.getLast? =
        second.path.edgeSubtypeSupport.head?) :
      ContainsImmediateReversal (.succ first (.succ second rest))
  | tail {length : Nat}
      {start next finish : collar.ScalarCompanionTurnState sourceEscape}
      (first : ExactPrimalArc start next)
      {rest : ExactPrimalArcTransfer length next finish} :
      ContainsImmediateReversal rest →
      ContainsImmediateReversal (.succ first rest)

theorem first_ne_second
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    state.1.first ≠ state.1.second := by
  rw [← state.realizedTurn_first, ← state.realizedTurn_second]
  exact state.realizedTurn.firstSecond.ne

theorem first_ne_third
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    state.1.first ≠ state.1.third := by
  rw [← state.realizedTurn_first, ← state.realizedTurn_third]
  exact state.realizedTurn.firstThird.ne

/-- If an exact arc launches through the source state's first edge, its
retained complementary corner is oriented with that edge incoming and the
second source edge bypassed. -/
theorem ExactPrimalArc.witnessCorner_orientation_first_of_head_eq_sourceFirst
    {source target : collar.ScalarCompanionTurnState sourceEscape}
    (arc : ExactPrimalArc source target)
    (hhead : arc.path.edgeSubtypeSupport.head? = some source.1.first) :
    arc.witness.corner.incoming = source.realizedTurn.first ∧
      arc.witness.corner.bypassed = source.realizedTurn.second := by
  have hwitnessHead :
      arc.witness.interior.primalArc.edgeSubtypeSupport.head? =
        some source.1.first := by
    rw [← arc.path_edgeSubtypeSupport_eq_witness]
    exact hhead
  have hfirstOption := edgeSubtypeSupport_head?_eq_some_firstEdgeSet
    arc.witness.interior.primalArc
      arc.witness.interior.primalArc_positive
  have hfirstSet :
      arc.witness.interior.primalArc.firstEdgeSet
          (SimpleGraph.Walk.not_nil_iff_lt_length.mpr
            arc.witness.interior.primalArc_positive) =
        source.1.first := by
    exact Option.some.inj (hfirstOption.symm.trans hwitnessHead)
  have hincoming : arc.witness.corner.incoming =
      source.realizedTurn.first := by
    rcases
        arc.witness.interior.primalArc_firstEdgeSet_eq_incoming_or_third with
      hincoming | hthird
    · exact hincoming.symm.trans <| hfirstSet.trans
        source.realizedTurn_first.symm
    · exact False.elim <| first_ne_third source <|
        (hfirstSet.symm.trans hthird).trans source.realizedTurn_third
  rcases arc.witness.corner.orientation with horientation | horientation
  · exact ⟨hincoming, horientation.2⟩
  · exact False.elim <| first_ne_second source <|
      source.realizedTurn_first.symm.trans <|
        hincoming.symm.trans <| horientation.1.trans
          source.realizedTurn_second

/-- Consecutive exact arcs that reverse an edge, retaining the actual corner
orientation of the departing step. -/
structure ImmediateReturnBoundary where
  before : collar.ScalarCompanionTurnState sourceEscape
  middle : collar.ScalarCompanionTurnState sourceEscape
  next : collar.ScalarCompanionTurnState sourceEscape
  arrival : ExactPrimalArc before middle
  departure : ExactPrimalArc middle next
  reversal : arrival.path.edgeSubtypeSupport.getLast? =
    departure.path.edgeSubtypeSupport.head?
  departure_head_eq_middleFirst :
    departure.path.edgeSubtypeSupport.head? = some middle.1.first
  departure_corner_orientation :
    departure.witness.corner.incoming = middle.realizedTurn.first ∧
      departure.witness.corner.bypassed = middle.realizedTurn.second

/-- Every transfer-level immediate reversal exposes a literal returning
corner between two consecutive exact arcs. -/
theorem ExactPrimalArcTransfer.ContainsImmediateReversal.nonempty_immediateReturnBoundary
    {length : Nat}
    {start finish : collar.ScalarCompanionTurnState sourceEscape}
    {transfer : ExactPrimalArcTransfer length start finish}
    (hreversal : transfer.ContainsImmediateReversal) :
    Nonempty (ImmediateReturnBoundary
      (collar := collar) (sourceEscape := sourceEscape)) := by
  induction hreversal with
  | @head length before middle next finish arrival departure rest reversal =>
      have hhead : departure.path.edgeSubtypeSupport.head? =
          some middle.1.first :=
        reversal.symm.trans arrival.lastEdge_eq_targetFirst
      exact ⟨{
        before := before
        middle := middle
        next := next
        arrival := arrival
        departure := departure
        reversal := reversal
        departure_head_eq_middleFirst := hhead
        departure_corner_orientation :=
          departure.witnessCorner_orientation_first_of_head_eq_sourceFirst
            hhead }⟩
  | @tail length before next finish first rest _hreversal ih =>
      exact ih

theorem ExactPrimalArcTransfer.exists_realizingWalk_chain_or_reversal
    {length : Nat}
    {start finish : collar.ScalarCompanionTurnState sourceEscape}
    (transfer : ExactPrimalArcTransfer length start finish) :
    ∃ walk : collar.commonCore.Walk start.junction finish.junction,
      transfer.RealizesWalk walk ∧ length ≤ walk.length ∧
        (walk.edgeSubtypeSupport.IsChain (· ≠ ·) ∨
          transfer.ContainsImmediateReversal) := by
  induction transfer with
  | zero state =>
      exact ⟨SimpleGraph.Walk.nil, .zero state, Nat.le_refl 0,
        Or.inl .nil⟩
  | @succ length start next finish first rest ih =>
      rcases ih with ⟨tail, hrealize, hlength, hshape⟩
      refine ⟨first.path.append tail, .succ first rest hrealize, ?_, ?_⟩
      · rw [SimpleGraph.Walk.length_append]
        have hfirst : 1 ≤ first.path.length := first.path_positive
        omega
      · rcases hshape with htailChain | htailReversal
        · cases hrealize with
          | zero state =>
              left
              simpa using first.edgeWord_isChain_ne
          | @succ tailLength tailStart tailNext tailFinish second tailRest
              tailTail htailRealize =>
              by_cases hreversal :
                  first.path.edgeSubtypeSupport.getLast? =
                    second.path.edgeSubtypeSupport.head?
              · exact Or.inr <| .head first second tailRest hreversal
              · left
                rw [edgeSubtypeSupport_append]
                apply first.edgeWord_isChain_ne.append htailChain
                intro last hlast firstEdge hfirstEdge heq
                apply hreversal
                have hlastEq :
                    first.path.edgeSubtypeSupport.getLast? = some last :=
                  Option.mem_def.mp hlast
                have hfirstTailEq :
                    (second.path.append tailTail).edgeSubtypeSupport.head? =
                      some firstEdge := Option.mem_def.mp hfirstEdge
                have hsecondWord :
                    second.path.edgeSubtypeSupport ≠ [] :=
                  edgeSubtypeSupport_ne_nil_of_length_pos second.path
                    second.path_positive
                have hfirstEq :
                    second.path.edgeSubtypeSupport.head? =
                      some firstEdge := by
                  rw [edgeSubtypeSupport_append,
                    List.head?_append_of_ne_nil _ hsecondWord] at hfirstTailEq
                  exact hfirstTailEq
                calc
                  first.path.edgeSubtypeSupport.getLast? = some last :=
                    hlastEq
                  _ = some firstEdge := congrArg some heq
                  _ = second.path.edgeSubtypeSupport.head? := hfirstEq.symm
        · exact Or.inr
            (ExactPrimalArcTransfer.ContainsImmediateReversal.tail
              first htailReversal)

/-- A recurrent exact orbit reduced against the support graph of its literal
arc concatenation. -/
structure SupportReducedPrimalJunctionItinerary where
  entry : collar.ScalarCompanionTurnState sourceEscape
  period : Nat
  period_ge_two : 2 ≤ period
  period_even : Even period
  transfer : ExactPrimalArcTransfer period entry entry
  walk : collar.commonCore.Walk entry.junction entry.junction
  realizes : transfer.RealizesWalk walk
  period_le_walk_length : period ≤ walk.length
  reduced_shape :
    (∃ (cycleRoot : collar.commonCoreVertex)
        (primalCycle : collar.commonCore.Walk cycleRoot cycleRoot),
      primalCycle.IsCycle ∧ 5 ≤ primalCycle.length ∧
        primalCycle.edges ⊆ walk.edges) ∨
      Nonempty (ImmediateReturnBoundary
        (collar := collar) (sourceEscape := sourceEscape))

/-- An alternating orbit contains either a supported ambient primal cycle or
an actual reversal between consecutive exact arcs. -/
theorem AlternatingOrbitCertificate.nonempty_supportReducedPrimalJunctionItinerary
    {hnoAction : ¬ collar.HasChargedKempeReentry sourceEscape}
    {start : collar.ScalarCompanionTurnState sourceEscape}
    (certificate : AlternatingOrbitCertificate hnoAction start) :
    Nonempty (SupportReducedPrimalJunctionItinerary
      (collar := collar) (sourceEscape := sourceEscape)) := by
  rcases certificate.exists_exact_even_return with
    ⟨entry, period, hperiod, heven, exactReturn⟩
  let transfer : ExactPrimalArcTransfer period entry entry :=
    exactRelationalTransfer_toExactPrimalArcTransfer exactReturn
  rcases transfer.exists_realizingWalk_chain_or_reversal with
    ⟨walk, hrealize, hwalkLength, hshape⟩
  refine ⟨{
    entry := entry
    period := period
    period_ge_two := hperiod
    period_even := heven
    transfer := transfer
    walk := walk
    realizes := hrealize
    period_le_walk_length := hwalkLength
    reduced_shape := ?_ }⟩
  rcases hshape with hchain | hreversal
  · have hwalkNonNil : ¬ walk.Nil := by
      apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
      omega
    rcases
        GoertzelV24AlternatingPrimalReduction.exists_supportedCycle_of_edgeSubtypeSupport_isChain_ne
          walk hwalkNonNil hchain with
      ⟨cycleRoot, primalCycle, hcycle, hcycleEdges⟩
    exact Or.inl ⟨cycleRoot, primalCycle, hcycle,
      commonCore_isCycle_length_ge_five primalCycle hcycle,
      hcycleEdges⟩
  · exact Or.inr hreversal.nonempty_immediateReturnBoundary

end ScalarCompanionTurnState

namespace ScalarCompanionTurn

/-- A signed turn yields a charged Kempe reentry, a supported primal cycle,
or a literal reversal between consecutive exact arcs. -/
theorem hasChargedKempeReentry_or_supportReducedPrimalJunctionItinerary
    {coordinate : Bool}
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    collar.HasChargedKempeReentry sourceEscape ∨
      Nonempty
        (ScalarCompanionTurnState.SupportReducedPrimalJunctionItinerary
          (collar := collar) (sourceEscape := sourceEscape)) := by
  rcases turn.hasChargedKempeReentry_or_alternatingOrbitCertificate with
    haction | ⟨_haction, certificate⟩
  · exact Or.inl haction
  · exact Or.inr
      certificate.nonempty_supportReducedPrimalJunctionItinerary

end ScalarCompanionTurn
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
