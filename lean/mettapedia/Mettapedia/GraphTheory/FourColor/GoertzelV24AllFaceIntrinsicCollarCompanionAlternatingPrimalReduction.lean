import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingPrimalArc
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceSize

/-! Canonical reduction of recurrent alternating primal itineraries. -/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace GoertzelV24AlternatingPrimalReduction

variable {W : Type*} [DecidableEq W]
  {H : SimpleGraph W} {root : W}

/-- Bypassing repetitions in a nonempty closed walk leaves either a simple
cycle or the unique two-edge closed backtrack. -/
theorem cycleBypass_isCycle_or_length_eq_two
    (walk : H.Walk root root) (hnil : ¬ walk.Nil) :
    walk.cycleBypass.IsCycle ∨ walk.cycleBypass.length = 2 := by
  cases walk with
  | nil =>
      exact False.elim (hnil (by simp))
  | @cons _ next _ h tail =>
      have hpath : tail.bypass.IsPath := tail.bypass_isPath
      by_cases hedge : s(root, next) ∈ tail.bypass.edges
      · right
        have hedge' : s(next, root) ∈ tail.bypass.edges := by
          simpa only [Sym2.eq_swap] using hedge
        have hone : tail.bypass.length = 1 :=
          hpath.length_eq_one_of_mem_edges hedge'
        simp only [SimpleGraph.Walk.cycleBypass,
          SimpleGraph.Walk.length_cons, hone]
      · left
        exact (SimpleGraph.Walk.cons_isCycle_iff tail.bypass h).2
          ⟨hpath, hedge⟩

omit [DecidableEq W] in
/-- A closed walk of length two is literally one edge followed by its reverse. -/
theorem eq_backtrack_of_length_eq_two
    (walk : H.Walk root root) (hlength : walk.length = 2) :
    ∃ (next : W) (h : H.Adj root next),
      walk = h.toWalk.append h.symm.toWalk := by
  cases walk with
  | nil => simp at hlength
  | @cons _ next _ h tail =>
      cases tail with
      | nil => simp at hlength
      | @cons _ next' _ h' rest =>
          cases rest with
          | nil =>
              refine ⟨next, h, ?_⟩
              rfl
          | @cons _ next'' _ h'' rest' =>
              simp only [SimpleGraph.Walk.length_cons] at hlength
              omega

/-- Explicit closed-walk reduction: the residual walk is a simple cycle or
one edge immediately followed by its reverse. -/
theorem cycleBypass_isCycle_or_eq_backtrack
    (walk : H.Walk root root) (hnil : ¬ walk.Nil) :
    walk.cycleBypass.IsCycle ∨
      ∃ (next : W) (h : H.Adj root next),
        walk.cycleBypass = h.toWalk.append h.symm.toWalk := by
  rcases cycleBypass_isCycle_or_length_eq_two walk hnil with
    hcycle | hlength
  · exact Or.inl hcycle
  · exact Or.inr (eq_backtrack_of_length_eq_two walk.cycleBypass hlength)

end GoertzelV24AlternatingPrimalReduction

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CorridorPumping
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

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

/-- Every common-core cycle is an ambient cycle and hence has length at least
five in a vertex-minimal Tait counterexample. -/
theorem commonCore_isCycle_length_ge_five
    {root : collar.commonCoreVertex}
    (commonCycle : collar.commonCore.Walk root root)
    (hcycle : commonCycle.IsCycle) :
    5 ≤ commonCycle.length := by
  let embedding : collar.commonCore ↪g G :=
    SimpleGraph.Embedding.induce (G := G) collar.commonCorePredicate
  let ambientCycle : G.Walk root.1 root.1 :=
    commonCycle.map embedding.toHom
  have hambientCycle : ambientCycle.IsCycle :=
    hcycle.map embedding.injective
  have hnotShort :=
    GoertzelV24MinimalFaceSize.not_isCycle_length_le_four_of_vertexMinimalTaitCounterexample
      graphData minimal ambientCycle hambientCycle
  have hsameLength : ambientCycle.length = commonCycle.length := by
    change (commonCycle.map embedding.toHom).length = commonCycle.length
    exact SimpleGraph.Walk.length_map embedding.toHom commonCycle
  omega

namespace ScalarCompanionTurnState

/-- A recurrent exact turn orbit reduced as far as arbitrary closed-walk
repetition permits. Its residual common-core walk is either an ambient simple
cycle of length at least five or a two-edge backtrack. -/
structure ReducedPrimalJunctionItinerary where
  entry : collar.ScalarCompanionTurnState sourceEscape
  period : Nat
  period_ge_two : 2 ≤ period
  period_even : Even period
  transfer : ExactPrimalArcTransfer period entry entry
  walk : collar.commonCore.Walk entry.junction entry.junction
  period_le_walk_length : period ≤ walk.length
  walk_not_nil : ¬ walk.Nil
  reduced_edges_subset : walk.cycleBypass.edges ⊆ walk.edges
  reduced_length_le : walk.cycleBypass.length ≤ walk.length
  reduced_shape :
    (walk.cycleBypass.IsCycle ∧ 5 ≤ walk.cycleBypass.length) ∨
      ∃ (next : collar.commonCoreVertex)
          (h : collar.commonCore.Adj entry.junction next),
        walk.cycleBypass = h.toWalk.append h.symm.toWalk

/-- The exact even itinerary carried by an alternating orbit admits the
canonical cycle-bypass reduction. -/
theorem AlternatingOrbitCertificate.nonempty_reducedPrimalJunctionItinerary
    {hnoAction : ¬ collar.HasChargedKempeReentry sourceEscape}
    {start : collar.ScalarCompanionTurnState sourceEscape}
    (certificate : AlternatingOrbitCertificate hnoAction start) :
    Nonempty (ReducedPrimalJunctionItinerary
      (collar := collar) (sourceEscape := sourceEscape)) := by
  rcases certificate.exists_exact_even_primalJunctionItinerary with
    ⟨entry, period, hperiod, heven, transfer, walk,
      hwalkLength, hwalkNonNil⟩
  have hshape :=
    GoertzelV24AlternatingPrimalReduction.cycleBypass_isCycle_or_eq_backtrack
      walk hwalkNonNil
  refine ⟨{
    entry := entry
    period := period
    period_ge_two := hperiod
    period_even := heven
    transfer := transfer
    walk := walk
    period_le_walk_length := hwalkLength
    walk_not_nil := hwalkNonNil
    reduced_edges_subset := walk.edges_cycleBypass_subset_edges
    reduced_length_le := walk.length_cycleBypass_le_length
    reduced_shape := ?_ }⟩
  rcases hshape with hcycle | hbacktrack
  · exact Or.inl ⟨hcycle,
      commonCore_isCycle_length_ge_five walk.cycleBypass hcycle⟩
  · exact Or.inr hbacktrack

end ScalarCompanionTurnState

namespace ScalarCompanionTurn

/-- A signed turn either yields the charged Kempe reentry or a canonical
reduced exact primal itinerary. -/
theorem hasChargedKempeReentry_or_reducedPrimalJunctionItinerary
    {coordinate : Bool}
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    collar.HasChargedKempeReentry sourceEscape ∨
      Nonempty (ScalarCompanionTurnState.ReducedPrimalJunctionItinerary
        (collar := collar) (sourceEscape := sourceEscape)) := by
  rcases turn.hasChargedKempeReentry_or_alternatingOrbitCertificate with
    haction | ⟨_haction, certificate⟩
  · exact Or.inl haction
  · exact Or.inr
      certificate.nonempty_reducedPrimalJunctionItinerary

end ScalarCompanionTurn

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
