import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingPrimalReturnLens

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

namespace ScalarCompanionTurnState.ImmediateReturnBoundary

variable {boundary : ScalarCompanionTurnState.ImmediateReturnBoundary
  (collar := collar) (sourceEscape := sourceEscape)}

namespace ExactReverseArrivalLens

variable (lens : boundary.ExactReverseArrivalLens)

@[simp]
theorem reverseTarget_coordinate_eq_middle :
    (boundary.reverseTargetState lens.firstTurn).1.coordinate =
      boundary.middle.1.coordinate := by
  rw [reverseTargetState, ScalarCompanionTurnState.ofTurn_coordinate]
  cases boundary.middle.1.coordinate <;> rfl

theorem reverseTarget_coordinate_eq_not_before :
    (boundary.reverseTargetState lens.firstTurn).1.coordinate =
      !boundary.before.1.coordinate := by
  rw [lens.reverseTarget_coordinate_eq_middle,
    boundary.middle_coordinate_eq_not_before]

@[simp]
theorem reverseTarget_first :
    (boundary.reverseTargetState lens.firstTurn).1.first =
      boundary.returnCorner.supportEdgeAmbientEdge
        boundary.reverseRootFirst := by
  rw [reverseTargetState, ScalarCompanionTurnState.ofTurn_first]
  change boundary.returnCorner.supportEdgeAmbientEdge
      lens.firstTurn.interior.first = _
  rw [lens.firstEdge_eq_reverseRootFirst]

@[simp]
theorem reverseTarget_second :
    (boundary.reverseTargetState lens.firstTurn).1.second =
      boundary.returnCorner.supportEdgeAmbientEdge
        boundary.reverseRootLast := by
  rw [reverseTargetState, ScalarCompanionTurnState.ofTurn_second]
  change boundary.returnCorner.supportEdgeAmbientEdge
      lens.firstTurn.interior.second = _
  rw [lens.secondEdge_eq_reverseRootLast]

@[simp]
theorem reverseTarget_third :
    (boundary.reverseTargetState lens.firstTurn).1.third =
      boundary.arrival.witness.corner.bypassed := by
  rw [reverseTargetState, ScalarCompanionTurnState.ofTurn_third]
  change lens.firstTurn.interior.thirdEdge = _
  exact lens.thirdEdge_eq_arrivalBypassed

/-- Reversing the rooted support cycle orders its launch pair either as
incoming/transverse or as transverse/incoming; the two equal-edge cases are
excluded by line-graph adjacency. -/
theorem reverseRootAmbient_order :
    (boundary.returnCorner.supportEdgeAmbientEdge
          boundary.reverseRootFirst =
        boundary.arrival.witness.corner.incoming ∧
      boundary.returnCorner.supportEdgeAmbientEdge
          boundary.reverseRootLast =
        boundary.before.realizedTurn.third) ∨
    (boundary.returnCorner.supportEdgeAmbientEdge
          boundary.reverseRootFirst =
        boundary.before.realizedTurn.third ∧
      boundary.returnCorner.supportEdgeAmbientEdge
          boundary.reverseRootLast =
        boundary.arrival.witness.corner.incoming) := by
  rcases boundary.arrivalRootFirst_eq_incoming_or_transverse with
    hfirst | hfirst <;>
    rcases boundary.arrivalRootLast_eq_incoming_or_transverse with
      hlast | hlast
  · exact False.elim <| boundary.reverseRootFirstSecond.ne <| by
      change boundary.arrivalSupportEdgeInReturnGraph
          boundary.arrival.witness.route.rootedAtLaunch.rootFirstSupportEdge =
        boundary.arrivalSupportEdgeInReturnGraph
          boundary.arrival.witness.route.rootedAtLaunch.rootLastSupportEdge
      rw [hfirst, hlast]
  · left
    constructor
    · rw [boundary.returnCorner_supportEdgeAmbientEdge_transport, hfirst]
      rfl
    · rw [boundary.returnCorner_supportEdgeAmbientEdge_transport, hlast]
      rfl
  · right
    constructor
    · rw [boundary.returnCorner_supportEdgeAmbientEdge_transport, hfirst]
      rfl
    · rw [boundary.returnCorner_supportEdgeAmbientEdge_transport, hlast]
      rfl
  · exact False.elim <| boundary.reverseRootFirstSecond.ne <| by
      change boundary.arrivalSupportEdgeInReturnGraph
          boundary.arrival.witness.route.rootedAtLaunch.rootFirstSupportEdge =
        boundary.arrivalSupportEdgeInReturnGraph
          boundary.arrival.witness.route.rootedAtLaunch.rootLastSupportEdge
      rw [hfirst, hlast]

/-- The endpoint of the reverse lens has one of exactly four ordered
three-edge permutations relative to the predecessor turn. -/
theorem reverseTarget_edgePermutation :
    ((boundary.reverseTargetState lens.firstTurn).1.first =
          boundary.before.1.first ∧
        (boundary.reverseTargetState lens.firstTurn).1.second =
          boundary.before.1.third ∧
        (boundary.reverseTargetState lens.firstTurn).1.third =
          boundary.before.1.second) ∨
    ((boundary.reverseTargetState lens.firstTurn).1.first =
          boundary.before.1.third ∧
        (boundary.reverseTargetState lens.firstTurn).1.second =
          boundary.before.1.first ∧
        (boundary.reverseTargetState lens.firstTurn).1.third =
          boundary.before.1.second) ∨
    ((boundary.reverseTargetState lens.firstTurn).1.first =
          boundary.before.1.second ∧
        (boundary.reverseTargetState lens.firstTurn).1.second =
          boundary.before.1.third ∧
        (boundary.reverseTargetState lens.firstTurn).1.third =
          boundary.before.1.first) ∨
    ((boundary.reverseTargetState lens.firstTurn).1.first =
          boundary.before.1.third ∧
        (boundary.reverseTargetState lens.firstTurn).1.second =
          boundary.before.1.second ∧
        (boundary.reverseTargetState lens.firstTurn).1.third =
          boundary.before.1.first) := by
  rcases reverseRootAmbient_order (boundary := boundary) with hroot | hroot <;>
    rcases boundary.arrival.witness.corner.orientation with
      horientation | horientation
  · exact Or.inl ⟨
      lens.reverseTarget_first.trans <| hroot.1.trans <|
        horientation.1.trans boundary.before.realizedTurn_first,
      lens.reverseTarget_second.trans <| hroot.2.trans
        boundary.before.realizedTurn_third,
      lens.reverseTarget_third.trans <| horientation.2.trans
        boundary.before.realizedTurn_second⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨
      lens.reverseTarget_first.trans <| hroot.1.trans <|
        horientation.1.trans boundary.before.realizedTurn_second,
      lens.reverseTarget_second.trans <| hroot.2.trans
        boundary.before.realizedTurn_third,
      lens.reverseTarget_third.trans <| horientation.2.trans
        boundary.before.realizedTurn_first⟩
  · exact Or.inr <| Or.inl ⟨
      lens.reverseTarget_first.trans <| hroot.1.trans
        boundary.before.realizedTurn_third,
      lens.reverseTarget_second.trans <| hroot.2.trans <|
        horientation.1.trans boundary.before.realizedTurn_first,
      lens.reverseTarget_third.trans <| horientation.2.trans
        boundary.before.realizedTurn_second⟩
  · exact Or.inr <| Or.inr <| Or.inr ⟨
      lens.reverseTarget_first.trans <| hroot.1.trans
        boundary.before.realizedTurn_third,
      lens.reverseTarget_second.trans <| hroot.2.trans <|
        horientation.1.trans boundary.before.realizedTurn_second,
      lens.reverseTarget_third.trans <| horientation.2.trans
        boundary.before.realizedTurn_first⟩

theorem reverseTarget_junction_eq_before :
    (boundary.reverseTargetState lens.firstTurn).junction =
      boundary.before.junction :=
  boundary.reverseTargetState_junction_eq_finish lens.firstTurn |>.trans
    lens.finishJunction_eq_before

theorem reverseTarget_ne_before :
    boundary.reverseTargetState lens.firstTurn ≠ boundary.before := by
  intro heq
  have hcoordinate := congrArg
    (fun state : collar.ScalarCompanionTurnState sourceEscape =>
      state.1.coordinate) heq
  rw [lens.reverseTarget_coordinate_eq_not_before] at hcoordinate
  cases boundary.before.1.coordinate <;> simp at hcoordinate

/-- Closed monodromy left after the lens geometry cancels: the endpoint is
at the same primal junction, in the opposite scalar coordinate, with one of
the four forced nonidentity incident-edge orders. -/
structure EndpointMonodromy where
  junction_eq :
    (boundary.reverseTargetState lens.firstTurn).junction =
      boundary.before.junction
  coordinate_eq :
    (boundary.reverseTargetState lens.firstTurn).1.coordinate =
      !boundary.before.1.coordinate
  edgePermutation :
    ((boundary.reverseTargetState lens.firstTurn).1.first =
          boundary.before.1.first ∧
        (boundary.reverseTargetState lens.firstTurn).1.second =
          boundary.before.1.third ∧
        (boundary.reverseTargetState lens.firstTurn).1.third =
          boundary.before.1.second) ∨
    ((boundary.reverseTargetState lens.firstTurn).1.first =
          boundary.before.1.third ∧
        (boundary.reverseTargetState lens.firstTurn).1.second =
          boundary.before.1.first ∧
        (boundary.reverseTargetState lens.firstTurn).1.third =
          boundary.before.1.second) ∨
    ((boundary.reverseTargetState lens.firstTurn).1.first =
          boundary.before.1.second ∧
        (boundary.reverseTargetState lens.firstTurn).1.second =
          boundary.before.1.third ∧
        (boundary.reverseTargetState lens.firstTurn).1.third =
          boundary.before.1.first) ∨
    ((boundary.reverseTargetState lens.firstTurn).1.first =
          boundary.before.1.third ∧
        (boundary.reverseTargetState lens.firstTurn).1.second =
          boundary.before.1.second ∧
        (boundary.reverseTargetState lens.firstTurn).1.third =
          boundary.before.1.first)
  target_ne_before :
    boundary.reverseTargetState lens.firstTurn ≠ boundary.before

/-- Every exact reverse arrival lens carries its closed endpoint monodromy. -/
def endpointMonodromy : lens.EndpointMonodromy where
  junction_eq := lens.reverseTarget_junction_eq_before
  coordinate_eq := lens.reverseTarget_coordinate_eq_not_before
  edgePermutation := lens.reverseTarget_edgePermutation
  target_ne_before := lens.reverseTarget_ne_before

end ExactReverseArrivalLens

/-- Full exact lens together with the nontrivial endpoint monodromy left
after its palindromic geometry cancels. -/
structure ExactReturnLensMonodromy where
  lens : boundary.ExactReverseArrivalLens
  endpoint : lens.EndpointMonodromy

theorem nonempty_exactReturnLensMonodromy :
    Nonempty boundary.ExactReturnLensMonodromy := by
  rcases boundary.nonempty_exactReverseArrivalLens with ⟨lens⟩
  exact ⟨{ lens := lens, endpoint := lens.endpointMonodromy }⟩

end ScalarCompanionTurnState.ImmediateReturnBoundary

namespace ScalarCompanionTurnState

/-- The support-reduced recurrent itinerary ends either on a supported
ambient primal cycle or on an exact closed endpoint monodromy. -/
theorem SupportReducedPrimalJunctionItinerary.supportedCycle_or_returnMonodromy
    (itinerary : SupportReducedPrimalJunctionItinerary
      (collar := collar) (sourceEscape := sourceEscape)) :
    (∃ (cycleRoot : collar.commonCoreVertex)
        (primalCycle : collar.commonCore.Walk cycleRoot cycleRoot),
      primalCycle.IsCycle ∧ 5 ≤ primalCycle.length ∧
        primalCycle.edges ⊆ itinerary.walk.edges) ∨
      ∃ boundary : ImmediateReturnBoundary
          (collar := collar) (sourceEscape := sourceEscape),
        Nonempty boundary.ExactReturnLensMonodromy := by
  rcases itinerary.reduced_shape with hcycle | hboundary
  · exact Or.inl hcycle
  · rcases hboundary with ⟨boundary⟩
    exact Or.inr ⟨boundary, boundary.nonempty_exactReturnLensMonodromy⟩

end ScalarCompanionTurnState

namespace ScalarCompanionTurn

/-- A signed turn now reduces to coloring content, a supported ambient primal
cycle, or an exact opposite-coordinate endpoint monodromy on a palindromic
return lens. -/
theorem hasChargedKempeReentry_or_supportedPrimalCycle_or_returnMonodromy
    {coordinate : Bool}
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    collar.HasChargedKempeReentry sourceEscape ∨
      (∃ (cycleRoot : collar.commonCoreVertex)
          (primalCycle : collar.commonCore.Walk cycleRoot cycleRoot),
        primalCycle.IsCycle ∧ 5 ≤ primalCycle.length) ∨
      ∃ boundary : ScalarCompanionTurnState.ImmediateReturnBoundary
          (collar := collar) (sourceEscape := sourceEscape),
        Nonempty boundary.ExactReturnLensMonodromy := by
  rcases turn.hasChargedKempeReentry_or_supportReducedPrimalJunctionItinerary
      with haction | hitinerary
  · exact Or.inl haction
  · rcases hitinerary with ⟨itinerary⟩
    rcases itinerary.supportedCycle_or_returnMonodromy with
      ⟨cycleRoot, primalCycle, hcycle, hlength, _hsubset⟩ |
        ⟨boundary, hmonodromy⟩
    · exact Or.inr <| Or.inl
        ⟨cycleRoot, primalCycle, hcycle, hlength⟩
    · exact Or.inr <| Or.inr ⟨boundary, hmonodromy⟩

end ScalarCompanionTurn
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
