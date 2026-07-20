import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingPrimalReturnMonodromy

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
  {coordinate : Bool}

namespace ScalarCompanionTurn

/-- Reverse the ordered changing pair of a signed turn while retaining its
coordinate, transverse edge, and junction geometry. -/
def swapFirstSecond
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    collar.ScalarCompanionTurn sourceEscape coordinate where
  first := turn.second
  second := turn.first
  third := turn.third
  firstSecond := turn.firstSecond.symm
  firstThird := turn.secondThird
  secondThird := turn.firstThird
  firstSupport := turn.secondSupport
  secondSupport := turn.firstSupport
  companion_ne := turn.companion_ne.symm
  thirdDiscrepancy := turn.thirdDiscrepancy

@[simp] theorem swapFirstSecond_first
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    turn.swapFirstSecond.first = turn.second := rfl

@[simp] theorem swapFirstSecond_second
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    turn.swapFirstSecond.second = turn.first := rfl

@[simp] theorem swapFirstSecond_third
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    turn.swapFirstSecond.third = turn.third := rfl

theorem swapFirstSecond_involutive
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    turn.swapFirstSecond.swapFirstSecond = turn := by
  cases turn
  rfl

theorem swapFirstSecond_ne
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    turn.swapFirstSecond ≠ turn := by
  intro heq
  have hfirst := congrArg
    (fun current : collar.ScalarCompanionTurn sourceEscape coordinate =>
      current.first) heq
  exact turn.firstSecond.ne hfirst.symm

theorem swapFirstSecond_junction_eq
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    turn.swapFirstSecond.junction = turn.junction := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
    turn.swapFirstSecond.firstSecond
  · exact turn.junction_mem_second
  · exact turn.junction_mem_first

end ScalarCompanionTurn

namespace ScalarCompanionTurnState.ImmediateReturnBoundary

variable {boundary : ScalarCompanionTurnState.ImmediateReturnBoundary
  (collar := collar) (sourceEscape := sourceEscape)}

/-- Canonical coordinate toggle at the predecessor launch corner. -/
noncomputable def arrivalLaunchToggleTurn :
    collar.ScalarCompanionTurn sourceEscape
      (!boundary.before.1.coordinate) :=
  boundary.arrival.witness.corner.toggleTurn

noncomputable def arrivalLaunchToggleState :
    collar.ScalarCompanionTurnState sourceEscape :=
  ScalarCompanionTurnState.ofTurn boundary.arrivalLaunchToggleTurn

noncomputable def arrivalLaunchToggleSwapState :
    collar.ScalarCompanionTurnState sourceEscape :=
  ScalarCompanionTurnState.ofTurn
    boundary.arrivalLaunchToggleTurn.swapFirstSecond

@[simp] theorem arrivalLaunchToggleState_first :
    boundary.arrivalLaunchToggleState.1.first =
      boundary.arrival.witness.corner.incoming := rfl

@[simp] theorem arrivalLaunchToggleState_second :
    boundary.arrivalLaunchToggleState.1.second =
      boundary.before.realizedTurn.third := rfl

@[simp] theorem arrivalLaunchToggleState_third :
    boundary.arrivalLaunchToggleState.1.third =
      boundary.arrival.witness.corner.bypassed := rfl

@[simp] theorem arrivalLaunchToggleSwapState_first :
    boundary.arrivalLaunchToggleSwapState.1.first =
      boundary.before.realizedTurn.third := rfl

@[simp] theorem arrivalLaunchToggleSwapState_second :
    boundary.arrivalLaunchToggleSwapState.1.second =
      boundary.arrival.witness.corner.incoming := rfl

@[simp] theorem arrivalLaunchToggleSwapState_third :
    boundary.arrivalLaunchToggleSwapState.1.third =
      boundary.arrival.witness.corner.bypassed := rfl

theorem arrivalLaunchToggleSwapState_ne :
    boundary.arrivalLaunchToggleSwapState ≠
      boundary.arrivalLaunchToggleState := by
  intro heq
  have hfirst := congrArg
    (fun state : collar.ScalarCompanionTurnState sourceEscape =>
      state.1.first) heq
  change boundary.before.realizedTurn.third =
    boundary.arrival.witness.corner.incoming at hfirst
  exact boundary.arrival.witness.corner.incoming_third.ne hfirst.symm

namespace ExactReverseArrivalLens

variable (lens : boundary.ExactReverseArrivalLens)

/-- The four endpoint permutations reduce to two canonical toggle states:
aligned order or reversed changing-pair order. -/
theorem reverseTarget_eq_toggle_or_swap :
    boundary.reverseTargetState lens.firstTurn =
        boundary.arrivalLaunchToggleState ∨
      boundary.reverseTargetState lens.firstTurn =
        boundary.arrivalLaunchToggleSwapState := by
  rcases reverseRootAmbient_order (boundary := boundary) with
    haligned | hreversed
  · left
    apply Subtype.ext
    apply Prod.ext
    · exact lens.reverseTarget_coordinate_eq_not_before
    · apply Prod.ext
      · exact lens.reverseTarget_first.trans haligned.1
      · apply Prod.ext
        · exact lens.reverseTarget_second.trans haligned.2
        · exact lens.reverseTarget_third
  · right
    apply Subtype.ext
    apply Prod.ext
    · exact lens.reverseTarget_coordinate_eq_not_before
    · apply Prod.ext
      · exact lens.reverseTarget_first.trans hreversed.1
      · apply Prod.ext
        · exact lens.reverseTarget_second.trans hreversed.2
        · exact lens.reverseTarget_third

theorem reverseTarget_toggle_xor_swap :
    (boundary.reverseTargetState lens.firstTurn =
        boundary.arrivalLaunchToggleState ∨
      boundary.reverseTargetState lens.firstTurn =
        boundary.arrivalLaunchToggleSwapState) ∧
    ¬(boundary.reverseTargetState lens.firstTurn =
          boundary.arrivalLaunchToggleState ∧
        boundary.reverseTargetState lens.firstTurn =
          boundary.arrivalLaunchToggleSwapState) := by
  refine ⟨lens.reverseTarget_eq_toggle_or_swap, ?_⟩
  rintro ⟨haligned, hreversed⟩
  exact boundary.arrivalLaunchToggleSwapState_ne
    (hreversed.symm.trans haligned)

/-- Boolean chiral residue of the exact return lens: `false` is the aligned
toggle order and `true` is the reversed changing-pair order. -/
noncomputable def returnChirality : Bool := by
  classical
  exact if boundary.reverseTargetState lens.firstTurn =
    boundary.arrivalLaunchToggleState then false else true

def chiralTargetState (chirality : Bool) :
    collar.ScalarCompanionTurnState sourceEscape :=
  match chirality with
  | false => boundary.arrivalLaunchToggleState
  | true => boundary.arrivalLaunchToggleSwapState

theorem reverseTarget_eq_chiralTargetState :
    boundary.reverseTargetState lens.firstTurn =
      chiralTargetState (boundary := boundary) lens.returnChirality := by
  classical
  by_cases haligned : boundary.reverseTargetState lens.firstTurn =
      boundary.arrivalLaunchToggleState
  · simp [returnChirality, haligned, chiralTargetState]
  · have hreversed := Or.resolve_left
      lens.reverseTarget_eq_toggle_or_swap haligned
    simpa [returnChirality, haligned, chiralTargetState] using hreversed

theorem returnChirality_eq_false_iff :
    lens.returnChirality = false ↔
      boundary.reverseTargetState lens.firstTurn =
        boundary.arrivalLaunchToggleState := by
  classical
  simp only [returnChirality]
  by_cases haligned : boundary.reverseTargetState lens.firstTurn =
      boundary.arrivalLaunchToggleState <;> simp [haligned]

theorem returnChirality_eq_true_iff :
    lens.returnChirality = true ↔
      boundary.reverseTargetState lens.firstTurn =
        boundary.arrivalLaunchToggleSwapState := by
  classical
  by_cases haligned : boundary.reverseTargetState lens.firstTurn =
      boundary.arrivalLaunchToggleState
  · have hnotReversed : boundary.reverseTargetState lens.firstTurn ≠
        boundary.arrivalLaunchToggleSwapState := by
      intro hreversed
      exact boundary.arrivalLaunchToggleSwapState_ne
        (hreversed.symm.trans haligned)
    have htoggleNeSwap : boundary.arrivalLaunchToggleState ≠
        boundary.arrivalLaunchToggleSwapState :=
      boundary.arrivalLaunchToggleSwapState_ne.symm
    simp [returnChirality, haligned, htoggleNeSwap]
  · have hreversed := Or.resolve_left
      lens.reverseTarget_eq_toggle_or_swap haligned
    simp [returnChirality, hreversed,
      boundary.arrivalLaunchToggleSwapState_ne]

theorem chiralTargetState_injective :
    Function.Injective
      (chiralTargetState (boundary := boundary)) := by
  intro first second heq
  cases first <;> cases second
  · rfl
  · exact False.elim <| boundary.arrivalLaunchToggleSwapState_ne heq.symm
  · exact False.elim <| boundary.arrivalLaunchToggleSwapState_ne heq
  · rfl

/-- The chiral bit is the unique Boolean whose canonical target is the
actual reverse endpoint. -/
theorem reverseTarget_eq_chiralTargetState_iff
    (chirality : Bool) :
    boundary.reverseTargetState lens.firstTurn =
        chiralTargetState (boundary := boundary) chirality ↔
      chirality = lens.returnChirality := by
  constructor
  · intro htarget
    apply chiralTargetState_injective (boundary := boundary)
    exact htarget.symm.trans lens.reverseTarget_eq_chiralTargetState
  · rintro rfl
    exact lens.reverseTarget_eq_chiralTargetState

/-- Compositional binary form of the endpoint monodromy. -/
structure BinaryEndpointMonodromy where
  chirality : Bool
  endpoint_eq :
    boundary.reverseTargetState lens.firstTurn =
      chiralTargetState (boundary := boundary) chirality
  chirality_eq : chirality = lens.returnChirality

def binaryEndpointMonodromy : lens.BinaryEndpointMonodromy where
  chirality := lens.returnChirality
  endpoint_eq := lens.reverseTarget_eq_chiralTargetState
  chirality_eq := rfl

end ExactReverseArrivalLens

namespace ExactReturnLensMonodromy

variable (monodromy : boundary.ExactReturnLensMonodromy)

def binaryEndpoint : monodromy.lens.BinaryEndpointMonodromy :=
  monodromy.lens.binaryEndpointMonodromy

theorem existsUnique_returnChirality :
    ∃! chirality : Bool,
      boundary.reverseTargetState monodromy.lens.firstTurn =
        ExactReverseArrivalLens.chiralTargetState
          (boundary := boundary) chirality := by
  refine ⟨monodromy.lens.returnChirality,
    monodromy.lens.reverseTarget_eq_chiralTargetState, ?_⟩
  intro chirality hchirality
  exact (monodromy.lens.reverseTarget_eq_chiralTargetState_iff
    chirality).1 hchirality

end ExactReturnLensMonodromy
end ScalarCompanionTurnState.ImmediateReturnBoundary

namespace ScalarCompanionTurn

/-- Global binary form: the monodromy branch carries a unique chiral bit,
not an unclassified finite-state ambiguity. -/
theorem hasChargedKempeReentry_or_supportedPrimalCycle_or_uniqueReturnChirality
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    collar.HasChargedKempeReentry sourceEscape ∨
      (∃ (cycleRoot : collar.commonCoreVertex)
          (primalCycle : collar.commonCore.Walk cycleRoot cycleRoot),
        primalCycle.IsCycle ∧ 5 ≤ primalCycle.length) ∨
      ∃ boundary : ScalarCompanionTurnState.ImmediateReturnBoundary
          (collar := collar) (sourceEscape := sourceEscape),
        ∃ lens : boundary.ExactReverseArrivalLens,
          ∃! chirality : Bool,
            boundary.reverseTargetState lens.firstTurn =
              ScalarCompanionTurnState.ImmediateReturnBoundary.ExactReverseArrivalLens.chiralTargetState
                (boundary := boundary) chirality := by
  rcases turn.hasChargedKempeReentry_or_supportedPrimalCycle_or_returnMonodromy
      with haction | hcycle | ⟨boundary, hmonodromy⟩
  · exact Or.inl haction
  · exact Or.inr <| Or.inl hcycle
  · rcases hmonodromy with ⟨monodromy⟩
    exact Or.inr <| Or.inr
      ⟨boundary, monodromy.lens,
        monodromy.existsUnique_returnChirality⟩

end ScalarCompanionTurn
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
