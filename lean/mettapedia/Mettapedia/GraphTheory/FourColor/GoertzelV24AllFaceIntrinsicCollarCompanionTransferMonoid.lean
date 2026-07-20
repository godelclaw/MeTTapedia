import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionChargedKempeReentry

/-! Exact classification of the four-state companion transfer monoid. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24CorridorPumping
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

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

namespace ScalarDiscrepancyColorState

variable {coordinate : Bool}

/-- Whether the source coloring owns the distinguished color in a scalar
discrepancy state. -/
def sourceOwnsZero
    (state : ScalarDiscrepancyColorState coordinate) : Bool :=
  if state.sourceColor = crossFaceZeroColor coordinate then true else false

@[simp]
theorem sourceOwnsZero_eq_true_iff
    (state : ScalarDiscrepancyColorState coordinate) :
    state.sourceOwnsZero = true ↔
      state.sourceColor = crossFaceZeroColor coordinate := by
  simp [sourceOwnsZero]

@[simp]
theorem sourceOwnsZero_eq_false_iff
    (state : ScalarDiscrepancyColorState coordinate) :
    state.sourceOwnsZero = false ↔
      state.sourceColor ≠ crossFaceZeroColor coordinate := by
  simp [sourceOwnsZero]

/-- Exchanging the two actual colorings preserves the companion color and
reverses ownership of the distinguished color. -/
def transpose (state : ScalarDiscrepancyColorState coordinate) :
    ScalarDiscrepancyColorState coordinate :=
  ⟨(state.targetColor, state.sourceColor),
    state.targetColor_ne_zero, state.sourceColor_ne_zero, by
      rcases state.exactlyOne_zeroColor with hsource | htarget
      · exact Or.inr ⟨hsource.2, hsource.1⟩
      · exact Or.inl ⟨htarget.2, htarget.1⟩⟩

@[simp]
theorem transpose_sourceColor
    (state : ScalarDiscrepancyColorState coordinate) :
    state.transpose.sourceColor = state.targetColor := rfl

@[simp]
theorem transpose_targetColor
    (state : ScalarDiscrepancyColorState coordinate) :
    state.transpose.targetColor = state.sourceColor := rfl

@[simp]
theorem transpose_transpose
    (state : ScalarDiscrepancyColorState coordinate) :
    state.transpose.transpose = state := by
  apply Subtype.ext
  rfl

end ScalarDiscrepancyColorState

/-- The four-state transition forgets the companion color: it holds exactly
when ownership of the distinguished color changes. -/
theorem scalarDiscrepancyColorTransition_iff_sourceOwnsZero_ne
    {coordinate : Bool}
    (first second : ScalarDiscrepancyColorState coordinate) :
    ScalarDiscrepancyColorTransition first second ↔
      first.sourceOwnsZero ≠ second.sourceOwnsZero := by
  constructor
  · intro htransition
    rcases htransition with hsourceTarget | htargetSource
    · have hsecondSource :=
        second.sourceColor_ne_zeroColor_of_targetColor_eq hsourceTarget.2
      simp [ScalarDiscrepancyColorState.sourceOwnsZero,
        hsourceTarget.1, hsecondSource]
    · have hfirstSource :=
        first.sourceColor_ne_zeroColor_of_targetColor_eq htargetSource.1
      simp [ScalarDiscrepancyColorState.sourceOwnsZero,
        hfirstSource, htargetSource.2]
  · intro howners
    by_cases hfirst :
        first.sourceColor = crossFaceZeroColor coordinate <;>
      by_cases hsecond :
        second.sourceColor = crossFaceZeroColor coordinate
    · exact False.elim (howners (by
        simp [ScalarDiscrepancyColorState.sourceOwnsZero, hfirst, hsecond]))
    · exact Or.inl ⟨hfirst,
        second.targetColor_eq_zeroColor_of_sourceColor_ne hsecond⟩
    · exact Or.inr ⟨
        first.targetColor_eq_zeroColor_of_sourceColor_ne hfirst, hsecond⟩
    · exact False.elim (howners (by
        simp [ScalarDiscrepancyColorState.sourceOwnsZero, hfirst, hsecond]))

/-- One transition toggles the ownership bit. -/
theorem ScalarDiscrepancyColorTransition.sourceOwnsZero_eq_not
    {coordinate : Bool}
    {first second : ScalarDiscrepancyColorState coordinate}
    (step : ScalarDiscrepancyColorTransition first second) :
    second.sourceOwnsZero = !first.sourceOwnsZero := by
  have hne :=
    (scalarDiscrepancyColorTransition_iff_sourceOwnsZero_ne first second).1
      step
  cases hfirst : first.sourceOwnsZero <;>
    cases hsecond : second.sourceOwnsZero <;> simp_all

/-- Scalar companion transfer is symmetric. -/
theorem ScalarDiscrepancyColorTransition.symm
    {coordinate : Bool}
    {first second : ScalarDiscrepancyColorState coordinate}
    (step : ScalarDiscrepancyColorTransition first second) :
    ScalarDiscrepancyColorTransition second first := by
  rcases step with hsourceTarget | htargetSource
  · exact Or.inr ⟨hsourceTarget.2, hsourceTarget.1⟩
  · exact Or.inl ⟨htargetSource.2, htargetSource.1⟩

/-- Transposition is the canonical ownership-reversing neighbor. -/
theorem ScalarDiscrepancyColorState.transition_transpose
    {coordinate : Bool}
    (state : ScalarDiscrepancyColorState coordinate) :
    ScalarDiscrepancyColorTransition state state.transpose := by
  rcases state.exactlyOne_zeroColor with hsource | htarget
  · exact Or.inl ⟨hsource.1, hsource.1⟩
  · exact Or.inr ⟨htarget.2, htarget.2⟩

/-- Exact transfer of length `n` acts on the ownership quotient by the
parity bit of `n`. -/
theorem ExactRelationalTransfer.scalarDiscrepancy_sourceOwnsZero_eq
    {coordinate : Bool} {length : Nat}
    {start finish : ScalarDiscrepancyColorState coordinate}
    (transfer : ExactRelationalTransfer ScalarDiscrepancyColorTransition
      length start finish) :
    finish.sourceOwnsZero =
      Bool.xor length.bodd start.sourceOwnsZero := by
  induction transfer with
  | zero => simp
  | @succ length start next finish step tail ih =>
      rw [ih, step.sourceOwnsZero_eq_not]
      cases hparity : length.bodd <;>
        cases howner : start.sourceOwnsZero <;>
          simp [Nat.bodd_succ, hparity]

/-- Every closed four-state transfer has even period. -/
theorem ExactRelationalTransfer.scalarDiscrepancy_even_of_return
    {coordinate : Bool} {period : Nat}
    {state : ScalarDiscrepancyColorState coordinate}
    (transfer : ExactRelationalTransfer ScalarDiscrepancyColorTransition
      period state state) :
    Even period := by
  have howner :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.ExactRelationalTransfer.scalarDiscrepancy_sourceOwnsZero_eq
      transfer
  have hparity : period.bodd = false := by
    cases hodd : period.bodd with
    | false => rfl
    | true =>
        exfalso
        rw [hodd] at howner
        cases hstate : state.sourceOwnsZero <;> simp [hstate] at howner
  apply Nat.even_iff.mpr
  rw [Nat.mod_two_of_bodd, hparity]
  rfl

/-- Every state has a canonical exact two-step return. -/
theorem ScalarDiscrepancyColorState.exactTwoReturn
    {coordinate : Bool}
    (state : ScalarDiscrepancyColorState coordinate) :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition 2 state state := by
  simpa using ExactRelationalTransfer.succ state.transition_transpose
    (ExactRelationalTransfer.succ state.transition_transpose.symm
      (ExactRelationalTransfer.zero
        (oneStep := ScalarDiscrepancyColorTransition) state))

/-- Conversely, every even length is an exact return period at every state. -/
theorem ScalarDiscrepancyColorState.exactReturn_of_even
    {coordinate : Bool} {period : Nat}
    (state : ScalarDiscrepancyColorState coordinate)
    (heven : Even period) :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
      period state state := by
  rcases heven with ⟨repetitions, rfl⟩
  simpa [Nat.mul_two] using state.exactTwoReturn.repeat repetitions

/-- Closed reachability in the unsigned four-state monoid is exactly even
parity; it imposes no further condition on the companion color. -/
theorem scalarDiscrepancy_exactReturn_iff_even
    {coordinate : Bool} (period : Nat)
    (state : ScalarDiscrepancyColorState coordinate) :
    ExactRelationalTransfer ScalarDiscrepancyColorTransition
        period state state ↔
      Even period := by
  exact ⟨ExactRelationalTransfer.scalarDiscrepancy_even_of_return,
    state.exactReturn_of_even⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

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
  {firstHit : FirstHitSingletonCompanionTransferPath
    (collar := collar) (sourceEscape := sourceEscape)}
  {change : firstHit.TransverseCompanionChange}

namespace FirstHitSingletonCompanionTransferPath.TransverseCompanionChange.ComplementarySupportCorner

variable {corner : change.ComplementarySupportCorner}

namespace ClosedSupportRoute

/-- Every graph-extracted closed complementary-support route has positive
even period in the four-state transfer system. -/
theorem exists_positive_even_exactReturn
    (route : corner.ClosedSupportRoute) :
    ∃ period : Nat,
      ∃ state : ScalarDiscrepancyColorState
          (!firstHit.transfer.coordinate),
        0 < period ∧ Even period ∧
          ExactRelationalTransfer ScalarDiscrepancyColorTransition
            period state state := by
  rcases route.exists_positive_exactReturn with
    ⟨period, state, hpositive, hreturn⟩
  exact ⟨period, state, hpositive,
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.ExactRelationalTransfer.scalarDiscrepancy_even_of_return
      hreturn,
    hreturn⟩

end ClosedSupportRoute

/-- Complementary support therefore resolves into a charged Kempe reentry
or a positive even graph-supported return. -/
theorem canonicalKempeReentry_or_positiveEvenExactReturn
    (corner : change.ComplementarySupportCorner) :
    (∃ route : corner.ChargedSupportRoute,
      ChargedTerminalKempeAction collar sourceEscape
          (!firstHit.transfer.coordinate) route.finishRepresentative ∧
        (sourceNormal.SameBaseKempeReentry sourceEscape ∨
          collar.targetNormal.SameBaseKempeReentry collar.targetEscape)) ∨
    ∃ period : Nat,
      ∃ state : ScalarDiscrepancyColorState
          (!firstHit.transfer.coordinate),
        0 < period ∧ Even period ∧
          ExactRelationalTransfer ScalarDiscrepancyColorTransition
            period state state := by
  rcases corner.canonicalKempeReentry_or_positiveExactReturn with
    hcharged | ⟨period, state, hpositive, hreturn⟩
  · exact Or.inl hcharged
  · exact Or.inr ⟨period, state, hpositive,
      GoertzelV24AdjacentPairInsertion.AdjacentPairData.ExactRelationalTransfer.scalarDiscrepancy_even_of_return
        hreturn,
      hreturn⟩

end FirstHitSingletonCompanionTransferPath.TransverseCompanionChange.ComplementarySupportCorner

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
