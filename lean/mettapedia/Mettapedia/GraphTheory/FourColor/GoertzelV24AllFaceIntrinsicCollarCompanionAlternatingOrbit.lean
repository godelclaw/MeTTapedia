import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAlternatingFirstTurn
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorPumping

/-! Finite two-coordinate dynamics of successive signed turns. -/

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

/-- Coloring content produced by any charged endpoint in the alternating
turn dynamics. -/
def HasChargedKempeReentry
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) : Prop :=
  ∃ (coordinate : Bool)
      (representative : IntrinsicCollarTerminalRepresentative
        collar.intrinsicCollarPortOverlapProfile),
    ChargedTerminalKempeAction collar sourceEscape coordinate
        representative ∧
      (sourceNormal.SameBaseKempeReentry sourceEscape ∨
        collar.targetNormal.SameBaseKempeReentry collar.targetEscape)

/-- Finite data underlying a signed turn. -/
abbrev ScalarCompanionTurnSignature
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge) :=
  Bool × collar.commonCore.edgeSet × collar.commonCore.edgeSet ×
    collar.commonCore.edgeSet

namespace ScalarCompanionTurnSignature

def coordinate (signature : collar.ScalarCompanionTurnSignature) : Bool :=
  signature.1

def first (signature : collar.ScalarCompanionTurnSignature) :
    collar.commonCore.edgeSet :=
  signature.2.1

def second (signature : collar.ScalarCompanionTurnSignature) :
    collar.commonCore.edgeSet :=
  signature.2.2.1

def third (signature : collar.ScalarCompanionTurnSignature) :
    collar.commonCore.edgeSet :=
  signature.2.2.2

/-- A signature is live when its four finite fields are realized by a full
signed turn. -/
def Realized
    (signature : collar.ScalarCompanionTurnSignature)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) : Prop :=
  ∃ turn : collar.ScalarCompanionTurn sourceEscape signature.coordinate,
    turn.first = signature.first ∧
      turn.second = signature.second ∧
      turn.third = signature.third

end ScalarCompanionTurnSignature

/-- Finite state space of realized signed-turn signatures. -/
def ScalarCompanionTurnState
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :=
  { signature : collar.ScalarCompanionTurnSignature //
    signature.Realized sourceEscape }

noncomputable instance scalarCompanionTurnStateFintype :
    Fintype (collar.ScalarCompanionTurnState sourceEscape) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

namespace ScalarCompanionTurnState

/-- Canonical finite state attached to a full signed turn. -/
def ofTurn {coordinate : Bool}
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    collar.ScalarCompanionTurnState sourceEscape :=
  ⟨(coordinate, turn.first, turn.second, turn.third),
    ⟨turn, rfl, rfl, rfl⟩⟩

/-- A chosen full turn realizing a finite state. -/
noncomputable def realizedTurn
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    collar.ScalarCompanionTurn sourceEscape state.1.coordinate :=
  Classical.choose state.2

theorem realizedTurn_first
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    state.realizedTurn.first = state.1.first :=
  (Classical.choose_spec state.2).1

theorem realizedTurn_second
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    state.realizedTurn.second = state.1.second :=
  (Classical.choose_spec state.2).2.1

theorem realizedTurn_third
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    state.realizedTurn.third = state.1.third :=
  (Classical.choose_spec state.2).2.2

/-- Canonical primal junction carried by a realized finite turn state. -/
noncomputable def junction
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    collar.commonCoreVertex :=
  state.realizedTurn.junction

@[simp]
theorem ofTurn_coordinate {coordinate : Bool}
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    (ofTurn turn).1.coordinate = coordinate := rfl

@[simp]
theorem ofTurn_first {coordinate : Bool}
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    (ofTurn turn).1.first = turn.first := rfl

@[simp]
theorem ofTurn_second {coordinate : Bool}
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    (ofTurn turn).1.second = turn.second := rfl

@[simp]
theorem ofTurn_third {coordinate : Bool}
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    (ofTurn turn).1.third = turn.third := rfl

/-- Forgetting a full turn to its finite signature preserves its canonical
primal junction exactly. -/
theorem ofTurn_junction {coordinate : Bool}
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    (ofTurn turn).junction = turn.junction := by
  apply SimpleGraph.lineGraphCommonVertex_unique turn.firstSecond
  · have hmem := (ofTurn turn).realizedTurn.junction_mem_first
    rw [realizedTurn_first, ofTurn_first] at hmem
    exact hmem
  · have hmem := (ofTurn turn).realizedTurn.junction_mem_second
    rw [realizedTurn_second, ofTurn_second] at hmem
    exact hmem

end ScalarCompanionTurnState

namespace ScalarCompanionTurn

variable {coordinate : Bool}
  (turn : collar.ScalarCompanionTurn sourceEscape coordinate)

/-- Exact geometric witness for the non-action branch of one alternating
step. -/
structure NextTurnWitness where
  corner : turn.ComplementarySupportCorner
  route : corner.ClosedSupportRoute
  interior : route.FirstInteriorTransverseTurn

namespace NextTurnWitness

variable {turn : collar.ScalarCompanionTurn sourceEscape coordinate}
  (witness : turn.NextTurnWitness)

/-- Full signed turn emitted by an exact next-turn witness. -/
noncomputable def nextTurn :
    collar.ScalarCompanionTurn sourceEscape (!coordinate) :=
  witness.interior.toScalarCompanionTurn

end NextTurnWitness

/-- Strengthened one-step resolution retaining the geometry that constructs
the next turn. -/
theorem hasChargedKempeReentry_or_nextTurnWitness :
    collar.HasChargedKempeReentry sourceEscape ∨
      Nonempty turn.NextTurnWitness := by
  rcases turn.nonempty_complementarySupportCorner with ⟨corner⟩
  rcases corner.exists_kempeAction_and_sameBaseReentry_or_closedSupportRoute with
    haction | hclosed
  · rcases haction with ⟨representative, action, hreentry⟩
    exact Or.inl ⟨!coordinate, representative, action, hreentry⟩
  · rcases hclosed with ⟨route⟩
    rcases route.kempeAction_and_sameBaseReentry_or_firstInteriorTransverseTurn with
      haction | hinterior
    · rcases haction with ⟨representative, action, hreentry⟩
      exact Or.inl ⟨coordinate, representative, action, hreentry⟩
    · rcases hinterior with ⟨interior⟩
      exact Or.inr ⟨NextTurnWitness.mk corner route interior⟩

end ScalarCompanionTurn

namespace ScalarCompanionTurnState

/-- Under absence of a charged Kempe reentry, every finite turn state has
an exact next-turn witness. -/
theorem nonempty_nextTurnWitness
    (hnoAction : ¬ collar.HasChargedKempeReentry sourceEscape)
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    Nonempty state.realizedTurn.NextTurnWitness := by
  exact Or.resolve_left
    state.realizedTurn.hasChargedKempeReentry_or_nextTurnWitness hnoAction

/-- Chosen exact next-turn witness on the finite state space. -/
noncomputable def nextTurnWitness
    (hnoAction : ¬ collar.HasChargedKempeReentry sourceEscape)
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    state.realizedTurn.NextTurnWitness :=
  Classical.choice (state.nonempty_nextTurnWitness hnoAction)

/-- Deterministic representative of the serial next-turn relation. -/
noncomputable def nextTurnState
    (hnoAction : ¬ collar.HasChargedKempeReentry sourceEscape)
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    collar.ScalarCompanionTurnState sourceEscape :=
  ofTurn (state.nextTurnWitness hnoAction).nextTurn

/-- Exact relational content retained by a finite-state transition. -/
def IsExactNext
    (source target : collar.ScalarCompanionTurnState sourceEscape) : Prop :=
  ∃ witness : source.realizedTurn.NextTurnWitness,
    target = ofTurn witness.nextTurn

/-- The chosen deterministic edge is an exact geometric next-turn edge. -/
theorem nextTurnState_isExactNext
    (hnoAction : ¬ collar.HasChargedKempeReentry sourceEscape)
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    state.IsExactNext (state.nextTurnState hnoAction) :=
  ⟨state.nextTurnWitness hnoAction, rfl⟩

/-- Every exact finite-state transition traverses a nonempty primal arc
and therefore changes the canonical junction. -/
theorem IsExactNext.junction_ne
    {source target : collar.ScalarCompanionTurnState sourceEscape}
    (hexact : source.IsExactNext target) :
    target.junction ≠ source.junction := by
  rcases hexact with ⟨witness, rfl⟩
  rw [ofTurn_junction]
  exact witness.interior.toScalarCompanionTurn_junction_ne_source

/-- The chosen deterministic transition also moves to a different primal
junction. -/
theorem nextTurnState_junction_ne
    (hnoAction : ¬ collar.HasChargedKempeReentry sourceEscape)
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    (state.nextTurnState hnoAction).junction ≠ state.junction :=
  (state.nextTurnState_isExactNext hnoAction).junction_ne

/-- Every exact step toggles the scalar coordinate. -/
@[simp]
theorem nextTurnState_coordinate
    (hnoAction : ¬ collar.HasChargedKempeReentry sourceEscape)
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    (state.nextTurnState hnoAction).1.coordinate = !state.1.coordinate := rfl

end ScalarCompanionTurnState

/-- Boolean coordinate after a prescribed number of alternating steps. -/
def alternatingCoordinate : Nat → Bool → Bool
  | 0, coordinate => coordinate
  | steps + 1, coordinate => !(alternatingCoordinate steps coordinate)

theorem alternatingCoordinate_eq_self_iff_even
    (steps : Nat) (coordinate : Bool) :
    alternatingCoordinate steps coordinate = coordinate ↔ Even steps := by
  induction steps with
  | zero => simp [alternatingCoordinate]
  | succ steps ih =>
      constructor
      · intro heq
        have hne : alternatingCoordinate steps coordinate ≠ coordinate := by
          exact Bool.not_eq.mp heq
        apply Nat.even_add_one.mpr
        intro heven
        exact hne (ih.mpr heven)
      · intro heven
        have hnotEven : ¬Even steps := Nat.even_add_one.mp heven
        apply Bool.not_eq.mpr
        intro heq
        exact hnotEven (ih.mp heq)

namespace ScalarCompanionTurnState

variable (hnoAction : ¬ collar.HasChargedKempeReentry sourceEscape)

/-- Coordinates along the chosen finite orbit alternate exactly. -/
theorem iterate_nextTurnState_coordinate
    (steps : Nat)
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    (((nextTurnState hnoAction)^[steps]) state).1.coordinate =
      alternatingCoordinate steps state.1.coordinate := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      rw [nextTurnState_coordinate hnoAction, ih]
      rfl

/-- Every chosen iterate is an exact relational chain of geometric
next-turn witnesses. -/
theorem exactRelationalTransfer_iterate
    (steps : Nat)
    (state : collar.ScalarCompanionTurnState sourceEscape) :
    ExactRelationalTransfer IsExactNext steps state
      (((nextTurnState hnoAction)^[steps]) state) := by
  induction steps generalizing state with
  | zero =>
      exact ExactRelationalTransfer.zero state
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ExactRelationalTransfer.succ
        (nextTurnState_isExactNext hnoAction state)
        (ih (state.nextTurnState hnoAction))

/-- Exact finite-orbit certificate for the non-action dynamics. -/
def AlternatingOrbitCertificate
    (start : collar.ScalarCompanionTurnState sourceEscape) : Prop :=
  ∃ preperiod period : Nat,
    preperiod < Fintype.card
        (collar.ScalarCompanionTurnState sourceEscape) + 1 ∧
      0 < period ∧
      period ≤ Fintype.card
        (collar.ScalarCompanionTurnState sourceEscape) ∧
      (∀ offset repetitions : Nat,
        ((nextTurnState hnoAction)^[
          preperiod + offset + repetitions * period]) start =
        ((nextTurnState hnoAction)^[preperiod + offset]) start) ∧
      Even period

/-- Finite alternating dynamics enters a positive even-period orbit, with
the standard cardinality bounds. -/
theorem alternatingOrbitCertificate
    (start : collar.ScalarCompanionTurnState sourceEscape) :
    AlternatingOrbitCertificate hnoAction start := by
  let step := nextTurnState hnoAction
  rcases finiteDeterministicTransfer_eventuallyPeriodicIteratesWithBounds
      step start with
    ⟨preperiod, period, hpreperiod, hperiodPos, hperiodBound,
      hperiodic⟩
  have hreturn : (step^[period]) ((step^[preperiod]) start) =
      (step^[preperiod]) start := by
    calc
      (step^[period]) ((step^[preperiod]) start) =
          (step^[period + preperiod]) start :=
        (Function.iterate_add_apply step period preperiod start).symm
      _ = (step^[preperiod + period]) start := by
        apply congrArg (fun exponent => (step^[exponent]) start)
        omega
      _ = (step^[preperiod]) start := by
        simpa using hperiodic 0 1
  let entry := (step^[preperiod]) start
  have hcoordinateReturn : alternatingCoordinate period entry.1.coordinate =
      entry.1.coordinate := by
    rw [← iterate_nextTurnState_coordinate hnoAction period entry]
    exact congrArg
      (fun state : collar.ScalarCompanionTurnState sourceEscape =>
        state.1.coordinate) hreturn
  exact ⟨preperiod, period, hpreperiod, hperiodPos, hperiodBound,
    hperiodic,
    (alternatingCoordinate_eq_self_iff_even period entry.1.coordinate).1
      hcoordinateReturn⟩

theorem AlternatingOrbitCertificate.exists_period_ge_two
    {start : collar.ScalarCompanionTurnState sourceEscape}
    (certificate : AlternatingOrbitCertificate hnoAction start) :
    ∃ preperiod period : Nat,
      preperiod < Fintype.card
          (collar.ScalarCompanionTurnState sourceEscape) + 1 ∧
        2 ≤ period ∧
        period ≤ Fintype.card
          (collar.ScalarCompanionTurnState sourceEscape) ∧
        (∀ offset repetitions : Nat,
          ((nextTurnState hnoAction)^[
            preperiod + offset + repetitions * period]) start =
          ((nextTurnState hnoAction)^[preperiod + offset]) start) ∧
        Even period := by
  rcases certificate with
    ⟨preperiod, period, hpreperiod, hperiodPos, hperiodBound,
      hperiodic, heven⟩
  rcases heven with ⟨half, hhalf⟩
  have hhalfPos : 0 < half := by
    by_contra hnotPositive
    have hzero : half = 0 := Nat.eq_zero_of_not_pos hnotPositive
    rw [hzero, zero_add] at hhalf
    exact (Nat.ne_of_gt hperiodPos) hhalf
  have htwo : 2 ≤ period := by omega
  exact ⟨preperiod, period, hpreperiod, htwo, hperiodBound,
    hperiodic, ⟨half, hhalf⟩⟩

/-- The recurrent part of a non-action orbit is an exact positive even
return, not merely a repeated finite signature. -/
theorem AlternatingOrbitCertificate.exists_exact_even_return
    {start : collar.ScalarCompanionTurnState sourceEscape}
    (certificate : AlternatingOrbitCertificate hnoAction start) :
    ∃ (entry : collar.ScalarCompanionTurnState sourceEscape)
        (period : Nat),
      2 ≤ period ∧ Even period ∧
        ExactRelationalTransfer IsExactNext period entry entry := by
  rcases certificate.exists_period_ge_two with
    ⟨preperiod, period, _hpreperiod, hperiodTwo, _hperiodBound,
      hperiodic, heven⟩
  let step := nextTurnState hnoAction
  let entry := (step^[preperiod]) start
  have hreturn : (step^[period]) entry = entry := by
    calc
      (step^[period]) entry = (step^[period + preperiod]) start :=
        (Function.iterate_add_apply step period preperiod start).symm
      _ = (step^[preperiod + period]) start := by
        apply congrArg (fun exponent => (step^[exponent]) start)
        omega
      _ = (step^[preperiod]) start := by
        simpa using hperiodic 0 1
      _ = entry := rfl
  have htransfer := exactRelationalTransfer_iterate hnoAction period entry
  rw [hreturn] at htransfer
  exact ⟨entry, period, hperiodTwo, heven, htransfer⟩

/-- The exact even return begins with a genuine primal move and closes by
an exact residual chain. -/
theorem AlternatingOrbitCertificate.exists_exact_even_moving_return
    {start : collar.ScalarCompanionTurnState sourceEscape}
    (certificate : AlternatingOrbitCertificate hnoAction start) :
    ∃ (entry next : collar.ScalarCompanionTurnState sourceEscape)
        (period : Nat),
      2 ≤ period ∧ Even period ∧
        entry.IsExactNext next ∧
        next.junction ≠ entry.junction ∧
        ExactRelationalTransfer IsExactNext (period - 1) next entry := by
  rcases certificate.exists_exact_even_return with
    ⟨entry, period, hperiodTwo, heven, hreturn⟩
  cases period with
  | zero => omega
  | succ remaining =>
      cases hreturn with
      | succ hfirst htail =>
          exact ⟨entry, _, remaining + 1, hperiodTwo, heven,
            hfirst, hfirst.junction_ne, by simpa using htail⟩

end ScalarCompanionTurnState

namespace ScalarCompanionTurn

variable {coordinate : Bool}

/-- Global finite-state dichotomy from any signed turn: coloring content is
found, or the exact turn dynamics enters a bounded positive even orbit. -/
theorem hasChargedKempeReentry_or_alternatingOrbitCertificate
    (turn : collar.ScalarCompanionTurn sourceEscape coordinate) :
    collar.HasChargedKempeReentry sourceEscape ∨
      ∃ hnoAction : ¬ collar.HasChargedKempeReentry sourceEscape,
        ScalarCompanionTurnState.AlternatingOrbitCertificate hnoAction
          (ScalarCompanionTurnState.ofTurn turn) := by
  classical
  by_cases haction : collar.HasChargedKempeReentry sourceEscape
  · exact Or.inl haction
  · exact Or.inr ⟨haction,
      ScalarCompanionTurnState.alternatingOrbitCertificate haction
        (ScalarCompanionTurnState.ofTurn turn)⟩

end ScalarCompanionTurn
end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
