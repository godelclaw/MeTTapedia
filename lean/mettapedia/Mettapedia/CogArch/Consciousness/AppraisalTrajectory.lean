import Mettapedia.CogArch.Consciousness.Valence
import Mettapedia.CogArch.ProtectedMindAgentWave

/-!
# Chronological assessments and path protection

State and transition profiles retain every actual intermediate observation,
using the existing chronological `EffectTraceInterleaving.run`.  The state
profile is a readout of the library's `List.scanl`, not another executor.
Transition assessments remain arbitrary value types.  Temporal addition is
available only when a value type carries an explicitly chosen additive
monoid; its total agrees with the existing `Valence.accumulated`.

State predicates, transition predicates and protected relations are authored
parameters.  The results select no universal monotonicity or nonnegativity
policy, scalar exchange rate, cross-subject aggregation, or consciousness
assignment.  Independent coordinates can carry different types and policies.
Protecting every transition is stronger than checking only a whole segment's
endpoints.  A transitive and reflexive relation permits the forward implication;
the converse need not hold.

The controls have equal final states and equal full two-coordinate totals,
but different chronological profiles and protection judgments.  Their repair
segment is beneficial under the stated relation; the repair does not erase a
previous violation.  A separately specified coordinate translation preserves
the complete profiles, rather than merely their totals.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.Consciousness.AppraisalTrajectory

open Mettapedia.GSLT.Dynamics.EffectTraceInterleaving
open Mettapedia.CogArch.ProtectedMindAgentWave
open Mettapedia.CogArch.Agent.WellbeingObserverTransformationBoundary
open Mettapedia.Cybernetics

universe uState uInput uValue uOther uTarget uTargetInput uCoordinate uView

variable {State : Type uState} {Input : Type uInput} {Value : Type uValue}

/-- The initial observation and every subsequent actual state observation. -/
def stateProfile (step : State → Input → State) (appraisal : State → Value)
    (initial : State) (inputs : List Input) : List Value :=
  (inputs.scanl step initial).map appraisal

/-- One assessment per input occurrence, with its actual before/after states. -/
def transitionProfile (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input Value) :
    State → List Input → List Value
  | _, [] => []
  | initial, input :: inputs =>
      appraisal initial input (step initial input) ::
        transitionProfile step appraisal (step initial input) inputs

@[simp] theorem stateProfile_nil (step : State → Input → State)
    (appraisal : State → Value) (initial : State) :
    stateProfile step appraisal initial [] = [appraisal initial] := by
  simp [stateProfile]

@[simp] theorem stateProfile_cons (step : State → Input → State)
    (appraisal : State → Value) (initial : State) (input : Input) (inputs : List Input) :
    stateProfile step appraisal initial (input :: inputs) =
      appraisal initial :: stateProfile step appraisal (step initial input) inputs := by
  simp [stateProfile]

@[simp] theorem transitionProfile_nil (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input Value) (initial : State) :
    transitionProfile step appraisal initial [] = [] := rfl

@[simp] theorem transitionProfile_cons (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input Value)
    (initial : State) (input : Input) (inputs : List Input) :
    transitionProfile step appraisal initial (input :: inputs) =
      appraisal initial input (step initial input) ::
        transitionProfile step appraisal (step initial input) inputs := rfl

/-- Indexing the state profile reads precisely the executed prefix, including
the initial state at index zero and the final state at the last index. -/
theorem stateProfile_at_prefix (step : State → Input → State)
    (appraisal : State → Value) (initial : State) (inputs : List Input)
    (index : Nat) (within : index < (stateProfile step appraisal initial inputs).length) :
    (stateProfile step appraisal initial inputs)[index] =
      appraisal (run step initial (inputs.take index)) := by
  simp [stateProfile, run]

theorem stateProfile_append (step : State → Input → State)
    (appraisal : State → Value) (initial : State) (first second : List Input) :
    stateProfile step appraisal initial (first ++ second) =
      stateProfile step appraisal initial first ++
        (stateProfile step appraisal (run step initial first) second).tail := by
  simp [stateProfile, List.scanl_append, run, List.map_tail]

@[simp] theorem transitionProfile_length (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input Value)
    (initial : State) (inputs : List Input) :
    (transitionProfile step appraisal initial inputs).length = inputs.length := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons input inputs inductionHypothesis => simp [inductionHypothesis]

/-- Each indexed assessment uses the actual adjacent executed prefixes. -/
theorem transitionProfile_at_input (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input Value)
    (initial : State) (inputs : List Input) (index : Nat) (within : index < inputs.length) :
    (transitionProfile step appraisal initial inputs)[index]'(by simpa using within) =
      appraisal (run step initial (inputs.take index)) inputs[index]
        (run step initial (inputs.take (index + 1))) := by
  induction inputs generalizing initial index with
  | nil => simp at within
  | cons input inputs inductionHypothesis =>
      cases index with
      | zero => simp
      | succ index =>
          simpa [List.take, run_cons] using
            inductionHypothesis (step initial input) index (Nat.lt_of_succ_lt_succ within)

theorem transitionProfile_append (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input Value)
    (initial : State) (first second : List Input) :
    transitionProfile step appraisal initial (first ++ second) =
      transitionProfile step appraisal initial first ++
        transitionProfile step appraisal (run step initial first) second := by
  induction first generalizing initial with
  | nil => simp
  | cons input inputs inductionHypothesis =>
      simp [inductionHypothesis]

theorem transitionProfile_sum [AddMonoid Value] (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input Value)
    (initial : State) (inputs : List Input) :
    (transitionProfile step appraisal initial inputs).sum =
      Valence.accumulated step appraisal initial inputs := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons input inputs inductionHypothesis => simp [inductionHypothesis]

/-- Readouts act on each occurrence, without needing an additive or ordered
structure.  This statement alone supplies no inverse to the readout. -/
theorem transitionProfile_readout {Other : Type uOther} (readout : Value → Other)
    (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input Value)
    (initial : State) (inputs : List Input) :
    transitionProfile step (fun before input after => readout (appraisal before input after))
      initial inputs = (transitionProfile step appraisal initial inputs).map readout := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons input inputs inductionHypothesis => simp [inductionHypothesis]

/-- A state policy applies to the initial state and every actual intermediate
state, including the final state. -/
def StatesProtected (step : State → Input → State) (appraisal : State → Value)
    (admitted : Value → Prop) (initial : State) (inputs : List Input) : Prop :=
  ∀ value ∈ stateProfile step appraisal initial inputs, admitted value

/-- A transition policy applies to every occurrence assessment. -/
def TransitionsProtected (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input Value)
    (admitted : Value → Prop) (initial : State) (inputs : List Input) : Prop :=
  ∀ value ∈ transitionProfile step appraisal initial inputs, admitted value

@[simp] theorem statesProtected_nil (step : State → Input → State)
    (appraisal : State → Value) (admitted : Value → Prop) (initial : State) :
    StatesProtected step appraisal admitted initial [] ↔ admitted (appraisal initial) := by
  simp [StatesProtected]

@[simp] theorem statesProtected_cons (step : State → Input → State)
    (appraisal : State → Value) (admitted : Value → Prop)
    (initial : State) (input : Input) (inputs : List Input) :
    StatesProtected step appraisal admitted initial (input :: inputs) ↔
      admitted (appraisal initial) ∧
        StatesProtected step appraisal admitted (step initial input) inputs := by
  simp [StatesProtected]

theorem statesProtected_initial (step : State → Input → State)
    (appraisal : State → Value) (admitted : Value → Prop)
    (initial : State) (inputs : List Input)
    (safe : StatesProtected step appraisal admitted initial inputs) :
    admitted (appraisal initial) := by
  cases inputs with
  | nil => exact (statesProtected_nil step appraisal admitted initial).1 safe
  | cons input inputs => exact (statesProtected_cons step appraisal admitted initial input inputs).1 safe |>.1

theorem statesProtected_endpoint (step : State → Input → State)
    (appraisal : State → Value) (admitted : Value → Prop)
    (initial : State) (inputs : List Input)
    (safe : StatesProtected step appraisal admitted initial inputs) :
    admitted (appraisal (run step initial inputs)) := by
  have within : inputs.length < (stateProfile step appraisal initial inputs).length := by
    simp [stateProfile]
  have finalAssessment := safe _ (List.getElem_mem within)
  simpa only [stateProfile_at_prefix, List.take_length] using finalAssessment

theorem statesProtected_append_iff (step : State → Input → State)
    (appraisal : State → Value) (admitted : Value → Prop)
    (initial : State) (first second : List Input) :
    StatesProtected step appraisal admitted initial (first ++ second) ↔
      StatesProtected step appraisal admitted initial first ∧
        StatesProtected step appraisal admitted (run step initial first) second := by
  induction first generalizing initial with
  | nil =>
      simp only [List.nil_append, statesProtected_nil, run_nil]
      exact ⟨fun safe =>
        ⟨statesProtected_initial step appraisal admitted initial second safe, safe⟩,
        And.right⟩
  | cons input inputs inductionHypothesis =>
      simp only [List.cons_append, statesProtected_cons, run_cons, inductionHypothesis]
      tauto

theorem transitionsProtected_append_iff (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input Value) (admitted : Value → Prop)
    (initial : State) (first second : List Input) :
    TransitionsProtected step appraisal admitted initial (first ++ second) ↔
      TransitionsProtected step appraisal admitted initial first ∧
        TransitionsProtected step appraisal admitted (run step initial first) second := by
  simp only [TransitionsProtected, transitionProfile_append, List.mem_append]
  exact ⟨fun safe => ⟨fun value member => safe value (Or.inl member),
    fun value member => safe value (Or.inr member)⟩,
    fun ⟨firstSafe, secondSafe⟩ value member =>
      member.elim (firstSafe value) (secondSafe value)⟩

/-- A suffix certificate cannot repair an earlier path-policy violation. -/
theorem earlier_refusal_persists (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input Value) (admitted : Value → Prop)
    (initial : State) (first second : List Input)
    (refused : ¬ TransitionsProtected step appraisal admitted initial first) :
    ¬ TransitionsProtected step appraisal admitted initial (first ++ second) :=
  fun safe => refused
    ((transitionsProtected_append_iff step appraisal admitted initial first second).1 safe).1

theorem transitionsProtected_readout_iff {Other : Type uOther} (readout : Value → Other)
    (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input Value) (admitted : Other → Prop)
    (initial : State) (inputs : List Input) :
    TransitionsProtected step
      (fun before input after => readout (appraisal before input after)) admitted initial inputs ↔
      TransitionsProtected step appraisal (fun value => admitted (readout value)) initial inputs := by
  simp [TransitionsProtected, transitionProfile_readout]

/-- Independent coordinate types retain independently authored policies. -/
theorem transitionsProtected_coordinates_iff {Coordinate : Type uCoordinate}
    {CoordinateValue : Coordinate → Type uValue}
    (step : State → Input → State)
    (appraisal : Valence.TransitionAppraisal State Input (∀ coordinate, CoordinateValue coordinate))
    (admitted : ∀ coordinate, CoordinateValue coordinate → Prop)
    (initial : State) (inputs : List Input) :
    TransitionsProtected step appraisal (fun values => ∀ coordinate, admitted coordinate (values coordinate))
      initial inputs ↔
      ∀ coordinate, TransitionsProtected step
        (fun before input after => appraisal before input after coordinate)
        (admitted coordinate) initial inputs := by
  constructor
  · intro safe coordinate
    apply (transitionsProtected_readout_iff
      (fun values : ∀ c, CoordinateValue c => values coordinate)
      step appraisal (admitted coordinate) initial inputs).2
    exact fun value member => safe value member coordinate
  · intro safe value member coordinate
    have component := (transitionsProtected_readout_iff
      (fun values : ∀ c, CoordinateValue c => values coordinate)
      step appraisal (admitted coordinate) initial inputs).1 (safe coordinate)
    exact component value member

/-! ## Translations preserve every actual intermediate assessment -/

theorem run_map {Target : Type uTarget} {TargetInput : Type uTargetInput}
    (step : State → Input → State) (targetStep : Target → TargetInput → Target)
    (mapState : State → Target) (mapInput : Input → TargetInput)
    (commutes : ∀ state input,
      mapState (step state input) = targetStep (mapState state) (mapInput input))
    (initial : State) (inputs : List Input) :
    run targetStep (mapState initial) (inputs.map mapInput) = mapState (run step initial inputs) := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons input inputs inductionHypothesis =>
      simp only [List.map_cons, run_cons]
      rw [← commutes, inductionHypothesis]

theorem stateProfile_map {Target : Type uTarget} {TargetInput : Type uTargetInput}
    (step : State → Input → State) (targetStep : Target → TargetInput → Target)
    (mapState : State → Target) (mapInput : Input → TargetInput)
    (commutes : ∀ state input,
      mapState (step state input) = targetStep (mapState state) (mapInput input))
    (appraisal : State → Value) (targetAppraisal : Target → Value)
    (agrees : ∀ state, targetAppraisal (mapState state) = appraisal state)
    (initial : State) (inputs : List Input) :
    stateProfile targetStep targetAppraisal (mapState initial) (inputs.map mapInput) =
      stateProfile step appraisal initial inputs := by
  induction inputs generalizing initial with
  | nil => simp [agrees]
  | cons input inputs inductionHypothesis =>
      simp only [List.map_cons, stateProfile_cons]
      rw [agrees, ← commutes, inductionHypothesis]

theorem transitionProfile_map {Target : Type uTarget} {TargetInput : Type uTargetInput}
    (step : State → Input → State) (targetStep : Target → TargetInput → Target)
    (mapState : State → Target) (mapInput : Input → TargetInput)
    (commutes : ∀ state input,
      mapState (step state input) = targetStep (mapState state) (mapInput input))
    (appraisal : Valence.TransitionAppraisal State Input Value)
    (targetAppraisal : Valence.TransitionAppraisal Target TargetInput Value)
    (agrees : ∀ state input,
      targetAppraisal (mapState state) (mapInput input) (mapState (step state input)) =
        appraisal state input (step state input))
    (initial : State) (inputs : List Input) :
    transitionProfile targetStep targetAppraisal (mapState initial) (inputs.map mapInput) =
      transitionProfile step appraisal initial inputs := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons input inputs inductionHypothesis =>
      simp only [List.map_cons, transitionProfile_cons]
      rw [← commutes, agrees, inductionHypothesis]

/-- Translation also preserves an assessed suffix in its actual prefix
context, rather than resetting that suffix to the original initial state.
These contexts are finite input prefixes; other component interventions
require their own commutation laws. -/
theorem transitionProfile_map_after_prefix {Target : Type uTarget} {TargetInput : Type uTargetInput}
    (step : State → Input → State) (targetStep : Target → TargetInput → Target)
    (mapState : State → Target) (mapInput : Input → TargetInput)
    (commutes : ∀ state input,
      mapState (step state input) = targetStep (mapState state) (mapInput input))
    (appraisal : Valence.TransitionAppraisal State Input Value)
    (targetAppraisal : Valence.TransitionAppraisal Target TargetInput Value)
    (agrees : ∀ state input,
      targetAppraisal (mapState state) (mapInput input) (mapState (step state input)) =
        appraisal state input (step state input))
    (initial : State) (earlier suffix : List Input) :
    transitionProfile targetStep targetAppraisal
      (run targetStep (mapState initial) (earlier.map mapInput)) (suffix.map mapInput) =
      transitionProfile step appraisal (run step initial earlier) suffix := by
  rw [run_map step targetStep mapState mapInput commutes]
  exact transitionProfile_map step targetStep mapState mapInput commutes
    appraisal targetAppraisal agrees _ suffix

/-- Every predicate on the retained transition assessments is transported,
including independent coordinate constraints. -/
theorem transitionsProtected_map_iff {Target : Type uTarget} {TargetInput : Type uTargetInput}
    (step : State → Input → State) (targetStep : Target → TargetInput → Target)
    (mapState : State → Target) (mapInput : Input → TargetInput)
    (commutes : ∀ state input,
      mapState (step state input) = targetStep (mapState state) (mapInput input))
    (appraisal : Valence.TransitionAppraisal State Input Value)
    (targetAppraisal : Valence.TransitionAppraisal Target TargetInput Value)
    (agrees : ∀ state input,
      targetAppraisal (mapState state) (mapInput input) (mapState (step state input)) =
        appraisal state input (step state input))
    (admitted : Value → Prop) (initial : State) (inputs : List Input) :
    TransitionsProtected targetStep targetAppraisal admitted (mapState initial) (inputs.map mapInput) ↔
      TransitionsProtected step appraisal admitted initial inputs := by
  unfold TransitionsProtected
  rw [transitionProfile_map step targetStep mapState mapInput commutes appraisal targetAppraisal agrees]

/-! ## The existing observer-visible protected relation, applied along a path -/

/-- A transition constraint is checked at every actual step; it supplies no
particular order or welfare interpretation for its appraisal type. -/
def ConstraintProtected {View : Type uView} {observe : State → View}
    (step : State → Input → State) (constraint : TransitionConstraint observe)
    (initial : State) (inputs : List Input) : Prop :=
  TransitionsProtected step
    (fun before _ after => (constraint.appraisal before, constraint.appraisal after))
    (fun values => constraint.Allows values.1 values.2) initial inputs

@[simp] theorem constraintProtected_nil {View : Type uView} {observe : State → View}
    (step : State → Input → State) (constraint : TransitionConstraint observe) (initial : State) :
    ConstraintProtected step constraint initial [] := by
  simp [ConstraintProtected, TransitionsProtected]

@[simp] theorem constraintProtected_cons {View : Type uView} {observe : State → View}
    (step : State → Input → State) (constraint : TransitionConstraint observe)
    (initial : State) (input : Input) (inputs : List Input) :
    ConstraintProtected step constraint initial (input :: inputs) ↔
      constraint.Allows (constraint.appraisal initial) (constraint.appraisal (step initial input)) ∧
        ConstraintProtected step constraint (step initial input) inputs := by
  simp [ConstraintProtected, TransitionsProtected]

theorem constraintProtected_append_iff {View : Type uView} {observe : State → View}
    (step : State → Input → State) (constraint : TransitionConstraint observe)
    (initial : State) (first second : List Input) :
    ConstraintProtected step constraint initial (first ++ second) ↔
      ConstraintProtected step constraint initial first ∧
        ConstraintProtected step constraint (run step initial first) second :=
  transitionsProtected_append_iff step _ _ initial first second

/-- The existing declared observer suffices to audit every protected step. -/
theorem constraintProtected_observed_iff {View : Type uView} {observe : State → View}
    (step : State → Input → State) (constraint : TransitionConstraint observe)
    (initial : State) (inputs : List Input) :
    ConstraintProtected step constraint initial inputs ↔
      TransitionsProtected step
        (fun before _ after => (constraint.readout (observe before), constraint.readout (observe after)))
        (fun values => constraint.Allows values.1 values.2) initial inputs := by
  simp only [constraint.agrees]
  rfl

theorem constraintProtected_prod_iff {View : Type uView} {observe : State → View}
    (step : State → Input → State)
    (first : TransitionConstraint.{uState, uView, uValue} observe)
    (second : TransitionConstraint.{uState, uView, uOther} observe)
    (initial : State) (inputs : List Input) :
    ConstraintProtected step (first.prod second) initial inputs ↔
      ConstraintProtected step first initial inputs ∧ ConstraintProtected step second initial inputs := by
  induction inputs generalizing initial with
  | nil => simp
  | cons input inputs inductionHypothesis =>
      simp only [constraintProtected_cons]
      rw [inductionHypothesis]
      change ((first.Allows _ _ ∧ second.Allows _ _) ∧ (_ ∧ _)) ↔ _
      tauto

/-- Passing each local relation implies the whole endpoint relation only
when that relation has the stated reflexivity and transitivity laws. -/
theorem constraintProtected_endpoint {View : Type uView} {observe : State → View}
    (step : State → Input → State) (constraint : TransitionConstraint observe)
    (reflexive : ∀ value, constraint.Allows value value)
    (transitive : ∀ {first middle last}, constraint.Allows first middle →
      constraint.Allows middle last → constraint.Allows first last)
    (initial : State) (inputs : List Input)
    (safe : ConstraintProtected step constraint initial inputs) :
    constraint.Allows (constraint.appraisal initial) (constraint.appraisal (run step initial inputs)) := by
  induction inputs generalizing initial with
  | nil => exact reflexive _
  | cons input inputs inductionHypothesis =>
      rcases (constraintProtected_cons step constraint initial input inputs).1 safe with
        ⟨first, tail⟩
      exact transitive first (inductionHypothesis _ tail)

/-! ## Finite controls with full multidimensional totals -/

namespace Controls

abbrev Quantities := ℚ × ℚ

/-- Two independently retained quantities, with additive state updates. -/
def step (state input : Quantities) : Quantities := state + input

/-- The assessment is computed from actual endpoint differences. -/
def appraisal : Valence.TransitionAppraisal Quantities Quantities Quantities :=
  fun before _ after => after - before

def initial : Quantities := (0, 0)
def earlyDrop : Quantities := (-2, 1)
def repair : Quantities := (3, 0)
def exposed : List Quantities := [earlyDrop, repair]
def buffered : List Quantities := [repair, earlyDrop]

/-- This authored policy permits decreases within the nonnegative region;
it is deliberately not a universal monotonicity policy. -/
def floorConstraint : TransitionConstraint (id : Quantities → Quantities) where
  Appraisal := Quantities
  appraisal := id
  readout := id
  agrees := fun _ => rfl
  Allows := fun _ after => 0 ≤ after.1 ∧ 0 ≤ after.2

def summaryObserver : Observer (List Quantities) (Quantities × Quantities) where
  observe inputs := (run step initial inputs, Valence.accumulated step appraisal initial inputs)

/-- Even identical occurrences, rearranged, can differ at intermediate states
while retaining the same endpoint and complete two-coordinate total. -/
theorem same_occurrences_endpoint_and_full_total :
    exposed.Perm buffered ∧ summaryObserver.observe exposed = summaryObserver.observe buffered ∧
      summaryObserver.observe exposed = ((1, 1), (1, 1)) := by
  refine ⟨List.Perm.swap _ _ [], ?_, ?_⟩ <;>
    norm_num [summaryObserver, run, Valence.accumulated, step, appraisal,
      initial, exposed, buffered, earlyDrop, repair]

theorem different_chronological_profiles :
    stateProfile step id initial exposed ≠ stateProfile step id initial buffered ∧
      transitionProfile step appraisal initial exposed ≠
        transitionProfile step appraisal initial buffered := by
  norm_num [stateProfile, transitionProfile, step, appraisal,
    initial, exposed, buffered, earlyDrop, repair]

/-- Both endpoint coordinates pass the stated relation, but only one complete
chronological path passes that relation at every actual transition. -/
theorem endpoint_acceptance_does_not_certify_path :
    floorConstraint.Allows (floorConstraint.appraisal initial)
        (floorConstraint.appraisal (run step initial exposed)) ∧
      ConstraintProtected step floorConstraint initial buffered ∧
      ¬ ConstraintProtected step floorConstraint initial exposed := by
  dsimp only [floorConstraint]
  norm_num [ConstraintProtected, TransitionsProtected, transitionProfile,
    run, step, initial, exposed, buffered, earlyDrop, repair]

/-- Checking the initial state too gives the same discriminating result here. -/
theorem full_state_protection_distinguishes_paths :
    StatesProtected step id (fun values => 0 ≤ values.1 ∧ 0 ≤ values.2) initial buffered ∧
      ¬ StatesProtected step id (fun values => 0 ≤ values.1 ∧ 0 ≤ values.2) initial exposed := by
  norm_num [StatesProtected, stateProfile, step,
    initial, exposed, buffered, earlyDrop, repair]

/-- Repair is a genuine improvement from the negative intermediate state and
is permitted as its own segment.  It leaves the earlier refusal intact. -/
theorem beneficial_repair_does_not_erase_refusal :
    Valence.accumulated step appraisal (run step initial [earlyDrop]) [repair] = (3, 0) ∧
      ConstraintProtected step floorConstraint (run step initial [earlyDrop]) [repair] ∧
      ¬ ConstraintProtected step floorConstraint initial ([earlyDrop] ++ [repair]) := by
  dsimp only [floorConstraint]
  norm_num [ConstraintProtected, TransitionsProtected, transitionProfile,
    Valence.accumulated, run, step, appraisal, initial, earlyDrop, repair]

/-- A complete numerical endpoint/total summary still cannot reconstruct the
chronological appraisal list.  This is stronger than scalar readout loss. -/
theorem chronological_appraisal_not_visible_in_summary :
    ¬ AppraisalVisibleAt (transitionProfile step appraisal initial) summaryObserver :=
  appraisal_not_visible_of_collision same_occurrences_endpoint_and_full_total.2.1
    different_chronological_profiles.2

theorem path_permission_not_visible_in_summary :
    ¬ AppraisalVisibleAt (ConstraintProtected step floorConstraint initial) summaryObserver := by
  apply appraisal_not_visible_of_collision
    (first := exposed) (second := buffered) same_occurrences_endpoint_and_full_total.2.1
  intro same
  exact endpoint_acceptance_does_not_certify_path.2.2
    (same ▸ endpoint_acceptance_does_not_certify_path.2.1)

/-! The target has independently written updates and assessments.  Its
coordinates exchange roles and use distinct positive scaling factors. -/

def encode (values : Quantities) : Quantities := (2 * values.2, 3 * values.1)
def decode (values : Quantities) : Quantities := (values.2 / 3, values.1 / 2)
def encodedStep (state input : Quantities) : Quantities :=
  (state.1 + input.1, state.2 + input.2)
def encodedAppraisal : Valence.TransitionAppraisal Quantities Quantities Quantities :=
  fun before _ after => ((after.2 - before.2) / 3, (after.1 - before.1) / 2)

theorem encoded_tick_commutes (state input : Quantities) :
    encode (step state input) = encodedStep (encode state) (encode input) := by
  apply Prod.ext <;> simp [encode, step, encodedStep] <;> ring

theorem encoded_state_appraisal_agrees (state : Quantities) : decode (encode state) = state := by
  apply Prod.ext <;> simp [decode, encode]

theorem encoded_transition_appraisal_agrees (state input : Quantities) :
    encodedAppraisal (encode state) (encode input) (encode (step state input)) =
      appraisal state input (step state input) := by
  apply Prod.ext <;> simp [encodedAppraisal, encode, step, appraisal] <;> ring

/-- A nonidentity coordinate translation preserves all actual intermediate
state and transition assessments for every initial state and input trace. -/
theorem encoded_complete_profiles_agree (start : Quantities) (inputs : List Quantities) :
    stateProfile encodedStep decode (encode start) (inputs.map encode) =
        stateProfile step id start inputs ∧
      transitionProfile encodedStep encodedAppraisal (encode start) (inputs.map encode) =
        transitionProfile step appraisal start inputs := by
  exact ⟨stateProfile_map step encodedStep encode encode encoded_tick_commutes id decode
      encoded_state_appraisal_agrees start inputs,
    transitionProfile_map step encodedStep encode encode encoded_tick_commutes appraisal
      encodedAppraisal encoded_transition_appraisal_agrees start inputs⟩

end Controls

end Mettapedia.CogArch.Consciousness.AppraisalTrajectory
