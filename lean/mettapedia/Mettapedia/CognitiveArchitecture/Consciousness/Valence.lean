import Mettapedia.CognitiveArchitecture.Agent.WellbeingObserverTransformationBoundary
import Mettapedia.CognitiveArchitecture.MicroPsi.Basic
import Mettapedia.GSLT.Dynamics.EffectTraceInterleaving
import Mathlib.Tactic.Ring

/-!
# Transition appraisals and conservative assessment under uncertainty

Learning reward, an architectural affect variable, and a proposed hedonic
appraisal are distinct interfaces.  Appraisals and their chronological
composition take values in an arbitrary additive monoid, including products
and independently indexed coordinate families.  The rational potential-drop
example and prefix policy are optional specializations.  Neither a reward value
nor a mathematical appraisal certificate establishes consciousness,
patienthood, or felt pleasure.
The existing occurrence-indexed `WellbeingJudgment` records which assessor and
execution supply a value; no subject identity or cross-subject aggregation is
introduced here.

Joffily and Coricelli, "Emotional Valence and the Free-Energy Principle" (2013),
propose valence as the negative time derivative of variational free energy.
`potentialDrop` is only a unit-step finite-difference reconstruction of that
proposal.  No continuous-time limit, generative-model identification, or
empirical adequacy theorem is asserted.  Arbitrary transition appraisals remain
available alongside it.  The separate categorical account in
`Cybernetics.ReflexiveValence` uses propagation and relational polarities and is
not identified with these rational quantities.

Temporal addition is an explicit assessment convention.  `RobustPrefixNonnegative`
means nonnegative cumulative change from the starting baseline at every prefix,
under every admitted assessor.  It neither means absence of negative episodes
nor absence of suffering.  Its nonempty-domain requirement prevents an empty
assessment family from certifying anything.  This is a conservative policy
relative to stated hypotheses, not a derived definition of moral welfare.

References:
* Joffily and Coricelli (2013), https://doi.org/10.1371/journal.pcbi.1003094
* Berridge, Robinson and Aldridge (2009), "Dissecting components of reward:
  liking, wanting, and learning", https://pmc.ncbi.nlm.nih.gov/articles/PMC2756052/
* Long et al. (2024), "Taking AI Welfare Seriously",
  https://arxiv.org/abs/2411.00986
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Consciousness.Valence

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Dynamics.EffectTraceInterleaving
open Mettapedia.CognitiveArchitecture.Agent
open Mettapedia.CognitiveArchitecture.Agent.WellbeingObserverTransformationBoundary

universe uState uInput uTarget uTargetInput uHypothesis uTargetHypothesis uValue uReadout uCoordinate

variable {State : Type uState} {Input : Type uInput}

/-- An authored transition assessment, indexed by both actual endpoints and
the input occurrence.  Its interpretation is a separate hypothesis. -/
abbrev TransitionAppraisal (State : Type uState) (Input : Type uInput)
    (Value : Type uValue) :=
  State → Input → State → Value

/-- Difference over one discrete time unit, not a continuous derivative. -/
def potentialDrop (potential : State → ℚ) : TransitionAppraisal State Input ℚ :=
  fun before _ after => potential before - potential after

theorem potentialDrop_nonneg_iff (potential : State → ℚ)
    (before after : State) (input : Input) :
    0 ≤ potentialDrop potential before input after ↔
      potential after ≤ potential before := by
  exact sub_nonneg

theorem potentialDrop_scale (potential : State → ℚ) (scale : ℚ)
    (before after : State) (input : Input) :
    potentialDrop (fun state => scale * potential state) before input after =
      scale * potentialDrop potential before input after := by
  simp only [potentialDrop]
  ring

/-- Accumulate assessments along the states actually produced by `step`.
Repeated inputs contribute repeated occurrences; no set deduplication occurs. -/
def accumulated {Value : Type uValue} [AddMonoid Value]
    (step : State → Input → State)
    (appraisal : TransitionAppraisal State Input Value) : State → List Input → Value
  | _, [] => 0
  | initial, input :: inputs =>
      appraisal initial input (step initial input) +
        accumulated step appraisal (step initial input) inputs

@[simp] theorem accumulated_nil {Value : Type uValue} [AddMonoid Value]
    (step : State → Input → State)
    (appraisal : TransitionAppraisal State Input Value) (initial : State) :
    accumulated step appraisal initial [] = 0 := rfl

@[simp] theorem accumulated_cons {Value : Type uValue} [AddMonoid Value]
    (step : State → Input → State)
    (appraisal : TransitionAppraisal State Input Value) (initial : State)
    (input : Input) (inputs : List Input) :
    accumulated step appraisal initial (input :: inputs) =
      appraisal initial input (step initial input) +
        accumulated step appraisal (step initial input) inputs := rfl

/-- Temporal composition starts the second segment at the first segment's
actual endpoint.  It does not reset the system or re-use the initial state. -/
theorem accumulated_append {Value : Type uValue} [AddMonoid Value]
    (step : State → Input → State)
    (appraisal : TransitionAppraisal State Input Value) (initial : State)
    (first second : List Input) :
    accumulated step appraisal initial (first ++ second) =
      accumulated step appraisal initial first +
        accumulated step appraisal (run step initial first) second := by
  induction first generalizing initial with
  | nil => simp
  | cons input inputs inductionHypothesis =>
      simp only [List.cons_append, accumulated_cons, run_cons]
      rw [inductionHypothesis]
      exact (add_assoc _ _ _).symm

/-- An optional readout preserves chronological composition when it preserves
zero and addition.  This law does not make the readout injective. -/
theorem accumulated_readout {Value : Type uValue} {Readout : Type uReadout}
    [AddMonoid Value] [AddMonoid Readout]
    (readout : Value →+ Readout) (step : State → Input → State)
    (appraisal : TransitionAppraisal State Input Value)
    (initial : State) (inputs : List Input) :
    readout (accumulated step appraisal initial inputs) =
      accumulated step (fun before input after => readout (appraisal before input after))
        initial inputs := by
  induction inputs generalizing initial with
  | nil => exact map_zero readout
  | cons input inputs inductionHypothesis =>
      simp only [accumulated_cons, map_add]
      rw [inductionHypothesis]

/-- Every coordinate of a retained family is accumulated independently,
along the same actual execution.  No total ordering of coordinates is needed. -/
theorem accumulated_apply {Coordinate : Type uCoordinate} {Value : Type uValue}
    [AddMonoid Value] (step : State → Input → State)
    (appraisal : TransitionAppraisal State Input (Coordinate → Value))
    (initial : State) (inputs : List Input) (coordinate : Coordinate) :
    accumulated step appraisal initial inputs coordinate =
      accumulated step (fun before input after => appraisal before input after coordinate)
        initial inputs := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons input inputs inductionHypothesis =>
      simp only [accumulated_cons, Pi.add_apply]
      rw [inductionHypothesis]

/-- Finite potential differences telescope along the actual execution. -/
theorem accumulated_potentialDrop (step : State → Input → State)
    (potential : State → ℚ) (initial : State) (inputs : List Input) :
    accumulated step (potentialDrop potential) initial inputs =
      potential initial - potential (run step initial inputs) := by
  induction inputs generalizing initial with
  | nil => simp
  | cons input inputs inductionHypothesis =>
      simp only [accumulated_cons, potentialDrop, run_cons]
      rw [inductionHypothesis]
      ring

/-- Actual tick commutation and per-transition appraisal compatibility imply
transport of the complete temporal accumulation. -/
theorem accumulated_map
    {Target : Type uTarget} {TargetInput : Type uTargetInput}
    {Value : Type uValue} [AddMonoid Value]
    (step : State → Input → State) (targetStep : Target → TargetInput → Target)
    (mapState : State → Target) (mapInput : Input → TargetInput)
    (commutes : ∀ state input,
      mapState (step state input) = targetStep (mapState state) (mapInput input))
    (appraisal : TransitionAppraisal State Input Value)
    (targetAppraisal : TransitionAppraisal Target TargetInput Value)
    (agrees : ∀ state input,
      targetAppraisal (mapState state) (mapInput input)
        (mapState (step state input)) = appraisal state input (step state input))
    (initial : State) (inputs : List Input) :
    accumulated targetStep targetAppraisal (mapState initial) (inputs.map mapInput) =
      accumulated step appraisal initial inputs := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons input inputs inductionHypothesis =>
      simp only [List.map_cons, accumulated_cons]
      rw [← commutes, agrees, inductionHypothesis]

/-- The existing occurrence-indexed evidence interface can retain exact
computed appraisals, separately for each assessor.  Its evidence is arithmetic
agreement with the authored execution, not evidence of felt experience. -/
def executionJudgment {Hypothesis : Type uHypothesis} {Owner Revision : Type}
    {Value : Type uValue} [AddMonoid Value]
    (step : State → Input → State)
    (appraisal : Hypothesis → TransitionAppraisal State Input Value)
    (executions : Mettapedia.Machines.StoreOccurrenceId Owner Revision →
      State × List Input) : PatienthoodWellbeing.WellbeingJudgment Hypothesis Owner Revision where
  Value := Value
  Evidence hypothesis occurrence value :=
    PLift (accumulated step (appraisal hypothesis)
      (executions occurrence).1 (executions occurrence).2 = value)

/-- A finite run's policy permits no negative cumulative prefix relative to
its initial baseline, under a nonempty family of admitted appraisals. -/
def RobustPrefixNonnegative {Hypothesis : Type uHypothesis}
    (admitted : Set Hypothesis)
    (step : State → Input → State)
    (appraisal : Hypothesis → TransitionAppraisal State Input ℚ)
    (initial : State) (inputs : List Input) : Prop :=
  admitted.Nonempty ∧ ∀ hypothesis ∈ admitted, ∀ horizon,
    0 ≤ accumulated step (appraisal hypothesis) initial (inputs.take horizon)

theorem robustPrefixNonnegative_nil {Hypothesis : Type uHypothesis}
    {admitted : Set Hypothesis} (nonempty : admitted.Nonempty)
    (step : State → Input → State)
    (appraisal : Hypothesis → TransitionAppraisal State Input ℚ) (initial : State) :
    RobustPrefixNonnegative admitted step appraisal initial [] := by
  exact ⟨nonempty, by intros; simp⟩

/-- The empty assessor family cannot satisfy the conservative policy. -/
theorem not_robustPrefixNonnegative_empty {Hypothesis : Type uHypothesis}
    (step : State → Input → State)
    (appraisal : Hypothesis → TransitionAppraisal State Input ℚ)
    (initial : State) (inputs : List Input) :
    ¬ RobustPrefixNonnegative (∅ : Set Hypothesis) step appraisal initial inputs := by
  rintro ⟨⟨hypothesis, member⟩, _⟩
  exact member

/-- Enlarging the admitted hypothesis set cannot manufacture a permission.
A nonempty subfamily is required to retain a meaningful policy. -/
theorem robustPrefixNonnegative_of_subset {Hypothesis : Type uHypothesis}
    {smaller larger : Set Hypothesis} (nonempty : smaller.Nonempty)
    (subset : smaller ⊆ larger)
    (step : State → Input → State)
    (appraisal : Hypothesis → TransitionAppraisal State Input ℚ)
    (initial : State) (inputs : List Input)
    (safe : RobustPrefixNonnegative larger step appraisal initial inputs) :
    RobustPrefixNonnegative smaller step appraisal initial inputs := by
  exact ⟨nonempty, fun hypothesis member => safe.2 hypothesis (subset member)⟩

/-- A negative prefix for any admitted hypothesis blocks this policy even if
other assessments or the final cumulative value are positive. -/
theorem not_robustPrefixNonnegative_of_negative {Hypothesis : Type uHypothesis}
    {admitted : Set Hypothesis} (step : State → Input → State)
    (appraisal : Hypothesis → TransitionAppraisal State Input ℚ)
    (initial : State) (inputs : List Input) {hypothesis : Hypothesis}
    (member : hypothesis ∈ admitted) (horizon : Nat)
    (negative : accumulated step (appraisal hypothesis) initial
      (inputs.take horizon) < 0) :
    ¬ RobustPrefixNonnegative admitted step appraisal initial inputs := by
  intro safe
  exact (not_lt_of_ge (safe.2 hypothesis member horizon)) negative

/-- Two permitted segments compose when the second certificate is evaluated
from the first segment's actual final state and fresh local baseline. -/
theorem robustPrefixNonnegative_append {Hypothesis : Type uHypothesis}
    {admitted : Set Hypothesis} (step : State → Input → State)
    (appraisal : Hypothesis → TransitionAppraisal State Input ℚ)
    (initial : State) (first second : List Input)
    (firstSafe : RobustPrefixNonnegative admitted step appraisal initial first)
    (secondSafe : RobustPrefixNonnegative admitted step appraisal
      (run step initial first) second) :
    RobustPrefixNonnegative admitted step appraisal initial (first ++ second) := by
  refine ⟨firstSafe.1, ?_⟩
  intro hypothesis member horizon
  by_cases within : horizon ≤ first.length
  · rw [List.take_append_of_le_length within]
    exact firstSafe.2 hypothesis member horizon
  · have past : first.length ≤ horizon := Nat.le_of_lt (Nat.lt_of_not_ge within)
    rw [List.take_append, List.take_of_length_le past, accumulated_append]
    apply add_nonneg
    · simpa using firstSafe.2 hypothesis member first.length
    · exact secondSafe.2 hypothesis member (horizon - first.length)

/-- Exact transport includes every admitted target assessor.  Covering only
some target hypotheses would provide preservation for only that subfamily.
The input map describes the actual translated run; no claim about additional
target runs or reordered event occurrences is made. -/
theorem robustPrefixNonnegative_map_iff
    {Target : Type uTarget} {TargetInput : Type uTargetInput}
    {Hypothesis : Type uHypothesis} {TargetHypothesis : Type uTargetHypothesis}
    (admitted : Set Hypothesis) (targetAdmitted : Set TargetHypothesis)
    (mapHypothesis : Hypothesis → TargetHypothesis)
    (preserves : ∀ hypothesis ∈ admitted, mapHypothesis hypothesis ∈ targetAdmitted)
    (covers : ∀ targetHypothesis ∈ targetAdmitted,
      ∃ hypothesis ∈ admitted, mapHypothesis hypothesis = targetHypothesis)
    (step : State → Input → State) (targetStep : Target → TargetInput → Target)
    (mapState : State → Target) (mapInput : Input → TargetInput)
    (commutes : ∀ state input,
      mapState (step state input) = targetStep (mapState state) (mapInput input))
    (appraisal : Hypothesis → TransitionAppraisal State Input ℚ)
    (targetAppraisal : TargetHypothesis → TransitionAppraisal Target TargetInput ℚ)
    (agrees : ∀ hypothesis ∈ admitted, ∀ state input,
      targetAppraisal (mapHypothesis hypothesis) (mapState state) (mapInput input)
        (mapState (step state input)) =
          appraisal hypothesis state input (step state input))
    (initial : State) (inputs : List Input) :
    RobustPrefixNonnegative targetAdmitted targetStep targetAppraisal
      (mapState initial) (inputs.map mapInput) ↔
        RobustPrefixNonnegative admitted step appraisal initial inputs := by
  constructor
  · rintro ⟨⟨targetHypothesis, targetMember⟩, safe⟩
    obtain ⟨hypothesis, member, _⟩ := covers targetHypothesis targetMember
    refine ⟨⟨hypothesis, member⟩, ?_⟩
    intro sourceHypothesis sourceMember horizon
    have bound := safe (mapHypothesis sourceHypothesis)
      (preserves sourceHypothesis sourceMember) horizon
    rw [← List.map_take, accumulated_map step targetStep mapState mapInput
      commutes (appraisal sourceHypothesis) _
      (agrees sourceHypothesis sourceMember)] at bound
    exact bound
  · rintro ⟨⟨hypothesis, member⟩, safe⟩
    refine ⟨⟨mapHypothesis hypothesis, preserves hypothesis member⟩, ?_⟩
    intro targetHypothesis targetMember horizon
    obtain ⟨sourceHypothesis, sourceMember, rfl⟩ := covers targetHypothesis targetMember
    rw [← List.map_take, accumulated_map step targetStep mapState mapInput
      commutes (appraisal sourceHypothesis) _ (agrees sourceHypothesis sourceMember)]
    exact safe sourceHypothesis sourceMember horizon

/-! ## Discriminating controls -/

namespace Controls

open Mettapedia.CognitiveArchitecture.MicroPsi

/-- Four independently retained numerical assessment coordinates.  Their
experiential interpretation is deliberately not supplied by these controls. -/
inductive AssessmentAxis where
  | pain
  | suffering
  | joy
  | happiness
  deriving DecidableEq

def advance (state : ℕ) (_ : Bool) : ℕ := state + 1

/-- Two kinds of input occurrence affect different coordinate pairs.
This authored example makes no claim that positive and negative experience
must cancel, or that one coordinate determines another. -/
def fourCoordinateAssessment :
    TransitionAppraisal ℕ Bool (AssessmentAxis → ℚ) :=
  fun _ input _ coordinate =>
    match coordinate with
    | .pain | .joy => if input then 1 else 0
    | .suffering | .happiness => if input then 0 else 1

/-- A possible balance readout, chosen solely to exhibit information loss.
The complete profile remains the primary assessment. -/
def balanceReadout : (AssessmentAxis → ℚ) →+ ℚ where
  toFun profile :=
    (profile .joy + profile .happiness) - (profile .pain + profile .suffering)
  map_zero' := by simp
  map_add' := by
    intro first second
    simp only [Pi.add_apply]
    ring

def balanceObserver : Observer (List Bool) ℚ where
  observe inputs := balanceReadout (accumulated advance fourCoordinateAssessment 0 inputs)

def painSufferingProfile (inputs : List Bool) : ℚ × ℚ :=
  let profile := accumulated advance fourCoordinateAssessment 0 inputs
  (profile .pain, profile .suffering)

/-- Equal scalar balance and equal final state conceal different pain and
suffering coordinates in genuinely executed histories. -/
theorem balance_does_not_determine_pain_suffering :
    run advance 0 [true] = run advance 0 [false] ∧
      balanceObserver.observe [true] = balanceObserver.observe [false] ∧
      painSufferingProfile [true] ≠ painSufferingProfile [false] ∧
      ¬ AppraisalVisibleAt painSufferingProfile balanceObserver := by
  have same : balanceObserver.observe [true] = balanceObserver.observe [false] := by
    norm_num [balanceObserver, balanceReadout, accumulated, fourCoordinateAssessment]
  have different : painSufferingProfile [true] ≠ painSufferingProfile [false] := by
    norm_num [painSufferingProfile, accumulated, fourCoordinateAssessment]
  exact ⟨rfl, same, different, appraisal_not_visible_of_collision same different⟩

/-- All four authored quantities can be positive in one accumulated profile,
even when the optional balance is zero. -/
theorem all_four_positive_at_zero_balance :
    (∀ coordinate, accumulated advance fourCoordinateAssessment 0 [true, false]
      coordinate = 1) ∧ balanceObserver.observe [true, false] = 0 := by
  constructor
  · intro coordinate
    cases coordinate <;> norm_num [accumulated, fourCoordinateAssessment]
  · norm_num [balanceObserver, balanceReadout, accumulated, fourCoordinateAssessment]

/-- Repeated occurrences contribute separately instead of being deduplicated. -/
theorem repeated_inputs_retain_multiplicity :
    accumulated advance fourCoordinateAssessment 0 [true, true] .pain = 2 ∧
      accumulated advance fourCoordinateAssessment 0 [true, true] .suffering = 0 := by
  norm_num [accumulated, fourCoordinateAssessment]

/-- The same reported reward coexists with independently authored PAD states. -/
abbrev LearningAffect := ℚ × PADState

def rewardObserver : Observer LearningAffect ℚ where
  observe := Prod.fst

def pleasureAppraisal (state : LearningAffect) : ℚ := state.2.pleasure.val

def rewardEqualHigh : LearningAffect := (7, PADState.happy)
def rewardEqualLow : LearningAffect := (7, PADState.sad)

/-- Equal learning reward does not make the architectural pleasure variable
recoverable.  These PAD labels do not establish experienced happiness. -/
theorem reward_does_not_determine_pleasure :
    rewardObserver.observe rewardEqualHigh = rewardObserver.observe rewardEqualLow ∧
      pleasureAppraisal rewardEqualHigh ≠ pleasureAppraisal rewardEqualLow ∧
      ¬ AppraisalVisibleAt pleasureAppraisal rewardObserver := by
  have different : pleasureAppraisal rewardEqualHigh ≠ pleasureAppraisal rewardEqualLow := by
    norm_num [pleasureAppraisal, rewardEqualHigh, rewardEqualLow,
      PADState.happy, PADState.sad, Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue.one,
      Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue.zero]
  exact ⟨rfl, different, appraisal_not_visible_of_collision
    (first := rewardEqualHigh) (second := rewardEqualLow) rfl different⟩

/-- Enriching the observer by the PAD coordinate earns the missing readout. -/
def affectObserver : Observer LearningAffect (ℚ × ℚ) where
  observe state := (state.1, state.2.pleasure.val)

theorem pleasure_visible_with_affect :
    AppraisalVisibleAt pleasureAppraisal affectObserver :=
  ⟨Prod.snd, fun _ => rfl⟩

/-- True increases a toy potential; false decreases it. -/
def move (state : ℚ) (input : Bool) : ℚ :=
  if input then state + 1 else state - 1

/-- Two admitted hypotheses retain distinct magnitudes with the same sign. -/
def assessment (sensitive : Bool) : TransitionAppraisal ℚ Bool ℚ :=
  potentialDrop (fun state => (if sensitive then 2 else 1) * state)

/-- Both appraisals certify the actual two-step decreasing trajectory. -/
theorem decreasing_run_robust :
    RobustPrefixNonnegative Set.univ move assessment 3 [false, false] := by
  refine ⟨⟨false, Set.mem_univ _⟩, ?_⟩
  intro hypothesis _ horizon
  cases hypothesis <;> cases horizon with
  | zero => simp
  | succ horizon =>
      cases horizon <;>
        norm_num [accumulated, assessment, potentialDrop, move, List.take]

/-- Change coordinates by a factor of two and reverse the input tags. -/
def encodedMove (state : ℚ) (input : Bool) : ℚ :=
  if input then state - 2 else state + 2

def encodedAssessment (hypothesis : Bool) : TransitionAppraisal ℚ Bool ℚ :=
  potentialDrop (fun state => if hypothesis then state / 2 else state)

theorem coordinate_tick_commutes (state : ℚ) (input : Bool) :
    2 * move state input = encodedMove (2 * state) (!input) := by
  cases input <;> simp [move, encodedMove] <;> ring

theorem coordinate_appraisal_commutes (hypothesis : Bool)
    (state : ℚ) (input : Bool) :
    encodedAssessment (!hypothesis) (2 * state) (!input)
      (2 * move state input) = assessment hypothesis state input (move state input) := by
  cases hypothesis <;> cases input <;>
    simp [encodedAssessment, assessment, potentialDrop, move]

/-- The concrete coordinate and tag changes preserve the entire prefix policy,
including both distinct admitted appraisals. -/
theorem coordinate_recode_robust_iff (initial : ℚ) (inputs : List Bool) :
    RobustPrefixNonnegative Set.univ encodedMove encodedAssessment
      (2 * initial) (inputs.map Bool.not) ↔
        RobustPrefixNonnegative Set.univ move assessment initial inputs := by
  apply robustPrefixNonnegative_map_iff Set.univ Set.univ Bool.not
    (fun _ _ => Set.mem_univ _) _ move encodedMove
    (fun state => 2 * state) Bool.not coordinate_tick_commutes
    assessment encodedAssessment (fun hypothesis _ => coordinate_appraisal_commutes hypothesis)
  intro hypothesis _
  exact ⟨!hypothesis, Set.mem_univ _, Bool.not_not hypothesis⟩

theorem coordinate_recode_positive :
    RobustPrefixNonnegative Set.univ encodedMove encodedAssessment 6 [true, true] := by
  have coordinates : (2 * 3 : ℚ) = 6 := by norm_num
  simpa only [coordinates, List.map_cons, List.map_nil, Bool.not_false] using
    (coordinate_recode_robust_iff 3 [false, false]).mpr decreasing_run_robust

/-- Returning to the starting potential has zero total change but retains a
negative first prefix.  An endpoint check alone loses this distinction. -/
theorem zero_total_with_negative_prefix :
    accumulated move (assessment false) 0 [true, false] = 0 ∧
      accumulated move (assessment false) 0 [true] = -1 ∧
      ¬ RobustPrefixNonnegative Set.univ move assessment 0 [true, false] := by
  refine ⟨by norm_num [accumulated, assessment, potentialDrop, move],
    by norm_num [accumulated, assessment, potentialDrop, move], ?_⟩
  apply not_robustPrefixNonnegative_of_negative move assessment 0 [true, false]
    (hypothesis := false) (Set.mem_univ _) 1
  norm_num [accumulated, assessment, potentialDrop, move]

/-- A prefix-safe trajectory can still contain a negative individual episode.
The policy must not be advertised as a suffering-free guarantee. -/
theorem robust_policy_allows_negative_episode :
    RobustPrefixNonnegative Set.univ move assessment 3 [false, false, true] ∧
      assessment false 1 true (move 1 true) = -1 := by
  constructor
  · refine ⟨⟨false, Set.mem_univ _⟩, ?_⟩
    intro hypothesis _ horizon
    cases hypothesis <;> cases horizon with
    | zero => simp
    | succ horizon =>
        cases horizon with
        | zero => norm_num [accumulated, assessment, potentialDrop, move, List.take]
        | succ horizon =>
            cases horizon <;>
              norm_num [accumulated, assessment, potentialDrop, move, List.take]
  · norm_num [assessment, potentialDrop, move]

/-- Alternative hypotheses can disagree in polarity, not only magnitude. -/
def disputedAssessment (hypothesis : Bool) : TransitionAppraisal ℚ Bool ℚ :=
  potentialDrop (fun state => if hypothesis then -state else state)

theorem disagreement_blocks_extension :
    RobustPrefixNonnegative {false} move disputedAssessment 3 [false] ∧
      ¬ RobustPrefixNonnegative Set.univ move disputedAssessment 3 [false] := by
  constructor
  · refine ⟨⟨false, Set.mem_singleton _⟩, ?_⟩
    intro hypothesis member horizon
    have equal : hypothesis = false := Set.mem_singleton_iff.mp member
    subst hypothesis
    cases horizon <;>
      norm_num [accumulated, disputedAssessment, potentialDrop, move, List.take]
  · apply not_robustPrefixNonnegative_of_negative move disputedAssessment 3 [false]
      (hypothesis := true) (Set.mem_univ _) 1
    norm_num [accumulated, disputedAssessment, potentialDrop, move]

end Controls

end Mettapedia.CognitiveArchitecture.Consciousness.Valence
