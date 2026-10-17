import Mettapedia.Languages.C11.StatementDataInteraction
import Mettapedia.Languages.C11.FixedCoreStatements
import Mettapedia.Languages.C11.StatementHistory
import Mettapedia.Languages.C11.ExpressionEventHistory
import Mettapedia.GSLT.Distinction.SimulationComposition

/-!
# A constructed statement-machine refinement stage

The concrete statement executor and its plain-data interface have different
observation carriers. The observation adapter below encodes concrete receipts,
verdicts and requests without changing concrete configurations or transitions.
The represented machine decodes its own configurations and executes the actual
statement executor. Their constructed relation preserves complete residuals
and matches each transition with exactly one transition in either direction.

The cost of this stage counts interface transitions. It is independent of
compiler instructions, native execution time and external effect delivery.
Structural representability does not confer earned-history, ownership or
publication authority. Those predicates remain separate from this stage.

The absent-transition law is constructed through the same configuration
codec, in both directions. The actual drivers are total: refusal, terminal
expression observations and malformed packets produce explicit finishing
verdicts, rather than absent transitions. Full finite-outcome transport and
regional divergence therefore preserve those distinctions. Regional divergence
means every finite run exhausts its budget before an interaction boundary; it
does not classify a suspended request as divergence.

The `FixedLocated` section also constructs a separate join between the fixed
C core and the located occurrence machine. Executable lowering admits pure
integer operands, named assignments, conditionals, loops and ordinary control.
An earned control invariant discovers the owning fixed control through every
actual located prefix, including partial expressions and stores. Its reverse
simulation either performs an actual fixed step or strictly decreases finite
pending expression work. Completed values and source refusals coincide with
licensed located completions. The license requires supplied choices to name
ready occurrences; malformed scheduling remains a separate refusal. Missing
choices suspend, while exhausted budgets retain unfinished work. Both retain
the exact causal receipt history and saved state. Operand schedules may differ,
and arbitrarily many source loop iterations are admitted.
The common expression observer keeps defined integer values and forgets the
first failure diagnostic; individual located histories retain those exact
receipts. Allocation, function calls and nested effectful operands are outside
this common fragment, and are not replaced by vacuous transitions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.StatementMachineRefinement

open IntegerMemoryModel LocatedExpressions LocatedStatements StatementData StatementDataExecution
open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {model : Model}

abbrev ObservedTransition (model : Model) :=
  Transition (Configuration model) ReceiptData ResultData RequestData

/-- The common observation adapter instantiated with the checked C codecs. -/
def observedMachine (model : Model) (policy : SignedConversionPolicy) :
    Machine (Configuration model) ReceiptData ResultData RequestData :=
  (StatementMachine.machine model policy).relabel encodeReceipt
    (fun verdict => .source (encodeVerdict verdict)) encodeRequest

/-- Encode only the retained configurations; observations are already plain data. -/
def encodeObservedTransition : ObservedTransition model → TransitionData
  | .silent next => .silent (encodeConfiguration next)
  | .publish events next => .publish events (encodeConfiguration next)
  | .finish verdict => .finish verdict
  | .fail events => .fail events
  | .call request saved => .call request (encodeConfiguration saved)

theorem transition_encoding_commutes (transition : SourceTransition model) :
    encodeObservedTransition (transition.relabel encodeReceipt
      (fun verdict => .source (encodeVerdict verdict)) encodeRequest) = liftTransition (encodeTransition transition) := by
  cases transition <;> rfl

def Related (source : Configuration model) (data : ConfigurationData) : Prop :=
  encodeConfiguration source = data

theorem related_iff_decode (source : Configuration model) (data : ConfigurationData) :
    Related source data ↔ decodeConfiguration model data = some source := by
  constructor
  · intro related
    rw [← related]
    exact decodeConfiguration_encode model source
  · exact encodeConfiguration_decode model data source

/-- The actual data executor commutes with the concrete observation adapter. -/
theorem step_encoded (model : Model) (policy : SignedConversionPolicy) (source : Configuration model) :
    (machineData model policy).step (encodeConfiguration source) =
      ((observedMachine model policy).step source).map encodeObservedTransition := by
  cases stepped : (StatementMachine.machine model policy).step source with
  | none => simp only [StatementMachine.machine] at stepped; cases stepped
  | some transition =>
      rw [machineData_step_encoded model policy source transition stepped]
      simp only [observedMachine, Machine.relabel, stepped, Option.map_some, transition_encoding_commutes]

/-- Absence of a transition transports through the actual configuration codec.
This additional law records the stuck endpoint without treating refusals as
missing transitions. -/
theorem forward_matches_stuck (model : Model) (policy : SignedConversionPolicy) :
    MatchesStuck (observedMachine model policy) (machineData model policy) Related 1 := by
  intro source data related blocked
  change encodeConfiguration source = data at related
  have encoded := step_encoded model policy source
  rw [blocked, Option.map_none] at encoded
  have blockedData : (machineData model policy).step data = none := by
    rw [← related]
    exact encoded
  exact ⟨1, le_rfl, data, (machineData model policy).run_succ_stuck (fuel := 0) blockedData, related⟩

/-- A represented absent transition reads back to the original endpoint. -/
theorem backward_matches_stuck (model : Model) (policy : SignedConversionPolicy) :
    MatchesStuck (machineData model policy) (observedMachine model policy)
      (fun data source => Related source data) 1 := by
  intro data source related blocked
  change encodeConfiguration source = data at related
  rw [← related, step_encoded] at blocked
  have blockedSource : (observedMachine model policy).step source = none := by
    cases found : (observedMachine model policy).step source with
    | none => rfl
    | some transition => simp only [found, Option.map_some, reduceCtorEq] at blocked
  exact ⟨1, le_rfl, source,
    (observedMachine model policy).run_succ_stuck (fuel := 0) blockedSource, related⟩

/-- The concrete driver always returns an explicit transition, including its
refusal and terminal classifications. This is not a program-termination law. -/
theorem source_step_ne_none (model : Model) (policy : SignedConversionPolicy)
    (source : Configuration model) : (observedMachine model policy).step source ≠ none := by
  simp only [observedMachine, Machine.relabel, StatementMachine.machine, Option.map_some,
    ne_eq, reduceCtorEq, not_false_eq_true]

/-- The represented driver also returns a transition for malformed input. -/
theorem data_step_ne_none (model : Model) (policy : SignedConversionPolicy)
    (data : ConfigurationData) : (machineData model policy).step data ≠ none := by
  simp only [machineData, ne_eq, reduceCtorEq, not_false_eq_true]

theorem source_run_ne_stuck (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (source stopped : Configuration model) :
    ((observedMachine model policy).run fuel source).2 ≠ .stuck stopped :=
  (observedMachine model policy).run_not_stuck_of_moves (source_step_ne_none model policy)
    fuel source stopped

theorem data_run_ne_stuck (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (data stopped : ConfigurationData) :
    ((machineData model policy).run fuel data).2 ≠ .stuck stopped :=
  (machineData model policy).run_not_stuck_of_moves (data_step_ne_none model policy)
    fuel data stopped

theorem forward (model : Model) (policy : SignedConversionPolicy) :
    CostSimulation (observedMachine model policy) (machineData model policy) Related 1 where
  silent := by
    intro source data next related stepped
    change encodeConfiguration source = data at related
    rw [← related]
    have encoded := step_encoded model policy source
    rw [stepped] at encoded
    simp only [Option.map_some, encodeObservedTransition] at encoded
    exact ⟨1, le_rfl, encodeConfiguration next,
      (machineData model policy).run_succ_silent (fuel := 0) encoded, rfl⟩
  publish := by
    intro source data events next related stepped
    change encodeConfiguration source = data at related
    rw [← related]
    have encoded := step_encoded model policy source
    rw [stepped] at encoded
    simp only [Option.map_some, encodeObservedTransition] at encoded
    refine ⟨1, le_rfl, encodeConfiguration next, ?_, rfl⟩
    simpa only [Machine.run, List.append_nil] using
      (machineData model policy).run_succ_publish (fuel := 0) encoded
  finish := by
    intro source data verdict related stepped
    change encodeConfiguration source = data at related
    rw [← related]
    have encoded := step_encoded model policy source
    rw [stepped] at encoded
    simp only [Option.map_some, encodeObservedTransition] at encoded
    exact ⟨1, le_rfl, (machineData model policy).run_succ_finish (fuel := 0) encoded⟩
  fail := by
    intro source data events related stepped
    change encodeConfiguration source = data at related
    rw [← related]
    have encoded := step_encoded model policy source
    rw [stepped] at encoded
    simp only [Option.map_some, encodeObservedTransition] at encoded
    exact ⟨1, le_rfl, (machineData model policy).run_succ_fail (fuel := 0) encoded⟩
  call := by
    intro source data request saved related stepped
    change encodeConfiguration source = data at related
    rw [← related]
    have encoded := step_encoded model policy source
    rw [stepped] at encoded
    simp only [Option.map_some, encodeObservedTransition] at encoded
    exact ⟨1, le_rfl, encodeConfiguration saved,
      (machineData model policy).run_succ_call (fuel := 0) encoded, rfl⟩

theorem backward (model : Model) (policy : SignedConversionPolicy) :
    CostSimulation (machineData model policy) (observedMachine model policy)
      (fun data source => Related source data) 1 where
  silent := by
    intro data source nextData related stepped
    change encodeConfiguration source = data at related
    rw [← related] at stepped
    rw [step_encoded] at stepped
    cases found : (observedMachine model policy).step source with
    | none => rw [found] at stepped; cases stepped
    | some transition =>
        rw [found] at stepped
        cases transition with
        | silent next =>
            have same : encodeConfiguration next = nextData := by
              simpa only [Option.map_some, encodeObservedTransition, Option.some.injEq,
                Transition.silent.injEq] using stepped
            rw [← same]
            exact ⟨1, le_rfl, next, (observedMachine model policy).run_succ_silent (fuel := 0) found, rfl⟩
        | publish events next | finish verdict | fail events | call request saved => cases stepped
  publish := by
    intro data source events nextData related stepped
    change encodeConfiguration source = data at related
    rw [← related] at stepped
    rw [step_encoded] at stepped
    cases found : (observedMachine model policy).step source with
    | none => rw [found] at stepped; cases stepped
    | some transition =>
        rw [found] at stepped
        cases transition with
        | publish actualEvents next =>
            have same : actualEvents = events ∧ encodeConfiguration next = nextData := by
              simpa only [Option.map_some, encodeObservedTransition, Option.some.injEq,
                Transition.publish.injEq] using stepped
            rw [← same.1, ← same.2]
            refine ⟨1, le_rfl, next, ?_, rfl⟩
            simpa only [Machine.run, List.append_nil] using
              (observedMachine model policy).run_succ_publish (fuel := 0) found
        | silent next | finish verdict | fail actualEvents | call request saved => cases stepped
  finish := by
    intro data source verdict related stepped
    change encodeConfiguration source = data at related
    rw [← related] at stepped
    rw [step_encoded] at stepped
    cases found : (observedMachine model policy).step source with
    | none => rw [found] at stepped; cases stepped
    | some transition =>
        rw [found] at stepped
        cases transition with
        | finish actualVerdict =>
            have same : actualVerdict = verdict := by
              simpa only [Option.map_some, encodeObservedTransition, Option.some.injEq,
                Transition.finish.injEq] using stepped
            rw [← same]
            exact ⟨1, le_rfl, (observedMachine model policy).run_succ_finish (fuel := 0) found⟩
        | silent next | publish events next | fail events | call request saved => cases stepped
  fail := by
    intro data source events related stepped
    change encodeConfiguration source = data at related
    rw [← related] at stepped
    rw [step_encoded] at stepped
    cases found : (observedMachine model policy).step source with
    | none => rw [found] at stepped; cases stepped
    | some transition =>
        rw [found] at stepped
        cases transition with
        | fail actualEvents =>
            have same : actualEvents = events := by
              simpa only [Option.map_some, encodeObservedTransition, Option.some.injEq,
                Transition.fail.injEq] using stepped
            rw [← same]
            exact ⟨1, le_rfl, (observedMachine model policy).run_succ_fail (fuel := 0) found⟩
        | silent next | publish actualEvents next | finish verdict | call request saved => cases stepped
  call := by
    intro data source request savedData related stepped
    change encodeConfiguration source = data at related
    rw [← related] at stepped
    rw [step_encoded] at stepped
    cases found : (observedMachine model policy).step source with
    | none => rw [found] at stepped; cases stepped
    | some transition =>
        rw [found] at stepped
        cases transition with
        | call actualRequest saved =>
            have same : actualRequest = request ∧ encodeConfiguration saved = savedData := by
              simpa only [Option.map_some, encodeObservedTransition, Option.some.injEq,
                Transition.call.injEq] using stepped
            rw [← same.1, ← same.2]
            exact ⟨1, le_rfl, saved,
              (observedMachine model policy).run_succ_call (fuel := 0) found, rfl⟩
        | silent next | publish events next | finish verdict | fail events => cases stepped

/-- The concrete, bidirectional refinement stage at one interface step per tick. -/
def stage (model : Model) (policy : SignedConversionPolicy) :
    Stage (observedMachine model policy) (machineData model policy) :=
  Stage.ofBackward Related 1 (forward model policy) (backward model policy)

theorem stage_cost (model : Model) (policy : SignedConversionPolicy) : (stage model policy).cost = 1 := rfl

theorem completion_reflected (model : Model) (policy : SignedConversionPolicy)
    (source : Configuration model) (data : ConfigurationData) (related : Related source data)
    (fuel : Nat) (final : ((machineData model policy).observe fuel data).status.Final) :
    ∃ sourceFuel, (observedMachine model policy).observe sourceFuel source =
      (machineData model policy).observe fuel data :=
  (stage model policy).reflected related final

theorem noncompletion_preserved (model : Model) (policy : SignedConversionPolicy)
    (source : Configuration model) (data : ConfigurationData) (related : Related source data)
    (never : ∀ fuel, ¬ ((observedMachine model policy).observe fuel source).status.Final) (fuel : Nat) :
    ¬ ((machineData model policy).observe fuel data).status.Final :=
  (stage model policy).never_completes related never fuel

def encodeObservedOutcome :
    Outcome (Configuration model) ResultData RequestData → Outcome ConfigurationData ResultData RequestData
  | .finished verdict => .finished verdict
  | .faulted => .faulted
  | .suspended request saved => .suspended request (encodeConfiguration saved)
  | .stuck saved => .stuck (encodeConfiguration saved)
  | .exhausted saved => .exhausted (encodeConfiguration saved)

/-- The common outcome relation is precisely the checked configuration
encoding on each retained endpoint, including hypothetical stuck endpoints. -/
theorem outcome_related_iff_encoding
    (source : Outcome (Configuration model) ResultData RequestData)
    (data : Outcome ConfigurationData ResultData RequestData) :
    OutcomeRel Related source data ↔ encodeObservedOutcome source = data := by
  constructor
  · intro related
    cases related <;> simp_all only [encodeObservedOutcome, Related]
  · intro encoded
    rw [← encoded]
    cases source with
    | finished verdict => exact .finished verdict
    | faulted => exact .faulted
    | suspended request saved => exact .suspended request rfl
    | stuck saved => exact .stuck rfl
    | exhausted saved => exact .exhausted rfl

/-- Finite runs retain exact events, verdicts, requests and encoded residuals. -/
theorem run_encoded (model : Model) (policy : SignedConversionPolicy) (fuel : Nat)
    (source : Configuration model) :
    (machineData model policy).run fuel (encodeConfiguration source) =
      (((observedMachine model policy).run fuel source).1,
        encodeObservedOutcome ((observedMachine model policy).run fuel source).2) := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      have commute := step_encoded model policy source
      cases found : (observedMachine model policy).step source with
      | none => simp only [Machine.run, found, commute, Option.map_none, encodeObservedOutcome]
      | some transition =>
          cases transition <;> simp only [Machine.run, found, commute, Option.map_some,
            encodeObservedTransition, ih, encodeObservedOutcome]

/-- Every finite source outcome transports through the constructed common
simulation, with the interface cost bound and exact receipt occurrences. -/
theorem finite_outcomes_forward (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (source : Configuration model) (data : ConfigurationData)
    (related : Related source data) :
    ∃ count ≤ fuel, ((machineData model policy).run count data).1 =
      ((observedMachine model policy).run fuel source).1 ∧
      OutcomeRel Related ((observedMachine model policy).run fuel source).2
        ((machineData model policy).run count data).2 := by
  simpa only [Nat.one_mul] using
    (forward model policy).run_related_all (forward_matches_stuck model policy) fuel related

theorem finite_outcomes_backward (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (source : Configuration model) (data : ConfigurationData)
    (related : Related source data) :
    ∃ count ≤ fuel, ((observedMachine model policy).run count source).1 =
      ((machineData model policy).run fuel data).1 ∧
      OutcomeRel (fun data source => Related source data) ((machineData model policy).run fuel data).2
        ((observedMachine model policy).run count source).2 := by
  simpa only [Nat.one_mul] using
    (backward model policy).run_related_all (backward_matches_stuck model policy) fuel related

/-- This codec supplies the stronger equal-budget instance of full finite
transport. Verdicts, requests and complete residual configurations are kept. -/
theorem finite_outcomes_exact (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (source : Configuration model) (data : ConfigurationData)
    (related : Related source data) :
    ((machineData model policy).run fuel data).1 = ((observedMachine model policy).run fuel source).1 ∧
      OutcomeRel Related ((observedMachine model policy).run fuel source).2
        ((machineData model policy).run fuel data).2 := by
  change encodeConfiguration source = data at related
  rw [← related, run_encoded]
  exact ⟨rfl, (outcome_related_iff_encoding _ _).mpr rfl⟩

/-- An arbitrary represented pause constructs its concrete residual; the
source endpoint is not supplied as trusted lvalue or memory data. -/
theorem represented_exhausted_source (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (source : Configuration model) (data saved : ConfigurationData)
    (events : List ReceiptData) (related : Related source data)
    (paused : (machineData model policy).run fuel data = (events, .exhausted saved)) :
    ∃ residual, (observedMachine model policy).run fuel source = (events, .exhausted residual) ∧
      Related residual saved := by
  obtain ⟨eventsAgree, outcomes⟩ := finite_outcomes_exact model policy fuel source data related
  rw [paused] at eventsAgree outcomes
  obtain ⟨residual, exhausted, retained⟩ := outcomes.symm.exhausted_inv
  exact ⟨residual, Prod.ext eventsAgree.symm exhausted, retained⟩

/-- Both transition simulations and their constructed absent-transition laws
instantiate regional-divergence preservation and reflection for all related
configurations in the admitted statement profile. -/
theorem divergence_correspondence (model : Model) (policy : SignedConversionPolicy)
    (source : Configuration model) (data : ConfigurationData) (related : Related source data) :
    (observedMachine model policy).DivergesWithin source ↔
      (machineData model policy).DivergesWithin data :=
  (forward model policy).divergesWithin_iff (forward_matches_stuck model policy)
    (backward model policy) (backward_matches_stuck model policy) related

/-- A raw packet that keeps advancing must actually decode. Malformed packets
end in their distinct representation verdict instead of diverging. -/
theorem represented_divergence_is_decodable (model : Model) (policy : SignedConversionPolicy)
    (data : ConfigurationData) (diverges : (machineData model policy).DivergesWithin data) :
    ∃ source : Configuration model, Related source data := by
  cases decoded : decodeConfiguration model data with
  | some source => exact ⟨source, (related_iff_decode source data).mpr decoded⟩
  | none =>
      have finished : (machineData model policy).step data = some (.finish (.malformed data)) := by
        simp only [machineData, stepData, decoded, bind, Option.bind_none]
      obtain ⟨residual, remains⟩ := diverges 1
      rw [(machineData model policy).run_succ_finish (fuel := 0) finished] at remains
      cases remains

theorem represented_divergence_iff_decode (model : Model) (policy : SignedConversionPolicy)
    (data : ConfigurationData) :
    (machineData model policy).DivergesWithin data ↔
      ∃ source, decodeConfiguration model data = some source ∧
        (observedMachine model policy).DivergesWithin source := by
  constructor
  · intro diverges
    obtain ⟨source, related⟩ := represented_divergence_is_decodable model policy data diverges
    exact ⟨source, (related_iff_decode source data).mp related,
      (divergence_correspondence model policy source data related).mpr diverges⟩
  · rintro ⟨source, decoded, diverges⟩
    exact (divergence_correspondence model policy source data
      ((related_iff_decode source data).mpr decoded)).mp diverges

/-- Continuing a represented exhausted prefix retains the exact concrete
endpoint and divergence of both machines in the same interaction region. -/
theorem divergence_after_represented_pause (model : Model) (policy : SignedConversionPolicy)
    (fuel : Nat) (source : Configuration model) (data saved : ConfigurationData)
    (events : List ReceiptData) (related : Related source data)
    (diverges : (observedMachine model policy).DivergesWithin source)
    (paused : (machineData model policy).run fuel data = (events, .exhausted saved)) :
    ∃ residual, (observedMachine model policy).run fuel source = (events, .exhausted residual) ∧
      Related residual saved ∧ (observedMachine model policy).DivergesWithin residual ∧
      (machineData model policy).DivergesWithin saved := by
  obtain ⟨residual, sourcePaused, retained⟩ :=
    represented_exhausted_source model policy fuel source data saved events related paused
  have sourceDiverges := diverges.resume (observedMachine model policy) sourcePaused
  exact ⟨residual, sourcePaused, retained, sourceDiverges,
    (divergence_correspondence model policy residual saved retained).mp sourceDiverges⟩

theorem outcome_status_encoded (outcome : Outcome (Configuration model) ResultData RequestData) :
    (encodeObservedOutcome outcome).status = outcome.status := by
  cases outcome <;> rfl

theorem observations_exact (model : Model) (policy : SignedConversionPolicy) (fuel : Nat)
    (source : Configuration model) :
    (machineData model policy).observe fuel (encodeConfiguration source) =
      (observedMachine model policy).observe fuel source := by
  simp only [Machine.observe, run_encoded, outcome_status_encoded]

theorem pause_encoded (model : Model) (policy : SignedConversionPolicy) (fuel : Nat)
    (source saved : Configuration model) (receipts : List ReceiptData)
    (paused : (observedMachine model policy).run fuel source = (receipts, .exhausted saved)) :
    (machineData model policy).run fuel (encodeConfiguration source) =
      (receipts, .exhausted (encodeConfiguration saved)) := by
  simp only [run_encoded, paused, encodeObservedOutcome]

theorem accounts_encoded (model : Model) (policy : SignedConversionPolicy)
    (price : Configuration model → Nat) (fuel : Nat) (source : Configuration model) :
    (machineData model policy).spent (priceData model price) fuel (encodeConfiguration source) =
      (observedMachine model policy).spent price fuel source := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      have commute := step_encoded model policy source
      cases found : (observedMachine model policy).step source with
      | none => simp only [Machine.spent, found, commute, Option.map_none]
      | some transition =>
          cases transition <;> simp only [Machine.spent, found, commute, Option.map_some,
            encodeObservedTransition, ih, priceData_encoded]

theorem scheduling_delivery_realized (model : Model) (source : Configuration model)
    (before after : ConfigurationData) (choice : LocatedExpressionData.IndexData)
    (related : Related source before) (delivered : StatementDataInteraction.deliverData model before choice = some after) :
    ∃ next, Related next after ∧
      StatementDataInteraction.Delivery (represent source) choice (represent next) := by
  obtain ⟨actual, next, decoded, encoded, delivery⟩ :=
    StatementDataInteraction.deliverData_sound model before after choice delivered
  have same : actual = source := by
    rw [(related_iff_decode source before).mp related] at decoded
    exact Option.some.inj decoded.symm
  rw [same] at delivery
  exact ⟨next, encoded.symm, delivery⟩

theorem independent_delivery_realized (model : Model) (source : Configuration model)
    (target : SemanticConfiguration model) (choice : LocatedExpressionData.IndexData)
    (delivery : StatementDataInteraction.Delivery (represent source) choice target) :
    ∃ next, represent next = target ∧
      StatementDataInteraction.deliverData model (encodeConfiguration source) choice =
        some (encodeConfiguration next) :=
  StatementDataInteraction.deliverData_complete model source target choice delivery

theorem silent_source_step (model : Model) (policy : SignedConversionPolicy)
    (before after : Configuration model)
    (stepped : (observedMachine model policy).step before = some (.silent after)) :
    StatementSemantics.Step policy (represent before) none (represent after) := by
  cases executed : StatementExecution.execute policy before with
  | none =>
      cases classified : StatementMachine.classify before with
      | silent next => exact False.elim (StatementMachine.classify_not_silent _ _ classified)
      | publish receipts next | finish verdict | fail receipts | call request saved =>
          simp only [observedMachine, Machine.relabel, StatementMachine.machine, executed, classified,
            Option.map_some, Transition.relabel] at stepped
          cases stepped
  | some result =>
      rcases result with ⟨event, next⟩
      cases event with
      | some event => simp only [observedMachine, Machine.relabel, StatementMachine.machine, executed, Option.map_some, Transition.relabel] at stepped; cases stepped
      | none =>
          have same : next = after := by
            simpa only [observedMachine, Machine.relabel, StatementMachine.machine, executed, Option.map_some,
              Transition.relabel, Option.some.injEq, Transition.silent.injEq] using stepped
          rw [← same]
          exact StatementExecution.execute_sound _ _ _ _ executed

theorem publishing_source_step (model : Model) (policy : SignedConversionPolicy)
    (before after : Configuration model) (events : List ReceiptData)
    (stepped : (observedMachine model policy).step before = some (.publish events after)) :
    ∃ event, events = [encodeReceipt ⟨event, before, after⟩] ∧
      StatementSemantics.Step policy (represent before) (some event) (represent after) := by
  cases executed : StatementExecution.execute policy before with
  | none =>
      cases classified : StatementMachine.classify before with
      | publish receipts next =>
          exact False.elim (StatementMachine.classify_not_publish _ _ _ classified)
      | silent next | finish verdict | fail receipts | call request saved =>
          simp only [observedMachine, Machine.relabel, StatementMachine.machine, executed, classified,
            Option.map_some, Transition.relabel] at stepped
          cases stepped
  | some result =>
      rcases result with ⟨event, next⟩
      cases event with
      | none => simp only [observedMachine, Machine.relabel, StatementMachine.machine, executed, Option.map_some, Transition.relabel] at stepped; cases stepped
      | some event =>
          have same : [encodeReceipt ⟨event, before, next⟩] = events ∧ next = after := by
            simpa only [observedMachine, Machine.relabel, StatementMachine.machine, executed, Option.map_some,
              Transition.relabel, List.map_cons, List.map_nil, Option.some.injEq, Transition.publish.injEq] using stepped
          rw [← same.2]
          exact ⟨event, same.1.symm, StatementExecution.execute_sound _ _ _ _ executed⟩

/-- Independently judged source steps construct both concrete and represented endpoints. -/
theorem independent_step_realized (model : Model) (policy : SignedConversionPolicy)
    (before : Configuration model) (after : SemanticConfiguration model) (event : Option (Event model))
    (stepped : StatementSemantics.Step policy (represent before) event after) :
    ∃ next, represent next = after ∧
      (observedMachine model policy).step before = some (match event with
        | none => .silent next
        | some event => .publish [encodeReceipt ⟨event, before, next⟩] next) ∧
      (machineData model policy).step (encodeConfiguration before) = some (match event with
        | none => .silent (encodeConfiguration next)
        | some event => .publish [encodeReceipt ⟨event, before, next⟩] (encodeConfiguration next)) := by
  obtain ⟨next, executed, represented⟩ := StatementExecution.execute_complete _ _ _ _ stepped
  have concrete := StatementMachine.step_of_execute policy before next event executed
  refine ⟨next, represented, ?_, ?_⟩
  · cases event <;> simp only [observedMachine, Machine.relabel, concrete, Option.map_some,
      Transition.relabel, List.map_cons, List.map_nil]
  · rw [machineData_step_encoded model policy before _ concrete]
    cases event <;> simp only [encodeTransition, liftTransition, List.map_cons, List.map_nil]

noncomputable def productive (model : Model) (policy : SignedConversionPolicy) :
    (observedMachine model policy).Productive :=
  (StatementMachine.productive model policy).relabeled encodeReceipt
    (fun verdict => ResultData.source (encodeVerdict verdict)) encodeRequest

end Mettapedia.Languages.C11.StatementMachineRefinement

namespace Mettapedia.Languages.C11.StatementMachineRefinement.FixedLocated

section PureExpressions

open IntegerMemoryModel ExpressionEvents ExpressionEventExecution ExpressionEventHistory
open LocatedExpressions

variable {model : Model}

inductive Pure : Expression model → Prop where
  | value (scalar : IntegerScalar.Value model.parameters) : Pure (.value scalar)
  | load (location : Destination) : Pure (.load location)
  | arithmetic (operator : IntegerBinaryOperator) {first second : Expression model}
      (left : Pure first) (right : Pure second) : Pure (.arithmetic operator first second)
  | cast (type : IntegerType IntegerExtension) {operand : Expression model}
      (inner : Pure operand) : Pure (.cast type operand)

/-- The value observer deliberately forgets which failure was reported first. -/
def observe : FixedCore.Result model → Option (IntegerScalar.Value model.parameters)
  | .value (.integer scalar) => some scalar
  | _ => none

def evaluate (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) : Expression model → Option (IntegerScalar.Value model.parameters)
  | .value scalar => some scalar
  | .load location => (load model memory location.location).bind (fun loaded => (loadedOutcome model loaded).scalar)
  | .arithmetic operator first second => do
      let left ← evaluate policy memory first
      let right ← evaluate policy memory second
      (arithmeticOutcome model (IntegerScalar.binary model.parameters operator left right)).scalar
  | .cast type operand => do
      let input ← evaluate policy memory operand
      (castOutcome model (IntegerScalar.cast model.parameters policy type input)).scalar
  | .assignment _ _ | .update _ _ _ | .comma _ _ => none

def values (policy : SignedConversionPolicy) (memory : ObjectAccessMemory.State model.characters) :
    (expression : Expression model) → Index expression → Option (IntegerScalar.Value model.parameters)
  | .value scalar, _ => some scalar
  | .load location, _ => (load model memory location.location).bind (fun loaded => (loadedOutcome model loaded).scalar)
  | .arithmetic _ first _, .inl (.inl index) => values policy memory first index
  | .arithmetic _ _ second, .inl (.inr index) => values policy memory second index
  | .arithmetic operator first second, .inr _ => evaluate policy memory (.arithmetic operator first second)
  | .cast _ operand, .inl index => values policy memory operand index
  | .cast type operand, .inr _ => evaluate policy memory (.cast type operand)
  | .assignment _ _, _ | .update _ _ _, _ | .comma _ _, _ => none

theorem values_result (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (expression : Expression model) :
    values policy memory expression (result expression) = evaluate policy memory expression := by
  cases expression <;> rfl

theorem Pure.readOnly {expression : Expression model} (pure : Pure expression) :
    ReadOnly (compile expression) := by
  induction pure with
  | value scalar => intro index location source same; cases same
  | load location => intro index location source same; cases same
  | arithmetic operator first second ihFirst ihSecond =>
      intro index location source same
      cases index with
      | inl index =>
          cases index with
          | inl index => exact operation_map_ne_store _ _ (ihFirst index) _ _ same
          | inr index => exact operation_map_ne_store _ _ (ihSecond index) _ _ same
      | inr index => cases same
  | cast type operand ih =>
      intro index location source same
      cases index with
      | inl index => exact operation_map_ne_store _ _ (ih index) _ _ same
      | inr index => cases same

theorem Pure.equations (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters)
    {expression : Expression model} (pure : Pure expression) :
    ValueEquations policy (compile expression) memory (values policy memory expression) := by
  induction pure with
  | value scalar => intro index; rfl
  | load location => intro index; rfl
  | arithmetic operator first second ihFirst ihSecond =>
      intro index
      cases index with
      | inl index =>
          cases index with
          | inl index =>
              change _ = operationValue policy memory _ ((compile _).operation index |>.map _)
              rw [operationValue_map]
              exact ihFirst index
          | inr index =>
              change _ = operationValue policy memory _ ((compile _).operation index |>.map _)
              rw [operationValue_map]
              exact ihSecond index
      | inr index =>
          simp only [values, compile, ExpressionPlanConstruction.arithmetic, operationValue,
            compiled_result, values_result, evaluate]
  | cast type operand ih =>
      intro index
      cases index with
      | inl index =>
          change _ = operationValue policy memory _ ((compile _).operation index |>.map _)
          rw [operationValue_map]
          exact ih index
      | inr index =>
          simp only [values, compile, ExpressionPlanConstruction.cast, operationValue,
            compiled_result, values_result, evaluate]

inductive ResolvesExpression (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) : FixedCore.Expression model → Expression model → Prop where
  | constant (scalar : IntegerScalar.Value model.parameters) : ResolvesExpression policy memory arrays scopes
      (.constant scalar) (.value scalar)
  | read (name : String) (declared : ObjectAccessMemory.Lvalue) (target : FixedCore.Address)
      (range : ByteRanges.Range)
      (resolved : FixedCore.Resolves name scopes (.object declared))
      (typed : FixedCore.rootAddress declared = some target)
      (located : ArrayPointers.ElementRange (ByteRanges.heap memory.storage) arrays target.pointer range) :
      ResolvesExpression policy memory arrays scopes (.read (.named name))
        (.load ⟨FixedCore.elementLvalue target range, target.type, rfl⟩)
  | binary (operator : IntegerBinaryOperator) {first second : FixedCore.Expression model}
      {left right : Expression model}
      (firstResolved : ResolvesExpression policy memory arrays scopes first left)
      (secondResolved : ResolvesExpression policy memory arrays scopes second right) :
      ResolvesExpression policy memory arrays scopes (.binary operator first second) (.arithmetic operator left right)
  | cast (type : IntegerType IntegerExtension) {source : FixedCore.Expression model} {target : Expression model}
      (resolved : ResolvesExpression policy memory arrays scopes source target) :
      ResolvesExpression policy memory arrays scopes (.cast type source) (.cast type target)

theorem ResolvesExpression.pure {policy : SignedConversionPolicy}
    {memory : ObjectAccessMemory.State model.characters} {arrays : ArrayPointers.Catalog}
    {scopes : List (FixedCore.Scope model)} {source : FixedCore.Expression model} {target : Expression model}
    (resolved : ResolvesExpression policy memory arrays scopes source target) : Pure target := by
  induction resolved with
  | constant scalar => exact .value scalar
  | read name declared target range resolved typed located => exact .load _
  | binary operator first second ihFirst ihSecond => exact .arithmetic operator ihFirst ihSecond
  | cast type resolved ih => exact .cast type ih

theorem observe_arithmetic (operator : IntegerBinaryOperator) (first second : FixedCore.Result model) :
    observe (match FixedCore.integerOperands first second with
      | .error reason => .fault reason
      | .ok (left, right) => FixedCore.arithmeticResult (IntegerScalar.binary model.parameters operator left right)) =
    (do let left ← observe first
        let right ← observe second
        (arithmeticOutcome model (IntegerScalar.binary model.parameters operator left right)).scalar) := by
  cases first with
  | fault reason => cases second <;> rfl
  | value first =>
      cases second with
      | fault reason => cases first <;> rfl
      | value second =>
          cases first <;> cases second <;> simp only [FixedCore.integerOperands, observe, bind, Option.bind_none,
            Option.bind_some]
          cases IntegerScalar.binary model.parameters operator _ _ <;> rfl

theorem observe_cast (policy : SignedConversionPolicy) (type : IntegerType IntegerExtension)
    (operand : FixedCore.Result model) :
    observe (match FixedCore.integerOperand operand with
      | .error reason => .fault reason
      | .ok input => FixedCore.castResult (IntegerScalar.cast model.parameters policy type input)) =
      (do let input ← observe operand
          (castOutcome model (IntegerScalar.cast model.parameters policy type input)).scalar) := by
  cases operand with
  | fault reason => rfl
  | value operand =>
      cases operand <;> simp only [FixedCore.integerOperand, observe, bind, Option.bind_none, Option.bind_some]
      cases IntegerScalar.cast model.parameters policy type _ <;> rfl

theorem ResolvesExpression.evaluate {policy : SignedConversionPolicy}
    {memory : ObjectAccessMemory.State model.characters} {arrays : ArrayPointers.Catalog}
    {scopes : List (FixedCore.Scope model)} {source : FixedCore.Expression model} {target : Expression model}
    (resolved : ResolvesExpression policy memory arrays scopes source target) :
    observe (FixedCore.evaluate model policy memory arrays scopes source) = evaluate policy memory target := by
  induction resolved with
  | constant scalar => rfl
  | read name declared target range resolved typed located =>
      simp only [FixedCore.evaluate, FixedCore.locate, FixedCore.objectAddress,
        FixedCore.resolve_complete _ _ _ resolved, typed, FixedCore.readElement,
        (ArrayPointers.elementRange_iff _ _ _ _).mpr located, FixedLocated.evaluate]
      cases hRead : load model memory (FixedCore.elementLvalue target range) with
      | none => rfl
      | some observed => cases observed <;> rfl
  | @binary operator firstSource secondSource left right first second ihFirst ihSecond =>
      have observed := observe_arithmetic (model := model) operator
        (FixedCore.evaluate model policy memory arrays scopes firstSource)
        (FixedCore.evaluate model policy memory arrays scopes secondSource)
      exact observed.trans (by rw [ihFirst, ihSecond]; rfl)
  | @cast type source target resolved ih =>
      have observed := observe_cast (model := model) policy type
        (FixedCore.evaluate model policy memory arrays scopes source)
      exact observed.trans (by rw [ih]; rfl)

theorem pure_history_no_invention (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (target : Expression model)
    (resolved : ResolvesExpression policy memory arrays scopes source target)
    (events : List (Occurrence (Index target) model)) (final : SemanticState (Index target) model)
    (history : SemanticHistory policy (compile target)
      (represent (initialState (compile target) memory)) events final)
    (scalar : IntegerScalar.Value model.parameters)
    (returned : lookupScalar final.cache (result target) = some scalar) :
    observe (FixedCore.evaluate model policy memory arrays scopes source) = some scalar ∧
      final.memory = ObjectAccessMemory.represent memory := by
  obtain ⟨same, unchanged⟩ := history.readOnly_result resolved.pure.readOnly
    (resolved.pure.equations policy memory) (by simpa only [compiled_result] using returned)
  rw [compiled_result, values_result] at same
  exact ⟨resolved.evaluate.trans same, unchanged⟩

theorem Pure.total (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters)
    {expression : Expression model} (pure : Pure expression)
    {scalar : IntegerScalar.Value model.parameters}
    (defined : evaluate policy memory expression = some scalar) :
    ∀ index, ∃ value, values policy memory expression index = some value := by
  induction pure generalizing scalar with
  | value input => intro index; exact ⟨input, rfl⟩
  | load location => intro index; exact ⟨scalar, defined⟩
  | arithmetic operator first second ihFirst ihSecond =>
      obtain ⟨left, firstValue, next⟩ := Option.bind_eq_some_iff.mp defined
      obtain ⟨right, secondValue, output⟩ := Option.bind_eq_some_iff.mp next
      intro index
      cases index with
      | inl index =>
          cases index with
          | inl index => exact ihFirst firstValue index
          | inr index => exact ihSecond secondValue index
      | inr index =>
          refine ⟨scalar, ?_⟩
          simp only [values, evaluate, firstValue, secondValue, bind, Option.bind_some, output]
  | cast type operand ih =>
      obtain ⟨input, inputValue, output⟩ := Option.bind_eq_some_iff.mp defined
      intro index
      cases index with
      | inl index => exact ih inputValue index
      | inr index =>
          refine ⟨scalar, ?_⟩
          simp only [values, evaluate, inputValue, bind, Option.bind_some, output]

theorem pure_history_complete (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (expression : Expression model)
    (pure : Pure expression) (scalar : IntegerScalar.Value model.parameters)
    (defined : evaluate policy memory expression = some scalar) :
    ∃ events final, SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) events final ∧
      final.pending = [] ∧ final.halted = none ∧
      final.memory = ObjectAccessMemory.represent memory ∧
      lookupScalar final.cache (result expression) = some scalar ∧
      Partition (compile expression) final.pending final.cache := by
  let before := represent (initialState (compile expression) memory)
  obtain ⟨events, final, history, drained, unhalted, unchanged, cache, partition⟩ :=
    readOnly_complete_history policy (compile expression) memory (values policy memory expression)
      pure.readOnly (pure.equations policy memory) (compiled_inputs_ordered expression)
      (pure.total policy memory defined) before.pending.length before le_rfl
      (initial_partition (compile expression) memory) rfl (by intro index outcome found; cases found) rfl
  have present : result expression ∈ final.cache.map Prod.fst := by
    rcases partition.2 (result expression) ((compile expression).component.enumeration.complete _) with
      pending | cached
    · rw [drained] at pending
      cases pending
    · exact cached
  have root := cache.cached present
  rw [values_result, defined] at root
  exact ⟨events, final, history, drained, unhalted, unchanged, root, partition⟩

theorem source_value_iff_history (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (target : Expression model)
    (resolved : ResolvesExpression policy memory arrays scopes source target)
    (scalar : IntegerScalar.Value model.parameters) :
    observe (FixedCore.evaluate model policy memory arrays scopes source) = some scalar ↔
    ∃ events final, SemanticHistory policy (compile target)
      (represent (initialState (compile target) memory)) events final ∧
      final.pending = [] ∧ final.halted = none ∧
      final.memory = ObjectAccessMemory.represent memory ∧
      lookupScalar final.cache (result target) = some scalar ∧
      Partition (compile target) final.pending final.cache := by
  constructor
  · intro defined
    exact pure_history_complete policy memory target resolved.pure scalar (resolved.evaluate.symm.trans defined)
  · rintro ⟨events, final, history, _, _, _, returned, _⟩
    exact (pure_history_no_invention policy memory arrays scopes source target resolved events final history
      scalar returned).1

theorem pure_schedules_agree (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (expression : Expression model)
    (pure : Pure expression)
    (firstEvents secondEvents : List (Occurrence (Index expression) model))
    (firstFinal secondFinal : SemanticState (Index expression) model)
    (firstHistory : SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) firstEvents firstFinal)
    (secondHistory : SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) secondEvents secondFinal)
    (first second : IntegerScalar.Value model.parameters)
    (firstReturned : lookupScalar firstFinal.cache (result expression) = some first)
    (secondReturned : lookupScalar secondFinal.cache (result expression) = some second) :
    first = second ∧ firstFinal.memory = secondFinal.memory := by
  obtain ⟨firstValue, firstMemory⟩ := firstHistory.readOnly_result pure.readOnly
    (pure.equations policy memory) (by simpa only [compiled_result] using firstReturned)
  obtain ⟨secondValue, secondMemory⟩ := secondHistory.readOnly_result pure.readOnly
    (pure.equations policy memory) (by simpa only [compiled_result] using secondReturned)
  exact ⟨Option.some.inj (firstValue.symm.trans secondValue), firstMemory.trans secondMemory.symm⟩

end PureExpressions

section ExpressionLowering
open IntegerMemoryModel ExpressionEvents ExpressionEventExecution ExpressionEventHistory LocatedExpressions
variable {model : Model}

/-- Resolve an admitted named integer read to its actual checked element range.
This does not assume the subsequent load succeeds. -/
def lowerRead (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (name : String) : Option (Expression model) := do
  let .object declared ← FixedCore.resolve scopes name | none
  let target ← FixedCore.rootAddress declared
  let range ← ArrayPointers.elementRange memory.storage arrays target.pointer
  pure (.load ⟨FixedCore.elementLvalue target range, target.type, rfl⟩)

/-- The common pure integer surface. Unsupported constructs are explicitly
outside this lowering, rather than silently reinterpreted. -/
def lower (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) : FixedCore.Expression model → Option (Expression model)
  | .constant scalar => some (.value scalar)
  | .read (.named name) => lowerRead memory arrays scopes name
  | .binary operator first second => do
      let left ← lower memory arrays scopes first
      let right ← lower memory arrays scopes second
      pure (.arithmetic operator left right)
  | .cast type operand => (.cast type) <$> lower memory arrays scopes operand
  | _ => none

theorem lowerRead_sound (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (name : String) (target : Expression model)
    (lowered : lowerRead memory arrays scopes name = some target) :
    ResolvesExpression policy memory arrays scopes (.read (.named name)) target := by
  unfold lowerRead at lowered
  obtain ⟨entity, found, after⟩ := Option.bind_eq_some_iff.mp lowered
  cases entity with
  | pointer value => cases after
  | object declared =>
      obtain ⟨address, addressed, after⟩ := Option.bind_eq_some_iff.mp after
      obtain ⟨range, ranged, after⟩ := Option.bind_eq_some_iff.mp after
      have same : Expression.load ⟨FixedCore.elementLvalue address range, address.type, rfl⟩ = target :=
        Option.some.inj after
      rw [← same]
      exact .read name declared address range
        (FixedCore.resolve_sound _ _ _ found) addressed ((ArrayPointers.elementRange_iff _ _ _ _).mp ranged)

theorem lower_sound (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (target : Expression model)
    (lowered : lower memory arrays scopes source = some target) :
    ResolvesExpression policy memory arrays scopes source target := by
  cases source with
  | constant scalar => cases lowered; exact .constant scalar
  | read place =>
      cases place with
      | named name => exact lowerRead_sound policy memory arrays scopes name target lowered
      | element name index => cases lowered
      | deref pointer => cases lowered
  | binary operator first second =>
      obtain ⟨left, leftLowered, after⟩ := Option.bind_eq_some_iff.mp lowered
      obtain ⟨right, rightLowered, after⟩ := Option.bind_eq_some_iff.mp after
      have same : Expression.arithmetic operator left right = target := Option.some.inj after
      rw [← same]
      exact .binary operator (lower_sound policy memory arrays scopes first left leftLowered)
        (lower_sound policy memory arrays scopes second right rightLowered)
  | cast type operand =>
      obtain ⟨inner, innerLowered, same⟩ := Option.map_eq_some_iff.mp lowered
      rw [← same]
      exact .cast type (lower_sound policy memory arrays scopes operand inner innerLowered)
  | compare _ _ _ | addressOf _ | offset _ _ | «variable» _ | null => cases lowered
termination_by source

theorem lower_complete {policy : SignedConversionPolicy}
    {memory : ObjectAccessMemory.State model.characters} {arrays : ArrayPointers.Catalog}
    {scopes : List (FixedCore.Scope model)} {source : FixedCore.Expression model} {target : Expression model}
    (resolved : ResolvesExpression policy memory arrays scopes source target) :
    lower memory arrays scopes source = some target := by
  induction resolved with
  | constant scalar => rfl
  | read name declared target range resolved typed located =>
      simp only [lower, lowerRead, FixedCore.resolve_complete _ _ _ resolved, typed,
        (ArrayPointers.elementRange_iff _ _ _ _).mpr located, bind, Option.bind_some, pure, Pure.pure]
  | binary operator first second ihFirst ihSecond =>
      simp only [lower, ihFirst, ihSecond, bind, Option.bind_some, pure, Pure.pure]
  | cast type resolved ih => simp only [lower, ih, Functor.map, Option.map_some]

theorem lower_iff (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (target : Expression model) :
    lower memory arrays scopes source = some target ↔
      ResolvesExpression policy memory arrays scopes source target :=
  ⟨lower_sound policy memory arrays scopes source target, lower_complete⟩

end ExpressionLowering

section ExpressionBoundaries
open IntegerMemoryModel ExpressionEvents ExpressionEventExecution ExpressionEventHistory LocatedExpressions
open LocatedExpressionData (IndexData encodeIndex decodeIndex)
variable {model : Model}

/-- Embed exactly the independent expression occurrences in the actual
statement control machine, retaining its continuation and schedule suffix. -/
theorem expression_history_in_statement (policy : SignedConversionPolicy) (expression : Expression model)
    (before after : SemanticState (Index expression) model) (events : List (Occurrence (Index expression) model))
    (history : SemanticHistory policy (compile expression) before events after)
    (continuation : LocatedStatements.AfterExpression model) (rest : List IndexData) :
    StatementHistory.History policy
      (.expression expression before continuation (events.map (fun event => encodeIndex expression event.index) ++ rest))
      (events.map (fun event => some (.occurrence expression (encodeIndex expression event.index) event.outcome)))
      (.expression expression after continuation rest) := by
  induction history with
  | nil before => exact .nil _
  | cons before middle after event events stepped following ih =>
      apply StatementHistory.History.cons _ _ _ _ _ ?_ ih
      exact .occurrence _ _ _ _ _ _ event.index event.outcome
        (LocatedExpressionData.decodeIndex_encode expression event.index)
        ((ExpressionSourceExecution.reduction_iff _ _ _ _ _ _).mp stepped)

theorem pure_complete_expression (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (expression : Expression model)
    (pure : Pure expression) (scalar : IntegerScalar.Value model.parameters)
    (defined : evaluate policy memory expression = some scalar) :
    ∃ events final, SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) events final ∧
      LocatedStatements.CompleteExpression expression final scalar ∧
      final.memory = ObjectAccessMemory.represent memory := by
  obtain ⟨events, final, history, pending, unhalted, unchanged, value, partition⟩ :=
    pure_history_complete policy memory expression pure scalar defined
  exact ⟨events, final, history, ⟨partition, pending, unhalted,
    fun undefined => readOnly_clean (compile expression) pure.readOnly ((ExpressionSourceExecution.compiled_conflict_iff _).mpr undefined), value⟩,
    unchanged⟩

/-- A fixed-core scalar evaluation constructs a complete located expression
block and reaches the same chosen statement continuation. -/
theorem source_expression_boundary (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (target : Expression model)
    (resolved : ResolvesExpression policy memory arrays scopes source target)
    (scalar : IntegerScalar.Value model.parameters)
    (defined : observe (FixedCore.evaluate model policy memory arrays scopes source) = some scalar)
    (continuation : LocatedStatements.AfterExpression model) (rest : List IndexData)
    (next : LocatedStatements.SemanticConfiguration model)
    (boundary : StatementSemantics.BoundaryTarget continuation scalar (ObjectAccessMemory.represent memory) rest next) :
    ∃ choices events, StatementHistory.History policy
      (.expression target (LocatedStatements.sourceInitial target (ObjectAccessMemory.represent memory))
        continuation (choices ++ rest)) events next := by
  obtain ⟨events, final, history, completed, unchanged⟩ :=
    pure_complete_expression policy memory target resolved.pure scalar (resolved.evaluate.symm.trans defined)
  refine ⟨events.map (fun event => encodeIndex target event.index),
    events.map (fun event => some (.occurrence target (encodeIndex target event.index) event.outcome)) ++
      [some (.boundary continuation.boundary target scalar)], ?_⟩
  apply StatementHistory.history_append _ _ _ _ _ _ (expression_history_in_statement _ _ _ _ _ history continuation rest)
  exact .cons _ _ _ _ _ (.boundary _ _ _ _ _ completed _ (by rw [unchanged]; exact boundary)) (.nil _)

/-- The boundary block runs on the existing executable statement machine;
its saved endpoint retains the complete memory meaning and schedule suffix. -/
theorem source_expression_boundary_runs (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (target : Expression model)
    (resolved : ResolvesExpression policy memory arrays scopes source target)
    (scalar : IntegerScalar.Value model.parameters)
    (defined : observe (FixedCore.evaluate model policy memory arrays scopes source) = some scalar)
    (continuation : LocatedStatements.AfterExpression model) (rest : List IndexData)
    (next : LocatedStatements.SemanticConfiguration model)
    (boundary : StatementSemantics.BoundaryTarget continuation scalar (ObjectAccessMemory.represent memory) rest next) :
    ∃ choices, ∃ events : List (Option (LocatedStatements.Event model)), ∃ saved receipts,
      LocatedStatements.represent saved = next ∧
      (StatementMachine.machine model policy).run events.length
        (.expression target (initialState (compile target) memory) continuation (choices ++ rest)) =
          (receipts, .exhausted saved) ∧
      receipts.map StatementMachine.Receipt.event = events.filterMap id := by
  obtain ⟨choices, events, history⟩ := source_expression_boundary policy memory arrays scopes source target
    resolved scalar defined continuation rest next boundary
  obtain ⟨saved, receipts, represented, ran, observations⟩ :=
    StatementHistory.history_realization _ _ _ events history
      (.expression target (initialState (compile target) memory) continuation (choices ++ rest)) rfl
  exact ⟨choices, events, saved, receipts, represented, ran, observations⟩

/-- A reached located boundary cannot invent a defined source value, even
when the scheduler chose a different licensed operand order. -/
theorem source_boundary_no_invention (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (target : Expression model)
    (resolved : ResolvesExpression policy memory arrays scopes source target)
    (events : List (Occurrence (Index target) model)) (final : SemanticState (Index target) model)
    (history : SemanticHistory policy (compile target)
      (represent (initialState (compile target) memory)) events final)
    (scalar : IntegerScalar.Value model.parameters)
    (completed : LocatedStatements.CompleteExpression target final scalar) :
    observe (FixedCore.evaluate model policy memory arrays scopes source) = some scalar ∧
      final.memory = ObjectAccessMemory.represent memory :=
  pure_history_no_invention policy memory arrays scopes source target resolved events final history scalar completed.result

end ExpressionBoundaries

section SharedControl
open IntegerMemoryModel LocatedExpressions
open LocatedExpressionData (IndexData)
variable {model : Model}

open ExpressionEvents ExpressionEventExecution ExpressionEventHistory Sequencing ValueSequencing ExpressionPlanConstruction
theorem Pure.root_dominates {expression : Expression model} (pure : Pure expression) :
    ∀ index : Index expression, index = result expression ∨ (compile expression).component.evaluation.order.Precedes index (result expression) := by
  induction pure with
  | value scalar => intro index; exact Or.inl (Fin.eq_zero index)
  | load location => intro index; exact Or.inl (Fin.eq_zero index)
  | @arithmetic operator first second firstPure secondPure firstIH secondIH =>
    intro index
    cases index with
    | inl index =>
      apply Or.inr
      cases index with
      | inl index =>
        apply (afterRoots_follows _ _ _ _ _).mpr
        refine ⟨.inl (result first), by simp [compiled_result], ?_⟩
        rcases firstIH index with same | prior
        · exact Or.inl (congrArg Sum.inl same)
        · exact Or.inr prior
      | inr index =>
        apply (afterRoots_follows _ _ _ _ _).mpr
        refine ⟨.inr (result second), by simp [compiled_result], ?_⟩
        rcases secondIH index with same | prior
        · exact Or.inl (congrArg Sum.inr same)
        · exact Or.inr prior
    | inr index => exact Or.inl (congrArg Sum.inr (Fin.eq_zero index))
  | @cast type operand pure ih =>
    intro index
    cases index with
    | inl index =>
      exact Or.inr ((afterRoots_follows _ _ _ _ _).mpr ⟨result operand, by simp [compiled_result], ih index⟩)
    | inr index => exact Or.inl (congrArg Sum.inr (Fin.eq_zero index))


theorem assignment_history (policy : SignedConversionPolicy)
    (before after : ObjectAccessMemory.State model.characters)
    (destination : Destination) (operand : Expression model) (pure : Pure operand)
    (input converted : IntegerScalar.Value model.parameters)
    (evaluated : evaluate policy before operand = some input)
    (assigned : IntegerAssignment.Assigning model policy (ObjectAccessMemory.represent before)
      destination.location input (.stored converted) (ObjectAccessMemory.represent after)) :
    ∃ events final,
      SemanticHistory policy (compile (.assignment destination operand))
        (represent (initialState (compile (.assignment destination operand)) before)) events final ∧
      LocatedStatements.CompleteExpression (.assignment destination operand) final converted ∧
      final.memory = ObjectAccessMemory.represent after := by
  let : DecidableEq (Index (.cast destination.type operand)) := LocatedExpressions.instDecidableEqIndex _
  have castPure : Pure (.cast destination.type operand) := .cast _ pure
  have conversion : IntegerScalar.CastEvaluation model.parameters policy destination.type input (.value converted) := by
    cases assigned with
    | stored after location input converted type formed cast writing =>
      have same : type = destination.type := by
        rw [destination.formed] at formed
        injection formed with same
        injection same with equal
        exact equal.symm
      subst type
      exact cast
  have written : Writing model (ObjectAccessMemory.represent before) (ObjectAccessMemory.represent after)
      destination.location converted := by cases assigned; assumption
  have castValue : evaluate policy before (.cast destination.type operand) = some converted := by
    simp only [evaluate, evaluated, bind, Option.bind_some, IntegerScalar.cast_complete _ _ _ _ _ conversion,
      castOutcome, Outcome.scalar]
  obtain ⟨events, final, history, drained, active, unchanged, value, partition⟩ :=
    pure_history_complete policy before (.cast destination.type operand) castPure converted castValue
  have clean := storeResult_clean (compile (.cast destination.type operand)) destination.location castPure.readOnly
    (by simpa only [compiled_result] using castPure.root_dominates)
  obtain ⟨allEvents, saved, combined, finished, notHalted, updated, root, partition⟩ :=
    storeResult_complete policy (compile (.cast destination.type operand)) destination.location before after converted
      clean (compiled_occurrences_unique _) events final history drained active unchanged partition
      (by simpa only [compiled_result] using value) written
  refine ⟨allEvents, saved, combined, ?_, updated⟩
  exact ⟨partition, finished, notHalted,
    fun undefined => clean ((ExpressionSourceExecution.compiled_conflict_iff _).mpr undefined), root⟩


/-- Equality of allocation headers, independent of bytes and object-cache contents. -/
def SameAllocationHeaders (before after : ObjectAccessMemory.State model.characters) : Prop :=
  ∀ allocation, (ByteRanges.heap before.storage allocation).1 = (ByteRanges.heap after.storage allocation).1

theorem writing_preserves_allocation_headers
    (before after : ObjectAccessMemory.State model.characters) (location : ObjectAccessMemory.Lvalue)
    (scalar : IntegerScalar.Value model.parameters)
    (written : Writing model (ObjectAccessMemory.represent before) (ObjectAccessMemory.represent after) location scalar) :
    SameAllocationHeaders before after := by
  obtain ⟨_, _, _, _, _, _, _, bytes, _⟩ := written.2
  obtain ⟨_, _, _, _, endpoint⟩ := bytes
  intro allocation
  change (ByteRanges.heap after.storage) = _ at endpoint
  rw [endpoint]
  exact (ByteRanges.updateRange_header _ _ _ allocation).symm

theorem ResolvesExpression.transport {policy : SignedConversionPolicy}
    {before after : ObjectAccessMemory.State model.characters} {arrays : ArrayPointers.Catalog}
    {scopes : List (FixedCore.Scope model)} {source : FixedCore.Expression model} {target : Expression model}
    (resolved : ResolvesExpression policy before arrays scopes source target)
    (headers : SameAllocationHeaders before after) : ResolvesExpression policy after arrays scopes source target := by
  induction resolved with
  | constant scalar => exact .constant _
  | read name declared target range resolved typed located =>
    apply ResolvesExpression.read name declared target range resolved typed
    rcases located with ⟨descriptor, live, bound, same⟩
    exact ⟨descriptor, (ArrayPointers.liveArray_headers _ _ _ _ _ headers).mp live, bound, same⟩
  | binary operator first second firstIH secondIH => exact .binary _ firstIH secondIH
  | cast type inner ih => exact .cast _ ih


/-- The common pure-operand control fragment. Its loop bodies and
continuations are arbitrary recursively admitted statements, rather than a
list of selected example programs. -/
inductive ResolvesStatement (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) : FixedCore.Statement model → LocatedStatements.Statement model → Prop where
  | assignment (name : String) {source : FixedCore.Expression model} {operand : Expression model}
      {destination : Destination}
      (location : ResolvesExpression policy memory arrays scopes (.read (.named name)) (.load destination))
      (value : ResolvesExpression policy memory arrays scopes source operand) :
      ResolvesStatement policy memory arrays scopes (.assign (.named name) source)
        (.expression (.assignment destination operand))
  | skip : ResolvesStatement policy memory arrays scopes .skip .empty
  | sequence {a b : FixedCore.Statement model} {x y : LocatedStatements.Statement model}
      (first : ResolvesStatement policy memory arrays scopes a x)
      (second : ResolvesStatement policy memory arrays scopes b y) :
      ResolvesStatement policy memory arrays scopes (.sequence a b) (.sequence x y)
  | conditional {condition : FixedCore.Expression model} {test : Expression model}
      {yes no : FixedCore.Statement model} {left right : LocatedStatements.Statement model}
      (expression : ResolvesExpression policy memory arrays scopes condition test)
      (onTrue : ResolvesStatement policy memory arrays scopes yes left)
      (onFalse : ResolvesStatement policy memory arrays scopes no right) :
      ResolvesStatement policy memory arrays scopes (.conditional condition yes no) (.conditional test left right)
  | whileLoop {condition : FixedCore.Expression model} {test : Expression model}
      {body : FixedCore.Statement model} {next : LocatedStatements.Statement model}
      (expression : ResolvesExpression policy memory arrays scopes condition test)
      (bodyResolved : ResolvesStatement policy memory arrays scopes body next) :
      ResolvesStatement policy memory arrays scopes (.whileLoop condition body) (.whileLoop test next)
  | breakLoop : ResolvesStatement policy memory arrays scopes .breakLoop .breakLoop
  | continueLoop : ResolvesStatement policy memory arrays scopes .continueLoop .continueLoop
  | returnEmpty : ResolvesStatement policy memory arrays scopes (.returnValue none) (.returnValue none)
  | returnValue {expression : FixedCore.Expression model} {value : Expression model}
      (resolved : ResolvesExpression policy memory arrays scopes expression value) :
      ResolvesStatement policy memory arrays scopes (.returnValue (some expression)) (.returnValue (some value))

theorem ResolvesStatement.transport {policy : SignedConversionPolicy}
    {before after : ObjectAccessMemory.State model.characters} {arrays : ArrayPointers.Catalog}
    {scopes : List (FixedCore.Scope model)} {source : FixedCore.Statement model} {target : LocatedStatements.Statement model}
    (resolved : ResolvesStatement policy before arrays scopes source target)
    (headers : SameAllocationHeaders before after) : ResolvesStatement policy after arrays scopes source target := by
  induction resolved with
  | assignment name location value => exact .assignment name (location.transport headers) (value.transport headers)
  | skip => exact .skip
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond
  | conditional expression yes no ihYes ihNo => exact .conditional (expression.transport headers) ihYes ihNo
  | whileLoop expression body ih => exact .whileLoop (expression.transport headers) ih
  | breakLoop => exact .breakLoop
  | continueLoop => exact .continueLoop
  | returnEmpty => exact .returnEmpty
  | returnValue expression => exact .returnValue (expression.transport headers)

inductive ResolvesContinuation (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) : FixedCore.Continuation model → LocatedStatements.Continuation model → Prop where
  | stop : ResolvesContinuation policy memory arrays scopes .stop .stop
  | sequence {source : FixedCore.Statement model} {target : LocatedStatements.Statement model}
      {before : FixedCore.Continuation model} {after : LocatedStatements.Continuation model}
      (statement : ResolvesStatement policy memory arrays scopes source target)
      (continuation : ResolvesContinuation policy memory arrays scopes before after) :
      ResolvesContinuation policy memory arrays scopes (.sequence source before) (.sequence target after)
  | loop {condition : FixedCore.Expression model} {test : Expression model}
      {body : FixedCore.Statement model} {next : LocatedStatements.Statement model}
      {before : FixedCore.Continuation model} {after : LocatedStatements.Continuation model}
      (expression : ResolvesExpression policy memory arrays scopes condition test)
      (statement : ResolvesStatement policy memory arrays scopes body next)
      (continuation : ResolvesContinuation policy memory arrays scopes before after) :
      ResolvesContinuation policy memory arrays scopes (.loop condition body before) (.whileBody test next after)

theorem ResolvesContinuation.transport {policy : SignedConversionPolicy}
    {before after : ObjectAccessMemory.State model.characters} {arrays : ArrayPointers.Catalog}
    {scopes : List (FixedCore.Scope model)} {source : FixedCore.Continuation model} {target : LocatedStatements.Continuation model}
    (resolved : ResolvesContinuation policy before arrays scopes source target)
    (headers : SameAllocationHeaders before after) : ResolvesContinuation policy after arrays scopes source target := by
  induction resolved with
  | stop => exact .stop
  | sequence statement continuation ih => exact .sequence (statement.transport headers) ih
  | loop expression statement continuation ih => exact .loop (expression.transport headers) (statement.transport headers) ih

def lowerFlow : FixedCore.Flow → LocatedStatements.Flow
  | .normal => .normal
  | .broken => .broken
  | .continued => .continued

def scalarReturn (value : Option (IntegerScalar.Value model.parameters)) : Option (FixedCore.Value model) :=
  value.map FixedCore.Value.integer

/-- Matching control boundaries. The loop-expression case absorbs the fixed
machine's separate loop restart transition. Return propagation can erase only
continuations without pending scope destruction. -/
inductive ControlRelated (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) : FixedCore.Control model → FixedCore.Continuation model →
      (List IndexData → LocatedStatements.SemanticConfiguration model) → Prop where
  | statement {source : FixedCore.Statement model} {target : LocatedStatements.Statement model}
      {before : FixedCore.Continuation model} {after : LocatedStatements.Continuation model}
      (statement : ResolvesStatement policy memory arrays scopes source target)
      (continuation : ResolvesContinuation policy memory arrays scopes before after) :
      ControlRelated policy memory arrays scopes (.execute source) before
        (fun selections => .statement target after (ObjectAccessMemory.represent memory) selections)
  | flow (flow : FixedCore.Flow)
      {before : FixedCore.Continuation model} {after : LocatedStatements.Continuation model}
      (continuation : ResolvesContinuation policy memory arrays scopes before after) :
      ControlRelated policy memory arrays scopes (.flow flow) before
        (fun selections => .flow (lowerFlow flow) after (ObjectAccessMemory.represent memory) selections)
  | loopExpression {condition : FixedCore.Expression model} {test : Expression model}
      {body : FixedCore.Statement model} {next : LocatedStatements.Statement model}
      {before : FixedCore.Continuation model} {after : LocatedStatements.Continuation model}
      (expression : ResolvesExpression policy memory arrays scopes condition test)
      (statement : ResolvesStatement policy memory arrays scopes body next)
      (continuation : ResolvesContinuation policy memory arrays scopes before after) :
      ControlRelated policy memory arrays scopes (.execute (.whileLoop condition body)) before
        (fun selections => .expression test (LocatedStatements.sourceInitial test (ObjectAccessMemory.represent memory))
          (.whileCondition test next after) selections)
  | returning (value : Option (IntegerScalar.Value model.parameters))
      {before : FixedCore.Continuation model} {after : LocatedStatements.Continuation model}
      (continuation : ResolvesContinuation policy memory arrays scopes before after) :
      ControlRelated policy memory arrays scopes (.returning (scalarReturn value)) before
        (fun selections => .returned value (ObjectAccessMemory.represent memory) selections)
  | fallthrough : ControlRelated policy memory arrays scopes (.returning none) .stop
      (fun selections => .flow .normal .stop (ObjectAccessMemory.represent memory) selections)

/-- Configuration constructor, with the original scope, array catalogue and
heap ownership kept intact. -/
def fixedConfiguration (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (control : FixedCore.Control model) (continuation : FixedCore.Continuation model) : FixedCore.Executable model :=
  ⟨memory, arrays, heap, [⟨scopes, control, continuation⟩], .running⟩

def Block (policy : SignedConversionPolicy)
    (before after : List IndexData → LocatedStatements.SemanticConfiguration model) : Prop :=
  ∀ rest, ∃ choices events, StatementHistory.History policy (before (choices ++ rest)) events (after rest)

theorem Block.refl (policy : SignedConversionPolicy)
    (state : List IndexData → LocatedStatements.SemanticConfiguration model) : Block policy state state := by
  intro rest
  exact ⟨[], [], .nil _⟩

theorem Block.trans {policy : SignedConversionPolicy}
    {first middle last : List IndexData → LocatedStatements.SemanticConfiguration model}
    (firstBlock : Block policy first middle) (suffix : Block policy middle last) : Block policy first last := by
  intro rest
  obtain ⟨lastChoices, lastEvents, lastHistory⟩ := suffix rest
  obtain ⟨firstChoices, firstEvents, firstHistory⟩ := firstBlock (lastChoices ++ rest)
  refine ⟨firstChoices ++ lastChoices, firstEvents ++ lastEvents, ?_⟩
  rw [List.append_assoc]
  exact StatementHistory.history_append _ _ _ _ _ _ firstHistory lastHistory

theorem block_administrative (policy : SignedConversionPolicy)
    (before after : List IndexData → LocatedStatements.SemanticConfiguration model)
    (step : ∀ selections, StatementSemantics.Administrative (before selections) (after selections)) :
    Block policy before after := by
  intro rest
  exact ⟨[], [none], .cons _ _ _ _ _ (.administrative _ _ (step rest)) (.nil _)⟩

theorem block_iteration (policy : SignedConversionPolicy)
    (before after : List IndexData → LocatedStatements.SemanticConfiguration model) (kind : LocatedStatements.Loop)
    (step : ∀ selections, StatementSemantics.Iteration (before selections) kind (after selections)) :
    Block policy before after := by
  intro rest
  exact ⟨[], [some (.iteration kind)], .cons _ _ _ _ _ (.iteration _ _ _ (step rest)) (.nil _)⟩

theorem scalar_truth_agrees (value : IntegerScalar.Value model.parameters) :
    IntegerScalar.truth value = LocatedStatements.truth value := by
  by_cases zero : value.integer.value = 0 <;> simp [IntegerScalar.truth, LocatedStatements.truth, zero]

theorem observe_some_iff (result : FixedCore.Result model) (scalar : IntegerScalar.Value model.parameters) :
    observe result = some scalar ↔ result = .value (.integer scalar) := by
  cases result with
  | fault reason => simp only [observe, reduceCtorEq]
  | value value => cases value <;> simp only [observe, Option.some.injEq, FixedCore.Result.value.injEq,
      FixedCore.Value.integer.injEq, reduceCtorEq]

theorem block_while (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (test : Expression model)
    (resolved : ResolvesExpression policy memory arrays scopes source test)
    (body : LocatedStatements.Statement model) (following : LocatedStatements.Continuation model)
    (scalar : IntegerScalar.Value model.parameters)
    (defined : FixedCore.evaluate model policy memory arrays scopes source = .value (.integer scalar)) :
    Block policy
      (fun selections => .expression test (LocatedStatements.sourceInitial test (ObjectAccessMemory.represent memory))
        (.whileCondition test body following) selections)
      (fun selections => if IntegerScalar.truth scalar then
        .statement body (.whileBody test body following) (ObjectAccessMemory.represent memory) selections
        else .flow .normal following (ObjectAccessMemory.represent memory) selections) := by
  intro rest
  apply source_expression_boundary policy memory arrays scopes source test resolved scalar
    ((observe_some_iff _ _).mpr defined)
  rw [scalar_truth_agrees]
  exact .whileCondition _ _ _ _ rfl ((LocatedStatements.truth_iff _ _).mp rfl)

end SharedControl

section StatementBlocks
open IntegerMemoryModel LocatedExpressions
open LocatedExpressionData (IndexData)
variable {model : Model}

def IntegerResult : FixedCore.Result model → Prop
  | .value (.integer _) | .fault _ => True
  | _ => False

theorem ResolvesExpression.integer_result {policy : SignedConversionPolicy}
    {memory : ObjectAccessMemory.State model.characters} {arrays : ArrayPointers.Catalog}
    {scopes : List (FixedCore.Scope model)} {source : FixedCore.Expression model} {target : Expression model}
    (resolved : ResolvesExpression policy memory arrays scopes source target) :
    IntegerResult (FixedCore.evaluate model policy memory arrays scopes source) := by
  cases resolved with
  | constant scalar => trivial
  | read name declared target range resolved typed located =>
      simp only [FixedCore.evaluate, FixedCore.locate, FixedCore.objectAddress,
        FixedCore.resolve_complete _ _ _ resolved, typed, FixedCore.readElement,
        (ArrayPointers.elementRange_iff _ _ _ _).mpr located]
      cases load model memory (FixedCore.elementLvalue target range) with
      | none => trivial
      | some result => cases result <;> trivial
  | @binary operator first second left right firstResolved secondResolved =>
      change IntegerResult (match FixedCore.integerOperands
        (FixedCore.evaluate model policy memory arrays scopes first)
        (FixedCore.evaluate model policy memory arrays scopes second) with
        | .error reason => .fault reason
        | .ok (left, right) => FixedCore.arithmeticResult (IntegerScalar.binary model.parameters operator left right))
      cases FixedCore.integerOperands
        (FixedCore.evaluate model policy memory arrays scopes first)
        (FixedCore.evaluate model policy memory arrays scopes second) with
      | error reason => trivial
      | ok pair =>
          rcases pair with ⟨left, right⟩
          change IntegerResult (FixedCore.arithmeticResult (IntegerScalar.binary model.parameters operator left right))
          cases IntegerScalar.binary model.parameters operator left right <;> trivial
  | @cast type source target resolved =>
      change IntegerResult (match FixedCore.integerOperand (FixedCore.evaluate model policy memory arrays scopes source) with
        | .error reason => .fault reason
        | .ok input => FixedCore.castResult (IntegerScalar.cast model.parameters policy type input))
      cases FixedCore.integerOperand (FixedCore.evaluate model policy memory arrays scopes source) with
      | error reason => trivial
      | ok input =>
          change IntegerResult (FixedCore.castResult (IntegerScalar.cast model.parameters policy type input))
          cases IntegerScalar.cast model.parameters policy type input <;> trivial

theorem block_conditional (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (test : Expression model)
    (resolved : ResolvesExpression policy memory arrays scopes source test)
    (yes no : LocatedStatements.Statement model) (following : LocatedStatements.Continuation model)
    (scalar : IntegerScalar.Value model.parameters)
    (defined : FixedCore.evaluate model policy memory arrays scopes source = .value (.integer scalar)) :
    Block policy
      (fun selections => .statement (.conditional test yes no) following (ObjectAccessMemory.represent memory) selections)
      (fun selections => .statement (if IntegerScalar.truth scalar then yes else no)
        following (ObjectAccessMemory.represent memory) selections) := by
  apply Block.trans (block_administrative policy _ _ (fun _ => .conditional _ _ _ _ _ _))
  intro rest
  apply source_expression_boundary policy memory arrays scopes source test resolved scalar
    ((observe_some_iff _ _).mpr defined)
  rw [scalar_truth_agrees]
  exact .conditional _ _ _ _ rfl ((LocatedStatements.truth_iff _ _).mp rfl)

theorem block_return (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (target : Expression model)
    (resolved : ResolvesExpression policy memory arrays scopes source target)
    (following : LocatedStatements.Continuation model)
    (scalar : IntegerScalar.Value model.parameters)
    (defined : FixedCore.evaluate model policy memory arrays scopes source = .value (.integer scalar)) :
    Block policy
      (fun selections => .statement (.returnValue (some target)) following (ObjectAccessMemory.represent memory) selections)
      (fun selections => .returned (some scalar) (ObjectAccessMemory.represent memory) selections) := by
  apply Block.trans (block_administrative policy _ _ (fun _ => .returnValue _ _ _ _))
  intro rest
  apply source_expression_boundary policy memory arrays scopes source target resolved scalar
    ((observe_some_iff _ _).mpr defined)
  exact .returnValue rfl

open ExpressionEvents ExpressionEventExecution ExpressionEventHistory
open LocatedExpressionData (encodeIndex)

theorem assignment_block (policy : SignedConversionPolicy)
    (before after : ObjectAccessMemory.State model.characters)
    (destination : Destination) (operand : Expression model) (pure : Pure operand)
    (input converted : IntegerScalar.Value model.parameters)
    (evaluated : evaluate policy before operand = some input)
    (assigned : IntegerAssignment.Assigning model policy (ObjectAccessMemory.represent before)
      destination.location input (.stored converted) (ObjectAccessMemory.represent after))
    (continuation : LocatedStatements.Continuation model) :
    Block policy
      (fun choices => .statement (.expression (.assignment destination operand)) continuation
        (ObjectAccessMemory.represent before) choices)
      (fun choices => .flow .normal continuation (ObjectAccessMemory.represent after) choices) := by
  apply (block_administrative policy _ _ (fun _ => StatementSemantics.Administrative.expression _ _ _ _)).trans
  intro rest
  obtain ⟨events, final, history, complete, updated⟩ :=
    assignment_history policy before after destination operand pure input converted evaluated assigned
  let choices := events.map (fun event => encodeIndex (.assignment destination operand) event.index)
  refine ⟨choices, events.map (fun event => some (LocatedStatements.Event.occurrence
    (.assignment destination operand) (encodeIndex (.assignment destination operand) event.index) event.outcome)) ++ [some (.boundary (LocatedStatements.AfterExpression.discard continuation).boundary (.assignment destination operand) converted)], ?_⟩
  have embedded := expression_history_in_statement policy (.assignment destination operand)
    (LocatedStatements.sourceInitial (.assignment destination operand) (ObjectAccessMemory.represent before))
    final events history (.discard continuation) rest
  have target : StatementSemantics.BoundaryTarget (.discard continuation) converted final.memory rest
      (.flow .normal continuation (ObjectAccessMemory.represent after) rest) := by
    rw [updated]
    exact .discard _ rfl
  exact StatementHistory.history_append policy _ _ _ _ _ embedded
    (.cons _ _ _ _ [] (StatementSemantics.Step.boundary _ _ _ _ _ complete _ target) (.nil _))


theorem statement_step_simulation (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {source : FixedCore.Statement model} {target : LocatedStatements.Statement model}
    {before : FixedCore.Continuation model} {after : LocatedStatements.Continuation model}
    (resolved : ResolvesStatement policy memory arrays scopes source target)
    (continuation : ResolvesContinuation policy memory arrays scopes before after)
    (next : FixedCore.Executable model)
    (stepped : FixedCore.step model policy abi program choice
      (fixedConfiguration memory arrays scopes heap (.execute source) before) = some next)
    (running : next.status = .running) :
    ∃ nextMemory control following target', next = fixedConfiguration nextMemory arrays scopes heap control following ∧
      ControlRelated policy nextMemory arrays scopes control following target' ∧
      Block policy (fun selections => .statement target after (ObjectAccessMemory.represent memory) selections) target' := by
  cases resolved with
  | @assignment name source operand destination location value =>
      cases location with
      | read _ declared address range resolved typed inside =>
          have located : FixedCore.locate model policy memory arrays scopes (.named name) =
              .ok address := by
            simp only [FixedCore.locate, FixedCore.resolve_complete _ _ _ resolved, FixedCore.objectAddress, typed]
          simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, located,
            FixedCore.Configuration.fail] at stepped
          cases evaluated : FixedCore.evaluate model policy memory arrays scopes source with
          | fault reason => simp only [evaluated] at stepped; cases stepped; cases running
          | value scalar =>
              cases scalar with
              | address address => simp only [evaluated] at stepped; cases stepped; cases running
              | null => simp only [evaluated] at stepped; cases stepped; cases running
              | integer scalar =>
                  simp only [evaluated] at stepped
                  cases stored : FixedCore.storeElement model policy memory arrays address scalar with
                  | fault reason => simp only [stored] at stepped; cases stepped; cases running
                  | done updated =>
                      simp only [stored] at stepped
                      cases stepped
                      have assigned := FixedCore.storeElement_sound model policy memory arrays address scalar
                      rw [stored] at assigned
                      cases assigned with
                      | stored other converted final otherInside assigned =>
                          have same : other = range := Option.some.inj
                            (((ArrayPointers.elementRange_iff _ _ _ _).mpr otherInside).symm.trans
                              ((ArrayPointers.elementRange_iff _ _ _ _).mpr inside))
                          subst other
                          have written : Writing model (ObjectAccessMemory.represent memory) (ObjectAccessMemory.represent updated)
                              (FixedCore.elementLvalue address range) converted := by cases assigned; assumption
                          have retained := continuation.transport (writing_preserves_allocation_headers memory updated _ converted written)
                          exact ⟨updated, .flow .normal, _, _, rfl, .flow .normal retained,
                            assignment_block policy memory updated _ operand value.pure scalar converted
                              (value.evaluate.symm.trans (by rw [evaluated]; rfl)) assigned after⟩
  | skip =>
      refine ⟨memory, ?_⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith] at stepped
      cases stepped
      exact ⟨.flow .normal, _, _, rfl, .flow .normal continuation,
        block_administrative policy _ _ (fun _ => .empty _ _ _)⟩
  | sequence first second =>
      refine ⟨memory, ?_⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith] at stepped
      cases stepped
      exact ⟨_, _, _, rfl, .statement first (.sequence second continuation),
        block_administrative policy _ _ (fun _ => .sequence _ _ _ _ _)⟩
  | @conditional condition test yes no left right expression onTrue onFalse =>
      refine ⟨memory, ?_⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith,
        FixedCore.Configuration.fail] at stepped
      cases evaluated : FixedCore.evaluate model policy memory arrays scopes condition with
      | fault reason => simp only [evaluated] at stepped; cases stepped; cases running
      | value value =>
          cases value with
          | address address => simp only [evaluated] at stepped; cases stepped; cases running
          | null => simp only [evaluated] at stepped; cases stepped; cases running
          | integer scalar =>
              simp only [evaluated] at stepped
              cases stepped
              refine ⟨_, _, _, rfl, ?_, block_conditional policy memory arrays scopes condition test expression
                left right after scalar evaluated⟩
              cases IntegerScalar.truth scalar with
              | false => exact .statement onFalse continuation
              | true => exact .statement onTrue continuation
  | @whileLoop condition test body nextBody expression bodyResolved =>
      refine ⟨memory, ?_⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith,
        FixedCore.Configuration.fail] at stepped
      cases evaluated : FixedCore.evaluate model policy memory arrays scopes condition with
      | fault reason => simp only [evaluated] at stepped; cases stepped; cases running
      | value value =>
          cases value with
          | address address => simp only [evaluated] at stepped; cases stepped; cases running
          | null => simp only [evaluated] at stepped; cases stepped; cases running
          | integer scalar =>
              have block := (block_administrative policy _ _ (fun _ =>
                StatementSemantics.Administrative.whileLoop test nextBody after (ObjectAccessMemory.represent memory) _)).trans
                (block_while policy memory arrays scopes condition test expression nextBody after scalar evaluated)
              cases selected : IntegerScalar.truth scalar with
              | false =>
                  simp only [evaluated, selected, Bool.false_eq_true, ↓reduceIte] at stepped
                  cases stepped
                  exact ⟨_, _, _, rfl, .flow .normal continuation, by simpa only [selected, Bool.false_eq_true, ↓reduceIte, lowerFlow] using block⟩
              | true =>
                  simp only [evaluated, selected, ↓reduceIte] at stepped
                  cases stepped
                  exact ⟨_, _, _, rfl, .statement bodyResolved (.loop expression bodyResolved continuation),
                    by simpa only [selected, ↓reduceIte] using block⟩
  | breakLoop =>
      refine ⟨memory, ?_⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith] at stepped
      cases stepped
      exact ⟨_, _, _, rfl, .flow .broken continuation,
        block_administrative policy _ _ (fun _ => .breakLoop _ _ _)⟩
  | continueLoop =>
      refine ⟨memory, ?_⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith] at stepped
      cases stepped
      exact ⟨_, _, _, rfl, .flow .continued continuation,
        block_administrative policy _ _ (fun _ => .continueLoop _ _ _)⟩
  | returnEmpty =>
      refine ⟨memory, ?_⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith] at stepped
      cases stepped
      exact ⟨_, _, _, rfl, .returning none continuation,
        block_administrative policy _ _ (fun _ => .returnEmpty _ _ _)⟩
  | @returnValue expression value resolved =>
      refine ⟨memory, ?_⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith,
        FixedCore.Configuration.fail] at stepped
      have kind := resolved.integer_result
      cases evaluated : FixedCore.evaluate model policy memory arrays scopes expression with
      | fault reason => simp only [evaluated] at stepped; cases stepped; cases running
      | value returned =>
          cases returned with
          | address address => simp only [evaluated, IntegerResult] at kind
          | null => simp only [evaluated, IntegerResult] at kind
          | integer scalar =>
              simp only [evaluated] at stepped
              cases stepped
              exact ⟨_, _, _, rfl, .returning (some scalar) continuation,
                block_return policy memory arrays scopes expression value resolved after scalar evaluated⟩

end StatementBlocks

section ControlSteps
open IntegerMemoryModel LocatedExpressions
open LocatedExpressionData (IndexData)
variable {model : Model}

/-- Every successful common-fragment fixed control transition is realized by
an actual finite located history. Actual writes are preserved; lexical resolution, array identity
and the caller's unused schedule are retained. -/
theorem control_step_simulation (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {target : List IndexData → LocatedStatements.SemanticConfiguration model}
    (related : ControlRelated policy memory arrays scopes control following target)
    (next : FixedCore.Executable model)
    (stepped : FixedCore.step model policy abi program choice
      (fixedConfiguration memory arrays scopes heap control following) = some next)
    (running : next.status = .running) :
    ∃ nextMemory newControl newFollowing newTarget,
      next = fixedConfiguration nextMemory arrays scopes heap newControl newFollowing ∧
      ControlRelated policy nextMemory arrays scopes newControl newFollowing newTarget ∧
      Block policy target newTarget := by
  cases related with
  | statement statement continuation =>
      exact statement_step_simulation policy memory arrays scopes heap abi program choice
        statement continuation next stepped running
  | @flow flow before after continuation =>
      refine ⟨memory, ?_⟩
      cases continuation with
      | stop =>
          cases flow with
          | normal =>
              simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
                FixedCore.Configuration.continueWith] at stepped
              cases stepped
              exact ⟨_, _, _, rfl, .fallthrough, Block.refl policy _⟩
          | broken | continued =>
              simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
                FixedCore.Configuration.fail] at stepped
              cases stepped
              cases running
      | @sequence source target before after statement continuation =>
          cases flow with
          | normal =>
              simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
                FixedCore.Configuration.continueWith] at stepped
              cases stepped
              exact ⟨_, _, _, rfl, .statement statement continuation,
                block_administrative policy _ _ (fun _ => .normalSequence _ _ _ _)⟩
          | broken =>
              simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
                FixedCore.Configuration.continueWith] at stepped
              cases stepped
              exact ⟨_, _, _, rfl, .flow .broken continuation,
                block_administrative policy _ _ (fun _ => .brokenSequence _ _ _ _)⟩
          | continued =>
              simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
                FixedCore.Configuration.continueWith] at stepped
              cases stepped
              exact ⟨_, _, _, rfl, .flow .continued continuation,
                block_administrative policy _ _ (fun _ => .continuedSequence _ _ _ _)⟩
      | @loop condition test body nextBody before after expression statement continuation =>
          cases flow with
          | broken =>
              simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
                FixedCore.Configuration.continueWith] at stepped
              cases stepped
              exact ⟨_, _, _, rfl, .flow .normal continuation,
                block_administrative policy _ _ (fun _ => .breakWhile _ _ _ _ _)⟩
          | normal =>
              simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
                FixedCore.Configuration.continueWith] at stepped
              cases stepped
              exact ⟨_, _, _, rfl, .loopExpression expression statement continuation,
                block_iteration policy _ _ .whileLoop (fun _ => .whileLoop .normal .normal _ _ _ _ _)⟩
          | continued =>
              simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
                FixedCore.Configuration.continueWith] at stepped
              cases stepped
              exact ⟨_, _, _, rfl, .loopExpression expression statement continuation,
                block_iteration policy _ _ .whileLoop (fun _ => .whileLoop .continued .continued _ _ _ _ _)⟩
  | @loopExpression condition test body nextBody before after expression statement continuation =>
      refine ⟨memory, ?_⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith,
        FixedCore.Configuration.fail] at stepped
      cases evaluated : FixedCore.evaluate model policy memory arrays scopes condition with
      | fault reason => simp only [evaluated] at stepped; cases stepped; cases running
      | value value =>
          cases value with
          | address address => simp only [evaluated] at stepped; cases stepped; cases running
          | null => simp only [evaluated] at stepped; cases stepped; cases running
          | integer scalar =>
              have block := block_while policy memory arrays scopes condition test expression nextBody after scalar evaluated
              cases selected : IntegerScalar.truth scalar with
              | false =>
                  simp only [evaluated, selected, Bool.false_eq_true, ↓reduceIte] at stepped
                  cases stepped
                  exact ⟨_, _, _, rfl, .flow .normal continuation,
                    by simpa only [selected, Bool.false_eq_true, ↓reduceIte, lowerFlow] using block⟩
              | true =>
                  simp only [evaluated, selected, ↓reduceIte] at stepped
                  cases stepped
                  exact ⟨_, _, _, rfl, .statement statement (.loop expression statement continuation),
                    by simpa only [selected, ↓reduceIte] using block⟩
  | @returning value before after continuation =>
      refine ⟨memory, ?_⟩
      cases continuation with
      | stop =>
          simp only [fixedConfiguration, FixedCore.step, FixedCore.advance] at stepped
          cases stepped
          cases running
      | sequence statement continuation =>
          simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
            FixedCore.Configuration.continueWith] at stepped
          cases stepped
          exact ⟨_, _, _, rfl, .returning value continuation, Block.refl policy _⟩
      | loop expression statement continuation =>
          simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
            FixedCore.Configuration.continueWith] at stepped
          cases stepped
          exact ⟨_, _, _, rfl, .returning value continuation, Block.refl policy _⟩
  | fallthrough =>
      refine ⟨memory, ?_⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance] at stepped
      cases stepped
      cases running

end ControlSteps

section FiniteHistories
open IntegerMemoryModel LocatedExpressions
open LocatedExpressionData (IndexData)
variable {model : Model}

/-- Arbitrary finite histories of the real fixed-core stepper, including
loop iteration, compose into located histories with the same retained control
boundary. Each fixed step carries its actual open allocation-choice packet;
this fragment does not inspect it or change allocation state. -/
theorem running_history_simulation (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {target : List IndexData → LocatedStatements.SemanticConfiguration model}
    (related : ControlRelated policy memory arrays scopes control following target)
    (final : FixedCore.Executable model)
    (history : Relation.ReflTransGen
      (fun before after => ∃ choice, FixedCore.step model policy abi program choice before = some after ∧
        after.status = .running)
      (fixedConfiguration memory arrays scopes heap control following) final) :
    ∃ finalMemory finalControl finalFollowing finalTarget,
      final = fixedConfiguration finalMemory arrays scopes heap finalControl finalFollowing ∧
      ControlRelated policy finalMemory arrays scopes finalControl finalFollowing finalTarget ∧
      Block policy target finalTarget := by
  induction history with
  | refl => exact ⟨memory, _, _, _, rfl, related, Block.refl policy target⟩
  | @tail middle final history step ih =>
      obtain ⟨middleMemory, middleControl, middleFollowing, middleTarget, rfl, middleRelated, firstBlock⟩ := ih
      obtain ⟨choice, stepped, running⟩ := step
      obtain ⟨finalMemory, finalControl, finalFollowing, finalTarget, represented, finalRelated, lastBlock⟩ :=
        control_step_simulation policy middleMemory arrays scopes heap abi program choice middleRelated final stepped running
      exact ⟨finalMemory, finalControl, finalFollowing, finalTarget, represented, finalRelated, firstBlock.trans lastBlock⟩

/-- A source-step block is executable on the existing located machine; the
saved endpoint and the chronological receipts are constructed, not assumed. -/
theorem Block.realization {policy : SignedConversionPolicy}
    {before after : List IndexData → LocatedStatements.SemanticConfiguration model}
    (block : Block policy before after) (rest : List IndexData)
    (load : List IndexData → LocatedStatements.Configuration model)
    (represented : ∀ selections, LocatedStatements.represent (load selections) = before selections) :
    ∃ choices, ∃ events : List (Option (LocatedStatements.Event model)), ∃ saved receipts,
      LocatedStatements.represent saved = after rest ∧
      (StatementMachine.machine model policy).run events.length (load (choices ++ rest)) =
        (receipts, .exhausted saved) ∧
      receipts.map StatementMachine.Receipt.event = events.filterMap id := by
  obtain ⟨choices, events, history⟩ := block rest
  obtain ⟨saved, receipts, final, executed, observations⟩ :=
    StatementHistory.history_realization policy _ _ events history (load (choices ++ rest)) (represented _)
  exact ⟨choices, events, saved, receipts, final, executed, observations⟩

/-- Only normal function fallthrough and an explicit integer/void return
count as a common successful output. Diagnostic states remain excluded. -/
def output : LocatedStatements.SemanticConfiguration model → Option (Option (IntegerScalar.Value model.parameters))
  | .returned value _ _ => some value
  | .flow .normal .stop _ _ => some none
  | _ => none

theorem control_finish_observation (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {target : List IndexData → LocatedStatements.SemanticConfiguration model}
    (related : ControlRelated policy memory arrays scopes control following target)
    (next : FixedCore.Executable model) (value : Option (FixedCore.Value model))
    (stepped : FixedCore.step model policy abi program choice
      (fixedConfiguration memory arrays scopes heap control following) = some next)
    (finished : next.status = .finished value) :
    ∃ result, value = scalarReturn result ∧ ∀ selections, output (target selections) = some result := by
  cases related with
  | statement statement continuation =>
      cases statement <;>
        simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
          FixedCore.Configuration.continueWith, FixedCore.Configuration.fail] at stepped
      all_goals repeat first | split at stepped | (cases stepped; cases finished)
  | flow flow continuation =>
      cases continuation <;> cases flow <;>
        simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
          FixedCore.Configuration.continueWith, FixedCore.Configuration.fail] at stepped
      all_goals cases stepped; cases finished
  | loopExpression expression statement continuation =>
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
        FixedCore.Configuration.continueWith, FixedCore.Configuration.fail] at stepped
      repeat first | split at stepped | (cases stepped; cases finished)
  | returning result continuation =>
      cases continuation with
      | stop =>
          simp only [fixedConfiguration, FixedCore.step, FixedCore.advance] at stepped
          cases stepped
          have same : scalarReturn result = value := FixedCore.Status.finished.inj finished
          exact ⟨result, same.symm, fun _ => rfl⟩
      | sequence statement continuation =>
          simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
            FixedCore.Configuration.continueWith] at stepped
          cases stepped; cases finished
      | loop expression statement continuation =>
          simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
            FixedCore.Configuration.continueWith] at stepped
          cases stepped; cases finished
  | fallthrough =>
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance] at stepped
      cases stepped
      have same : none = value := FixedCore.Status.finished.inj finished
      exact ⟨none, same.symm, fun _ => rfl⟩

/-- A whole successful finite fixed history has a located history ending with
the same return observation. Arbitrarily many loop iterations are permitted;
termination is the input history, not an additional global assumption. -/
theorem completed_history_simulation (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {target : List IndexData → LocatedStatements.SemanticConfiguration model}
    (related : ControlRelated policy memory arrays scopes control following target)
    (before final : FixedCore.Executable model) (value : Option (FixedCore.Value model))
    (history : Relation.ReflTransGen
      (fun before after => ∃ choice, FixedCore.step model policy abi program choice before = some after ∧
        after.status = .running)
      (fixedConfiguration memory arrays scopes heap control following) before)
    (choice : FixedCore.Choice)
    (last : FixedCore.step model policy abi program choice before = some final)
    (finished : final.status = .finished value) :
    ∃ result after, value = scalarReturn result ∧ Block policy target after ∧
      ∀ selections, output (after selections) = some result := by
  obtain ⟨finalMemory, finalControl, finalFollowing, finalTarget, rfl, finalRelated, block⟩ :=
    running_history_simulation policy memory arrays scopes heap abi program related before history
  obtain ⟨result, observed, outputs⟩ :=
    control_finish_observation policy finalMemory arrays scopes heap abi program choice finalRelated final value last finished
  exact ⟨result, finalTarget, observed, block, outputs⟩

def verdictOutput : StatementMachine.Verdict model → Option (Option (IntegerScalar.Value model.parameters))
  | .returned value _ => some value
  | .fallthrough _ => some none
  | _ => none

theorem output_finishes (policy : SignedConversionPolicy)
    (saved : LocatedStatements.Configuration model) (value : Option (IntegerScalar.Value model.parameters))
    (observed : output (LocatedStatements.represent saved) = some value) :
    ∃ verdict, (StatementMachine.machine model policy).step saved = some (.finish verdict) ∧
      verdictOutput verdict = some value := by
  cases saved with
  | statement statement continuation memory choices => cases observed
  | expression expression state continuation choices => cases observed
  | returned result memory choices =>
      cases observed
      exact ⟨.returned _ _, rfl, rfl⟩
  | flow flow continuation memory choices =>
      cases continuation <;> cases flow <;> simp only [LocatedStatements.represent, output, reduceCtorEq] at observed
      cases observed
      exact ⟨.fallthrough _, rfl, rfl⟩

/-- A successfully completed source block finishes on the actual located
runner, preserving every emitted receipt and the exact unused selection suffix. -/
theorem Block.finished_realization {policy : SignedConversionPolicy}
    {before after : List IndexData → LocatedStatements.SemanticConfiguration model}
    (block : Block policy before after) (rest : List IndexData)
    (load : List IndexData → LocatedStatements.Configuration model)
    (represented : ∀ selections, LocatedStatements.represent (load selections) = before selections)
    (value : Option (IntegerScalar.Value model.parameters)) (observed : output (after rest) = some value) :
    ∃ choices events saved receipts verdict,
      LocatedStatements.represent saved = after rest ∧
      (StatementMachine.machine model policy).run (events.length + 1) (load (choices ++ rest)) =
        (receipts, .finished verdict) ∧
      receipts.map StatementMachine.Receipt.event = (events : List (Option (LocatedStatements.Event model))).filterMap id ∧
      verdictOutput verdict = some value := by
  obtain ⟨choices, events, saved, receipts, endpoint, executed, emissions⟩ := block.realization rest load represented
  obtain ⟨verdict, finish, result⟩ := output_finishes policy saved value (endpoint.symm ▸ observed)
  refine ⟨choices, events, saved, receipts, verdict, endpoint, ?_, emissions, result⟩
  rw [(StatementMachine.machine model policy).run_add, executed]
  simp only [Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine.continueRun,
    (StatementMachine.machine model policy).run_succ_finish (fuel := 0) finish, List.append_nil]

end FiniteHistories

section AssignmentOperations
open IntegerMemoryModel ExpressionEvents ExpressionEventExecution LocatedExpressions
variable {model : Model} {Index : Type} [DecidableEq Index]

theorem available_unique {cache : Cache Index model} {index : Index}
    {first second : IntegerScalar.Value model.parameters}
    (left : Available cache index first) (right : Available cache index second) : first = second :=
  Option.some.inj (((lookupScalar_iff _ _ _).mpr left).symm.trans ((lookupScalar_iff _ _ _).mpr right))

theorem cast_operation_result
    (policy : SignedConversionPolicy) (before after : ObjectAccessMemory.SemanticState model.characters)
    (type : IntegerType IntegerExtension) (input : IntegerScalar.Value model.parameters)
    (cache : Cache Index model) (index : Index) (outcome : Outcome model)
    (inputPresent : Available cache index input)
    (casting : OperationEvaluation model policy cache before (.cast type index) outcome after) :
    ∃ result, IntegerScalar.CastEvaluation model.parameters policy type input result ∧
      outcome = castOutcome model result ∧ after = before := by
  cases casting with
  | cast type source value result present conversion =>
      have same := available_unique present inputPresent
      subst value
      exact ⟨result, conversion, rfl, rfl⟩

/-- Assignment's conversion and owned write are the same independently judged
operations as the located machine's separate cast and store occurrences.
Caches identify the input and converted value; they do not license a store
before its sequencing predecessors have executed. -/
theorem assignment_operations_iff
    (policy : SignedConversionPolicy) (before after : ObjectAccessMemory.SemanticState model.characters)
    (destination : Destination) (input converted : IntegerScalar.Value model.parameters)
    (inputs outputs : Cache Index model) (inputIndex outputIndex : Index)
    (inputPresent : Available inputs inputIndex input)
    (outputPresent : Available outputs outputIndex converted) :
    IntegerAssignment.Assigning model policy before destination.location input (.stored converted) after ↔
      OperationEvaluation model policy inputs before (.cast destination.type inputIndex) (.value converted) before ∧
      OperationEvaluation model policy outputs before (.store destination.location outputIndex) (.stored converted) after := by
  constructor
  · intro assigning
    cases assigning with
    | stored after location input converted type formed conversion writing =>
        have same : type = destination.type := by
          rw [destination.formed] at formed
          injection formed with same
          injection same with equal
          exact equal.symm
        subst type
        exact ⟨.cast _ _ _ _ (.value converted) inputPresent conversion,
          .store _ _ _ _ _ outputPresent writing⟩
  · rintro ⟨casting, storing⟩
    obtain ⟨result, conversion, outcome, _⟩ := cast_operation_result policy before before destination.type
      input inputs inputIndex (.value converted) inputPresent casting
    have same : result = .value converted := (castOutcome_injective model) outcome.symm
    subst result
    cases storing with
    | store after location source scalar present writing =>
        exact .stored _ _ _ _ _ destination.type destination.formed conversion writing

/-- The fixed core's actual checked element store and the two located
operations have exactly the same successful semantic-memory endpoint. -/
theorem storeElement_operations_iff
    (policy : SignedConversionPolicy) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (address : FixedCore.Address) (range : ByteRanges.Range)
    (inside : ArrayPointers.ElementRange (ByteRanges.heap memory.storage) arrays address.pointer range)
    (input : IntegerScalar.Value model.parameters) (after : ObjectAccessMemory.SemanticState model.characters) :
    (FixedCore.storeElement model policy memory arrays address input).represent = .done after ↔
      ∃ converted,
        OperationEvaluation model policy ([(0, .value input)] : Cache Nat model)
          (ObjectAccessMemory.represent memory) (.cast address.type 0) (.value converted)
          (ObjectAccessMemory.represent memory) ∧
        OperationEvaluation model policy ([(1, .value converted)] : Cache Nat model)
          (ObjectAccessMemory.represent memory) (.store (FixedCore.elementLvalue address range) 1) (.stored converted) after := by
  let destination : Destination := ⟨FixedCore.elementLvalue address range, address.type, rfl⟩
  have inputPresent : Available ([(0, .value input)] : Cache Nat model) 0 input := (lookupScalar_iff _ _ _).mp rfl
  have outputPresent (value : IntegerScalar.Value model.parameters) :
      Available ([(1, .value value)] : Cache Nat model) 1 value := (lookupScalar_iff _ _ _).mp rfl
  constructor
  · intro stored
    have independent := FixedCore.storeElement_sound model policy memory arrays address input
    rw [stored] at independent
    cases independent with
    | stored other converted final inRange assigning =>
        have same : other = range := Option.some.inj
          (((ArrayPointers.elementRange_iff _ _ _ _).mpr inRange).symm.trans
            ((ArrayPointers.elementRange_iff _ _ _ _).mpr inside))
        subst other
        exact ⟨converted, (assignment_operations_iff policy _ _ destination input converted _ _ 0 1
          inputPresent (outputPresent converted)).mp assigning⟩
  · rintro ⟨converted, cast, store⟩
    have assigning := (assignment_operations_iff policy _ _ destination input converted _ _ 0 1
      inputPresent (outputPresent converted)).mpr ⟨cast, store⟩
    obtain ⟨saved, assigned, represented⟩ := IntegerAssignment.assign_complete model policy memory after
      destination.location input (.stored converted) assigning
    simp only [FixedCore.storeElement, (ArrayPointers.elementRange_iff _ _ _ _).mpr inside,
      assigned, destination, FixedCore.Effect.represent, represented]

end AssignmentOperations

section StatementLowering
open IntegerMemoryModel LocatedExpressions
variable {model : Model}

/-- Executable admission and lowering for the common control fragment. Calls and
declarations are not disguised as empty control operations. -/
def lowerStatement (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) : FixedCore.Statement model → Option (LocatedStatements.Statement model)
  | .assign (.named name) source => do
      let location ← lower memory arrays scopes (.read (.named name))
      match location with
      | .load destination => do
          let operand ← lower memory arrays scopes source
          pure (.expression (.assignment destination operand))
      | _ => none
  | .skip => some .empty
  | .sequence first second => do
      let left ← lowerStatement memory arrays scopes first
      let right ← lowerStatement memory arrays scopes second
      pure (.sequence left right)
  | .conditional condition yes no => do
      let test ← lower memory arrays scopes condition
      let left ← lowerStatement memory arrays scopes yes
      let right ← lowerStatement memory arrays scopes no
      pure (.conditional test left right)
  | .whileLoop condition body => do
      let test ← lower memory arrays scopes condition
      let next ← lowerStatement memory arrays scopes body
      pure (.whileLoop test next)
  | .breakLoop => some .breakLoop
  | .continueLoop => some .continueLoop
  | .returnValue none => some (.returnValue none)
  | .returnValue (some expression) => do
      let value ← lower memory arrays scopes expression
      pure (.returnValue (some value))
  | _ => none

theorem lowerStatement_sound (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Statement model)
    (target : LocatedStatements.Statement model)
    (lowered : lowerStatement memory arrays scopes source = some target) :
    ResolvesStatement policy memory arrays scopes source target := by
  cases source with
  | assign place source =>
      cases place with
      | named name =>
          obtain ⟨location, readLowered, after⟩ := Option.bind_eq_some_iff.mp lowered
          cases location with
          | load destination =>
              obtain ⟨operand, operandLowered, after⟩ := Option.bind_eq_some_iff.mp after
              have same : LocatedStatements.Statement.expression (.assignment destination operand) = target := Option.some.inj after
              rw [← same]
              exact .assignment name (lower_sound policy memory arrays scopes _ _ readLowered)
                (lower_sound policy memory arrays scopes _ _ operandLowered)
          | value _ | arithmetic _ _ _ | cast _ _ | assignment _ _ | update _ _ _ | comma _ _ => cases after
      | element _ _ | deref _ => cases lowered
  | skip => cases lowered; exact .skip
  | sequence first second =>
      obtain ⟨left, leftLowered, after⟩ := Option.bind_eq_some_iff.mp lowered
      obtain ⟨right, rightLowered, after⟩ := Option.bind_eq_some_iff.mp after
      have same : LocatedStatements.Statement.sequence left right = target := Option.some.inj after
      rw [← same]
      exact .sequence (lowerStatement_sound policy memory arrays scopes first left leftLowered)
        (lowerStatement_sound policy memory arrays scopes second right rightLowered)
  | conditional condition yes no =>
      obtain ⟨test, testLowered, after⟩ := Option.bind_eq_some_iff.mp lowered
      obtain ⟨left, leftLowered, after⟩ := Option.bind_eq_some_iff.mp after
      obtain ⟨right, rightLowered, after⟩ := Option.bind_eq_some_iff.mp after
      have same : LocatedStatements.Statement.conditional test left right = target := Option.some.inj after
      rw [← same]
      exact .conditional (lower_sound policy memory arrays scopes condition test testLowered)
        (lowerStatement_sound policy memory arrays scopes yes left leftLowered)
        (lowerStatement_sound policy memory arrays scopes no right rightLowered)
  | whileLoop condition body =>
      obtain ⟨test, testLowered, after⟩ := Option.bind_eq_some_iff.mp lowered
      obtain ⟨next, nextLowered, after⟩ := Option.bind_eq_some_iff.mp after
      have same : LocatedStatements.Statement.whileLoop test next = target := Option.some.inj after
      rw [← same]
      exact .whileLoop (lower_sound policy memory arrays scopes condition test testLowered)
        (lowerStatement_sound policy memory arrays scopes body next nextLowered)
  | breakLoop => cases lowered; exact .breakLoop
  | continueLoop => cases lowered; exact .continueLoop
  | returnValue value =>
      cases value with
      | none => cases lowered; exact .returnEmpty
      | some expression =>
          obtain ⟨inner, innerLowered, after⟩ := Option.bind_eq_some_iff.mp lowered
          have same : LocatedStatements.Statement.returnValue (some inner) = target := Option.some.inj after
          rw [← same]
          exact .returnValue (lower_sound policy memory arrays scopes expression inner innerLowered)
  | setPointer _ _ | call _ _ _ | external _ _ _ | allocate _ _ _ | release _ | block _ _ => cases lowered
termination_by source

theorem lowerStatement_complete {policy : SignedConversionPolicy}
    {memory : ObjectAccessMemory.State model.characters} {arrays : ArrayPointers.Catalog}
    {scopes : List (FixedCore.Scope model)} {source : FixedCore.Statement model}
    {target : LocatedStatements.Statement model}
    (resolved : ResolvesStatement policy memory arrays scopes source target) :
    lowerStatement memory arrays scopes source = some target := by
  induction resolved with
  | assignment name location value =>
      simp only [lowerStatement, lower_complete location, lower_complete value, bind, Option.bind_some, pure, Pure.pure]
  | skip | breakLoop | continueLoop | returnEmpty => rfl
  | sequence first second ihFirst ihSecond => simp only [lowerStatement, ihFirst, ihSecond, bind, Option.bind_some, pure, Pure.pure]
  | conditional expression yes no ihYes ihNo =>
      simp only [lowerStatement, lower_complete expression, ihYes, ihNo, bind, Option.bind_some, pure, Pure.pure]
  | whileLoop expression body ih =>
      simp only [lowerStatement, lower_complete expression, ih, bind, Option.bind_some, pure, Pure.pure]
  | returnValue resolved => simp only [lowerStatement, lower_complete resolved, bind, Option.bind_some, pure, Pure.pure]

theorem lowerStatement_iff (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Statement model)
    (target : LocatedStatements.Statement model) :
    lowerStatement memory arrays scopes source = some target ↔
      ResolvesStatement policy memory arrays scopes source target :=
  ⟨lowerStatement_sound policy memory arrays scopes source target, lowerStatement_complete⟩

end StatementLowering

section DecisionReflection
open IntegerMemoryModel LocatedExpressions ExpressionEvents ExpressionEventExecution ExpressionEventHistory
open LocatedExpressionData (IndexData)
variable {model : Model}

/-- A pending expression retains the source control which owns its eventual
branch/return decision. Its prior occurrences, not an arbitrary cache, justify
the value available at that decision. -/
inductive ExpressionControl (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) : FixedCore.Control model → FixedCore.Continuation model →
      Expression model → LocatedStatements.AfterExpression model → Prop where
  | conditional {condition : FixedCore.Expression model} {test : Expression model}
      {yes no : FixedCore.Statement model} {left right : LocatedStatements.Statement model}
      {before : FixedCore.Continuation model} {after : LocatedStatements.Continuation model}
      (expression : ResolvesExpression policy memory arrays scopes condition test)
      (onTrue : ResolvesStatement policy memory arrays scopes yes left)
      (onFalse : ResolvesStatement policy memory arrays scopes no right)
      (continuation : ResolvesContinuation policy memory arrays scopes before after) :
      ExpressionControl policy memory arrays scopes (.execute (.conditional condition yes no)) before
        test (.conditional left right after)
  | whileLoop {condition : FixedCore.Expression model} {test : Expression model}
      {body : FixedCore.Statement model} {next : LocatedStatements.Statement model}
      {before : FixedCore.Continuation model} {after : LocatedStatements.Continuation model}
      (expression : ResolvesExpression policy memory arrays scopes condition test)
      (statement : ResolvesStatement policy memory arrays scopes body next)
      (continuation : ResolvesContinuation policy memory arrays scopes before after) :
      ExpressionControl policy memory arrays scopes (.execute (.whileLoop condition body)) before
        test (.whileCondition test next after)
  | returnValue {source : FixedCore.Expression model} {target : Expression model}
      {before : FixedCore.Continuation model} {after : LocatedStatements.Continuation model}
      (expression : ResolvesExpression policy memory arrays scopes source target)
      (continuation : ResolvesContinuation policy memory arrays scopes before after) :
      ExpressionControl policy memory arrays scopes (.execute (.returnValue (some source))) before target .returnValue

/-- Any complete, history-justified located decision reflects the corresponding
actual fixed-core transition. This is independent of the chosen occurrence
schedule and excludes forged cached results. -/
theorem expression_boundary_reflection (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {expression : Expression model} {continuation : LocatedStatements.AfterExpression model}
    (context : ExpressionControl policy memory arrays scopes control following expression continuation)
    (events : List (Occurrence (Index expression) model)) (saved : SemanticState (Index expression) model)
    (history : SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) events saved)
    (scalar : IntegerScalar.Value model.parameters)
    (completed : LocatedStatements.CompleteExpression expression saved scalar)
    (selections : List IndexData) (target : LocatedStatements.SemanticConfiguration model)
    (boundary : StatementSemantics.BoundaryTarget continuation scalar saved.memory selections target) :
    ∃ newControl newFollowing newTarget,
      FixedCore.step model policy abi program choice
          (fixedConfiguration memory arrays scopes heap control following) =
        some (fixedConfiguration memory arrays scopes heap newControl newFollowing) ∧
      ControlRelated policy memory arrays scopes newControl newFollowing newTarget ∧
      newTarget selections = target ∧ saved.memory = ObjectAccessMemory.represent memory := by
  cases context with
  | @conditional condition test yes no left right before after resolved onTrue onFalse continuation =>
      obtain ⟨observed, unchanged⟩ := source_boundary_no_invention policy memory arrays scopes condition expression resolved
        events saved history scalar completed
      have evaluated := (observe_some_iff _ _).mp observed
      rw [unchanged] at boundary
      have targetShape := StatementExecution.afterExpression_complete _ _ memory selections target boundary
      refine ⟨.execute (if IntegerScalar.truth scalar then yes else no), following,
        (fun rest => .statement (if IntegerScalar.truth scalar then left else right)
          after (ObjectAccessMemory.represent memory) rest), ?_, ?_, ?_, unchanged⟩
      · simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, evaluated, FixedCore.Configuration.continueWith]
      · cases IntegerScalar.truth scalar with
        | false => exact .statement onFalse continuation
        | true => exact .statement onTrue continuation
      · simpa only [StatementExecution.afterExpression, LocatedStatements.represent, ← scalar_truth_agrees] using targetShape
  | @whileLoop condition test body nextBody before after resolved statement continuation =>
      obtain ⟨observed, unchanged⟩ := source_boundary_no_invention policy memory arrays scopes condition expression resolved
        events saved history scalar completed
      have evaluated := (observe_some_iff _ _).mp observed
      rw [unchanged] at boundary
      have targetShape := StatementExecution.afterExpression_complete _ _ memory selections target boundary
      cases selected : IntegerScalar.truth scalar with
      | false =>
          refine ⟨.flow .normal, following,
            (fun rest => .flow .normal after (ObjectAccessMemory.represent memory) rest), ?_, .flow .normal continuation,
            ?_, unchanged⟩
          · simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, evaluated, selected,
              Bool.false_eq_true, ↓reduceIte, FixedCore.Configuration.continueWith]
          · simpa only [StatementExecution.afterExpression, ← scalar_truth_agrees, selected, Bool.false_eq_true,
              ↓reduceIte, LocatedStatements.represent] using targetShape
      | true =>
          refine ⟨.execute body, .loop condition body following,
            (fun rest => .statement nextBody (.whileBody expression nextBody after) (ObjectAccessMemory.represent memory) rest),
            ?_, .statement statement (.loop resolved statement continuation), ?_, unchanged⟩
          · simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, evaluated, selected,
              ↓reduceIte, FixedCore.Configuration.continueWith]
          · simpa only [StatementExecution.afterExpression, ← scalar_truth_agrees, selected,
              ↓reduceIte, LocatedStatements.represent] using targetShape
  | @returnValue source expression before after resolved continuation =>
      obtain ⟨observed, unchanged⟩ := source_boundary_no_invention policy memory arrays scopes source expression resolved
        events saved history scalar completed
      have evaluated := (observe_some_iff _ _).mp observed
      rw [unchanged] at boundary
      have targetShape := StatementExecution.afterExpression_complete _ _ memory selections target boundary
      refine ⟨.returning (some (.integer scalar)), following,
        (fun rest => .returned (some scalar) (ObjectAccessMemory.represent memory) rest), ?_,
        .returning (some scalar) continuation, ?_, unchanged⟩
      · simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, evaluated, FixedCore.Configuration.continueWith]
      · exact targetShape

end DecisionReflection

section AssignmentReflection
open IntegerMemoryModel LocatedExpressions ExpressionEvents ExpressionEventExecution ExpressionEventHistory
open LocatedExpressionData (IndexData)
variable {model : Model}

/-- Every complete legal assignment schedule performs the same independent
conversion and owned write. The two final occurrences need not be in the same order. -/
theorem assignment_history_sound (policy : SignedConversionPolicy)
    (before : ObjectAccessMemory.State model.characters) (destination : Destination)
    (operand : Expression model) (pure : Pure operand)
    (events : List (Occurrence (Index (.assignment destination operand)) model))
    (final : SemanticState (Index (.assignment destination operand)) model)
    (history : SemanticHistory policy (compile (.assignment destination operand))
      (represent (initialState (compile (.assignment destination operand)) before)) events final)
    (scalar : IntegerScalar.Value model.parameters)
    (complete : LocatedStatements.CompleteExpression (.assignment destination operand) final scalar) :
    ∃ input, evaluate policy before operand = some input ∧
      IntegerAssignment.Assigning model policy (ObjectAccessMemory.represent before) destination.location input
        (.stored scalar) final.memory := by
  let : DecidableEq (Index (.cast destination.type operand)) := LocatedExpressions.instDecidableEqIndex _
  have pureCast : Pure (.cast destination.type operand) := .cast _ pure
  obtain ⟨value, writing⟩ := storeResult_history_sound policy (compile (.cast destination.type operand)) before
    destination.location (values policy before (.cast destination.type operand)) pureCast.readOnly
    (pureCast.equations policy before) (by simpa only [compiled_result] using pureCast.root_dominates)
    events final history complete.pending scalar complete.result
  rw [compiled_result, values_result] at value
  obtain ⟨input, evaluated, converted⟩ := Option.bind_eq_some_iff.mp value
  have castValue : IntegerScalar.cast model.parameters policy destination.type input = .value scalar := by
    cases result : IntegerScalar.cast model.parameters policy destination.type input with
    | value actual =>
        change (castOutcome model (IntegerScalar.cast model.parameters policy destination.type input)).scalar = some scalar at converted
        simp only [result, castOutcome, Outcome.scalar, Option.some.injEq] at converted
        rw [converted]
    | signal identifier =>
        change (castOutcome model (IntegerScalar.cast model.parameters policy destination.type input)).scalar = some scalar at converted
        simp only [result, castOutcome, Outcome.scalar, reduceCtorEq] at converted
  refine ⟨input, evaluated, .stored _ _ _ _ _ destination.type destination.formed ?_ writing⟩
  have checked := IntegerScalar.cast_sound model.parameters policy destination.type input
  rw [castValue] at checked
  exact checked

/-- The common named assignment has no extra successful located behavior.
Its actual fixed-core step reaches the same semantic memory, with no replay. -/
theorem assignment_boundary_reflection (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice) (name : String) (source : FixedCore.Expression model)
    (destination : Destination) (operand : Expression model)
    (located : ResolvesExpression policy memory arrays scopes (.read (.named name)) (.load destination))
    (resolved : ResolvesExpression policy memory arrays scopes source operand)
    (before : FixedCore.Continuation model) (after : LocatedStatements.Continuation model)
    (continuation : ResolvesContinuation policy memory arrays scopes before after)
    (events : List (Occurrence (Index (.assignment destination operand)) model))
    (final : SemanticState (Index (.assignment destination operand)) model)
    (history : SemanticHistory policy (compile (.assignment destination operand))
      (represent (initialState (compile (.assignment destination operand)) memory)) events final)
    (scalar : IntegerScalar.Value model.parameters)
    (complete : LocatedStatements.CompleteExpression (.assignment destination operand) final scalar) :
    ∃ saved, FixedCore.step model policy abi program choice
      (fixedConfiguration memory arrays scopes heap (.execute (.assign (.named name) source)) before) =
        some (fixedConfiguration saved arrays scopes heap (.flow .normal) before) ∧
      ObjectAccessMemory.represent saved = final.memory ∧
      ResolvesContinuation policy saved arrays scopes before after := by
  obtain ⟨input, evaluated, assigned⟩ := assignment_history_sound policy memory destination operand resolved.pure
    events final history scalar complete
  have sourceValue := observe_some_iff _ input |>.mp (resolved.evaluate.trans evaluated)
  cases located with
  | read _ declared address range nameResolved typed inside =>
    obtain ⟨saved, stored, represented⟩ := IntegerAssignment.assign_complete model policy memory final.memory
      (FixedCore.elementLvalue address range) input (.stored scalar) assigned
    have coreStored : FixedCore.storeElement model policy memory arrays address input = .done saved := by
      simp only [FixedCore.storeElement, (ArrayPointers.elementRange_iff _ _ _ _).mpr inside, stored]
    have place : FixedCore.locate model policy memory arrays scopes (.named name) = .ok address := by
      simp only [FixedCore.locate, FixedCore.resolve_complete _ _ _ nameResolved, FixedCore.objectAddress, typed]
    have written : Writing model (ObjectAccessMemory.represent memory) final.memory
        (FixedCore.elementLvalue address range) scalar := by cases assigned; assumption
    rw [← represented] at written
    refine ⟨saved, ?_, represented, continuation.transport (writing_preserves_allocation_headers _ _ _ _ written)⟩
    simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, place, sourceValue, coreStored]

/-- A failed fixed assignment cannot be disguised as a successful complete
located expression by choosing a different operand/store/result schedule. -/
theorem faulted_assignment_has_no_complete_history (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice) (name : String) (source : FixedCore.Expression model)
    (destination : Destination) (operand : Expression model)
    (located : ResolvesExpression policy memory arrays scopes (.read (.named name)) (.load destination))
    (resolved : ResolvesExpression policy memory arrays scopes source operand)
    (before : FixedCore.Continuation model) (after : LocatedStatements.Continuation model)
    (continuation : ResolvesContinuation policy memory arrays scopes before after)
    (next : FixedCore.Executable model) (fault : FixedCore.Fault model)
    (stepped : FixedCore.step model policy abi program choice
      (fixedConfiguration memory arrays scopes heap (.execute (.assign (.named name) source)) before) = some next)
    (failed : next.status = .faulted fault)
    (events : List (Occurrence (Index (.assignment destination operand)) model))
    (final : SemanticState (Index (.assignment destination operand)) model)
    (history : SemanticHistory policy (compile (.assignment destination operand))
      (represent (initialState (compile (.assignment destination operand)) memory)) events final)
    (scalar : IntegerScalar.Value model.parameters) :
    ¬ LocatedStatements.CompleteExpression (.assignment destination operand) final scalar := by
  intro complete
  obtain ⟨saved, actual, _, _⟩ := assignment_boundary_reflection policy memory arrays scopes heap abi program
    choice name source destination operand located resolved before after continuation events final history scalar complete
  have same := Option.some.inj (stepped.symm.trans actual)
  subst next
  cases failed
end AssignmentReflection

/-! ## Source faults, retained failures and exact pending histories

The fixed evaluator reports one diagnostic; independent located schedules may
encounter a different failing operand first. Correspondence therefore preserves
successful values and source refusal, while the located receipt history keeps
its precise diagnostic. Empty budgets and missing scheduler choices retain a
continuation instead of being folded into refusal. -/

section FaultAndPending

open IntegerMemoryModel ExpressionEvents ExpressionEventExecution ExpressionEventHistory LocatedExpressions
open LocatedExpressionData (IndexData encodeIndex)
variable {model : Model}

/-- An independently evaluated defined source value excludes every reached
terminal diagnostic and every refused ready occurrence. -/
theorem pure_failure_excludes_value (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (expression : Expression model)
    (pure : Pure expression) (events : List (Occurrence (Index expression) model))
    (final : SemanticState (Index expression) model)
    (history : SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) events final)
    (partition : Partition (compile expression) final.pending final.cache)
    (failed : Failure policy (compile expression) final)
    (scalar : IntegerScalar.Value model.parameters) :
    evaluate policy memory expression ≠ some scalar := by
  intro defined
  obtain ⟨unchanged, agrees⟩ := history.readOnly_values pure.readOnly
    (pure.equations policy memory) rfl (by intro index outcome found; cases found)
  have total := pure.total policy memory defined
  cases failed with
  | terminal index outcome halted recorded terminal =>
      have same := agrees index outcome recorded
      obtain ⟨value, valueEq⟩ := total index
      rw [valueEq] at same
      simp only [Outcome.terminal, same, Option.isNone_some, Bool.false_eq_true] at terminal
  | refused index continuing ready refused =>
      obtain ⟨outcome, after, step, _⟩ := readOnly_progress policy (compile expression) memory
        (values policy memory expression) pure.readOnly (pure.equations policy memory)
        (compiled_inputs_ordered expression) total final partition unchanged agrees continuing index ready
      cases step with
      | execute _ _ _ _ _ _ _ operation _ _ =>
          exact refused outcome after.memory operation

/-- The successful and failed alternatives are constructed on the actual
occurrence plan. Failure keeps its precise terminal record or refused operation. -/
theorem expression_complete_or_failure (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (expression : Expression model)
    (clean : ¬ (compile expression).component.evaluation.Undefined) :
    ∃ events final, SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) events (represent final) ∧
      Partition (compile expression) final.pending final.cache ∧
      ((∃ scalar, LocatedStatements.CompleteExpression expression (represent final) scalar) ∨
        Failure policy (compile expression) (represent final)) := by
  obtain ⟨events, final, history, partition, stopped⟩ := ExpressionEventHistory.complete_or_failure
    policy (compile expression) memory clean
  refine ⟨events, final, history, partition, ?_⟩
  rcases stopped with ⟨scalar, pending, unhalted, result⟩ | failed
  · exact Or.inl ⟨scalar, ⟨partition, pending, unhalted,
      fun undefined => clean ((ExpressionSourceExecution.compiled_conflict_iff _).mpr undefined),
      by simpa only [compiled_result, represent] using result⟩⟩
  · exact Or.inr failed

theorem pure_failure_iff_undefined (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (expression : Expression model)
    (pure : Pure expression) :
    evaluate policy memory expression = none ↔
    ∃ events final, SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) events (represent final) ∧
      Partition (compile expression) final.pending final.cache ∧
      Failure policy (compile expression) (represent final) := by
  constructor
  · intro undefined
    obtain ⟨events, final, history, partition, stopped⟩ := expression_complete_or_failure policy memory expression
      (readOnly_clean _ pure.readOnly)
    rcases stopped with ⟨scalar, completed⟩ | failed
    · have value := (history.readOnly_result pure.readOnly (pure.equations policy memory)
        (by simpa only [compiled_result] using completed.result)).1
      rw [compiled_result, values_result, undefined] at value
      cases value
    · exact ⟨events, final, history, partition, failed⟩
  · rintro ⟨events, final, history, partition, failed⟩
    cases defined : evaluate policy memory expression with
    | none => rfl
    | some scalar =>
        exact False.elim (pure_failure_excludes_value policy memory expression pure events (represent final) history partition failed scalar defined)

theorem ResolvesExpression.fault_iff_undefined {policy : SignedConversionPolicy}
    {memory : ObjectAccessMemory.State model.characters} {arrays : ArrayPointers.Catalog}
    {scopes : List (FixedCore.Scope model)} {source : FixedCore.Expression model} {target : Expression model}
    (resolved : ResolvesExpression policy memory arrays scopes source target) :
    (∃ fault, FixedCore.evaluate model policy memory arrays scopes source = .fault fault) ↔
      FixedLocated.evaluate policy memory target = none := by
  rw [← resolved.evaluate]
  have integer := resolved.integer_result
  cases computed : FixedCore.evaluate model policy memory arrays scopes source with
  | fault reason => exact ⟨fun _ => rfl, fun _ => ⟨reason, rfl⟩⟩
  | value value =>
      cases value <;> simp_all [IntegerResult, observe]

theorem source_fault_iff_failed_history (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (target : Expression model)
    (resolved : ResolvesExpression policy memory arrays scopes source target) :
    (∃ fault, FixedCore.evaluate model policy memory arrays scopes source = .fault fault) ↔
    ∃ events final, SemanticHistory policy (compile target)
      (represent (initialState (compile target) memory)) events (represent final) ∧
      Partition (compile target) final.pending final.cache ∧ Failure policy (compile target) (represent final) :=
  resolved.fault_iff_undefined.trans (pure_failure_iff_undefined policy memory target resolved.pure)

theorem source_fault_iff_no_complete_history (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (target : Expression model)
    (resolved : ResolvesExpression policy memory arrays scopes source target) :
    (∃ fault, FixedCore.evaluate model policy memory arrays scopes source = .fault fault) ↔
    ¬ ∃ events final scalar, SemanticHistory policy (compile target)
      (represent (initialState (compile target) memory)) events final ∧
      LocatedStatements.CompleteExpression target final scalar := by
  rw [resolved.fault_iff_undefined]
  constructor
  · rintro undefined ⟨events, final, scalar, history, completed⟩
    have value := (source_boundary_no_invention policy memory arrays scopes source target resolved
      events final history scalar completed).1
    rw [resolved.evaluate, undefined] at value
    cases value
  · intro absent
    cases defined : evaluate policy memory target with
    | none => rfl
    | some scalar =>
        obtain ⟨events, final, history, completed, _⟩ := pure_complete_expression policy memory target
          resolved.pure scalar defined
        exact False.elim (absent ⟨events, final, scalar, history, completed⟩)

/-- Scheduler admission for the next actual occurrence. Missing choices are
allowed: they request interaction. Invalid or unready supplied choices are a
separate scheduling refusal, not source undefined behavior. -/
def LicensedNext : LocatedStatements.SemanticConfiguration model → Prop
  | .expression expression saved _ selections =>
      saved.halted = none → saved.pending ≠ [] → ∀ data rest, selections = data :: rest →
        ∃ index, LocatedExpressionData.decodeIndex expression data = some index ∧
          SequencingSchedule.Ready (compile expression).component.evaluation.order saved.pending index
  | _ => True

/-- A failed independent expression history has an actual finishing
verdict. The only extra selection names the refused ready occurrence; no
successful or pending execution is classified as a failure. -/
theorem failure_finishes (policy : SignedConversionPolicy) (expression : Expression model)
    (state : SemanticState (Index expression) model)
    (partition : Partition (compile expression) state.pending state.cache)
    (clean : ¬ (compile expression).component.evaluation.Undefined)
    (failed : Failure policy (compile expression) state)
    (continuation : LocatedStatements.AfterExpression model) :
    ∃ choices : List IndexData,
      (∀ rest, LicensedNext (.expression expression state continuation (choices ++ rest))) ∧
      ∀ rest (saved : LocatedStatements.Configuration model),
      LocatedStatements.represent saved = .expression expression state continuation (choices ++ rest) →
      ∃ verdict, (StatementMachine.machine model policy).step saved = some (.finish verdict) ∧
        verdictOutput verdict = none := by
  have conflict := ((compile expression).component.evaluation.findConflict_none_iff
    (compile expression).component.enumeration).mpr clean
  cases failed with
  | terminal index outcome halted recorded terminal =>
      refine ⟨[], ?_, ?_⟩
      · intro rest continuing
        change state.halted = none at continuing
        rw [halted] at continuing
        cases continuing
      intro rest saved represented
      cases saved <;> cases represented
      rename_i state
      exact ⟨_, StatementMachine.terminal_propagates policy expression state continuation rest index outcome
        conflict ((partitionCheck_iff _ _ _).mpr partition) halted terminal, rfl⟩
  | refused index continuing ready refused =>
      refine ⟨[encodeIndex expression index], ?_, ?_⟩
      · intro rest _ _ data tail same
        obtain ⟨rfl, rfl⟩ := List.cons.inj same
        exact ⟨index, LocatedExpressionData.decodeIndex_encode expression index, ready⟩
      intro rest saved represented
      cases saved <;> cases represented
      rename_i state
      change state.halted = none at continuing
      have operationNone : executeOperation model policy state.memory state.cache
          ((compile expression).operation index) = none := by
        cases computed : executeOperation model policy state.memory state.cache
            ((compile expression).operation index) with
        | none => rfl
        | some pair => exact False.elim (refused pair.1 (ObjectAccessMemory.represent pair.2)
            (executeOperation_sound _ _ _ _ _ _ _ computed))
      have nonempty : state.pending ≠ [] := by
        intro empty
        have present := ready.1
        simp only [represent, empty, List.not_mem_nil] at present
      have unfinished : StatementExecution.finishedExpression? expression state = none := by
        cases completed : StatementExecution.finishedExpression? expression state with
        | none => rfl
        | some scalar =>
            have drained := ((StatementExecution.finishedExpression_iff expression state scalar).mp completed).pending
            exact False.elim (nonempty drained)
      have notExecuted : execute policy (compile expression) state index = none := by
        cases selected : SequencingSchedule.select (compile expression).component.evaluation.order state.pending index <;>
          simp [execute, continuing, selected, operationNone]
      have notStepped : StatementExecution.execute policy
          (.expression expression state continuation (encodeIndex expression index :: rest)) = none := by
        simp only [StatementExecution.execute, unfinished, LocatedExpressionData.decodeIndex_encode,
          bind, Option.bind_some, notExecuted, Option.bind_none]
      refine ⟨.refused (.expression expression state continuation (encodeIndex expression index :: rest)), ?_, rfl⟩
      have checked : partitionCheck (compile expression) state.pending state.cache = true :=
        (partitionCheck_iff _ _ _).mpr partition
      simp only [List.singleton_append, StatementMachine.machine, notStepped, StatementMachine.classify,
        conflict, checked, ↓reduceIte, continuing]
      cases pending : state.pending with
      | nil => exact False.elim (nonempty pending)
      | cons first rest => rfl

/-- A finite located history ending in a completed refusal. Its endpoint
contains the exact diagnostic state; the shared observation only forgets the
first diagnostic. Neither fuel exhaustion nor a selection request qualifies. -/
def RefusalBlock (policy : SignedConversionPolicy)
    (before : List IndexData → LocatedStatements.SemanticConfiguration model) : Prop :=
  ∀ rest, ∃ choices events final,
    StatementHistory.History policy (before (choices ++ rest)) events final ∧
    LicensedNext final ∧
    ∀ saved : LocatedStatements.Configuration model, LocatedStatements.represent saved = final →
      ∃ verdict, (StatementMachine.machine model policy).step saved = some (.finish verdict) ∧
        verdictOutput verdict = none

theorem Block.then_refusal {policy : SignedConversionPolicy}
    {before middle : List IndexData → LocatedStatements.SemanticConfiguration model}
    (first : Block policy before middle) (last : RefusalBlock policy middle) : RefusalBlock policy before := by
  intro rest
  obtain ⟨lastChoices, lastEvents, final, tail, licensed, finishing⟩ := last rest
  obtain ⟨firstChoices, firstEvents, prefixHistory⟩ := first (lastChoices ++ rest)
  refine ⟨firstChoices ++ lastChoices, firstEvents ++ lastEvents, final, ?_, licensed, finishing⟩
  rw [List.append_assoc]
  exact StatementHistory.history_append _ _ _ _ _ _ prefixHistory tail

theorem failed_expression_block (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (expression : Expression model)
    (events : List (Occurrence (Index expression) model)) (final : SemanticState (Index expression) model)
    (history : SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) events final)
    (partition : Partition (compile expression) final.pending final.cache)
    (clean : ¬ (compile expression).component.evaluation.Undefined)
    (failed : Failure policy (compile expression) final)
    (continuation : LocatedStatements.AfterExpression model) :
    RefusalBlock policy (fun selections => .expression expression
      (LocatedStatements.sourceInitial expression (ObjectAccessMemory.represent memory)) continuation selections) := by
  obtain ⟨lastChoices, licensed, finishing⟩ := failure_finishes policy expression final partition clean failed continuation
  intro rest
  refine ⟨events.map (fun event => encodeIndex expression event.index) ++ lastChoices,
    events.map (fun event => some (.occurrence expression (encodeIndex expression event.index) event.outcome)),
    .expression expression final continuation (lastChoices ++ rest), ?_, licensed rest, finishing rest⟩
  rw [List.append_assoc]
  exact expression_history_in_statement policy expression _ _ _ history continuation (lastChoices ++ rest)

theorem source_expression_refusal_block (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (target : Expression model)
    (resolved : ResolvesExpression policy memory arrays scopes source target)
    (fault : FixedCore.Fault model)
    (undefined : FixedCore.evaluate model policy memory arrays scopes source = .fault fault)
    (continuation : LocatedStatements.AfterExpression model) :
    RefusalBlock policy (fun selections => .expression target
      (LocatedStatements.sourceInitial target (ObjectAccessMemory.represent memory)) continuation selections) := by
  obtain ⟨events, final, history, partition, failed⟩ :=
    (source_fault_iff_failed_history policy memory arrays scopes source target resolved).mp ⟨fault, undefined⟩
  exact failed_expression_block policy memory target events (represent final) history partition
    (readOnly_clean _ resolved.pure.readOnly) failed continuation

/-- A successful source assignment rules out every failed located schedule,
including schedules that publish the result before the store. The account
keeps the old memory until the unique store is consumed. -/
theorem assignment_failure_excludes_stored (policy : SignedConversionPolicy)
    (memory after : ObjectAccessMemory.State model.characters)
    (destination : Destination) (operand : Expression model) (pure : Pure operand)
    (input converted : IntegerScalar.Value model.parameters)
    (evaluated : evaluate policy memory operand = some input)
    (assigned : IntegerAssignment.Assigning model policy (ObjectAccessMemory.represent memory)
      destination.location input (.stored converted) (ObjectAccessMemory.represent after))
    (events : List (Occurrence (Index (.assignment destination operand)) model))
    (final : SemanticState (Index (.assignment destination operand)) model)
    (history : SemanticHistory policy (compile (.assignment destination operand))
      (represent (initialState (compile (.assignment destination operand)) memory)) events final)
    (partition : Partition (compile (.assignment destination operand)) final.pending final.cache) :
    ¬ Failure policy (compile (.assignment destination operand)) final := by
  have castPure : Pure (.cast destination.type operand) := .cast _ pure
  have conversion : IntegerScalar.CastEvaluation model.parameters policy destination.type input (.value converted) := by
    cases assigned with
    | stored after location input converted type formed cast writing =>
        have same : type = destination.type := by
          rw [destination.formed] at formed
          injection formed with same
          injection same with equal
          exact equal.symm
        subst type
        exact cast
  have writing : Writing model (ObjectAccessMemory.represent memory) (ObjectAccessMemory.represent after)
      destination.location converted := by cases assigned; assumption
  have castValue : evaluate policy memory (.cast destination.type operand) = some converted := by
    simp only [evaluate, evaluated, bind, Option.bind_some, IntegerScalar.cast_complete _ _ _ _ _ conversion,
      castOutcome, Outcome.scalar]
  let plan := compile (.cast destination.type operand)
  let assignedValues := values policy memory (.cast destination.type operand)
  have equations : ValueEquations policy plan memory assignedValues := castPure.equations policy memory
  have total : ∀ index, ∃ scalar, assignedValues index = some scalar := castPure.total policy memory castValue
  have rootValue : assignedValues plan.component.result = some converted := by
    simpa only [plan, assignedValues, compiled_result, values_result] using castValue
  have account := history.storeAccount castPure.readOnly equations
    (by simpa only [plan, compiled_result] using castPure.root_dominates)
    (StoreAccount.initial plan memory destination.location assignedValues)
  have allValues : ∀ index, ∃ scalar, storeValues plan assignedValues index = some scalar := by
    intro index
    cases index with
    | inl old => exact total old
    | inr fresh => exact ⟨converted, rootValue⟩
  intro failed
  cases failed with
  | terminal index outcome halted recorded terminal =>
      have same := account.cache index outcome recorded
      obtain ⟨scalar, value⟩ := allValues index
      rw [value] at same
      simp only [Outcome.terminal, same, Option.isNone_some, Bool.false_eq_true] at terminal
  | refused index continuing ready refused =>
      have available : ∀ source ∈ ((compile (.assignment destination operand)).operation index).inputs,
          lookupScalar final.cache source = storeValues plan assignedValues source := by
        intro source present
        exact account.cache.cached (ready_inputs_cached _ _ _ index partition
          (compiled_inputs_ordered _) ready source present)
      cases index with
      | inl old =>
          have unchanged := account.beforeStore (account.predecessors old ready.1)
          obtain ⟨scalar, value⟩ := total old
          have operationValueEq : operationValue policy memory (storeValues plan assignedValues)
              ((plan.operation old).map Sum.inl) = some scalar := by
            rw [operationValue_map]
            change operationValue policy memory assignedValues (plan.operation old) = some scalar
            exact (equations old).symm.trans value
          obtain ⟨outcome, computed, _⟩ := operationValue_realized policy memory
            (storeValues plan assignedValues) final.cache ((plan.operation old).map Sum.inl) scalar
            available operationValueEq
          apply refused outcome (ObjectAccessMemory.represent memory)
          rw [unchanged]
          exact executeOperation_sound _ _ _ _ _ _ _ computed
      | inr fresh =>
          have casesFresh : fresh = 0 ∨ fresh = 1 := by omega
          rcases casesFresh with rfl | rfl
          · have unchanged := account.beforeStore ready.1
            have cached : lookupScalar final.cache (.inl plan.component.result) = some converted :=
              (available _ (by simp [plan, compile, ExpressionPlanConstruction.storeResult, Operation.inputs])).trans rootValue
            apply refused (.stored converted) (ObjectAccessMemory.represent after)
            change OperationEvaluation model policy final.cache final.memory
              (.store destination.location (.inl plan.component.result)) (.stored converted)
              (ObjectAccessMemory.represent after)
            rw [unchanged]
            exact .store _ _ _ _ _ ((lookupScalar_iff _ _ _).mp cached) writing
          · have cached : lookupScalar final.cache (.inl plan.component.result) = some converted :=
              (available _ (by simp [plan, compile, ExpressionPlanConstruction.storeResult, Operation.inputs])).trans rootValue
            exact refused (.value converted) final.memory (.copy _ _ _ ((lookupScalar_iff _ _ _).mp cached))

theorem assignment_clean (destination : Destination) (operand : Expression model) (pure : Pure operand) :
    ¬ (compile (.assignment destination operand)).component.evaluation.Undefined :=
  storeResult_clean (compile (.cast destination.type operand)) destination.location (Pure.cast _ pure).readOnly
    (by simpa only [compiled_result] using (Pure.cast destination.type pure).root_dominates)

/-- Fixed assignment refusal constructs a failed actual located history;
operand, conversion and store failures are all covered by the same plan. -/
theorem source_assignment_fault_history (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice) (name : String) (source : FixedCore.Expression model)
    (destination : Destination) (operand : Expression model)
    (located : ResolvesExpression policy memory arrays scopes (.read (.named name)) (.load destination))
    (resolved : ResolvesExpression policy memory arrays scopes source operand)
    (before : FixedCore.Continuation model) (after : LocatedStatements.Continuation model)
    (continuation : ResolvesContinuation policy memory arrays scopes before after)
    (next : FixedCore.Executable model) (fault : FixedCore.Fault model)
    (stepped : FixedCore.step model policy abi program choice
      (fixedConfiguration memory arrays scopes heap (.execute (.assign (.named name) source)) before) = some next)
    (failed : next.status = .faulted fault) :
    ∃ events final, SemanticHistory policy (compile (.assignment destination operand))
      (represent (initialState (compile (.assignment destination operand)) memory)) events (represent final) ∧
      Partition (compile (.assignment destination operand)) final.pending final.cache ∧
      Failure policy (compile (.assignment destination operand)) (represent final) := by
  obtain ⟨events, final, history, partition, result⟩ := expression_complete_or_failure policy memory
    (.assignment destination operand) (assignment_clean destination operand resolved.pure)
  rcases result with ⟨scalar, complete⟩ | rejected
  · exact False.elim (faulted_assignment_has_no_complete_history policy memory arrays scopes heap abi program
      choice name source destination operand located resolved before after continuation next fault stepped failed
      events (represent final) history scalar complete)
  · exact ⟨events, final, history, partition, rejected⟩

/-- A rejected located assignment reflects to the real fixed-core step.
Reconciliation of the cast and store is derived from the independent memory
judgment, not assumed as a correspondence premise. -/
theorem source_assignment_failure_reflects (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice) (name : String) (source : FixedCore.Expression model)
    (destination : Destination) (operand : Expression model)
    (located : ResolvesExpression policy memory arrays scopes (.read (.named name)) (.load destination))
    (resolved : ResolvesExpression policy memory arrays scopes source operand)
    (before : FixedCore.Continuation model)
    (events : List (Occurrence (Index (.assignment destination operand)) model))
    (final : SemanticState (Index (.assignment destination operand)) model)
    (history : SemanticHistory policy (compile (.assignment destination operand))
      (represent (initialState (compile (.assignment destination operand)) memory)) events final)
    (partition : Partition (compile (.assignment destination operand)) final.pending final.cache)
    (failed : Failure policy (compile (.assignment destination operand)) final) :
    ∃ next fault, FixedCore.step model policy abi program choice
      (fixedConfiguration memory arrays scopes heap (.execute (.assign (.named name) source)) before) = some next ∧
      next.status = .faulted fault := by
  cases located with
  | read _ declared address range found typed inside =>
      have place : FixedCore.locate model policy memory arrays scopes (.named name) = .ok address := by
        simp only [FixedCore.locate, FixedCore.resolve_complete _ _ _ found, FixedCore.objectAddress, typed]
      cases evaluated : FixedCore.evaluate model policy memory arrays scopes source with
      | fault reason =>
          exact ⟨{fixedConfiguration memory arrays scopes heap (.execute (.assign (.named name) source)) before with status := .faulted reason}, reason, by simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
            place, evaluated, FixedCore.Configuration.fail], rfl⟩
      | value value =>
          cases value with
          | address other =>
              have impossible := resolved.integer_result
              simp only [evaluated, IntegerResult] at impossible
          | null =>
              have impossible := resolved.integer_result
              simp only [evaluated, IntegerResult] at impossible
          | integer input =>
              cases stored : FixedCore.storeElement model policy memory arrays address input with
              | fault reason =>
                  exact ⟨{fixedConfiguration memory arrays scopes heap (.execute (.assign (.named name) source)) before with status := .faulted reason}, reason, by simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
                    place, evaluated, stored, FixedCore.Configuration.fail], rfl⟩
              | done saved =>
                  have sourceStored := FixedCore.storeElement_sound model policy memory arrays address input
                  rw [stored] at sourceStored
                  cases sourceStored with
                  | stored other converted after inRange assigned =>
                      have same : other = range := Option.some.inj
                        (((ArrayPointers.elementRange_iff _ _ _ _).mpr inRange).symm.trans
                          ((ArrayPointers.elementRange_iff _ _ _ _).mpr inside))
                      subst other
                      exact False.elim (assignment_failure_excludes_stored policy memory saved _ operand resolved.pure
                        input converted (resolved.evaluate.symm.trans ((observe_some_iff _ _).mpr evaluated)) assigned
                        events final history partition failed)

/-- Every faulting step of an admitted fixed statement constructs a refused
located block, including operand, conversion and memory-write failures. -/
theorem statement_fault_simulation (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {source : FixedCore.Statement model} {target : LocatedStatements.Statement model}
    {before : FixedCore.Continuation model} {after : LocatedStatements.Continuation model}
    (resolved : ResolvesStatement policy memory arrays scopes source target)
    (continuation : ResolvesContinuation policy memory arrays scopes before after)
    (next : FixedCore.Executable model) (fault : FixedCore.Fault model)
    (stepped : FixedCore.step model policy abi program choice
      (fixedConfiguration memory arrays scopes heap (.execute source) before) = some next)
    (failed : next.status = .faulted fault) :
    RefusalBlock policy (fun selections => .statement target after (ObjectAccessMemory.represent memory) selections) := by
  cases resolved with
  | @assignment name source operand destination location value =>
      obtain ⟨events, final, history, partition, stopped⟩ := source_assignment_fault_history policy memory arrays scopes
        heap abi program choice name source destination operand location value before after continuation next fault stepped failed
      exact (block_administrative policy _ _ (fun _ => .expression _ _ _ _)).then_refusal
        (failed_expression_block policy memory (.assignment destination operand) events (represent final) history
          partition (assignment_clean destination operand value.pure) stopped (.discard after))
  | skip | sequence first second | breakLoop | continueLoop | returnEmpty =>
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith] at stepped
      cases stepped
      cases failed
  | @conditional condition test yes no left right expression first second =>
      have integer := expression.integer_result
      cases evaluated : FixedCore.evaluate model policy memory arrays scopes condition with
      | fault reason =>
          exact (block_administrative policy _ _ (fun _ => .conditional _ _ _ _ _ _)).then_refusal
            (source_expression_refusal_block policy memory arrays scopes condition test expression reason evaluated
              (.conditional left right after))
      | value value =>
          cases value with
          | address address | null => simp only [evaluated, IntegerResult] at integer
          | integer scalar =>
              simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, evaluated,
                FixedCore.Configuration.continueWith] at stepped
              cases stepped
              cases failed
  | @whileLoop condition test body target expression bodyResolved =>
      have integer := expression.integer_result
      cases evaluated : FixedCore.evaluate model policy memory arrays scopes condition with
      | fault reason =>
          exact (block_administrative policy _ _ (fun _ => .whileLoop _ _ _ _ _)).then_refusal
            (source_expression_refusal_block policy memory arrays scopes condition test expression reason evaluated
              (.whileCondition test target after))
      | value value =>
          cases value with
          | address address | null => simp only [evaluated, IntegerResult] at integer
          | integer scalar =>
              simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, evaluated,
                FixedCore.Configuration.continueWith] at stepped
              split at stepped <;> cases stepped <;> cases failed
  | @returnValue source target expression =>
      cases evaluated : FixedCore.evaluate model policy memory arrays scopes source with
      | fault reason =>
          exact (block_administrative policy _ _ (fun _ => .returnValue _ _ _ _)).then_refusal
            (source_expression_refusal_block policy memory arrays scopes source target expression reason evaluated .returnValue)
      | value value =>
          simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, evaluated,
            FixedCore.Configuration.continueWith] at stepped
          cases stepped
          cases failed

theorem control_fault_simulation (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {target : List IndexData → LocatedStatements.SemanticConfiguration model}
    (related : ControlRelated policy memory arrays scopes control following target)
    (next : FixedCore.Executable model) (fault : FixedCore.Fault model)
    (stepped : FixedCore.step model policy abi program choice
      (fixedConfiguration memory arrays scopes heap control following) = some next)
    (failed : next.status = .faulted fault) : RefusalBlock policy target := by
  cases related with
  | statement statement continuation =>
      exact statement_fault_simulation policy memory arrays scopes heap abi program choice
        statement continuation next fault stepped failed
  | @flow flow before after continuation =>
      cases continuation with
      | stop =>
          cases flow with
          | normal =>
              simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
                FixedCore.Configuration.continueWith] at stepped
              cases stepped
              cases failed
          | broken | continued =>
              intro rest
              refine ⟨[], [], _, .nil _, by trivial, ?_⟩
              intro saved represented
              cases saved with
              | statement _ _ _ _ | expression _ _ _ _ | returned _ _ _ => cases represented
              | flow actual following current choices =>
                  obtain ⟨rfl, rfl, _, rfl⟩ := LocatedStatements.State.flow.inj represented
                  exact ⟨_, rfl, rfl⟩
      | sequence statement continuation | loop expression statement continuation =>
          cases flow <;>
            simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
              FixedCore.Configuration.continueWith] at stepped <;>
            cases stepped <;> cases failed
  | @loopExpression condition test body target before after expression statement continuation =>
      have integer := expression.integer_result
      cases evaluated : FixedCore.evaluate model policy memory arrays scopes condition with
      | fault reason =>
          exact source_expression_refusal_block policy memory arrays scopes condition test expression reason evaluated
            (.whileCondition test target after)
      | value value =>
          cases value with
          | address address | null => simp only [evaluated, IntegerResult] at integer
          | integer scalar =>
              simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, evaluated,
                FixedCore.Configuration.continueWith] at stepped
              split at stepped <;> cases stepped <;> cases failed
  | returning result continuation =>
      cases continuation <;>
        simp only [fixedConfiguration, FixedCore.step, FixedCore.advance,
          FixedCore.Configuration.continueWith] at stepped <;>
        cases stepped <;> cases failed
  | fallthrough =>
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance] at stepped
      cases stepped
      cases failed

/-- Arbitrarily many admitted source steps, with intervening writes and loop
iterations, compose with the final faulting block. Earlier commits are retained. -/
theorem faulted_history_simulation (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {target : List IndexData → LocatedStatements.SemanticConfiguration model}
    (related : ControlRelated policy memory arrays scopes control following target)
    (before final : FixedCore.Executable model) (fault : FixedCore.Fault model)
    (history : Relation.ReflTransGen
      (fun before after => ∃ choice, FixedCore.step model policy abi program choice before = some after ∧
        after.status = .running)
      (fixedConfiguration memory arrays scopes heap control following) before)
    (choice : FixedCore.Choice)
    (last : FixedCore.step model policy abi program choice before = some final)
    (failed : final.status = .faulted fault) : RefusalBlock policy target := by
  obtain ⟨finalMemory, finalControl, finalFollowing, finalTarget, rfl, finalRelated, block⟩ :=
    running_history_simulation policy memory arrays scopes heap abi program related before history
  exact block.then_refusal (control_fault_simulation policy finalMemory arrays scopes heap abi program choice
    finalRelated final fault last failed)

/-- Realization exposes the last pending checkpoint separately from the
finishing refusal. Replaying the prefix retains the exact receipts and state. -/
theorem RefusalBlock.realization {policy : SignedConversionPolicy}
    {before : List IndexData → LocatedStatements.SemanticConfiguration model}
    (block : RefusalBlock policy before) (rest : List IndexData)
    (load : List IndexData → LocatedStatements.Configuration model)
    (represented : ∀ selections, LocatedStatements.represent (load selections) = before selections) :
    ∃ choices events saved receipts verdict,
      (StatementMachine.machine model policy).run events.length (load (choices ++ rest)) =
        (receipts, .exhausted saved) ∧
      (StatementMachine.machine model policy).run (events.length + 1) (load (choices ++ rest)) =
        (receipts, .finished verdict) ∧
      receipts.map StatementMachine.Receipt.event = (events : List (Option (LocatedStatements.Event model))).filterMap id ∧
      verdictOutput verdict = none := by
  obtain ⟨choices, events, final, history, _, finishing⟩ := block rest
  obtain ⟨saved, receipts, endpoint, executed, emissions⟩ :=
    StatementHistory.history_realization policy _ _ events history (load (choices ++ rest)) (represented _)
  obtain ⟨verdict, finish, observed⟩ := finishing saved endpoint
  refine ⟨choices, events, saved, receipts, verdict, executed, ?_, emissions, observed⟩
  rw [(StatementMachine.machine model policy).run_add, executed]
  simp only [Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine.continueRun,
    (StatementMachine.machine model policy).run_succ_finish (fuel := 0) finish, List.append_nil]

theorem source_expression_fault_runs (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (source : FixedCore.Expression model) (target : Expression model)
    (resolved : ResolvesExpression policy memory arrays scopes source target)
    (fault : FixedCore.Fault model)
    (undefined : FixedCore.evaluate model policy memory arrays scopes source = .fault fault)
    (continuation : LocatedStatements.AfterExpression model) (rest : List IndexData) :
    ∃ choices events saved receipts verdict,
      (StatementMachine.machine model policy).run events.length
        (.expression target (initialState (compile target) memory) continuation (choices ++ rest)) =
          (receipts, .exhausted saved) ∧
      (StatementMachine.machine model policy).run (events.length + 1)
        (.expression target (initialState (compile target) memory) continuation (choices ++ rest)) =
          (receipts, .finished verdict) ∧
      receipts.map StatementMachine.Receipt.event = (events : List (Option (LocatedStatements.Event model))).filterMap id ∧
      verdictOutput verdict = none := by
  exact (source_expression_refusal_block policy memory arrays scopes source target resolved fault undefined continuation).realization
    rest (fun choices => .expression target (initialState (compile target) memory) continuation choices) (fun _ => rfl)

/-- Failure at a retained conditional, loop test or return operand reflects
to that expression's owning fixed control step. The history may use any
licensed operand schedule. -/
theorem expression_failure_reflection (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {expression : Expression model} {continuation : LocatedStatements.AfterExpression model}
    (related : ExpressionControl policy memory arrays scopes control following expression continuation)
    (events : List (Occurrence (Index expression) model)) (saved : SemanticState (Index expression) model)
    (history : SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) events saved)
    (partition : Partition (compile expression) saved.pending saved.cache)
    (failed : Failure policy (compile expression) saved) :
    ∃ next fault, FixedCore.step model policy abi program choice
      (fixedConfiguration memory arrays scopes heap control following) = some next ∧
      next.status = .faulted fault := by
  have reflected {source : FixedCore.Expression model}
      (resolved : ResolvesExpression policy memory arrays scopes source expression) :
      ∃ fault, FixedCore.evaluate model policy memory arrays scopes source = .fault fault := by
    apply resolved.fault_iff_undefined.mpr
    cases computed : evaluate policy memory expression with
    | none => rfl
    | some scalar => exact False.elim (pure_failure_excludes_value policy memory expression resolved.pure
        events saved history partition failed scalar computed)
  cases related with
  | @conditional condition test yes no left right before after resolved onTrue onFalse continuation =>
      obtain ⟨fault, computed⟩ := reflected resolved
      refine ⟨{fixedConfiguration memory arrays scopes heap
        (.execute (.conditional condition yes no)) following with status := .faulted fault}, fault, ?_, rfl⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, computed, FixedCore.Configuration.fail]
  | @whileLoop condition test body next before after resolved statement continuation =>
      obtain ⟨fault, computed⟩ := reflected resolved
      refine ⟨{fixedConfiguration memory arrays scopes heap
        (.execute (.whileLoop condition body)) following with status := .faulted fault}, fault, ?_, rfl⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, computed, FixedCore.Configuration.fail]
  | @returnValue source target before after resolved continuation =>
      obtain ⟨fault, computed⟩ := reflected resolved
      refine ⟨{fixedConfiguration memory arrays scopes heap
        (.execute (.returnValue (some source))) following with status := .faulted fault}, fault, ?_, rfl⟩
      simp only [fixedConfiguration, FixedCore.step, FixedCore.advance, computed, FixedCore.Configuration.fail]

private theorem history_split (policy : SignedConversionPolicy)
    (before after : LocatedStatements.SemanticConfiguration model)
    (events : List (Option (LocatedStatements.Event model)))
    (history : StatementHistory.History policy before events after) (fuel : Nat) :
    ∃ middle, StatementHistory.History policy before (events.take fuel) middle ∧
      StatementHistory.History policy middle (events.drop fuel) after := by
  induction fuel generalizing before events with
  | zero => exact ⟨before, .nil _, history⟩
  | succ fuel ih =>
      cases history with
      | nil => exact ⟨after, .nil _, .nil _⟩
      | cons before next after event events stepped following =>
          obtain ⟨middle, first, last⟩ := ih next events following
          exact ⟨middle, .cons _ _ _ _ _ stepped first, last⟩

/-- A budget may stop anywhere inside a constructed control block. The
saved configuration is justified by the consumed source history and owns
exactly its unconsumed suffix, rather than an unevaluated restart. -/
theorem history_retained_split (policy : SignedConversionPolicy)
    (before after : LocatedStatements.SemanticConfiguration model)
    (events : List (Option (LocatedStatements.Event model)))
    (history : StatementHistory.History policy before events after) (fuel : Nat)
    (initial : LocatedStatements.Configuration model) (represented : LocatedStatements.represent initial = before) :
    ∃ middle final firstReceipts lastReceipts,
      StatementHistory.History policy before (events.take fuel) (LocatedStatements.represent middle) ∧
      StatementHistory.History policy (LocatedStatements.represent middle) (events.drop fuel) after ∧
      (StatementMachine.machine model policy).run (events.take fuel).length initial = (firstReceipts, .exhausted middle) ∧
      (StatementMachine.machine model policy).run (events.drop fuel).length middle = (lastReceipts, .exhausted final) ∧
      LocatedStatements.represent final = after ∧
      firstReceipts.map StatementMachine.Receipt.event = (events.take fuel).filterMap id ∧
      lastReceipts.map StatementMachine.Receipt.event = (events.drop fuel).filterMap id := by
  obtain ⟨boundary, first, last⟩ := history_split policy before after events history fuel
  obtain ⟨middle, firstReceipts, reached, firstRun, firstEvents⟩ :=
    StatementHistory.history_realization policy _ _ _ first initial represented
  obtain ⟨final, lastReceipts, finalRepr, lastRun, lastEvents⟩ :=
    StatementHistory.history_realization policy _ _ _ last middle reached
  exact ⟨middle, final, firstReceipts, lastReceipts, reached.symm ▸ first, reached.symm ▸ last,
    firstRun, lastRun, finalRepr, firstEvents, lastEvents⟩

theorem RefusalBlock.retained_realization {policy : SignedConversionPolicy}
    {before : List IndexData → LocatedStatements.SemanticConfiguration model}
    (block : RefusalBlock policy before) (rest : List IndexData)
    (load : List IndexData → LocatedStatements.Configuration model)
    (represented : ∀ selections, LocatedStatements.represent (load selections) = before selections)
    (fuel : Nat) :
    ∃ choices, ∃ events : List (Option (LocatedStatements.Event model)),
      ∃ middle final firstReceipts lastReceipts verdict,
      StatementHistory.History policy (before (choices ++ rest)) (events.take fuel)
        (LocatedStatements.represent middle) ∧
      (StatementMachine.machine model policy).run (events.take fuel).length (load (choices ++ rest)) =
        (firstReceipts, .exhausted middle) ∧
      (StatementMachine.machine model policy).run ((events.drop fuel).length + 1) middle =
        (lastReceipts, .finished verdict) ∧
      (StatementMachine.machine model policy).run events.length (load (choices ++ rest)) =
        (firstReceipts ++ lastReceipts, .exhausted final) ∧
      firstReceipts.map StatementMachine.Receipt.event = (events.take fuel).filterMap id ∧
      lastReceipts.map StatementMachine.Receipt.event = (events.drop fuel).filterMap id ∧
      verdictOutput verdict = none := by
  obtain ⟨choices, events, endpoint, history, _, finishing⟩ := block rest
  obtain ⟨middle, final, firstReceipts, lastReceipts, firstHistory, _, firstRun, lastRun, finalRepr,
    firstEvents, lastEvents⟩ := history_retained_split policy _ _ events history fuel
      (load (choices ++ rest)) (represented _)
  obtain ⟨verdict, finished, rejected⟩ := finishing final finalRepr
  refine ⟨choices, events, middle, final, firstReceipts, lastReceipts, verdict,
    firstHistory, firstRun, ?_, ?_, firstEvents, lastEvents, rejected⟩
  · rw [(StatementMachine.machine model policy).run_add, lastRun]
    simp only [Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine.continueRun,
      (StatementMachine.machine model policy).run_succ_finish (fuel := 0) finished, List.append_nil]
  · have length : events.length = (events.take fuel).length + (events.drop fuel).length := by
      rw [← List.length_append, List.take_append_drop]
    rw [length, (StatementMachine.machine model policy).run_add, firstRun]
    simp only [Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine.continueRun, lastRun]

/-- A finishing executable expression with an earned cache and a licensed
next scheduler choice is a genuine primitive failure. Malformed or unready
choice packets are deliberately outside this statement. -/
theorem expression_finished_reflects_failure (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (expression : Expression model)
    (events : List (Occurrence (Index expression) model)) (state : State (Index expression) model)
    (history : SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) events (represent state))
    (clean : ¬ (compile expression).component.evaluation.Undefined)
    (continuation : LocatedStatements.AfterExpression model) (selections : List IndexData)
    (licensed : state.halted = none → state.pending ≠ [] → ∀ data rest, selections = data :: rest →
      ∃ index, LocatedExpressionData.decodeIndex expression data = some index ∧
        SequencingSchedule.Ready (compile expression).component.evaluation.order state.pending index)
    (verdict : StatementMachine.Verdict model)
    (finished : (StatementMachine.machine model policy).step (.expression expression state continuation selections) =
      some (.finish verdict)) : Failure policy (compile expression) (represent state) := by
  have partition := history.partition (initial_partition (compile expression) memory)
  have conflict := ((compile expression).component.evaluation.findConflict_none_iff
    (compile expression).component.enumeration).mpr clean
  have checked : partitionCheck (compile expression) state.pending state.cache = true := (partitionCheck_iff _ _ _).mpr partition
  cases halted : state.halted with
  | some pair =>
      obtain ⟨index, outcome⟩ := pair
      obtain ⟨recorded, terminal⟩ := history.halted_recorded index outcome halted
      exact .terminal index outcome halted recorded terminal
  | none =>
      by_cases empty : state.pending = []
      · have present := partition.2 (result expression) ((compile expression).component.enumeration.complete _)
        change result expression ∈ state.pending ∨ _ at present
        rw [empty] at present
        obtain ⟨outcome, found⟩ := lookup_exists_of_key state.cache _ (present.resolve_left (by simp))
        obtain ⟨scalar, value⟩ := history.unhalted_scalar_cache halted _ _ found
        have complete : LocatedStatements.CompleteExpression expression (represent state) scalar :=
          ⟨partition, empty, halted,
            fun undefined => clean ((ExpressionSourceExecution.compiled_conflict_iff _).mpr undefined),
            by simp only [represent, lookupScalar, found, Option.bind_some, value]⟩
        have completed := (StatementExecution.finishedExpression_iff expression state scalar).mpr complete
        simp only [StatementMachine.machine, StatementExecution.execute, completed] at finished
        cases finished
      · have unfinished : StatementExecution.finishedExpression? expression state = none := by
          cases computed : StatementExecution.finishedExpression? expression state with
          | none => rfl
          | some scalar => exact False.elim (empty ((StatementExecution.finishedExpression_iff _ _ _).mp computed).pending)
        cases selections with
        | nil =>
            simp only [StatementMachine.machine, StatementExecution.execute, unfinished, StatementMachine.classify,
              conflict, checked, ↓reduceIte, halted] at finished
            cases pending : state.pending with
            | nil => exact False.elim (empty pending)
            | cons first rest => simp only [pending] at finished; cases finished
        | cons data rest =>
            obtain ⟨index, decoded, ready⟩ := licensed halted empty data rest rfl
            cases operated : executeOperation model policy state.memory state.cache ((compile expression).operation index) with
            | none =>
                refine .refused index halted ready ?_
                intro outcome after operation
                obtain ⟨saved, computed, _⟩ := executeOperation_complete model policy state.memory after state.cache
                  ((compile expression).operation index) outcome operation
                rw [operated] at computed
                cases computed
            | some pair =>
                obtain ⟨outcome, memory⟩ := pair
                let after : State (Index expression) model :=
                  ⟨state.pending.erase index, memory, (index, outcome) :: state.cache, haltAfter index outcome⟩
                have step : Reduction policy (compile expression) (represent state) index outcome (represent after) :=
                  .execute _ _ _ _ partition halted clean
                    (.consume _ _ _ ready (SequencingSchedule.removal_erase index state.pending ready.1))
                    (executeOperation_sound _ _ _ _ _ _ _ operated) rfl rfl
                obtain ⟨next, advanced, _⟩ := execute_complete policy (compile expression) state _ index outcome step
                simp only [StatementMachine.machine, StatementExecution.execute, unfinished, decoded,
                  bind, Option.bind_some, advanced] at finished
                cases finished

/-- The pending control carries the actual admitted pure source operand. -/
theorem ExpressionControl.pure {policy : SignedConversionPolicy}
    {memory : ObjectAccessMemory.State model.characters} {arrays : ArrayPointers.Catalog}
    {scopes : List (FixedCore.Scope model)}
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {expression : Expression model} {continuation : LocatedStatements.AfterExpression model}
    (related : ExpressionControl policy memory arrays scopes control following expression continuation) :
    Pure expression := by
  cases related with
  | conditional resolved _ _ _ => exact resolved.pure
  | whileLoop resolved _ _ => exact resolved.pure
  | returnValue resolved _ => exact resolved.pure

/-- A completed machine refusal at an earned conditional, loop test or return
operand reflects to the actual owning source step. The scheduler admission
only validates the next selected occurrence; it assumes no evaluation result. -/
theorem expression_finished_source_fault (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {expression : Expression model} {continuation : LocatedStatements.AfterExpression model}
    (related : ExpressionControl policy memory arrays scopes control following expression continuation)
    (events : List (Occurrence (Index expression) model)) (saved : State (Index expression) model)
    (history : SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) events (represent saved))
    (selections : List IndexData)
    (licensed : saved.halted = none → saved.pending ≠ [] → ∀ data rest, selections = data :: rest →
      ∃ index, LocatedExpressionData.decodeIndex expression data = some index ∧
        SequencingSchedule.Ready (compile expression).component.evaluation.order saved.pending index)
    (verdict : StatementMachine.Verdict model)
    (finished : (StatementMachine.machine model policy).step (.expression expression saved continuation selections) =
      some (.finish verdict)) :
    ∃ next fault, FixedCore.step model policy abi program choice
      (fixedConfiguration memory arrays scopes heap control following) = some next ∧
      next.status = .faulted fault := by
  exact expression_failure_reflection policy memory arrays scopes heap abi program choice related
    events (represent saved) history (history.partition (initial_partition (compile expression) memory))
    (expression_finished_reflects_failure policy memory expression events saved history
      (readOnly_clean _ related.pure.readOnly) continuation selections licensed verdict finished)

/-- Actual assignment refusal reflects to the source store/cast computation,
including result-before-store schedules and memory-access refusal. -/
theorem assignment_finished_source_fault (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice) (name : String) (source : FixedCore.Expression model)
    (destination : Destination) (operand : Expression model)
    (located : ResolvesExpression policy memory arrays scopes (.read (.named name)) (.load destination))
    (resolved : ResolvesExpression policy memory arrays scopes source operand)
    (before : FixedCore.Continuation model) (continuation : LocatedStatements.AfterExpression model)
    (events : List (Occurrence (Index (.assignment destination operand)) model))
    (saved : State (Index (.assignment destination operand)) model)
    (history : SemanticHistory policy (compile (.assignment destination operand))
      (represent (initialState (compile (.assignment destination operand)) memory)) events (represent saved))
    (selections : List IndexData)
    (licensed : saved.halted = none → saved.pending ≠ [] → ∀ data rest, selections = data :: rest →
      ∃ index, LocatedExpressionData.decodeIndex (.assignment destination operand) data = some index ∧
        SequencingSchedule.Ready (compile (.assignment destination operand)).component.evaluation.order saved.pending index)
    (verdict : StatementMachine.Verdict model)
    (finished : (StatementMachine.machine model policy).step
      (.expression (.assignment destination operand) saved continuation selections) = some (.finish verdict)) :
    ∃ next fault, FixedCore.step model policy abi program choice
      (fixedConfiguration memory arrays scopes heap (.execute (.assign (.named name) source)) before) = some next ∧
      next.status = .faulted fault := by
  exact source_assignment_failure_reflects policy memory arrays scopes heap abi program choice
    name source destination operand located resolved before events (represent saved) history
    (history.partition (initial_partition (compile (.assignment destination operand)) memory))
    (expression_finished_reflects_failure policy memory (.assignment destination operand) events saved history
      (assignment_clean destination operand resolved.pure) continuation selections licensed verdict finished)

end FaultAndPending

section ReachedControlExecution
open IntegerMemoryModel LocatedExpressions ExpressionEvents ExpressionEventExecution ExpressionEventHistory
open LocatedExpressionData (IndexData)
variable {model : Model}

/-- Pending occurrence work, including the administrative entry into an
expression. Control steps outside expressions are matched by source steps. -/
def workRank : LocatedStatements.SemanticConfiguration model → Nat
  | .statement statement _ _ _ => match statement with
    | .expression operand | .conditional operand _ _ | .whileLoop operand _
      | .returnValue (some operand) => (compile operand).component.enumeration.items.dedup.length + 2
    | _ => 0
  | .expression _ saved _ _ => saved.pending.length + 1
  | _ => 0

/-- An earned control position retains the fixed source that owns a pending
expression, together with its actual partial occurrence history. Assignments
keep their original memory until the completed store boundary is reflected. -/
inductive ReachedControl (policy : SignedConversionPolicy) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId) :
    FixedCore.Executable model → LocatedStatements.SemanticConfiguration model → Prop where
  | boundary {memory : ObjectAccessMemory.State model.characters}
      {control : FixedCore.Control model} {following : FixedCore.Continuation model}
      {target : List IndexData → LocatedStatements.SemanticConfiguration model}
      (related : ControlRelated policy memory arrays scopes control following target)
      (selections : List IndexData) :
      ReachedControl policy arrays scopes heap
        (fixedConfiguration memory arrays scopes heap control following) (target selections)
  | expression {memory : ObjectAccessMemory.State model.characters}
      {control : FixedCore.Control model} {following : FixedCore.Continuation model}
      {expression : Expression model} {continuation : LocatedStatements.AfterExpression model}
      (owner : ExpressionControl policy memory arrays scopes control following expression continuation)
      (events : List (Occurrence (Index expression) model))
      (saved : SemanticState (Index expression) model)
      (history : SemanticHistory policy (compile expression)
        (represent (initialState (compile expression) memory)) events saved)
      (selections : List IndexData) :
      ReachedControl policy arrays scopes heap
        (fixedConfiguration memory arrays scopes heap control following)
        (.expression expression saved continuation selections)
  | assignment {memory : ObjectAccessMemory.State model.characters}
      (name : String) (source : FixedCore.Expression model) (destination : Destination) (operand : Expression model)
      (location : ResolvesExpression policy memory arrays scopes (.read (.named name)) (.load destination))
      (resolved : ResolvesExpression policy memory arrays scopes source operand)
      {following : FixedCore.Continuation model} {continuation : LocatedStatements.Continuation model}
      (owner : ResolvesContinuation policy memory arrays scopes following continuation)
      (events : List (Occurrence (Index (.assignment destination operand)) model))
      (saved : SemanticState (Index (.assignment destination operand)) model)
      (history : SemanticHistory policy (compile (.assignment destination operand))
        (represent (initialState (compile (.assignment destination operand)) memory)) events saved)
      (selections : List IndexData) :
      ReachedControl policy arrays scopes heap
        (fixedConfiguration memory arrays scopes heap (.execute (.assign (.named name) source)) following)
        (.expression (.assignment destination operand) saved (.discard continuation) selections)

def SourceRunningStep (policy : SignedConversionPolicy)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (before after : FixedCore.Executable model) : Prop :=
  ∃ choice, FixedCore.step model policy abi program choice before = some after ∧ after.status = .running

/-- Each discovered segment either performs a real source step or consumes
strictly smaller pending expression work without advancing that source. -/
def ReverseProgress (policy : SignedConversionPolicy)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (before after : FixedCore.Executable model)
    (left right : LocatedStatements.SemanticConfiguration model) : Prop :=
  (after = before ∧ workRank right < workRank left) ∨ SourceRunningStep policy abi program before after

private theorem occurrence_progress (policy : SignedConversionPolicy) (expression : Expression model)
    {before after : SemanticState (Index expression) model} {index : Index expression} {outcome : Outcome model}
    (step : ExpressionSourceExecution.Advance policy expression before index outcome after) :
    after.pending.length < before.pending.length := by
  cases step with
  | execute _ _ _ _ _ _ _ _ removed _ _ _ _ =>
      have consumed := removed.length
      omega

private theorem pending_expression_reverse (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {memory : ObjectAccessMemory.State model.characters}
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {expression : Expression model} {continuation : LocatedStatements.AfterExpression model}
    (owner : ExpressionControl policy memory arrays scopes control following expression continuation)
    (events : List (Occurrence (Index expression) model)) (saved : SemanticState (Index expression) model)
    (history : SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) events saved)
    (selections : List IndexData) {event : Option (LocatedStatements.Event model)}
    {target : LocatedStatements.SemanticConfiguration model}
    (step : StatementSemantics.Step policy (.expression expression saved continuation selections) event target) :
    ∃ next, ReachedControl policy arrays scopes heap next target ∧
      ReverseProgress policy abi program (fixedConfiguration memory arrays scopes heap control following) next
        (.expression expression saved continuation selections) target := by
  cases step with
  | administrative _ _ stepped => cases stepped
  | iteration _ _ _ stepped => cases stepped
  | occurrence expression before after continuation data rest index outcome decoded advanced =>
      have reduced := (ExpressionSourceExecution.reduction_iff _ _ _ _ _ _).mpr advanced
      have later := history.append (.cons _ _ _ ⟨index, outcome⟩ [] reduced (.nil _))
      exact ⟨_, .expression owner _ after later rest, Or.inl ⟨rfl, by
        simpa only [workRank, Nat.add_lt_add_iff_right] using occurrence_progress policy expression advanced⟩⟩
  | boundary expression saved continuation selections scalar completed target continued =>
      obtain ⟨newControl, newFollowing, newTarget, actual, related, endpoint, _⟩ :=
        expression_boundary_reflection policy memory arrays scopes heap abi program choice owner
          events saved history scalar completed selections target continued
      exact ⟨_, endpoint ▸ ReachedControl.boundary related selections, Or.inr ⟨choice, actual, rfl⟩⟩

private theorem pending_assignment_reverse (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {memory : ObjectAccessMemory.State model.characters}
    (name : String) (source : FixedCore.Expression model) (destination : Destination) (operand : Expression model)
    (location : ResolvesExpression policy memory arrays scopes (.read (.named name)) (.load destination))
    (resolved : ResolvesExpression policy memory arrays scopes source operand)
    {following : FixedCore.Continuation model} {continuation : LocatedStatements.Continuation model}
    (owner : ResolvesContinuation policy memory arrays scopes following continuation)
    (events : List (Occurrence (Index (.assignment destination operand)) model))
    (saved : SemanticState (Index (.assignment destination operand)) model)
    (history : SemanticHistory policy (compile (.assignment destination operand))
      (represent (initialState (compile (.assignment destination operand)) memory)) events saved)
    (selections : List IndexData) {event : Option (LocatedStatements.Event model)}
    {target : LocatedStatements.SemanticConfiguration model}
    (step : StatementSemantics.Step policy (.expression (.assignment destination operand) saved (.discard continuation) selections)
      event target) :
    ∃ next, ReachedControl policy arrays scopes heap next target ∧
      ReverseProgress policy abi program
        (fixedConfiguration memory arrays scopes heap (.execute (.assign (.named name) source)) following) next
        (.expression (.assignment destination operand) saved (.discard continuation) selections) target := by
  cases step with
  | administrative _ _ stepped => cases stepped
  | iteration _ _ _ stepped => cases stepped
  | occurrence expression before after continuation data rest index outcome decoded advanced =>
      have reduced := (ExpressionSourceExecution.reduction_iff _ _ _ _ _ _).mpr advanced
      have later := history.append (.cons _ _ _ ⟨index, outcome⟩ [] reduced (.nil _))
      exact ⟨_, .assignment name source destination operand location resolved owner _ after later rest,
        Or.inl ⟨rfl, by simpa only [workRank, Nat.add_lt_add_iff_right] using occurrence_progress policy (.assignment destination operand) advanced⟩⟩
  | boundary expression saved after selections scalar completed target continued =>
      obtain ⟨memory', actual, represented, following'⟩ := assignment_boundary_reflection policy memory arrays scopes heap
        abi program choice name source destination operand location resolved following continuation owner events saved history scalar completed
      cases continued with
      | discard _ same =>
          cases same
          refine ⟨_, ?_, Or.inr ⟨choice, actual, rfl⟩⟩
          rw [← represented]
          exact .boundary (.flow .normal following') selections
      | conditional _ _ _ _ same _ => cases same
      | whileCondition _ _ _ _ same _ => cases same
      | doCondition _ _ _ _ same _ => cases same
      | forInitial _ _ _ _ same _ _ => cases same
      | forCondition _ _ _ _ _ same _ => cases same
      | forIncrement _ _ _ _ same _ _ => cases same
      | returnValue same => cases same


private theorem starting_statement_reverse (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {memory : ObjectAccessMemory.State model.characters}
    {source : FixedCore.Statement model} {statement : LocatedStatements.Statement model}
    {following : FixedCore.Continuation model} {continuation : LocatedStatements.Continuation model}
    (related : ResolvesStatement policy memory arrays scopes source statement)
    (owner : ResolvesContinuation policy memory arrays scopes following continuation)
    (selections : List IndexData) {event : Option (LocatedStatements.Event model)}
    {target : LocatedStatements.SemanticConfiguration model}
    (step : StatementSemantics.Step policy (.statement statement continuation (ObjectAccessMemory.represent memory) selections)
      event target) :
    ∃ next, ReachedControl policy arrays scopes heap next target ∧
      ReverseProgress policy abi program
        (fixedConfiguration memory arrays scopes heap (.execute source) following) next
        (.statement statement continuation (ObjectAccessMemory.represent memory) selections) target := by
  cases step with
  | iteration _ _ _ iterated => cases iterated
  | administrative _ _ admin =>
      cases related with
      | assignment name location resolved =>
          cases admin
          exact ⟨_, .assignment name _ _ _ location resolved owner [] _ (.nil _) selections,
            Or.inl ⟨rfl, by simp [workRank, LocatedStatements.sourceInitial]⟩⟩
      | skip =>
          cases admin
          exact ⟨_, .boundary (.flow .normal owner) selections, Or.inr ⟨choice, by
            simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith], rfl⟩⟩
      | sequence first second =>
          cases admin
          exact ⟨_, .boundary (.statement first (.sequence second owner)) selections, Or.inr ⟨choice, by
            simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith], rfl⟩⟩
      | conditional resolved yes no =>
          cases admin
          exact ⟨_, .expression (.conditional resolved yes no owner) [] _ (.nil _) selections,
            Or.inl ⟨rfl, by simp [workRank, LocatedStatements.sourceInitial]⟩⟩
      | whileLoop resolved body =>
          cases admin
          exact ⟨_, .expression (.whileLoop resolved body owner) [] _ (.nil _) selections,
            Or.inl ⟨rfl, by simp [workRank, LocatedStatements.sourceInitial]⟩⟩
      | breakLoop =>
          cases admin
          exact ⟨_, .boundary (.flow .broken owner) selections, Or.inr ⟨choice, by
            simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith], rfl⟩⟩
      | continueLoop =>
          cases admin
          exact ⟨_, .boundary (.flow .continued owner) selections, Or.inr ⟨choice, by
            simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith], rfl⟩⟩
      | returnEmpty =>
          cases admin
          exact ⟨_, .boundary (.returning none owner) selections, Or.inr ⟨choice, by
            simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith, scalarReturn], rfl⟩⟩
      | returnValue resolved =>
          cases admin
          exact ⟨_, .expression (.returnValue resolved owner) [] _ (.nil _) selections,
            Or.inl ⟨rfl, by simp [workRank, LocatedStatements.sourceInitial]⟩⟩


private theorem flow_reverse (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {memory : ObjectAccessMemory.State model.characters}
    (flow : FixedCore.Flow)
    {following : FixedCore.Continuation model} {continuation : LocatedStatements.Continuation model}
    (owner : ResolvesContinuation policy memory arrays scopes following continuation)
    (selections : List IndexData) {event : Option (LocatedStatements.Event model)}
    {target : LocatedStatements.SemanticConfiguration model}
    (step : StatementSemantics.Step policy (.flow (lowerFlow flow) continuation (ObjectAccessMemory.represent memory) selections)
      event target) :
    ∃ next, ReachedControl policy arrays scopes heap next target ∧
      ReverseProgress policy abi program
        (fixedConfiguration memory arrays scopes heap (.flow flow) following) next
        (.flow (lowerFlow flow) continuation (ObjectAccessMemory.represent memory) selections) target := by
  cases owner with
  | stop =>
      cases flow <;> cases step with
      | administrative _ _ admin => cases admin
      | iteration _ _ _ iterated => cases iterated
  | sequence statement owner =>
      cases flow with
      | normal =>
          cases step with
          | iteration _ _ _ iterated => cases iterated
          | administrative _ _ admin =>
              cases admin
              exact ⟨_, .boundary (.statement statement owner) selections, Or.inr ⟨choice, by
                simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith], rfl⟩⟩
      | broken =>
          cases step with
          | iteration _ _ _ iterated => cases iterated
          | administrative _ _ admin =>
              cases admin
              exact ⟨_, .boundary (.flow .broken owner) selections, Or.inr ⟨choice, by
                simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith], rfl⟩⟩
      | continued =>
          cases step with
          | iteration _ _ _ iterated => cases iterated
          | administrative _ _ admin =>
              cases admin
              exact ⟨_, .boundary (.flow .continued owner) selections, Or.inr ⟨choice, by
                simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith], rfl⟩⟩
  | loop expression statement owner =>
      cases flow with
      | normal =>
          cases step with
          | administrative _ _ admin => cases admin
          | iteration _ _ _ iterated =>
              cases iterated
              exact ⟨_, .boundary (.loopExpression expression statement owner) selections, Or.inr ⟨choice, by
                simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith], rfl⟩⟩
      | broken =>
          cases step with
          | administrative _ _ admin =>
              cases admin
              exact ⟨_, .boundary (.flow .normal owner) selections, Or.inr ⟨choice, by
                simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith], rfl⟩⟩
          | iteration _ _ _ iterated => cases iterated with
              | whileLoop _ restart _ _ _ _ _ => cases restart
      | continued =>
          cases step with
          | administrative _ _ admin => cases admin
          | iteration _ _ _ iterated =>
              cases iterated
              exact ⟨_, .boundary (.loopExpression expression statement owner) selections, Or.inr ⟨choice, by
                simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith], rfl⟩⟩

/-- A located step from an earned state discovers its own source segment.
No whole-run decomposition is supplied by the caller. -/
theorem ReachedControl.step (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {source : FixedCore.Executable model} {before after : LocatedStatements.SemanticConfiguration model}
    (related : ReachedControl policy arrays scopes heap source before)
    (event : Option (LocatedStatements.Event model)) (step : StatementSemantics.Step policy before event after) :
    ∃ next, ReachedControl policy arrays scopes heap next after ∧
      ReverseProgress policy abi program source next before after := by
  cases related with
  | boundary related selections =>
      cases related with
      | statement statement continuation =>
          exact starting_statement_reverse policy arrays scopes heap abi program choice statement continuation selections step
      | flow flow continuation =>
          exact flow_reverse policy arrays scopes heap abi program choice flow continuation selections step
      | loopExpression expression statement continuation =>
          exact pending_expression_reverse policy arrays scopes heap abi program choice
            (.whileLoop expression statement continuation) [] _ (.nil _) selections step
      | returning value continuation =>
          cases step with
          | administrative _ _ admin => cases admin
          | iteration _ _ _ iterated => cases iterated
      | fallthrough =>
          cases step with
          | administrative _ _ admin => cases admin
          | iteration _ _ _ iterated => cases iterated
  | expression owner events saved history selections =>
      exact pending_expression_reverse policy arrays scopes heap abi program choice owner events saved history selections step
  | assignment name source destination operand location resolved owner events saved history selections =>
      exact pending_assignment_reverse policy arrays scopes heap abi program choice
        name source destination operand location resolved owner events saved history selections step

/-- Every arbitrary reached located history reconstructs an actual fixed
history and retains its current owning source control. -/
theorem ReachedControl.history (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    {source : FixedCore.Executable model} {before after : LocatedStatements.SemanticConfiguration model}
    (related : ReachedControl policy arrays scopes heap source before)
    (events : List (Option (LocatedStatements.Event model)))
    (history : StatementHistory.History policy before events after) :
    ∃ final, Relation.ReflTransGen (SourceRunningStep policy abi program) source final ∧
      ReachedControl policy arrays scopes heap final after := by
  induction history generalizing source with
  | nil => exact ⟨source, .refl, related⟩
  | cons before middle after event events stepped following ih =>
      obtain ⟨next, reached, progress⟩ := related.step policy arrays scopes heap abi program
        (FixedCore.canonicalChoice model source) event stepped
      obtain ⟨final, tail, result⟩ := ih reached
      refine ⟨final, ?_, result⟩
      rcases progress with ⟨rfl, _⟩ | actual
      · exact tail
      · exact (Relation.ReflTransGen.single actual).trans tail


theorem ReachedControl.running {policy : SignedConversionPolicy} {arrays : ArrayPointers.Catalog}
    {scopes : List (FixedCore.Scope model)} {heap : List Mettapedia.Machines.CMemory.BlockId}
    {source : FixedCore.Executable model} {target : LocatedStatements.SemanticConfiguration model}
    (related : ReachedControl policy arrays scopes heap source target) : source.status = .running := by
  cases related <;> rfl

/-- The rank used by reverse simulation is well founded. A source loop must
therefore contribute real source progress; it cannot be hidden in endless
expression administration. -/
theorem workRank_wellFounded : WellFounded (fun after before : LocatedStatements.SemanticConfiguration model =>
    workRank after < workRank before) := (measure workRank).wf

/-- Every actual exhausted prefix discovers an owning source control and
preserves the exact chronological located receipt occurrences. -/
theorem ReachedControl.exhausted (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    {source : FixedCore.Executable model} (initial saved : LocatedStatements.Configuration model)
    (related : ReachedControl policy arrays scopes heap source (LocatedStatements.represent initial))
    (fuel : Nat) (receipts : List (StatementMachine.Receipt model))
    (paused : (StatementMachine.machine model policy).run fuel initial = (receipts, .exhausted saved)) :
    ∃ final events, Relation.ReflTransGen (SourceRunningStep policy abi program) source final ∧
      ReachedControl policy arrays scopes heap final (LocatedStatements.represent saved) ∧
      StatementHistory.History policy (LocatedStatements.represent initial) events (LocatedStatements.represent saved) ∧
      events.length = fuel ∧ receipts.map StatementMachine.Receipt.event = events.filterMap id := by
  obtain ⟨events, history, length, observations⟩ := StatementHistory.exhausted_has_source_history policy fuel initial saved receipts paused
  obtain ⟨final, sourceHistory, endpoint⟩ := related.history policy arrays scopes heap abi program events history
  exact ⟨final, events, sourceHistory, endpoint, history, length, observations⟩

/-- The common completed observer keeps values, while coarsening the choice
of first fault. Budget and interaction outcomes are not completed observers. -/
def TerminalAgrees (observation : Option (Option (IntegerScalar.Value model.parameters)))
    (source : FixedCore.Executable model) : Prop :=
  match observation with
  | some result => source.status = .finished (scalarReturn result)
  | none => ∃ reason, source.status = .faulted reason

def ReachesTerminal (policy : SignedConversionPolicy)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (source : FixedCore.Executable model) (observation : Option (Option (IntegerScalar.Value model.parameters))) : Prop :=
  ∃ before after, Relation.ReflTransGen (SourceRunningStep policy abi program) source before ∧
    ∃ choice, FixedCore.step model policy abi program choice before = some after ∧ TerminalAgrees observation after

theorem ReachesTerminal.prepend {policy : SignedConversionPolicy}
    {abi : IntegerType IntegerExtension → ObjectLayout.Layout} {program : FixedCore.Program model}
    {source before : FixedCore.Executable model} {observation : Option (Option (IntegerScalar.Value model.parameters))}
    (history : Relation.ReflTransGen (SourceRunningStep policy abi program) source before)
    (terminal : ReachesTerminal policy abi program before observation) : ReachesTerminal policy abi program source observation := by
  obtain ⟨middle, after, suffix, choice, stepped, observed⟩ := terminal
  exact ⟨middle, after, history.trans suffix, choice, stepped, observed⟩

private theorem returning_reaches_terminal (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice) (memory : ObjectAccessMemory.State model.characters)
    (result : Option (IntegerScalar.Value model.parameters))
    {following : FixedCore.Continuation model} {continuation : LocatedStatements.Continuation model}
    (owner : ResolvesContinuation policy memory arrays scopes following continuation) :
    ReachesTerminal policy abi program
      (fixedConfiguration memory arrays scopes heap (.returning (scalarReturn result)) following) (some result) := by
  induction owner with
  | stop =>
      exact ⟨_, {fixedConfiguration memory arrays scopes heap (.returning (scalarReturn result)) .stop with
        status := .finished (scalarReturn result)}, .refl, choice, by
          simp [fixedConfiguration, FixedCore.step, FixedCore.advance], rfl⟩
  | sequence statement continuation ih | loop expression statement continuation ih =>
      apply ih.prepend
      apply Relation.ReflTransGen.single
      exact ⟨choice, by simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith], rfl⟩

private theorem expression_finish_output_none (policy : SignedConversionPolicy) (expression : Expression model)
    (saved : ExpressionEventExecution.State (Index expression) model)
    (continuation : LocatedStatements.AfterExpression model) (selections : List IndexData)
    (verdict : StatementMachine.Verdict model)
    (finished : (StatementMachine.machine model policy).step (.expression expression saved continuation selections) =
      some (.finish verdict)) : verdictOutput verdict = none := by
  unfold StatementMachine.machine at finished
  cases computed : StatementExecution.execute policy (.expression expression saved continuation selections) with
  | some pair =>
      cases pair with
      | mk event after => cases event <;> simp only [computed] at finished <;> cases finished
  | none =>
      simp only [computed, Option.some.injEq] at finished
      simp only [StatementMachine.classify] at finished
      repeat first | split at finished | (cases finished <;> rfl)


private theorem pending_expression_finished (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {memory : ObjectAccessMemory.State model.characters}
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {expression : Expression model} {continuation : LocatedStatements.AfterExpression model}
    (owner : ExpressionControl policy memory arrays scopes control following expression continuation)
    (events : List (Occurrence (Index expression) model)) (saved : SemanticState (Index expression) model)
    (history : SemanticHistory policy (compile expression)
      (represent (initialState (compile expression) memory)) events saved)
    (selections : List IndexData) (physical : LocatedStatements.Configuration model)
    (represented : LocatedStatements.represent physical = .expression expression saved continuation selections)
    (licensed : LicensedNext (.expression expression saved continuation selections))
    (verdict : StatementMachine.Verdict model)
    (finished : (StatementMachine.machine model policy).step physical = some (.finish verdict)) :
    ReachesTerminal policy abi program (fixedConfiguration memory arrays scopes heap control following)
      (verdictOutput verdict) := by
  cases physical <;> cases represented
  rename_i actual
  obtain ⟨next, reason, stepped, faulted⟩ := expression_finished_source_fault policy memory arrays scopes heap abi program
    choice owner events actual history selections licensed verdict finished
  refine ⟨_, next, .refl, choice, stepped, ?_⟩
  rw [expression_finish_output_none policy expression actual continuation selections verdict finished]
  exact ⟨reason, faulted⟩

private theorem pending_assignment_finished (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {memory : ObjectAccessMemory.State model.characters}
    (name : String) (source : FixedCore.Expression model) (destination : Destination) (operand : Expression model)
    (location : ResolvesExpression policy memory arrays scopes (.read (.named name)) (.load destination))
    (resolved : ResolvesExpression policy memory arrays scopes source operand)
    {following : FixedCore.Continuation model} {continuation : LocatedStatements.Continuation model}
    (events : List (Occurrence (Index (.assignment destination operand)) model))
    (saved : SemanticState (Index (.assignment destination operand)) model)
    (history : SemanticHistory policy (compile (.assignment destination operand))
      (represent (initialState (compile (.assignment destination operand)) memory)) events saved)
    (selections : List IndexData) (physical : LocatedStatements.Configuration model)
    (represented : LocatedStatements.represent physical =
      .expression (.assignment destination operand) saved (.discard continuation) selections)
    (licensed : LicensedNext (.expression (.assignment destination operand) saved (.discard continuation) selections))
    (verdict : StatementMachine.Verdict model)
    (finished : (StatementMachine.machine model policy).step physical = some (.finish verdict)) :
    ReachesTerminal policy abi program
      (fixedConfiguration memory arrays scopes heap (.execute (.assign (.named name) source)) following)
      (verdictOutput verdict) := by
  cases physical <;> cases represented
  rename_i actual
  obtain ⟨next, reason, stepped, faulted⟩ := assignment_finished_source_fault policy memory arrays scopes heap abi program
    choice name source destination operand location resolved following (.discard continuation) events actual history
      selections licensed verdict finished
  refine ⟨_, next, .refl, choice, stepped, ?_⟩
  rw [expression_finish_output_none policy (.assignment destination operand) actual (.discard continuation) selections verdict finished]
  exact ⟨reason, faulted⟩


private theorem boundary_finished (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice) {memory : ObjectAccessMemory.State model.characters}
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {target : List IndexData → LocatedStatements.SemanticConfiguration model}
    (related : ControlRelated policy memory arrays scopes control following target)
    (selections : List IndexData) (physical : LocatedStatements.Configuration model)
    (represented : LocatedStatements.represent physical = target selections)
    (licensed : LicensedNext (target selections)) (verdict : StatementMachine.Verdict model)
    (finished : (StatementMachine.machine model policy).step physical = some (.finish verdict)) :
    ReachesTerminal policy abi program (fixedConfiguration memory arrays scopes heap control following)
      (verdictOutput verdict) := by
  cases related with
  | statement statement owner =>
      cases physical with
      | flow _ _ _ _ | expression _ _ _ _ | returned _ _ _ => cases represented
      | statement actual after current choices =>
          obtain ⟨rfl, rfl, _, rfl⟩ := LocatedStatements.State.statement.inj represented
          cases statement <;> simp [StatementMachine.machine, StatementExecution.execute, StatementExecution.controlStep] at finished
  | @flow flow before after owner =>
      cases physical with
      | statement _ _ _ _ | expression _ _ _ _ | returned _ _ _ => cases represented
      | flow actual continuation current choices =>
          obtain ⟨rfl, rfl, _, rfl⟩ := LocatedStatements.State.flow.inj represented
          cases owner with
          | stop =>
              cases flow with
              | normal =>
                  simp only [StatementMachine.machine, StatementExecution.execute, lowerFlow,
                    StatementMachine.classify] at finished
                  cases finished
                  apply (returning_reaches_terminal policy arrays scopes heap abi program choice memory none
                    (show ResolvesContinuation policy memory arrays scopes .stop .stop from .stop)).prepend
                  exact Relation.ReflTransGen.single ⟨choice, by
                    simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.continueWith,
                      scalarReturn], rfl⟩
              | broken =>
                  simp only [StatementMachine.machine, StatementExecution.execute, lowerFlow,
                    StatementMachine.classify] at finished
                  cases finished
                  refine ⟨_, {fixedConfiguration memory arrays scopes heap (.flow .broken) .stop with
                    status := .faulted .constraint}, .refl, choice, ?_, ⟨.constraint, rfl⟩⟩
                  simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.fail]
              | continued =>
                  simp only [StatementMachine.machine, StatementExecution.execute, lowerFlow,
                    StatementMachine.classify] at finished
                  cases finished
                  refine ⟨_, {fixedConfiguration memory arrays scopes heap (.flow .continued) .stop with
                    status := .faulted .constraint}, .refl, choice, ?_, ⟨.constraint, rfl⟩⟩
                  simp [fixedConfiguration, FixedCore.step, FixedCore.advance, FixedCore.Configuration.fail]
          | sequence statement owner | loop expression statement owner =>
              cases flow <;> simp [StatementMachine.machine, StatementExecution.execute, StatementExecution.controlStep, lowerFlow] at finished
  | loopExpression expression statement owner =>
      exact pending_expression_finished policy arrays scopes heap abi program choice
        (.whileLoop expression statement owner) [] _ (.nil _) selections physical represented licensed verdict finished
  | returning result owner =>
      cases physical with
      | statement _ _ _ _ | expression _ _ _ _ | flow _ _ _ _ => cases represented
      | returned actual current choices =>
          obtain ⟨rfl, _, rfl⟩ := LocatedStatements.State.returned.inj represented
          simp only [StatementMachine.machine, StatementExecution.execute, StatementMachine.classify] at finished
          cases finished
          exact returning_reaches_terminal policy arrays scopes heap abi program choice memory actual owner
  | fallthrough =>
      cases physical with
      | statement _ _ _ _ | expression _ _ _ _ | returned _ _ _ => cases represented
      | flow actual continuation current choices =>
          obtain ⟨rfl, rfl, _, rfl⟩ := LocatedStatements.State.flow.inj represented
          simp only [StatementMachine.machine, StatementExecution.execute, StatementMachine.classify] at finished
          cases finished
          exact returning_reaches_terminal policy arrays scopes heap abi program choice memory none .stop

/-- A finishing reached machine state reconstructs a genuine source
completion/refusal. Exact diagnostic receipts remain in the reached history;
only the comparison observer coarsens which failed operand was encountered first. -/
theorem ReachedControl.finished (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    (choice : FixedCore.Choice)
    {source : FixedCore.Executable model} {target : LocatedStatements.SemanticConfiguration model}
    (related : ReachedControl policy arrays scopes heap source target)
    (physical : LocatedStatements.Configuration model)
    (represented : LocatedStatements.represent physical = target)
    (licensed : LicensedNext target) (verdict : StatementMachine.Verdict model)
    (finished : (StatementMachine.machine model policy).step physical = some (.finish verdict)) :
    ReachesTerminal policy abi program source (verdictOutput verdict) := by
  cases related with
  | boundary related selections =>
      exact boundary_finished policy arrays scopes heap abi program choice related selections physical represented licensed verdict finished
  | expression owner events saved history selections =>
      exact pending_expression_finished policy arrays scopes heap abi program choice owner events saved history
        selections physical represented licensed verdict finished
  | assignment name source destination operand location resolved owner events saved history selections =>
      exact pending_assignment_finished policy arrays scopes heap abi program choice
        name source destination operand location resolved events saved history selections physical represented licensed verdict finished

/-- A scheduler supplies only decoded ready occurrence choices at reached
prefixes. An absent choice is permitted and remains an interaction request. -/
def LicensedExecution (policy : SignedConversionPolicy) (fuel : Nat)
    (initial : LocatedStatements.Configuration model) : Prop :=
  ∀ count < fuel, ∀ receipts saved,
    (StatementMachine.machine model policy).run count initial = (receipts, .exhausted saved) →
      LicensedNext (LocatedStatements.represent saved)

/-- The actual finishing run discovers its final live control and exact
receipt prefix. A licensed terminal choice then reflects to a source result. -/
theorem ReachedControl.finished_run (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    {source : FixedCore.Executable model} (initial : LocatedStatements.Configuration model)
    (related : ReachedControl policy arrays scopes heap source (LocatedStatements.represent initial))
    (fuel : Nat) (receipts : List (StatementMachine.Receipt model)) (verdict : StatementMachine.Verdict model)
    (ran : (StatementMachine.machine model policy).run fuel initial = (receipts, .finished verdict)) :
    ∃ count < fuel, ∃ saved final events,
      (StatementMachine.machine model policy).run count initial = (receipts, .exhausted saved) ∧
      Relation.ReflTransGen (SourceRunningStep policy abi program) source final ∧
      ReachedControl policy arrays scopes heap final (LocatedStatements.represent saved) ∧
      StatementHistory.History policy (LocatedStatements.represent initial) events (LocatedStatements.represent saved) ∧
      events.length = count ∧ receipts.map StatementMachine.Receipt.event = events.filterMap id ∧
      (StatementMachine.machine model policy).step saved = some (.finish verdict) ∧
      (LicensedNext (LocatedStatements.represent saved) →
        ReachesTerminal policy abi program source (verdictOutput verdict)) := by
  obtain ⟨count, bound, saved, earlier, finalEvents, paused, stopped, emissions⟩ :=
    (StatementMachine.machine model policy).run_boundary_prefix ran (by intro saved same; cases same)
  obtain ⟨rfl, finished⟩ := ((StatementMachine.machine model policy).run_one_finished_iff saved finalEvents verdict).mp stopped
  simp only [List.append_nil] at emissions
  subst earlier
  obtain ⟨final, events, sourceHistory, endpoint, history, length, observations⟩ :=
    related.exhausted policy arrays scopes heap abi program initial saved count receipts paused
  refine ⟨count, bound, saved, final, events, paused, sourceHistory, endpoint, history,
    length, observations, finished, ?_⟩
  intro licensed
  exact (endpoint.finished policy arrays scopes heap abi program (FixedCore.canonicalChoice model final)
    saved rfl licensed verdict finished).prepend sourceHistory

/-- Every completed run with admitted scheduling has a genuine source
completion/refusal, regardless of operand order or number of source loops. -/
theorem ReachedControl.finished_run_of_licensed (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    {source : FixedCore.Executable model} (initial : LocatedStatements.Configuration model)
    (related : ReachedControl policy arrays scopes heap source (LocatedStatements.represent initial))
    (fuel : Nat) (receipts : List (StatementMachine.Receipt model)) (verdict : StatementMachine.Verdict model)
    (ran : (StatementMachine.machine model policy).run fuel initial = (receipts, .finished verdict))
    (licensed : LicensedExecution policy fuel initial) :
    ReachesTerminal policy abi program source (verdictOutput verdict) := by
  obtain ⟨count, bound, saved, final, events, paused, _, _, _, _, _, _, reflection⟩ :=
    related.finished_run policy arrays scopes heap abi program initial fuel receipts verdict ran
  exact reflection (licensed count bound receipts saved paused)

private theorem call_retains_configuration (policy : SignedConversionPolicy)
    (before saved : LocatedStatements.Configuration model) (request : StatementMachine.SelectionRequest model)
    (called : (StatementMachine.machine model policy).step before = some (.call request saved)) :
    saved = before := by
  cases executed : StatementExecution.execute policy before with
  | some result =>
      rcases result with ⟨event, next⟩
      cases event <;> simp only [StatementMachine.machine, executed] at called <;> cases called
  | none =>
      have classified : StatementMachine.classify before = .call request saved := by
        simpa only [StatementMachine.machine, executed, Option.some.injEq] using called
      cases before <;> simp only [StatementMachine.classify] at classified <;>
        repeat first | split at classified | (cases classified <;> rfl)

/-- A scheduler suspension has the same earned owning control as its exact
pre-request exhausted prefix. Requesting a choice does not replay a store,
consume an occurrence, or become a source fault. -/
theorem ReachedControl.suspended (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    {source : FixedCore.Executable model} (initial saved : LocatedStatements.Configuration model)
    (related : ReachedControl policy arrays scopes heap source (LocatedStatements.represent initial))
    (fuel : Nat) (receipts : List (StatementMachine.Receipt model)) (request : StatementMachine.SelectionRequest model)
    (ran : (StatementMachine.machine model policy).run fuel initial = (receipts, .suspended request saved)) :
    ∃ count < fuel, ∃ final events,
      (StatementMachine.machine model policy).run count initial = (receipts, .exhausted saved) ∧
      Relation.ReflTransGen (SourceRunningStep policy abi program) source final ∧
      ReachedControl policy arrays scopes heap final (LocatedStatements.represent saved) ∧
      StatementHistory.History policy (LocatedStatements.represent initial) events (LocatedStatements.represent saved) ∧
      events.length = count ∧ receipts.map StatementMachine.Receipt.event = events.filterMap id ∧
      (StatementMachine.machine model policy).step saved = some (.call request saved) := by
  obtain ⟨count, bound, before, earlier, finalEvents, paused, stopped, emissions⟩ :=
    (StatementMachine.machine model policy).run_boundary_prefix ran (by intro saved same; cases same)
  obtain ⟨rfl, called⟩ := ((StatementMachine.machine model policy).run_one_suspended_iff before finalEvents request saved).mp stopped
  have same := call_retains_configuration policy before saved request called
  subst before
  simp only [List.append_nil] at emissions
  subst earlier
  obtain ⟨final, events, sourceHistory, endpoint, history, length, observations⟩ :=
    related.exhausted policy arrays scopes heap abi program initial saved count receipts paused
  exact ⟨count, bound, final, events, paused, sourceHistory, endpoint, history, length, observations, called⟩

/-- Every independently licensed statement transition admits its actual
next occurrence. No evaluation-order policy is added. -/
theorem licensed_of_step {policy : SignedConversionPolicy}
    {before after : LocatedStatements.SemanticConfiguration model}
    {event : Option (LocatedStatements.Event model)}
    (stepped : StatementSemantics.Step policy before event after) : LicensedNext before := by
  cases stepped with
  | administrative before after stepped => cases stepped <;> trivial
  | iteration before after kind stepped => cases stepped <;> trivial
  | occurrence expression before after continuation data rest index outcome decoded advanced =>
      intro _ _ actual tail same
      obtain ⟨rfl, rfl⟩ := List.cons.inj same
      refine ⟨index, decoded, ?_⟩
      cases advanced with
      | execute _ _ _ _ _ _ _ ready _ _ _ _ _ =>
          exact (ExpressionSourceExecution.ready_iff _ _ _).mpr ready
  | boundary expression saved continuation selections value completed target continued =>
      intro _ nonempty
      exact False.elim (nonempty completed.pending)

private theorem history_initial_licensed {policy : SignedConversionPolicy}
    {before after : LocatedStatements.SemanticConfiguration model}
    {events : List (Option (LocatedStatements.Event model))}
    (history : StatementHistory.History policy before events after)
    (licensed : LicensedNext after) : LicensedNext before := by
  cases history with
  | nil => exact licensed
  | cons _ _ _ _ _ stepped _ => exact licensed_of_step stepped

/-- The schedules used to realize independent histories are admitted at all
actual prefixes, provided their last residual admits the next boundary. -/
theorem history_licensed_execution (policy : SignedConversionPolicy)
    {before after : LocatedStatements.SemanticConfiguration model}
    (events : List (Option (LocatedStatements.Event model)))
    (history : StatementHistory.History policy before events after)
    (initial : LocatedStatements.Configuration model) (represented : LocatedStatements.represent initial = before)
    (licensed : LicensedNext after) : LicensedExecution policy (events.length + 1) initial := by
  intro count bound receipts saved paused
  have below : count ≤ events.length := by omega
  obtain ⟨middle, final, firstReceipts, lastReceipts, _, lastHistory, firstRun, _, endpoint, _, _⟩ :=
    history_retained_split policy before after events history count initial represented
  rw [List.length_take, Nat.min_eq_left below] at firstRun
  have same : middle = saved := Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome.exhausted.inj
    (congrArg Prod.snd (firstRun.symm.trans paused))
  subst middle
  exact history_initial_licensed lastHistory (endpoint.symm ▸ licensed)

/-- A successful common output contains no pending expression choice. -/
theorem output_licensed (saved : LocatedStatements.SemanticConfiguration model)
    (value : Option (IntegerScalar.Value model.parameters)) (observed : output saved = some value) :
    LicensedNext saved := by
  cases saved with
  | statement _ _ _ _ | returned _ _ _ | flow _ _ _ _ => trivial
  | expression _ _ _ _ => cases observed


/-- The successful constructed block has an admitted schedule all the way
through its final finishing boundary. -/
theorem Block.licensed_finished_realization {policy : SignedConversionPolicy}
    {before after : List IndexData → LocatedStatements.SemanticConfiguration model}
    (block : Block policy before after) (rest : List IndexData)
    (load : List IndexData → LocatedStatements.Configuration model)
    (represented : ∀ selections, LocatedStatements.represent (load selections) = before selections)
    (value : Option (IntegerScalar.Value model.parameters)) (observed : output (after rest) = some value) :
    ∃ choices fuel receipts verdict,
      (StatementMachine.machine model policy).run fuel (load (choices ++ rest)) = (receipts, .finished verdict) ∧
      LicensedExecution policy fuel (load (choices ++ rest)) ∧ verdictOutput verdict = some value := by
  obtain ⟨choices, events, history⟩ := block rest
  obtain ⟨saved, receipts, endpoint, executed, _⟩ :=
    StatementHistory.history_realization policy _ _ events history (load (choices ++ rest)) (represented _)
  obtain ⟨verdict, finish, result⟩ := output_finishes policy saved value (endpoint.symm ▸ observed)
  refine ⟨choices, events.length + 1, receipts, verdict, ?_, ?_, result⟩
  · rw [(StatementMachine.machine model policy).run_add, executed]
    simp only [Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine.continueRun,
      (StatementMachine.machine model policy).run_succ_finish (fuel := 0) finish, List.append_nil]
  · exact history_licensed_execution policy events history _ (represented _) (output_licensed _ value observed)

/-- The constructed refusal ends at an admitted ready operation or a recorded
terminal outcome. Malformed scheduler choices cannot witness this result. -/
theorem RefusalBlock.licensed_realization {policy : SignedConversionPolicy}
    {before : List IndexData → LocatedStatements.SemanticConfiguration model}
    (block : RefusalBlock policy before) (rest : List IndexData)
    (load : List IndexData → LocatedStatements.Configuration model)
    (represented : ∀ selections, LocatedStatements.represent (load selections) = before selections) :
    ∃ choices fuel receipts verdict,
      (StatementMachine.machine model policy).run fuel (load (choices ++ rest)) = (receipts, .finished verdict) ∧
      LicensedExecution policy fuel (load (choices ++ rest)) ∧ verdictOutput verdict = none := by
  obtain ⟨choices, events, final, history, licensed, finishing⟩ := block rest
  obtain ⟨saved, receipts, endpoint, executed, _⟩ :=
    StatementHistory.history_realization policy _ _ events history (load (choices ++ rest)) (represented _)
  obtain ⟨verdict, finish, observed⟩ := finishing saved endpoint
  refine ⟨choices, events.length + 1, receipts, verdict, ?_, ?_, observed⟩
  · rw [(StatementMachine.machine model policy).run_add, executed]
    simp only [Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine.continueRun,
      (StatementMachine.machine model policy).run_succ_finish (fuel := 0) finish, List.append_nil]
  · exact history_licensed_execution policy events history _ (represented _) licensed

/-- Equality of the complete common-fragment observations. Both successful
values and source refusal are realized, and every admitted located completion
reflects. The observer coarsens diagnostics, never receipts or pending states. -/
theorem terminal_observation_iff (policy : SignedConversionPolicy)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (scopes : List (FixedCore.Scope model)) (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    {control : FixedCore.Control model} {following : FixedCore.Continuation model}
    {target : List IndexData → LocatedStatements.SemanticConfiguration model}
    (related : ControlRelated policy memory arrays scopes control following target)
    (load : List IndexData → LocatedStatements.Configuration model)
    (represented : ∀ selections, LocatedStatements.represent (load selections) = target selections)
    (observation : Option (Option (IntegerScalar.Value model.parameters))) :
    ReachesTerminal policy abi program (fixedConfiguration memory arrays scopes heap control following) observation ↔
      ∃ choices fuel receipts verdict,
        (StatementMachine.machine model policy).run fuel (load choices) = (receipts, .finished verdict) ∧
        LicensedExecution policy fuel (load choices) ∧ verdictOutput verdict = observation := by
  constructor
  · rintro ⟨before, final, history, choice, last, agrees⟩
    cases observation with
    | none =>
        obtain ⟨fault, failed⟩ := agrees
        have block := faulted_history_simulation policy memory arrays scopes heap abi program related
          before final fault history choice last failed
        simpa only [List.append_nil] using block.licensed_realization [] load represented
    | some value =>
        obtain ⟨result, after, same, block, observed⟩ :=
          completed_history_simulation policy memory arrays scopes heap abi program related before final
            (scalarReturn value) history choice last agrees
        have equal : value = result := by
          cases value <;> cases result <;> simp_all [scalarReturn]
        subst result
        simpa only [List.append_nil] using block.licensed_finished_realization [] load represented value (observed [])
  · rintro ⟨choices, fuel, receipts, verdict, ran, licensed, observed⟩
    have reached : ReachedControl policy arrays scopes heap
        (fixedConfiguration memory arrays scopes heap control following) (LocatedStatements.represent (load choices)) :=
      (represented choices).symm ▸ ReachedControl.boundary related choices
    rw [← observed]
    exact reached.finished_run_of_licensed policy arrays scopes heap abi program (load choices) fuel receipts verdict ran licensed

private theorem run_ne_faulted (policy : SignedConversionPolicy) (fuel : Nat)
    (initial : LocatedStatements.Configuration model) :
    ((StatementMachine.machine model policy).run fuel initial).2 ≠ .faulted := by
  induction fuel generalizing initial with
  | zero => simp only [Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine.run, ne_eq, reduceCtorEq, not_false_eq_true]
  | succ fuel ih =>
      cases executed : StatementExecution.execute policy initial with
      | none =>
          cases classified : StatementMachine.classify initial with
          | silent next => exact False.elim (StatementMachine.classify_not_silent _ _ classified)
          | publish events next => exact False.elim (StatementMachine.classify_not_publish _ _ _ classified)
          | fail events => exact False.elim (StatementMachine.classify_not_fail _ _ classified)
          | finish verdict | call request next =>
              simp only [Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine.run, StatementMachine.machine,
                executed, classified, ne_eq, reduceCtorEq, not_false_eq_true]
      | some result =>
          rcases result with ⟨event, next⟩
          cases event <;> simpa only [Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine.run,
            StatementMachine.machine, executed] using ih next

/-- Whole-run regional agreement. Completed observations use the common
value/refusal observer; budgets and requests retain a genuine source control,
its actual located partial history, and every chronological receipt occurrence. -/
theorem ReachedControl.run (policy : SignedConversionPolicy)
    (arrays : ArrayPointers.Catalog) (scopes : List (FixedCore.Scope model))
    (heap : List Mettapedia.Machines.CMemory.BlockId)
    (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : FixedCore.Program model)
    {source : FixedCore.Executable model} (initial : LocatedStatements.Configuration model)
    (related : ReachedControl policy arrays scopes heap source (LocatedStatements.represent initial))
    (fuel : Nat) (receipts : List (StatementMachine.Receipt model))
    (outcome : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (LocatedStatements.Configuration model)
      (StatementMachine.Verdict model) (StatementMachine.SelectionRequest model))
    (ran : (StatementMachine.machine model policy).run fuel initial = (receipts, outcome))
    (licensed : LicensedExecution policy fuel initial) :
    match outcome with
    | .finished verdict => ReachesTerminal policy abi program source (verdictOutput verdict)
    | .exhausted saved | .suspended _ saved =>
        ∃ final events, Relation.ReflTransGen (SourceRunningStep policy abi program) source final ∧
          ReachedControl policy arrays scopes heap final (LocatedStatements.represent saved) ∧
          StatementHistory.History policy (LocatedStatements.represent initial) events (LocatedStatements.represent saved) ∧
          receipts.map StatementMachine.Receipt.event = events.filterMap id
    | .stuck _ | .faulted => False := by
  cases outcome with
  | finished verdict =>
      exact related.finished_run_of_licensed policy arrays scopes heap abi program
        initial fuel receipts verdict ran licensed
  | exhausted saved =>
      obtain ⟨final, events, history, reached, eventsHistory, _, observations⟩ :=
        related.exhausted policy arrays scopes heap abi program initial saved fuel receipts ran
      exact ⟨final, events, history, reached, eventsHistory, observations⟩
  | suspended request saved =>
      obtain ⟨_, _, final, events, _, history, reached, eventsHistory, _, observations, _⟩ :=
        related.suspended policy arrays scopes heap abi program initial saved fuel receipts request ran
      exact ⟨final, events, history, reached, eventsHistory, observations⟩
  | stuck saved =>
      exact (StatementMachine.machine model policy).run_not_stuck_of_moves
        (by intro state; simp only [StatementMachine.machine, ne_eq, reduceCtorEq, not_false_eq_true])
        fuel initial saved (congrArg Prod.snd ran)
  | faulted => exact run_ne_faulted policy fuel initial (congrArg Prod.snd ran)


end ReachedControlExecution

end Mettapedia.Languages.C11.StatementMachineRefinement.FixedLocated
