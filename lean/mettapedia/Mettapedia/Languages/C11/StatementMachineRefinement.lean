import Mettapedia.Languages.C11.StatementDataInteraction
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
