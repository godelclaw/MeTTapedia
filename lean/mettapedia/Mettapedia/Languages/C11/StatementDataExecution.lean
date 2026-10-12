import Mettapedia.Languages.C11.StatementData

/-!
# Executable represented statement steps and exact residual transport

The represented interface uses the constructed statement machine and the
independent statement/control judgments. Malformed packets have a distinct
representation verdict. Valid terminal faults, conflicts and scheduler
suspensions preserve the complete saved packet. Plain receipts carry source
steps; decoding a receipt does not certify that step or authorize publication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.StatementDataExecution

open IntegerMemoryModel LocatedExpressions LocatedStatements
open LocatedExpressionData (ExpressionData IndexData OutcomeData ScalarData)
open StatementData
open Mettapedia.GSLT.Distinction.ProductiveBlocks (Machine Transition)

variable {model : Model}

private theorem decodeList_encode {Source Data : Type} (encode : Source → Data) (decode : Data → Option Source)
    (inverse : ∀ source, decode (encode source) = some source) (sources : List Source) :
    (sources.map encode).mapM decode = some sources := by
  induction sources with
  | nil => rfl
  | cons source rest ih => simp only [List.map_cons, List.mapM_cons, inverse, bind, Option.bind_some, ih, pure]

private theorem encodeList_decode {Source Data : Type} (encode : Source → Data) (decode : Data → Option Source)
    (inverse : ∀ data source, decode data = some source → encode source = data)
    (data : List Data) (sources : List Source) (decoded : data.mapM decode = some sources) : sources.map encode = data := by
  induction data generalizing sources with
  | nil => cases decoded; rfl
  | cons data rest ih =>
      simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, found, following, followingRead, rfl⟩ := decoded
      simp only [List.map_cons, inverse _ _ found, ih _ followingRead]

inductive EventData where
  | occurrence (expression : ExpressionData) (index : IndexData) (outcome : OutcomeData)
  | boundary (kind : Boundary) (expression : ExpressionData) (value : ScalarData)
  | iteration (kind : Loop)
  deriving DecidableEq, Repr

def encodeEvent : Event model → EventData
  | .occurrence expression index outcome => .occurrence
      (LocatedExpressionData.encodeExpression expression) index (LocatedExpressionData.encodeOutcome outcome)
  | .boundary kind expression value => .boundary kind
      (LocatedExpressionData.encodeExpression expression) (LocatedExpressionData.encodeScalar value)
  | .iteration kind => .iteration kind

def decodeEvent (model : Model) : EventData → Option (Event model)
  | .occurrence expression index outcome => do some (.occurrence
      (← LocatedExpressionData.decodeExpression model expression) index (← LocatedExpressionData.decodeOutcome model outcome))
  | .boundary kind expression value => do some (.boundary kind
      (← LocatedExpressionData.decodeExpression model expression) (← LocatedExpressionData.decodeScalar model value))
  | .iteration kind => some (.iteration kind)

theorem decodeEvent_encode (model : Model) (event : Event model) : decodeEvent model (encodeEvent event) = some event := by
  cases event <;> simp only [encodeEvent, decodeEvent, LocatedExpressionData.decodeExpression_encode,
    LocatedExpressionData.decodeOutcome_encode, LocatedExpressionData.decodeScalar_encode, bind, Option.bind_some]

theorem encodeEvent_decode (model : Model) (data : EventData) (event : Event model)
    (decoded : decodeEvent model data = some event) : encodeEvent event = data := by
  cases data with
  | occurrence expression index outcome =>
      simp only [decodeEvent, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, result, resultRead, rfl⟩ := decoded
      simp only [encodeEvent, LocatedExpressionData.encodeExpression_decode _ _ _ sourceRead,
        LocatedExpressionData.encodeOutcome_decode _ _ _ resultRead]
  | boundary kind expression value =>
      simp only [decodeEvent, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, scalar, scalarRead, rfl⟩ := decoded
      simp only [encodeEvent, LocatedExpressionData.encodeExpression_decode _ _ _ sourceRead,
        LocatedExpressionData.encodeScalar_decode _ _ _ scalarRead]
  | iteration kind => cases decoded; rfl


def encodeObservations (events : List (Option (Event model))) : List (Option EventData) :=
  events.map (encodeOptional encodeEvent)

def decodeObservations (model : Model) (data : List (Option EventData)) : Option (List (Option (Event model))) :=
  data.mapM (decodeOptional (decodeEvent model))

theorem decodeObservations_encode (model : Model) (events : List (Option (Event model))) :
    decodeObservations model (encodeObservations events) = some events :=
  decodeList_encode _ _ (decodeOptional_encode _ _ (decodeEvent_encode model)) events

theorem encodeObservations_decode (model : Model) (data : List (Option EventData)) (events : List (Option (Event model)))
    (decoded : decodeObservations model data = some events) : encodeObservations events = data :=
  encodeList_decode _ _ (encodeOptional_decode _ _ (encodeEvent_decode model)) _ _ decoded

structure ReceiptData where
  event : EventData
  before : ConfigurationData
  after : ConfigurationData
  deriving DecidableEq, Repr

def encodeReceipt (receipt : StatementMachine.Receipt model) : ReceiptData :=
  ⟨encodeEvent receipt.event, encodeConfiguration receipt.before, encodeConfiguration receipt.after⟩

def decodeReceipt (model : Model) (data : ReceiptData) : Option (StatementMachine.Receipt model) := do
  some ⟨← decodeEvent model data.event, ← decodeConfiguration model data.before, ← decodeConfiguration model data.after⟩

theorem decodeReceipt_encode (model : Model) (receipt : StatementMachine.Receipt model) :
    decodeReceipt model (encodeReceipt receipt) = some receipt := by
  cases receipt
  simp only [encodeReceipt, decodeReceipt, decodeEvent_encode, decodeConfiguration_encode, bind, Option.bind_some]

theorem encodeReceipt_decode (model : Model) (data : ReceiptData) (receipt : StatementMachine.Receipt model)
    (decoded : decodeReceipt model data = some receipt) : encodeReceipt receipt = data := by
  simp only [decodeReceipt, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
  obtain ⟨event, eventRead, before, beforeRead, after, afterRead, rfl⟩ := decoded
  cases data
  simp only [encodeReceipt, encodeEvent_decode _ _ _ eventRead,
    encodeConfiguration_decode _ _ _ beforeRead, encodeConfiguration_decode _ _ _ afterRead]

inductive VerdictData where
  | returned (value : Option ScalarData) (saved : ConfigurationData)
  | fallthrough (saved : ConfigurationData)
  | invalidControl (flow : Flow) (saved : ConfigurationData)
  | terminal (expression : ExpressionData) (index : IndexData) (outcome : OutcomeData) (saved : ConfigurationData)
  | unsequenced (expression : ExpressionData) (first second : IndexData) (saved : ConfigurationData)
  | refused (saved : ConfigurationData)
  deriving DecidableEq, Repr

def encodeVerdict : StatementMachine.Verdict model → VerdictData
  | .returned value saved => .returned (encodeOptional LocatedExpressionData.encodeScalar value) (encodeConfiguration saved)
  | .fallthrough saved => .fallthrough (encodeConfiguration saved)
  | .invalidControl flow saved => .invalidControl flow (encodeConfiguration saved)
  | .terminal expression index outcome saved => .terminal
      (LocatedExpressionData.encodeExpression expression) index (LocatedExpressionData.encodeOutcome outcome) (encodeConfiguration saved)
  | .unsequenced expression first second saved => .unsequenced
      (LocatedExpressionData.encodeExpression expression) first second (encodeConfiguration saved)
  | .refused saved => .refused (encodeConfiguration saved)

def decodeVerdict (model : Model) : VerdictData → Option (StatementMachine.Verdict model)
  | .returned value saved => do some (.returned
      (← decodeOptional (LocatedExpressionData.decodeScalar model) value) (← decodeConfiguration model saved))
  | .fallthrough saved => (decodeConfiguration model saved).map StatementMachine.Verdict.fallthrough
  | .invalidControl flow saved => (decodeConfiguration model saved).map (StatementMachine.Verdict.invalidControl flow)
  | .terminal expression index outcome saved => do some (.terminal
      (← LocatedExpressionData.decodeExpression model expression) index
      (← LocatedExpressionData.decodeOutcome model outcome) (← decodeConfiguration model saved))
  | .unsequenced expression first second saved => do some (.unsequenced
      (← LocatedExpressionData.decodeExpression model expression) first second (← decodeConfiguration model saved))
  | .refused saved => (decodeConfiguration model saved).map StatementMachine.Verdict.refused

theorem decodeVerdict_encode (model : Model) (verdict : StatementMachine.Verdict model) :
    decodeVerdict model (encodeVerdict verdict) = some verdict := by
  cases verdict <;> simp only [encodeVerdict, decodeVerdict, decodeConfiguration_encode,
    LocatedExpressionData.decodeExpression_encode, LocatedExpressionData.decodeOutcome_encode,
    decodeOptional_encode _ _ (LocatedExpressionData.decodeScalar_encode model), Option.map_some, bind, Option.bind_some]

theorem encodeVerdict_decode (model : Model) (data : VerdictData) (verdict : StatementMachine.Verdict model)
    (decoded : decodeVerdict model data = some verdict) : encodeVerdict verdict = data := by
  cases data with
  | returned value saved =>
      simp only [decodeVerdict, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨scalar, scalarRead, source, sourceRead, rfl⟩ := decoded
      simp only [encodeVerdict, encodeOptional_decode _ _ (LocatedExpressionData.encodeScalar_decode model) _ _ scalarRead,
        encodeConfiguration_decode _ _ _ sourceRead]
  | fallthrough saved | invalidControl flow saved | refused saved =>
      obtain ⟨source, sourceRead, rfl⟩ := Option.map_eq_some_iff.mp decoded
      simp only [encodeVerdict, encodeConfiguration_decode _ _ _ sourceRead]
  | terminal expression index outcome saved =>
      simp only [decodeVerdict, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, result, resultRead, state, stateRead, rfl⟩ := decoded
      simp only [encodeVerdict, LocatedExpressionData.encodeExpression_decode _ _ _ sourceRead,
        LocatedExpressionData.encodeOutcome_decode _ _ _ resultRead, encodeConfiguration_decode _ _ _ stateRead]
  | unsequenced expression first second saved =>
      simp only [decodeVerdict, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, state, stateRead, rfl⟩ := decoded
      simp only [encodeVerdict, LocatedExpressionData.encodeExpression_decode _ _ _ sourceRead,
        encodeConfiguration_decode _ _ _ stateRead]

structure RequestData where
  expression : ExpressionData
  enabled : List IndexData
  deriving DecidableEq, Repr

def encodeRequest (request : StatementMachine.SelectionRequest model) : RequestData :=
  ⟨LocatedExpressionData.encodeExpression request.expression, request.enabled⟩

def decodeRequest (model : Model) (data : RequestData) : Option (StatementMachine.SelectionRequest model) :=
  (LocatedExpressionData.decodeExpression model data.expression).map (fun expression => ⟨expression, data.enabled⟩)

theorem decodeRequest_encode (model : Model) (request : StatementMachine.SelectionRequest model) :
    decodeRequest model (encodeRequest request) = some request := by
  cases request
  simp only [encodeRequest, decodeRequest, LocatedExpressionData.decodeExpression_encode, Option.map_some]

theorem encodeRequest_decode (model : Model) (data : RequestData) (request : StatementMachine.SelectionRequest model)
    (decoded : decodeRequest model data = some request) : encodeRequest request = data := by
  obtain ⟨source, sourceRead, rfl⟩ := Option.map_eq_some_iff.mp decoded
  cases data
  simp only [encodeRequest, LocatedExpressionData.encodeExpression_decode _ _ _ sourceRead]

abbrev SourceTransitionData := Transition ConfigurationData ReceiptData VerdictData RequestData
abbrev SourceTransition (model : Model) := Transition (Configuration model) (StatementMachine.Receipt model)
  (StatementMachine.Verdict model) (StatementMachine.SelectionRequest model)

def encodeTransition : SourceTransition model → SourceTransitionData
  | .silent next => .silent (encodeConfiguration next)
  | .publish receipts next => .publish (receipts.map encodeReceipt) (encodeConfiguration next)
  | .finish verdict => .finish (encodeVerdict verdict)
  | .fail receipts => .fail (receipts.map encodeReceipt)
  | .call request saved => .call (encodeRequest request) (encodeConfiguration saved)

def decodeTransition (model : Model) : SourceTransitionData → Option (SourceTransition model)
  | .silent next => (decodeConfiguration model next).map Transition.silent
  | .publish receipts next => do some (.publish (← receipts.mapM (decodeReceipt model)) (← decodeConfiguration model next))
  | .finish verdict => (decodeVerdict model verdict).map Transition.finish
  | .fail receipts => (receipts.mapM (decodeReceipt model)).map Transition.fail
  | .call request saved => do some (.call (← decodeRequest model request) (← decodeConfiguration model saved))

theorem decodeTransition_encode (model : Model) (transition : SourceTransition model) :
    decodeTransition model (encodeTransition transition) = some transition := by
  cases transition <;> simp only [encodeTransition, decodeTransition, decodeConfiguration_encode, decodeVerdict_encode,
    decodeRequest_encode, decodeList_encode _ _ (decodeReceipt_encode model), Option.map_some, bind, Option.bind_some]

theorem encodeTransition_decode (model : Model) (data : SourceTransitionData) (transition : SourceTransition model)
    (decoded : decodeTransition model data = some transition) : encodeTransition transition = data := by
  cases data with
  | silent next =>
      obtain ⟨source, sourceRead, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg Transition.silent (encodeConfiguration_decode _ _ _ sourceRead)
  | finish verdict =>
      obtain ⟨source, sourceRead, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg Transition.finish (encodeVerdict_decode _ _ _ sourceRead)
  | fail receipts =>
      obtain ⟨source, sourceRead, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg Transition.fail (encodeList_decode _ _ (encodeReceipt_decode model) _ _ sourceRead)
  | publish receipts next =>
      simp only [decodeTransition, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨events, eventsRead, source, sourceRead, rfl⟩ := decoded
      simp only [encodeTransition, encodeList_decode _ _ (encodeReceipt_decode model) _ _ eventsRead,
        encodeConfiguration_decode _ _ _ sourceRead]
  | call request saved =>
      simp only [decodeTransition, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, sourceRead, state, stateRead, rfl⟩ := decoded
      simp only [encodeTransition, encodeRequest_decode _ _ _ sourceRead, encodeConfiguration_decode _ _ _ stateRead]

def executeData (model : Model) (policy : SignedConversionPolicy) (data : ConfigurationData) :
    Option (Option EventData × ConfigurationData) := do
  let before ← decodeConfiguration model data
  let (event, after) ← StatementExecution.execute policy before
  some (encodeOptional encodeEvent event, encodeConfiguration after)

theorem executeData_sound (model : Model) (policy : SignedConversionPolicy)
    (before after : ConfigurationData) (event : Option EventData)
    (computed : executeData model policy before = some (event, after)) :
    ∃ source target observation, decodeConfiguration model before = some source ∧
      after = encodeConfiguration target ∧ event = encodeOptional encodeEvent observation ∧
      StatementSemantics.Step policy (represent source) observation (represent target) := by
  simp only [executeData, bind, Option.bind_eq_some_iff, Option.some.injEq] at computed
  obtain ⟨source, sourceRead, ⟨observation, target⟩, executed, equal⟩ := computed
  cases equal
  exact ⟨source, target, observation, sourceRead, rfl, rfl, StatementExecution.execute_sound _ _ _ _ executed⟩

theorem executeData_complete (model : Model) (policy : SignedConversionPolicy) (before : Configuration model)
    (after : SemanticConfiguration model) (event : Option (Event model))
    (stepped : StatementSemantics.Step policy (represent before) event after) :
    ∃ target, represent target = after ∧
      executeData model policy (encodeConfiguration before) =
        some (encodeOptional encodeEvent event, encodeConfiguration target) := by
  obtain ⟨target, executed, represented⟩ := StatementExecution.execute_complete _ _ _ _ stepped
  exact ⟨target, represented, by simp only [executeData, decodeConfiguration_encode, executed, bind, Option.bind_some]⟩

def stepData (model : Model) (policy : SignedConversionPolicy) (data : ConfigurationData) : Option SourceTransitionData := do
  let source ← decodeConfiguration model data
  let transition ← (StatementMachine.machine model policy).step source
  some (encodeTransition transition)

theorem stepData_on_encoded (model : Model) (policy : SignedConversionPolicy) (source : Configuration model)
    (transition : SourceTransition model) (stepped : (StatementMachine.machine model policy).step source = some transition) :
    stepData model policy (encodeConfiguration source) = some (encodeTransition transition) := by
  simp only [stepData, decodeConfiguration_encode, stepped, bind, Option.bind_some]

theorem stepData_iff (model : Model) (policy : SignedConversionPolicy) (data : ConfigurationData)
    (transition : SourceTransitionData) : stepData model policy data = some transition ↔
    ∃ source next, decodeConfiguration model data = some source ∧
      (StatementMachine.machine model policy).step source = some next ∧ encodeTransition next = transition := by
  simp only [stepData, bind, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨source, decoded, next, stepped, encoded⟩
    exact ⟨source, next, decoded, stepped, encoded⟩
  · rintro ⟨source, next, decoded, stepped, encoded⟩
    exact ⟨source, decoded, next, stepped, encoded⟩

inductive ResultData where
  | source (verdict : VerdictData)
  | malformed (supplied : ConfigurationData)
  deriving DecidableEq, Repr

abbrev TransitionData := Transition ConfigurationData ReceiptData ResultData RequestData

def liftTransition : SourceTransitionData → TransitionData
  | .silent next => .silent next
  | .publish receipts next => .publish receipts next
  | .finish verdict => .finish (.source verdict)
  | .fail receipts => .fail receipts
  | .call request saved => .call request saved

def machineData (model : Model) (policy : SignedConversionPolicy) : Machine ConfigurationData ReceiptData ResultData RequestData where
  step data := some <| match stepData model policy data with
    | some transition => liftTransition transition
    | none => .finish (.malformed data)

theorem machineData_step_encoded (model : Model) (policy : SignedConversionPolicy) (source : Configuration model)
    (transition : SourceTransition model) (stepped : (StatementMachine.machine model policy).step source = some transition) :
    (machineData model policy).step (encodeConfiguration source) = some (liftTransition (encodeTransition transition)) := by
  simp only [machineData, stepData_on_encoded _ _ _ _ stepped]

def encodeRunOutcome : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (Configuration model)
    (StatementMachine.Verdict model) (StatementMachine.SelectionRequest model) →
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome ConfigurationData ResultData RequestData
  | .finished verdict => .finished (.source (encodeVerdict verdict))
  | .faulted => .faulted
  | .suspended request saved => .suspended (encodeRequest request) (encodeConfiguration saved)
  | .stuck saved => .stuck (encodeConfiguration saved)
  | .exhausted saved => .exhausted (encodeConfiguration saved)

theorem runData_encoded (model : Model) (policy : SignedConversionPolicy) (fuel : Nat) (initial : Configuration model) :
    (machineData model policy).run fuel (encodeConfiguration initial) =
      (((StatementMachine.machine model policy).run fuel initial).1.map encodeReceipt,
        encodeRunOutcome ((StatementMachine.machine model policy).run fuel initial).2) := by
  induction fuel generalizing initial with
  | zero => rfl
  | succ fuel ih =>
      cases stepped : (StatementMachine.machine model policy).step initial with
      | none => simp only [StatementMachine.machine] at stepped; cases stepped
      | some transition =>
          have encoded := machineData_step_encoded model policy initial transition stepped
          cases transition <;> simp only [Machine.run, stepped, encoded, encodeTransition, liftTransition,
            encodeRunOutcome, ih, List.map_append, List.map_nil]

def priceData (model : Model) (price : Configuration model → Nat) (data : ConfigurationData) : Nat :=
  match decodeConfiguration model data with
  | none => 0
  | some source => price source

theorem priceData_encoded (model : Model) (price : Configuration model → Nat) (source : Configuration model) :
    priceData model price (encodeConfiguration source) = price source := by
  simp only [priceData, decodeConfiguration_encode]

theorem spentData_encoded (model : Model) (policy : SignedConversionPolicy) (price : Configuration model → Nat)
    (fuel : Nat) (initial : Configuration model) :
    (machineData model policy).spent (priceData model price) fuel (encodeConfiguration initial) =
      (StatementMachine.machine model policy).spent price fuel initial := by
  induction fuel generalizing initial with
  | zero => rfl
  | succ fuel ih =>
      cases stepped : (StatementMachine.machine model policy).step initial with
      | none => simp only [StatementMachine.machine] at stepped; cases stepped
      | some transition =>
          have encoded := machineData_step_encoded model policy initial transition stepped
          cases transition <;> simp only [Machine.spent, stepped, encoded, encodeTransition, liftTransition,
            priceData_encoded, ih]

theorem resume_after_prefix (model : Model) (policy : SignedConversionPolicy) (first second : Nat)
    (initial saved : ConfigurationData) (receipts : List ReceiptData)
    (paused : (machineData model policy).run first initial = (receipts, .exhausted saved)) :
    (machineData model policy).run (first + second) initial =
      (receipts ++ ((machineData model policy).run second saved).1, ((machineData model policy).run second saved).2) :=
  (machineData model policy).established_and_pending first second initial saved receipts paused

theorem resumed_accounts (model : Model) (policy : SignedConversionPolicy) (price : ConfigurationData → Nat)
    (first second : Nat) (initial saved : ConfigurationData) (receipts : List ReceiptData)
    (paused : (machineData model policy).run first initial = (receipts, .exhausted saved)) :
    (machineData model policy).spent price (first + second) initial =
      (machineData model policy).spent price first initial + (machineData model policy).spent price second saved := by
  rw [(machineData model policy).spent_add, paused]
  rfl

noncomputable def productive (model : Model) (policy : SignedConversionPolicy) : (machineData model policy).Productive where
  rank := priceData model LocatedStatements.rank
  moves data := by simp only [machineData, ne_eq, reduceCtorEq, not_false_eq_true]
  silent_decreases := by
    intro before after stepped
    cases decoded : decodeConfiguration model before with
    | none => simp only [machineData, stepData, decoded, bind, Option.bind_none] at stepped; cases stepped
    | some source =>
        cases executed : (StatementMachine.machine model policy).step source with
        | none => simp only [StatementMachine.machine] at executed; cases executed
        | some transition =>
            simp only [machineData, stepData, decoded, executed, bind, Option.bind_some] at stepped
            cases transition with
            | silent next =>
                have same : encodeConfiguration next = after := by
                  simpa only [encodeTransition, liftTransition, Option.some.injEq, Transition.silent.injEq] using stepped
                rw [← same, priceData_encoded]
                simp only [priceData, decoded]
                exact (StatementMachine.productive model policy).silent_decreases executed
            | publish events next | finish verdict | fail events | call request saved => cases stepped

end Mettapedia.Languages.C11.StatementDataExecution
