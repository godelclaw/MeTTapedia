import Mettapedia.Languages.C11.StatementDataInteraction

/-!
# Independently judged scheduling histories and checked statement residuals

A structural packet is distinct from a historically earned residual. This
module replays a finite sequence of source ticks and checked scheduling
supplies from a canonical initial statement and caller-supplied memory. Every
accepted endpoint has an independently judged source/control and delivery
history. All finite histories of this profile have constructed concrete
endpoints. Replay does not authenticate the initial world or grant ownership,
external-effect delivery or publication authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.StatementDataHistory

open IntegerMemoryModel LocatedExpressions LocatedStatements
open LocatedExpressionData (IndexData MemoryData)
open StatementData StatementDataExecution StatementDataInteraction

variable {model : Model}

inductive Command where
  | tick
  | deliver (choice : IndexData)
  deriving DecidableEq, Repr

inductive SourceStep (policy : SignedConversionPolicy) : SemanticConfiguration model → Command →
    Option (Event model) → SemanticConfiguration model → Prop where
  | tick (before after : SemanticConfiguration model) (event : Option (Event model))
      (stepped : StatementSemantics.Step policy before event after) : SourceStep policy before .tick event after
  | deliver (before after : SemanticConfiguration model) (choice : IndexData)
      (delivered : Delivery before choice after) : SourceStep policy before (.deliver choice) none after

inductive History (policy : SignedConversionPolicy) : SemanticConfiguration model → List Command →
    List (Option (Event model)) → SemanticConfiguration model → Prop where
  | nil (state : SemanticConfiguration model) : History policy state [] [] state
  | cons (before middle after : SemanticConfiguration model) (command : Command) (event : Option (Event model))
      (commands : List Command) (events : List (Option (Event model)))
      (stepped : SourceStep policy before command event middle)
      (following : History policy middle commands events after) :
      History policy before (command :: commands) (event :: events) after

def performData (model : Model) (policy : SignedConversionPolicy) (before : ConfigurationData) :
    Command → Option (Option EventData × ConfigurationData)
  | .tick => executeData model policy before
  | .deliver choice => (deliverData model before choice).map (fun after => (none, after))

theorem performData_sound (model : Model) (policy : SignedConversionPolicy) (before : Configuration model)
    (after : ConfigurationData) (command : Command) (event : Option EventData)
    (computed : performData model policy (encodeConfiguration before) command = some (event, after)) :
    ∃ target observation, after = encodeConfiguration target ∧ event = encodeOptional encodeEvent observation ∧
      SourceStep policy (represent before) command observation (represent target) := by
  cases command with
  | tick =>
      obtain ⟨source, target, observation, decoded, encoded, eventEqual, stepped⟩ := executeData_sound _ _ _ _ _ computed
      rw [decodeConfiguration_encode] at decoded
      cases decoded
      exact ⟨target, observation, encoded, eventEqual, .tick _ _ _ stepped⟩
  | deliver choice =>
      obtain ⟨afterData, delivered, equal⟩ := Option.map_eq_some_iff.mp computed
      cases equal
      obtain ⟨source, target, decoded, encoded, admitted⟩ := deliverData_sound _ _ _ _ delivered
      rw [decodeConfiguration_encode] at decoded
      cases decoded
      exact ⟨target, none, encoded, rfl, .deliver _ _ _ admitted⟩

theorem performData_complete (model : Model) (policy : SignedConversionPolicy) (before : Configuration model)
    (after : SemanticConfiguration model) (command : Command) (event : Option (Event model))
    (stepped : SourceStep policy (represent before) command event after) :
    ∃ target, represent target = after ∧
      performData model policy (encodeConfiguration before) command =
        some (encodeOptional encodeEvent event, encodeConfiguration target) := by
  cases stepped with
  | tick after event stepped => exact executeData_complete _ _ _ _ _ stepped
  | deliver after choice delivered =>
      obtain ⟨target, represented, computed⟩ := deliverData_complete _ _ _ _ delivered
      exact ⟨target, represented, by simp only [performData, computed, Option.map_some, encodeOptional]⟩

def replay (model : Model) (policy : SignedConversionPolicy) (before : ConfigurationData) :
    List Command → Option (List (Option EventData) × ConfigurationData)
  | [] => some ([], before)
  | command :: rest => do
      let (event, middle) ← performData model policy before command
      let (events, after) ← replay model policy middle rest
      some (event :: events, after)

theorem replay_sound (model : Model) (policy : SignedConversionPolicy) (before : Configuration model)
    (commands : List Command) (events : List (Option EventData)) (after : ConfigurationData)
    (computed : replay model policy (encodeConfiguration before) commands = some (events, after)) :
    ∃ target observations, after = encodeConfiguration target ∧ events = encodeObservations observations ∧
      History policy (represent before) commands observations (represent target) := by
  induction commands generalizing before events after with
  | nil =>
      have equal : ([], encodeConfiguration before) = (events, after) := Option.some.inj computed
      cases equal
      exact ⟨before, [], rfl, rfl, .nil _⟩
  | cons command rest ih =>
      simp only [replay, bind, Option.bind_eq_some_iff, Option.some.injEq] at computed
      obtain ⟨⟨event, middle⟩, performed, ⟨following, targetData⟩, replayed, equal⟩ := computed
      cases equal
      obtain ⟨next, observation, encoded, eventEqual, sourceStep⟩ := performData_sound _ _ _ _ _ _ performed
      rw [encoded] at replayed
      obtain ⟨target, observations, targetEqual, observed, followingHistory⟩ := ih next following targetData replayed
      refine ⟨target, observation :: observations, targetEqual, ?_, .cons _ _ _ _ _ _ _ sourceStep followingHistory⟩
      simp only [encodeObservations, List.map_cons, eventEqual, observed]

theorem replay_complete (model : Model) (policy : SignedConversionPolicy) (before after : SemanticConfiguration model)
    (commands : List Command) (events : List (Option (Event model)))
    (history : History policy before commands events after) (initial : Configuration model)
    (represented : represent initial = before) :
    ∃ target, represent target = after ∧ replay model policy (encodeConfiguration initial) commands =
      some (encodeObservations events, encodeConfiguration target) := by
  induction history generalizing initial with
  | nil before => exact ⟨initial, represented, rfl⟩
  | cons before middle after command event commands events stepped following ih =>
      have sourceStep : SourceStep policy (represent initial) command event middle := by rw [represented]; exact stepped
      obtain ⟨next, nextRepresented, performed⟩ := performData_complete _ _ _ _ _ _ sourceStep
      obtain ⟨target, targetRepresented, replayed⟩ := ih next nextRepresented
      exact ⟨target, targetRepresented, by
        simp only [replay, performed, replayed, bind, Option.bind_some, encodeObservations, List.map_cons]⟩

theorem replay_append (model : Model) (policy : SignedConversionPolicy) (before : ConfigurationData)
    (first second : List Command) :
    replay model policy before (first ++ second) = (do
      let (events, middle) ← replay model policy before first
      let (following, after) ← replay model policy middle second
      some (events ++ following, after)) := by
  induction first generalizing before with
  | nil =>
      simp only [List.nil_append, replay, bind, Option.bind_some]
      cases replay model policy before second with
      | none => rfl
      | some result => cases result; rfl
  | cons command rest ih =>
      simp only [List.cons_append, replay]
      cases performed : performData model policy before command with
      | none => simp only [bind, Option.bind_none]
      | some result =>
          rcases result with ⟨event, middle⟩
          simp only [bind, Option.bind_some, ih]
          cases replayed : replay model policy middle rest with
          | none => simp only [Option.bind_none]
          | some result =>
              rcases result with ⟨events, next⟩
              simp only [Option.bind_some]
              cases replay model policy next second with
              | none => rfl
              | some result => cases result; rfl

structure HistoryData where
  statement : Syntax
  initialMemory : MemoryData
  initialSelections : List IndexData
  commands : List Command
  observations : List (Option EventData)
  retained : ConfigurationData
  deriving DecidableEq, Repr

structure NativeHistory (model : Model) where
  statement : Statement model
  initialMemory : ObjectAccessMemory.State model.characters
  initialSelections : List IndexData
  commands : List Command
  observations : List (Option (Event model))
  retained : Configuration model

def encodeHistory (history : NativeHistory model) : HistoryData :=
  ⟨encodeStatement history.statement, LocatedExpressionData.encodeMemory history.initialMemory, history.initialSelections,
    history.commands, encodeObservations history.observations, encodeConfiguration history.retained⟩

def decodeHistory (model : Model) (data : HistoryData) : Option (NativeHistory model) := do
  some ⟨← decodeStatement model data.statement, ← LocatedExpressionData.decodeMemory model data.initialMemory,
    data.initialSelections, data.commands, ← decodeObservations model data.observations,
    ← decodeConfiguration model data.retained⟩

theorem decodeHistory_encode (model : Model) (history : NativeHistory model) : decodeHistory model (encodeHistory history) = some history := by
  cases history
  simp only [encodeHistory, decodeHistory, decodeStatement_encode, LocatedExpressionData.decodeMemory_encode,
    decodeObservations_encode, decodeConfiguration_encode, bind, Option.bind_some]

theorem encodeHistory_decode (model : Model) (data : HistoryData) (history : NativeHistory model)
    (decoded : decodeHistory model data = some history) : encodeHistory history = data := by
  simp only [decodeHistory, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
  obtain ⟨statement, statementRead, memory, memoryRead, observations, observationsRead, retained, retainedRead, rfl⟩ := decoded
  cases data
  simp only [encodeHistory, encodeStatement_decode _ _ _ statementRead, LocatedExpressionData.encodeMemory_decode _ _ _ memoryRead,
    encodeObservations_decode _ _ _ observationsRead, encodeConfiguration_decode _ _ _ retainedRead]

def restore (model : Model) (policy : SignedConversionPolicy) (data : HistoryData) : Option ConfigurationData := do
  let statement ← decodeStatement model data.statement
  let memory ← LocatedExpressionData.decodeMemory model data.initialMemory
  let (observations, saved) ← replay model policy (encodeConfiguration (initial statement memory data.initialSelections)) data.commands
  if saved = data.retained ∧ observations = data.observations then some saved else none

theorem restore_sound (model : Model) (policy : SignedConversionPolicy) (data : HistoryData) (retained : ConfigurationData)
    (restored : restore model policy data = some retained) :
    ∃ statement memory saved observations,
      decodeStatement model data.statement = some statement ∧ LocatedExpressionData.decodeMemory model data.initialMemory = some memory ∧
      retained = data.retained ∧ retained = encodeConfiguration saved ∧ data.observations = encodeObservations observations ∧
      History policy (represent (initial statement memory data.initialSelections)) data.commands observations (represent saved) := by
  simp only [restore, bind, Option.bind_eq_some_iff] at restored
  obtain ⟨statement, statementRead, memory, memoryRead, ⟨events, savedData⟩, replayed, restored⟩ := restored
  by_cases exactEndpoint : savedData = data.retained ∧ events = data.observations
  · simp only [if_pos exactEndpoint, Option.some.injEq] at restored
    cases restored
    obtain ⟨saved, observations, endpoint, observed, history⟩ := replay_sound _ _ _ _ _ _ replayed
    exact ⟨statement, memory, saved, observations, statementRead, memoryRead, exactEndpoint.1, endpoint,
      exactEndpoint.2.symm.trans observed, history⟩
  · simp only [if_neg exactEndpoint] at restored
    contradiction

theorem restore_complete (model : Model) (policy : SignedConversionPolicy) (statement : Statement model)
    (memory : ObjectAccessMemory.State model.characters) (selections : List IndexData) (after : SemanticConfiguration model)
    (commands : List Command) (events : List (Option (Event model)))
    (history : History policy (represent (initial statement memory selections)) commands events after) :
    ∃ saved, represent saved = after ∧
      restore model policy (encodeHistory ⟨statement, memory, selections, commands, events, saved⟩) = some (encodeConfiguration saved) := by
  obtain ⟨saved, represented, replayed⟩ := replay_complete _ _ _ _ _ _ history (initial statement memory selections) rfl
  refine ⟨saved, represented, ?_⟩
  simp only [restore, encodeHistory, decodeStatement_encode, LocatedExpressionData.decodeMemory_encode,
    replayed, bind, Option.bind_some, and_self, ↓reduceIte]

def extend (history : HistoryData) (command : Command) (event : Option EventData) (saved : ConfigurationData) : HistoryData :=
  {history with commands := history.commands ++ [command], observations := history.observations ++ [event], retained := saved}

theorem restore_extended (model : Model) (policy : SignedConversionPolicy) (history : HistoryData) (before after : ConfigurationData)
    (command : Command) (event : Option EventData) (restored : restore model policy history = some before)
    (performed : performData model policy before command = some (event, after)) :
    restore model policy (extend history command event after) = some after := by
  simp only [restore, bind, Option.bind_eq_some_iff] at restored
  obtain ⟨statement, statementRead, memory, memoryRead, ⟨events, savedData⟩, replayed, restored⟩ := restored
  by_cases endpoint : savedData = history.retained ∧ events = history.observations
  · simp only [if_pos endpoint, Option.some.injEq] at restored
    cases restored
    simp only [restore, extend, statementRead, memoryRead, bind, Option.bind_some, replay_append, replayed,
      replay, performed, endpoint.2, and_self, ↓reduceIte]
  · simp only [if_neg endpoint] at restored
    contradiction

def checkedPerform (model : Model) (policy : SignedConversionPolicy) (history : HistoryData) (command : Command) :
    Option (Option EventData × HistoryData) := do
  let before ← restore model policy history
  let (event, after) ← performData model policy before command
  some (event, extend history command event after)

theorem checkedPerform_preserves (model : Model) (policy : SignedConversionPolicy) (before after : HistoryData)
    (command : Command) (event : Option EventData) (computed : checkedPerform model policy before command = some (event, after)) :
    restore model policy after = some after.retained := by
  simp only [checkedPerform, bind, Option.bind_eq_some_iff, Option.some.injEq] at computed
  obtain ⟨source, restored, ⟨observation, target⟩, performed, equal⟩ := computed
  cases equal
  exact restore_extended _ _ _ _ _ _ _ restored performed

def checkedRespond (model : Model) (policy : SignedConversionPolicy) (history : HistoryData)
    (request : RequestPacket) (response : ResponseData) : Option HistoryData := do
  let before ← restore model policy history
  let after ← respond model before request response
  some (extend history (.deliver response.choice) none after)

theorem checkedRespond_preserves (model : Model) (policy : SignedConversionPolicy) (before after : HistoryData)
    (request : RequestPacket) (response : ResponseData) (computed : checkedRespond model policy before request response = some after) :
    restore model policy after = some after.retained := by
  simp only [checkedRespond, bind, Option.bind_eq_some_iff, Option.some.injEq] at computed
  obtain ⟨source, restored, target, responded, rfl⟩ := computed
  unfold respond at responded
  split at responded
  · split at responded
    · have performed : performData model policy source (.deliver response.choice) = some (none, target) := by
        simp only [performData, responded, Option.map_some]
      exact restore_extended _ _ _ _ _ _ _ restored performed
    · contradiction
  · contradiction

def account (model : Model) (policy : SignedConversionPolicy) (price : Command → ConfigurationData → Nat)
    (before : ConfigurationData) : List Command → Nat
  | [] => 0
  | command :: rest => price command before + match performData model policy before command with
      | none => 0
      | some (_, after) => account model policy price after rest

theorem account_append (model : Model) (policy : SignedConversionPolicy) (price : Command → ConfigurationData → Nat)
    (before middle : ConfigurationData) (first second : List Command) (events : List (Option EventData))
    (replayed : replay model policy before first = some (events, middle)) :
    account model policy price before (first ++ second) =
      account model policy price before first + account model policy price middle second := by
  induction first generalizing before events with
  | nil =>
      have same : ([], before) = (events, middle) := Option.some.inj replayed
      cases same
      simp only [List.nil_append, account, Nat.zero_add]
  | cons command rest ih =>
      simp only [replay, bind, Option.bind_eq_some_iff, Option.some.injEq] at replayed
      obtain ⟨⟨event, next⟩, performed, ⟨observations, saved⟩, replayed, equal⟩ := replayed
      cases equal
      simp only [List.cons_append, account, performed, ih next observations replayed, Nat.add_assoc]

def schedulingPrice : Command → ConfigurationData → Nat
  | .tick, _ => 0
  | .deliver _, _ => 1

def sourcePrice (model : Model) (price : Configuration model → Nat) : Command → ConfigurationData → Nat
  | .tick, configuration => priceData model price configuration
  | .deliver _, _ => 0

end Mettapedia.Languages.C11.StatementDataHistory
