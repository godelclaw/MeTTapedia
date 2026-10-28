import Std

/-!
# Pinned Omega agent core

Executable observation model for singnet/Omega
94d7b9a2e1ef6b5873aee764ca1ef16de8dcd943, src/loop.metta and
src/providers.py.
This is the agent loop, not the UniversalAI Omega theory.

Host assumptions: configuration, channels, prompt assembly and tool execution
return their recorded values. Integer fixture-clock readings stand for the
source's get_time comparisons. Tool bodies remain opaque observations. The
source builds context before receiving input; its provider accepts structured
messages and tool specifications and returns ID-bearing calls. providers.py
contains provider exceptions as an empty response. File/embedding/plugin
behavior is outside these transition proofs and is checked by conformance.
-/

namespace OmegaArchitecture

structure Config where
  newInputLoops : Int := 50
  wakeLoops : Int := 1
  wakeInterval : Int := 600
  maxTokens : Nat := 6000
  reasoning : String := "medium"
deriving Repr, DecidableEq

structure State where
  loops : Int
  previous : String
  messages : List String
  history : List String
  nextWake : Option Int
deriving Repr, DecidableEq

/-- initLoop resets control; initMemory leaves persisted history available. -/
def boot (cfg : Config) (history : List String) : State :=
  ⟨cfg.newInputLoops, "", [], history, none⟩

/-- src/loop.metta: omega decrements on every k>1, including idle iterations.
The counter is signed: repeated idle ticks can make it negative. -/
def beginIteration (cfg : Config) (k : Nat) (state : State) :=
  if k = 1 then boot cfg state.history
  else { state with loops := state.loops - 1 }

/-- Receive returns the latest value. A repeated nonempty value is not novel. -/
def receivePhase (cfg : Config) (k : Nat) (state : State) (event : String) :
    State × Bool :=
  let initial := beginIteration cfg k state
  let novel := event != "" && event != initial.previous
  let received := { initial with
    previous := if event != "" then event else initial.previous }
  let armed := if k > 1 && novel then
    { received with loops := cfg.newInputLoops } else received
  (armed, novel)

/-- Selected property 1: duplicate input does not replenish the fast budget. -/
theorem duplicate_input_does_not_rearm (cfg : Config) (state : State)
    (k : Nat) (later : k ≠ 1) :
    (receivePhase cfg k state state.previous).2 = false ∧
      (receivePhase cfg k state state.previous).1.loops = state.loops - 1 := by
  simp [receivePhase, beginIteration, later]

/-- src/loop.metta: nextWakeAt is initialized before a provider invocation. -/
def armWake (cfg : Config) (state : State) (now : Int) :=
  { state with nextWake := some (now + cfg.wakeInterval) }

/-- Wake schedules maxWakeLoops+1 because the next iteration decrements first.
An unset wake deadline is retained as an explicit host/source precondition. -/
def idleWake (cfg : Config) (state : State) (now : Int) : State :=
  match state.nextWake with
  | none => state
  | some deadline =>
    if now > deadline then { state with loops := 1 + cfg.wakeLoops }
    else state

/-- Selected property 2: equality at the deadline does not wake the source. -/
theorem wake_is_strict (cfg : Config) (state : State) (deadline : Int)
    (set : state.nextWake = some deadline) :
    idleWake cfg state deadline = state ∧
      (idleWake cfg state (deadline + 1)).loops = 1 + cfg.wakeLoops := by
  have later : deadline < deadline + 1 := by omega
  simp [idleWake, set, later]

structure Request where
  context : String
  message : String
  priorMessages : List String
  tools : List String
  maxTokens : Nat
  reasoning : String
deriving Repr, DecidableEq

/-- Context is the pre-receive snapshot, supplied by the host observation. -/
def request (cfg : Config) (context message : String) (state : State)
    (tools : List String) : Request :=
  ⟨context, message, state.messages, tools, cfg.maxTokens, cfg.reasoning⟩

structure Call where
  id : String
  name : String
deriving Repr, DecidableEq

inductive Response where
  | calls (items : List Call) (response : String) (messages : List String)
  | responseError (feedback : String) (messages : List String)
  | providerFailure (reason : String) (messages : List String)
deriving Repr, DecidableEq

inductive Action where
  | providerRequest (request : Request)
  | dispatch (call : Call)
  | appendHistory (entry : String)
  | sleep
  | providerFailure (reason : String)
deriving Repr, DecidableEq

structure Transition where
  state : State
  actions : List Action
  halted : Bool
deriving Repr, DecidableEq

/-- The formatted history entry is an opaque observed string: memory.metta
records new input, response, timestamp and error feedback. -/
def finishActive (state : State) (req : Request) (novel : Bool)
    (response : Response) (historyEntry : String) : Transition :=
  match response with
  | .providerFailure reason messages =>
    -- providers.py catches the exception and supplies an empty LLMResponse;
    -- the loop reaches its ordinary history/sleep boundary with no invented
    -- call. A genuinely new human message is still retained.
    let next : State := { { state with messages := messages } with
      history := if novel then state.history ++ [historyEntry] else state.history }
    ⟨next, [.providerRequest req, .providerFailure reason] ++
      (if novel then [.appendHistory historyEntry] else []) ++ [.sleep], false⟩
  | .calls calls _response messages =>
    let keep := novel || !calls.isEmpty
    let next : State := { { state with messages := messages } with
      history := if keep then state.history ++ [historyEntry] else state.history }
    ⟨next, [.providerRequest req] ++ calls.map Action.dispatch ++
      (if keep then [.appendHistory historyEntry] else []) ++ [.sleep], false⟩
  | .responseError _feedback messages =>
    ⟨{ { state with messages := messages } with
         history := state.history ++ [historyEntry] },
      [.providerRequest req, .appendHistory historyEntry, .sleep], false⟩

def dispatches : List Action → List Call
  | [] => []
  | .dispatch command :: rest => command :: dispatches rest
  | _ :: rest => dispatches rest

theorem dispatches_map_append (calls : List Call) (suffix : List Action) :
    dispatches (calls.map Action.dispatch ++ suffix) = calls ++ dispatches suffix := by
  induction calls with
  | nil => rfl
  | cons head tail ih => simp [dispatches, ih]

/-- Selected property 3: provider containment invents no dispatch and reaches
the normal sleep boundary. -/
theorem provider_failure_is_contained (state : State)
    (req : Request) (novel : Bool) (reason historyEntry : String)
    (messages : List String) :
    let failed := finishActive state req novel (.providerFailure reason messages) historyEntry
    failed.halted = false ∧
      failed.state.history = (if novel then state.history ++ [historyEntry]
                              else state.history) ∧
      dispatches failed.actions = [] ∧ failed.actions.getLast? = some .sleep := by
  by_cases h : novel = true
  · simp [finishActive, dispatches, h]
  · simp [finishActive, dispatches, h]

/-- Selected property 4: structured dispatch preserves the provider call IDs
and order exactly. -/
theorem dispatch_preserves_call_ids (state : State) (req : Request)
    (novel : Bool) (calls : List Call) (response historyEntry : String)
    (messages : List String) :
    (dispatches (finishActive state req novel (.calls calls response messages)
      historyEntry).actions).map Call.id = calls.map Call.id := by
  by_cases keep : novel = true ∨ ¬ calls = []
  · simp [finishActive, dispatches_map_append, dispatches, keep]
  · simp [finishActive, dispatches_map_append, dispatches, keep]

/-- Actual core action order, excluding logging and heartbeat host observers. -/
def cycle (cfg : Config) (k : Nat) (state : State) (event context message : String)
    (tools : List String) (now : Int) (response : Response)
    (historyEntry : String) : Transition :=
  let (received, novel) := receivePhase cfg k state event
  if received.loops > 0 then
    let active := armWake cfg received now
    finishActive active (request cfg context message active tools) novel response historyEntry
  else ⟨idleWake cfg received now, [.sleep], false⟩

end OmegaArchitecture

#print axioms OmegaArchitecture.duplicate_input_does_not_rearm
#print axioms OmegaArchitecture.wake_is_strict
#print axioms OmegaArchitecture.provider_failure_is_contained
#print axioms OmegaArchitecture.dispatch_preserves_call_ids
