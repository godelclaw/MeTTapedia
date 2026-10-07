import Std

/-!
# Pinned Omega agent core

Executable observation model for singnet/Omega
ee0618a293ec3662a32b10b09c6cbb073f59d6b2, src/loop.metta.
This is the agent loop, not the UniversalAI Omega theory.

Host assumptions: configuration, channels, prompt assembly and command parsing
return their recorded values. Integer fixture-clock readings stand for the
source's get_time comparisons. Command bodies remain opaque observations.
The source builds context before receiving input; its provider accepts a
prompt string, token limit and reasoning mode, and returns command text.
Provider exceptions are uncaught. File/embedding/plugin behavior is outside
these transition proofs and is checked separately by conformance.
-/

namespace OmegaArchitecture

structure Config where
  newInputLoops : Int := 50
  wakeLoops : Int := 1
  wakeInterval : Int := 600
  maxTokens : Nat := 6000
  reasoning : String := "medium"
  spamShield : Bool := false
deriving Repr, DecidableEq

structure State where
  loops : Int
  previous : String
  lastResults : String
  history : List String
  nextWake : Option Int
deriving Repr, DecidableEq

/-- initLoop resets control; initMemory leaves persisted history available. -/
def boot (cfg : Config) (history : List String) : State :=
  ⟨cfg.newInputLoops, "", "", history, none⟩

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
  humanMessage : Option String
  spamReminder : Bool
  maxTokens : Nat
  reasoning : String
deriving Repr, DecidableEq

/-- Context is the pre-receive snapshot, supplied by the host observation. -/
def request (cfg : Config) (context : String) (state : State)
    (novel : Bool) : Request :=
  ⟨context, if novel then some state.previous else none,
    !novel && cfg.spamShield, cfg.maxTokens, cfg.reasoning⟩

inductive Response where
  | providerFailure (reason : String)
  | parsed (commands : List String) (response results : String)
  | parseFailure (response feedback : String)
deriving Repr, DecidableEq

inductive Action where
  | providerRequest (request : Request)
  | dispatch (command : String)
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
  | .providerFailure reason =>
    ⟨state, [.providerRequest req, .providerFailure reason], true⟩
  | .parsed commands _response results =>
    let keep := novel || !commands.isEmpty
    let next : State := { state with lastResults := results, history := if keep then state.history ++ [historyEntry] else state.history }
    ⟨next, [.providerRequest req] ++ commands.map Action.dispatch ++
      (if keep then [.appendHistory historyEntry] else []) ++ [.sleep], false⟩
  | .parseFailure _response feedback =>
    ⟨{ state with lastResults := feedback, history := state.history ++ [historyEntry] },
      [.providerRequest req, .appendHistory historyEntry, .sleep], false⟩

def dispatches : List Action → List String
  | [] => []
  | .dispatch command :: rest => command :: dispatches rest
  | _ :: rest => dispatches rest

/-- Selected property 3: a provider failure halts before dispatch or history
append; the source has no enclosing catch/retry around llmProviderChat. -/
theorem provider_failure_has_no_dispatch_or_history (state : State)
    (req : Request) (novel : Bool) (reason historyEntry : String) :
    let failed := finishActive state req novel (.providerFailure reason) historyEntry
    failed.halted = true ∧ failed.state.history = state.history ∧
      dispatches failed.actions = [] := by
  simp [finishActive, dispatches]

/-- Actual core action order, excluding logging and heartbeat host observers. -/
def cycle (cfg : Config) (k : Nat) (state : State) (event context : String)
    (now : Int) (response : Response) (historyEntry : String) : Transition :=
  let (received, novel) := receivePhase cfg k state event
  if received.loops > 0 then
    let active := armWake cfg received now
    finishActive active (request cfg context active novel) novel response historyEntry
  else ⟨idleWake cfg received now, [.sleep], false⟩

end OmegaArchitecture

#print axioms OmegaArchitecture.duplicate_input_does_not_rearm
#print axioms OmegaArchitecture.wake_is_strict
#print axioms OmegaArchitecture.provider_failure_has_no_dispatch_or_history
