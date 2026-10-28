import Std

/-!
# Common LLM request, completion and admission boundary

Messages, tool identities and opaque reasoning belong to the protocol. The
operator admission policy is separate and can be bypassed for upstream cores.
The model connects to CeTTa's `lib/llm.metta`, `lib/llm/io.metta` and
`lib/llm/compat.metta`, and the framework's `native_llm_host.py` and
`llm_policy.py`, through ordered protocol items, request handles and terminal
observations. Codec parsing, schema validation and cryptography are outside
this model. The projection gate models the additional checks required by a
caller that executes tools; the protocol library itself executes no tools.

The claims cover this executable model, not the correctness of C, provider
JSON decoders, cryptographic signatures or the external service. The host must
allocate distinct handles, correlate observations faithfully, serialize the
ledger transaction, and not retry HTTP inside one submitted request.
-/
namespace MeTTaClaw.LlmBoundary

inductive Role where
  | system | developer | user | assistant | tool
  deriving DecidableEq, Repr

structure ToolCall where
  id : String
  name : String
  argumentsJson : String
  deriving DecidableEq, Repr

inductive Protocol where
  | chatCompletions | responses | anthropic
  deriving DecidableEq, Repr

structure NativeAttachment where
  protocol : Protocol
  version : String
  payload : String
  deriving DecidableEq, Repr

inductive CallStatus where
  | completed | incomplete | unknown
  deriving DecidableEq, Repr

inductive Part where
  | text (bytes : String)
  | refusal (bytes : String)
  | tool (call : ToolCall) (status : CallStatus)
  | reasoning (native : NativeAttachment)
  | opaque (native : NativeAttachment)
  deriving DecidableEq, Repr

inductive Item where
  | message (role : Role) (parts : List Part)
  | tool (call : ToolCall) (status : CallStatus)
  | reasoning (native : NativeAttachment)
  | opaque (native : NativeAttachment)
  deriving DecidableEq, Repr

structure Message where
  role : Role
  text : String
  calls : List ToolCall := []
  toolResultFor : Option String := none
  opaqueReasoning : List String := []
  orderedParts : List Part := []
  deriving DecidableEq, Repr

structure Request where
  correlation : Nat
  messages : List Message
  maxOutput : Nat
  effort : Option String
  deriving DecidableEq, Repr

structure Handle where
  epoch : Nat
  transport : Nat
  deriving DecidableEq, Repr

structure Usage where
  input : Option Nat
  output : Option Nat
  cached : Option Nat
  reasoning : Option Nat
  cacheWrite : Option Nat := none
  deriving DecidableEq, Repr

inductive Completion where
  | answered (message : Message) (usage : Usage)
  | truncated (partialMessage : Message) (usage : Usage)
  | failed (kind : String)
  | cancelled
  deriving DecidableEq, Repr

inductive Phase where
  | idle
  | pending (request : Request) (handle : Handle)
  | terminal (request : Request) (handle : Handle) (result : Completion)
  deriving DecidableEq, Repr

structure Observation where
  handle : Handle
  result : Completion
  deriving DecidableEq, Repr

def observe (state : Phase) (event : Observation) : Phase :=
  match state with
  | .pending request handle =>
      if event.handle = handle then .terminal request handle event.result else state
  | _ => state

def delivers (state : Phase) (event : Observation) : Bool :=
  match state with
  | .pending _ handle => decide (event.handle = handle)
  | _ => false

theorem terminal_is_stable (request : Request) (handle : Handle)
    (result : Completion) (event : Observation) :
    observe (.terminal request handle result) event = .terminal request handle result := rfl

theorem wrong_handle_is_ignored (request : Request) (handle : Handle)
    (event : Observation) (different : event.handle ≠ handle) :
    observe (.pending request handle) event = .pending request handle := by
  simp [observe, different]

theorem completion_is_idempotent (state : Phase) (event : Observation) :
    observe (observe state event) event = observe state event := by
  cases state with
  | idle => rfl
  | terminal => rfl
  | pending request handle =>
      by_cases h : event.handle = handle <;> simp [observe, h]

theorem delivered_once (state : Phase) (event : Observation)
    (accepted : delivers state event = true) :
    delivers (observe state event) event = false := by
  cases state with
  | idle => simp [delivers] at accepted
  | terminal => simp [delivers] at accepted
  | pending request handle =>
      have same : event.handle = handle := of_decide_eq_true accepted
      simp [observe, delivers, same]

-- Count delivery transitions over arbitrary traces, including repeated and
-- foreign observations. Terminal data may be read repeatedly without another
-- transition that delivers it to a caller.
def deliveryCount : Phase → List Observation → Nat
  | _, [] => 0
  | state, event :: rest =>
      (if delivers state event then 1 else 0) + deliveryCount (observe state event) rest

theorem terminal_deliveryCount_zero (request : Request) (handle : Handle)
    (result : Completion) (events : List Observation) :
    deliveryCount (.terminal request handle result) events = 0 := by
  induction events with
  | nil => rfl
  | cons event rest ih => simpa [deliveryCount, delivers, observe] using ih

theorem deliveryCount_at_most_one (state : Phase) (events : List Observation) :
    deliveryCount state events ≤ 1 := by
  induction events generalizing state with
  | nil => simp [deliveryCount]
  | cons event rest ih =>
      cases state with
      | idle => simpa [deliveryCount, delivers, observe] using ih .idle
      | terminal request handle result =>
          simp [terminal_deliveryCount_zero]
      | pending request handle =>
          by_cases same : event.handle = handle
          · simp [deliveryCount, delivers, observe, same, terminal_deliveryCount_zero]
          · simpa [deliveryCount, delivers, observe, same] using ih (.pending request handle)

-- Handle-specific dequeue is the native worker's ownership boundary. Finding
-- one consumer's reply preserves every other consumer's ordered queue.
def takeOwned (handle : Handle) : List Observation → Option Observation × List Observation
  | [] => (none, [])
  | event :: rest =>
      if event.handle = handle then (some event, rest)
      else let next := takeOwned handle rest
           (next.1, event :: next.2)

def foreignEvents (handle : Handle) (events : List Observation) : List Observation :=
  events.filter (fun event => decide (event.handle ≠ handle))

theorem owned_dequeue_preserves_foreign_order (handle : Handle) (events : List Observation) :
    foreignEvents handle (takeOwned handle events).2 = foreignEvents handle events := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      by_cases same : event.handle = handle
      · simp [takeOwned, foreignEvents, same]
      · simpa [takeOwned, foreignEvents, same] using congrArg (List.cons event) ih

inductive Stop where
  | stop | toolCalls | length | refusal | failed | unknown
  deriving DecidableEq, Repr

structure OrderedResult where
  protocol : Protocol
  version : String
  items : List Item
  stop : Stop
  usage : Usage
  deriving DecidableEq, Repr

def completeStop : Stop → Bool
  | .stop | .toolCalls => true
  | _ => false

def replayTo (protocol : Protocol) (version : String) (result : OrderedResult) :
    Option (List Item) :=
  if result.protocol = protocol ∧ result.version = version ∧ completeStop result.stop = true
  then some result.items else none

theorem replay_preserves_order_and_payload (protocol : Protocol) (version : String)
    (result : OrderedResult) (items : List Item)
    (accepted : replayTo protocol version result = some items) : items = result.items := by
  unfold replayTo at accepted
  split at accepted
  · exact (Option.some.inj accepted).symm
  · contradiction

theorem cross_protocol_replay_rejected (protocol : Protocol) (version : String)
    (result : OrderedResult) (different : result.protocol ≠ protocol) :
    replayTo protocol version result = none := by
  simp [replayTo, different]

def partReady : Part → Bool
  | .tool _ status => decide (status = .completed)
  | .opaque _ => false
  | _ => true

def itemReady : Item → Bool
  | .message _ parts => parts.all partReady
  | .tool _ status => decide (status = .completed)
  | .opaque _ => false
  | _ => true

def partCalls : Part → List ToolCall
  | .tool call _ => [call]
  | _ => []

def itemCalls : Item → List ToolCall
  | .message _ parts => parts.flatMap partCalls
  | .tool call _ => [call]
  | _ => []

-- Validating arguments against a provider schema is a caller obligation. This
-- gate prevents a partial/unknown item or an unfinished completion from being
-- treated as a completed tool batch. IDs and argument bytes are unchanged.
def dispatchProjection (result : OrderedResult) : Option (List ToolCall) :=
  if completeStop result.stop && result.items.all itemReady
  then some (result.items.flatMap itemCalls) else none

theorem truncated_response_cannot_dispatch (result : OrderedResult)
    (truncated : result.stop = .length) : dispatchProjection result = none := by
  simp [dispatchProjection, truncated, completeStop]

theorem unfinished_batch_cannot_dispatch (result : OrderedResult)
    (unfinished : result.items.all itemReady = false) : dispatchProjection result = none := by
  simp [dispatchProjection, unfinished]

theorem dispatch_preserves_call_identities (result : OrderedResult) (calls : List ToolCall)
    (accepted : dispatchProjection result = some calls) :
    calls.map ToolCall.id = (result.items.flatMap itemCalls).map ToolCall.id := by
  unfold dispatchProjection at accepted
  split at accepted
  · exact congrArg (List.map ToolCall.id) (Option.some.inj accepted).symm
  · contradiction

inductive Profile where
  | upstream | managed
  deriving DecidableEq, Repr

structure Limits where
  -- Zero disables a cap, matching the operator configuration.
  requests : Nat
  output : Nat
  deriving DecidableEq, Repr

structure Accounting where
  requests : Nat
  reservedAndUsedOutput : Nat
  deriving DecidableEq, Repr

def admitted (profile : Profile) (limit : Limits) (used : Accounting)
    (request : Request) : Bool :=
  match profile with
  | .upstream => true
  | .managed => decide
      ((limit.requests = 0 ∨ used.requests + 1 ≤ limit.requests) ∧
       (limit.output = 0 ∨ used.reservedAndUsedOutput + request.maxOutput ≤ limit.output))

def reserve (used : Accounting) (request : Request) : Accounting :=
  { requests := used.requests + 1
    reservedAndUsedOutput := used.reservedAndUsedOutput + request.maxOutput }

theorem upstream_adds_no_budget (limit : Limits) (used : Accounting) (request : Request) :
    admitted .upstream limit used request = true := rfl

theorem managed_reservation_preserves_caps (limit : Limits) (used : Accounting)
    (request : Request) (accepted : admitted .managed limit used request = true) :
    (limit.requests = 0 ∨ (reserve used request).requests ≤ limit.requests) ∧
    (limit.output = 0 ∨ (reserve used request).reservedAndUsedOutput ≤ limit.output) := by
  simpa [admitted, reserve] using accepted

-- A lost reply is not evidence of zero billable output. Only a known terminal
-- usage observation can release part of a reservation.
def releaseUnused (reserved : Nat) (knownOutput : Option Nat) : Nat :=
  match knownOutput with
  | none => reserved
  | some output => output

theorem uncertain_request_keeps_reservation (reserved : Nat) :
    releaseUnused reserved none = reserved := rfl

theorem observed_usage_refines_reservation (reserved output : Nat)
    (hostBound : output ≤ reserved) : releaseUnused reserved (some output) ≤ reserved := by
  exact hostBound

-- The same boundary observations used by the native fixture: a foreign event,
-- a matching completion, then its duplicate. Neither foreign nor duplicate
-- completion delivers a second answer.
def fixtureRequest : Request := ⟨17, [], 42, some "low"⟩
def fixtureHandle : Handle := ⟨1, 7⟩
def fixtureForeign : Observation := ⟨⟨1, 8⟩, .failed "foreign"⟩
def fixtureCompletion : Observation := ⟨fixtureHandle, .failed "fixture"⟩

example : observe (.pending fixtureRequest fixtureHandle) fixtureForeign =
    .pending fixtureRequest fixtureHandle := by decide
example : delivers (.pending fixtureRequest fixtureHandle) fixtureCompletion = true := by decide
example : delivers (observe (.pending fixtureRequest fixtureHandle) fixtureCompletion)
    fixtureCompletion = false := by decide

example : deliveryCount (.pending fixtureRequest fixtureHandle)
    [fixtureForeign, fixtureCompletion, fixtureCompletion] = 1 := by decide
example : (takeOwned fixtureHandle [fixtureForeign, fixtureCompletion]).2 =
    [fixtureForeign] := by decide

def fixtureUsage : Usage := ⟨some 9, some 3, some 7, none, none⟩
def fixtureNative : NativeAttachment := ⟨.anthropic, "2023-06-01", "signed-fixture"⟩
def fixtureCall : ToolCall := ⟨"call-a", "nop", "{}"⟩
def fixtureResult : OrderedResult :=
  ⟨.anthropic, "2023-06-01", [.message .assistant
    [.reasoning fixtureNative, .text "before", .tool fixtureCall .completed, .text "after"]],
   .toolCalls, fixtureUsage⟩

example : replayTo .anthropic "2023-06-01" fixtureResult = some fixtureResult.items := by decide
example : dispatchProjection fixtureResult = some [fixtureCall] := by decide
example : dispatchProjection { fixtureResult with stop := .length } = none := by decide
example : dispatchProjection { fixtureResult with items := [.tool fixtureCall .incomplete] } = none := by decide

#print axioms completion_is_idempotent
#print axioms delivered_once
#print axioms managed_reservation_preserves_caps
#print axioms deliveryCount_at_most_one
#print axioms owned_dequeue_preserves_foreign_order
#print axioms replay_preserves_order_and_payload
#print axioms dispatch_preserves_call_identities

end MeTTaClaw.LlmBoundary
