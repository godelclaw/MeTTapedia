import Mettapedia.Languages.MeTTa.HE.NativeArgumentControlMachine
import Mettapedia.GSLT.Distinction.SimulationComposition

/-!
# Lossless data for retained argument control

The decoder retains all argument phases, parent selections, pending service
continuations, answer occurrences, reply identities and work accounts. A
request endpoint is tied to that entire configuration. Structural identity
prevents splicing replies between different retained endpoints; it does not
provide cryptographic authenticity or establish native ownership.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeArgumentControlEncoding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeArgumentControl
open TypedApplyEncoding (readState readBindings readResults readIndex)
open NativeArgumentProjection (readSnapshot)

def readParent : Atom → Option Parent
  | .expression [.symbol "only", state, prepared, value, bindings] => do
      return .only (← readState state) (← readPrepared prepared) value (← readBindings bindings)
  | .expression [.symbol "alternatives", saved, prepared] => do
      return .alternatives (← readSnapshot saved) (← readPrepared prepared)
  | _ => none

@[simp] theorem readParent_parentData (parent : Parent) :
    readParent (parentData parent) = some parent := by
  cases parent <;> simp [readParent, parentData]

def readWaiting : Atom → Option Waiting
  | .expression [.symbol "prepare", state] => do return .prepare (← readState state)
  | .expression [.symbol "transform", state, prepared] => do
      return .transform (← readState state) (← readPrepared prepared)
  | .expression [.symbol "evaluate", state, prepared] => do
      return .evaluate (← readState state) (← readPrepared prepared)
  | .expression [.symbol "resume-evaluation", state, prepared, continuation, reply] => do
      return .resumeEvaluation (← readState state) (← readPrepared prepared) continuation reply
  | .expression [.symbol "effect", state, prepared, continuation, request] => do
      return .effect (← readState state) (← readPrepared prepared) continuation request
  | .expression [.symbol "continuation", child, parent] => do
      return .continuation (← readState child) (← readParent parent)
  | _ => none

@[simp] theorem readWaiting_waitingData (waiting : Waiting) :
    readWaiting (waitingData waiting) = some waiting := by
  cases waiting <;> simp [readWaiting, waitingData]

def readFrame : Atom → Option Frame
  | .expression [.symbol "enter", state] => do return .enter (← readState state)
  | .expression [.symbol "prepared", state, prepared] => do
      return .prepared (← readState state) (← readPrepared prepared)
  | .expression [.symbol "raw-ready", state, prepared, value] => do
      return .rawReady (← readState state) (← readPrepared prepared) value
  | .expression [.symbol "iterate", saved, prepared] => do
      return .iterate (← readSnapshot saved) (← readPrepared prepared)
  | .expression [.symbol "after-iter-child", saved, prepared] => do
      return .afterIterChild (← readSnapshot saved) (← readPrepared prepared)
  | .expression [.symbol "after-only-child", state, prepared, value, bindings] => do
      return .afterOnlyChild (← readState state) (← readPrepared prepared) value (← readBindings bindings)
  | .expression [.symbol "waiting", service, ticket] => do
      return .waiting (← readWaiting service) (← readIndex ticket)
  | _ => none

@[simp] theorem readFrame_frameData (frame : Frame) : readFrame (frameData frame) = some frame := by
  cases frame <;> simp [readFrame, frameData]

private theorem read_map (frames : List Frame) :
    (frames.map frameData).mapM readFrame = some frames := by
  induction frames with
  | nil => rfl
  | cons first rest ih => simp [ih]

private theorem read_indices (serials : List Nat) :
    (serials.map TypedApplyEncoding.index).mapM readIndex = some serials := by
  induction serials with
  | nil => rfl
  | cons first rest ih => simp [ih]

def readConfiguration : Atom → Option Configuration
  | .expression [.symbol "he-native-argument-control-v1", .expression frames,
      emitted, episode, nextTicket, .expression replies, work] => do
      return ⟨← frames.mapM readFrame, ← readResults emitted, ← readIndex episode,
        ← readIndex nextTicket, ← replies.mapM readIndex, ← readIndex work⟩
  | _ => none

@[simp] theorem readConfiguration_configurationData (state : Configuration) :
    readConfiguration (configurationData state) = some state := by
  cases state
  simp only [configurationData, readConfiguration]
  rw [read_map]
  simp only [TypedApplyEncoding.readResults_resultsData, TypedApplyEncoding.readIndex_index]
  rw [read_indices]
  simp

theorem configurationData_injective : Function.Injective configurationData := by
  intro left right equal
  have decoded := congrArg readConfiguration equal
  simpa using decoded

def readEndpoint : Atom → Option (Nat × Waiting × Configuration)
  | .expression [.symbol "he-native-argument-request-v1", ticket, service, configuration] => do
      return (← readIndex ticket, ← readWaiting service, ← readConfiguration configuration)
  | _ => none

@[simp] theorem readEndpoint_request (state : Configuration) (service : Waiting) (ticket : Nat) :
    readEndpoint (request state service ticket).endpoint = some (ticket, service, state) := by
  simp [request, readEndpoint]

theorem request_endpoint_injective {left right : Configuration} {one two : Waiting} {a b : Nat}
    (same : (request left one a).endpoint = (request right two b).endpoint) :
    a = b ∧ one = two ∧ left = right := by
  have decoded := congrArg readEndpoint same
  simpa using decoded

/-- An endpoint from a different complete saved configuration is rejected,
even if its ticket and service shape have been copied. -/
theorem different_endpoint_rejected (state other : Configuration) (service sourceService : Waiting)
    (ticket sourceTicket : Nat) (rest : List Frame) (value : ReplyValue) (charge : Nat)
    (pending : state.frames = .waiting service ticket :: rest) (different : other ≠ state) :
    deliver state ⟨(request other sourceService sourceTicket).endpoint, value, charge⟩ =
      .rejected .endpointMismatch := by
  have mismatch : (request other sourceService sourceTicket).endpoint ≠ (request state service ticket).endpoint := by
    intro same
    exact different (request_endpoint_injective same).2.2
  simp [deliver, pending, mismatch]

/-- An accepted reply changes the saved endpoint. Even a fresh service of
the same kind cannot accept the old reply a second time. -/
theorem duplicate_reply_rejected {state after : Configuration} {reply : Reply}
    (accepted : deliver state reply = .accepted after) (next : Configuration) :
    deliver after reply ≠ .accepted next := by
  intro repeated
  obtain ⟨tickets, _, _, _⟩ := delivery_accounts accepted
  have stateDiff : state ≠ after := by
    intro same
    rw [same] at tickets
    omega
  cases (deliver_iff _ _ _).mp accepted with
  | accepted service ticket rest events frames pending endpoint body =>
    cases (deliver_iff _ _ _).mp repeated with
    | accepted nextService nextTicket nextRest nextEvents nextFrames nextPending nextEndpoint nextBody =>
      have same := endpoint.symm.trans nextEndpoint
      exact stateDiff (request_endpoint_injective same).2.2

/-! ## Checked replies and retained interaction packets -/

open NativeArgumentControlMachine
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def replyValueData : ReplyValue → Atom
  | .prepared prepared => .expression [.symbol "prepared", preparedData prepared]
  | .transformed (.value value) => .expression [.symbol "transformed-value", value]
  | .transformed .dropped => .expression [.symbol "transformed-dropped"]
  | .transformed (.error result) => .expression [.symbol "transformed-error", TypedApplyEncoding.resultData result]
  | .evaluated results => .expression [.symbol "evaluated", TypedApplyEncoding.resultsData results]
  | .collectorUnavailable => .expression [.symbol "collector-unavailable"]
  | .effectRequired continuation effect => .expression [.symbol "effect-required", continuation, effect]
  | .effectReturned value => .expression [.symbol "effect-returned", value]
  | .continuationEntered => .expression [.symbol "continuation-entered"]
  | .continuationCancelled => .expression [.symbol "continuation-cancelled"]

def readReplyValue : Atom → Option ReplyValue
  | .expression [.symbol "prepared", prepared] => (readPrepared prepared).map ReplyValue.prepared
  | .expression [.symbol "transformed-value", value] => some (.transformed (.value value))
  | .expression [.symbol "transformed-dropped"] => some (.transformed .dropped)
  | .expression [.symbol "transformed-error", result] =>
      (TypedApplyEncoding.readResult result).map (fun result => .transformed (.error result))
  | .expression [.symbol "evaluated", results] => (readResults results).map ReplyValue.evaluated
  | .expression [.symbol "collector-unavailable"] => some .collectorUnavailable
  | .expression [.symbol "effect-required", continuation, effect] => some (.effectRequired continuation effect)
  | .expression [.symbol "effect-returned", value] => some (.effectReturned value)
  | .expression [.symbol "continuation-entered"] => some .continuationEntered
  | .expression [.symbol "continuation-cancelled"] => some .continuationCancelled
  | _ => none

@[simp] theorem readReplyValue_replyValueData (value : ReplyValue) :
    readReplyValue (replyValueData value) = some value := by
  cases value with
  | prepared prepared => simp only [replyValueData, readReplyValue, readPrepared_preparedData, Option.map_some]
  | transformed result =>
      cases result with
      | value | dropped => rfl
      | error result => simp only [replyValueData, readReplyValue,
          TypedApplyEncoding.readResult_resultData, Option.map_some]
  | evaluated results => simp only [replyValueData, readReplyValue,
      TypedApplyEncoding.readResults_resultsData, Option.map_some]
  | _ => rfl

def replyData (reply : NativeArgumentControl.Reply) : Atom :=
  .expression [.symbol "he-native-argument-reply-v1", reply.endpoint,
    replyValueData reply.value, TypedApplyEncoding.index reply.charge]

def readReply : Atom → Option NativeArgumentControl.Reply
  | .expression [.symbol "he-native-argument-reply-v1", endpoint, value, charge] => do
      return ⟨endpoint, ← readReplyValue value, ← readIndex charge⟩
  | _ => none

@[simp] theorem readReply_replyData (reply : NativeArgumentControl.Reply) :
    readReply (replyData reply) = some reply := by
  cases reply
  simp only [replyData, readReply, readReplyValue_replyValueData,
    TypedApplyEncoding.readIndex_index, bind, Option.bind_some, pure]

theorem replyData_injective : Function.Injective replyData := by
  intro left right encoded
  have decoded := congrArg readReply encoded
  simpa only [readReply_replyData, Option.some.injEq] using decoded

def readRejection : Atom → Option Rejection
  | .symbol "no-pending" => some .noPending
  | .symbol "endpoint-mismatch" => some .endpointMismatch
  | .symbol "wrong-kind" => some .wrongKind
  | _ => none

@[simp] theorem readRejection_rejectionData (reason : Rejection) :
    readRejection (rejectionData reason) = some reason := by cases reason <;> rfl

def readInteraction : Atom → Option Interaction
  | .expression [.symbol "he-native-argument-interaction-v1", .symbol "active", saved] =>
      (readConfiguration saved).map Interaction.active
  | .expression [.symbol "he-native-argument-interaction-v1", .symbol "refused", reason, saved, reply] => do
      return .refused (← readRejection reason) (← readConfiguration saved) reply
  | .expression [.symbol "he-native-argument-interaction-v1", .symbol "malformed-reply", saved, reply] =>
      (readConfiguration saved).map (fun saved => .malformedReply saved reply)
  | .expression [.symbol "he-native-argument-interaction-v1", .symbol "callback-fault", saved, failure] =>
      (readConfiguration saved).map (fun saved => .callbackFault saved failure)
  | .expression [.symbol "he-native-argument-interaction-v1", .symbol "cancelled", saved] =>
      (readConfiguration saved).map Interaction.cancelled
  | _ => none

@[simp] theorem readInteraction_interactionData (saved : Interaction) :
    readInteraction (interactionData saved) = some saved := by
  cases saved <;> simp only [interactionData, readInteraction,
    readConfiguration_configurationData, readRejection_rejectionData, Option.map_some,
    bind, Option.bind_some, pure]

theorem interactionData_injective : Function.Injective interactionData := by
  intro left right encoded
  have decoded := congrArg readInteraction encoded
  simpa only [readInteraction_interactionData, Option.some.injEq] using decoded

abbrev ProtocolReply := Mettapedia.GSLT.Distinction.ProductiveBlocks.Reply Atom Atom

/-- Raw replies are decoded and checked by the actual endpoint consumer.
Refusals retain the entire saved controller, including consumed serials and
external work. Only an accepted reply can install its result or a new child. -/
def resumeInteraction (saved : Interaction) (answer : ProtocolReply) : Interaction :=
  match saved with
  | .active state => match answer with
      | .returned data => match readReply data with
          | none => .malformedReply state data
          | some reply => match deliver state reply with
              | .accepted next => .active next
              | .rejected reason => .refused reason state data
      | .faulted failure => .callbackFault state failure
      | .cancelled => .cancelled state
  | other => other

/-- The represented consumer reads complete packet states, checks raw reply
syntax and invokes the existing endpoint checker. Malformed configuration
data is retained; it cannot become an accepted controller configuration. -/
def resumeInteractionData (saved : Atom) (answer : ProtocolReply) : Atom :=
  match readInteraction saved with
  | some (.active state) => match answer with
      | .returned data => match readReply data with
          | none => interactionData (.malformedReply state data)
          | some reply => match deliver state reply with
              | .accepted next => interactionData (.active next)
              | .rejected reason => interactionData (.refused reason state data)
      | .faulted failure => interactionData (.callbackFault state failure)
      | .cancelled => interactionData (.cancelled state)
  | _ => saved

theorem resumeInteraction_encoded (saved : Interaction) (answer : ProtocolReply) :
    resumeInteractionData (interactionData saved) answer = interactionData (resumeInteraction saved answer) := by
  cases saved <;> simp only [resumeInteractionData, readInteraction_interactionData, resumeInteraction]
  case active state =>
    cases answer <;> try rfl
    case returned data =>
      cases decoded : readReply data with
      | none => simp only [decoded]
      | some reply =>
          simp only [decoded]
          cases deliver state reply <;> rfl

theorem returned_reply_accepted_iff (saved after : Configuration) (reply : NativeArgumentControl.Reply) :
    resumeInteraction (.active saved) (.returned (replyData reply)) = .active after ↔
      DeliveryRel saved reply after := by
  simp only [resumeInteraction, readReply_replyData]
  rw [← deliver_iff]
  cases delivered : deliver saved reply <;> simp only [Interaction.active.injEq, Delivery.accepted.injEq,
    reduceCtorEq]

/-- Acceptance of arbitrary external data requires both successful decoding
and the independent delivery judgment for this complete retained endpoint. -/
theorem raw_reply_accepted_iff (saved after : Configuration) (data : Atom) :
    resumeInteraction (.active saved) (.returned data) = .active after ↔
      ∃ reply, readReply data = some reply ∧ DeliveryRel saved reply after := by
  cases decoded : readReply data with
  | none =>
      simp only [resumeInteraction, decoded, reduceCtorEq, false_iff]
      rintro ⟨reply, accepted, _⟩
      cases accepted
  | some reply =>
      have delivery :
          (match deliver saved reply with
            | .accepted next => Interaction.active next
            | .rejected reason => .refused reason saved data) = .active after ↔
          DeliveryRel saved reply after := by
        rw [← deliver_iff]
        cases delivered : deliver saved reply <;>
          simp only [Interaction.active.injEq, Delivery.accepted.injEq, reduceCtorEq]
      simp only [resumeInteraction, decoded, Option.some.injEq]
      rw [delivery]
      constructor
      · intro admitted
        exact ⟨reply, rfl, admitted⟩
      · rintro ⟨actual, rfl, admitted⟩
        exact admitted

theorem represented_reply_accepted_iff (saved after : Configuration) (reply : NativeArgumentControl.Reply) :
    resumeInteractionData (interactionData (.active saved)) (.returned (replyData reply)) =
      interactionData (.active after) ↔ DeliveryRel saved reply after := by
  rw [resumeInteraction_encoded, interactionData_injective.eq_iff]
  exact returned_reply_accepted_iff saved after reply

theorem rejected_reply_retains_saved (saved : Configuration) (reply : NativeArgumentControl.Reply)
    (reason : Rejection) (rejected : deliver saved reply = .rejected reason) :
    resumeInteraction (.active saved) (.returned (replyData reply)) = .refused reason saved (replyData reply) ∧
    resumeInteractionData (interactionData (.active saved)) (.returned (replyData reply)) =
      interactionData (.refused reason saved (replyData reply)) := by
  have source : resumeInteraction (.active saved) (.returned (replyData reply)) =
      .refused reason saved (replyData reply) := by
    simp only [resumeInteraction, readReply_replyData, rejected]
  exact ⟨source, by rw [resumeInteraction_encoded, source]⟩

theorem accepted_reply_preserves_accounts (saved after : Configuration) (reply : NativeArgumentControl.Reply)
    (accepted : resumeInteractionData (interactionData (.active saved)) (.returned (replyData reply)) =
      interactionData (.active after)) :
    after.nextTicket = saved.nextTicket + 1 ∧
      after.replyHistory = saved.replyHistory ++ [pendingTicket saved] ∧
      after.externalWork = saved.externalWork + reply.charge ∧ after.episode = saved.episode := by
  have earned := (represented_reply_accepted_iff saved after reply).mp accepted
  exact delivery_accounts ((deliver_iff saved reply after).mpr earned)

def callEventData (endpoint : Atom) : Atom := .expression [.symbol "service-call", endpoint]

def replyEventData : ProtocolReply → Atom
  | .returned data => .expression [.symbol "service-returned", data]
  | .faulted failure => .expression [.symbol "service-faulted", failure]
  | .cancelled => .expression [.symbol "service-cancelled"]

def interactionCallback : Callback Interaction Atom Atom Atom Atom :=
  ⟨callEventData, replyEventData, resumeInteraction⟩

def representedCallback : Callback Atom Atom Atom Atom Atom :=
  ⟨callEventData, replyEventData, resumeInteractionData⟩

def InteractionRelated (source : Interaction) (data : Atom) : Prop := interactionData source = data

theorem callbacks_resume_related {saved : Interaction} {data : Atom}
    (related : InteractionRelated saved data) (answer : ProtocolReply) :
    InteractionRelated (interactionCallback.resume saved answer) (representedCallback.resume data answer) := by
  subst data
  exact (resumeInteraction_encoded saved answer).symm

/-- Lift retained configurations through protocol transitions. Verdicts and
events are already data; request endpoints retain the complete controller. -/
def encodeInteractionAdvance {Request : Type} :
    Transition Interaction Atom Atom Request → Transition Atom Atom Atom Request
  | .silent next => .silent (interactionData next)
  | .publish events next => .publish events (interactionData next)
  | .finish verdict => .finish verdict
  | .fail events => .fail events
  | .call request saved => .call request (interactionData saved)

/-- The executable packet interface has an explicit malformed-state verdict.
Decoding a packet supplies no historical or external-effect authority. -/
def interactionDataMachine (operations : Operations) (policy : RefusalPolicy) : Machine Atom Atom Atom Atom where
  step data := match readInteraction data with
    | none => some (.finish (.expression [.symbol "malformed-interaction", data]))
    | some (.active saved) => some (encodeInteractionAdvance (interactionAdvance (inspect operations saved)))
    | some (.refused reason saved reply) => match policy with
        | .stop => some (.finish (interactionData (.refused reason saved reply)))
        | .retry => some (.silent (interactionData (.active saved)))
    | some (.malformedReply saved reply) => match policy with
        | .stop => some (.finish (interactionData (.malformedReply saved reply)))
        | .retry => some (.silent (interactionData (.active saved)))
    | some (.callbackFault saved failure) => some (.finish (interactionData (.callbackFault saved failure)))
    | some (.cancelled saved) => some (.finish (interactionData (.cancelled saved)))

theorem interaction_step_encoded (operations : Operations) (policy : RefusalPolicy) (saved : Interaction) :
    (interactionDataMachine operations policy).step (interactionData saved) =
      ((interactionMachine operations policy).step saved).map encodeInteractionAdvance := by
  cases saved <;> simp only [interactionDataMachine, readInteraction_interactionData,
    interactionMachine, inspectInteraction, Option.map_some, encodeInteractionAdvance]
  case refused => cases policy <;> rfl
  case malformedReply => cases policy <;> rfl

theorem interaction_forward (operations : Operations) (policy : RefusalPolicy) :
    CostSimulation (interactionMachine operations policy) (interactionDataMachine operations policy) InteractionRelated 1 where
  silent := by
    intro source data next related stepped
    change interactionData source = data at related
    rw [← related]
    have encoded := interaction_step_encoded operations policy source
    rw [stepped] at encoded
    simp only [Option.map_some, encodeInteractionAdvance] at encoded
    exact ⟨1, le_rfl, interactionData next,
      (interactionDataMachine operations policy).run_succ_silent (fuel := 0) encoded, rfl⟩
  publish := by
    intro source data events next related stepped
    change interactionData source = data at related
    rw [← related]
    have encoded := interaction_step_encoded operations policy source
    rw [stepped] at encoded
    simp only [Option.map_some, encodeInteractionAdvance] at encoded
    refine ⟨1, le_rfl, interactionData next, ?_, rfl⟩
    simpa only [Machine.run, List.append_nil] using
      (interactionDataMachine operations policy).run_succ_publish (fuel := 0) encoded
  finish := by
    intro source data verdict related stepped
    change interactionData source = data at related
    rw [← related]
    have encoded := interaction_step_encoded operations policy source
    rw [stepped] at encoded
    simp only [Option.map_some, encodeInteractionAdvance] at encoded
    exact ⟨1, le_rfl, (interactionDataMachine operations policy).run_succ_finish (fuel := 0) encoded⟩
  fail := by
    intro source data events related stepped
    change interactionData source = data at related
    rw [← related]
    have encoded := interaction_step_encoded operations policy source
    rw [stepped] at encoded
    simp only [Option.map_some, encodeInteractionAdvance] at encoded
    exact ⟨1, le_rfl, (interactionDataMachine operations policy).run_succ_fail (fuel := 0) encoded⟩
  call := by
    intro source data request saved related stepped
    change interactionData source = data at related
    rw [← related]
    have encoded := interaction_step_encoded operations policy source
    rw [stepped] at encoded
    simp only [Option.map_some, encodeInteractionAdvance] at encoded
    exact ⟨1, le_rfl, interactionData saved,
      (interactionDataMachine operations policy).run_succ_call (fuel := 0) encoded, rfl⟩

theorem interaction_backward (operations : Operations) (policy : RefusalPolicy) :
    CostSimulation (interactionDataMachine operations policy) (interactionMachine operations policy)
      (fun data source => InteractionRelated source data) 1 where
  silent := by
    intro data source nextData related stepped
    change interactionData source = data at related
    rw [← related] at stepped
    rw [interaction_step_encoded] at stepped
    cases found : (interactionMachine operations policy).step source with
    | none => rw [found] at stepped; cases stepped
    | some transition =>
        rw [found] at stepped
        cases transition with
        | silent next =>
            have same : interactionData next = nextData := by
              simpa only [Option.map_some, encodeInteractionAdvance, Option.some.injEq,
                Transition.silent.injEq] using stepped
            rw [← same]
            exact ⟨1, le_rfl, next, (interactionMachine operations policy).run_succ_silent (fuel := 0) found, rfl⟩
        | publish events next | finish verdict | fail events | call request saved => cases stepped
  publish := by
    intro data source events nextData related stepped
    change interactionData source = data at related
    rw [← related] at stepped
    rw [interaction_step_encoded] at stepped
    cases found : (interactionMachine operations policy).step source with
    | none => rw [found] at stepped; cases stepped
    | some transition =>
        rw [found] at stepped
        cases transition with
        | publish actualEvents next =>
            have same : actualEvents = events ∧ interactionData next = nextData := by
              simpa only [Option.map_some, encodeInteractionAdvance, Option.some.injEq,
                Transition.publish.injEq] using stepped
            rw [← same.1, ← same.2]
            refine ⟨1, le_rfl, next, ?_, rfl⟩
            simpa only [Machine.run, List.append_nil] using
              (interactionMachine operations policy).run_succ_publish (fuel := 0) found
        | silent next | finish verdict | fail actualEvents | call request saved => cases stepped
  finish := by
    intro data source verdict related stepped
    change interactionData source = data at related
    rw [← related] at stepped
    rw [interaction_step_encoded] at stepped
    cases found : (interactionMachine operations policy).step source with
    | none => rw [found] at stepped; cases stepped
    | some transition =>
        rw [found] at stepped
        cases transition with
        | finish actualVerdict =>
            have same : actualVerdict = verdict := by
              simpa only [Option.map_some, encodeInteractionAdvance, Option.some.injEq,
                Transition.finish.injEq] using stepped
            rw [← same]
            exact ⟨1, le_rfl, (interactionMachine operations policy).run_succ_finish (fuel := 0) found⟩
        | silent next | publish events next | fail events | call request saved => cases stepped
  fail := by
    intro data source events related stepped
    change interactionData source = data at related
    rw [← related] at stepped
    rw [interaction_step_encoded] at stepped
    cases found : (interactionMachine operations policy).step source with
    | none => rw [found] at stepped; cases stepped
    | some transition =>
        rw [found] at stepped
        cases transition with
        | fail actualEvents =>
            have same : actualEvents = events := by
              simpa only [Option.map_some, encodeInteractionAdvance, Option.some.injEq,
                Transition.fail.injEq] using stepped
            rw [← same]
            exact ⟨1, le_rfl, (interactionMachine operations policy).run_succ_fail (fuel := 0) found⟩
        | silent next | publish actualEvents next | finish verdict | call request saved => cases stepped
  call := by
    intro data source request savedData related stepped
    change interactionData source = data at related
    rw [← related] at stepped
    rw [interaction_step_encoded] at stepped
    cases found : (interactionMachine operations policy).step source with
    | none => rw [found] at stepped; cases stepped
    | some transition =>
        rw [found] at stepped
        cases transition with
        | call actualRequest saved =>
            have same : actualRequest = request ∧ interactionData saved = savedData := by
              simpa only [Option.map_some, encodeInteractionAdvance, Option.some.injEq,
                Transition.call.injEq] using stepped
            rw [← same.1, ← same.2]
            exact ⟨1, le_rfl, saved,
              (interactionMachine operations policy).run_succ_call (fuel := 0) found, rfl⟩
        | silent next | publish events next | finish verdict | fail events => cases stepped


def interactionRepresentationStage (operations : Operations) (policy : RefusalPolicy) :
    Stage (interactionMachine operations policy) (interactionDataMachine operations policy) :=
  Stage.ofBackward InteractionRelated 1 (interaction_forward operations policy) (interaction_backward operations policy)

/-- The actual interface has no absent transitions. The codec nevertheless
constructs the common endpoint-matching law without inventing a stuck state. -/
theorem interaction_matches_stuck (operations : Operations) (policy : RefusalPolicy) :
    MatchesStuck (interactionMachine operations policy) (interactionDataMachine operations policy)
      InteractionRelated 1 := by
  intro source data related missing
  change interactionData source = data at related
  rw [← related]
  have absent : (interactionDataMachine operations policy).step (interactionData source) = none := by
    rw [interaction_step_encoded, missing, Option.map_none]
  exact ⟨1, le_rfl, interactionData source,
    (interactionDataMachine operations policy).run_succ_stuck (fuel := 0) absent, rfl⟩

theorem interaction_matches_stuck_back (operations : Operations) (policy : RefusalPolicy) :
    MatchesStuck (interactionDataMachine operations policy) (interactionMachine operations policy)
      (fun data source => InteractionRelated source data) 1 := by
  intro data source related missing
  change interactionData source = data at related
  rw [← related, interaction_step_encoded] at missing
  have absent : (interactionMachine operations policy).step source = none := by
    cases found : (interactionMachine operations policy).step source with
    | none => rfl
    | some advance => rw [found] at missing; cases missing
  exact ⟨1, le_rfl, source,
    (interactionMachine operations policy).run_succ_stuck (fuel := 0) absent, related⟩

def encodeInteractionOutcome {Request : Type} : Outcome Interaction Atom Request → Outcome Atom Atom Request
  | .finished verdict => .finished verdict
  | .faulted => .faulted
  | .suspended request saved => .suspended request (interactionData saved)
  | .stuck saved => .stuck (interactionData saved)
  | .exhausted saved => .exhausted (interactionData saved)

theorem interaction_outcome_related_iff {Request : Type} (source : Outcome Interaction Atom Request)
    (data : Outcome Atom Atom Request) :
    OutcomeRel InteractionRelated source data ↔ encodeInteractionOutcome source = data := by
  constructor
  · intro related
    cases related <;> simp_all only [encodeInteractionOutcome, InteractionRelated]
  · intro encoded
    rw [← encoded]
    cases source with
    | finished verdict => exact .finished verdict
    | faulted => exact .faulted
    | suspended request saved => exact .suspended request rfl
    | stuck saved => exact .stuck rfl
    | exhausted saved => exact .exhausted rfl

theorem interaction_run_encoded (operations : Operations) (policy : RefusalPolicy) (fuel : Nat)
    (saved : Interaction) :
    (interactionDataMachine operations policy).run fuel (interactionData saved) =
      (((interactionMachine operations policy).run fuel saved).1,
        encodeInteractionOutcome ((interactionMachine operations policy).run fuel saved).2) := by
  induction fuel generalizing saved with
  | zero => rfl
  | succ fuel ih =>
      have commute := interaction_step_encoded operations policy saved
      cases found : (interactionMachine operations policy).step saved with
      | none => simp only [Machine.run, found, commute, Option.map_none, encodeInteractionOutcome]
      | some advance =>
          cases advance <;> simp only [Machine.run, found, commute, Option.map_some,
            encodeInteractionAdvance, ih, encodeInteractionOutcome]

theorem interaction_data_step_ne_none (operations : Operations) (policy : RefusalPolicy) (data : Atom) :
    (interactionDataMachine operations policy).step data ≠ none := by
  intro missing
  simp only [interactionDataMachine] at missing
  cases decoded : readInteraction data with
  | none => rw [decoded] at missing; cases missing
  | some saved => rw [decoded] at missing; cases saved <;> cases policy <;> cases missing

/-! ## The constructed callback-closure instance -/

/-- The common environment supplies identical raw replies and event logs on
both sides. Its invocation is atomic and finite; machine cost excludes work
inside the external handler. Packet acceptance supplies no effect authority. -/
theorem interaction_closed_forward (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) :
    CostSimulation ((interactionMachine operations policy).close interactionCallback environment)
      ((interactionDataMachine operations policy).close representedCallback environment) InteractionRelated 1 :=
  (interaction_forward operations policy).closed interactionCallback representedCallback environment rfl rfl
    (fun related answer => callbacks_resume_related related answer)

theorem interaction_closed_backward (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) :
    CostSimulation ((interactionDataMachine operations policy).close representedCallback environment)
      ((interactionMachine operations policy).close interactionCallback environment)
      (fun data source => InteractionRelated source data) 1 :=
  (interaction_backward operations policy).closed representedCallback interactionCallback environment rfl rfl
    (fun related answer => callbacks_resume_related related answer)

theorem interaction_closed_matches_stuck (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) :
    MatchesStuck ((interactionMachine operations policy).close interactionCallback environment)
      ((interactionDataMachine operations policy).close representedCallback environment) InteractionRelated 1 :=
  (interaction_matches_stuck operations policy).closed interactionCallback representedCallback environment

theorem interaction_closed_matches_stuck_back (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) :
    MatchesStuck ((interactionDataMachine operations policy).close representedCallback environment)
      ((interactionMachine operations policy).close interactionCallback environment)
      (fun data source => InteractionRelated source data) 1 :=
  (interaction_matches_stuck_back operations policy).closed representedCallback interactionCallback environment

def interactionClosedStage (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) :
    Stage ((interactionMachine operations policy).close interactionCallback environment)
      ((interactionDataMachine operations policy).close representedCallback environment) :=
  Stage.ofBackward InteractionRelated 1 (interaction_closed_forward operations policy environment)
    (interaction_closed_backward operations policy environment)

theorem interaction_closed_step_encoded (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) (saved : Interaction) :
    ((interactionDataMachine operations policy).close representedCallback environment).step (interactionData saved) =
      (((interactionMachine operations policy).close interactionCallback environment).step saved).map
        encodeInteractionAdvance := by
  simp only [Machine.close, interaction_step_encoded]
  cases found : (interactionMachine operations policy).step saved with
  | none => rfl
  | some advance =>
      cases advance <;> simp only [Option.map_some, encodeInteractionAdvance]
      case call endpoint retained =>
        simp only [representedCallback, interactionCallback, Machine.callEvents, resumeInteraction_encoded]

/-- Complete callback traces and outcomes agree at the same budget, including
refusal, retry, cancellation and the complete retained parent after a reply. -/
theorem interaction_closed_run_encoded (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) (fuel : Nat) (saved : Interaction) :
    ((interactionDataMachine operations policy).close representedCallback environment).run fuel (interactionData saved) =
      ((((interactionMachine operations policy).close interactionCallback environment).run fuel saved).1,
        encodeInteractionOutcome (((interactionMachine operations policy).close interactionCallback environment).run fuel saved).2) := by
  induction fuel generalizing saved with
  | zero => rfl
  | succ fuel ih =>
      have commute := interaction_closed_step_encoded operations policy environment saved
      cases found : ((interactionMachine operations policy).close interactionCallback environment).step saved with
      | none => simp only [Machine.run, found, commute, Option.map_none, encodeInteractionOutcome]
      | some advance =>
          cases advance <;> simp only [Machine.run, found, commute, Option.map_some,
            encodeInteractionAdvance, ih, encodeInteractionOutcome]

/-- One atomic service interaction uses the actual saved waiting endpoint.
The event list includes the call, every handler event, and the exact reply. -/
theorem interaction_waiting_one_call (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) (saved : Configuration)
    (service : Waiting) (ticket : Nat) (rest : List Frame)
    (pending : saved.frames = .waiting service ticket :: rest) :
    ((interactionMachine operations policy).close interactionCallback environment).run 1 (.active saved) =
      (Machine.callEvents interactionCallback environment (request saved service ticket).endpoint,
        .exhausted (resumeInteraction (.active saved)
          (environment (request saved service ticket).endpoint).2)) := by
  have stepped : (interactionMachine operations policy).step (.active saved) =
      some (.call (request saved service ticket).endpoint (.active saved)) := by
    simp only [interactionMachine, inspectInteraction,
      awaiting_preserves operations saved service ticket rest pending, interactionAdvance]
  have closed :
      ((interactionMachine operations policy).close interactionCallback environment).step (.active saved) =
        some (.publish
          (Machine.callEvents interactionCallback environment (request saved service ticket).endpoint)
          (resumeInteraction (.active saved) (environment (request saved service ticket).endpoint).2)) := by
    simp only [Machine.close, stepped, Option.map_some, interactionCallback]
  simpa only [Machine.run, List.append_nil] using
    ((interactionMachine operations policy).close interactionCallback environment).run_succ_publish
      (fuel := 0) closed

/-- Pausing after an actual closed prefix retains its events and complete
residual. Resuming the encoded residual gives exactly the same continuation,
without adding the already recorded call or handler events a second time. -/
theorem interaction_closed_resume (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) (first second : Nat)
    (saved residual : Interaction) (events : List Atom)
    (paused : ((interactionMachine operations policy).close interactionCallback environment).run first saved =
      (events, .exhausted residual)) :
    ((interactionDataMachine operations policy).close representedCallback environment).run (first + second)
        (interactionData saved) =
      (events ++ (((interactionMachine operations policy).close interactionCallback environment).run second residual).1,
        encodeInteractionOutcome
          (((interactionMachine operations policy).close interactionCallback environment).run second residual).2) := by
  rw [interaction_closed_run_encoded,
    Machine.established_and_pending _ first second saved residual events paused]

theorem interaction_closed_finite_outcomes (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) (fuel : Nat) (saved : Interaction) (data : Atom)
    (related : InteractionRelated saved data) :
    ∃ count ≤ fuel,
      (((interactionDataMachine operations policy).close representedCallback environment).run count data).1 =
        (((interactionMachine operations policy).close interactionCallback environment).run fuel saved).1 ∧
      OutcomeRel InteractionRelated
        (((interactionMachine operations policy).close interactionCallback environment).run fuel saved).2
        (((interactionDataMachine operations policy).close representedCallback environment).run count data).2 := by
  simpa only [Nat.one_mul] using
    (interaction_closed_forward operations policy environment).run_related_all
      (interaction_closed_matches_stuck operations policy environment) fuel related

theorem interaction_closed_outcomes_exact (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) (fuel : Nat) (saved : Interaction) (data : Atom)
    (related : InteractionRelated saved data) :
    (((interactionDataMachine operations policy).close representedCallback environment).run fuel data).1 =
        (((interactionMachine operations policy).close interactionCallback environment).run fuel saved).1 ∧
      OutcomeRel InteractionRelated
        (((interactionMachine operations policy).close interactionCallback environment).run fuel saved).2
        (((interactionDataMachine operations policy).close representedCallback environment).run fuel data).2 := by
  change interactionData saved = data at related
  rw [← related, interaction_closed_run_encoded]
  exact ⟨rfl, (interaction_outcome_related_iff _ _).mpr rfl⟩

/-- A represented pause constructs the actual structured residual rather than
accepting a replaced child, history or work account as a trusted endpoint. -/
theorem interaction_closed_exhausted_source (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) (fuel : Nat) (saved : Interaction) (data after : Atom)
    (events : List Atom) (related : InteractionRelated saved data)
    (paused : ((interactionDataMachine operations policy).close representedCallback environment).run fuel data =
      (events, .exhausted after)) :
    ∃ residual,
      ((interactionMachine operations policy).close interactionCallback environment).run fuel saved =
        (events, .exhausted residual) ∧ InteractionRelated residual after := by
  obtain ⟨sameEvents, outcomes⟩ := interaction_closed_outcomes_exact operations policy environment fuel saved data related
  rw [paused] at sameEvents outcomes
  obtain ⟨residual, exhausted, retained⟩ := outcomes.symm.exhausted_inv
  exact ⟨residual, Prod.ext sameEvents.symm exhausted, retained⟩

/-- This transports divergence, including repeated requests under a retry
policy. It proves neither handler fairness nor eventual acceptance. -/
theorem interaction_closed_divergence (operations : Operations) (policy : RefusalPolicy)
    (environment : Environment Atom Atom Atom Atom) (saved : Interaction) (data : Atom)
    (related : InteractionRelated saved data) :
    ((interactionMachine operations policy).close interactionCallback environment).DivergesWithin saved ↔
      ((interactionDataMachine operations policy).close representedCallback environment).DivergesWithin data :=
  (interaction_closed_forward operations policy environment).divergesWithin_iff
    (interaction_closed_matches_stuck operations policy environment)
    (interaction_closed_backward operations policy environment)
    (interaction_closed_matches_stuck_back operations policy environment) related

end Mettapedia.Languages.MeTTa.HE.NativeArgumentControlEncoding
