import Mettapedia.Languages.MeTTa.HE.NativeArgumentControlPolicy

/-!
# Retained control and services for native argument frames

This component models argument control, not expression evaluation. Evaluation,
domain refinement, substitution, Need reification and continuation entry have
explicit service requests and replies. The original telescope domain is kept
apart from the resolved evaluation domain. Callback and native-export
correspondence remain open implementation obligations.

Reply identity includes the complete retained frame stack, answer history,
prior reply identities and service account. It is structural endpoint data,
not a cryptographic capability or a proof of native ownership.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeArgumentControl

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeArgumentControlPolicy
open NativeArgumentProjection (Snapshot)
open TypedApplyEncoding (stateData readState bindingsData readBindings resultsData readResults index readIndex)

structure Operations where
  merge : Bindings → Bindings → Option Bindings
  extend : Bindings → Atom → Atom → Option Bindings

structure Prepared where
  domain : Atom
  bound : Atom
  policy : Policy
  deriving Repr

def original (state : TypedApplyState) : Atom := state.origArgs.getD state.idx Atom.undefinedType
def originalDomain (state : TypedApplyState) : Atom := state.argTypes.getD state.idx Atom.undefinedType

def preparedData (prepared : Prepared) : Atom :=
  .expression [prepared.domain, prepared.bound, policyData prepared.policy]

def readPrepared : Atom → Option Prepared
  | .expression [domain, bound, policy] => do return ⟨domain, bound, ← readPolicy policy⟩
  | _ => none

@[simp] theorem readPrepared_preparedData (prepared : Prepared) :
    readPrepared (preparedData prepared) = some prepared := by
  cases prepared
  simp [readPrepared, preparedData]

inductive Parent where
  | only (state : TypedApplyState) (prepared : Prepared) (value : Atom) (bindings : Bindings)
  | alternatives (saved : Snapshot) (prepared : Prepared)
  deriving Repr

inductive Waiting where
  | prepare (state : TypedApplyState)
  | transform (state : TypedApplyState) (prepared : Prepared)
  | evaluate (state : TypedApplyState) (prepared : Prepared)
  | resumeEvaluation (state : TypedApplyState) (prepared : Prepared) (continuation reply : Atom)
  | effect (state : TypedApplyState) (prepared : Prepared) (continuation request : Atom)
  | continuation (child : TypedApplyState) (parent : Parent)
  deriving Repr

inductive Frame where
  | enter (state : TypedApplyState)
  | prepared (state : TypedApplyState) (resolved : Prepared)
  | rawReady (state : TypedApplyState) (prepared : Prepared) (value : Atom)
  | iterate (saved : Snapshot) (prepared : Prepared)
  | afterIterChild (saved : Snapshot) (prepared : Prepared)
  | afterOnlyChild (state : TypedApplyState) (prepared : Prepared) (value : Atom) (bindings : Bindings)
  | waiting (service : Waiting) (ticket : Nat)
  deriving Repr

def Parent.frame : Parent → Frame
  | .only state prepared value bindings => .afterOnlyChild state prepared value bindings
  | .alternatives saved prepared => .afterIterChild saved prepared

def parentData : Parent → Atom
  | .only state prepared value bindings => .expression [.symbol "only", stateData state,
      preparedData prepared, value, bindingsData bindings]
  | .alternatives saved prepared => .expression [.symbol "alternatives",
      NativeArgumentProjection.snapshotData saved, preparedData prepared]

def waitingData : Waiting → Atom
  | .prepare state => .expression [.symbol "prepare", stateData state]
  | .transform state prepared => .expression [.symbol "transform", stateData state, preparedData prepared]
  | .evaluate state prepared => .expression [.symbol "evaluate", stateData state, preparedData prepared]
  | .resumeEvaluation state prepared continuation reply => .expression [.symbol "resume-evaluation",
      stateData state, preparedData prepared, continuation, reply]
  | .effect state prepared continuation request => .expression [.symbol "effect", stateData state,
      preparedData prepared, continuation, request]
  | .continuation child parent => .expression [.symbol "continuation", stateData child, parentData parent]

def frameData : Frame → Atom
  | .enter state => .expression [.symbol "enter", stateData state]
  | .prepared state resolved => .expression [.symbol "prepared", stateData state, preparedData resolved]
  | .rawReady state prepared value => .expression [.symbol "raw-ready", stateData state, preparedData prepared, value]
  | .iterate saved prepared => .expression [.symbol "iterate", NativeArgumentProjection.snapshotData saved, preparedData prepared]
  | .afterIterChild saved prepared => .expression [.symbol "after-iter-child", NativeArgumentProjection.snapshotData saved, preparedData prepared]
  | .afterOnlyChild state prepared value bindings => .expression [.symbol "after-only-child",
      stateData state, preparedData prepared, value, bindingsData bindings]
  | .waiting service ticket => .expression [.symbol "waiting", waitingData service, index ticket]

structure Configuration where
  frames : List Frame
  emitted : ResultList
  episode : Nat
  nextTicket : Nat
  replyHistory : List Nat
  externalWork : Nat
  deriving Repr

def configurationData (state : Configuration) : Atom :=
  .expression [.symbol "he-native-argument-control-v1", .expression (state.frames.map frameData),
    resultsData state.emitted, index state.episode, index state.nextTicket,
    .expression (state.replyHistory.map index), index state.externalWork]

structure Request where
  endpoint : Atom
  service : Waiting
  deriving Repr

def request (state : Configuration) (service : Waiting) (ticket : Nat) : Request :=
  ⟨.expression [.symbol "he-native-argument-request-v1", index ticket, waitingData service,
    configurationData state], service⟩

def issue (state : Configuration) (rest : List Frame) (service : Waiting) : Configuration :=
  {state with frames := .waiting service state.nextTicket :: rest, nextTicket := state.nextTicket + 1}

def issuedRequest (state : Configuration) (rest : List Frame) (service : Waiting) : Request :=
  request (issue state rest service) service state.nextTicket

inductive TransformReply where
  | value (value : Atom)
  | dropped
  | error (failure : ResultPair)
  deriving Repr

inductive ReplyValue where
  | prepared (result : Prepared)
  | transformed (result : TransformReply)
  | evaluated (results : ResultList)
  /-- The callback result collector could not be initialized. The native
  WAIT_EVAL control branch releases this argument frame without an answer. -/
  | collectorUnavailable
  | effectRequired (continuation request : Atom)
  | effectReturned (reply : Atom)
  | continuationEntered
  | continuationCancelled
  deriving Repr

structure Reply where
  endpoint : Atom
  value : ReplyValue
  charge : Nat := 0
  deriving Repr

inductive Rejection where
  | noPending | endpointMismatch | wrongKind
  deriving Repr, DecidableEq

def selectedSnapshot (state : TypedApplyState) (_prepared : Prepared) (results : ResultList) : Snapshot :=
  ⟨state, original state, originalDomain state, results, 0, .iterate, none, none⟩

def acceptedFrame : Waiting → ReplyValue → Option (List Frame)
  | .prepare state, .prepared prepared => some [.prepared state prepared]
  | .transform state prepared, .transformed (.value value) => some [.rawReady state prepared value]
  | .transform _ _, .transformed .dropped => some []
  | .evaluate state prepared, .evaluated results => some [.iterate (selectedSnapshot state prepared results) prepared]
  | .resumeEvaluation state prepared _ _, .evaluated results => some [.iterate (selectedSnapshot state prepared results) prepared]
  | .evaluate _ _, .collectorUnavailable => some []
  | .resumeEvaluation _ _ _ _, .collectorUnavailable => some []
  | .evaluate state prepared, .effectRequired continuation effect => some [.waiting (.effect state prepared continuation effect) 0]
  | .resumeEvaluation state prepared _ _, .effectRequired continuation effect => some [.waiting (.effect state prepared continuation effect) 0]
  | .effect state prepared continuation _, .effectReturned result => some [.waiting (.resumeEvaluation state prepared continuation result) 0]
  | .continuation child parent, .continuationEntered => some [.enter child, parent.frame]
  | .continuation _ parent, .continuationCancelled => some [parent.frame]
  | _, _ => none

/-- A fresh external request receives a fresh serial. It is never executed
by this construction. -/
def reticket (ticket : Nat) : List Frame → List Frame
  | [.waiting service _] => [.waiting service ticket]
  | frames => frames

def pendingTicket (state : Configuration) : Nat :=
  match state.frames with
  | .waiting _ ticket :: _ => ticket
  | _ => state.nextTicket

def replied (state : Configuration) (rest : List Frame) (reply : Reply)
    (frames : List Frame) : Configuration :=
  {state with frames := reticket state.nextTicket frames ++ rest, nextTicket := state.nextTicket + 1, replyHistory := state.replyHistory ++ [pendingTicket state], externalWork := state.externalWork + reply.charge}

inductive Delivery where
  | accepted (state : Configuration)
  | rejected (reason : Rejection)
  deriving Repr

inductive FrameReplyRel : Waiting → ReplyValue → List Frame → Prop where
  | prepare (state prepared) : FrameReplyRel (.prepare state) (.prepared prepared) [.prepared state prepared]
  | transformed (state prepared value) : FrameReplyRel (.transform state prepared) (.transformed (.value value)) [.rawReady state prepared value]
  | dropped (state prepared) : FrameReplyRel (.transform state prepared) (.transformed .dropped) []
  | evaluated (state prepared results) : FrameReplyRel (.evaluate state prepared) (.evaluated results) [.iterate (selectedSnapshot state prepared results) prepared]
  | resumed (state prepared continuation reply results) : FrameReplyRel (.resumeEvaluation state prepared continuation reply) (.evaluated results) [.iterate (selectedSnapshot state prepared results) prepared]
  | unavailable (state prepared) : FrameReplyRel (.evaluate state prepared) .collectorUnavailable []
  | unavailableResumed (state prepared continuation reply) : FrameReplyRel (.resumeEvaluation state prepared continuation reply) .collectorUnavailable []
  | requested (state prepared continuation effect) : FrameReplyRel (.evaluate state prepared) (.effectRequired continuation effect) [.waiting (.effect state prepared continuation effect) 0]
  | requestedAgain (state prepared old reply continuation effect) : FrameReplyRel (.resumeEvaluation state prepared old reply) (.effectRequired continuation effect) [.waiting (.effect state prepared continuation effect) 0]
  | effectReturned (state prepared continuation effect result) : FrameReplyRel (.effect state prepared continuation effect) (.effectReturned result) [.waiting (.resumeEvaluation state prepared continuation result) 0]
  | entered (child parent) : FrameReplyRel (.continuation child parent) .continuationEntered [.enter child, parent.frame]
  | cancelled (child parent) : FrameReplyRel (.continuation child parent) .continuationCancelled [parent.frame]

theorem acceptedFrame_iff (service : Waiting) (value : ReplyValue) (frames : List Frame) :
    acceptedFrame service value = some frames ↔ FrameReplyRel service value frames := by
  constructor
  · cases service <;> cases value <;> simp only [acceptedFrame] <;> intro equal <;>
      first | (cases equal; constructor) | contradiction | skip
    case transform.transformed =>
      rename_i state prepared reply
      cases reply
      · cases equal; constructor
      · cases equal; constructor
      · contradiction
  · intro related
    cases related <;> rfl

def response (service : Waiting) (value : ReplyValue) : Option (ResultList × List Frame) :=
  match service, value with
  | .transform _ _, .transformed (.error failure) => some ([failure], [])
  | _, _ => do return ([], ← acceptedFrame service value)

inductive ResponseRel : Waiting → ReplyValue → ResultList → List Frame → Prop where
  | ordinary {service value frames} : FrameReplyRel service value frames →
      ResponseRel service value [] frames
  | error (state prepared failure) : ResponseRel (.transform state prepared)
      (.transformed (.error failure)) [failure] []

private theorem response_ordinary {service : Waiting} {value : ReplyValue} {frames : List Frame}
    (related : FrameReplyRel service value frames) : response service value = some ([], frames) := by
  cases related <;> rfl

theorem response_iff (service : Waiting) (value : ReplyValue) (events : ResultList) (frames : List Frame) :
    response service value = some (events, frames) ↔ ResponseRel service value events frames := by
  constructor
  · intro computed
    cases service <;> cases value <;> simp only [response, acceptedFrame, pure] at computed <;>
      first
      | (cases computed; exact .ordinary (by constructor))
      | contradiction
      | skip
    case transform.transformed =>
      rename_i state prepared result
      cases result
      · cases computed
        exact .ordinary (.transformed _ _ _)
      · cases computed
        exact .ordinary (.dropped _ _)
      · cases computed
        exact .error _ _ _
  · intro related
    cases related with
    | ordinary body => exact response_ordinary body
    | error => rfl

/-- The full endpoint is checked before the reply kind. A missing, duplicate
or spliced reply cannot change the retained configuration. -/
def deliver (state : Configuration) (reply : Reply) : Delivery :=
  match state.frames with
  | .waiting service ticket :: rest =>
      if reply.endpoint ≠ (request state service ticket).endpoint then .rejected .endpointMismatch
      else match response service reply.value with
      | none => .rejected .wrongKind
      | some (events, frames) => .accepted (replied {state with emitted := state.emitted ++ events} rest reply frames)
  | _ => .rejected .noPending

/-- Construct a reply to the currently retained endpoint. This is a local
protocol fixture/driver operation: it establishes neither service truth nor
external authority. Externally supplied replies still go through `deliver`.
The correspondence below avoids re-expanding a reflexive full-state equality
when the reply endpoint is constructed from the same saved state. -/
def fulfillCurrent (state : Configuration) (value : ReplyValue) (charge : Nat) : Delivery :=
  match state.frames with
  | .waiting service ticket :: rest =>
      let reply : Reply := ⟨(request state service ticket).endpoint, value, charge⟩
      match response service value with
      | none => .rejected .wrongKind
      | some (events, frames) => .accepted (replied {state with emitted := state.emitted ++ events} rest reply frames)
  | _ => .rejected .noPending

theorem fulfillCurrent_correspondence (state : Configuration) (value : ReplyValue) (charge : Nat)
    (service : Waiting) (ticket : Nat) (rest : List Frame)
    (pending : state.frames = .waiting service ticket :: rest) :
    fulfillCurrent state value charge =
      deliver state ⟨(request state service ticket).endpoint, value, charge⟩ := by
  simp only [fulfillCurrent, deliver, pending]
  rw [if_neg (not_not.mpr rfl)]

theorem fulfillCurrent_missing (state : Configuration) (value : ReplyValue) (charge : Nat)
    (noService : ∀ service ticket rest, state.frames ≠ .waiting service ticket :: rest) :
    fulfillCurrent state value charge = .rejected .noPending := by
  unfold fulfillCurrent
  cases frames : state.frames with
  | nil => rfl
  | cons first rest =>
    cases first <;> try rfl
    case waiting service ticket => exact (noService service ticket rest frames).elim

/-- Independent acceptance, including exact endpoint and ordered frames. -/
inductive DeliveryRel (state : Configuration) (reply : Reply) : Configuration → Prop where
  | accepted (service ticket rest events frames)
      (pending : state.frames = .waiting service ticket :: rest)
      (endpoint : reply.endpoint = (request state service ticket).endpoint)
      (body : ResponseRel service reply.value events frames) :
      DeliveryRel state reply (replied {state with emitted := state.emitted ++ events} rest reply frames)

theorem deliver_iff (state : Configuration) (reply : Reply) (after : Configuration) :
    deliver state reply = .accepted after ↔ DeliveryRel state reply after := by
  constructor
  · intro delivered
    unfold deliver at delivered
    cases pending : state.frames with
    | nil => simp [pending] at delivered
    | cons frame rest =>
      cases frame <;> simp only [pending] at delivered <;> try contradiction
      case waiting service ticket =>
        split at delivered
        · contradiction
        · rename_i endpoint
          have equal : reply.endpoint = (request state service ticket).endpoint := by simpa only [not_not] using endpoint
          cases body : response service reply.value with
          | none => simp [body] at delivered
          | some returned =>
            obtain ⟨events, frames⟩ := returned
            simp only [body] at delivered
            cases delivered
            simpa only [pending] using
              (DeliveryRel.accepted _ _ _ _ _ pending equal ((response_iff _ _ _ _).mp body))
  · intro related
    cases related with
    | accepted service ticket rest events frames pending endpoint body =>
      have computed := (response_iff service reply.value events frames).mpr body
      simp only [deliver, pending]
      rw [if_neg (not_not.mpr endpoint), computed]

theorem delivery_accounts {state after : Configuration} {reply : Reply}
    (accepted : deliver state reply = .accepted after) :
    after.nextTicket = state.nextTicket + 1 ∧
    after.replyHistory = state.replyHistory ++ [pendingTicket state] ∧
    after.externalWork = state.externalWork + reply.charge ∧ after.episode = state.episode := by
  cases (deliver_iff _ _ _).mp accepted
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem delivery_preserves_emitted_prefix {state after : Configuration} {reply : Reply}
    (accepted : deliver state reply = .accepted after) : ∃ added, after.emitted = state.emitted ++ added := by
  cases (deliver_iff _ _ _).mp accepted with
  | accepted service ticket rest events frames pending endpoint body => exact ⟨events, rfl⟩

theorem continuation_reply (state : Configuration) (child : TypedApplyState) (parent : Parent)
    (ticket : Nat) (rest : List Frame) (charge : Nat)
    (pending : state.frames = .waiting (.continuation child parent) ticket :: rest) :
    deliver state ⟨(request state (.continuation child parent) ticket).endpoint, .continuationEntered, charge⟩ =
      .accepted (replied state rest
        ⟨(request state (.continuation child parent) ticket).endpoint, .continuationEntered, charge⟩
        [.enter child, parent.frame]) := by
  simp [deliver, pending, response, acceptedFrame, replied, pendingTicket]

theorem evaluated_reply (state : Configuration) (arguments : TypedApplyState) (prepared : Prepared)
    (ticket : Nat) (rest : List Frame) (results : ResultList) (charge : Nat)
    (pending : state.frames = .waiting (.evaluate arguments prepared) ticket :: rest) :
    deliver state ⟨(request state (.evaluate arguments prepared) ticket).endpoint, .evaluated results, charge⟩ =
      .accepted (replied state rest
        ⟨(request state (.evaluate arguments prepared) ticket).endpoint, .evaluated results, charge⟩
        [.iterate (selectedSnapshot arguments prepared results) prepared]) := by
  simp [deliver, pending, response, acceptedFrame, replied, pendingTicket]

theorem evaluation_reply_order (arguments : TypedApplyState) (prepared : Prepared) (results : ResultList) :
    (selectedSnapshot arguments prepared results).pending = results := by
  simp [selectedSnapshot, NativeArgumentProjection.Snapshot.pending]

theorem evaluation_reply_domains (arguments : TypedApplyState) (prepared : Prepared) (results : ResultList) :
    (selectedSnapshot arguments prepared results).domain = originalDomain arguments ∧
      (selectedSnapshot arguments prepared results).original = original arguments := ⟨rfl, rfl⟩

end Mettapedia.Languages.MeTTa.HE.NativeArgumentControl
