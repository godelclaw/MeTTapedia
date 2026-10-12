import Mettapedia.Languages.MeTTa.HE.NativeArgumentControl

/-!
# The complete retained argument-control component

The native ENTER, WAIT_EVAL, ITERATE, AFTER_ITER_CHILD and AFTER_ONLY_CHILD
phases are represented explicitly. ENTER's services and continuation entry
are suspension boundaries. Their replies cannot replace a selected prefix.
The common step driver supplies exact budget resumption and event accounts.

This is executable argument administration with named services. It neither
implements a fourth expression evaluator nor asserts native callback, Need,
binding, allocation or exported-frame correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeArgumentControlMachine

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeArgumentControlPolicy NativeArgumentControl
open NativeArgumentProjection (Snapshot Action)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def FailureRel (errorAsData : Bool) (original value : Atom) : Prop :=
  errorAsData = false ∧ isEmptyOrError value = true ∧ value ≠ original

def changedFailure (errorAsData : Bool) (original value : Atom) : Bool :=
  !errorAsData && isEmptyOrError value && decide (value ≠ original)

theorem changedFailure_iff (errorAsData : Bool) (original value : Atom) :
    changedFailure errorAsData original value = true ↔ FailureRel errorAsData original value := by
  simp only [changedFailure, FailureRel, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, and_assoc]

def activate (snapshot : Snapshot) (value : Atom) (bindings : Bindings) : Snapshot :=
  {snapshot.afterOutcome with phase := .afterChild, activeValue := some value, activeBindings := some bindings}

def consume (operations : Operations) (errorAsData : Bool) (snapshot : Snapshot) : Action :=
  match snapshot.pending with
  | [] => .exhausted
  | (value, evaluated) :: _ =>
      match operations.merge snapshot.state.env evaluated with
      | none => .skipped snapshot.afterOutcome
      | some merged =>
          if changedFailure errorAsData snapshot.original value then .failure (value, merged) snapshot.afterOutcome
          else match operations.extend merged snapshot.domain value with
            | none => .skipped snapshot.afterOutcome
            | some extended => .child (value, extended) (activate snapshot value extended)

inductive ConsumerRel (operations : Operations) (errorAsData : Bool) (snapshot : Snapshot) : Action → Prop where
  | exhausted : snapshot.pending = [] → ConsumerRel operations errorAsData snapshot .exhausted
  | mergeFailed (value evaluated remaining) :
      snapshot.pending = (value, evaluated) :: remaining →
      operations.merge snapshot.state.env evaluated = none →
      ConsumerRel operations errorAsData snapshot (.skipped snapshot.afterOutcome)
  | error (value evaluated remaining merged) :
      snapshot.pending = (value, evaluated) :: remaining →
      operations.merge snapshot.state.env evaluated = some merged →
      FailureRel errorAsData snapshot.original value →
      ConsumerRel operations errorAsData snapshot (.failure (value, merged) snapshot.afterOutcome)
  | binderFailed (value evaluated remaining merged) :
      snapshot.pending = (value, evaluated) :: remaining →
      operations.merge snapshot.state.env evaluated = some merged →
      ¬FailureRel errorAsData snapshot.original value →
      operations.extend merged snapshot.domain value = none →
      ConsumerRel operations errorAsData snapshot (.skipped snapshot.afterOutcome)
  | selected (value evaluated remaining merged extended) :
      snapshot.pending = (value, evaluated) :: remaining →
      operations.merge snapshot.state.env evaluated = some merged →
      ¬FailureRel errorAsData snapshot.original value →
      operations.extend merged snapshot.domain value = some extended →
      ConsumerRel operations errorAsData snapshot (.child (value, extended) (activate snapshot value extended))

theorem consume_sound (operations : Operations) (errorAsData : Bool) (snapshot : Snapshot) :
    ConsumerRel operations errorAsData snapshot (consume operations errorAsData snapshot) := by
  unfold consume
  cases pending : snapshot.pending with
  | nil => exact .exhausted pending
  | cons selected remaining =>
    obtain ⟨value, evaluated⟩ := selected
    simp only
    cases mergeResult : operations.merge snapshot.state.env evaluated with
    | none => exact .mergeFailed _ _ _ pending mergeResult
    | some merged =>
      simp only
      by_cases failed : changedFailure errorAsData snapshot.original value = true
      · rw [if_pos failed]
        exact .error _ _ _ _ pending mergeResult ((changedFailure_iff _ _ _).mp failed)
      · rw [if_neg failed]
        have ordinary : ¬FailureRel errorAsData snapshot.original value := fun failure =>
          failed ((changedFailure_iff _ _ _).mpr failure)
        cases extendResult : operations.extend merged snapshot.domain value with
        | none => exact .binderFailed _ _ _ _ pending mergeResult ordinary extendResult
        | some extended => exact .selected _ _ _ _ _ pending mergeResult ordinary extendResult

theorem consume_complete (operations : Operations) (errorAsData : Bool) (snapshot : Snapshot)
    (action : Action) (related : ConsumerRel operations errorAsData snapshot action) :
    consume operations errorAsData snapshot = action := by
  cases related with
  | exhausted pending => simp [consume, pending]
  | mergeFailed value evaluated remaining pending merged => simp [consume, pending, merged]
  | error value evaluated remaining merged pending mergedReply failed =>
    simp [consume, pending, mergedReply, (changedFailure_iff _ _ _).mpr failed]
  | binderFailed value evaluated remaining merged pending mergedReply ordinary extended =>
    have notFailed : ¬changedFailure errorAsData snapshot.original value = true := fun failure =>
      ordinary ((changedFailure_iff _ _ _).mp failure)
    simp [consume, pending, mergedReply, notFailed, extended]
  | selected value evaluated remaining merged extended pending mergedReply ordinary extendedReply =>
    have notFailed : ¬changedFailure errorAsData snapshot.original value = true := fun failure =>
      ordinary ((changedFailure_iff _ _ _).mp failure)
    simp [consume, pending, mergedReply, notFailed, extendedReply]

theorem consume_iff (operations : Operations) (errorAsData : Bool) (snapshot : Snapshot) (action : Action) :
    consume operations errorAsData snapshot = action ↔ ConsumerRel operations errorAsData snapshot action := by
  constructor
  · intro equal
    rw [← equal]
    exact consume_sound _ _ _
  · exact consume_complete _ _ _ _

/-- The ordinary HE phase is the already-qualified consumer, with no
profile-dependent error-as-data change hidden in that connection. -/
theorem consume_ordinary_he (operations : Operations) (snapshot : Snapshot) :
    consume operations false snapshot =
      NativeArgumentProjection.consume operations.merge operations.extend snapshot := by
  unfold consume NativeArgumentProjection.consume
  cases snapshot.pending with
  | nil => rfl
  | cons selected remaining =>
    obtain ⟨value, evaluated⟩ := selected
    simp [changedFailure, activate]
    rfl

/-- Selecting, rejecting or emitting a reply consumes one occurrence. Its
remaining siblings keep their order, multiplicity, provenance and original
parent environment. The selected child does not consume another sibling. -/
theorem consume_retains_order (operations : Operations) (errorAsData : Bool)
    {snapshot saved : Snapshot}
    (retained : (consume operations errorAsData snapshot).retained = some saved) :
    saved.outcomes = snapshot.outcomes ∧ saved.nextOutcome = snapshot.nextOutcome + 1 ∧
      saved.pending = snapshot.pending.tail ∧ saved.state = snapshot.state ∧
      saved.original = snapshot.original ∧ saved.domain = snapshot.domain := by
  have related := consume_sound operations errorAsData snapshot
  generalize computed : consume operations errorAsData snapshot = action at related retained
  cases related <;> simp only [NativeArgumentProjection.Action.retained] at retained
  case exhausted => contradiction
  case mergeFailed =>
    cases retained
    exact ⟨rfl, rfl, NativeArgumentProjection.pending_afterOutcome _, rfl, rfl, rfl⟩
  case error =>
    cases retained
    exact ⟨rfl, rfl, NativeArgumentProjection.pending_afterOutcome _, rfl, rfl, rfl⟩
  case binderFailed =>
    cases retained
    exact ⟨rfl, rfl, NativeArgumentProjection.pending_afterOutcome _, rfl, rfl, rfl⟩
  case selected =>
    cases retained
    exact ⟨rfl, rfl, NativeArgumentProjection.pending_afterOutcome _, rfl, rfl, rfl⟩

inductive Fault where
  | invalidArgumentState | invalidChildPhase
  deriving Repr, DecidableEq

inductive Event where
  | answer (result : ResultPair)
  | fault (reason : Fault)
  deriving Repr

abbrev Advance := Transition Configuration Event Configuration Request

def replace (state : Configuration) (frames : List Frame) : Configuration := {state with frames := frames}

def publish (state : Configuration) (frames : List Frame) (result : ResultPair) : Advance :=
  .publish [.answer result] {state with frames := frames, emitted := state.emitted ++ [result]}

def call (state : Configuration) (rest : List Frame) (service : Waiting) : Advance :=
  .call (issuedRequest state rest service) (issue state rest service)

def rawBindings (operations : Operations) (state : TypedApplyState) (prepared : Prepared)
    (value : Atom) : Option Bindings :=
  if prepared.policy.dependentTelescope then operations.extend state.env (originalDomain state) value
  else some state.env

def consumed (state : Configuration) (rest : List Frame) (snapshot : Snapshot)
    (prepared : Prepared) : Action → Advance
  | .exhausted => .silent (replace state rest)
  | .skipped saved => .silent (replace state (.iterate saved prepared :: rest))
  | .failure result saved => publish state (.iterate saved prepared :: rest) result
  | .child selected saved => call state rest
      (.continuation (snapshot.state.advance selected.1 selected.2) (.alternatives saved prepared))

instance (state : TypedApplyState) : Decidable state.WellFormed := by
  unfold TypedApplyState.WellFormed
  infer_instance

/-- Inspection computes a protocol transition. External evaluation, effects
and continuation entry are returned as requests rather than performed. -/
def inspect (operations : Operations) (state : Configuration) : Advance :=
  match state.frames with
  | [] => .finish state
  | .enter arguments :: rest =>
      if ¬arguments.WellFormed then .fail [.fault .invalidArgumentState]
      else if arguments.idx = arguments.origArgs.length then
        publish state rest (.expression (arguments.headAtom :: arguments.evArgs), arguments.env)
      else call state rest (.prepare arguments)
  | .prepared arguments prepared :: rest =>
      if prepared.policy.raw (original arguments) prepared.domain prepared.bound then
        if prepared.policy.transform prepared.domain then call state rest (.transform arguments prepared)
        else .silent (replace state (.rawReady arguments prepared prepared.bound :: rest))
      else call state rest (.evaluate arguments prepared)
  | .rawReady arguments prepared value :: rest =>
      match rawBindings operations arguments prepared value with
      | none => .silent (replace state rest)
      | some bindings => call state rest
          (.continuation (arguments.advance value bindings) (.only arguments prepared value bindings))
  | .iterate snapshot prepared :: rest => consumed state rest snapshot prepared
      (consume operations prepared.policy.errorAsData snapshot)
  | .afterIterChild snapshot prepared :: rest =>
      match NativeArgumentProjection.returnedChild snapshot with
      | none => .fail [.fault .invalidChildPhase]
      | some saved => .silent (replace state (.iterate saved prepared :: rest))
  | .afterOnlyChild _ _ _ _ :: rest => .silent (replace state rest)
  | .waiting service ticket :: _ => .call (request state service ticket) state

/-- Independent phase rules. Each request, child endpoint and emitted
occurrence is constructed from the retained inputs of the rule. -/
inductive AdvanceRel (operations : Operations) (state : Configuration) : Advance → Prop where
  | finished : state.frames = [] → AdvanceRel operations state (.finish state)
  | invalid (arguments rest) : state.frames = .enter arguments :: rest → ¬arguments.WellFormed →
      AdvanceRel operations state (.fail [.fault .invalidArgumentState])
  | completed (arguments rest) : state.frames = .enter arguments :: rest → arguments.WellFormed →
      arguments.idx = arguments.origArgs.length →
      AdvanceRel operations state (publish state rest (.expression (arguments.headAtom :: arguments.evArgs), arguments.env))
  | preparation (arguments rest) : state.frames = .enter arguments :: rest → arguments.WellFormed →
      arguments.idx ≠ arguments.origArgs.length → AdvanceRel operations state (call state rest (.prepare arguments))
  | transformed (arguments prepared rest) : state.frames = .prepared arguments prepared :: rest →
      RawRel prepared.policy (original arguments) prepared.domain prepared.bound →
      prepared.policy.transform prepared.domain = true →
      AdvanceRel operations state (call state rest (.transform arguments prepared))
  | raw (arguments prepared rest) : state.frames = .prepared arguments prepared :: rest →
      RawRel prepared.policy (original arguments) prepared.domain prepared.bound →
      prepared.policy.transform prepared.domain = false →
      AdvanceRel operations state (.silent (replace state (.rawReady arguments prepared prepared.bound :: rest)))
  | evaluation (arguments prepared rest) : state.frames = .prepared arguments prepared :: rest →
      ¬RawRel prepared.policy (original arguments) prepared.domain prepared.bound →
      AdvanceRel operations state (call state rest (.evaluate arguments prepared))
  | rawFailed (arguments prepared value rest) : state.frames = .rawReady arguments prepared value :: rest →
      rawBindings operations arguments prepared value = none → AdvanceRel operations state (.silent (replace state rest))
  | rawChild (arguments prepared value rest bindings) : state.frames = .rawReady arguments prepared value :: rest →
      rawBindings operations arguments prepared value = some bindings → AdvanceRel operations state
        (call state rest (.continuation (arguments.advance value bindings) (.only arguments prepared value bindings)))
  | consume (snapshot prepared rest action) : state.frames = .iterate snapshot prepared :: rest →
      ConsumerRel operations prepared.policy.errorAsData snapshot action →
      AdvanceRel operations state (consumed state rest snapshot prepared action)
  | returned (snapshot prepared rest saved) : state.frames = .afterIterChild snapshot prepared :: rest →
      NativeArgumentProjection.returnedChild snapshot = some saved →
      AdvanceRel operations state (.silent (replace state (.iterate saved prepared :: rest)))
  | invalidReturn (snapshot prepared rest) : state.frames = .afterIterChild snapshot prepared :: rest →
      NativeArgumentProjection.returnedChild snapshot = none →
      AdvanceRel operations state (.fail [.fault .invalidChildPhase])
  | onlyReturned (arguments prepared value bindings rest) :
      state.frames = .afterOnlyChild arguments prepared value bindings :: rest →
      AdvanceRel operations state (.silent (replace state rest))
  | awaiting (service ticket rest) : state.frames = .waiting service ticket :: rest →
      AdvanceRel operations state (.call (request state service ticket) state)

theorem inspect_sound (operations : Operations) (state : Configuration) :
    AdvanceRel operations state (inspect operations state) := by
  unfold inspect
  cases frames : state.frames with
  | nil => exact .finished frames
  | cons frame rest =>
    cases frame <;> simp only
    case enter arguments =>
      by_cases invalid : ¬arguments.WellFormed
      · rw [if_pos invalid]
        exact .invalid _ _ frames invalid
      · rw [if_neg invalid]
        have valid : arguments.WellFormed := not_not.mp invalid
        by_cases complete : arguments.idx = arguments.origArgs.length
        · rw [if_pos complete]
          exact .completed _ _ frames valid complete
        · rw [if_neg complete]
          exact .preparation _ _ frames valid complete
    case prepared arguments prepared =>
      by_cases raw : prepared.policy.raw (original arguments) prepared.domain prepared.bound = true
      · rw [if_pos raw]
        have demand := (raw_iff _ _ _ _).mp raw
        cases transformed : prepared.policy.transform prepared.domain with
        | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact .raw _ _ _ frames demand transformed
        | true => simp only [↓reduceIte]; exact .transformed _ _ _ frames demand transformed
      · rw [if_neg raw]
        exact .evaluation _ _ _ frames (fun demand => raw ((raw_iff _ _ _ _).mpr demand))
    case rawReady arguments prepared value =>
      cases extended : rawBindings operations arguments prepared value with
      | none => exact .rawFailed _ _ _ _ frames extended
      | some bindings => exact .rawChild _ _ _ _ _ frames extended
    case iterate snapshot prepared => exact .consume _ _ _ _ frames (consume_sound _ _ _)
    case afterIterChild snapshot prepared =>
      cases returned : NativeArgumentProjection.returnedChild snapshot with
      | none => exact .invalidReturn _ _ _ frames returned
      | some saved => exact .returned _ _ _ _ frames returned
    case afterOnlyChild arguments prepared value bindings => exact .onlyReturned _ _ _ _ _ frames
    case waiting service ticket => exact .awaiting _ _ _ frames

theorem inspect_complete (operations : Operations) (state : Configuration) (advance : Advance)
    (related : AdvanceRel operations state advance) : inspect operations state = advance := by
  cases related with
  | finished empty => simp [inspect, empty]
  | invalid arguments rest frames invalid => simp [inspect, frames, invalid]
  | completed arguments rest frames valid complete => simp [inspect, frames, valid, complete]
  | preparation arguments rest frames valid incomplete => simp [inspect, frames, valid, incomplete]
  | transformed arguments prepared rest frames raw transformed =>
      simp [inspect, frames, (raw_iff _ _ _ _).mpr raw, transformed]
  | raw arguments prepared rest frames raw notTransformed =>
      simp [inspect, frames, (raw_iff _ _ _ _).mpr raw, notTransformed]
  | evaluation arguments prepared rest frames evaluated =>
      have notRaw : ¬prepared.policy.raw (original arguments) prepared.domain prepared.bound = true :=
        fun raw => evaluated ((raw_iff _ _ _ _).mp raw)
      simp [inspect, frames, notRaw]
  | rawFailed arguments prepared value rest frames extended => simp [inspect, frames, extended]
  | rawChild arguments prepared value rest bindings frames extended => simp [inspect, frames, extended]
  | consume snapshot prepared rest action frames consumed => simp [inspect, frames, consume_complete _ _ _ _ consumed]
  | returned snapshot prepared rest saved frames returned => simp [inspect, frames, returned]
  | invalidReturn snapshot prepared rest frames returned => simp [inspect, frames, returned]
  | onlyReturned arguments prepared value bindings rest frames => simp [inspect, frames]
  | awaiting service ticket rest frames => simp [inspect, frames]

theorem inspect_iff (operations : Operations) (state : Configuration) (advance : Advance) :
    inspect operations state = advance ↔ AdvanceRel operations state advance := by
  constructor
  · intro equal
    rw [← equal]
    exact inspect_sound _ _
  · exact inspect_complete _ _ _

private theorem call_pending (state : Configuration) (rest : List Frame) (service : Waiting)
    (called : Request) (saved : Configuration) (equal : call state rest service = .call called saved) :
    ∃ ticket tail, saved.frames = .waiting called.service ticket :: tail ∧
      called = request saved called.service ticket := by
  have fields : issuedRequest state rest service = called ∧ issue state rest service = saved := by
    simpa only [call, Transition.call.injEq] using equal
  rw [← fields.1, ← fields.2]
  exact ⟨state.nextTicket, rest, rfl, rfl⟩

private theorem transition_call_pending (operations : Operations) (state : Configuration)
    (transition : Advance) (related : AdvanceRel operations state transition)
    (called : Request) (saved : Configuration) (equal : transition = .call called saved) :
    ∃ ticket tail, saved.frames = .waiting called.service ticket :: tail ∧
      called = request saved called.service ticket := by
  cases related <;> try simp [publish] at equal
  case preparation => exact call_pending _ _ _ _ _ equal
  case transformed => exact call_pending _ _ _ _ _ equal
  case evaluation => exact call_pending _ _ _ _ _ equal
  case rawChild => exact call_pending _ _ _ _ _ equal
  case consume snapshot prepared rest action frames related =>
    cases related <;> simp only [consumed, publish] at equal <;> try contradiction
    case selected => exact call_pending _ _ _ _ _ equal
  case awaiting service ticket rest frames =>
    have fields : request state service ticket = called ∧ state = saved := by
      simpa only [Transition.call.injEq] using equal
    rw [← fields.1, ← fields.2]
    exact ⟨ticket, rest, frames, rfl⟩

theorem inspect_call_pending (operations : Operations) (state : Configuration)
    (called : Request) (saved : Configuration)
    (equal : inspect operations state = .call called saved) :
    ∃ ticket tail, saved.frames = .waiting called.service ticket :: tail ∧
      called = request saved called.service ticket :=
  transition_call_pending operations state _ (inspect_sound operations state) called saved equal

/-- A locally constructed current-endpoint reply has exactly the behavior
of the external reply checker. This justifies finite protocol fixtures;
it does not certify their evaluation or effect answers. -/
theorem fulfill_inspected_call (operations : Operations) (state : Configuration)
    (called : Request) (saved : Configuration) (value : ReplyValue) (charge : Nat)
    (equal : inspect operations state = .call called saved) :
    fulfillCurrent saved value charge = deliver saved ⟨called.endpoint, value, charge⟩ := by
  obtain ⟨ticket, rest, pending, requestEqual⟩ := inspect_call_pending operations state called saved equal
  have current := fulfillCurrent_correspondence saved value charge called.service ticket rest pending
  simpa only [← requestEqual] using current

/-! ## Productive administration and exact budget resumption -/

def frameRank : Frame → Nat
  | .prepared _ _ => 2
  | .rawReady _ _ _ => 1
  | .iterate snapshot _ => snapshot.pending.length + 1
  | .afterIterChild snapshot _ => snapshot.pending.length + 2
  | .afterOnlyChild _ _ _ _ => 1
  | _ => 0

def stackRank : List Frame → Nat
  | [] => 0
  | frame :: rest => frameRank frame + stackRank rest

def rank (state : Configuration) : Nat := stackRank state.frames

private theorem returned_pending {snapshot saved : Snapshot}
    (returned : NativeArgumentProjection.returnedChild snapshot = some saved) :
    saved.pending = snapshot.pending := by
  unfold NativeArgumentProjection.returnedChild at returned
  split at returned
  · cases returned
    rfl
  · contradiction

private theorem transition_silent_decreases (operations : Operations) (state after : Configuration)
    (transition : Advance) (related : AdvanceRel operations state transition)
    (silent : transition = .silent after) : rank after < rank state := by
  cases related <;> try simp [publish, call] at silent
  case raw arguments prepared rest frames raw notTransformed =>
    cases silent
    simp [rank, replace, frames, stackRank, frameRank]
  case rawFailed arguments prepared value rest frames failed =>
    cases silent
    simp [rank, replace, frames, stackRank, frameRank]
  case consume snapshot prepared rest action frames related =>
    cases related <;> simp only [consumed, publish, call] at silent
    case exhausted pending =>
      cases silent
      simp [rank, replace, frames, stackRank, frameRank, pending]
    case mergeFailed value evaluated remaining pending mergeFailed =>
      cases silent
      simp [rank, replace, frames, stackRank, frameRank,
        NativeArgumentProjection.pending_afterOutcome, pending]
    case error => contradiction
    case binderFailed value evaluated remaining merged pending mergedReply ordinary extended =>
      cases silent
      simp [rank, replace, frames, stackRank, frameRank,
        NativeArgumentProjection.pending_afterOutcome, pending]
    case selected => contradiction
  case returned snapshot prepared rest saved frames returned =>
    cases silent
    simp [rank, replace, frames, stackRank, frameRank, returned_pending returned]
  case onlyReturned arguments prepared value bindings rest frames =>
    cases silent
    simp [rank, replace, frames, stackRank, frameRank]

theorem silent_decreases (operations : Operations) (state after : Configuration)
    (related : AdvanceRel operations state (.silent after)) : rank after < rank state :=
  transition_silent_decreases operations state after (.silent after) related rfl

def machine (operations : Operations) : Machine Configuration Event Configuration Request :=
  ⟨fun state => some (inspect operations state)⟩

/-- No service termination or source-program termination is assumed. Every
silent administrative segment decreases the retained stack's rank; an
unanswered service remains a visible suspension. -/
def productive (operations : Operations) : (machine operations).Productive where
  rank := rank
  silent_decreases := by
    intro state next stepped
    have inspected : inspect operations state = .silent next := Option.some.inj stepped
    exact silent_decreases operations state next ((inspect_iff _ _ _).mp inspected)
  moves := by intro state; simp [machine]

theorem administrative_progress (operations : Operations) (state : Configuration) :
    ∃ k ≤ rank state, ∃ settled transition,
      (machine operations).run k state = ([], .exhausted settled) ∧
      (machine operations).step settled = some transition ∧ transition.administrative = false :=
  (productive operations).settles state

theorem resume_prefix (operations : Operations) (first second : Nat) (state residual : Configuration)
    (events : List Event)
    (paused : (machine operations).run first state = (events, .exhausted residual)) :
    (machine operations).run (first + second) state =
      (events ++ ((machine operations).run second residual).1,
        ((machine operations).run second residual).2) :=
  (machine operations).established_and_pending first second state residual events paused

theorem resume_account (operations : Operations) (price : Configuration → Nat)
    (first second : Nat) (state residual : Configuration) (events : List Event)
    (paused : (machine operations).run first state = (events, .exhausted residual)) :
    (machine operations).spent price (first + second) state =
      (machine operations).spent price first state + (machine operations).spent price second residual := by
  rw [Machine.spent_add, paused]
  rfl

/-- Looking at a suspended endpoint neither consumes its reply nor repeats
its effect. Repeated inspection returns the exact same saved state. -/
theorem awaiting_preserves (operations : Operations) (state : Configuration)
    (service : Waiting) (ticket : Nat) (rest : List Frame)
    (pending : state.frames = .waiting service ticket :: rest) :
    inspect operations state = .call (request state service ticket) state := by
  simp [inspect, pending]

theorem awaiting_run (operations : Operations) (state : Configuration)
    (service : Waiting) (ticket fuel : Nat) (rest : List Frame)
    (pending : state.frames = .waiting service ticket :: rest) :
    (machine operations).run (fuel + 1) state = ([], .suspended (request state service ticket) state) := by
  apply Machine.run_succ_call
  simp [machine, awaiting_preserves operations state service ticket rest pending]

/-! ## Retained interaction outcomes -/

/-- Refusal either ends the current interaction region or explicitly retries
the unchanged retained endpoint. This policy does not certify a service reply. -/
inductive RefusalPolicy where
  | stop | retry
  deriving Repr, DecidableEq

/-- Protocol boundaries retain the entire argument controller and the supplied
reply. Callback failures are separate from faults of argument administration. -/
inductive Interaction where
  | active (saved : Configuration)
  | refused (reason : Rejection) (saved : Configuration) (reply : Atom)
  | malformedReply (saved : Configuration) (reply : Atom)
  | callbackFault (saved : Configuration) (failure : Atom)
  | cancelled (saved : Configuration)
  deriving Repr

def rejectionData : Rejection → Atom
  | .noPending => .symbol "no-pending"
  | .endpointMismatch => .symbol "endpoint-mismatch"
  | .wrongKind => .symbol "wrong-kind"

def interactionData : Interaction → Atom
  | .active saved => .expression [.symbol "he-native-argument-interaction-v1",
      .symbol "active", configurationData saved]
  | .refused reason saved reply => .expression [.symbol "he-native-argument-interaction-v1",
      .symbol "refused", rejectionData reason, configurationData saved, reply]
  | .malformedReply saved reply => .expression [.symbol "he-native-argument-interaction-v1",
      .symbol "malformed-reply", configurationData saved, reply]
  | .callbackFault saved failure => .expression [.symbol "he-native-argument-interaction-v1",
      .symbol "callback-fault", configurationData saved, failure]
  | .cancelled saved => .expression [.symbol "he-native-argument-interaction-v1",
      .symbol "cancelled", configurationData saved]

def eventData : Event → Atom
  | .answer result => .expression [.symbol "answer", TypedApplyEncoding.resultData result]
  | .fault .invalidArgumentState => .expression [.symbol "argument-fault", .symbol "invalid-state"]
  | .fault .invalidChildPhase => .expression [.symbol "argument-fault", .symbol "invalid-child-phase"]

/-- Observation relabeling and a retained-state lift of the existing controller.
Its actual complete endpoint is the request; no request is performed here. -/
def interactionAdvance : Advance → Transition Interaction Atom Atom Atom
  | .silent next => .silent (.active next)
  | .publish events next => .publish (events.map eventData) (.active next)
  | .finish final => .finish (configurationData final)
  | .fail faults => .fail (faults.map eventData)
  | .call request saved => .call request.endpoint (.active saved)

def inspectInteraction (operations : Operations) (policy : RefusalPolicy) :
    Interaction → Transition Interaction Atom Atom Atom
  | .active saved => interactionAdvance (inspect operations saved)
  | .refused reason saved reply => match policy with
      | .stop => .finish (interactionData (.refused reason saved reply))
      | .retry => .silent (.active saved)
  | .malformedReply saved reply => match policy with
      | .stop => .finish (interactionData (.malformedReply saved reply))
      | .retry => .silent (.active saved)
  | .callbackFault saved failure => .finish (interactionData (.callbackFault saved failure))
  | .cancelled saved => .finish (interactionData (.cancelled saved))

def interactionMachine (operations : Operations) (policy : RefusalPolicy) :
    Machine Interaction Atom Atom Atom := ⟨fun saved => some (inspectInteraction operations policy saved)⟩

/-- Independent controller phase rules and explicit refusal/cancellation
boundaries. A retry is a policy action on its unchanged saved state. -/
inductive InteractionAdvanceRel (operations : Operations) (policy : RefusalPolicy) :
    Interaction → Transition Interaction Atom Atom Atom → Prop where
  | active (saved : Configuration) (advance : Advance)
      (earned : AdvanceRel operations saved advance) :
      InteractionAdvanceRel operations policy (.active saved) (interactionAdvance advance)
  | refusedStop (reason : Rejection) (saved : Configuration) (reply : Atom)
      (stopping : policy = .stop) :
      InteractionAdvanceRel operations policy (.refused reason saved reply)
        (.finish (interactionData (.refused reason saved reply)))
  | refusedRetry (reason : Rejection) (saved : Configuration) (reply : Atom)
      (retrying : policy = .retry) :
      InteractionAdvanceRel operations policy (.refused reason saved reply) (.silent (.active saved))
  | malformedStop (saved : Configuration) (reply : Atom) (stopping : policy = .stop) :
      InteractionAdvanceRel operations policy (.malformedReply saved reply)
        (.finish (interactionData (.malformedReply saved reply)))
  | malformedRetry (saved : Configuration) (reply : Atom) (retrying : policy = .retry) :
      InteractionAdvanceRel operations policy (.malformedReply saved reply) (.silent (.active saved))
  | callbackFault (saved : Configuration) (failure : Atom) :
      InteractionAdvanceRel operations policy (.callbackFault saved failure)
        (.finish (interactionData (.callbackFault saved failure)))
  | cancelled (saved : Configuration) :
      InteractionAdvanceRel operations policy (.cancelled saved)
        (.finish (interactionData (.cancelled saved)))

theorem inspectInteraction_sound (operations : Operations) (policy : RefusalPolicy) (saved : Interaction) :
    InteractionAdvanceRel operations policy saved (inspectInteraction operations policy saved) := by
  cases saved with
  | active saved => exact .active saved _ (inspect_sound operations saved)
  | refused reason saved reply => cases policy <;> constructor <;> rfl
  | malformedReply saved reply => cases policy <;> constructor <;> rfl
  | callbackFault saved failure => exact .callbackFault saved failure
  | cancelled saved => exact .cancelled saved

theorem inspectInteraction_complete {operations : Operations} {policy : RefusalPolicy}
    {saved : Interaction} {advance : Transition Interaction Atom Atom Atom}
    (earned : InteractionAdvanceRel operations policy saved advance) :
    inspectInteraction operations policy saved = advance := by
  cases earned with
  | active saved advance earned =>
      exact congrArg interactionAdvance (inspect_complete operations saved advance earned)
  | refusedStop reason saved reply stopping => simp only [inspectInteraction, stopping]
  | refusedRetry reason saved reply retrying => simp only [inspectInteraction, retrying]
  | malformedStop saved reply stopping => simp only [inspectInteraction, stopping]
  | malformedRetry saved reply retrying => simp only [inspectInteraction, retrying]
  | callbackFault | cancelled => rfl

theorem interaction_step_iff (operations : Operations) (policy : RefusalPolicy) (saved : Interaction)
    (advance : Transition Interaction Atom Atom Atom) :
    (interactionMachine operations policy).step saved = some advance ↔
      InteractionAdvanceRel operations policy saved advance := by
  constructor
  · intro stepped
    have exactAdvance : inspectInteraction operations policy saved = advance := Option.some.inj stepped
    rw [← exactAdvance]
    exact inspectInteraction_sound operations policy saved
  · intro earned
    exact congrArg some (inspectInteraction_complete earned)

theorem interaction_step_ne_none (operations : Operations) (policy : RefusalPolicy) (saved : Interaction) :
    (interactionMachine operations policy).step saved ≠ none := by
  intro impossible
  cases impossible

end Mettapedia.Languages.MeTTa.HE.NativeArgumentControlMachine
