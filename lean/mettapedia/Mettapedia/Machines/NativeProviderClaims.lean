import Std

/-!
# Native transport resource claims

The active frontier contains only current transport claims, not the archive.
Capacity and an interactive reserve describe transport resources. They are
not work, token or retry quotas. The source implementation's arbitrary
identifier-length and capacity ceilings are not part of this native model.
A zero reserve means that no slots are reserved for interactive work.

Owner/transport identity, complete scoped observations, durable publication
and the external executor are separate contracts. In particular, registering
dispatch intent is not evidence of provider acceptance and does not itself
perform a send. A replay grants no new execution.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NativeProviderClaims

inductive Lane where
  | interactive | background
  deriving DecidableEq, Repr

inductive Activity where
  | exclusive
  | named (identity : String) (lane : Lane)
  deriving DecidableEq, Repr

structure Claim where
  call : String
  owner : String
  process : String
  activity : Activity
  deriving DecidableEq, Repr

structure Policy where
  capacity : Nat
  reserve : Nat
  deriving DecidableEq, Repr

def validPolicy (policy : Policy) : Bool :=
  0 < policy.capacity && policy.reserve < policy.capacity

def background : Claim → Bool
  | ⟨_, _, _, .named _ .background⟩ => true
  | _ => false

def conflicting (incoming : Claim) (old : Claim) : Bool :=
  old.call == incoming.call || match old.activity, incoming.activity with
  | .exclusive, _ | _, .exclusive => true
  | .named oldName _, .named newName _ => oldName == newName

def eligible (policy : Policy) (active : List Claim) (incoming : Claim) : Bool :=
  validPolicy policy &&
    !active.any (conflicting incoming) &&
    active.length < policy.capacity &&
    (!background incoming || (active.filter background).length < policy.capacity - policy.reserve)

def acquire (policy : Policy) (active : List Claim) (incoming : Claim) : Option (List Claim) :=
  if eligible policy active incoming then some (active ++ [incoming]) else none

theorem an_accepted_claim_is_appended (policy : Policy) (active next : List Claim) (incoming : Claim)
    (accepted : acquire policy active incoming = some next) : next = active ++ [incoming] := by
  unfold acquire at accepted
  split at accepted
  · exact (Option.some.inj accepted).symm
  · cases accepted

theorem refusal_does_not_publish_a_partial_frontier (policy : Policy) (active : List Claim)
    (incoming : Claim) (refused : eligible policy active incoming = false) :
    acquire policy active incoming = none := by simp [acquire, refused]

theorem accepted_claim_has_capacity (policy : Policy) (active next : List Claim) (incoming : Claim)
    (accepted : acquire policy active incoming = some next) : next.length ≤ policy.capacity := by
  unfold acquire at accepted
  split at accepted
  · rename_i allowed
    have bound : active.length < policy.capacity := by
      have facts := allowed
      simp [eligible] at facts
      exact facts.1.2
    have same := (Option.some.inj accepted).symm
    subst next
    simp only [List.length_append, List.length_singleton]
    omega
  · cases accepted

theorem duplicate_call_or_activity_is_not_acquired (policy : Policy) (active : List Claim)
    (incoming old : Claim) (member : old ∈ active) (conflict : conflicting incoming old = true) :
    acquire policy active incoming = none := by
  have any : active.any (conflicting incoming) = true := List.any_eq_true.mpr ⟨old, member, conflict⟩
  simp [acquire, eligible, any]

theorem a_second_identical_claim_is_not_new (policy : Policy) (active : List Claim) (incoming : Claim) :
    acquire policy (active ++ [incoming]) incoming = none := by
  apply duplicate_call_or_activity_is_not_acquired policy _ incoming incoming (by simp)
  simp [conflicting]

theorem background_claim_respects_reserve (policy : Policy) (active next : List Claim) (incoming : Claim)
    (isBackground : background incoming = true)
    (accepted : acquire policy active incoming = some next) :
    (next.filter background).length ≤ policy.capacity - policy.reserve := by
  unfold acquire at accepted
  split at accepted
  · rename_i allowed
    have bound : (active.filter background).length < policy.capacity - policy.reserve := by
      have facts := allowed
      simp [eligible, isBackground] at facts
      exact facts.2
    have same := (Option.some.inj accepted).symm
    subst next
    have step : (active.filter background).length + 1 ≤ policy.capacity - policy.reserve := by omega
    simpa [List.filter_append, isBackground] using step
  · cases accepted

def retire (active : List Claim) (call : String) : List Claim :=
  active.filter fun claim => claim.call != call

theorem a_released_call_is_absent (active : List Claim) (call : String) (claim : Claim)
    (member : claim ∈ retire active call) : claim.call ≠ call := by
  simpa [retire] using (List.mem_filter.mp member).2

theorem release_preserves_unrelated_claims (active : List Claim) (call : String) (claim : Claim)
    (different : claim.call ≠ call) : claim ∈ retire active call ↔ claim ∈ active := by
  simp [retire, different]

inductive DispatchState where
  | reserved | intent (transport : String) | ended
  deriving DecidableEq, Repr

def registerIntent (state : DispatchState) (transport : String) : Option DispatchState :=
  match state with
  | .reserved => some (.intent transport)
  | _ => none

theorem intent_is_registered_only_from_reserved (state : DispatchState) (transport : String) :
    (registerIntent state transport).isSome = true ↔ state = .reserved := by
  cases state <;> simp [registerIntent]

theorem intent_cannot_be_registered_twice (first second : String) :
    registerIntent (.intent first) second = none := rfl

inductive ProcessObservation where
  | live | exited | unavailable
  deriving DecidableEq, Repr

inductive Recovery where
  | keep | releaseUnsent | preserveUnknown
  deriving DecidableEq, Repr

def recover (state : DispatchState) (observation : ProcessObservation) : Recovery :=
  match observation, state with
  | .exited, .reserved => .releaseUnsent
  | .exited, .intent _ => .preserveUnknown
  | _, _ => .keep

theorem unavailable_is_not_death (state : DispatchState) : recover state .unavailable = .keep := by
  cases state <;> rfl

theorem death_before_intent_is_unsent : recover .reserved .exited = .releaseUnsent := rfl
theorem death_after_intent_is_unknown (transport : String) :
    recover (.intent transport) .exited = .preserveUnknown := rfl

/-! A terminal resource observation is independent of process death. These
pure transitions describe captured, well-formed application facts. Storage
publication, transport authentication and usage merging remain their own
contracts; this model neither stops a transport nor authorizes a send. -/

inductive LeasePhase where
  | active | completed | failed | unknown
  deriving DecidableEq, Repr

structure Lease where
  owner : String
  phase : LeasePhase
  deriving DecidableEq, Repr

inductive EndReason where
  | unsent | failed | unknown | completed
  deriving DecidableEq, Repr

inductive ResourceStage where
  | reserved | dispatched (transport : String) | ended (reason : EndReason)
  deriving DecidableEq, Repr

structure Intent where
  owner : String
  process : String
  transport : String
  deriving DecidableEq, Repr

structure TerminalFocus where
  claim : Claim
  stage : ResourceStage
  lease : Option Lease
  answer : Option String
  intent : Option Intent
  attempt : Option String
  frontier : List Claim
  index : Option Claim
  deriving DecidableEq, Repr

inductive Closure where
  | running | unavailable | failed (transport : String) | unknown (transport : String)
  deriving DecidableEq, Repr

inductive EndCommand where
  | abandon | close (observation : Closure)
  deriving DecidableEq, Repr

def endLease (owner : String) (lease : Option Lease) (answer : Option String)
    (phase : LeasePhase) : Option Lease :=
  match lease, answer with
  | some ⟨who, .active⟩, none => if who == owner then some ⟨owner, phase⟩ else lease
  | _, _ => lease

def releaseResource (state : TerminalFocus) (reason : EndReason) (phase : LeasePhase) : TerminalFocus :=
  { state with
    stage := .ended reason
    frontier := retire state.frontier state.claim.call
    index := none
    lease := endLease state.claim.owner state.lease state.answer phase }

def validClaim (claim : Claim) : Bool :=
  !claim.call.isEmpty && !claim.owner.isEmpty && !claim.process.isEmpty &&
    match claim.activity with
    | .exclusive => true
    | .named name _ => !name.isEmpty

def validFrontier : List Claim → Bool
  | [] => true
  | claim :: rest => validClaim claim && !rest.any (conflicting claim) && validFrontier rest

def aligned (state : TerminalFocus) : Bool :=
  validFrontier state.frontier &&
    state.frontier.find? (fun c => c.call == state.claim.call) == some state.claim &&
    state.index == some state.claim

def registered (state : TerminalFocus) (transport : String) : Bool :=
  state.intent == some ⟨state.claim.owner, state.claim.process, transport⟩ &&
    state.attempt == some transport

/-- First resource-release projection. `none` means no first release, not a
particular public refusal code or absence of a separate usage update. -/
def terminate (state : TerminalFocus) (owner process : String) (command : EndCommand) :
    Option TerminalFocus :=
  if owner != state.claim.owner || process != state.claim.process then none else
  match command, state.stage with
  | .abandon, .reserved =>
    if aligned state && state.intent.isNone && state.attempt.isNone && state.answer.isNone then
      some (releaseResource state .unsent .failed) else none
  | .close (.failed transport), .dispatched physical =>
    if physical == transport && registered state transport && aligned state then
      some (releaseResource state .failed .failed) else none
  | .close (.unknown transport), .dispatched physical =>
    if physical == transport && registered state transport && aligned state then
      some (releaseResource state .unknown .unknown) else none
  | _, _ => none

theorem release_preserves_the_answer (state : TerminalFocus) (reason : EndReason) (phase : LeasePhase) :
    (releaseResource state reason phase).answer = state.answer := rfl

theorem release_preserves_dispatch_and_attempt (state : TerminalFocus) (reason : EndReason)
    (phase : LeasePhase) :
    ((releaseResource state reason phase).intent, (releaseResource state reason phase).attempt) =
      (state.intent, state.attempt) := rfl

theorem release_clears_the_matching_index (state : TerminalFocus) (reason : EndReason) (phase : LeasePhase) :
    (releaseResource state reason phase).index = none := rfl

theorem released_frontier_has_no_call (state : TerminalFocus) (reason : EndReason)
    (phase : LeasePhase) (claim : Claim)
    (member : claim ∈ (releaseResource state reason phase).frontier) :
    claim.call ≠ state.claim.call := a_released_call_is_absent _ _ _ member

theorem release_keeps_other_resources (state : TerminalFocus) (reason : EndReason)
    (phase : LeasePhase) (claim : Claim) (other : claim.call ≠ state.claim.call) :
    claim ∈ (releaseResource state reason phase).frontier ↔ claim ∈ state.frontier :=
  release_preserves_unrelated_claims _ _ _ other

theorem another_owners_lease_is_preserved (owner who : String) (old next : LeasePhase)
    (answer : Option String) (different : who ≠ owner) :
    endLease owner (some ⟨who, old⟩) answer next = some ⟨who, old⟩ := by
  cases old <;> cases answer <;> simp [endLease, different]

theorem an_existing_answer_keeps_the_lease (owner answer : String) (lease : Option Lease)
    (phase : LeasePhase) : endLease owner lease (some answer) phase = lease := by
  cases lease with
  | none => rfl
  | some lease => cases lease with | mk who old => cases old <;> rfl

theorem wrong_resource_owner_is_refused (state : TerminalFocus) (owner process : String)
    (command : EndCommand) (different : owner ≠ state.claim.owner) :
    terminate state owner process command = none := by simp [terminate, different]

theorem wrong_process_incarnation_is_refused (state : TerminalFocus) (owner process : String)
    (command : EndCommand) (different : process ≠ state.claim.process) :
    terminate state owner process command = none := by simp [terminate, different]

theorem running_transport_is_not_closed (state : TerminalFocus) (owner process : String) :
    terminate state owner process (.close .running) = none := by
  simp only [terminate]
  split <;> rfl

theorem unavailable_transport_is_not_closed (state : TerminalFocus) (owner process : String) :
    terminate state owner process (.close .unavailable) = none := by
  simp only [terminate]
  split <;> rfl

theorem reserved_abandonment_needs_no_death (state : TerminalFocus)
    (reserved : state.stage = .reserved) (ready : aligned state = true)
    (noIntent : state.intent = none) (noAttempt : state.attempt = none)
    (noAnswer : state.answer = none) :
    terminate state state.claim.owner state.claim.process .abandon =
      some (releaseResource state .unsent .failed) := by
  simp [terminate, reserved, ready, noIntent, noAttempt, noAnswer]

theorem registered_closed_transport_can_release (state : TerminalFocus) (transport : String)
    (dispatched : state.stage = .dispatched transport) (ready : aligned state = true)
    (sameIntent : registered state transport = true) :
    terminate state state.claim.owner state.claim.process (.close (.failed transport)) =
      some (releaseResource state .failed .failed) := by
  simp [terminate, dispatched, ready, sameIntent]

theorem unknown_closure_can_release_without_a_false_answer (state : TerminalFocus) (transport : String)
    (dispatched : state.stage = .dispatched transport) (ready : aligned state = true)
    (sameIntent : registered state transport = true) :
    terminate state state.claim.owner state.claim.process (.close (.unknown transport)) =
      some (releaseResource state .unknown .unknown) := by
  simp [terminate, dispatched, ready, sameIntent]

theorem resource_release_never_returns_to_reserved (state : TerminalFocus) (reason : EndReason)
    (phase : LeasePhase) : (releaseResource state reason phase).stage ≠ .reserved := by
  simp [releaseResource]

theorem releasing_twice_does_not_remove_more_resources (state : TerminalFocus)
    (first second : EndReason) (p q : LeasePhase) :
    (releaseResource (releaseResource state first p) second q).frontier =
      (releaseResource state first p).frontier := by
  simp [releaseResource, retire, List.filter_filter]

theorem an_ended_resource_has_no_second_first_release (state : TerminalFocus)
    (reason : EndReason) (phase : LeasePhase) (owner process : String) (command : EndCommand) :
    terminate (releaseResource state reason phase) owner process command = none := by
  cases command with
  | abandon => simp [terminate, releaseResource]
  | close observation => cases observation <;> simp [terminate, releaseResource]

theorem an_existing_intent_prevents_unsent_abandonment (state : TerminalFocus)
    (intent : Intent) (present : state.intent = some intent) (owner process : String) :
    terminate state owner process .abandon = none := by
  unfold terminate
  split
  · rfl
  · cases state.stage <;> simp [present]

theorem a_terminal_lease_is_preserved (owner who : String) (old next : LeasePhase)
    (answer : Option String) (terminal : old ≠ .active) :
    endLease owner (some ⟨who, old⟩) answer next = some ⟨who, old⟩ := by
  cases old <;> cases answer <;> simp_all [endLease]

structure TerminalInput where
  stage : Nat
  lease : Nat
  answer : Bool
  intent : Nat
  owner : Bool
  process : Bool
  command : Nat
  indexed : Bool
  deriving Repr

def terminalInputState (input : TerminalInput) : TerminalFocus :=
  let claim : Claim := ⟨"call", "owner", "process", .named "A" .interactive⟩
  let other : Claim := ⟨"other-call", "owner", "process", .named "B" .interactive⟩
  { claim
    stage := match input.stage with
      | 0 => .reserved | 1 => .dispatched "transport" | 2 => .ended .unsent
      | 3 => .ended .failed | 4 => .ended .unknown | _ => .ended .completed
    lease := match input.lease with
      | 0 => some ⟨"owner", .active⟩ | 1 => some ⟨"successor", .active⟩
      | 2 => some ⟨"owner", .completed⟩ | 3 => some ⟨"owner", .failed⟩
      | 4 => some ⟨"owner", .unknown⟩ | _ => none
    answer := if input.answer then some "transport" else none
    intent := match input.intent with
      | 0 => none | 1 => some ⟨"owner", "process", "transport"⟩
      | 2 => some ⟨"owner", "process", "different"⟩
      | _ => some ⟨"owner", "other-process", "transport"⟩
    attempt := if input.intent == 0 then none else some "transport"
    frontier := if input.stage < 2 then [claim, other] else [other]
    index := if input.stage < 2 && input.indexed then some claim else none }

def terminalInputCommand (code : Nat) : EndCommand :=
  match code with
  | 0 => .abandon | 1 => .close (.failed "transport") | 2 => .close (.unknown "transport")
  | 3 => .close .running | _ => .close .unavailable

def terminalProjection (state : TerminalFocus) : String :=
  String.intercalate ","
    [toString (match state.stage with
      | .reserved => 0 | .dispatched _ => 1 | .ended .unsent => 2
      | .ended .failed => 3 | .ended .unknown => 4 | .ended .completed => 5),
     toString (match state.lease with
      | some ⟨"owner", .active⟩ => 0 | some ⟨_, .active⟩ => 1
      | some ⟨_, .completed⟩ => 2 | some ⟨_, .failed⟩ => 3
      | some ⟨_, .unknown⟩ => 4 | none => 5),
     if state.frontier.any (fun c => c.call == "call") then "1" else "0",
     if state.index.isSome then "1" else "0"]

def terminalCases : List TerminalInput :=
  let ordinary := [0, 1].flatMap fun stage => (List.range 6).flatMap fun lease =>
    [false, true].flatMap fun answer => (List.range 5).map fun command =>
      TerminalInput.mk stage lease answer (if stage == 0 then 0 else 1) true true command true
  let separated := (List.range 4).flatMap fun intent => [false, true].flatMap fun owner =>
    [false, true].flatMap fun process => [false, true].flatMap fun indexed =>
      [0, 1, 2].map fun command => TerminalInput.mk 1 0 false intent owner process command indexed
  let ended := [2, 3, 4, 5].flatMap fun stage => [0, 1, 2].map fun command =>
    TerminalInput.mk stage 0 false (if stage == 2 then 0 else 1) true true command true
  ordinary ++ separated ++ ended

def terminalInputs : String := "NATIVE_TERMINAL_INPUTS " ++ String.intercalate " "
  (terminalCases.map fun input => String.intercalate ","
    [toString input.stage, toString input.lease, if input.answer then "1" else "0",
     toString input.intent, if input.owner then "1" else "0", if input.process then "1" else "0",
     toString input.command, if input.indexed then "1" else "0"])

def terminalTrace : String := "NATIVE_TERMINAL_STATES " ++ String.intercalate " "
  (terminalCases.map fun input =>
    let state := terminalInputState input
    terminalProjection ((terminate state (if input.owner then "owner" else "stranger")
      (if input.process then "process" else "other-process") (terminalInputCommand input.command)).getD state))

def traceCases : List (Policy × List Claim × Claim) :=
  let i := fun call activity => Claim.mk call "owner" "process" activity
  let policy : Policy := ⟨2, 1⟩
  let a := i "a" (.named "A" .background)
  let b := i "b" (.named "B" .interactive)
  [ (policy, [], a),
    (policy, [a], i "b" (.named "B" .background)),
    (policy, [a], b),
    (policy, [a, b], i "c" (.named "C" .interactive)),
    (policy, [a], i "b" (.named "A" .interactive)),
    (policy, [i "a" .exclusive], b),
    (policy, [a], i "b" .exclusive),
    (policy, [], i "a" .exclusive),
    (⟨1, 0⟩, [], a),
    (⟨32, 1⟩, [a], b),
    (⟨0, 0⟩, [], a) ]

def trace : String := "NATIVE_CLAIM_SCHEDULING " ++ String.intercalate " "
  (traceCases.map fun (policy, active, incoming) => if eligible policy active incoming then "eligible" else "busy")

def activityInput : Activity → String
  | .exclusive => "x"
  | .named name .interactive => "i:" ++ name
  | .named name .background => "b:" ++ name

def claimInput (claim : Claim) : String := claim.call ++ "," ++ activityInput claim.activity

def traceInputs : String := "NATIVE_CLAIM_INPUTS " ++ String.intercalate " "
  (traceCases.map fun (policy, active, incoming) =>
    toString policy.capacity ++ "," ++ toString policy.reserve ++ "|" ++
      String.intercalate ";" (active.map claimInput) ++ "|" ++ claimInput incoming)

def recoveryCases : List (DispatchState × ProcessObservation) :=
  [.reserved, .intent "transport", .ended].flatMap fun state =>
    [.live, .exited, .unavailable].map fun observation => (state, observation)

def recoveryInputs : String := "NATIVE_CLAIM_RECOVERY_INPUTS " ++ String.intercalate " "
  (recoveryCases.map fun (state, observation) =>
    (match state with | .reserved => "reserved" | .intent _ => "intent" | .ended => "ended") ++ "," ++
    (match observation with | .live => "live" | .exited => "exited" | .unavailable => "unavailable"))

def recoveryTrace : String := "NATIVE_CLAIM_RECOVERY " ++ String.intercalate " "
  (recoveryCases.map fun (state, observation) => match recover state observation with
    | .keep => "keep" | .releaseUnsent => "unsent" | .preserveUnknown => "unknown")

end Mettapedia.Machines.NativeProviderClaims

#eval IO.println Mettapedia.Machines.NativeProviderClaims.trace
#eval IO.println Mettapedia.Machines.NativeProviderClaims.traceInputs
#eval IO.println Mettapedia.Machines.NativeProviderClaims.recoveryInputs
#eval IO.println Mettapedia.Machines.NativeProviderClaims.recoveryTrace
#eval IO.println Mettapedia.Machines.NativeProviderClaims.terminalInputs
#eval IO.println Mettapedia.Machines.NativeProviderClaims.terminalTrace
