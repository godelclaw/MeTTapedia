import Std

/-!
# Native transport resource claims

The active frontier contains only current transport claims, not the archive.
Capacity and an interactive reserve describe transport resources. They are
not work, token or retry quotas. The source implementation's arbitrary
identifier-length and capacity ceilings are not part of this native model.

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
