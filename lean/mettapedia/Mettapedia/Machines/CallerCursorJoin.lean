import Mathlib.Tactic

/-!
# Closed callee cursors resume a caller's binding snapshot

The reference recursively observes an admitted callee trace and matches every
completed value under the saved bindings. A matcher can reject after writing
partial bindings; the source discards that working state. The target retains
its working store and restores the snapshot before every subsequent attempt.
Committed world effects survive rejected matches and caller alternatives.

This finite boundary-trace refinement preserves producer/caller chronology,
duplicates, interruption, invalidation and every physical boundary prefix. A
caller transition summarizes its admitted continuation trace. Pointer transport,
live native execution, intra-caller scheduling and authored source fuel remain
separate C correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CallerCursorJoin

variable {Key Value World Effect Answer : Type}

abbrev Bindings (Key Value : Type) := Key → Option Value

def put [DecidableEq Key] (env : Bindings Key Value) (key : Key) (value : Value) : Bindings Key Value :=
  fun query => if query = key then some value else env query

def meet [DecidableEq Key] [DecidableEq Value] (env : Bindings Key Value) (key : Key) (value : Value) :
    Option (Bindings Key Value) :=
  match env key with
  | none => some (put env key value)
  | some old => if old = value then some env else none

structure MatchResult (Key Value : Type) where
  bindings : Bindings Key Value
  accepted : Bool

/-- One slot is a specialization of the same relational destination service. -/
def slot [DecidableEq Key] [DecidableEq Value] (key : Key) (env : Bindings Key Value) (value : Value) : MatchResult Key Value :=
  match meet env key value with
  | none => ⟨env, false⟩
  | some bound => ⟨bound, true⟩

inductive Event (Value Effect : Type) where
  | value (payload : Value)
  | effect (operation : Effect)
  | interrupted
  | invalidated
  deriving DecidableEq, Repr

inductive Observation (Effect Answer : Type) where
  | effect (operation : Effect)
  | published (answer : Answer)
  deriving DecidableEq, Repr

inductive Stop where
  | paused
  | complete
  | cancelled
  | invalidated
  deriving DecidableEq, Repr

structure Result (World Value Effect Answer : Type) where
  world : World
  trace : List (Observation Effect Answer)
  remaining : List (Event Value Effect)
  stop : Stop

structure CallerResult (Key Value World Effect Answer : Type) where
  world : World
  bindings : Bindings Key Value
  trace : List (Observation Effect Answer)

structure State (Key Value World Effect : Type) where
  world : World
  bindings : Bindings Key Value
  remaining : List (Event Value Effect)

variable (snapshot : Bindings Key Value)
    (destination : Bindings Key Value → Value → MatchResult Key Value)
    (effect : World → Effect → World)
    (caller : World → Bindings Key Value → Value → CallerResult Key Value World Effect Answer)

def reference : Nat → List (Event Value Effect) → World → Result World Value Effect Answer
  | 0, events, world => ⟨world, [], events, .paused⟩
  | _ + 1, [], world => ⟨world, [], [], .complete⟩
  | budget + 1, .effect operation :: rest, world =>
      let suffix := reference budget rest (effect world operation)
      {suffix with trace := .effect operation :: suffix.trace}
  | budget + 1, .value value :: rest, world =>
      let matched := destination snapshot value
      if matched.accepted then
        let child := caller world matched.bindings value
        let suffix := reference budget rest child.world
        {suffix with trace := child.trace ++ suffix.trace}
      else reference budget rest world
  | _ + 1, .interrupted :: rest, world => ⟨world, [], rest, .cancelled⟩
  | _ + 1, .invalidated :: rest, world => ⟨world, [], rest, .invalidated⟩

def target : Nat → State Key Value World Effect → Result World Value Effect Answer
  | 0, state => ⟨state.world, [], state.remaining, .paused⟩
  | budget + 1, state =>
      let restored := {state with bindings := snapshot}
      match state.remaining with
      | [] => ⟨state.world, [], [], .complete⟩
      | .effect operation :: rest =>
          let suffix := target budget {restored with world := effect state.world operation, remaining := rest}
          {suffix with trace := .effect operation :: suffix.trace}
      | .value value :: rest =>
          let matched := destination restored.bindings value
          if matched.accepted then
            let child := caller state.world matched.bindings value
            let suffix := target budget ⟨child.world, child.bindings, rest⟩
            {suffix with trace := child.trace ++ suffix.trace}
          else target budget ⟨state.world, matched.bindings, rest⟩
      | .interrupted :: rest => ⟨state.world, [], rest, .cancelled⟩
      | .invalidated :: rest => ⟨state.world, [], rest, .invalidated⟩

theorem target_refines (allowance : Nat)
    (events : List (Event Value Effect)) (world : World) (current : Bindings Key Value) :
    target snapshot destination effect caller allowance ⟨world, current, events⟩ =
      reference snapshot destination effect caller allowance events world := by
  induction allowance generalizing events world current with
  | zero => rfl
  | succ budget ih =>
      cases events with
      | nil => rfl
      | cons event rest =>
          cases event <;> simp [target, reference, ih]

theorem current_bindings_cannot_leak (allowance : Nat) (events : List (Event Value Effect))
    (world : World) (left right : Bindings Key Value) :
    target snapshot destination effect caller allowance ⟨world, left, events⟩ =
      target snapshot destination effect caller allowance ⟨world, right, events⟩ := by
  cases allowance <;> rfl

namespace Controls

def empty : Bindings Nat Nat := fun _ => none

def emit (world : Nat) (env : Bindings Nat Nat) (value : Nat) :
    CallerResult Nat Nat Nat Nat Nat :=
  ⟨world + 1, env, [.published value]⟩

def effects (world operation : Nat) := world + operation

theorem duplicate_values_are_not_deduplicated :
    (target empty (slot 0) effects emit 3 ⟨0, empty, [.value 7, .value 7]⟩).trace =
      [.published 7, .published 7] := by decide +kernel

theorem producer_and_caller_effects_keep_chronology :
    (target empty (slot 0) effects emit 5
      ⟨0, empty, [.effect 3, .value 7, .effect 4, .value 9]⟩).trace =
      [.effect 3, .published 7, .effect 4, .published 9] ∧
    (target empty (slot 0) effects emit 5
      ⟨0, empty, [.effect 3, .value 7, .effect 4, .value 9]⟩).world = 9 := by
  decide +kernel

theorem interruption_preserves_the_published_prefix :
    (target empty (slot 0) effects emit 8
      ⟨0, empty, [.effect 3, .value 7, .interrupted, .effect 99, .value 9]⟩).trace =
      [.effect 3, .published 7] ∧
    (target empty (slot 0) effects emit 8
      ⟨0, empty, [.effect 3, .value 7, .interrupted, .effect 99, .value 9]⟩).stop = .cancelled := by
  decide +kernel

theorem invalidation_is_not_logical_exhaustion :
    (target empty (slot 0) effects emit 1 ⟨0, empty, [.invalidated]⟩).stop = .invalidated ∧
      (target empty (slot 0) effects emit 1 ⟨0, empty, []⟩).stop = .complete := by
  decide +kernel

theorem prior_receiver_binding_is_restored :
    (target empty (slot 0) effects emit 3
      ⟨0, put empty 0 99, [.value 7, .value 9]⟩).trace = [.published 7, .published 9] := by
  decide +kernel

/-- The predecessor mistake: meet the second return against the previous
caller's destination, so a distinct answer disappears. -/
def withoutRestore (values : List Nat) (env : Bindings Nat Nat) : List Nat :=
  match values with
  | [] => []
  | value :: rest => match meet env 0 value with
    | none => withoutRestore rest env
    | some bound => value :: withoutRestore rest bound

theorem missing_rollback_loses_a_distinct_answer :
    withoutRestore [7, 9] empty = [7] ∧
      (target empty (slot 0) effects emit 3 ⟨0, empty, [.value 7, .value 9]⟩).trace =
        [.published 7, .published 9] := by decide +kernel

/-- A relational pattern binds a repeated payload slot, then checks a literal.
Its failed prefix remains in the working store, as in an in-place matcher. -/
def nineOnly (env : Bindings Nat Nat) (value : Nat) : MatchResult Nat Nat :=
  match meet env 0 value with
  | none => ⟨env, false⟩
  | some bound => ⟨bound, decide (value = 9)⟩

theorem bound_destination_keeps_duplicate_matches :
    (target (put empty 0 7) (slot 0) effects emit 4
      ⟨0, empty, [.value 7, .value 7, .value 9]⟩).trace =
        [.published 7, .published 7] := by decide +kernel

theorem partial_rejection_cannot_poison_later_match :
    (target empty nineOnly effects emit 4
      ⟨0, empty, [.value 7, .value 7, .value 9]⟩).trace = [.published 9] := by
  decide +kernel

theorem rejected_matches_keep_committed_effects :
    (target empty nineOnly effects emit 5
      ⟨0, empty, [.effect 3, .value 7, .effect 4, .value 9]⟩).trace =
      [.effect 3, .effect 4, .published 9] ∧
    (target empty nineOnly effects emit 5
      ⟨0, empty, [.effect 3, .value 7, .effect 4, .value 9]⟩).world = 8 := by
  decide +kernel

theorem rejected_prefix_can_resume :
    (target empty nineOnly effects emit 1
      ⟨0, empty, [.value 7, .value 9]⟩).remaining = [.value 9] ∧
    (target empty nineOnly effects emit 1
      ⟨0, empty, [.value 7, .value 9]⟩).stop = .paused ∧
    (target empty nineOnly effects emit 2
      ⟨0, put empty 0 7, [.value 9]⟩).trace = [.published 9] := by decide +kernel

def withoutRelationalRestore (values : List Nat) (env : Bindings Nat Nat) : List Nat :=
  match values with
  | [] => []
  | value :: rest =>
      let matched := nineOnly env value
      (if matched.accepted then [value] else []) ++
        withoutRelationalRestore rest matched.bindings

theorem partial_rollback_fault_is_detected :
    withoutRelationalRestore [7, 7, 9] empty = [] ∧
      (target empty nineOnly effects emit 4
        ⟨0, empty, [.value 7, .value 7, .value 9]⟩).trace = [.published 9] := by
  decide +kernel

end Controls
end Mettapedia.Machines.CallerCursorJoin
