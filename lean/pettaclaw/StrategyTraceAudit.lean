import Std

/-!
# Read-only audit of recorded managed-host transitions

This monitor checks selected safety rules of `ObservedStrategy` on concrete
ledger traces. It is a partial observation model, not a replacement strategy.
The adapter must supply an injective identity map and faithful snapshots,
receipts and events from one atomic database view. Clock/budget enforcement,
external input detection, physical effects, payload presentation and the
soundness of task checkers are not established by this audit.
-/

namespace StrategyTraceAudit

structure Capture where
  serial : Nat
  request : Nat
  revision : Nat
  mode : Nat
  executable : List Nat
  permitted : List Nat
deriving DecidableEq, Repr

structure Action where
  ticket : Nat
  request : Nat
  reported : Bool := false
  observed : Bool := false
  success : Bool := false
  reserved : List Nat := []
  results : List Nat := []
deriving DecidableEq, Repr

structure State where
  revision : Nat := 0
  mode : Nat := 0
  paused : Bool := false
  nextSerial : Nat := 0
  pending : Option Capture := none
  accepted : List Nat := []
  active : List Nat := []
  actions : List Action := []
deriving DecidableEq, Repr

inductive Event where
  | deliver (request : Nat)
  | control (mode : Nat) (paused : Bool)
  | restore
  | capture (snapshot : Capture)
  | command (serial ticket request tool : Nat)
  | otherReply (serial : Nat)
  | reserve (ticket position : Nat)
  | commandResult (ticket position : Nat)
  | report (ticket : Nat) (success : Bool)
  | observe (ticket : Nat)
  | attest (request ticket : Nat)
  | finish (request ticket : Nat)
  | cancel (request : Nat)
  | neutral
deriving DecidableEq, Repr

def settled (s : State) : Bool := s.actions.all (fun a => a.reported && a.observed)

def modify (s : State) (ticket : Nat) (f : Action → Action) : State :=
  { s with actions := s.actions.map (fun a => if a.ticket = ticket then f a else a) }

def find (s : State) (ticket : Nat) : Option Action :=
  s.actions.find? (fun a => a.ticket == ticket)

def step (s : State) : Event → Option State
  | .deliver request =>
      if request ∈ s.accepted then none else
      some { s with revision := s.revision + 1,
                    accepted := s.accepted ++ [request], active := s.active ++ [request] }
  | .control mode paused =>
      some { s with revision := s.revision + 1, mode := mode, paused := paused }
  | .restore => some { s with revision := s.revision + 1, pending := none }
  | .capture snap =>
      if !s.paused && s.pending.isNone && settled s &&
          decide (snap.serial = s.nextSerial ∧ snap.revision = s.revision ∧
                  snap.mode = s.mode ∧ snap.request ∈ s.active) then
        some { s with nextSerial := s.nextSerial + 1, pending := some snap }
      else none
  | .command serial ticket request tool => do
      let snap ← s.pending
      if !s.paused && settled s &&
          decide (serial = snap.serial ∧ snap.revision = s.revision ∧
                  snap.mode = s.mode ∧ request = snap.request ∧ request ∈ s.active ∧
                  tool ∈ snap.executable ∧ tool ∈ snap.permitted ∧
                  (find s ticket).isNone = true) then
        some { s with pending := none, actions := s.actions ++ [{ ticket := ticket, request := request }] }
      else none
  | .otherReply serial => do
      let snap ← s.pending
      if serial = snap.serial then some { s with pending := none } else none
  | .reserve ticket position => do
      let action ← find s ticket
      if !action.reported && decide (position = action.reserved.length) then
        some (modify s ticket (fun a => { a with reserved := a.reserved ++ [position] }))
      else none
  | .commandResult ticket position => do
      let action ← find s ticket
      if position ∈ action.reserved ∧ position ∉ action.results then
        some (modify s ticket (fun a => { a with results := a.results ++ [position] }))
      else none
  | .report ticket success => do
      let action ← find s ticket
      if !action.reported then
        some { modify s ticket (fun a => { a with reported := true, success := success }) with
               revision := s.revision + 1 }
      else none
  | .observe ticket => do
      let action ← find s ticket
      if action.reported then
        some (modify s ticket (fun a => { a with observed := true }))
      else none
  | .attest request ticket => do
      let action ← find s ticket
      if action.reported && action.observed &&
          decide (action.request = request ∧ request ∈ s.active) then
        some (modify s ticket (fun a => { a with success := true }))
      else none
  | .finish request ticket => do
      let action ← find s ticket
      if settled s && s.pending.isNone && action.success &&
          decide (action.request = request ∧ request ∈ s.active) then
        some { s with active := s.active.filter (fun r => r != request) }
      else none
  | .cancel request =>
      if request ∈ s.active then
        some { s with active := s.active.filter (fun r => r != request) }
      else none
  | .neutral => some s

def replay : State → List Event → Option State
  | s, [] => some s
  | s, e :: es => (step s e).bind (fun next => replay next es)

def firstFailure : State → List Event → Nat → Option Nat
  | _, [], _ => none
  | s, e :: es, index => match step s e with
      | none => some index
      | some next => firstFailure next es (index + 1)

inductive Valid : State → List Event → State → Prop
  | nil (s : State) : Valid s [] s
  | cons {s next final : State} {event : Event} {events : List Event}
      (head : step s event = some next) (tail : Valid next events final) :
      Valid s (event :: events) final

/-- An accepted trace has an admitted transition at every recorded step. -/
theorem replay_iff_valid (s : State) (events : List Event) (final : State) :
    replay s events = some final ↔ Valid s events final := by
  induction events generalizing s with
  | nil =>
      constructor
      · intro h
        simp only [replay, Option.some.injEq] at h
        subst final
        exact .nil s
      · intro h
        cases h
        rfl
  | cons event events ih =>
      constructor
      · intro h
        cases hs : step s event with
        | none => simp [replay, hs] at h
        | some next =>
            exact .cons hs ((ih next).mp (by simpa [replay, hs] using h))
      · intro h
        cases h with
        | cons head tail => simpa [replay, head] using (ih _).mpr tail

theorem replay_append (s : State) (xs ys : List Event) :
    replay s (xs ++ ys) = (replay s xs).bind (fun next => replay next ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons event events ih =>
      cases hs : step s event <;> simp [replay, hs, ih]

/-- If the whole trace passes, every earlier prefix passes too. -/
theorem accepted_prefix (s final : State) (xs ys : List Event)
    (h : replay s (xs ++ ys) = some final) :
    ∃ middle, replay s xs = some middle := by
  rw [replay_append] at h
  cases hx : replay s xs with
  | none => simp [hx] at h
  | some middle => exact ⟨middle, rfl⟩

theorem restore_preserves_work_and_actions (s : State) :
    step s .restore = some { s with revision := s.revision + 1, pending := none } := rfl

theorem control_preserves_work_and_actions (s : State) (mode : Nat) (paused : Bool) :
    step s (.control mode paused) =
      some { s with revision := s.revision + 1, mode := mode, paused := paused } := rfl

private def active : State :=
  { revision := 1, accepted := [7], active := [7] }
private def snap : Capture := ⟨0, 7, 1, 0, [10], [10]⟩
private def sampled : State := { active with nextSerial := 1, pending := some snap }
private def issued : State :=
  { active with nextSerial := 1, actions := [{ ticket := 5, request := 7 }] }

theorem stale_decision_is_rejected :
    step { sampled with revision := 2 } (.command 0 5 7 10) = none := by decide
theorem advertised_only_tool_is_rejected :
    step sampled (.command 0 5 7 99) = none := by decide
theorem capture_before_feedback_is_rejected :
    step issued (.capture { snap with serial := 1 }) = none := by decide
theorem observation_before_result_is_rejected :
    step issued (.observe 5) = none := by decide
theorem result_without_reservation_is_rejected :
    step issued (.commandResult 5 0) = none := by decide
theorem duplicate_reservation_is_rejected :
    replay issued [.reserve 5 0, .reserve 5 0] = none := by decide
theorem duplicate_result_is_rejected :
    replay issued [.reserve 5 0, .commandResult 5 0, .commandResult 5 0] = none := by decide
theorem unchecked_completion_is_rejected :
    replay issued [.report 5 false, .observe 5, .finish 7 5] = none := by decide
theorem late_result_after_restore_is_retained :
    (replay issued [.restore, .report 5 false, .observe 5]).isSome = true := by decide
theorem checked_completion_is_admitted :
    (replay issued [.report 5 false, .observe 5, .attest 7 5, .finish 7 5]).isSome = true := by decide

end StrategyTraceAudit
