import Mettapedia.Machines.ConstraintPropagation.ResidualChecks

/-!
# Conditional continuation execution under retained branch state

A recursive reference checks pending obligations before each binding, effect
and return. The target installs them in a separate checking phase and executes
one instruction per admitted transition. Refutation keeps committed effects;
unready obligations leave with the value. Suspension retains the actual state.
This finite linear-body law does not certify foreign solver correctness, C
pointer transport, arbitrary branching, or authored source-fuel correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConditionalContinuation

open ConstraintPropagation.ResidualChecks (discharge)

variable {Context Value Check Effect : Type}

inductive Instruction (Context Effect : Type) where
  | bind (update : Context → Context)
  | emit (effect : Effect)
  | fail

structure Answer (Context Value Check : Type) where
  context : Context
  value : Value
  pending : List Check

structure Observation (Context Value Check Effect : Type) where
  answer : Option (Answer Context Value Check)
  trace : List Effect

def prepend (past : List Effect) (out : Observation Context Value Check Effect) :=
  {out with trace := past ++ out.trace}

/-- The source checks the current obligations directly, before running work. -/
def reference (probe : Context → Check → Option Bool) (read : Value → Context → Value)
    (packet : Value) : List (Instruction Context Effect) → Context → List Check →
      Observation Context Value Check Effect
  | [], context, pending =>
    match discharge (probe context) pending with
    | none => ⟨none, []⟩
    | some residual => ⟨some ⟨context, read packet context, residual⟩, []⟩
  | instruction :: rest, context, pending =>
    match discharge (probe context) pending with
    | none => ⟨none, []⟩
    | some residual =>
      match instruction with
      | .bind update => reference probe read packet rest (update context) residual
      | .emit effect => prepend [effect] (reference probe read packet rest context residual)
      | .fail => ⟨none, []⟩

inductive Phase where
  | check | execute | returned | failed
  deriving DecidableEq

structure State (Context Value Check Effect : Type) where
  packet : Value
  context : Context
  pending : List Check
  code : List (Instruction Context Effect)
  trace : List Effect := []
  phase : Phase := .check

def step (probe : Context → Check → Option Bool)
    (state : State Context Value Check Effect) : State Context Value Check Effect :=
  match state.phase with
  | .returned | .failed => state
  | .check =>
      match discharge (probe state.context) state.pending with
      | none => {state with phase := .failed}
      | some pending => {state with pending := pending, phase := .execute}
  | .execute =>
      match state.code with
      | [] => {state with phase := .returned}
      | .bind update :: rest =>
          {state with context := update state.context, code := rest, phase := .check}
      | .emit effect :: rest =>
          {state with trace := state.trace ++ [effect], code := rest, phase := .check}
      | .fail :: _ => {state with phase := .failed}

def advance (probe : Context → Check → Option Bool) : Nat →
    State Context Value Check Effect → State Context Value Check Effect
  | 0, state => state
  | n + 1, state => advance probe n (step probe state)

def observe (read : Value → Context → Value) (state : State Context Value Check Effect) :
    Observation Context Value Check Effect :=
  ⟨if state.phase == .returned then
      some ⟨state.context, read state.packet state.context, state.pending⟩ else none,
    state.trace⟩

def finished (state : State Context Value Check Effect) : Prop :=
  state.phase = .returned ∨ state.phase = .failed

theorem finished_stable (probe : Context → Check → Option Bool)
    (state : State Context Value Check Effect) (done : finished state) (n : Nat) :
    advance probe n state = state := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases done with h | h <;> simpa [advance, step, h] using ih

theorem advance_add (probe : Context → Check → Option Bool) (first extra : Nat)
    (state : State Context Value Check Effect) :
    advance probe (first + extra) state = advance probe extra (advance probe first state) := by
  induction first generalizing state with
  | zero => simp [advance]
  | succ n ih => simpa [Nat.succ_add, advance] using ih (step probe state)

theorem packet_retained (probe : Context → Check → Option Bool)
    (state : State Context Value Check Effect) (n : Nat) :
    (advance probe n state).packet = state.packet := by
  have one : ∀ s : State Context Value Check Effect, (step probe s).packet = s.packet := by
    intro s
    cases hp : s.phase <;> simp only [step, hp]
    · split <;> rfl
    · cases s.code with
      | nil => rfl
      | cons instruction rest => cases instruction <;> rfl
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simpa only [advance, ih] using one state

/-- The target's two-phase worklist implements the independent recursive
reference, including a retained conditional result and failed effect prefixes. -/
private theorem advance_two (probe : Context → Check → Option Bool) (n : Nat)
    (state : State Context Value Check Effect) :
    advance probe (n + 2) state = advance probe n (step probe (step probe state)) := rfl

theorem execution_refines (probe : Context → Check → Option Bool)
    (read : Value → Context → Value) (packet : Value)
    (code : List (Instruction Context Effect)) (context : Context)
    (pending : List Check) (past : List Effect) :
    let endState := advance probe (2 * (code.length + 1))
      ⟨packet, context, pending, code, past, .check⟩
    finished endState ∧ observe read endState =
      prepend past (reference probe read packet code context pending) := by
  induction code generalizing context pending past with
  | nil =>
      cases h : discharge (probe context) pending <;>
        simp [advance, step, h, finished, observe, reference, prepend]
  | cons instruction rest ih =>
      have fuel : 2 * ((instruction :: rest).length + 1) =
          2 * (rest.length + 1) + 2 := by simp; omega
      dsimp only
      rw [fuel, advance_two]
      cases h : discharge (probe context) pending with
      | none =>
          simp only [step, h]
          rw [finished_stable probe _ (Or.inr rfl)]
          simp [finished, observe, reference, h, prepend]
      | some residual =>
          cases instruction with
          | bind update =>
              simpa only [step, h, reference] using ih (update context) residual past
          | emit effect =>
              simpa only [step, h, reference, prepend, List.append_assoc]
                using ih context residual (past ++ [effect])
          | fail =>
              simp only [step, h]
              rw [finished_stable probe _ (Or.inr rfl)]
              simp [finished, observe, reference, h, prepend]

/-- Refusing physical admission changes neither the branch nor its work. -/
def permitted (probe : Context → Check → Option Bool) (allow : Bool)
    (state : State Context Value Check Effect) := if allow then step probe state else state

theorem refusal_keeps_state (probe : Context → Check → Option Bool)
    (state : State Context Value Check Effect) : permitted probe false state = state := rfl

namespace Frontier

/-- Root entry is binary in a valid cursor; an opaque frame cannot be
certified as retired by an ordinary equation-position check. -/
inductive Frame where
  | root (entered : Bool)
  | equation (matched : Bool) (next count : Nat)
  | opaque
  deriving DecidableEq

def sourceWork : Frame → List Unit
  | .root true => []
  | .root false => [()]
  | .equation true next count => List.replicate (count - next) ()
  | .equation false _ _ => [()]
  | .opaque => [()]

def retired : Frame → Bool
  | .root entered => entered
  | .equation matched next count => matched && decide (count ≤ next)
  | .opaque => false

def owns (frames : List Frame) : Bool := frames.all retired

theorem frame_retired_iff (frame : Frame) : retired frame = true ↔ sourceWork frame = [] := by
  cases frame with
  | root entered => cases entered <;> simp [retired, sourceWork]
  | equation matched next count => cases matched <;> simp [retired, sourceWork, Nat.sub_eq_zero_iff_le]
  | «opaque» => simp [retired, sourceWork]

/-- The cursor's concrete position guard excludes every pending compiled
lookup before authority transfers to an already-entered native owner. -/
theorem owns_iff_no_compiled_work (frames : List Frame) :
    owns frames = true ↔ frames.flatMap sourceWork = [] := by
  simp [owns, List.all_eq_true, List.flatMap_eq_nil_iff, frame_retired_iff]

end Frontier

namespace Controls

def probe (context : Option Nat) (forbidden : Nat) : Option Bool :=
  context.map fun value => decide (value ≠ forbidden)

def read (packet : String) (_ : Option Nat) := packet

def body : List (Instruction (Option Nat) Nat) :=
  [.emit 7, .bind (fun _ => some 2), .emit 9]

def start : State (Option Nat) String Nat Nat :=
  ⟨"(readln!)", none, [1], body, [], .check⟩

theorem unready_obligation_leaves_with_data :
    (observe read (advance probe 2 (⟨"(readln!)", none, [1], [], [], .check⟩ : State (Option Nat) String Nat Nat))).answer =
      some ⟨none, "(readln!)", [1]⟩ := rfl

theorem failed_binding_blocks_later_effect :
    reference probe read "value" [.bind (fun _ => some 1), .emit 99] none [1] =
      ⟨none, []⟩ := rfl

theorem failure_keeps_committed_effect :
    reference probe read "value" [.emit 7, .bind (fun _ => some 1), .emit 99] none [1] =
      ⟨none, [7]⟩ := rfl

theorem dropping_obligation_changes_answer :
    (reference probe read "value" [.bind (fun _ => some 1), .emit 99] none []).trace = [99] ∧
    (reference probe read "value" [.bind (fun _ => some 1), .emit 99] none [1]).trace = [] := by
  constructor <;> rfl

theorem paused_branch_keeps_real_state :
    advance probe 2 start = ⟨"(readln!)", none, [1], body.tail, [7], .check⟩ := rfl

theorem split_continuation_has_one_effect_prefix :
    (advance probe 6 (advance probe 2 start)).trace = [7, 9] := rfl

theorem restarting_entrance_replays_effect :
    (advance probe 2 start).trace ++ (advance probe 8 start).trace = [7, 7, 9] := rfl

theorem pending_equation_blocks_frontier_transfer :
    Frontier.owns [.root true, .equation true 1 2] = false := rfl

theorem retired_equation_allows_native_owner :
    Frontier.owns [.root true, .equation true 2 2] = true := rfl

end Controls

end Mettapedia.Machines.ConditionalContinuation
