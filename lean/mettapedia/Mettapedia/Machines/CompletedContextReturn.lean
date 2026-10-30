import Mettapedia.Machines.NativeCallReturn

/-!
# Closed readback of completed contextual returns

The source recursively reads a value in its carried environment. The target
expands current bindings into a bounded postfix construction plan and executes
that plan on an explicit value stack. An unresolved read retains the original
packet and environment. Expression and conditional packets never enter this
value-only construction path.

This finite tree fragment establishes the staging law, including alias chains,
cycles bounded by inspection fuel and constructor multiplicity. It does not
model C graph ownership, every atom representation, constraint registration or
authored source fuel. The inspection bound here is an admission allowance.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CompletedContextReturn

inductive Value where
  | literal (n : Nat)
  | slot (key : Nat)
  | pair (left right : Value)
  deriving DecidableEq, Repr

inductive Closed where
  | literal (n : Nat)
  | pair (left right : Closed)
  deriving DecidableEq, Repr

abbrev Env := Nat → Option Value

def referenceRead : Nat → Env → Value → Option Closed
  | 0, _, _ => none
  | _ + 1, _, .literal value => some (.literal value)
  | n + 1, env, .slot key => (env key).bind (referenceRead n env)
  | n + 1, env, .pair left right => do
      let a ← referenceRead n env left
      let b ← referenceRead n env right
      pure (.pair a b)

inductive Instruction where
  | literal (n : Nat)
  | pair
  deriving DecidableEq, Repr

def lower : Nat → Env → Value → Option (List Instruction)
  | 0, _, _ => none
  | _ + 1, _, .literal value => some [.literal value]
  | n + 1, env, .slot key => (env key).bind (lower n env)
  | n + 1, env, .pair left right => do
      let a ← lower n env left
      let b ← lower n env right
      pure (a ++ b ++ [.pair])

def execute : List Instruction → List Closed → Option (List Closed)
  | [], stack => some stack
  | .literal value :: rest, stack => execute rest (.literal value :: stack)
  | .pair :: rest, right :: left :: stack => execute rest (.pair left right :: stack)
  | .pair :: _, _ => none

def encode : Closed → List Instruction
  | .literal value => [.literal value]
  | .pair left right => encode left ++ encode right ++ [.pair]

theorem execute_append (first later : List Instruction) (stack : List Closed) :
    execute (first ++ later) stack = (execute first stack).bind (execute later) := by
  induction first generalizing stack with
  | nil => rfl
  | cons instruction rest ih =>
      cases instruction with
      | literal value => simpa [execute] using ih (.literal value :: stack)
      | pair =>
          cases stack with
          | nil => rfl
          | cons right stack =>
              cases stack with
              | nil => rfl
              | cons left stack => simpa [execute] using ih (.pair left right :: stack)

theorem encode_executes (value : Closed) (stack : List Closed) :
    execute (encode value) stack = some (value :: stack) := by
  induction value generalizing stack with
  | literal value => rfl
  | pair left right leftIH rightIH =>
      simp [encode, execute_append, leftIH, rightIH, execute]

theorem lower_readback (budget : Nat) (env : Env) (value : Value) :
    lower budget env value = (referenceRead budget env value).map encode := by
  induction budget generalizing value with
  | zero => rfl
  | succ n ih =>
      cases value with
      | literal value => rfl
      | slot key =>
          cases h : env key <;> simp [lower, referenceRead, h, ih]
      | pair left right =>
          simp only [lower, referenceRead, ih]
          cases referenceRead n env left <;> cases referenceRead n env right <;>
            simp [encode]

abbrev Packet := NativeCallReturn.Packet Value Nat Nat

inductive Result where
  | ready (value : Closed)
  | held (environment : Env) (packet : Packet)

def reference (budget : Nat) (env : Env) (packet : Packet) : Result :=
  match packet with
  | .value .completed value =>
      match referenceRead budget env value with
      | some closed => .ready closed
      | none => .held env packet
  | _ => .held env packet

def target (budget : Nat) (env : Env) (packet : Packet) : Result :=
  match packet with
  | .value .completed value =>
      match (lower budget env value).bind (fun code => execute code []) with
      | some [closed] => .ready closed
      | _ => .held env packet
  | _ => .held env packet

theorem target_refines (budget : Nat) (env : Env) (packet : Packet) :
    target budget env packet = reference budget env packet := by
  cases packet with
  | value role value =>
      cases role with
      | expression => rfl
      | completed =>
          simp only [target, reference, lower_readback]
          cases referenceRead budget env value <;> simp [encode_executes]
  | raised fault => rfl
  | conditional value delayed => rfl

namespace Controls

def empty : Env := fun _ => none

def chain : Env
  | 0 => some (.slot 1)
  | 1 => some (.literal 7)
  | _ => none

theorem raw_slot_can_be_ready_in_context :
    target 4 chain (.value .completed (.slot 0)) = .ready (.literal 7) := rfl

theorem constructor_keeps_duplicate_positions :
    target 5 chain (.value .completed (.pair (.slot 0) (.slot 0))) =
      .ready (.pair (.literal 7) (.literal 7)) := rfl

theorem incomplete_read_preserves_packet_and_world :
    target 5 empty (.value .completed (.pair (.literal 1) (.slot 0))) =
      .held empty (.value .completed (.pair (.literal 1) (.slot 0))) := rfl

theorem readable_conditional_still_needs_its_obligation :
    target 5 chain (.conditional (.slot 0) 42) =
      .held chain (.conditional (.slot 0) 42) := rfl

theorem expression_role_cannot_be_erased :
    target 5 chain (.value .expression (.slot 0)) =
      .held chain (.value .expression (.slot 0)) := rfl

theorem insufficient_allowance_retains_the_original :
    target 1 chain (.value .completed (.slot 0)) =
      .held chain (.value .completed (.slot 0)) := rfl

end Controls
end Mettapedia.Machines.CompletedContextReturn
