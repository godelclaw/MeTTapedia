import Mettapedia.Machines.NativeCallReturn

/-!
# Terminal native entry through an existing caller

The source has ordinary value computations, local binding, branching and native
entry. Pure lowering rejects every native occurrence. Terminal lowering admits
native work only after pure operands, pure binding producers and pure conditions.
The target returns the original native packet to its caller without interpreting
its payload or rebuilding an entrance expression. Pure prefixes and local binding
are evaluated on both sides.

The refinements below cover that stage boundary, including native failure and
frontiers. They do not model source fuel, physical allocation, named callee
admission, C pointers or the dialect's subsequent completion of the packet.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NativeTailReturn

abbrev Env := Nat → Nat
abbrev Packet := NativeCallReturn.Source Nat Nat Nat
abbrev Native := Nat → Nat → Packet

def push (value : Nat) (env : Env) : Env
  | 0 => value
  | n + 1 => env n

inductive Term where
  | value (n : Nat)
  | slot (index : Nat)
  | add (left right : Term)
  | bind (producer body : Term)
  | branch (condition yes no : Term)
  | native (name : Nat) (operand : Term)
  deriving DecidableEq, Repr

inductive Pure where
  | value (n : Nat)
  | slot (index : Nat)
  | add (left right : Pure)
  | bind (producer body : Pure)
  | branch (condition yes no : Pure)
  deriving DecidableEq, Repr

def Pure.eval : Pure → Env → Nat
  | .value n, _ => n
  | .slot index, env => env index
  | .add left right, env => left.eval env + right.eval env
  | .bind producer body, env => body.eval (push (producer.eval env) env)
  | .branch condition yes no, env =>
      if condition.eval env = 0 then no.eval env else yes.eval env

structure Observation where
  entries : List Nat
  packet : Packet
  deriving DecidableEq, Repr

def value (n : Nat) : Observation := ⟨[], .one (.value .completed n)⟩

def sequence (first : Observation) (body : Nat → Observation) : Observation :=
  match first.packet with
  | .one (.value .completed n) =>
      let next := body n
      ⟨first.entries ++ next.entries, next.packet⟩
  | _ => first

def source (native : Native) : Term → Env → Observation
  | .value n, _ => value n
  | .slot index, env => value (env index)
  | .add left right, env =>
      sequence (source native left env) fun a =>
        sequence (source native right env) fun b => value (a + b)
  | .bind producer body, env =>
      sequence (source native producer env) fun n => source native body (push n env)
  | .branch condition yes no, env =>
      sequence (source native condition env) fun n =>
        if n = 0 then source native no env else source native yes env
  | .native name operand, env =>
      sequence (source native operand env) fun n => ⟨[name], native name n⟩

def lowerPure : Term → Option Pure
  | .value n => some (.value n)
  | .slot index => some (.slot index)
  | .add left right => return .add (← lowerPure left) (← lowerPure right)
  | .bind producer body => return .bind (← lowerPure producer) (← lowerPure body)
  | .branch condition yes no =>
      return .branch (← lowerPure condition) (← lowerPure yes) (← lowerPure no)
  | .native _ _ => none

inductive Code where
  | returned (computation : Pure)
  | entered (name : Nat) (operand : Pure)
  | bind (producer : Pure) (body : Code)
  | branch (condition : Pure) (yes no : Code)
  deriving DecidableEq, Repr

def lower : Term → Option Code
  | .value n => some (.returned (.value n))
  | .slot index => some (.returned (.slot index))
  | .add left right => return .returned (.add (← lowerPure left) (← lowerPure right))
  | .bind producer body => return .bind (← lowerPure producer) (← lower body)
  | .branch condition yes no =>
      return .branch (← lowerPure condition) (← lower yes) (← lower no)
  | .native name operand => return .entered name (← lowerPure operand)

def run (native : Native) : Code → Env → Observation
  | .returned computation, env => value (computation.eval env)
  | .entered name operand, env => ⟨[name], native name (operand.eval env)⟩
  | .bind producer body, env => run native body (push (producer.eval env) env)
  | .branch condition yes no, env =>
      if condition.eval env = 0 then run native no env else run native yes env

theorem pure_refines (native : Native) (term : Term) (code : Pure)
    (compiled : lowerPure term = some code) (env : Env) :
    source native term env = value (code.eval env) := by
  induction term generalizing code env with
  | value n => cases compiled; rfl
  | slot index => cases compiled; rfl
  | native name operand ih => simp [lowerPure] at compiled
  | add left right leftIH rightIH =>
      cases a : lowerPure left <;> cases b : lowerPure right <;>
        simp [lowerPure, a, b] at compiled
      subst code
      simp [source, leftIH _ a, rightIH _ b, Pure.eval, sequence, value]
  | bind producer body producerIH bodyIH =>
      cases a : lowerPure producer <;> cases b : lowerPure body <;>
        simp [lowerPure, a, b] at compiled
      subst code
      simp [source, producerIH _ a, bodyIH _ b, Pure.eval, sequence, value]
  | branch condition yes no conditionIH yesIH noIH =>
      cases a : lowerPure condition <;> cases b : lowerPure yes <;>
        cases c : lowerPure no <;> simp [lowerPure, a, b, c] at compiled
      subst code
      simp only [source, conditionIH _ a, sequence, value]
      split <;> simp_all [Pure.eval, value]

theorem lowering_refines (native : Native) (term : Term) (code : Code)
    (compiled : lower term = some code) (env : Env) :
    source native term env = run native code env := by
  induction term generalizing code env with
  | value n => cases compiled; rfl
  | slot index => cases compiled; rfl
  | add left right leftIH rightIH =>
      cases a : lowerPure left <;> cases b : lowerPure right <;>
        simp [lower, a, b] at compiled
      subst code
      simp [source, pure_refines native left _ a, pure_refines native right _ b,
        run, Pure.eval, sequence, value]
  | bind producer body producerIH bodyIH =>
      cases a : lowerPure producer <;> cases b : lower body <;>
        simp [lower, a, b] at compiled
      subst code
      simp [source, pure_refines native producer _ a, bodyIH _ b, run, sequence, value]
  | branch condition yes no conditionIH yesIH noIH =>
      cases a : lowerPure condition <;> cases b : lower yes <;>
        cases c : lower no <;> simp [lower, a, b, c] at compiled
      subst code
      simp only [source, pure_refines native condition _ a, sequence, value, run]
      split <;> simp_all
  | native name operand operandIH =>
      cases a : lowerPure operand <;> simp [lower, a] at compiled
      subst code
      simp [source, pure_refines native operand _ a, run, sequence, value]

theorem native_entry_bound (native : Native) (code : Code) (env : Env) :
    (run native code env).entries.length ≤ 1 := by
  induction code generalizing env with
  | returned computation => simp [run, value]
  | entered name operand => simp [run]
  | bind producer body ih => exact ih _
  | branch condition yes no yesIH noIH =>
      simp only [run]
      split <;> simp_all

theorem admitted_source_entry_bound (native : Native) (term : Term) (code : Code)
    (compiled : lower term = some code) (env : Env) :
    (source native term env).entries.length ≤ 1 := by
  rw [lowering_refines native term code compiled env]
  exact native_entry_bound native code env

theorem tail_keeps_packet (native : Native) (name : Nat) (operand : Pure) (env : Env) :
    (run native (.entered name operand) env).packet = native name (operand.eval env) := by
  rfl

theorem tail_failure_enters_once (name : Nat) (operand : Pure) (env : Env) :
    run (fun _ _ => .failure) (.entered name operand) env = ⟨[name], .failure⟩ := by
  rfl

namespace Controls

theorem native_in_operand_refused :
    lower (.native 1 (.native 2 (.value 7))) = none := by decide +kernel

theorem native_in_binding_producer_refused :
    lower (.bind (.native 1 (.value 7)) (.add (.slot 0) (.value 1))) = none := by
  decide +kernel

theorem native_in_condition_refused :
    lower (.branch (.native 1 (.value 7)) (.value 1) (.value 2)) = none := by
  decide +kernel

theorem pure_prefix_and_terminal_native_admitted :
    lower (.bind (.add (.value 1) (.value 2)) (.native 7 (.slot 0))) =
      some (.bind (.add (.value 1) (.value 2)) (.entered 7 (.slot 0))) := by
  decide +kernel

theorem native_frontier_keeps_duplicates :
    (run (fun _ _ => .frontier .completed #[7, 7, 9])
      (.entered 1 (.value 0)) (fun _ => 0)).packet = .frontier .completed #[7, 7, 9] := by
  rfl

theorem false_branch_does_not_enter :
    run (fun _ _ => .failure)
      (.branch (.value 0) (.entered 1 (.value 7)) (.returned (.value 9)))
      (fun _ => 0) = value 9 := by
  decide +kernel

end Controls
end Mettapedia.Machines.NativeTailReturn
