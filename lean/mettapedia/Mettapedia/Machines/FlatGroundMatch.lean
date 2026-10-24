import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Eliminating the traversal stack for flat ground patterns

The reference machine decomposes constructors into a work stack. The direct
machine checks the same constructor and then visits its leaf fields in order.
Leaf actions are arbitrary stateful operations: a repeated-slot comparison,
binding through a cell alias, failure, refusal, or a native error can stop either
machine with its current state. No commutation or purity of leaf actions is
assumed. Both machines retain precisely the same partial state on failure;
their caller can therefore apply the same rollback and fallback handlers.

The native adapter admits only ground algebraic views and keeps logical-list
patterns on its existing path. Compiler metadata, native groundness, matching
primitives and memory conformance remain implementation obligations. This is
a traversal refinement, not a proof of overall runtime optimality.

The compiler comparison outside Prolog is specialization of pattern matching
in ML: https://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf
-/

set_option autoImplicit false
namespace Mettapedia.Machines.FlatGroundMatch

inductive Value where
  | atom (value : Nat)
  | node (tag : Nat) (fields : List Value)
  deriving Repr

inductive Pattern (Leaf : Type) where
  | leaf (operation : Leaf)
  | node (tag : Nat) (fields : List (Pattern Leaf))

inductive Outcome (State : Type) where
  | ok (state : State)
  | failed (state : State)
  | declined (state : State)
  | error (state : State)
  | exhausted (state : State)
  deriving DecidableEq, Repr

variable {Leaf State Result : Type}

def reference (leaf : Leaf → Value → State → Outcome State) :
    Nat → List (Pattern Leaf × Value) → State → Outcome State
  | _, [], state => .ok state
  | 0, _ :: _, state => .exhausted state
  | fuel + 1, (pattern, value) :: rest, state =>
      match pattern with
      | .leaf operation =>
          match leaf operation value state with
          | .ok next => reference leaf fuel rest next
          | .failed next => .failed next
          | .declined next => .declined next
          | .error next => .error next
          | .exhausted next => .exhausted next
      | .node tag patterns =>
          match value with
          | .atom _ => .failed state
          | .node actual fields =>
              if tag = actual ∧ patterns.length = fields.length then
                reference leaf fuel (List.zip patterns fields ++ rest) state
              else .failed state

def fields (leaf : Leaf → Value → State → Outcome State) :
    List Leaf → List Value → State → Outcome State
  | [], [], state => .ok state
  | operation :: rest, value :: values, state =>
      match leaf operation value state with
      | .ok next => fields leaf rest values next
      | .failed next => .failed next
      | .declined next => .declined next
      | .error next => .error next
      | .exhausted next => .exhausted next
  | _, _, state => .failed state

def direct (leaf : Leaf → Value → State → Outcome State)
    (tag : Nat) (operations : List Leaf) (value : Value) (state : State) : Outcome State :=
  match value with
  | .atom _ => .failed state
  | .node actual values =>
      if tag = actual ∧ operations.length = values.length then
        fields leaf operations values state
      else .failed state

theorem leaf_stack_exact (leaf : Leaf → Value → State → Outcome State)
    (operations : List Leaf) (values : List Value) (state : State)
    (sameLength : operations.length = values.length) :
    reference leaf operations.length
      (List.zip (operations.map Pattern.leaf) values) state =
        fields leaf operations values state := by
  induction operations generalizing values state with
  | nil =>
      cases values with
      | nil => rfl
      | cons _ _ => simp at sameLength
  | cons operation rest ih =>
      cases values with
      | nil => simp at sameLength
      | cons value values =>
          have tailLength : rest.length = values.length := by simpa using sameLength
          simp only [List.length_cons, List.map_cons, List.zip_cons_cons, reference, fields]
          cases leaf operation value state <;> simp [ih values _ tailLength]

theorem flat_exact (leaf : Leaf → Value → State → Outcome State)
    (tag : Nat) (operations : List Leaf) (value : Value) (state : State) :
    reference leaf (operations.length + 1)
      [(Pattern.node tag (operations.map Pattern.leaf), value)] state =
        direct leaf tag operations value state := by
  cases value with
  | atom _ => rfl
  | node actual values =>
      simp only [reference, List.length_map, List.append_nil, direct]
      split
      · rename_i admitted
        exact leaf_stack_exact leaf operations values state admitted.2
      · rfl

theorem atomic_exact (leaf : Leaf → Value → State → Outcome State)
    (operation : Leaf) (value : Value) (state : State) :
    reference leaf 1 [(Pattern.leaf operation, value)] state = leaf operation value state := by
  cases step : leaf operation value state <;> simp [reference, step]

/-- Error handling, rollback and saved continuations can observe the complete
result, including the partial state at the point matching stopped. -/
theorem handled_flat_exact (leaf : Leaf → Value → State → Outcome State)
    (tag : Nat) (operations : List Leaf) (value : Value) (state : State)
    (handle : Outcome State → Result) :
    handle (reference leaf (operations.length + 1)
      [(Pattern.node tag (operations.map Pattern.leaf), value)] state) =
        handle (direct leaf tag operations value state) := by
  rw [flat_exact]

def lookupScalar (slot : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (other, value) :: rest => if slot = other then some value else lookupScalar slot rest

def bindScalar (slot : Nat) (value : Value) (state : List (Nat × Nat)) :
    Outcome (List (Nat × Nat)) :=
  match value with
  | .node _ _ => .declined state
  | .atom scalar =>
      match lookupScalar slot state with
      | none => .ok ((slot, scalar) :: state)
      | some previous => if previous = scalar then .ok state else .failed state

example : direct bindScalar 3 [0, 0] (.node 3 [.atom 7, .atom 7]) [] =
    .ok [(0, 7)] := by decide

/-- Repeated slots retain their equality constraint and the exact failed prefix. -/
example : direct bindScalar 3 [0, 0] (.node 3 [.atom 7, .atom 8]) [] =
    .failed [(0, 7)] := by decide

example : direct bindScalar 3 [0] (.node 4 [.atom 7]) [] = .failed [] := by decide

example : direct bindScalar 3 [0] (.node 3 []) [] = .failed [] := by decide

/-- A refused leaf does not execute the following leaf. -/
example : direct (fun operation _ history =>
    if operation = 1 then .declined (operation :: history)
    else .ok (operation :: history)) 3 [0, 1, 2]
      (.node 3 [.atom 7, .atom 8, .atom 9]) [] = .declined [1, 0] := by decide

end Mettapedia.Machines.FlatGroundMatch
