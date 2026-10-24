import Mathlib.Init
import Mathlib.Tactic

/-!+# Operand plans for contextual execution control

An admitted source head elaborates into a control operation and operand
coordinates. The array reader is independent of the source interpreter below,
which destructures an ordered list. Their agreement preserves the opaque
operands themselves: elaboration neither evaluates a producer nor inspects a
pattern or continuation. In particular, a missing branch is not an Empty datum.

These are source-layout laws, not an execution strategy or a native C refinement.
Dialect admission, live lexical environments, effects, semantic fuel and physical
owners remain separate obligations. An ordinary force and a function return
scope are different operations even if one admitted lowering executes both
through the same direct body entry. Memoized Need is not introduced here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ExecutionControl

inductive Head where
  | letBinding
  | chain
  | branch
  | bindings
  | evaluate
  | function
  deriving DecidableEq, Repr

inductive Operation where
  | sequence
  | branch
  | sequenceMany
  | force
  | returnScope
  deriving DecidableEq, Repr

structure Plan where
  operation : Operation
  source : Nat
  first : Option Nat
  last : Option Nat
  deriving DecidableEq, Repr

/-- Arity is checked before any operand is read. Coordinates exclude the head. -/
def elaborate (head : Head) (arity : Nat) : Option Plan :=
  match head, arity with
  | .letBinding, 3 => some ⟨.sequence, 1, some 0, some 2⟩
  | .chain, 3 => some ⟨.sequence, 0, some 1, some 2⟩
  | .branch, 2 => some ⟨.branch, 0, some 1, none⟩
  | .branch, 3 => some ⟨.branch, 0, some 1, some 2⟩
  | .bindings, 2 => some ⟨.sequenceMany, 0, none, some 1⟩
  | .evaluate, 1 => some ⟨.force, 0, none, none⟩
  | .function, 1 => some ⟨.returnScope, 0, none, none⟩
  | _, _ => none

def Plan.InBounds (plan : Plan) (arity : Nat) : Prop :=
  plan.source < arity ∧
    (∀ index, plan.first = some index → index < arity) ∧
    (∀ index, plan.last = some index → index < arity)

/-- Admission establishes every coordinate the reader may subsequently use. -/
theorem elaborate_inBounds {head : Head} {arity : Nat} {plan : Plan}
    (admitted : elaborate head arity = some plan) : plan.InBounds arity := by
  cases head <;>
    (rcases arity with _ | (_ | (_ | (_ | arity))) <;>
      simp_all [elaborate])
  all_goals subst plan; simp [Plan.InBounds]

inductive Request (Operand : Type*) where
  | sequence (producer pattern body : Operand)
  | branch (condition yes : Operand) (no : Option Operand)
  | sequenceMany (bindings body : Operand)
  | force (source : Operand)
  | returnScope (body : Operand)
  deriving DecidableEq, Repr

variable {Operand : Type*}

private def required (fields : Array Operand) (position : Option Nat) : Option Operand :=
  position.bind (fields[·]?)

/-- The lowered reader observes a fixed number of array coordinates. It has no
operation for evaluating, copying or comparing an operand. -/
def read (plan : Plan) (fields : Array Operand) : Option (Request Operand) := do
  let source ← fields[plan.source]?
  match plan.operation with
  | .sequence =>
      let pattern ← required fields plan.first
      let body ← required fields plan.last
      return .sequence source pattern body
  | .branch =>
      let yes ← required fields plan.first
      match plan.last with
      | none => return .branch source yes none
      | some position =>
          let no ← fields[position]?
          return .branch source yes (some no)
  | .sequenceMany =>
      let body ← required fields plan.last
      return .sequenceMany source body
  | .force => return .force source
  | .returnScope => return .returnScope source

/-- Independent source destructuring, before an execution strategy consumes
the request. This explicitly distinguishes the two binding operand orders. -/
def reference (head : Head) (fields : List Operand) : Option (Request Operand) :=
  match head, fields with
  | .letBinding, [pattern, producer, body] => some (.sequence producer pattern body)
  | .chain, [producer, pattern, body] => some (.sequence producer pattern body)
  | .branch, [condition, yes] => some (.branch condition yes none)
  | .branch, [condition, yes, no] => some (.branch condition yes (some no))
  | .bindings, [bindings, body] => some (.sequenceMany bindings body)
  | .evaluate, [source] => some (.force source)
  | .function, [body] => some (.returnScope body)
  | _, _ => none

/-- Reading an elaborated operand plan agrees with independent source layout,
including under/over-application and the missing-branch distinction. -/
theorem read_elaborate (head : Head) (fields : List Operand) :
    (elaborate head fields.length).bind (fun plan => read plan fields.toArray) =
      reference head fields := by
  cases fields with
  | nil => cases head <;> rfl
  | cons a fields =>
      cases fields with
      | nil => cases head <;> rfl
      | cons b fields =>
          cases fields with
          | nil => cases head <;> rfl
          | cons c fields =>
              cases fields with
              | nil => cases head <;> rfl
              | cons d rest => cases head <;> rfl

/-- The core sequence is shared, while the source layouts are not confused. -/
theorem binding_layouts_agree (pattern producer body : Operand) :
    (elaborate .letBinding 3).bind (fun plan => read plan #[pattern, producer, body]) =
      (elaborate .chain 3).bind (fun plan => read plan #[producer, pattern, body]) := by
  change (elaborate .letBinding [pattern, producer, body].length).bind
      (fun plan => read plan [pattern, producer, body].toArray) =
    (elaborate .chain [producer, pattern, body].length).bind
      (fun plan => read plan [producer, pattern, body].toArray)
  rw [read_elaborate, read_elaborate]
  rfl

theorem force_is_not_return_scope (source : Operand) :
    reference .evaluate [source] ≠ reference .function [source] := by
  simp [reference]

example : reference .letBinding [7, 7, 9] = some (.sequence 7 7 9) := rfl
example : (elaborate .letBinding 2 : Option Plan) = none := rfl
example : reference .branch [1, 2] ≠ reference .branch [1, 2, 0] := by decide

end Mettapedia.Machines.ExecutionControl

#print axioms Mettapedia.Machines.ExecutionControl.read_elaborate
#print axioms Mettapedia.Machines.ExecutionControl.elaborate_inBounds
#print axioms Mettapedia.Machines.ExecutionControl.binding_layouts_agree
#print axioms Mettapedia.Machines.ExecutionControl.force_is_not_return_scope
