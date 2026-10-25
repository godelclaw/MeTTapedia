import Mathlib.Data.List.Basic

/-!
# Typed primitive results and their native lowering

A primitive projects existing data or computes a truth. Native code returns a
uniform carrier, but its admitted instruction retains the result role. The
lowering preserves the operation's state transition and chooses representation
from that role. Inspecting the returned carrier alone cannot replace the role.

This is the result boundary of a primitive, before dialect-specific completion
and typing. Native pointer lifetimes and correspondence with C remain separate.
The prepared backend additionally requires effect-free admission before it can
discard an unsuccessful speculative attempt; these laws do not license replay.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PrimitiveResultRole

inductive Value (Atom : Type*) where
  | atom (value : Atom)
  | boolean (value : Bool)
  deriving DecidableEq

inductive Operation (World Input Atom : Type*) where
  | project (body : World → Input → World × Value Atom)
  | predicate (body : World → Input → World × Bool)

inductive ResultRole where
  | data
  | truth
  deriving DecidableEq

structure Plan (World Input Atom : Type*) where
  role : ResultRole
  body : World → Input → World × Value Atom

variable {World Input Atom : Type*}

def source (encode : Bool → Value Atom) (operation : Operation World Input Atom)
    (world : World) (input : Input) : World × Value Atom :=
  match operation with
  | .project body => body world input
  | .predicate body =>
      let returned := body world input
      (returned.1, encode returned.2)

def lower : Operation World Input Atom → Plan World Input Atom
  | .project body => ⟨.data, body⟩
  | .predicate body =>
      ⟨.truth, fun world input =>
        let returned := body world input
        (returned.1, .boolean returned.2)⟩

def target (encode : Bool → Value Atom) (plan : Plan World Input Atom)
    (world : World) (input : Input) : World × Option (Value Atom) :=
  let returned := plan.body world input
  let result := match plan.role, returned.2 with
    | .data, value => some value
    | .truth, .boolean truth => some (encode truth)
    | .truth, .atom _ => none
  (returned.1, result)

/-- The raw native body is evaluated once. Its result role, rather than a
Boolean-looking payload, determines representation conversion. -/
theorem lowering_refines (encode : Bool → Value Atom)
    (operation : Operation World Input Atom) (world : World) (input : Input) :
    target encode (lower operation) world input =
      let result := source encode operation world input
      (result.1, some result.2) := by
  cases operation <;> rfl

theorem projection_preserves (encode : Bool → Value Atom)
    (body : World → Input → World × Value Atom) (world : World) (input : Input) :
    target encode (lower (.project body)) world input =
      ((body world input).1, some (body world input).2) := rfl

theorem state_preserved (encode : Bool → Value Atom)
    (operation : Operation World Input Atom) (world : World) (input : Input) :
    (target encode (lower operation) world input).1 =
      (source encode operation world input).1 := by
  rw [lowering_refines]

/-- A corrupted truth-result instruction cannot silently publish arbitrary
data as a computed Boolean. Its body has run; this is not admission refusal. -/
theorem invalid_truth_result (encode : Bool → Value Atom)
    (body : World → Input → World × Atom) (world : World) (input : Input) :
    target encode ⟨.truth, fun world input =>
      let returned := body world input
      (returned.1, .atom returned.2)⟩ world input =
      ((body world input).1, none) := rfl

def recodeByShape (encode : Bool → Value Atom) : Value Atom → Value Atom
  | .boolean truth => encode truth
  | .atom value => .atom value

example :
    let encode : Bool → Value String := fun b => .atom (if b then "true" else "false")
    target encode (lower (.project fun (world : Nat) (_ : Unit) =>
        (world + 1, .boolean true))) 0 () = (1, some (.boolean true)) := rfl

example :
    let encode : Bool → Value String := fun b => .atom (if b then "true" else "false")
    recodeByShape encode (.boolean true) ≠ (.boolean true : Value String) := by
  decide

example :
    let encode : Bool → Value String := fun b => .atom (if b then "true" else "false")
    target encode (lower (.predicate fun (world : Nat) (_ : Unit) =>
        (world + 1, true))) 0 () = (1, some (.atom "true")) := rfl

namespace BooleanCodec

variable [DecidableEq Atom]

/-- A Boolean operand is observed through the program's declared images.
Collapsed images refuse admission rather than choosing an arbitrary truth. -/
def read (encode : Bool → Atom) (value : Atom) : Option Bool :=
  if encode false = encode true then none
  else if value = encode false then some false
  else if value = encode true then some true
  else none

theorem read_encode (encode : Bool → Atom)
    (distinct : encode false ≠ encode true) (value : Bool) :
    read encode (encode value) = some value := by
  cases value <;> simp [read, distinct, Ne.symm distinct]

def unary (encode : Bool → Atom) (operation : Bool → Bool) (value : Atom) : Option Atom :=
  (read encode value).map (fun truth => encode (operation truth))

def binary (encode : Bool → Atom) (operation : Bool → Bool → Bool)
    (left right : Atom) : Option Atom :=
  (read encode left).bind fun first =>
    (read encode right).map fun second => encode (operation first second)

/-- Decoding operands, computing with the shared Boolean operation and
re-encoding the result implements the same abstract unary truth function. -/
theorem unary_refines (encode : Bool → Atom)
    (distinct : encode false ≠ encode true) (operation : Bool → Bool) (value : Bool) :
    unary encode operation (encode value) = some (encode (operation value)) := by
  simp [unary, read_encode encode distinct]

theorem binary_refines (encode : Bool → Atom)
    (distinct : encode false ≠ encode true) (operation : Bool → Bool → Bool)
    (left right : Bool) :
    binary encode operation (encode left) (encode right) =
      some (encode (operation left right)) := by
  simp [binary, read_encode encode distinct]

theorem collapsed_refused (encode : Bool → Atom)
    (collapsed : encode false = encode true) (value : Atom) : read encode value = none := by
  simp [read, collapsed]

example : unary (fun b => if b then 17 else 29) (!·) 29 = some 17 := by decide
example : unary (fun _ => 17) (!·) 17 = none := by decide

end BooleanCodec

#print axioms lowering_refines
#print axioms projection_preserves
#print axioms state_preserved
#print axioms invalid_truth_result
#print axioms BooleanCodec.read_encode
#print axioms BooleanCodec.unary_refines
#print axioms BooleanCodec.binary_refines
#print axioms BooleanCodec.collapsed_refused

end Mettapedia.Machines.PrimitiveResultRole
