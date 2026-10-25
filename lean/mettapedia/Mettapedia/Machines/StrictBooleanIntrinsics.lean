import Mettapedia.Machines.RegisterCode

/-!
# Strict Boolean intrinsic admission

The ready-value fragment has binary conjunction and disjunction. Both
operands must be available Boolean values; a false left conjunction or a
true left disjunction does not excuse a missing or ill-typed right operand.
The existing register lowering preserves this partial interpretation for
every scoped body, including refusal. This is an operation/lowering law,
not verification of native dispatch or of effectful language evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StrictBooleanIntrinsics

open RegisterCode

inductive Value where
  | boolean (value : Bool)
  | other (tag : Nat)
  deriving DecidableEq

inductive Operation where
  | conjunction
  | disjunction
  deriving DecidableEq

/-- Ready-value dispatch rejects non-Boolean operands and incorrect arity. -/
def dispatch : Operation → List Value → Option Value
  | .conjunction, [.boolean left, .boolean right] => some (.boolean (left && right))
  | .disjunction, [.boolean left, .boolean right] => some (.boolean (left || right))
  | _, _ => none

def truth : Value → Option Bool
  | .boolean value => some value
  | .other _ => none

/-- This fragment has ordinary local let bindings and no equation calls. -/
def semantics : Sem Value Value Operation Nat Empty where
  patReads _ := []
  patSlots slot := [slot]
  lit := id
  op := dispatch
  truth := truth
  bindLet slot value registers := some (Function.update registers slot (some value))
  bindLet_frame := by
    intro slot value registers next same query outside
    cases same
    exact Function.update_of_ne (by simpa using outside) _ _
  bindLet_local := by
    intro slot value left right _
    refine Option.Rel.some fun query inside => ?_
    simp only [List.mem_singleton] at inside
    subst inside
    simp
  enter head := nomatch head

def noCalls : Empty → List Value → Option Value := fun head => nomatch head

theorem conjunction_truth_table (left right : Bool) :
    dispatch .conjunction [.boolean left, .boolean right] =
      some (.boolean (left && right)) := by
  cases left <;> cases right <;> rfl

theorem disjunction_truth_table (left right : Bool) :
    dispatch .disjunction [.boolean left, .boolean right] =
      some (.boolean (left || right)) := by
  cases left <;> cases right <;> rfl

theorem non_boolean_right (operation : Operation) (left : Bool) (tag : Nat) :
    dispatch operation [.boolean left, .other tag] = none := by
  cases operation <;> rfl

theorem non_boolean_left (operation : Operation) (tag : Nat) (right : Value) :
    dispatch operation [.other tag, right] = none := by
  cases operation <;> rfl

theorem incorrect_arity (operation : Operation) (arguments : List Value)
    (wrong : arguments.length ≠ 2) : dispatch operation arguments = none := by
  cases arguments with
  | nil => cases operation <;> rfl
  | cons first rest =>
      cases rest with
      | nil => cases operation <;> cases first <;> rfl
      | cons second tail =>
          cases tail with
          | nil => exact False.elim (wrong rfl)
          | cons third tail =>
              cases operation <;> cases first <;> cases second <;> rfl

/-- The strict node evaluator reads the right operand even when the left
value would decide a short-circuit operator. -/
theorem false_and_missing_right (registers : Regs Value) (slot : Nat)
    (missing : registers slot = none) :
    eval semantics noCalls registers
      (.op .conjunction [.lit (.boolean false), .slot slot]) = none := by
  simp [eval, evalList, semantics, missing]

theorem true_or_missing_right (registers : Regs Value) (slot : Nat)
    (missing : registers slot = none) :
    eval semantics noCalls registers
      (.op .disjunction [.lit (.boolean true), .slot slot]) = none := by
  simp [eval, evalList, semantics, missing]

theorem false_and_wrong_right (registers : Regs Value) (tag : Nat) :
    eval semantics noCalls registers
      (.op .conjunction [.lit (.boolean false), .lit (.other tag)]) = none := by
  rfl

theorem true_or_wrong_right (registers : Regs Value) (tag : Nat) :
    eval semantics noCalls registers
      (.op .disjunction [.lit (.boolean true), .lit (.other tag)]) = none := by
  rfl

/-- The separately defined register executor agrees with the strict source
interpretation, not just on successful Boolean results but on decline too. -/
theorem lowering_observation (fuses : Operation → Nat → Bool)
    {locals next : Nat} {scope : Finset Nat}
    (body : Node Value Operation Nat Empty) (registers : Regs Value)
    (scoping : Scoped semantics.toPatterns locals scope body)
    (bound : ∀ slot ∈ scope, slot < locals) (fresh : locals ≤ next) :
    answer (exec semantics noCalls (compile fuses body true 0 next).1 registers) =
      (eval semantics noCalls registers body).map Prod.fst := by
  exact (lower_answers semantics noCalls fuses scoping bound (fun _ _ => rfl) fresh).answer_eq

example : dispatch .conjunction [.boolean true, .boolean false] = some (.boolean false) := by
  decide

example : dispatch .disjunction [.boolean false, .boolean true] = some (.boolean true) := by
  decide

/-- Numeric truthiness is not part of this admission contract. -/
example : dispatch .disjunction [.boolean true, .other 1] ≠ some (.boolean true) := by
  decide

#print axioms incorrect_arity
#print axioms false_and_missing_right
#print axioms true_or_missing_right
#print axioms lowering_observation

end Mettapedia.Machines.StrictBooleanIntrinsics
