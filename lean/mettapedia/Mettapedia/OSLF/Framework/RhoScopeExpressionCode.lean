import Mettapedia.OSLF.Framework.RhoScopeExpression

/-!
# Independently decoded programs for sorted scope expressions

Scope expressions compile to a postfix instruction stream. The interpreter
checks the sort and arity of every instruction, retaining variable indices
and fixed-point binders. Its roundtrip is proved for arbitrary stack tails;
malformed streams fail. Code length and supplied structural description
cost are compared only after the independent decoding theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeExpressionCode

open RhoScopeExpression Mettapedia.OSLF.Binding.RhoSchema

universe u

inductive Instruction (Atom : Type u) where
  | atom (label : Atom)
  | var (index : Nat)
  | disj (sort : Srt)
  | quote | drop | par | mu

abbrev Packed (Atom : Type u) := (sort : Srt) × Expression Atom sort

def step {Atom : Type u} : Instruction Atom → List (Packed Atom) → Option (List (Packed Atom))
  | .atom label, stack => some (⟨.pr, .atom label⟩ :: stack)
  | .var index, stack => some (⟨.nm, .var index⟩ :: stack)
  | .disj .pr, ⟨.pr, second⟩ :: ⟨.pr, first⟩ :: stack =>
      some (⟨.pr, .or first second⟩ :: stack)
  | .disj .nm, ⟨.nm, second⟩ :: ⟨.nm, first⟩ :: stack =>
      some (⟨.nm, .or first second⟩ :: stack)
  | .quote, ⟨.pr, process⟩ :: stack => some (⟨.nm, .quote process⟩ :: stack)
  | .drop, ⟨.nm, name⟩ :: stack => some (⟨.pr, .drop name⟩ :: stack)
  | .par, ⟨.pr, second⟩ :: ⟨.pr, first⟩ :: stack =>
      some (⟨.pr, .par first second⟩ :: stack)
  | .mu, ⟨.nm, body⟩ :: stack => some (⟨.nm, .mu body⟩ :: stack)
  | _, _ => none

def run {Atom : Type u} : List (Instruction Atom) → List (Packed Atom) → Option (List (Packed Atom))
  | [], stack => some stack
  | instruction :: rest, stack => (step instruction stack).bind (run rest)

theorem run_append {Atom : Type u} (first second : List (Instruction Atom))
    (stack : List (Packed Atom)) :
    run (first ++ second) stack = (run first stack).bind (run second) := by
  induction first generalizing stack with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [List.cons_append, run, Option.bind_assoc]
    exact congrArg (Option.bind (step instruction stack)) (funext ih)

def encode {Atom : Type u} : {sort : Srt} → Expression Atom sort → List (Instruction Atom)
  | _, .atom label => [.atom label]
  | _, .var index => [.var index]
  | sort, .or first second => encode first ++ encode second ++ [.disj sort]
  | _, .quote process => encode process ++ [.quote]
  | _, .drop name => encode name ++ [.drop]
  | _, .par first second => encode first ++ encode second ++ [.par]
  | _, .mu body => encode body ++ [.mu]

theorem run_encode {Atom : Type u} {sort : Srt} (expression : Expression Atom sort)
    (stack : List (Packed Atom)) :
    run (encode expression) stack = some (⟨sort, expression⟩ :: stack) := by
  induction expression generalizing stack with
  | atom label => rfl
  | var index => rfl
  | @or sort first second firstIH secondIH =>
    cases sort <;> simp [encode, run_append, firstIH, secondIH, run, step]
  | quote process ih => simp [encode, run_append, ih, run, step]
  | drop name ih => simp [encode, run_append, ih, run, step]
  | par first second firstIH secondIH =>
    simp [encode, run_append, firstIH, secondIH, run, step]
  | mu body ih => simp [encode, run_append, ih, run, step]

def decode {Atom : Type u} (code : List (Instruction Atom)) : Option (Packed Atom) :=
  match run code [] with
  | some [expression] => some expression
  | _ => none

theorem decode_encode {Atom : Type u} {sort : Srt} (expression : Expression Atom sort) :
    decode (encode expression) = some ⟨sort, expression⟩ := by
  rw [decode, run_encode]

theorem encode_injective {Atom : Type u} {sort : Srt} :
    Function.Injective (encode (Atom := Atom) (sort := sort)) := by
  intro first second same
  have decoded := congrArg decode same
  rw [decode_encode, decode_encode] at decoded
  exact eq_of_heq ((Sigma.mk.inj_iff.mp (Option.some.inj decoded)).2)

def weight {Atom : Type u} (atomCost : Atom → Nat) : Instruction Atom → Nat
  | .atom label => atomCost label
  | _ => 1

def programCost {Atom : Type u} (atomCost : Atom → Nat) (code : List (Instruction Atom)) : Nat :=
  (code.map (weight atomCost)).sum

theorem cost_append {Atom : Type u} (atomCost : Atom → Nat)
    (first second : List (Instruction Atom)) :
    programCost atomCost (first ++ second) = programCost atomCost first + programCost atomCost second := by
  simp [programCost]

theorem cost_singleton {Atom : Type u} (atomCost : Atom → Nat) (instruction : Instruction Atom) :
    programCost atomCost [instruction] = weight atomCost instruction := rfl

theorem cost_encode {Atom : Type u} (atomCost : Atom → Nat) {sort : Srt}
    (expression : Expression Atom sort) :
    programCost atomCost (encode expression) = expression.description atomCost := by
  induction expression with
  | atom label => rfl
  | var index => rfl
  | @or sort first second firstIH secondIH =>
    rw [encode, cost_append, cost_append, firstIH, secondIH]
    simp [cost_singleton, weight, Expression.description, Nat.add_assoc]
  | quote process ih =>
    rw [encode, cost_append, ih]
    rfl
  | drop name ih =>
    rw [encode, cost_append, ih]
    rfl
  | par first second firstIH secondIH =>
    rw [encode, cost_append, cost_append, firstIH, secondIH]
    simp [cost_singleton, weight, Expression.description, Nat.add_assoc]
  | mu body ih =>
    rw [encode, cost_append, ih]
    rfl

/-- Uniform word cost counts actual instructions; payload bits are treated separately. -/
theorem length_encode {Atom : Type u} {sort : Srt} (expression : Expression Atom sort) :
    (encode expression).length = expression.description (fun _ => 1) := by
  have same := cost_encode (fun _ : Atom => 1) expression
  have uniform : ∀ code : List (Instruction Atom),
      programCost (fun _ => 1) code = code.length := by
    intro code
    induction code with
    | nil => rfl
    | cons instruction rest ih =>
      cases instruction <;> simp [programCost, weight] at ih ⊢ <;> omega
  rw [uniform] at same
  exact same

end Mettapedia.OSLF.Framework.RhoScopeExpressionCode
