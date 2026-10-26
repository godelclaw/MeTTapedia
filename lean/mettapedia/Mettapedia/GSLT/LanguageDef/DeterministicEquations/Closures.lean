import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Program

/-!
# Deterministic equation programs with closure calls

A closure is a value `(partial g (list c₁ … cₘ))`: a symbol `g` and the values
it has captured.  It is what the term `(partial g (list e₁ … eₘ))` evaluates to
when no equation defines `partial` and the host does not handle it.

This evaluator extends `DeterministicEquations.eval` by one rule.  An
expression whose head is not a symbol evaluates its elements from left to
right as before; when the first value is a closure `(partial g (list cs))`,
the expression is the call of `g` on `cs` followed by the other values, as a
PeTTa partial application completes its stored argument prefix
(`PartialApplicationExpansion.expand`).  Any other such expression is still a
constructor of its values.  Every other rule, the program's equation
selection and the host's primitives are those of `DeterministicEquations`.

Fuel bounds the depth of evaluation, as in `DeterministicEquations.eval`, and
is monotone (`eval_mono`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Closures

open Mettapedia.GSLT.LanguageDef.DeterministicEquations

/-- The closure of `g` that has captured `cs`. -/
def closure (g : String) (cs : List Term) : Term :=
  .expr [.sym "partial", .sym g, .list cs]

/-- The symbol and captured values of a closure. -/
def closureOf : Term → Option (String × List Term)
  | .expr [.sym "partial", .sym g, .list cs] => some (g, cs)
  | _ => none

@[simp] theorem closureOf_closure (g : String) (cs : List Term) :
    closureOf (closure g cs) = some (g, cs) := rfl

/-- The values of an expression whose head is not a symbol: the call of a
closure, or a constructor. -/
def applyValues (call : String → List Term → Outcome) : List Term → Outcome
  | [] => .value (.expr [])
  | v :: vs =>
    match closureOf v with
    | some (g, cs) => call g (cs ++ vs)
    | none => .value (.expr (v :: vs))

/-- One step of the evaluation of a term: `DeterministicEquations.evalStep`
with closure calls. -/
def evalStep (ev : Env → Term → Outcome) (call : String → List Term → Outcome)
    (env : Env) : Term → Outcome
  | .var x =>
    match env.lookup x with
    | some v => .value v
    | none => .failure
  | .sym s => .value (.sym s)
  | .lit s => .value (.lit s)
  | .list items =>
    match evalItemsWith ev env items with
    | .values vs => .value (.list vs)
    | .stop o => o
  | .expr [] => .value (.expr [])
  | .expr [.sym "let", .var x, e, b] =>
    match ev env e with
    | .value v => ev ((x, v) :: env) b
    | o => o
  | .expr [.sym "let", _, _, _] => .failure
  | .expr [.sym "metta-nullary", .sym s] => .value (.expr [.sym s])
  | .expr [.sym "metta-nullary", _] => .failure
  | .expr (.sym f :: args) =>
    match evalItemsWith ev env args with
    | .values vs => call f vs
    | .stop o => o
  | .expr items =>
    match evalItemsWith ev env items with
    | .values vs => applyValues call vs
    | .stop o => o

/-- Evaluation of a term under an environment with some fuel. -/
def eval (P : Program) (H : Host) : Nat → Env → Term → Outcome
  | 0, _, _ => .exhausted
  | n + 1, env, t => evalStep (eval P H n) (applyWith P H (eval P H n)) env t

/-- A call with some fuel. -/
abbrev apply (P : Program) (H : Host) (n : Nat) (f : String) (vs : List Term) :
    Outcome :=
  applyWith P H (eval P H n) f vs

/-! ## Fuel -/

theorem applyValues_refines {call call' : String → List Term → Outcome}
    (hc : ∀ f vs, Refines (call f vs) (call' f vs)) :
    ∀ vs, Refines (applyValues call vs) (applyValues call' vs)
  | [] => Refines.refl _
  | v :: vs => by
    rcases hv : closureOf v with _ | ⟨g, cs⟩
    · simp only [applyValues, hv]
      exact Refines.refl _
    · simp only [applyValues, hv]
      exact hc _ _

theorem evalStep_refines {ev ev' : Env → Term → Outcome}
    {call call' : String → List Term → Outcome}
    (h : ∀ env t, Refines (ev env t) (ev' env t))
    (hc : ∀ f vs, Refines (call f vs) (call' f vs)) (env : Env) (t : Term) :
    Refines (evalStep ev call env t) (evalStep ev' call' env t) := by
  unfold evalStep
  split
  · exact Refines.refl _
  · exact Refines.refl _
  · exact Refines.refl _
  · rename_i items
    rcases evalItemsWith_refines h env items with hs | hs
    · rw [hs]
      exact Refines.refl _
    · rw [hs]
      exact Or.inl rfl
  · exact Refines.refl _
  · rename_i x e b
    rcases h env e with he | he
    · rw [he]
      exact Or.inl rfl
    · rw [← he]
      split
      · exact h _ _
      · exact Refines.refl _
  · exact Refines.refl _
  · exact Refines.refl _
  · exact Refines.refl _
  · rename_i f args _ _ _ _
    rcases evalItemsWith_refines h env args with hs | hs
    · rw [hs]
      split
      · exact hc _ _
      · exact Refines.refl _
    · rw [hs]
      exact Or.inl rfl
  · rename_i items _ _ _ _ _ _
    rcases evalItemsWith_refines h env items with hs | hs
    · rw [hs]
      split
      · exact applyValues_refines hc _
      · exact Refines.refl _
    · rw [hs]
      exact Or.inl rfl

/-- One more unit of fuel refines every evaluation. -/
theorem eval_refines_succ (P : Program) (H : Host) :
    ∀ n env t, Refines (eval P H n env t) (eval P H (n + 1) env t)
  | 0, _, _ => Or.inl rfl
  | n + 1, env, t => by
    simp only [eval]
    exact evalStep_refines (eval_refines_succ P H n)
      (applyWith_refines P H (eval_refines_succ P H n)) env t

/-- More fuel refines every evaluation. -/
theorem eval_refines_add (P : Program) (H : Host) (n k : Nat) (env : Env)
    (t : Term) : Refines (eval P H n env t) (eval P H (n + k) env t) := by
  induction k with
  | zero => exact Refines.refl _
  | succ k ih =>
    rcases ih with h | h
    · exact Or.inl h
    · rw [h, ← Nat.add_assoc]
      exact eval_refines_succ P H (n + k) env t

/-- Fuel is monotone: an evaluation that ends with some fuel ends the same way
with more. -/
theorem eval_mono (P : Program) (H : Host) (n k : Nat) (env : Env) (t : Term)
    (h : eval P H n env t ≠ .exhausted) :
    eval P H (n + k) env t = eval P H n env t :=
  ((eval_refines_add P H n k env t).eq h).symm

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Closures
