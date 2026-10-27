import Mathlib.Tactic

/-!
# Sharing arguments already established as values

A computational context controls when, whether and how often it requests its
arguments. An ordinary strict helper first computes all arguments once, then
supplies the cached values. These differ for effects, choice and failure.
They agree for any lawful monad and any context when the incoming arguments
are already pure values. Purity of the context itself is not required.

This is the argument boundary, not a theorem that arbitrary source expressions
are values, that reflective contexts ignore new definitions, or that the C
evaluator refines this model. Source admission and native controls are separate.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.ValueArguments

universe u v
variable {m : Type u → Type v} [Monad m] {α β : Type u}

def collect : (count : Nat) → (Fin count → m α) → m (Fin count → α)
  | 0, _ => pure Fin.elim0
  | count + 1, arguments => do
      let first ← arguments 0
      let rest ← collect count (fun index => arguments index.succ)
      pure (Fin.cases first rest)

def strictApply {count : Nat} (arguments : Fin count → m α)
    (context : (Fin count → m α) → m β) : m β := do
  let values ← collect count arguments
  context (fun index => pure (values index))

theorem collect_pure [LawfulMonad m] (count : Nat) (values : Fin count → α) :
    collect count (fun index => pure (values index) : Fin count → m α) = pure values := by
  induction count with
  | zero =>
      simp only [collect]
      congr 1
      funext index
      exact Fin.elim0 index
  | succ count ih =>
      simp only [collect, ih, pure_bind]
      congr 1
      funext index
      cases index using Fin.cases <;> rfl

theorem strictApply_ready [LawfulMonad m] {count : Nat}
    (arguments : Fin count → m α) (values : Fin count → α)
    (ready : ∀ index, arguments index = pure (values index))
    (context : (Fin count → m α) → m β) :
    strictApply arguments context = context arguments := by
  have same : arguments = fun index => pure (values index) := funext ready
  rw [same]
  simp only [strictApply, collect_pure, pure_bind]

namespace Controls

def alternatives : Fin 1 → List Nat := fun _ => [1, 2]
def twice (arguments : Fin 1 → List Nat) : List Nat := do
  let first ← arguments 0
  let second ← arguments 0
  pure (first + second)

theorem sharing_changes_choice_multiplicity :
    twice alternatives = [2, 3, 3, 4] ∧ strictApply alternatives twice = [2, 4] := by decide

theorem eager_unused_failure_loses_the_answer :
    let absent : Fin 1 → List Nat := fun _ => []
    let unused : (Fin 1 → List Nat) → List Nat := fun _ => [0]
    unused absent = [0] ∧ strictApply absent unused = [] := by decide

def counted : Fin 1 → StateM Nat Nat := fun _ => fun state => (7, state + 1)
def unused : (Fin 1 → StateM Nat Nat) → StateM Nat Nat := fun _ => pure 0

theorem eager_unused_effect_is_observable :
    (unused counted).run 0 = (0, 0) ∧ (strictApply counted unused).run 0 = (0, 1) := by
  constructor <;> rfl

theorem ready_arguments_preserve_an_effectful_context :
    let ready : Fin 1 → StateM Nat Nat := fun _ => pure 7
    let body : (Fin 1 → StateM Nat Nat) → StateM Nat Nat := fun arguments => do
      let value ← arguments 0
      modify (· + 2)
      pure (value + value)
    strictApply ready body = body ready := by
  apply strictApply_ready _ (fun _ => 7)
  intro index
  rfl

end Controls
end Mettapedia.Algorithms.Compression.ValueArguments
