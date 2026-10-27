import Mettapedia.Algorithms.Compression.TemplateExport
import Mettapedia.Algorithms.Compression.ValueArguments

/-!
# Parameter transport without changing computational demand

Constructor interpretations receive unevaluated argument computations. They
may request an argument zero, one or several times and may be effectful,
failing or nondeterministic. The actual port-renumbering compiler preserves
that interpretation. Delayed computations are packaged as values before a
strict helper call, rather than executed and cached as argument results.

This is the nonreflective demand interface. Actual source evaluation positions,
entry-value admission, closure capture, syntax lowering and C execution are
separate obligations, not consequences of a type label or a source name.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.DeferredArguments

open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema
open TemplateMatching

universe u

inductive Argument (m : Type u → Type u) (α : Type u) where
  | ready (value : α)
  | delayed (force : Unit → m α)

def read {m : Type u → Type u} [Monad m] {α : Type u} : Argument m α → m α
  | .ready value => pure value
  | .delayed force => force ()

mutual
def evaluate {Action : Type} (operators : Nat → List Action → Action)
    (environment : SchemaHole → Option Action) : SchemaPattern → Option Action
  | .hole role index => environment (role, index)
  | .node op children => (evaluateList operators environment children).map (operators op)

def evaluateList {Action : Type} (operators : Nat → List Action → Action)
    (environment : SchemaHole → Option Action) : List SchemaPattern → Option (List Action)
  | [] => some []
  | first :: rest => do
      let value ← evaluate operators environment first
      let values ← evaluateList operators environment rest
      pure (value :: values)
end

def transport {Action : Type} (parameters : List SchemaHole)
    (environment : SchemaHole → Option Action) : SchemaHole → Option Action :=
  fun key => if key.1 = .value then parameters[key.2]?.bind environment else none

theorem evaluate_compiled {Action : Type} (operators : Nat → List Action → Action)
    (environment : SchemaHole → Option Action) (parameters : List SchemaHole) :
    ∀ pattern, (∀ key ∈ schemaOccurrences pattern, key ∈ parameters) →
      evaluate operators (transport parameters environment) (TemplateExport.body parameters pattern) =
        evaluate operators environment pattern := by
  apply SchemaPattern.rec
    (motive_1 := fun pattern => (∀ key ∈ schemaOccurrences pattern, key ∈ parameters) →
      evaluate operators (transport parameters environment) (TemplateExport.body parameters pattern) =
        evaluate operators environment pattern)
    (motive_2 := fun patterns => (∀ key ∈ schemaOccurrencesList patterns, key ∈ parameters) →
      evaluateList operators (transport parameters environment) (TemplateExport.bodies parameters patterns) =
        evaluateList operators environment patterns)
  · intro role index covered
    have present : (role, index) ∈ parameters := covered _ (by simp [schemaOccurrences])
    simp [TemplateExport.body, evaluate, transport, List.getElem?_idxOf present]
  · intro op children ih covered
    simpa only [TemplateExport.body, evaluate] using congrArg (Option.map (operators op)) (ih covered)
  · intro covered
    rfl
  · intro first rest firstResult restResult covered
    have headCovered : ∀ key ∈ schemaOccurrences first, key ∈ parameters := by
      intro key present
      exact covered key (List.mem_append_left _ present)
    have tailCovered : ∀ key ∈ schemaOccurrencesList rest, key ∈ parameters := by
      intro key present
      exact covered key (List.mem_append_right _ present)
    simp only [TemplateExport.bodies, evaluateList, firstResult headCovered, restResult tailCovered]

theorem compiled_demand_preserved {m : Type → Type} [Monad m] {α : Type}
    (operators : Nat → List (m α) → m α) (arguments : SchemaHole → Option (Argument m α))
    (pattern : SchemaPattern) :
    evaluate operators (transport (TemplateExport.parameters pattern) (fun key => (arguments key).map read))
      (TemplateExport.body (TemplateExport.parameters pattern) pattern) =
        evaluate operators (fun key => (arguments key).map read) pattern := by
  apply evaluate_compiled
  intro key present
  simpa [TemplateExport.parameters] using present

def callOne {m : Type → Type} [Monad m] {α β : Type}
    (argument : Argument m α) (body : m α → m β) : m β := do
  let values ← ValueArguments.collect 1 (fun _ => pure argument)
  body (read (values 0))

theorem callOne_preserves {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (argument : Argument m α) (body : m α → m β) :
    callOne argument body = body (read argument) := by
  simp [callOne, ValueArguments.collect_pure]

namespace Controls

def choices : Argument List Nat := .delayed (fun _ => [1, 2])

def twice {m : Type → Type} [Monad m] (action : m Nat) : m Nat := do
  let first ← action
  let second ← action
  pure (first + second)

theorem delayed_choice_is_not_cached :
    callOne choices twice = [2, 3, 3, 4] ∧
      ValueArguments.strictApply (fun _ : Fin 1 => [1, 2])
        (fun arguments => twice (arguments 0)) = [2, 4] := by
  constructor <;> rfl

theorem unused_delayed_failure_does_not_erase_success :
    callOne (.delayed (fun _ => ([] : List Nat))) (fun _ => [7]) = [7] := by rfl

def counted : Argument (StateM Nat) Nat := .delayed (fun _ => fun state => (7, state + 1))

theorem delayed_effect_runs_at_each_request :
    (callOne counted twice).run 0 = (14, 2) := by rfl

theorem unused_delayed_effect_is_not_run :
    (callOne counted (fun _ => pure 9)).run 0 = (9, 0) := by rfl

theorem different_role_keys_keep_different_ports :
    let ports : List SchemaHole := [(.code, 0), (.value, 0)]
    transport ports (fun key => if key.1 = .code then some 3 else some 7) (.value, 0) = some 3 ∧
      transport ports (fun key => if key.1 = .code then some 3 else some 7) (.value, 1) = some 7 := by
  constructor <;> rfl

end Controls
end Mettapedia.Algorithms.Compression.DeferredArguments
