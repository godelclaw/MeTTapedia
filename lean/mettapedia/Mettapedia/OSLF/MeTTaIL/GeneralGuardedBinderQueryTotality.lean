import Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseTotalityReadiness

/-!
# Resolved guard queries for arbitrary contextual binder captures

Every actual provider row and argument cursor either completes or rejects the
guard comparison. The query input remains available for arbitrary typed
process bodies with the original Name dependency telescope. Duplicate rows
retain their original cursor positions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderExecution

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open EquationFrontierBinderProfile

def environment (allowed : List Token) : GeneralPremise.Environment := GeneralPlanEnvironment.environment (plan allowed)

def allowSignature : GeneralPremise.Signature := ⟨"allow", [.proc], [.input]⟩

def query (choice : Choice) (bound : List TypeExpr) (initial : Assignment) : GeneralPremise.Query.Request :=
  ⟨choice.context bound, "allow", [.fvar "Q"], initial⟩

theorem query_signature (allowed : List Token) (choice : Choice) (bound : List TypeExpr) (initial : Assignment) :
    GeneralPremise.signature? (environment allowed).provider (query choice bound initial).relation
      (query choice bound initial).arguments.length = some allowSignature := rfl

theorem provider_row_values {allowed : List Token} {index : Nat} {row : GeneralPremise.ProviderRow}
    (found : (environment allowed).provider.rows[index]? = some row) :
    ∃ token, row.values = [guard token] := by
  have member := List.mem_of_getElem? found
  change row ∈ allowed.map (fun token => (⟨"allow", [guard token]⟩ : GeneralPremise.ProviderRow)) at member
  obtain ⟨token, _, same⟩ := List.mem_map.mp member
  subst row
  exact ⟨token, rfl⟩

def QueryTaskSafe (allowed : List Token) (choice : Choice) (bound : List TypeExpr) (initial : Assignment) :
    GeneralPremise.Query.Task (environment allowed) (query choice bound initial) → Prop
  | .start => True
  | .rows frame => frame.signature = allowSignature
  | .arguments frame => frame.assignment = initial ∧
      ((frame.schemas = [] ∧ frame.values = [] ∧ frame.modes = []) ∨
        (frame.index = 0 ∧ frame.schemas = [.fvar "Q"] ∧ frame.modes = [.input] ∧
          ∃ token, frame.values = [guard token]))
  | .matcher _ => False

theorem query_task_ready {allowed : List Token} {choice : Choice} {bound : List TypeExpr} {initial : Assignment}
    (typed : GeneralPremise.TypedAssignment (environment allowed) (choice.context bound) initial)
    (names : GeneralPremise.BoundNames initial ["P", "Q"])
    (task : GeneralPremise.Query.Task (environment allowed) (query choice bound initial))
    (safe : QueryTaskSafe allowed choice bound initial task) :
    GeneralPremise.Query.checkTaskReady (environment allowed) (query choice bound initial) task = true := by
  cases task with
  | start =>
      simp only [GeneralPremise.Query.checkTaskReady, query_signature, Option.isSome_some]
  | rows frame => rfl
  | arguments frame =>
      rcases safe with ⟨same, finished | ⟨index, schemas, modes, token, values⟩⟩
      · rcases finished with ⟨schemas, values, modes⟩
        simp only [GeneralPremise.Query.checkTaskReady, schemas, values, modes]
      · obtain ⟨target, projected⟩ := query_projection_total typed names
        simp only [GeneralPremise.Query.checkTaskReady, schemas, values, modes]
        change (instantiateAt? choice.rule choice.spec bound.length (.premise 0 0 frame.index) [] 0
          frame.assignment (.fvar "Q")).isSome = true
        rw [same, index, projected]
        rfl
  | matcher frame => exact False.elim safe

theorem query_expand_safe {allowed : List Token} {choice : Choice} {bound : List TypeExpr} {initial : Assignment}
    (typed : GeneralPremise.TypedAssignment (environment allowed) (choice.context bound) initial)
    (names : GeneralPremise.BoundNames initial ["P", "Q"])
    (task : GeneralPremise.Query.Task (environment allowed) (query choice bound initial))
    (safe : QueryTaskSafe allowed choice bound initial task)
    (next : GeneralPremise.Query.Task (environment allowed) (query choice bound initial))
    (member : next ∈ (GeneralPremise.Query.expand (environment allowed) (query choice bound initial) task).tasks) :
    QueryTaskSafe allowed choice bound initial next := by
  cases task with
  | start =>
      simp only [GeneralPremise.Query.expand, query_signature, List.mem_singleton] at member
      subst next
      rfl
  | rows frame =>
      change frame.signature = allowSignature at safe
      simp only [GeneralPremise.Query.expand] at member
      split at member
      · simp only [List.not_mem_nil] at member
      · rename_i row found
        obtain ⟨token, values⟩ := provider_row_values found
        split at member
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with selected | tail
          · subst next
            exact ⟨rfl, Or.inr ⟨rfl, rfl, congrArg (fun signature => signature.modes) safe, token, values⟩⟩
          · subst next
            exact safe
        · simp only [List.mem_singleton] at member
          subst next
          exact safe
  | arguments frame =>
      rcases frame with ⟨rowIndex, argumentIndex, assignment, schemas, values, modes, origins, finish⟩
      change assignment = initial ∧
        ((schemas = [] ∧ values = [] ∧ modes = []) ∨
          (argumentIndex = 0 ∧ schemas = [.fvar "Q"] ∧ modes = [.input] ∧
            ∃ token, values = [guard token])) at safe
      rcases safe with ⟨same, finished | ⟨index, schemaShape, modeShape, token, valueShape⟩⟩
      · rcases finished with ⟨schemaShape, valueShape, modeShape⟩
        subst schemas values modes
        simp only [GeneralPremise.Query.expand, GeneralPremise.Query.expandArguments] at member
        split at member <;> simp at member
      · subst assignment argumentIndex schemas values modes
        obtain ⟨target, projected⟩ := query_projection_total typed names
        simp only [GeneralPremise.Query.expand, GeneralPremise.Query.expandArguments] at member
        split at member
        · rename_i absent
          change instantiateAt? choice.rule choice.spec bound.length (.premise 0 0 0) [] 0
            initial (.fvar "Q") = none at absent
          rw [projected] at absent
          cases absent
        · split at member
          · simp only [List.mem_singleton] at member
            subst next
            exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
          · simp at member
  | matcher frame => exact False.elim safe

def QuerySafe (allowed : List Token) (choice : Choice) (bound : List TypeExpr) (initial : Assignment)
    (state : GeneralPremise.Query.State (environment allowed) (query choice bound initial)) : Prop :=
  state.unresolved = [] ∧ ∀ task ∈ state.agenda, QueryTaskSafe allowed choice bound initial task

theorem query_start_safe (allowed : List Token) (choice : Choice) (bound : List TypeExpr) (initial : Assignment) :
    QuerySafe allowed choice bound initial (GeneralPremise.Query.start (environment allowed) (query choice bound initial)) := by
  constructor
  · rfl
  · intro task member
    simp only [GeneralPremise.Query.start, List.mem_singleton] at member
    subst task
    trivial

theorem query_tick_safe {allowed : List Token} {choice : Choice} {bound : List TypeExpr} {initial : Assignment}
    (typed : GeneralPremise.TypedAssignment (environment allowed) (choice.context bound) initial)
    (names : GeneralPremise.BoundNames initial ["P", "Q"])
    (state : GeneralPremise.Query.State (environment allowed) (query choice bound initial))
    (safe : QuerySafe allowed choice bound initial state) :
    QuerySafe allowed choice bound initial (GeneralPremise.Query.tick (environment allowed) (query choice bound initial) state) := by
  cases agenda : state.agenda with
  | nil => simpa only [GeneralPremise.Query.tick, GeneralPremise.Scheduler.tick, agenda] using safe
  | cons task remaining =>
      have first := safe.2 task (by simp [agenda])
      have resolved := GeneralPremise.Query.checkTaskReady_sound _ _ task (query_task_ready typed names task first)
      constructor
      · simp only [GeneralPremise.Query.tick, GeneralPremise.Scheduler.tick, agenda, safe.1, resolved, List.nil_append]
      · intro next member
        simp only [GeneralPremise.Query.tick, GeneralPremise.Scheduler.tick, agenda, List.mem_append] at member
        rcases member with fresh | later
        · exact query_expand_safe typed names task first next fresh
        · exact safe.2 next (by rw [agenda]; exact List.mem_cons_of_mem _ later)

theorem query_run_safe {allowed : List Token} {choice : Choice} {bound : List TypeExpr} {initial : Assignment}
    (typed : GeneralPremise.TypedAssignment (environment allowed) (choice.context bound) initial)
    (names : GeneralPremise.BoundNames initial ["P", "Q"]) (fuel : Nat) :
    QuerySafe allowed choice bound initial
      (GeneralPremise.Query.run (environment allowed) (query choice bound initial) fuel
        (GeneralPremise.Query.start (environment allowed) (query choice bound initial))) := by
  have preserved : ∀ state, QuerySafe allowed choice bound initial state →
      QuerySafe allowed choice bound initial
        (GeneralPremise.Query.run (environment allowed) (query choice bound initial) fuel state) := by
    induction fuel with
    | zero => exact fun _ safe => safe
    | succ fuel ih => exact fun state safe => ih _ (query_tick_safe typed names state safe)
  exact preserved _ (query_start_safe allowed choice bound initial)

theorem query_run_unresolved {allowed : List Token} {choice : Choice} {bound : List TypeExpr} {initial : Assignment}
    (typed : GeneralPremise.TypedAssignment (environment allowed) (choice.context bound) initial)
    (names : GeneralPremise.BoundNames initial ["P", "Q"]) (fuel : Nat) :
    (GeneralPremise.Query.run (environment allowed) (query choice bound initial) fuel
      (GeneralPremise.Query.start (environment allowed) (query choice bound initial))).unresolved = [] :=
  (query_run_safe typed names fuel).1

theorem query_completed {allowed : List Token} {choice : Choice} {bound : List TypeExpr} {initial : Assignment}
    (typed : GeneralPremise.TypedAssignment (environment allowed) (choice.context bound) initial)
    (names : GeneralPremise.BoundNames initial ["P", "Q"]) :
    ∃ fuel, GeneralPremise.Scheduler.complete
      (GeneralPremise.Query.run (environment allowed) (query choice bound initial) fuel
        (GeneralPremise.Query.start (environment allowed) (query choice bound initial))) = true := by
  obtain ⟨fuel, idle⟩ := GeneralPremise.Query.finiteDrain (environment allowed) (query choice bound initial)
    (GeneralPremise.Query.start (environment allowed) (query choice bound initial))
  exact ⟨fuel, (GeneralPremise.Scheduler.complete_iff _).mpr ⟨idle, query_run_unresolved typed names fuel⟩⟩

#print axioms query_run_unresolved
#print axioms query_completed

end Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderExecution
