import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls

open Mettapedia.OSLF.Framework

/-!
# Delayed lambda frontier controls

The first inspection and first yielded beta receipt have distinct work
positions. These controls use the original generated constructor tests on
the new cursor backend, including negative and mixed-successor questions.
Capture avoidance and coincident-target histories are preserved.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Lambda.ScheduledControls

open Mettapedia.OSLF.Binding
open LambdaContextualRung LambdaScopedAuthoringComparison
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Scheduling
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls

def run {Γ : Ctx sig} (selection : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.Selection)
    (formula : Formula Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.Leaf)
    (source : Term sig Γ .term) (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.backend selection Γ)
    (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.tests selection Γ) formula source budget

def observe (label : String) (make : Formula Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.Leaf →
    Formula Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.Leaf) {Γ : Ctx sig}
    (source : Term sig Γ .term) (budget : Nat) : Option (Option Bool) := do
  let former ← Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.former? label
  return (run {} (make (.atom former)) source budget).answer

def targets {Γ : Ctx sig} (budget : Nat) (source : Term sig Γ .term) :=
  (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.frontier {} budget source).map fun receipt =>
    encodeTerm receipt.target

def mixedQuestion (make : Formula Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.Leaf →
    Formula Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.Leaf) : Option (Option Bool) := do
  let former ← leftLambda?
  return (run {} (make (.atom former)) mixed 30).answer

#guard targets 0 redex == []
#guard targets 1 redex == []
#guard targets 2 redex == [encodeTerm identity]
#guard Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.closed {} 2 redex == false
#guard Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.closed {} 8 redex == true
#guard observe "Lam" Formula.possibility redex 1 == some none
#guard observe "Lam" Formula.possibility redex 3 == some (some true)
#guard observe "App" Formula.possibility redex 3 == some none
#guard observe "App" Formula.possibility redex 10 == some (some false)
#guard observe "Lam" Formula.outgoingUniversal redex 10 == some (some true)
#guard observe "App" Formula.outgoingUniversal redex 3 == some (some false)
#guard mixedQuestion Formula.possibility == some (some true)
#guard mixedQuestion Formula.outgoingUniversal == some (some false)
#guard (run {} (.possibility (.possibility .top)) redex 30).answer == some false
#guard (run {} (.outgoingUniversal .bottom) identity 5).answer == some true
#guard (run {} (.possibility .top) underLambda 30).answer == some true
#guard (run {lamCong := false} (.possibility .top) underLambda 5).answer == some false
#guard targets 50 captureSource == [encodeTerm captureTarget]
#guard !(targets 50 captureSource).contains (encodeTerm capturedIncorrectly)
#guard targets 100 duplicate == [encodeTerm duplicate, encodeTerm duplicate]
#guard (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.frontier {} 100 duplicate).map
    (fun receipt => match receipt.history with
      | .fire index [.step premise ordinal (.fire child [])] => (index, premise, ordinal, child)
      | _ => (100, 100, 100, 100)) == [(2, 0, 0, 0), (3, 0, 0, 0)]

theorem first_inspection_is_not_a_yield : targets 1 redex = [] := by
  unfold targets Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.frontier Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.state
    Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run
  simp only [resume, start, advance, Cursor.outputs]
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.tasks.eq_def]
  rfl

theorem first_yield_before_closure :
    targets 2 redex = [encodeTerm identity] ∧
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.closed {} 2 redex = false := by
  constructor
  · unfold targets Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.frontier Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.state
      Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run
    simp only [resume, start, advance, Cursor.outputs]
    rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.tasks.eq_def]
    rfl
  · unfold Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.closed Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.state
      Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run
    simp only [resume, start, advance, Cursor.closed]
    rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.tasks.eq_def]
    rfl

theorem pause_resume_preserves_cursor (first more : Nat) :
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.state {} (first + more) duplicate =
      resume more (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.state {} first duplicate) :=
  Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.exact_resume {} first more duplicate

theorem all_duplicate_origins_retained :
    (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.tasks {} duplicate).flatten.map (·.history) =
      [.fire 2 [.step 0 0 (.fire 0 [])], .fire 3 [.step 0 0 (.fire 0 [])]] := by
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.flatten_tasks]
  exact duplicate_origins_retained

theorem bounded_duplicate_origins_retained :
    (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.frontier {}
      (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.completionBudget {} duplicate) duplicate).map (·.history) =
      [.fire 2 [.step 0 0 (.fire 0 [])], .fire 3 [.step 0 0 (.fire 0 [])]] := by
  have complete : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.closed {}
      (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.completionBudget {} duplicate) duplicate = true :=
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.whole_profile_complete {} [] duplicate
  exact (congrArg (fun entries => entries.map (·.history))
    (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.closed_frontier_exact {} _ duplicate complete)).trans
      duplicate_origins_retained

theorem both_polarities_complete (formula : Formula Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.Leaf) :
    (run {} formula mixed
      (workBound (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.backend {} [])
        (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.tests {} []) formula mixed)).Decided :=
  Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled.whole_formula_complete {} []
    (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.tests {} []) formula mixed

end Mettapedia.OSLF.NativeTypes.Instances.Lambda.ScheduledControls
