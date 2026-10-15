import Mettapedia.OSLF.NativeTypes.Decision.Stream
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend

open Mettapedia.OSLF.Framework

/-!
# Resumable authored lambda work

Each node inspection is suspended until its work item is advanced. Beta
occurrences and enabled congruence branches preserve the original declaration
order. Child ordinals count yielded physical firings, independently of
inspection pauses. The exhaustive comparison recovers the existing complete
authored readout; ordinary bounded execution never computes that readout.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled

open Mettapedia.OSLF.Binding
open LambdaContextualRung LambdaScopedAuthoringComparison LambdaPatternRendering
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Decision.Scheduling

def tasks (selection : Selection) {Γ : Ctx sig} (source : Term sig Γ .term) :
    Stream (Firing selection source) := .pause fun _ =>
  match source with
  | .var _ => .done
  | .op .lam (.cons body .nil) =>
      if enabled : selection.lamCong = true then
        Stream.mapIdx (liftLam enabled) (tasks selection body)
      else .done
  | .op .app (.cons function (.cons argument .nil)) =>
      Stream.append (Stream.ofList (betaFirings selection (appT function argument))) fun _ =>
        Stream.append
          (if enabled : selection.appCongL = true then
            Stream.mapIdx (liftAppL enabled argument) (tasks selection function)
           else .done) fun _ =>
          if enabled : selection.appCongR = true then
            Stream.mapIdx (liftAppR enabled function) (tasks selection argument)
          else .done
termination_by nodeCount source
decreasing_by all_goals simp only [nodeCount, argumentNodeCount]; omega

theorem flatten_tasks (selection : Selection) : {Γ : Ctx sig} →
    (source : Term sig Γ .term) → (tasks selection source).flatten = firings selection source
  | _, .var _ => by rw [tasks, firings]; rfl
  | _, .op .lam (.cons body .nil) => by
      rw [tasks, firings]
      change (if enabled : selection.lamCong = true then
        Stream.mapIdx (liftLam enabled) (tasks selection body) else .done).flatten = _
      split
      · rw [Stream.flatten_mapIdx_zero, flatten_tasks selection body]
        rfl
      · rfl
  | _, .op .app (.cons function (.cons argument .nil)) => by
      have beta := Stream.flatten_ofList (betaFirings selection (appT function argument))
      have left :
          (if enabled : selection.appCongL = true then
            Stream.mapIdx (liftAppL enabled argument) (tasks selection function)
           else .done).flatten =
          (if enabled : selection.appCongL = true then
            (firings selection function).zipIdx.map fun (entry, ordinal) =>
              liftAppL enabled argument entry ordinal
           else []) := by
        split
        · rename_i enabled
          exact (Stream.flatten_mapIdx_zero (liftAppL enabled argument) (tasks selection function)).trans
            (congrArg (fun entries => entries.zipIdx.map fun (entry, ordinal) =>
              liftAppL enabled argument entry ordinal) (flatten_tasks selection function))
        · rfl
      have right :
          (if enabled : selection.appCongR = true then
            Stream.mapIdx (liftAppR enabled function) (tasks selection argument)
           else .done).flatten =
          (if enabled : selection.appCongR = true then
            (firings selection argument).zipIdx.map fun (entry, ordinal) =>
              liftAppR enabled function entry ordinal
           else []) := by
        split
        · rename_i enabled
          exact (Stream.flatten_mapIdx_zero (liftAppR enabled function) (tasks selection argument)).trans
            (congrArg (fun entries => entries.zipIdx.map fun (entry, ordinal) =>
              liftAppR enabled function entry ordinal) (flatten_tasks selection argument))
        · rfl
      rw [tasks, firings]
      change (Stream.append _ (fun _ => Stream.append _ (fun _ => _))).flatten = _
      exact (Stream.flatten_append _ _).trans
        ((congrArg (fun rest => _ ++ rest) (Stream.flatten_append _ _)).trans
          ((congrArg₂ List.append beta (congrArg₂ List.append left right)).trans
            (List.append_assoc _ _ _).symm))
termination_by _ source => nodeCount source
decreasing_by all_goals simp only [nodeCount, argumentNodeCount]; omega

def state (selection : Selection) {Γ : Ctx sig} (budget : Nat) (source : Term sig Γ .term) :=
  Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run (tasks selection source) budget

def frontier (selection : Selection) {Γ : Ctx sig} (budget : Nat) (source : Term sig Γ .term) :=
  (state selection budget source).outputs

def closed (selection : Selection) {Γ : Ctx sig} (budget : Nat) (source : Term sig Γ .term) :=
  (state selection budget source).closed

def completionBudget (selection : Selection) {Γ : Ctx sig} (source : Term sig Γ .term) : Nat :=
  (tasks selection source).workBound

theorem exact_resume (selection : Selection) {Γ : Ctx sig}
    (first more : Nat) (source : Term sig Γ .term) :
    state selection (first + more) source = resume more (state selection first source) :=
  run_resume (tasks selection source) first more

theorem ordered_partition (selection : Selection) {Γ : Ctx sig}
    (budget : Nat) (source : Term sig Γ .term) :
    frontier selection budget source ++ (state selection budget source).pending.flatten = firings selection source :=
  (run_partition (tasks selection source) budget).trans (flatten_tasks selection source)

theorem frontier_sound (selection : Selection) {Γ : Ctx sig} (budget : Nat)
    (source : Term sig Γ .term) (receipt : Firing selection source)
    (listed : receipt ∈ frontier selection budget source) :
    SelectedStep selection Γ source receipt.target :=
  firings_sound source receipt (by
    rw [← flatten_tasks selection source]
    exact listed_sound (tasks selection source) budget receipt listed)

theorem closed_frontier_exact (selection : Selection) {Γ : Ctx sig} (budget : Nat)
    (source : Term sig Γ .term) (complete : closed selection budget source = true) :
    frontier selection budget source = firings selection source :=
  (closed_readout (tasks selection source) budget complete).trans (flatten_tasks selection source)

def backend (selection : Selection) (Γ : Ctx sig) :
    Backend (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.theory selection Γ) (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.Source Γ) where
  Receipt source := Firing selection source
  target _ receipt := receipt.target
  frontier := frontier selection
  closed := closed selection
  sound := frontier_sound selection
  coverage budget source complete target step := by
    obtain ⟨receipt, listed, same⟩ := firings_complete step
    refine ⟨receipt, ?_, same.symm⟩
    rw [closed_frontier_exact selection budget source complete]
    exact listed
  target_admitted _ _ _ receipt _ := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.source_admitted receipt.target
  completionBudget := completionBudget selection
  complete_at source _ := run_closed_at (tasks selection source) _ (Nat.le_refl _)
  frontier_stable source budget enough := congrArg Cursor.outputs (run_stable (tasks selection source) budget enough)
  closed_stable source budget enough := congrArg Cursor.closed (run_stable (tasks selection source) budget enough)

/-- Coverage and the effective bound hold over all intrinsic contexts and all
selections of the original authored declarations. -/
theorem whole_profile_complete (selection : Selection) (Γ : Ctx sig)
    (source : Term sig Γ .term) :
    (backend selection Γ).closed ((backend selection Γ).completionBudget source) source = true :=
  (backend selection Γ).complete_at source (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.source_admitted source)

theorem whole_formula_complete {Leaf : Type} (selection : Selection) (Γ : Ctx sig)
    (tests : Leaf → Test (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.theory selection Γ)
      (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.Source Γ)) (formula : Formula Leaf) (source : Term sig Γ .term) :
    (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check (backend selection Γ) tests formula source
      (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.workBound (backend selection Γ) tests formula source)).Decided :=
  checked_complete (backend selection Γ) tests formula source
    (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.source_admitted source) _ (Nat.le_refl _)

theorem zero_work_keeps_inspection (selection : Selection) {Γ : Ctx sig} (source : Term sig Γ .term) :
    frontier selection 0 source = [] ∧ closed selection 0 source = false := by
  constructor
  · rfl
  · unfold closed state Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run start Cursor.closed
    simp only [resume]
    rw [tasks.eq_def]

theorem original_authored_readout {Γ : Ctx sig} (source : Term sig Γ .term)
    (fuel : Nat) (enough : nodeCount source ≤ fuel) :
    Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
      Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty LambdaAuthoredFullRuleProfile.language
        fuel Γ.length (encodeTerm source) =
      (tasks {} source).flatten.map (fun receipt => (receipt.history, encodeTerm receipt.target)) := by
  rw [flatten_tasks]
  exact Mettapedia.OSLF.NativeTypes.Instances.Lambda.EngineComparison.engine_readout source fuel enough

end Mettapedia.OSLF.NativeTypes.Instances.Lambda.Scheduled
