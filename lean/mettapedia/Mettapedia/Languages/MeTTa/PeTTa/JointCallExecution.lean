import Mettapedia.Languages.MeTTa.PeTTa.SchematicCallTyping
import Mettapedia.Machines.OrderedGuardPipeline

/-!
# Joint call contracts inside effectful execution

The finite candidate relation is checked by the independently justified
schematic constraint compiler. Its existential witnesses do not become
execution alternatives or binding refinements. A successful check retains
exactly the caller's local state. A rejected result retains the world left
by the body, including effects preceding the check.

These laws concern completed candidate observations. They do not identify
an unfinished classifier search with rejection, or prove the SWI translator
and its attributed-variable implementation correct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.JointCallExecution

open Mettapedia.Logic.LP
open Mettapedia.Machines.ScopedCommit
open Mettapedia.Machines.OrderedGuardPipeline
open SchematicCallTyping

variable {σ : LPSignature} {Local World Result : Type}
variable [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]

structure Fields (σ : LPSignature) (Local : Type) where
  inputs : Local → List (Candidates σ)
  result : Local → Candidates σ

def accepted (schemes : List (Scheme σ)) (fields : Fields σ Local)
    (state : Local) : Bool :=
  JointSchemeContracts.guard
    (compile schemes (fields.inputs state) (fields.result state)) []

theorem accepted_exact (schemes : List (Scheme σ)) (fields : Fields σ Local)
    (state : Local) :
    accepted schemes fields state = true ↔
      CallTyped schemes (fields.inputs state) (fields.result state) :=
  checker_exact schemes (fields.inputs state) (fields.result state)

def checkingStates (schemes : List (Scheme σ)) (fields : Fields σ Local) :
    Guard Local :=
  fun state => if accepted schemes fields state then [state] else []

/-- Positive independent typing evidence discharges a boundary for every
consumer, with the same bindings, alternatives, delimiter and world. -/
theorem accepted_erases_boundary (schemes : List (Scheme σ))
    (fields : Fields σ Local) (next : Body Local World) (state : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World)
    (typed : CallTyped schemes (fields.inputs state) (fields.result state)) :
    eval (guard (checkingStates schemes fields) next)
        state success failure saved world =
      eval next state success failure saved world := by
  have pass := (accepted_exact schemes fields state).mpr typed
  simp [Mettapedia.Machines.OrderedGuardPipeline.guard, checkingStates, pass, eval]

def checked (schemes : List (Scheme σ)) (fields : Fields σ Local)
    (body : Body Local World) : Body Local World :=
  andThen body (guard (checkingStates schemes fields) .done)

/-- Check each answer after the body has produced it. Witness multiplicity
never changes the body's success or failure continuations. -/
theorem checked_eval (schemes : List (Scheme σ)) (fields : Fields σ Local)
    (body : Body Local World) (state : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (checked schemes fields body) state success failure saved world =
      eval body state (fun value alternatives current =>
        if accepted schemes fields value then success value alternatives current
        else alternatives current) failure saved world := by
  unfold checked
  rw [eval_andThen]
  congr 1
  funext value alternatives current
  cases answer : accepted schemes fields value <;>
    simp [Mettapedia.Machines.OrderedGuardPipeline.guard, checkingStates, answer, eval]

/-- A known rejection cannot erase the preceding computation's effects. -/
theorem rejection_keeps_prefix (schemes : List (Scheme σ))
    (fields : Fields σ Local) (action : Local → World → Local × World)
    (state : Local) (world : World)
    (rejected : ¬ CallTyped schemes (fields.inputs (action state world).1)
      (fields.result (action state world).1)) :
    run (checked schemes fields (.effect action .done)) state world =
      ([], (action state world).2) := by
  have refused : accepted schemes fields (action state world).1 = false := by
    cases answer : accepted schemes fields (action state world).1 with
    | false => rfl
    | true => exact False.elim (rejected ((accepted_exact _ _ _).mp answer))
  simp [run, checked, andThen, Mettapedia.Machines.OrderedGuardPipeline.guard,
    checkingStates, eval, refused, finish]

namespace Controls

open JointSchemeContracts.Controls (sig number string)
open SchematicCallTyping.Controls (identityScheme)

def numberFields : Fields sig Nat := ⟨fun _ => [[.plain number]], fun _ => [.plain number]⟩
def conflictingFields : Fields sig Nat := ⟨fun _ => [[.plain number]], fun _ => [.plain string]⟩
def touching : Body Nat Nat := .effect (fun state world => (state, world + 1)) .done

private theorem number_accepted (state : Nat) :
    accepted [identityScheme, {identityScheme with occurrence := 1}] numberFields state = true := by
  apply (accepted_exact (σ := sig)
    [identityScheme, {identityScheme with occurrence := 1}] numberFields state).mpr
  have original := SchematicCallTyping.Controls.matching_polymorphic_call
  cases original with
  | call member witness inputs result =>
      simp only [List.mem_singleton] at member
      subst_vars
      exact .call (by simp) witness inputs result

private theorem conflict_refused (state : Nat) :
    accepted [identityScheme] conflictingFields state = false := by
  have notTyped := SchematicCallTyping.Controls.shared_result_rejects_conflict
  cases answer : accepted [identityScheme] conflictingFields state with
  | false => rfl
  | true => exact False.elim (notTyped ((accepted_exact (σ := sig)
      [identityScheme] conflictingFields state).mp answer))

theorem duplicate_witnesses_preserve_duplicate_program_occurrences :
    run (checked [identityScheme, {identityScheme with occurrence := 1}]
      numberFields (.choice touching touching)) 0 0 = ([0,0],2) := by
  simp [run, checked, andThen, Mettapedia.Machines.OrderedGuardPipeline.guard,
    checkingStates, number_accepted, touching, eval, collect, finish]

theorem rejected_result_retains_effect :
    run (checked [identityScheme] conflictingFields touching) 0 0 = ([],1) := by
  simp [run, checked, andThen, Mettapedia.Machines.OrderedGuardPipeline.guard,
    checkingStates, conflict_refused, touching, eval, collect, finish]

theorem moving_rejection_before_effect_is_observable :
    run (checked [identityScheme] conflictingFields touching) 0 0 ≠
      run (guard (checkingStates [identityScheme] conflictingFields) touching) 0 0 := by
  simp [run, checked, andThen, Mettapedia.Machines.OrderedGuardPipeline.guard,
    checkingStates, conflict_refused, touching, eval, collect, finish]

end Controls

#print axioms accepted_erases_boundary
#print axioms checked_eval
#print axioms rejection_keeps_prefix

end Mettapedia.Languages.MeTTa.PeTTa.JointCallExecution
