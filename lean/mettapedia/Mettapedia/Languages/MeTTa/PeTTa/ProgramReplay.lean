import Mettapedia.Languages.MeTTa.PeTTa.Resumption

/-!
# Complete configurations for finite program replay

The replay observer advances only through the existing executable `Eval.step`.
Its zero-fuel readout is proved equal to the existing `Eval.run`, and arbitrary
fuel chunks preserve the entire reached configuration. Retaining a configuration
also keeps already performed output when the ordinary fault outcome omits it.
The independent declarative transition graph certifies every observer step.

The read-only source profile excludes dynamic evaluation and mutable primitive
operations. Its complete store remains the loaded program store, so the empty
cell support and finite space prefix reconstruct every function-valued field.
This is an executable-model bridge, not a native parser or C refinement theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Eval

/-- Retain the actual configuration reached after at most the supplied number
of existing machine transitions. A terminal configuration has no next step. -/
def advance (program : Program) : Nat → Configuration → Configuration
  | 0, configuration => configuration
  | fuel + 1, configuration =>
      match step program configuration with
      | none => configuration
      | some next => advance program fuel next

theorem advance_stopped (program : Program) (fuel : Nat) (configuration : Configuration)
    (stopped : step program configuration = none) :
    advance program fuel configuration = configuration := by
  cases fuel <;> simp [advance, stopped]

/-- The observer does not replace the evaluator: its readout agrees with the
actual fuel runner for completion, exhaustion and primitive faults. -/
theorem run_advance (program : Program) (fuel : Nat) (configuration : Configuration) :
    run program 0 (advance program fuel configuration) = run program fuel configuration := by
  induction fuel generalizing configuration with
  | zero => rfl
  | succ fuel ih =>
      cases next : step program configuration with
      | some target =>
          simp only [advance, next]
          exact (ih target).trans (run_succ_of_step program fuel configuration target next).symm
      | none =>
          simp only [advance, next]
          cases configuration with
          | mk state control frames input output =>
              cases control <;> cases frames <;> simp_all [run]

theorem advance_split (program : Program) (first second : Nat) (configuration : Configuration) :
    advance program second (advance program first configuration) =
      advance program (first + second) configuration := by
  induction first generalizing configuration with
  | zero => simp [advance]
  | succ first ih =>
      cases next : step program configuration with
      | none =>
          rw [advance_stopped program (first + 1) configuration next,
            advance_stopped program second configuration next,
            advance_stopped program (first + 1 + second) configuration next]
      | some target => simpa [advance, next, Nat.succ_add] using ih target

def checkpoints (program : Program) : List Nat → Configuration → List Configuration
  | [], _ => []
  | fuel :: rest, configuration =>
      let reached := advance program fuel configuration
      reached :: checkpoints program rest reached

def chunks (program : Program) : List Nat → Configuration → Configuration
  | [], configuration => configuration
  | fuel :: rest, configuration => chunks program rest (advance program fuel configuration)

theorem chunks_eq_advance_sum (program : Program) (fuels : List Nat) (configuration : Configuration) :
    chunks program fuels configuration = advance program fuels.sum configuration := by
  induction fuels generalizing configuration with
  | nil => rfl
  | cons fuel rest ih =>
      rw [chunks, ih, advance_split]
      rfl

def resumeChunks (program : Program) : List Nat → Outcome → Outcome
  | [], outcome => outcome
  | fuel :: rest, outcome => resumeChunks program rest (resume program fuel outcome)

theorem resumeChunks_run (program : Program) (fuels : List Nat) (paid : Nat)
    (configuration : Configuration) :
    resumeChunks program fuels (run program paid configuration) =
      run program (paid + fuels.sum) configuration := by
  induction fuels generalizing paid with
  | nil => simp [resumeChunks]
  | cons fuel rest ih =>
      rw [resumeChunks, resume_run, ih]
      simp [Nat.add_assoc]

theorem chunks_readout (program : Program) (fuels : List Nat) (configuration : Configuration) :
    run program 0 (chunks program fuels configuration) =
      resumeChunks program fuels (run program 0 configuration) := by
  rw [chunks_eq_advance_sum, run_advance, resumeChunks_run, Nat.zero_add]

theorem advance_path (program : Program) (fuel : Nat) (configuration : Configuration) :
    (theory program).MultiStep configuration (advance program fuel configuration) := by
  induction fuel generalizing configuration with
  | zero => exact .refl _
  | succ fuel ih =>
      cases next : step program configuration with
      | none =>
          simp only [advance, next]
          exact .refl _
      | some target =>
          exact .step (step_transition next) (by simpa [advance, next] using ih target)

/-- Only the four state-mutating primitives can alter the loaded store.
Dynamic source execution and parsing are also excluded from this profile. -/
def readOnlyHead (head : String) : Bool :=
  !(head ∈ ["new-space", "add-atom", "remove-atom", "change-state!", "eval", "parse", "readln!"])

theorem primitive_preserves_state {state after : Effects.State} {head : String}
    {arguments answers : List Atom} (allowed : readOnlyHead head = true)
    (returned : StdLib.apply state head arguments = .ok (after, answers)) : after = state := by
  have notNew : head ≠ "new-space" := by
    intro same
    have forbidden : readOnlyHead head = false := by rw [same]; decide
    exact Bool.noConfusion (allowed.symm.trans forbidden)
  have notAdd : head ≠ "add-atom" := by
    intro same
    have forbidden : readOnlyHead head = false := by rw [same]; decide
    exact Bool.noConfusion (allowed.symm.trans forbidden)
  have notRemove : head ≠ "remove-atom" := by
    intro same
    have forbidden : readOnlyHead head = false := by rw [same]; decide
    exact Bool.noConfusion (allowed.symm.trans forbidden)
  have notChange : head ≠ "change-state!" := by
    intro same
    have forbidden : readOnlyHead head = false := by rw [same]; decide
    exact Bool.noConfusion (allowed.symm.trans forbidden)
  exact StdLib.successful_apply_state notNew notAdd notRemove notChange returned

def readOnlyProgram (program : Program) : Bool :=
  program.equations.all (fun equation => codeWithin readOnlyHead equation.body)

theorem checked_program_closed (program : Program) (checked : readOnlyProgram program = true) :
    ProgramClosed readOnlyHead program := by
  constructor
  · decide
  · intro equation member _
    exact List.all_eq_true.mp checked equation member

theorem transition_preserves_state {program : Program} {source target : Configuration}
    (within : configurationWithin readOnlyHead source)
    (transition : DeclarativeSpec.Transition program source target) :
    target.state = source.state := by
  cases transition
  all_goals try rfl
  rename_i bindings head index values after answers control _ _ returned
  have allowed := within.1
  rw [control] at allowed
  simp only [controlWithin, targetWithin, atomsWithin, Bool.and_true,
    Bool.and_eq_true] at allowed
  exact primitive_preserves_state allowed.1 returned

theorem advance_preserves_state (program : Program) (fuel : Nat) (source : Configuration)
    (closed : ProgramClosed readOnlyHead program)
    (within : configurationWithin readOnlyHead source) :
    (advance program fuel source).state = source.state := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      cases next : step program source with
      | none => simp [advance, next]
      | some target =>
          have transition := step_transition next
          simpa only [advance, next] using
            (ih target (transition_within closed transition within)).trans
              (transition_preserves_state within transition)

theorem chunks_preserve_state (program : Program) (fuels : List Nat) (source : Configuration)
    (closed : ProgramClosed readOnlyHead program)
    (within : configurationWithin readOnlyHead source) :
    (chunks program fuels source).state = source.state := by
  rw [chunks_eq_advance_sum]
  exact advance_preserves_state program fuels.sum source closed within

/-- Finite readout reconstructs all store fields, including the entire
unallocated private-space tail and every absent named cell. -/
theorem loaded_store_reconstruction (program : Program) :
    NamedSpaces.Store.reconstruct (Effects.loaded program).core []
      (Effects.loaded program).spacesPrefix ((Effects.loaded program).cellRows []) =
      Effects.loaded program := by
  apply NamedSpaces.Store.reconstruct_exact
  · exact Effects.loaded_empty_tail program
  · intro _ _
    rfl

theorem chunks_loaded_store_reconstruction (program : Program) (fuels : List Nat)
    (expression : Atom) (input : List Atom)
    (checked : readOnlyProgram program = true)
    (code : codeWithin readOnlyHead expression = true) :
    let initial : Configuration :=
      { state := Effects.loaded program
        control := .evaluate [] expression
        input }
    let reached := chunks program fuels initial
    NamedSpaces.Store.reconstruct reached.state.core [] reached.state.spacesPrefix
      (reached.state.cellRows []) = reached.state := by
  dsimp only
  have same := chunks_preserve_state program fuels
    { state := Effects.loaded program, control := .evaluate [] expression, input }
    (checked_program_closed program checked) ⟨code, rfl⟩
  rw [same]
  exact loaded_store_reconstruction program

namespace Examples

def program : Program :=
  { equations := [{ head := "dup", arguments := [.var "x"], body := .var "x" },
                  { head := "dup", arguments := [.var "x"], body := .var "x" }]
    declarations := []
    layout := [.equation, .equation] }

def seven : Atom := .grounded (.int 7)

def call : Atom := .expression [.symbol "dup", seven]

def answerView : Outcome → Option (List Atom)
  | .complete _ answers _ _ => some answers
  | _ => none

def faultView : Outcome → Option Effects.Fault
  | .fault reason _ => some reason
  | _ => none

theorem authored_equation_atoms_retained :
    SpaceSemantics.loadedAtoms program =
      [.expression [.symbol "=", .expression [.symbol "dup", .var "x"], .var "x"],
       .expression [.symbol "=", .expression [.symbol "dup", .var "x"], .var "x"]] := by
  rfl

theorem authored_program_admitted : readOnlyProgram program = true := by decide

theorem duplicate_answers_retained :
    answerView (run program 15 (start (Effects.loaded program) call)) =
      some [seven, seven] := by
  rw [← run_advance]
  with_unfolding_all rfl

def correlated : Atom := .expression
  [.symbol "let", .var "held", seven,
   .expression [.symbol "superpose", .expression [.var "held", .var "held"]]]

theorem binding_frame_retained :
    (advance program 2 (start (Effects.loaded program) correlated)).frames =
      [.bind [] (.var "held")
        (.expression [.symbol "superpose", .expression [.var "held", .var "held"]])] := by rfl

theorem correlated_answers_after_chunks :
    answerView (run program 0 (chunks program [0, 2, 12] (start (Effects.loaded program) correlated))) =
      some [seven, seven] := by decide +kernel

def message : Atom := .grounded (.string "once")

def effectThenFault : Atom := .expression
  [.symbol "let", .var "ignored", .expression [.symbol "println!", message],
   .expression [.symbol "%", seven, .grounded (.int 0)]]

theorem output_before_pause :
    (advance program 7 (start (Effects.loaded program) effectThenFault)).output = [message] := by rfl

theorem output_before_fault_retained :
    (chunks program [7, 10] (start (Effects.loaded program) effectThenFault)).output = [message] := by
  decide +kernel

theorem terminal_fault_distinct_from_exhaustion :
    faultView (run program 0 (chunks program [7, 14] (start (Effects.loaded program) effectThenFault))) =
      some .zeroDivisor := by with_unfolding_all rfl

theorem erasing_performed_output_changes_configuration :
    (advance program 7 (start (Effects.loaded program) effectThenFault)).output ≠ [] := by
  decide +kernel

def batching : Configuration :=
  { state := Effects.loaded program
    control := .sequence
      [.arguments [] (.function "println!") [] [.symbol "a"] 1,
       .arguments [] (.function "println!") [] [.symbol "b"] 1] []
    frames := [.bind [] (.var "held") (.expression [.symbol "println!", .var "held"])] }

/-- The existing list-valued machine completes inner alternatives before the
binding continuation executes. The native source oracle tests that boundary. -/
theorem sequence_delays_binding_continuation :
    (advance program 5 batching).output = [.symbol "a", .symbol "b"] := by rfl

theorem sequence_prefix_is_not_interleaved :
    (advance program 5 batching).output ≠ [.symbol "a", Effects.boolean true] := by
  decide +kernel

theorem mutable_heads_refused :
    readOnlyHead "new-space" = false ∧ readOnlyHead "add-atom" = false ∧
      readOnlyHead "remove-atom" = false ∧ readOnlyHead "change-state!" = false := by decide

theorem dynamic_heads_refused :
    readOnlyHead "eval" = false ∧ readOnlyHead "parse" = false ∧ readOnlyHead "readln!" = false := by
  decide

end Examples

end Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay
