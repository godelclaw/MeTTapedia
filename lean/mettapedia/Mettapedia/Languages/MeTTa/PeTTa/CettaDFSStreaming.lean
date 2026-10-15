import Mettapedia.Languages.MeTTa.PeTTa.CettaDFSProducer
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Streaming source execution through labelled finite runs

The existing eager depth-first source machine instantiates the existing
productive-block run interface. A root answer is an ordered occurrence;
steps producing no root answer are silent to this observer. Output, input,
store, bindings, alternatives and caller frames remain in the saved source
configuration. Faults and malformed stopped configurations are handoffs
retaining that configuration, rather than successful exhaustion.

The adapter's readback is the actual source runner, and its event list is
exactly the extension of the source answer history. Budget splitting, prefix
growth and account splitting then use the generic labelled-run laws. No
global productivity rank, equivalence with the batch evaluator, native C
refinement or validity of a changed shared world is asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

abbrev Configuration := CettaEagerDFS.Configuration
abbrev Barrier := CettaDFSProducer.Barrier

/-- Classify actual source steps for the root-answer observer. Completion
inspection and handoff execute no extra source reduction. -/
def machine (program : Program) : Machine Configuration Atom Configuration Barrier where
  step configuration := some <|
    match CettaEagerDFS.step program configuration with
    | some next =>
        match CettaDFSProducer.emission configuration with
        | [] => .silent next
        | values => .publish values next
    | none =>
        if CettaEagerDFS.completed configuration then .finish configuration
        else match CettaEagerDFS.fault configuration with
          | some reason => .call (.fault reason) configuration
          | none => .call .stopped configuration

/-- Read back every retained or completed configuration. A generic faulted
outcome has no configuration; this adapter never produces that outcome. -/
def readback : Outcome Configuration Configuration Barrier → Option Configuration
  | .finished configuration | .stuck configuration | .exhausted configuration =>
      some configuration
  | .suspended _ configuration => some configuration
  | .faulted => none

/-- Readback of any finite labelled run is the independently executable
source runner, including its world and complete control state. -/
theorem run_readback (program : Program) (fuel : Nat) (source : Configuration) :
    readback ((machine program).run fuel source).2 =
      some (CettaEagerDFS.advance program fuel source) := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      cases stepped : CettaEagerDFS.step program source with
      | none =>
          by_cases finished : CettaEagerDFS.completed source = true
          · simp [Machine.run, machine, stepped, finished, readback, CettaEagerDFS.advance]
          · cases failed : CettaEagerDFS.fault source <;>
              simp [Machine.run, machine, stepped, finished, failed, readback,
                CettaEagerDFS.advance]
      | some next =>
          cases emitted : CettaDFSProducer.emission source with
          | nil =>
              simpa [Machine.run, machine, stepped, emitted, CettaEagerDFS.advance] using ih next
          | cons value rest =>
              simpa [Machine.run, machine, stepped, emitted, CettaEagerDFS.advance] using ih next

/-- The observed prefix is exactly the new source answer occurrences. Equal
values at different positions remain different list entries. -/
theorem run_answer_history (program : Program) (fuel : Nat) (source : Configuration)
    (valid : CettaEagerDFS.ScopesValid source.scopes) :
    CettaEagerDFS.answers (CettaEagerDFS.advance program fuel source) =
      CettaEagerDFS.answers source ++ ((machine program).run fuel source).1 := by
  induction fuel generalizing source with
  | zero => simp [CettaEagerDFS.advance, Machine.run]
  | succ fuel ih =>
      cases stepped : CettaEagerDFS.step program source with
      | none =>
          by_cases finished : CettaEagerDFS.completed source = true
          · simp [Machine.run, machine, stepped, finished, CettaEagerDFS.advance]
          · cases failed : CettaEagerDFS.fault source <;>
              simp [Machine.run, machine, stepped, finished, failed, CettaEagerDFS.advance]
      | some next =>
          have transition := CettaEagerDFS.step_transition stepped
          have retained := CettaEagerDFS.transition_scopes_valid transition valid
          have appended := CettaDFSProducer.transition_answers transition valid
          have later := ih next retained
          cases emitted : CettaDFSProducer.emission source with
          | nil =>
              simpa [Machine.run, machine, stepped, emitted, CettaEagerDFS.advance,
                appended] using later
          | cons value rest =>
              simpa [Machine.run, machine, stepped, emitted, CettaEagerDFS.advance,
                appended, List.append_assoc] using later

/-- Every bounded prefix has a genuine path in the independent source rules,
with at most one source transition per scheduler inspection. -/
theorem run_source (program : Program) (fuel : Nat) (source : Configuration)
    (valid : CettaEagerDFS.ScopesValid source.scopes) :
    ∃ target count, count ≤ fuel ∧
      readback ((machine program).run fuel source).2 = some target ∧
      CettaEagerDFS.SourceRun program count source target ∧
      CettaEagerDFS.ScopesValid target.scopes ∧
      CettaEagerDFS.answers target =
        CettaEagerDFS.answers source ++ ((machine program).run fuel source).1 := by
  obtain ⟨count, bound, path⟩ := CettaEagerDFS.advance_has_source_run program fuel source
  exact ⟨_, count, bound, run_readback program fuel source, path,
    CettaEagerDFS.advance_scopes_valid program fuel source valid,
    run_answer_history program fuel source valid⟩

/-- The owned producer log and the labelled run observe the same actual
source prefix. Capture and admission microsteps need not have the same count
as source transitions; the earned source path supplies the matching budget. -/
theorem producer_log_correspondence {Stored Context Output : Type} {clients : Nat}
    (program : Program) (capture : Atom → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (packet : CettaDFSProducer.Packet Stored Context Output clients)
    (execution : Mettapedia.Machines.Cursor.ProducerOccurrenceLog.Execution
      Configuration Atom Empty Barrier)
    (attached : packet.execution = some execution)
    (valid : CettaEagerDFS.ScopesValid execution.producer.scopes) :
    let result := Mettapedia.Machines.Cursor.ProducerOccurrenceLog.run
      (CettaDFSProducer.step program) capture capacity compatible ticks packet
    ∃ next sourceSteps, result.2.execution = some next ∧
      CettaEagerDFS.SourceRun program sourceSteps execution.producer next.producer ∧
      readback ((machine program).run sourceSteps execution.producer).2 = some next.producer ∧
      ((machine program).run sourceSteps execution.producer).1 =
        result.1.flatMap Mettapedia.Machines.Cursor.ProducerOccurrenceLog.returned := by
  dsimp only
  obtain ⟨next, count, retained, path, _, answers⟩ :=
    CettaDFSProducer.run_source capture capacity compatible ticks packet execution attached valid
  have advances := CettaEagerDFS.source_run_advances path
  have observed := run_answer_history program count execution.producer valid
  rw [advances] at observed
  refine ⟨next, count, retained, path, ?_, ?_⟩
  · rw [run_readback, advances]
  · exact List.append_cancel_left (observed.symm.trans answers)

/-- The generic resumption law applies to the actual streaming evaluator,
preserving established occurrences and the complete saved configuration. -/
theorem resume_after_prefix (program : Program) (first second : Nat)
    (source residual : Configuration) (events : List Atom)
    (paused : (machine program).run first source = (events, .exhausted residual)) :
    (machine program).run (first + second) source =
      (events ++ ((machine program).run second residual).1,
        ((machine program).run second residual).2) :=
  (machine program).established_and_pending first second source residual events paused

/-- Longer budgets extend the ordered answer prefix without revising a final
status. Changing the strategy or source is not covered by this law. -/
theorem observation_prefix (program : Program) (first second : Nat)
    (source : Configuration) :
    ((machine program).observe first source).Prefix
      ((machine program).observe (first + second) source) :=
  (machine program).observe_prefix first second source

/-- A supplied price account splits at the exact saved state. Its physical
meaning and bounds require separate implementation evidence. -/
theorem account_split (program : Program) (price : Configuration → Nat)
    (first second : Nat) (source : Configuration) :
    (machine program).spent price (first + second) source =
      (machine program).spent price first source +
        (machine program).spentAfter price second ((machine program).run first source).2 :=
  (machine program).spent_add price first second source

namespace Controls

open CettaDFSProducer.Controls (program ready a b printReady)

def firstAnswer : Configuration :=
  CettaEagerDFS.advance program 1 ready

theorem pause_after_one_answer :
    (machine program).run 1 ready = ([a], .exhausted firstAnswer) := rfl

theorem resume_keeps_both_remaining_occurrences :
    (machine program).run 2 firstAnswer =
      ([a, b], .exhausted (CettaEagerDFS.advance program 3 ready)) := rfl

theorem split_after_an_observed_answer :
    (machine program).run 3 ready =
      ([a] ++ ((machine program).run 2 firstAnswer).1,
        ((machine program).run 2 firstAnswer).2) :=
  resume_after_prefix program 1 2 ready firstAnswer [a] pause_after_one_answer

/-- Restarting the initial computation repeats the established occurrence. -/
theorem restarting_repeats_an_answer :
    [a] ++ ((machine program).run 3 ready).1 ≠ ((machine program).run 3 ready).1 := by
  decide

theorem performed_output_survives_pause :
    (CettaEagerDFS.advance program 1 printReady).world.output = [a] ∧
      ((machine program).run 1 printReady).1 = [] := ⟨rfl, rfl⟩

theorem resumption_does_not_repeat_output :
    (CettaEagerDFS.advance program 2
      (CettaEagerDFS.advance program 1 printReady)).world.output = [a] := rfl

theorem stopped_fault_is_not_completion (reason : Effects.Fault) :
    let source : Configuration :=
      ⟨ready.world, [{frontier := [⟨.fault reason, []⟩]}]⟩
    (machine program).run 1 source = ([], .suspended (.fault reason) source) := rfl

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming
