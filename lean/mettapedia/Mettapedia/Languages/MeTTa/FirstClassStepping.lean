import Mettapedia.Machines.FirstClassStepping
import Mettapedia.Languages.MeTTa.HE.RecursiveExecution
import Mettapedia.Languages.MeTTa.PeTTa.Resumption
import Mettapedia.GSLT.Meredith.GSLT

/-!
# Retained stepping for the maintained HE and PeTTa source machines

HE uses the resource-checked recursive worker and its existing ordered evaluator
correspondence. Its publication boundaries are returned answer occurrences;
resource requests retain their complete pending task and continuation. This is
the read-only recursive profile, not an arbitrary mutable-world HE scheduler.

PeTTa uses its actual configuration transition function and independent source
judgments. Fork and prepared primitive-call boundaries are explicit observations;
all other control transitions are silent. Completion retains the full final
configuration; primitive faults retain their actual receiver as refusals. Ordered
answers, store, input and performed output remain source observations. This is
the existing closed, saturated profile, not the whole upstream dialect.

These adapters choose observation boundaries; they do not identify native ticks,
coarse atom rewriting, or the two dialects' evaluation strategies. Open source
descriptions do not mint native execution authority, and no arbitrary-schedule
effect equivalence or automatic authority serialization is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.FirstClassStepping

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

open Mettapedia.Machines.FirstClassStepping

namespace HEProfile

open HE HE.RecursiveTasks HE.RecursiveMachine

def recorded (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (fuel requests : Nat) : Delivery Configuration ResultPair Configuration Checked.ResourceRequest :=
  record (Checked.machine dispatch) fuel requests (.ready (Configuration.initial space task))

/-- Completed stepping returns the entire original ordered evaluator list,
including repeated occurrences and the actual retained final receiver. -/
theorem completed_results (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (fuel requests : Nat) (final : Configuration)
    (completed : (recorded space dispatch task fuel requests).checkpoint = .done final) :
    (recorded space dispatch task fuel requests).events = task.denote space dispatch ∧
      final.emitted = (recorded space dispatch task fuel requests).events ∧ final.space = space := by
  have observedRun := record_prefix (Checked.machine dispatch) fuel requests
    (.ready (Configuration.initial space task))
  change (recorded space dispatch task fuel requests).checkpoint = .done final at completed
  change (Checked.machine dispatch).continueRun (recorded space dispatch task fuel requests).used
    ([], Checkpoint.outcome (.ready (Configuration.initial space task))) =
      ((recorded space dispatch task fuel requests).events,
        (recorded space dispatch task fuel requests).checkpoint.outcome) at observedRun
  rw [completed] at observedRun
  have executed : (Checked.machine dispatch).run (recorded space dispatch task fuel requests).used
      (Configuration.initial space task) = ((recorded space dispatch task fuel requests).events,
        .finished final) := by simpa [Machine.continueRun, Checkpoint.outcome] using observedRun
  exact HE.RecursiveExecution.finished_results space dispatch task _ _ final
    (Checked.finished_refines dispatch _ _ _ _ executed)

theorem unrecorded_completion_retains_results (space : Space) (dispatch : GroundedDispatch)
    (task : Task) (capability : Capability (Checked.machine dispatch)
      (Configuration.initial space task)) (final : Configuration)
    (completed : capability.checkpoint = .done final) :
    final.emitted = task.denote space dispatch ∧ final.space = space := by
  obtain ⟨fuel, events, ran⟩ := capability.reached
  rw [completed] at ran
  obtain ⟨same, retained, world⟩ := HE.RecursiveExecution.finished_results space dispatch task
    fuel events final (Checked.finished_refines dispatch _ _ _ _ ran)
  exact ⟨retained.trans same, world⟩

namespace Controls

def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def terminal : Configuration :=
  ⟨Space.empty, .returning [(a, Bindings.empty), (a, Bindings.empty), (b, Bindings.empty)], [], []⟩

theorem equal_answers_remain_separate_and_ordered :
    (record (Checked.machine GroundedDispatch.none) 8 4 (.ready terminal)).events =
      [(a, Bindings.empty), (a, Bindings.empty), (b, Bindings.empty)] := by decide +kernel

theorem one_boundary_keeps_the_other_occurrences :
    (advance (Checked.machine GroundedDispatch.none) 8 (.ready terminal)).events =
      [(a, Bindings.empty)] ∧
      (advance (Checked.machine GroundedDispatch.none) 8 (.ready terminal)).checkpoint =
        .ready ⟨Space.empty, .returning [(a, Bindings.empty), (b, Bindings.empty)], [], [(a, Bindings.empty)]⟩ := by
  decide +kernel

def blocked : Configuration := Configuration.initial Space.empty (.atom a Atom.atomType Bindings.empty 0 [])

theorem exhausted_evaluator_depth_is_blocked :
    (drive (Checked.machine GroundedDispatch.none) 8 3 (.ready blocked)) =
      .blocked .evaluationDepth blocked := by decide +kernel

theorem blocked_is_not_done :
    (drive (Checked.machine GroundedDispatch.none) 8 3 (.ready blocked)).is_done = false := by decide +kernel

theorem scheduler_pause_is_not_done :
    (advance (Checked.machine GroundedDispatch.none) 0 (.ready terminal)).checkpoint.is_done = false := by
  decide +kernel

def invocation : Atom := .expression [.symbol "f", a]

theorem protocol_reply_restores_the_original_invocation :
    (recorded Space.empty GroundedDispatch.none
      (.returned invocation Atom.notReducible Atom.undefinedType Bindings.empty 1 []) 8 3).events =
        [(invocation, Bindings.empty)] := by decide +kernel

end Controls
end HEProfile

namespace PeTTaProfile

open PeTTa PeTTa.Eval

inductive Terminal where
  | complete
  | fault (reason : Effects.Fault)

def terminal (configuration : Configuration) : Option Terminal :=
  match configuration.control, configuration.frames with
  | .returned _, [] => some .complete
  | .fault reason, _ => some (.fault reason)
  | _, _ => none

inductive Event where
  | fork (alternatives : List Atom)
  | primitive (name : String) (arguments : List Atom)
  deriving DecidableEq

def observations (configuration : Configuration) : List Event :=
  match configuration.control with
  | .evaluate _ (.expression [.symbol "superpose", .expression alternatives]) => [.fork alternatives]
  | .arguments _ (.function head) [] values _ =>
      if ioHead head || StdLib.known head then [.primitive head values] else []
  | _ => []

def machine (program : SpaceSemantics.Program) : Machine Configuration Event Configuration Empty where
  step configuration :=
    match terminal configuration with
    | some .complete => some (.finish configuration)
    | some (.fault _) => some (.fail [])
    | none =>
        match Eval.step program configuration with
        | none => none
        | some next =>
            let events := observations configuration
            if events.isEmpty then some (.silent next) else some (.publish events next)

theorem complete_terminal_exact (configuration : Configuration) :
    terminal configuration = some .complete ↔
      ∃ answers, configuration.control = .returned answers ∧ configuration.frames = [] := by
  rcases configuration with ⟨state, control, frames, input, output⟩
  cases control <;> cases frames <;> simp [terminal]

theorem fault_terminal_exact (configuration : Configuration) (reason : Effects.Fault) :
    terminal configuration = some (.fault reason) ↔ configuration.control = .fault reason := by
  rcases configuration with ⟨state, control, frames, input, output⟩
  cases control <;> cases frames <;> simp [terminal]

/-- Actual continuing transitions are exactly the maintained source step.
No equality of raw step counts is assumed or needed. -/
theorem progress_exact (program : SpaceSemantics.Program) (before after : Configuration) :
    Progress (machine program) before after ↔
      terminal before = none ∧ Eval.step program before = some after := by
  cases stopped : terminal before with
  | some value => cases value <;> simp [Progress, machine, stopped]
  | none =>
      cases moved : Eval.step program before with
      | none => simp [Progress, machine, stopped, moved]
      | some next =>
          by_cases empty : observations before = [] <;>
            simp [Progress, machine, stopped, moved, empty]

theorem finish_exact (program : SpaceSemantics.Program) (before final : Configuration) :
    (machine program).step before = some (.finish final) ↔
      terminal before = some .complete ∧ before = final := by
  cases stopped : terminal before with
  | some value => cases value <;> simp [machine, stopped]
  | none =>
      cases moved : Eval.step program before <;>
        simp [machine, stopped, moved]
      split <;> simp

theorem refusal_exact (program : SpaceSemantics.Program) (before : Configuration) (events : List Event) :
    (machine program).step before = some (.fail events) ↔
      (∃ reason, terminal before = some (.fault reason)) ∧ events = [] := by
  cases stopped : terminal before with
  | some value => cases value <;> simp [machine, stopped]
  | none =>
      cases moved : Eval.step program before <;> simp [machine, stopped, moved]
      split <;> simp

theorem source_path (program : SpaceSemantics.Program) (initial final : Configuration)
    (path : Relation.ReflTransGen (Progress (machine program)) initial final) :
    (Eval.theory program).MultiStep initial final := by
  induction path with
  | refl => exact .refl _
  | tail _ moved earlier =>
      exact Mettapedia.GSLT.Meredith.multiStep_trans _ earlier
        (.step (Eval.step_transition ((progress_exact program _ _).mp moved).2) (.refl _))

private theorem prepend_source_path (program : SpaceSemantics.Program) (initial final : Configuration)
    (outcome : Eval.Outcome) (path : Relation.ReflTransGen (Progress (machine program)) initial final)
    (completed : DeclarativeSpec.Runs program final outcome) :
    DeclarativeSpec.Runs program initial outcome := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact completed
  | head moved _ earlier =>
      exact .next (Eval.step_transition ((progress_exact program _ _).mp moved).2) earlier

theorem capability_done_original (program : SpaceSemantics.Program) (initial : Configuration)
    (capability : Capability (machine program) initial) (final : Configuration)
    (completed : capability.checkpoint = .done final) :
    ∃ answers, final.control = .returned answers ∧ final.frames = [] ∧
      DeclarativeSpec.Runs program initial
        (.complete final.state answers final.input final.output) := by
  have valid := capability.valid
  rw [completed] at valid
  obtain ⟨receiver, path, finished⟩ := valid
  obtain ⟨stopped, same⟩ := (finish_exact program receiver final).mp finished
  subst receiver
  obtain ⟨answers, control, frames⟩ := (complete_terminal_exact final).mp stopped
  exact ⟨answers, control, frames, prepend_source_path program initial final _
    path (.completed control frames)⟩

theorem capability_refused_original (program : SpaceSemantics.Program) (initial : Configuration)
    (capability : Capability (machine program) initial) (receiver : Configuration)
    (refused : capability.checkpoint = .refused receiver) :
    ∃ reason, receiver.control = .fault reason ∧
      DeclarativeSpec.Runs program initial (.fault reason receiver) := by
  have valid := capability.valid
  rw [refused] at valid
  obtain ⟨path, events, failed⟩ := valid
  obtain ⟨⟨reason, stopped⟩, _empty⟩ := (refusal_exact program receiver events).mp failed
  have control := (fault_terminal_exact receiver reason).mp stopped
  exact ⟨reason, control, prepend_source_path program initial receiver _
    path (.fault control)⟩

def sourceObservation : Checkpoint Configuration Configuration Empty → Option Eval.Outcome
  | .done final => match final.control with
      | .returned answers => some (.complete final.state answers final.input final.output)
      | _ => none
  | .refused receiver => match receiver.control with
      | .fault reason => some (.fault reason receiver)
      | _ => none
  | _ => none

private theorem source_step_is_nonterminal (program : SpaceSemantics.Program)
    (before after : Configuration) (moved : Eval.step program before = some after) : terminal before = none := by
  rcases before with ⟨state, control, frames, input, output⟩
  cases control <;> cases frames <;> first | rfl | simp [Eval.step] at moved

private theorem source_step_advances_once (program : SpaceSemantics.Program)
    (before after : Configuration) (moved : Eval.step program before = some after) :
    (advance (machine program) 1 (.ready before)).checkpoint = .ready after := by
  have active := source_step_is_nonterminal program before after moved
  by_cases empty : observations before = [] <;>
    simp [advance, machine, active, moved, empty]

/-- Every independent finite source derivation is reached by actual reference
advancement. Primitive faults and completed answers use different checkpoints. -/
theorem original_runs_realized (program : SpaceSemantics.Program) (initial : Configuration)
    (outcome : Eval.Outcome) (derived : DeclarativeSpec.Runs program initial outcome) :
    ∃ requests, sourceObservation (drive (machine program) 1 requests (.ready initial)) = some outcome := by
  induction derived with
  | completed control frames =>
      have stopped := (complete_terminal_exact _).mpr ⟨_, control, frames⟩
      exact ⟨1, by simp [drive, advance, machine, stopped, sourceObservation, control]⟩
  | fault control =>
      have stopped := (fault_terminal_exact _ _).mpr control
      exact ⟨1, by simp [drive, advance, machine, stopped, sourceObservation, control]⟩
  | next transition _ earlier =>
      obtain ⟨requests, realized⟩ := earlier
      exact ⟨requests + 1, by
        simpa only [drive, source_step_advances_once program _ _ (Eval.transition_step transition)] using realized⟩

theorem capability_observation_original (program : SpaceSemantics.Program) (initial : Configuration)
    (capability : Capability (machine program) initial) (outcome : Eval.Outcome)
    (observed : sourceObservation capability.checkpoint = some outcome) :
    DeclarativeSpec.Runs program initial outcome := by
  cases kept : capability.checkpoint with
  | ready _ | stuck _ => simp [sourceObservation, kept] at observed
  | blocked impossible _ => exact impossible.elim
  | done final =>
      obtain ⟨answers, control, _frames, derived⟩ := capability_done_original program initial capability final kept
      have same : Eval.Outcome.complete final.state answers final.input final.output = outcome := by
        simpa [sourceObservation, kept, control] using observed
      exact same ▸ derived
  | refused receiver =>
      obtain ⟨reason, control, derived⟩ := capability_refused_original program initial capability receiver kept
      have same : Eval.Outcome.fault reason receiver = outcome := by
        simpa [sourceObservation, kept, control] using observed
      exact same ▸ derived

/-- Preservation and reflection against the original whole-program judgment,
with literal state, answer list, input, output and fault receiver observations. -/
theorem original_runs_iff_retained_observation (program : SpaceSemantics.Program)
    (initial : Configuration) (outcome : Eval.Outcome) :
    DeclarativeSpec.Runs program initial outcome ↔
      ∃ requests, sourceObservation
        (((Capability.begin (machine program) initial).resume 1 requests).checkpoint) = some outcome := by
  constructor
  · intro derived
    obtain ⟨requests, realized⟩ := original_runs_realized program initial outcome derived
    exact ⟨requests, realized⟩
  · rintro ⟨requests, observed⟩
    exact capability_observation_original program initial _ outcome observed

/-- Fork observation retains every written alternative; it does not choose one
branch and discard the rest. Continuation and captured bindings stay source data. -/
theorem fork_keeps_all_alternatives (program : SpaceSemantics.Program)
    (state : Effects.State) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (alternatives : List Atom)
    (frames : List Frame) (input output : List Atom) :
    (machine program).step { state := state, control := (.evaluate bindings
      (.expression [.symbol "superpose", .expression alternatives])), frames := frames, input := input, output := output } =
      some (.publish [.fork alternatives]
        { state, control := .sequence (alternatives.map (.evaluate bindings)) [], frames, input, output }) := by
  simp [machine, terminal, observations, Eval.step]

namespace Controls

def program : SpaceSemantics.Program := { equations := [], declarations := [] }
def seven : Atom := .grounded (.int 7)
def message : Atom := .grounded (.string "once")
def repeated : Atom := .expression [.symbol "let", .var "held", seven,
  .expression [.symbol "superpose", .expression [.var "held", .var "held"]]]

def readout : Checkpoint Configuration Configuration Empty → Option (List Atom × List Atom)
  | .done final => match final.control with
      | .returned answers => some (answers, final.output)
      | _ => none
  | _ => none

theorem captured_bindings_and_duplicate_answers_survive :
    readout (drive (machine program) 2 30 (.ready (Eval.start Effects.empty repeated))) =
      some ([seven, seven], []) := by decide +kernel

def printing : Configuration :=
  { state := Effects.empty, control := .arguments [] (.function "println!") [] [message] 1,
    frames := [.collect] }
def printed : Configuration :=
  { state := Effects.empty, control := .returned [Effects.boolean true], frames := [.collect], output := [message] }

theorem step_retains_performed_output_and_continuation :
    (advance (machine program) 8 (.ready printing)).checkpoint = .ready printed := rfl

theorem resume_does_not_repeat_the_output :
    readout (drive (machine program) 8 3 (.ready printed)) =
      some ([.expression [Effects.boolean true]], [message]) := by decide +kernel

def describe : Checkpoint Configuration Configuration Empty → Description (Nat × Nat) Nat Nat :=
  inspect (fun configuration => (configuration.frames.length, configuration.input.length))
    (fun configuration => configuration.output.length) Empty.elim

/-- This chosen open view omits performed output. Equal descriptions therefore
cannot authorize reconstructing an interchangeable executable receiver. -/
theorem equal_open_views_can_hide_different_effect_histories :
    describe (.ready printed) = describe (.ready { printed with output := [] }) ∧
      readout (drive (machine program) 8 3 (.ready printed)) ≠
        readout (drive (machine program) 8 3 (.ready { printed with output := [] })) := by decide +kernel

def printTwice : Atom := .expression [.symbol "superpose", .expression
  [.expression [.symbol "println!", message], .expression [.symbol "println!", message]]]

theorem equal_branches_perform_two_output_occurrences :
    readout (drive (machine program) 2 40 (.ready (Eval.start Effects.empty printTwice))) =
      some ([Effects.boolean true, Effects.boolean true], [message, message]) := by decide +kernel

def laterMessage : Atom := .grounded (.string "later")
def printInOrder (first second : Atom) : Atom := .expression [.symbol "superpose", .expression
  [.expression [.symbol "println!", first], .expression [.symbol "println!", second]]]

/-- Identical answer lists do not license permuting effectful branches. -/
theorem branch_order_can_change_the_required_effect_observation :
    readout (drive (machine program) 2 40
      (.ready (Eval.start Effects.empty (printInOrder message laterMessage)))) =
        some ([Effects.boolean true, Effects.boolean true], [message, laterMessage]) ∧
      readout (drive (machine program) 2 40
        (.ready (Eval.start Effects.empty (printInOrder laterMessage message)))) =
          some ([Effects.boolean true, Effects.boolean true], [laterMessage, message]) ∧
      [message, laterMessage] ≠ [laterMessage, message] := by decide +kernel

theorem empty_completion_is_done :
    readout (drive (machine program) 8 3
      (.ready (Eval.start Effects.empty (.expression [.symbol "empty"])))) = some ([], []) ∧
      (drive (machine program) 8 3
        (.ready (Eval.start Effects.empty (.expression [.symbol "empty"])))).is_done = true := by
  decide +kernel

def badPrint : Configuration :=
  { state := Effects.empty, control := .arguments [] (.function "println!") [] [] 0 }

theorem primitive_fault_is_refused_and_not_done :
    (drive (machine program) 8 3 (.ready badPrint)).phase = .refused ∧
      (drive (machine program) 8 3 (.ready badPrint)).is_done = false := by decide +kernel

theorem exhausted_scheduler_budget_is_running :
    (drive (machine program) 0 3 (.ready printing)).phase = .running := by decide +kernel

theorem resumption_preserves_the_complete_receiver :
    drive (machine program) 2 20
      (drive (machine program) 2 1 (.ready (Eval.start Effects.empty repeated))) =
        drive (machine program) 2 21 (.ready (Eval.start Effects.empty repeated)) :=
  (drive_add _ _ _ _ _).symm

end Controls
end PeTTaProfile

#print axioms HEProfile.completed_results
#print axioms HEProfile.unrecorded_completion_retains_results
#print axioms HEProfile.Controls.equal_answers_remain_separate_and_ordered
#print axioms HEProfile.Controls.protocol_reply_restores_the_original_invocation
#print axioms PeTTaProfile.progress_exact
#print axioms PeTTaProfile.finish_exact
#print axioms PeTTaProfile.refusal_exact
#print axioms PeTTaProfile.source_path
#print axioms PeTTaProfile.capability_done_original
#print axioms PeTTaProfile.capability_refused_original
#print axioms PeTTaProfile.original_runs_realized
#print axioms PeTTaProfile.capability_observation_original
#print axioms PeTTaProfile.original_runs_iff_retained_observation
#print axioms PeTTaProfile.fork_keeps_all_alternatives
#print axioms PeTTaProfile.Controls.captured_bindings_and_duplicate_answers_survive
#print axioms PeTTaProfile.Controls.equal_branches_perform_two_output_occurrences
#print axioms PeTTaProfile.Controls.equal_open_views_can_hide_different_effect_histories
#print axioms PeTTaProfile.Controls.branch_order_can_change_the_required_effect_observation

end Mettapedia.Languages.MeTTa.FirstClassStepping
