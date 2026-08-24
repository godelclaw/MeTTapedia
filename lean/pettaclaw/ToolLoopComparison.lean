import CodingAgent
import FeedbackSensitiveBatch

/-!
# Tool-loop comparison: static batches and brokered feedback

This file connects the feedback-sensitive batching boundary to the policy
presets used by PettaClaw, and records two further failure witnesses from the
deployed runtime shape.

The brokered evidence barrier is the sequential quotient shared by the local
Codex and OpenCode implementations inspected for this model: calls are recorded,
tool results are recorded, and another model decision follows a result boundary.
Both implementations may execute independent calls concurrently; no theorem
here claims that concurrency itself is safe, or that either source tree conforms
to this model without a separate executable correspondence check.
-/

namespace PettaClaw.ToolLoopComparison

open PettaClaw.FeedbackSensitiveBatch

/-! ## A permissive, stimulus-guarded execution policy -/

inductive Mode where
  | agent
  | iter
  | coding
  | iterCoding
deriving Repr, DecidableEq

/-- Every mode retains the existing five-command envelope. The model chooses a
short or long batch; mode selection does not force stepwise execution. -/
def batchLimit : Mode → Nat
  | _ => 5

def admitBatch {Command : Type*} (mode : Mode) (commands : List Command) :
    List Command :=
  commands.take (batchLimit mode)

theorem every_mode_retains_five_commands {Command : Type*}
    (mode : Mode)
    (first second third fourth fifth : Command) (rest : List Command) :
    admitBatch mode
      ([first, second, third, fourth, fifth] ++ rest) =
      [first, second, third, fourth, fifth] := by
  cases mode <;> simp [admitBatch, batchLimit]

/-- The revision witnessed immediately before each command. Execution stops at
the first revision which differs from the context frontier captured for the
model turn. -/
def runUnlessStimulus {Command : Type*} (captured : Nat) :
    List (Nat × Command) → List Command
  | [] => []
  | (live, command) :: rest =>
      if live = captured then
        command :: runUnlessStimulus captured rest
      else
        []

/-- With no new stimulus the guard preserves the whole chosen batch. -/
theorem stable_frontier_executes_full_batch {Command : Type*}
    (captured : Nat) (commands : List Command) :
    runUnlessStimulus captured
      (commands.map (fun command => (captured, command))) = commands := by
  induction commands with
  | nil => rfl
  | cons command rest ih => simp [runUnlessStimulus, ih]

/-- A changed frontier withholds exactly the suffix which has not yet run. -/
theorem changed_frontier_withholds_unexecuted_suffix {Command : Type*}
    (captured changed : Nat) (different : changed ≠ captured)
    (executed : List Command) (next : Command)
    (suffix : List (Nat × Command)) :
    runUnlessStimulus captured
      (executed.map (fun command => (captured, command)) ++
        (changed, next) :: suffix) = executed := by
  induction executed with
  | nil => simp [runUnlessStimulus, different]
  | cons command rest ih => simp [runUnlessStimulus, ih]

/-- The guarded policy is strictly less restrictive than a universal
one-command cap on a stable two-command trace. -/
theorem stable_guard_preserves_a_batch_rejected_by_hard_single_step
    {Command : Type*} (first second : Command) :
    runUnlessStimulus 7 [(7, first), (7, second)] = [first, second] ∧
      [first, second].take 1 = [first] := by
  simp [runUnlessStimulus]

/-- Cooperative interruption occurs only between effects. A stimulus arriving
inside a non-preemptible command cannot be acted on before that command ends. -/
def earliestNextGuard (started duration : Nat) : Nat :=
  started + duration

theorem nonpreemptible_command_imposes_reaction_latency
    (started duration stimulus : Nat)
    (_arrivedAfterStart : started < stimulus)
    (arrivedBeforeFinish : stimulus < started + duration) :
    stimulus < earliestNextGuard started duration := by
  simpa [earliestNextGuard] using arrivedBeforeFinish

/-! ## Brokered evidence is a semantic boundary -/

/-- A known, permitted call is pending before broker execution, while a
successful broker resolution appends its result and returns to `ready`. A later
model step therefore receives evidence which did not exist when the call was
proposed. -/
theorem brokered_success_crosses_an_evidence_boundary
    (execute : CodingAgent.Executor)
    (view : CodingAgent.RequestView) (state : CodingAgent.State)
    (call workspace evidence : Nat)
    (ready : state.phase = .ready)
    (known : call ∈ view.executable)
    (allowed : call ∈ view.permitted)
    (result : execute state.workspace call =
      .success workspace evidence) :
    let pending := CodingAgent.sample view state (.call call)
    let settled := CodingAgent.resolve execute pending
    pending.phase = .awaiting call view ∧
      settled.phase = .ready ∧
      settled.history = state.history ++
        [.proposed call, .result call evidence] := by
  simp [CodingAgent.sample, CodingAgent.resolve, ready, known, allowed, result]

/-- While a call is pending, another model directive is observational stutter.
This is the formal call/result barrier absent from a static command list. -/
theorem pending_call_blocks_resampling
    (view nextView : CodingAgent.RequestView)
    (state : CodingAgent.State) (call : Nat)
    (directive : CodingAgent.Directive)
    (ready : state.phase = .ready)
    (known : call ∈ view.executable) :
    CodingAgent.sample nextView
      (CodingAgent.sample view state (.call call)) directive =
      CodingAgent.sample view state (.call call) :=
  CodingAgent.cannot_resample_while_awaiting
    view nextView state call directive ready known

/-! ## Further non-robustness witnesses in the deployed Gödel shape -/

inductive BatchCommand where
  | reject
  | mutate
deriving Repr, DecidableEq

structure BatchState where
  world : Nat
  failures : Nat
deriving Repr, DecidableEq

/-- The deployed dispatcher records a failed command and continues with the
suffix; a later command may still change the external world. -/
def runOne : BatchState → BatchCommand → BatchState
  | state, .reject => { state with failures := state.failures + 1 }
  | state, .mutate => { state with world := state.world + 1 }

def runCommittedBatch (commands : List BatchCommand) (state : BatchState) :
    BatchState :=
  commands.foldl runOne state

theorem rejected_prefix_does_not_bar_mutating_suffix :
    runCommittedBatch [.reject, .mutate] ⟨0, 0⟩ = ⟨1, 1⟩ := by
  rfl

/-- A bounded suffix projection cannot, in general, preserve facts that differ
only in the discarded prefix. This is the abstract failure mode of retaining
only the last characters of a multi-command result bundle. -/
def lastOne {α : Type*} (items : List α) : List α :=
  items.drop (items.length - 1)

theorem result_suffix_projection_is_not_injective :
    lastOne [0, 2] = lastOne [1, 2] ∧ [0, 2] ≠ [1, 2] := by
  decide

/-- A memory lookup followed by a preselected use is another instance of the
same feedback no-go as terminal interaction. -/
inductive Evidence where
  | supports
  | contradicts
deriving Repr, DecidableEq, Inhabited

inductive BeliefUse where
  | act
  | abstain
deriving Repr, DecidableEq

def requiredForEvidence : RequiredContinuation Evidence BeliefUse
  | .supports => .act
  | .contradicts => .abstain

theorem query_and_use_cannot_share_a_correct_precommitted_batch :
    ¬ ∃ fixed, PrecommitmentCorrect requiredForEvidence fixed := by
  apply no_precommitted_continuation_for_feedback_sensitive_step
  exact ⟨.supports, .contradicts, by decide⟩

/-- The brokered form is strictly more expressive at this boundary: returning
the query result before choosing its use handles both observations, while no
single precommitted use can.  This is the precise relevant advantage of the
Codex/OpenCode-style call/result/continuation protocol over a static command
list; it is not a claim of general agent superiority. -/
theorem evidence_barrier_handles_query_then_use_while_precommitment_cannot :
    (∀ evidence,
      observeThenChoose requiredForEvidence evidence =
        requiredForEvidence evidence) ∧
      ¬ ∃ fixed, PrecommitmentCorrect requiredForEvidence fixed := by
  exact ⟨fun evidence => observe_then_choose_is_correct
    requiredForEvidence evidence,
    query_and_use_cannot_share_a_correct_precommitted_batch⟩

end PettaClaw.ToolLoopComparison

#print axioms PettaClaw.ToolLoopComparison.every_mode_retains_five_commands
#print axioms PettaClaw.ToolLoopComparison.stable_frontier_executes_full_batch
#print axioms PettaClaw.ToolLoopComparison.changed_frontier_withholds_unexecuted_suffix
#print axioms PettaClaw.ToolLoopComparison.stable_guard_preserves_a_batch_rejected_by_hard_single_step
#print axioms PettaClaw.ToolLoopComparison.nonpreemptible_command_imposes_reaction_latency
#print axioms PettaClaw.ToolLoopComparison.brokered_success_crosses_an_evidence_boundary
#print axioms PettaClaw.ToolLoopComparison.pending_call_blocks_resampling
#print axioms PettaClaw.ToolLoopComparison.rejected_prefix_does_not_bar_mutating_suffix
#print axioms PettaClaw.ToolLoopComparison.result_suffix_projection_is_not_injective
#print axioms PettaClaw.ToolLoopComparison.query_and_use_cannot_share_a_correct_precommitted_batch
#print axioms PettaClaw.ToolLoopComparison.evidence_barrier_handles_query_then_use_while_precommitment_cannot
