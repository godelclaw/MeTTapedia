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

/-! ## A replaceable execution-policy coordinate -/

inductive Mode where
  | agent
  | iter
  | coding
  | iterCoding
deriving Repr, DecidableEq

/-- Interactive policies admit one command per observation. Coding policies
retain the existing bounded five-command batch. This is policy data, not a new
case in the weak process kernel. -/
def batchLimit : Mode → Nat
  | .agent | .iter => 1
  | .coding | .iterCoding => 5

def admitBatch {Command : Type*} (mode : Mode) (commands : List Command) :
    List Command :=
  commands.take (batchLimit mode)

theorem agent_admits_at_most_one {Command : Type*} (commands : List Command) :
    (admitBatch .agent commands).length ≤ 1 := by
  simp [admitBatch, batchLimit]

theorem iter_admits_at_most_one {Command : Type*} (commands : List Command) :
    (admitBatch .iter commands).length ≤ 1 := by
  simp [admitBatch, batchLimit]

theorem interactive_admission_has_no_second_command
    {Command : Type*} (mode : Mode)
    (interactive : mode = .agent ∨ mode = .iter)
    (commands : List Command) :
    (admitBatch mode commands).length < 2 := by
  rcases interactive with rfl | rfl
  · simpa [Nat.lt_succ_iff] using agent_admits_at_most_one commands
  · simpa [Nat.lt_succ_iff] using iter_admits_at_most_one commands

theorem coding_retains_five_commands {Command : Type*}
    (first second third fourth fifth : Command) (rest : List Command) :
    admitBatch .coding
      ([first, second, third, fourth, fifth] ++ rest) =
      [first, second, third, fourth, fifth] := by
  simp [admitBatch, batchLimit]

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

#print axioms PettaClaw.ToolLoopComparison.agent_admits_at_most_one
#print axioms PettaClaw.ToolLoopComparison.interactive_admission_has_no_second_command
#print axioms PettaClaw.ToolLoopComparison.coding_retains_five_commands
#print axioms PettaClaw.ToolLoopComparison.brokered_success_crosses_an_evidence_boundary
#print axioms PettaClaw.ToolLoopComparison.pending_call_blocks_resampling
#print axioms PettaClaw.ToolLoopComparison.rejected_prefix_does_not_bar_mutating_suffix
#print axioms PettaClaw.ToolLoopComparison.result_suffix_projection_is_not_injective
#print axioms PettaClaw.ToolLoopComparison.query_and_use_cannot_share_a_correct_precommitted_batch
#print axioms PettaClaw.ToolLoopComparison.evidence_barrier_handles_query_then_use_while_precommitment_cannot
