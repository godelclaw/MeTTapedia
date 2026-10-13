import CodingAgent
import FeedbackSensitiveBatch

/-!

Historical/design model: this file records a policy studied before the sequential
tool simplification. Its holds, quotas, or scheduling assumptions are not the
current dispatch contract. See `SequentialTools.lean` for that contract and
`CommandHolds.lean` for the conditional costs of the removed hold policy.
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

universe u

/-! ## Batch admission

Until `b7e8837` every preset admitted up to five commands per response, and the
model chose a short or long batch.  With the observed strategy on, as both
deployed agents run it, the broker keeps the requested count only for a batch
made entirely of host-state reads it lists as independent
(`strategy_host.INDEPENDENT_READS`); any other batch runs its first command and
the rest is recorded once as deferred.  This count limit is not what grounds
the loop.  The dispatcher already withholds dependent commands at new input and
after a failed send or deletion (`runUnlessStimulus` and `runFresh` below), and
`IterGrounding` proves result totality, no silent deferral and complete
evidence for a runner that executes every proposed command in order and pairs
each with its result.  The theorems here state the limit exactly and what it
withholds. -/

/-- The requested count, at least one (`skills.pl` `command_batch_limit`). -/
def staticLimit (requested : Nat) : Nat := max 1 requested

/-- The deployed count limit (`strategy_host.batch_limit`). -/
def brokerLimit {Command : Type u} (independent : Command → Bool)
    (requested : Nat) (commands : List Command) : Nat :=
  if !commands.isEmpty && commands.all independent then staticLimit requested
  else 1

def admitBatch {Command : Type u} (independent : Command → Bool)
    (requested : Nat) (commands : List Command) : List Command :=
  commands.take (brokerLimit independent requested commands)

/-- Before the count limit, and with the observed strategy off, a response
kept five commands. -/
theorem static_envelope_retains_five_commands {Command : Type u}
    (first second third fourth fifth : Command) (rest : List Command) :
    ([first, second, third, fourth, fifth] ++ rest).take (staticLimit 5) =
      [first, second, third, fourth, fifth] := by
  simp [staticLimit]

/-- A batch of independent reads keeps the requested count. -/
theorem independent_reads_keep_the_requested_count {Command : Type u}
    (independent : Command → Bool) (requested : Nat) (commands : List Command)
    (reads : ∀ c ∈ commands, independent c = true) :
    admitBatch independent requested commands =
      commands.take (staticLimit requested) := by
  cases commands with
  | nil => simp [admitBatch]
  | cons c cs =>
      have all : (c :: cs).all independent = true := List.all_eq_true.mpr reads
      simp only [admitBatch, brokerLimit]
      simp [all]

/-- Any other batch runs its first command only. -/
theorem any_other_batch_runs_its_first_command {Command : Type u}
    (independent : Command → Bool) (requested : Nat) (commands : List Command)
    (other : ∃ c ∈ commands, independent c = false) :
    admitBatch independent requested commands = commands.take 1 := by
  obtain ⟨c, member, notRead⟩ := other
  have some : commands.all independent = false :=
    List.all_eq_false.mpr ⟨c, member, by simp [notRead]⟩
  simp [admitBatch, brokerLimit, some]

/-- The revision witnessed immediately before each command. Execution stops at
the first revision which differs from the context frontier captured for the
model turn. -/
def runUnlessStimulus {Command : Type u} (captured : Nat) :
    List (Nat × Command) → List Command
  | [] => []
  | (live, command) :: rest =>
      if live = captured then
        command :: runUnlessStimulus captured rest
      else
        []

/-- With no new stimulus the guard preserves the whole chosen batch. -/
theorem stable_frontier_executes_full_batch {Command : Type u}
    (captured : Nat) (commands : List Command) :
    runUnlessStimulus captured
      (commands.map (fun command => (captured, command))) = commands := by
  induction commands with
  | nil => rfl
  | cons command rest ih => simp [runUnlessStimulus, ih]

/-- A changed frontier withholds exactly the suffix which has not yet run. -/
theorem changed_frontier_withholds_unexecuted_suffix {Command : Type u}
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
    {Command : Type u} (first second : Command) :
    runUnlessStimulus 7 [(7, first), (7, second)] = [first, second] ∧
      [first, second].take 1 = [first] := by
  simp [runUnlessStimulus]

/-- What the count limit withholds: with no new input the stimulus guard runs
the whole chosen batch, while the deployed limit runs one command of any batch
that is not made entirely of independent reads. -/
theorem count_limit_withholds_what_the_guard_would_run {Command : Type u}
    (independent : Command → Bool) (requested captured : Nat)
    (commands : List Command) (other : ∃ c ∈ commands, independent c = false) :
    runUnlessStimulus captured
        (commands.map (fun command => (captured, command))) = commands ∧
      admitBatch independent requested commands = commands.take 1 :=
  ⟨stable_frontier_executes_full_batch captured commands,
    any_other_batch_runs_its_first_command independent requested commands other⟩

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
def lastOne {α : Type u} (items : List α) : List α :=
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

/-! ## Per-chat freshness: the deployed refinement of the stimulus guard

`runUnlessStimulus` withholds every unexecuted command once newer input
arrives.  The PeTTa runtime narrows this to what that input could change: a
conversation effect into a chat whose new input the model has not read, and a
rest, which would sleep through it.  A withheld step stops the batch there,
as a failed send does.  This is the per-command form of
`VerifiedFrontier.pending_same_conversation_blocks_commit`: input for one
conversation never blocks an effect in another.  Runtimes without the
per-command check keep the global guard above. -/

/-- A command, as far as unread input can matter to it. -/
inductive Step where
  | speak (chat : Nat)
  | rest
  | other
deriving Repr, DecidableEq

/-- Whether a step may run while `unread` chats hold input the model has not
read. -/
def unaffected (unread : List Nat) : Step → Bool
  | .speak chat => !unread.contains chat
  | .rest => unread.isEmpty
  | .other => true

/-- Run the chosen steps up to the first one that unread input affects. -/
def runFresh (unread : List Nat) : List Step → List Step
  | [] => []
  | step :: rest =>
      if unaffected unread step then step :: runFresh unread rest else []

/-- The refinement only ever runs a prefix of the chosen batch, in order. -/
theorem run_fresh_is_prefix (unread : List Nat) (steps : List Step) :
    runFresh unread steps <+: steps := by
  induction steps with
  | nil => exact List.nil_prefix
  | cons step rest ih =>
      unfold runFresh
      split
      · exact List.cons_prefix_cons.mpr ⟨rfl, ih⟩
      · exact List.nil_prefix

theorem no_unread_input_runs_the_whole_batch (steps : List Step) :
    runFresh [] steps = steps := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [runFresh, unaffected, ih]

/-- A message in one chat never withholds a send to another, nor anything
that does not speak or rest. -/
theorem unrelated_input_withholds_nothing (unread : List Nat)
    (steps : List Step)
    (unrelated : ∀ step ∈ steps, unaffected unread step = true) :
    runFresh unread steps = steps := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
      have here := unrelated step (by simp)
      have later : ∀ s ∈ rest, unaffected unread s = true :=
        fun s member => unrelated s (by simp [member])
      simp [runFresh, here, ih later]

/-- A reply into a chat with unread input is withheld together with
everything after it; what ran before it stays run. -/
theorem reply_into_unread_chat_stops_the_batch (unread : List Nat)
    (before after : List Step) (chat : Nat) (unreadChat : chat ∈ unread)
    (ran : ∀ step ∈ before, unaffected unread step = true) :
    runFresh unread (before ++ .speak chat :: after) = before := by
  induction before with
  | nil => simp [runFresh, unaffected, unreadChat]
  | cons step rest ih =>
      have here := ran step (by simp)
      have later : ∀ s ∈ rest, unaffected unread s = true :=
        fun s member => ran s (by simp [member])
      simp [runFresh, here, ih later]

/-- A rest waits while anything is unread: sleeping would make the sender
wait out the whole rest. -/
theorem rest_waits_on_unread_input (unread : List Nat) (after : List Step)
    (someUnread : unread ≠ []) :
    runFresh unread (.rest :: after) = [] := by
  cases unread with
  | nil => exact absurd rfl someUnread
  | cons chat more => simp [runFresh, unaffected]

/-- Where the global guard withholds a whole suffix of steps chosen before
newer input arrived, the refinement keeps every step that input cannot
affect. -/
theorem refinement_keeps_what_the_global_guard_withheld {Command : Type u}
    (captured changed : Nat) (different : changed ≠ captured)
    (commands : List Command) (unread : List Nat) (steps : List Step)
    (unrelated : ∀ step ∈ steps, unaffected unread step = true) :
    runUnlessStimulus captured (commands.map (fun command => (changed, command)))
        = [] ∧
      runFresh unread steps = steps := by
  refine ⟨?_, unrelated_input_withholds_nothing unread steps unrelated⟩
  cases commands with
  | nil => rfl
  | cons command rest => simp [runUnlessStimulus, different]

end PettaClaw.ToolLoopComparison

#print axioms PettaClaw.ToolLoopComparison.static_envelope_retains_five_commands
#print axioms PettaClaw.ToolLoopComparison.independent_reads_keep_the_requested_count
#print axioms PettaClaw.ToolLoopComparison.any_other_batch_runs_its_first_command
#print axioms PettaClaw.ToolLoopComparison.count_limit_withholds_what_the_guard_would_run
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
#print axioms PettaClaw.ToolLoopComparison.run_fresh_is_prefix
#print axioms PettaClaw.ToolLoopComparison.no_unread_input_runs_the_whole_batch
#print axioms PettaClaw.ToolLoopComparison.unrelated_input_withholds_nothing
#print axioms PettaClaw.ToolLoopComparison.reply_into_unread_chat_stops_the_batch
#print axioms PettaClaw.ToolLoopComparison.rest_waits_on_unread_input
#print axioms PettaClaw.ToolLoopComparison.refinement_keeps_what_the_global_guard_withheld
