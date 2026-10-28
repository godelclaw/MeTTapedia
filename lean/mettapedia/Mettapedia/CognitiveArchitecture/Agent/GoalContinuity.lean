import Mettapedia.CognitiveArchitecture.Agent.TaskPhase
import Mettapedia.CognitiveArchitecture.Agent.ContextAttention
import Mathlib.Data.Finset.Basic

/-!
# Revision-bound goal assessment and continuation

The small core of a goal/continuation protocol: finishing work is independent
of meeting its goal. Assessment uses a nonempty set of required criteria and
keeps evidence eligibility, evaluator health and verdict separate. A passing
assessment is applicable only to its exact goal, target and evidence revision.
Revision identifiers are assumed to name immutable contents; this is not a
proof that a hash, evaluator or supplied evidence is trustworthy.

Historical task completion uses `TaskPhase`; required context uses
`ContextAttention`. The model specifies no centralized scheduler, compulsory
review, truth oracle, or runtime implementation. It abstracts the assessment
and continuation ideas in One Hive Goals and Continuity, proposed v0.1,
sections 3--8, without claiming to implement its entire admission protocol.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.GoalContinuity

structure Stamp where
  goal : Nat
  definition : Nat
  target : Nat
  evidence : Nat
  deriving DecidableEq, Repr

structure Contract where
  stamp : Stamp
  required : Finset Nat
  nonempty : required.Nonempty

inductive Verdict where
  | pass | fail | undetermined
  deriving DecidableEq, Repr

structure CriterionResult where
  eligible : Bool
  healthy : Bool
  verdict : Verdict
  receipt : Option Nat
  deriving DecidableEq, Repr

def Pass (r : CriterionResult) : Prop :=
  r.eligible = true ∧ r.healthy = true ∧ r.verdict = .pass ∧ r.receipt.isSome = true

def Fail (r : CriterionResult) : Prop :=
  r.eligible = true ∧ r.healthy = true ∧ r.verdict = .fail ∧ r.receipt.isSome = true

instance (r : CriterionResult) : Decidable (Pass r) := by unfold Pass; infer_instance
instance (r : CriterionResult) : Decidable (Fail r) := by unfold Fail; infer_instance

inductive Outcome where
  | met | notMet | undetermined
  deriving DecidableEq, Repr

/-- Missing rows are represented by undetermined results. Diagnostics remain
in the results even when another criterion determines the overall outcome. -/
def assess (g : Contract) (results : Nat → CriterionResult) : Outcome :=
  if ∀ c ∈ g.required, Pass (results c) then .met
  else if ∃ c ∈ g.required, Fail (results c) then .notMet
  else .undetermined

theorem met_iff_all_required_pass (g : Contract) (results : Nat → CriterionResult) :
    assess g results = .met ↔ ∀ c ∈ g.required, Pass (results c) := by
  unfold assess
  split_ifs <;> simp_all

theorem pass_excludes_failure (r : CriterionResult) (pass : Pass r) : ¬ Fail r := by
  intro fail
  have incompatible := pass.2.2.1.symm.trans fail.2.2.1
  cases incompatible

theorem required_failure_is_not_met (g : Contract) (results : Nat → CriterionResult)
    (c : Nat) (required : c ∈ g.required) (failed : Fail (results c)) :
    assess g results = .notMet := by
  have notAll : ¬ ∀ c ∈ g.required, Pass (results c) := by
    intro all
    exact pass_excludes_failure _ (all c required) failed
  simp [assess, notAll, show ∃ c ∈ g.required, Fail (results c) from ⟨c, required, failed⟩]

theorem required_error_blocks_met (g : Contract) (results : Nat → CriterionResult)
    (c : Nat) (required : c ∈ g.required) (error : (results c).healthy = false) :
    assess g results ≠ .met := by
  intro met
  have healthy := ((met_iff_all_required_pass g results).mp met c required).2.1
  simp [error] at healthy

theorem missing_receipt_blocks_met (g : Contract) (results : Nat → CriterionResult)
    (c : Nat) (required : c ∈ g.required) (missing : (results c).receipt = none) :
    assess g results ≠ .met := by
  intro met
  have present := ((met_iff_all_required_pass g results).mp met c required).2.2.2
  simp [missing] at present

structure Evaluation where
  stamp : Stamp
  results : Nat → CriterionResult

def GoalMet (g : Contract) (evaluation : Evaluation) : Prop :=
  evaluation.stamp = g.stamp ∧ assess g evaluation.results = .met

theorem changed_definition_invalidates (g : Contract) (evaluation : Evaluation)
    (changed : evaluation.stamp.definition ≠ g.stamp.definition) :
    ¬ GoalMet g evaluation := fun h => changed (congrArg Stamp.definition h.1)

theorem changed_target_invalidates (g : Contract) (evaluation : Evaluation)
    (changed : evaluation.stamp.target ≠ g.stamp.target) :
    ¬ GoalMet g evaluation := fun h => changed (congrArg Stamp.target h.1)

theorem changed_evidence_invalidates (g : Contract) (evaluation : Evaluation)
    (changed : evaluation.stamp.evidence ≠ g.stamp.evidence) :
    ¬ GoalMet g evaluation := fun h => changed (congrArg Stamp.evidence h.1)

structure Project where
  contract : Contract
  task : TaskPhase.Status Nat
  assessment : Option Evaluation

/-- Recording an assessment does not advance the evidence epoch and thereby
invalidate the assessment it just recorded. -/
def recordAssessment (p : Project) (e : Evaluation) : Project :=
  { p with assessment := some e }

theorem recording_preserves_evidence_epoch (p : Project) (e : Evaluation) :
    (recordAssessment p e).contract.stamp.evidence = p.contract.stamp.evidence := rfl

def completeTask (p : Project) (receipt : Nat) : Project :=
  { p with task := TaskPhase.stepStatus p.task true (some receipt) }

theorem task_completion_preserves_assessment (p : Project) (receipt : Nat) :
    (completeTask p receipt).assessment = p.assessment := rfl

private def sampleContract : Contract := ⟨⟨0, 1, 1, 1⟩, {0}, by simp⟩
private def noEvidence : CriterionResult := ⟨false, true, .undetermined, none⟩

theorem completed_task_need_not_meet_goal :
    ∃ p : Project, p.task = .completed 7 ∧
      ∃ e, p.assessment = some e ∧ ¬ GoalMet p.contract e := by
  refine ⟨⟨sampleContract, .completed 7, some ⟨sampleContract.stamp, fun _ => noEvidence⟩⟩,
    rfl, ⟨sampleContract.stamp, fun _ => noEvidence⟩, rfl, ?_⟩
  simp [GoalMet, assess, sampleContract, Pass, Fail, noEvidence]

/-! A continuation is a current handoff, not a proof that external effects ran. -/

structure Continuation where
  stamp : Stamp
  required : List Nat
  unresolved : List Nat
  nextAction : Option Nat

structure Checkpoint where
  generation : Nat
  continuation : Continuation

/-- A stale writer cannot replace the currently accepted handoff. -/
def save (current : Checkpoint) (expected : Nat) (next : Continuation) : Checkpoint :=
  if current.generation = expected then ⟨expected + 1, next⟩ else current

theorem stale_checkpoint_preserves_current (current : Checkpoint) (expected : Nat)
    (next : Continuation) (stale : current.generation ≠ expected) :
    save current expected next = current := by simp [save, stale]

theorem old_writer_cannot_replace_accepted (current : Checkpoint)
    (accepted stale : Continuation) :
    let saved := save current current.generation accepted
    save saved current.generation stale = saved := by simp [save]

/-- Instantiate the existing required-context interface. Retrieval is optional;
the handoff's required references and unresolved work have separate fields. -/
def contextState (c : Continuation) : ContextAttention.State :=
  { ContextAttention.initial with
      active := some ⟨c.stamp.goal, c.required, c.unresolved⟩ }

structure Packet where
  stamp : Stamp
  nextAction : Option Nat
  view : ContextAttention.RequestView

def packet (c : Continuation) (budget : Nat) (memories : List Nat) : Packet :=
  ⟨c.stamp, c.nextAction, ContextAttention.assemble budget memories (contextState c)⟩

theorem optional_retrieval_preserves_binding_and_next_action (c : Continuation)
    (budget : Nat) (memories : List Nat) :
    (packet c budget memories).stamp = c.stamp ∧
      (packet c budget memories).nextAction = c.nextAction := ⟨rfl, rfl⟩

theorem optional_retrieval_preserves_requirements (c : Continuation)
    (budget : Nat) (memories : List Nat) :
    (ContextAttention.assemble budget memories (contextState c)).required = c.required := by
  exact ContextAttention.assembly_preserves_required_facts budget memories (contextState c)

theorem optional_retrieval_preserves_open_work (c : Continuation)
    (budget : Nat) (memories : List Nat) :
    (ContextAttention.assemble budget memories (contextState c)).active =
      some ⟨c.stamp.goal, c.required, c.unresolved⟩ := rfl

end Mettapedia.CognitiveArchitecture.Agent.GoalContinuity
