/-!
# Witnessed task-phase state

Task phases are kept outside the process kernel.  An unknown phase is simply
pending, beginning a phase is explicit, and completing it requires an evidence
reference.  Completion is absorbing within one task instance: later begin or
completion events cannot silently make a completed phase pending again.

There is no global phase order and no mode-specific action cap here.  Separate
tasks may choose unrelated phase vocabularies and may have several active
phases at once.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.TaskPhase

universe uTask uPhase uEvidence uRevision uRevision₂

/-- Per-phase status.  Completion retains its evidence reference. -/
inductive Status (EvidenceRef : Type uEvidence) where
  | pending
  | active
  | completed (evidence : EvidenceRef)
deriving Repr, DecidableEq

/-- A small event language with no reopening or downgrade event. -/
inductive Event (Phase : Type uPhase) (EvidenceRef : Type uEvidence) where
  | begin (phase : Phase)
  | complete (phase : Phase) (evidence : EvidenceRef)
  | unrelated
deriving Repr, DecidableEq

/-- A task-local phase world.  Starting another task requires constructing a
new world with a new `task`; it is not an implicit phase transition. -/
structure World
    (Task : Type uTask) (Phase : Type uPhase)
    (EvidenceRef : Type uEvidence) (Revision : Type uRevision) where
  task : Task
  evidenceRevision : Revision
  status : Phase → Status EvidenceRef

/-- One phase-local transition.  A completion witness is never overwritten. -/
def stepStatus {EvidenceRef : Type uEvidence} :
    Status EvidenceRef → Bool → Option EvidenceRef → Status EvidenceRef
  | .completed evidence, _, _ => .completed evidence
  | _, true, some evidence => .completed evidence
  | .pending, true, none => .active
  | status, false, _ => status
  | .active, true, none => .active

/-- Apply one task event without changing the evidence revision. -/
def step
    {Task : Type uTask} {Phase : Type uPhase}
    {EvidenceRef : Type uEvidence} {Revision : Type uRevision}
    [DecidableEq Phase]
    (world : World Task Phase EvidenceRef Revision)
    (event : Event Phase EvidenceRef) : World Task Phase EvidenceRef Revision :=
  match event with
  | .begin phase =>
      { world with status := fun candidate =>
          stepStatus (world.status candidate) (candidate = phase) none }
  | .complete phase evidence =>
      { world with status := fun candidate =>
          stepStatus (world.status candidate) (candidate = phase) (some evidence) }
  | .unrelated => world

/-- Updating the evidence revision does not rewrite phase facts. -/
def revise
    {Task : Type uTask} {Phase : Type uPhase}
    {EvidenceRef : Type uEvidence} {Revision₁ : Type uRevision}
    {Revision₂ : Type uRevision₂}
    (world : World Task Phase EvidenceRef Revision₁) (revision : Revision₂) :
    World Task Phase EvidenceRef Revision₂ where
  task := world.task
  evidenceRevision := revision
  status := world.status

/-- Once one phase is completed, every later event leaves it completed with
the same witness. -/
theorem completed_is_absorbing
    {Task : Type uTask} {Phase : Type uPhase}
    {EvidenceRef : Type uEvidence} {Revision : Type uRevision}
    [DecidableEq Phase]
    (world : World Task Phase EvidenceRef Revision)
    (phase : Phase) (evidence : EvidenceRef)
    (completed : world.status phase = .completed evidence)
    (event : Event Phase EvidenceRef) :
    (step world event).status phase = .completed evidence := by
  cases event <;> simp_all [step, stepStatus]

/-- Revision refresh preserves a witnessed completion exactly. -/
theorem revise_preserves_completed
    {Task : Type uTask} {Phase : Type uPhase}
    {EvidenceRef : Type uEvidence} {Revision₁ : Type uRevision}
    {Revision₂ : Type uRevision₂}
    (world : World Task Phase EvidenceRef Revision₁)
    (revision : Revision₂) (phase : Phase) (evidence : EvidenceRef)
    (completed : world.status phase = .completed evidence) :
    (revise world revision).status phase = .completed evidence := by
  exact completed

/-- A phase cannot become completed merely by beginning it; a completion
witness is required. -/
theorem begin_pending_is_active
    {Task : Type uTask} {Phase : Type uPhase}
    {EvidenceRef : Type uEvidence} {Revision : Type uRevision}
    [DecidableEq Phase]
    (world : World Task Phase EvidenceRef Revision)
    (phase : Phase) (pending : world.status phase = .pending) :
    (step world (.begin phase)).status phase = .active := by
  simp [step, stepStatus, pending]

end Mettapedia.CognitiveArchitecture.Agent.TaskPhase

#print axioms Mettapedia.CognitiveArchitecture.Agent.TaskPhase.completed_is_absorbing
#print axioms Mettapedia.CognitiveArchitecture.Agent.TaskPhase.begin_pending_is_active
