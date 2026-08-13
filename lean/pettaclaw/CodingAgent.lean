import ProtectedPlasticity

/-!
# CodingAgent — a brokered action/evidence loop

An executable model of the sequential core of the OpenAI Codex coding-agent
loop.  The source correspondence is pinned to `openai/codex` main commit
`1da59ad257115cc5734e6781d5ac0b4f08a6e064` (2026-08-14); stable release
`rust-v0.147.0` has annotated tag object
`3ed6f04f6bf8b7c46299d1cb1ff99c74ce21a51d`, resolving to commit
`be6e8eac029b183056b7e4402879f15d2c85f61b`; it is the reproducible release
baseline.

The model retains five implementation facts:

* one request view supplies both the advertised tool schemas and the router
  used for calls from that request;
* a model tool proposal does not itself mutate the workspace;
* only a permitted broker resolution may apply an executor result;
* success, failure, denial, and unknown-tool results become evidence before
  another model step;
* a final assistant answer terminates the task without an ambient tool action.

This is the single-call sequential quotient.  The implementation may dispatch
several calls concurrently, but drains their futures in request order before
the next sampling request.  Conformance of that parallel implementation to an
appropriate serialization is outside the theorem boundary here.

The theory deliberately does not claim that an answer is correct or verified.
It proves causal mediation and evidence availability.  Model quality, prompt
discipline, tool correctness, and source-to-model correspondence remain in the
trusted boundary.
-/

namespace CodingAgent

/-! ## Request snapshots and task state -/

/-- Opaque tool identifiers are natural numbers.  Advertisement, executable
dispatch, and permission are separate because none implies either other one.
The complete record is captured for one sampling request. -/
structure RequestView where
  advertised : List Nat
  executable : List Nat
  permitted : List Nat
deriving Repr, DecidableEq

inductive Observation
  | user (payload : Nat)
  | proposed (call : Nat)
  | result (call payload : Nat)
  | failed (call error : Nat)
  | denied (call : Nat)
  | unknown (call : Nat)
  | interrupted
deriving Repr, DecidableEq

inductive Directive
  | call (tool : Nat)
  | finish (answer : Nat)
deriving Repr, DecidableEq

/-- The exact request view is retained while its proposed call is pending. -/
inductive Phase
  | ready
  | awaiting (call : Nat) (view : RequestView)
  | done (answer : Nat)
  | aborted
deriving Repr, DecidableEq

structure State where
  workspace : Nat
  history : List Observation
  phase : Phase
deriving Repr, DecidableEq

def initial (workspace prompt : Nat) : State :=
  ⟨workspace, [.user prompt], .ready⟩

/-- A failed execution cannot smuggle in a workspace replacement. -/
inductive Outcome
  | success (workspace evidence : Nat)
  | failure (error : Nat)
deriving Repr, DecidableEq

abbrev Executor := Nat → Nat → Outcome

/-! ## The small-step loop -/

/-- One model sampling result.  Unknown calls are immediately reflected as
evidence.  A known call becomes pending; execution is a separate transition. -/
def sample (view : RequestView) (state : State) : Directive → State
  | .call call =>
      match state.phase with
      | .ready =>
          let proposed := state.history ++ [.proposed call]
          if call ∈ view.executable then
            { state with history := proposed, phase := .awaiting call view }
          else
            { state with
              history := proposed ++ [.unknown call]
              phase := .ready }
      | _ => state
  | .finish answer =>
      match state.phase with
      | .ready => { state with phase := .done answer }
      | _ => state

/-- The broker is the only transition that invokes the executor.  It uses the
request view stored with the pending call, rather than a freshly substituted
catalog or policy. -/
def resolve (execute : Executor) (state : State) : State :=
  match state.phase with
  | .awaiting call view =>
      if call ∈ view.permitted then
        match execute state.workspace call with
        | .success workspace evidence =>
            { state with
              workspace := workspace
              history := state.history ++ [.result call evidence]
              phase := .ready }
        | .failure error =>
            { state with
              history := state.history ++ [.failed call error]
              phase := .ready }
      else
        { state with
          history := state.history ++ [.denied call]
          phase := .ready }
  | _ => state

def interrupt (state : State) : State :=
  { state with history := state.history ++ [.interrupted], phase := .aborted }

inductive Event
  | model (view : RequestView) (directive : Directive)
  | broker
  | cancel

def step (execute : Executor) (state : State) : Event → State
  | .model view directive => sample view state directive
  | .broker => resolve execute state
  | .cancel => interrupt state

def run (execute : Executor) : List Event → State → State
  | [], state => state
  | event :: rest, state => run execute rest (step execute state event)

/-! ## Request coherence and the evidence barrier -/

/-- A model proposal is data, not an ambient workspace capability. -/
theorem sample_preserves_workspace (view : RequestView) (state : State)
    (directive : Directive) :
    (sample view state directive).workspace = state.workspace := by
  cases state with
  | mk workspace history phase =>
      cases directive with
      | finish answer => cases phase <;> rfl
      | call tool =>
          cases phase with
          | ready =>
              by_cases known : tool ∈ view.executable <;>
                simp [sample, known]
          | awaiting call pendingView => rfl
          | done answer => rfl
          | aborted => rfl

/-- A known proposal retains exactly the request view under which the tool was
advertised and routed. -/
theorem request_view_is_captured (view : RequestView) (state : State)
    (call : Nat) (ready : state.phase = .ready)
    (known : call ∈ view.executable) :
    (sample view state (.call call)).phase = .awaiting call view := by
  simp [sample, ready, known]

/-- No second model result is admitted while execution evidence is pending. -/
theorem cannot_resample_while_awaiting (view nextView : RequestView)
    (state : State) (call : Nat) (directive : Directive)
    (ready : state.phase = .ready) (known : call ∈ view.executable) :
    sample nextView (sample view state (.call call)) directive =
      sample view state (.call call) := by
  cases directive <;> simp [sample, ready, known]

theorem unknown_call_preserves_workspace (view : RequestView) (state : State)
    (call : Nat) (ready : state.phase = .ready)
    (unknown : call ∉ view.executable) :
    let next := sample view state (.call call)
    next.workspace = state.workspace ∧
      next.history = state.history ++ [.proposed call, .unknown call] ∧
      next.phase = .ready := by
  simp [sample, ready, unknown]

/-- A successful round trip exposes the executor's result to the next model
step and returns the machine to `ready`. -/
theorem successful_round_records_evidence (execute : Executor)
    (view : RequestView) (state : State) (call workspace evidence : Nat)
    (ready : state.phase = .ready)
    (known : call ∈ view.executable)
    (allowed : call ∈ view.permitted)
    (result : execute state.workspace call = .success workspace evidence) :
    let next := resolve execute (sample view state (.call call))
    next.workspace = workspace ∧
      next.history = state.history ++
        [.proposed call, .result call evidence] ∧
      next.phase = .ready := by
  simp [sample, resolve, ready, known, allowed, result]

theorem failed_round_records_evidence_without_mutation (execute : Executor)
    (view : RequestView) (state : State) (call error : Nat)
    (ready : state.phase = .ready)
    (known : call ∈ view.executable)
    (allowed : call ∈ view.permitted)
    (result : execute state.workspace call = .failure error) :
    let next := resolve execute (sample view state (.call call))
    next.workspace = state.workspace ∧
      next.history = state.history ++ [.proposed call, .failed call error] ∧
      next.phase = .ready := by
  simp [sample, resolve, ready, known, allowed, result]

theorem denied_round_records_evidence_without_mutation (execute : Executor)
    (view : RequestView) (state : State) (call : Nat)
    (ready : state.phase = .ready)
    (known : call ∈ view.executable)
    (denied : call ∉ view.permitted) :
    let next := resolve execute (sample view state (.call call))
    next.workspace = state.workspace ∧
      next.history = state.history ++ [.proposed call, .denied call] ∧
      next.phase = .ready := by
  simp [sample, resolve, ready, known, denied]

/-! ## Every workspace effect is broker-mediated -/

def AuthorizedResolution (execute : Executor) (before after : State) : Prop :=
  ∃ call view workspace evidence,
    before.phase = .awaiting call view ∧
      call ∈ view.permitted ∧
      execute before.workspace call = .success workspace evidence ∧
      after = resolve execute before

theorem resolve_change_requires_authorized_success (execute : Executor)
    (state : State)
    (changed : (resolve execute state).workspace ≠ state.workspace) :
    AuthorizedResolution execute state (resolve execute state) := by
  cases state with
  | mk initialWorkspace history phase =>
      cases phase with
      | ready => simp [resolve] at changed
      | done answer => simp [resolve] at changed
      | aborted => simp [resolve] at changed
      | awaiting call view =>
          by_cases allowed : call ∈ view.permitted
          · cases outcomeEq : execute initialWorkspace call with
            | success workspace evidence =>
                exact ⟨call, view, workspace, evidence, rfl, allowed,
                  outcomeEq, rfl⟩
            | failure error =>
                have unchanged :
                    (resolve execute
                      ⟨initialWorkspace, history, .awaiting call view⟩).workspace =
                      initialWorkspace := by
                  simp [resolve, allowed, outcomeEq]
                exact False.elim (changed unchanged)
          · have unchanged :
                (resolve execute
                  ⟨initialWorkspace, history, .awaiting call view⟩).workspace =
                  initialWorkspace := by
              simp [resolve, allowed]
            exact False.elim (changed unchanged)

theorem step_change_requires_authorized_success (execute : Executor)
    (state : State) (event : Event)
    (changed : (step execute state event).workspace ≠ state.workspace) :
    AuthorizedResolution execute state (step execute state event) := by
  cases event with
  | model view directive =>
      exact False.elim (changed (sample_preserves_workspace view state directive))
  | broker => exact resolve_change_requires_authorized_success execute state changed
  | cancel => exact False.elim (changed rfl)

/-- An audit predicate checks every adjacent state in a finite run, rather
than merely comparing endpoints (whose changes could cancel). -/
def Audited (execute : Executor) : State → List Event → Prop
  | _, [] => True
  | state, event :: rest =>
      ((step execute state event).workspace ≠ state.workspace →
        AuthorizedResolution execute state (step execute state event)) ∧
      Audited execute (step execute state event) rest

theorem every_trace_is_audited (execute : Executor)
    (state : State) (events : List Event) :
    Audited execute state events := by
  induction events generalizing state with
  | nil => trivial
  | cons event rest ih =>
      exact ⟨step_change_requires_authorized_success execute state event,
        ih (step execute state event)⟩

/-! ## Cancellation, termination, and a necessary limitation -/

theorem cancellation_preserves_workspace (state : State) :
    (interrupt state).workspace = state.workspace := rfl

theorem cancellation_aborts (state : State) :
    (interrupt state).phase = .aborted := rfl

theorem answer_is_workspace_pure (view : RequestView) (state : State)
    (answer : Nat) :
    (sample view state (.finish answer)).workspace = state.workspace :=
  sample_preserves_workspace view state (.finish answer)

/-- A final answer establishes a task boundary: later model directives do not
silently reopen the completed task. -/
theorem answer_is_terminal (view nextView : RequestView) (state : State)
    (answer : Nat) (directive : Directive) (ready : state.phase = .ready) :
    sample nextView (sample view state (.finish answer)) directive =
      sample view state (.finish answer) := by
  cases directive <;> simp [sample, ready]

def isToolEvidence : Observation → Bool
  | .result _ _ | .failed _ _ | .denied _ | .unknown _ => true
  | _ => false

/-- The core permits an unverified final answer.  Verification is a policy and
workflow discipline, not an invariant of this transition system. -/
theorem unverified_answer_is_reachable :
    ∃ state : State,
      state.phase = .done 7 ∧
        ¬ (state.history.any isToolEvidence) := by
  refine ⟨sample ⟨[], [], []⟩ (initial 0 1) (.finish 7), ?_⟩
  decide

/-! ## Essential composition with Iter and PettaClaw -/

/-- Iter transformations prepare model-visible messages and advertisements.
They do not receive the executable or permitted coordinates of a Codex request
view. -/
def prepareWithIter (transformations : List IterArchitecture.Transformation)
    (messages : List Nat) (view : RequestView) :
    IterArchitecture.Boundary × RequestView :=
  let boundary := IterArchitecture.applyTransformations transformations
    ⟨messages, view.advertised⟩
  (boundary, { view with advertised := boundary.advertised })

/-- Transformational plasticity of the request boundary cannot itself grant
execution or permission. -/
theorem iter_preparation_preserves_execution_authority
    (transformations : List IterArchitecture.Transformation)
    (messages : List Nat) (view : RequestView) :
    (prepareWithIter transformations messages view).2.executable =
        view.executable ∧
      (prepareWithIter transformations messages view).2.permitted =
        view.permitted := by
  simp [prepareWithIter]

/-- Host the coding loop as protected development: the CodingAgent event may
change development, but cannot rewrite constitution or life. -/
def hostedCodingStep {K L : Type} (execute : Executor)
    (state : ProtectedPlasticity.Coordinates K State L) (event : Event) :
    ProtectedPlasticity.Coordinates K State L :=
  ProtectedPlasticity.revise state (fun agent => step execute agent event)

theorem hosted_coding_preserves_kernel_and_life {K L : Type}
    (execute : Executor) (state : ProtectedPlasticity.Coordinates K State L)
    (event : Event) :
    let next := hostedCodingStep execute state event
    next.kernel = state.kernel ∧ next.life = state.life := by
  simp [hostedCodingStep, ProtectedPlasticity.revise]

/-- A coding step and an independent PettaClaw life evolution commute.  Thus
the CodingAgent loop composes with a life-loop; it does not subsume one. -/
theorem coding_and_life_commute {K L : Type} (execute : Executor)
    (state : ProtectedPlasticity.Coordinates K State L)
    (event : Event) (living : L → L) :
    ProtectedPlasticity.evolve (hostedCodingStep execute state event) living =
      hostedCodingStep execute (ProtectedPlasticity.evolve state living) event := by
  rfl

end CodingAgent

/-! ## Axiom audit -/
#print axioms CodingAgent.sample_preserves_workspace
#print axioms CodingAgent.request_view_is_captured
#print axioms CodingAgent.cannot_resample_while_awaiting
#print axioms CodingAgent.successful_round_records_evidence
#print axioms CodingAgent.failed_round_records_evidence_without_mutation
#print axioms CodingAgent.denied_round_records_evidence_without_mutation
#print axioms CodingAgent.resolve_change_requires_authorized_success
#print axioms CodingAgent.every_trace_is_audited
#print axioms CodingAgent.answer_is_terminal
#print axioms CodingAgent.unverified_answer_is_reachable
#print axioms CodingAgent.iter_preparation_preserves_execution_authority
#print axioms CodingAgent.hosted_coding_preserves_kernel_and_life
#print axioms CodingAgent.coding_and_life_commute
