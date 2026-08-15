import WeakSelfHostingCore
import CodingAgent

/-!
# ThreePolicyFusion — one runner, three conservative policies

This file gives the transition semantics to be mirrored by the runnable PeTTa
seed.  One state carries independent Iter development, PettaClaw life, and
CodingAgent task coordinates.  Selecting a policy changes which controller
view is normally used; it does not revoke the other action forms.

The three projection theorems are the preservation result.  From any mixed
trace, erasing unrelated actions recovers exactly the corresponding source
semantics.  The protected root is unchanged by every trace.
-/

namespace ThreePolicyFusion

open WeakSelfHostingCore

inductive Policy
  | agent
  | iter
  | coding
deriving Repr, DecidableEq

structure State (K : Type) where
  kernel : K
  development : IterArchitecture.Boundary
  life : ProtectedPlasticity.Living
  coding : CodingAgent.State
  active : Policy

inductive Action
  | select (policy : Policy)
  | transform (transformation : IterArchitecture.Transformation)
  | live (action : ProtectedPlasticity.LifeAction)
  | code (event : CodingAgent.Event)

def step {K : Type} (heartbeat : Nat) (execute : CodingAgent.Executor)
    (state : State K) : Action → State K
  | .select policy => { state with active := policy }
  | .transform transformation =>
      { state with
        development := IterArchitecture.applyTransformation
          state.development transformation }
  | .live action =>
      { state with
        life := ProtectedPlasticity.lifeStep heartbeat state.life action }
  | .code event =>
      { state with coding := CodingAgent.step execute state.coding event }

def run {K : Type} (heartbeat : Nat) (execute : CodingAgent.Executor) :
    List Action → State K → State K
  | [], state => state
  | action :: rest, state =>
      run heartbeat execute rest (step heartbeat execute state action)

/-! ## Erasure maps -/

def iterActions : List Action → List IterArchitecture.Transformation
  | [] => []
  | .transform transformation :: rest =>
      transformation :: iterActions rest
  | _ :: rest => iterActions rest

def agentActions : List Action → List ProtectedPlasticity.LifeAction
  | [] => []
  | .live action :: rest => action :: agentActions rest
  | _ :: rest => agentActions rest

def codingActions : List Action → List CodingAgent.Event
  | [] => []
  | .code event :: rest => event :: codingActions rest
  | _ :: rest => codingActions rest

/-! ## Root preservation -/

theorem step_preserves_kernel {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (state : State K) (action : Action) :
    (step heartbeat execute state action).kernel = state.kernel := by
  cases action <;> rfl

theorem run_preserves_kernel {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (actions : List Action) (state : State K) :
    (run heartbeat execute actions state).kernel = state.kernel := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      calc
        (run heartbeat execute (action :: rest) state).kernel =
            (run heartbeat execute rest
              (step heartbeat execute state action)).kernel := rfl
        _ = (step heartbeat execute state action).kernel :=
          ih (step heartbeat execute state action)
        _ = state.kernel := step_preserves_kernel heartbeat execute state action

/-! ## Exact conservative projections -/

theorem iter_projection {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (actions : List Action) (state : State K) :
    (run heartbeat execute actions state).development =
      IterArchitecture.applyTransformations
        (iterActions actions) state.development := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | select policy =>
          simpa [run, step, iterActions] using
            ih (step heartbeat execute state (.select policy))
      | transform transformation =>
          simpa [run, step, iterActions,
            IterArchitecture.applyTransformations] using
            ih (step heartbeat execute state (.transform transformation))
      | live action =>
          simpa [run, step, iterActions] using
            ih (step heartbeat execute state (.live action))
      | code event =>
          simpa [run, step, iterActions] using
            ih (step heartbeat execute state (.code event))

theorem agent_projection {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (actions : List Action) (state : State K) :
    (run heartbeat execute actions state).life =
      ProtectedPlasticity.lifeRun heartbeat
        (agentActions actions) state.life := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | select policy =>
          simpa [run, step, agentActions] using
            ih (step heartbeat execute state (.select policy))
      | transform transformation =>
          simpa [run, step, agentActions] using
            ih (step heartbeat execute state (.transform transformation))
      | live action =>
          simpa [run, step, agentActions, ProtectedPlasticity.lifeRun] using
            ih (step heartbeat execute state (.live action))
      | code event =>
          simpa [run, step, agentActions] using
            ih (step heartbeat execute state (.code event))

theorem coding_projection {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (actions : List Action) (state : State K) :
    (run heartbeat execute actions state).coding =
      CodingAgent.run execute (codingActions actions) state.coding := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | select policy =>
          simpa [run, step, codingActions] using
            ih (step heartbeat execute state (.select policy))
      | transform transformation =>
          simpa [run, step, codingActions] using
            ih (step heartbeat execute state (.transform transformation))
      | live action =>
          simpa [run, step, codingActions] using
            ih (step heartbeat execute state (.live action))
      | code event =>
          simpa [run, step, codingActions, CodingAgent.run] using
            ih (step heartbeat execute state (.code event))

/-! ## Policy selection and independence -/

theorem selection_is_operational_stutter {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (state : State K) (policy : Policy) :
    let next := step heartbeat execute state (.select policy)
    next.kernel = state.kernel ∧
      next.development = state.development ∧
      next.life = state.life ∧ next.coding = state.coding := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem transform_life_commute {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (state : State K)
    (transformation : IterArchitecture.Transformation)
    (action : ProtectedPlasticity.LifeAction) :
    step heartbeat execute
        (step heartbeat execute state (.transform transformation))
        (.live action) =
      step heartbeat execute
        (step heartbeat execute state (.live action))
        (.transform transformation) := by
  rfl

theorem transform_coding_commute {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (state : State K)
    (transformation : IterArchitecture.Transformation)
    (event : CodingAgent.Event) :
    step heartbeat execute
        (step heartbeat execute state (.transform transformation))
        (.code event) =
      step heartbeat execute
        (step heartbeat execute state (.code event))
        (.transform transformation) := by
  rfl

theorem life_coding_commute {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (state : State K)
    (action : ProtectedPlasticity.LifeAction)
    (event : CodingAgent.Event) :
    step heartbeat execute
        (step heartbeat execute state (.live action))
        (.code event) =
      step heartbeat execute
        (step heartbeat execute state (.code event))
        (.live action) := by
  rfl

/-! ## The fused step is an ordinary weak-core extension -/

def hostedAction {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (action : Action) :
    State K → Outcome (State K) :=
  hostTransformation (fun state => step heartbeat execute state action)

theorem fused_action_is_hosted_by_weak_core {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (state : State K) (action : Action) :
    resolve state (hostedAction heartbeat execute action state) =
      step heartbeat execute state action := by
  rfl

/-! ## Process-core executable normal form

The executable kernel does not even name the three policies.  It protects an
abstract root and lets a process replace the entire periphery on success.
Agent, Iter, and Coding state—and policy selection itself—are merely one
possible periphery representation supplied by an adapter.
-/

structure Periphery where
  development : IterArchitecture.Boundary
  life : ProtectedPlasticity.Living
  coding : CodingAgent.State
  active : Policy
deriving Repr, DecidableEq

structure Rooted (K : Type) where
  root : K
  periphery : Periphery
deriving Repr, DecidableEq

def pack {K : Type} (state : State K) : Rooted K :=
  ⟨state.kernel,
    ⟨state.development, state.life, state.coding, state.active⟩⟩

/-- The whole cognitive process kernel: accept every successful periphery and
treat failure as a stuttering step. -/
def processStep {K : Type} (state : Rooted K) :
    Outcome Periphery → Rooted K
  | .success next => { state with periphery := next }
  | .failure => state

abbrev Process := Periphery → Outcome Periphery

/-- A process sees and may replace all plastic state, but receives no root
coordinate to rewrite. -/
def invoke {K : Type} (state : Rooted K) (process : Process) : Rooted K :=
  processStep state (process state.periphery)

def processRun {K : Type} :
    List (Outcome Periphery) → Rooted K → Rooted K
  | [], state => state
  | outcome :: rest, state => processRun rest (processStep state outcome)

theorem failed_process_is_transactional {K : Type} (state : Rooted K) :
    processStep state .failure = state := by
  rfl

theorem every_successful_periphery_is_admitted {K : Type}
    (state : Rooted K) (target : Periphery) :
    processStep state (.success target) = { state with periphery := target } := by
  rfl

theorem process_step_preserves_root {K : Type} (state : Rooted K)
    (outcome : Outcome Periphery) :
    (processStep state outcome).root = state.root := by
  cases outcome <;> rfl

theorem process_run_preserves_root {K : Type}
    (outcomes : List (Outcome Periphery)) (state : Rooted K) :
    (processRun outcomes state).root = state.root := by
  induction outcomes generalizing state with
  | nil => rfl
  | cons outcome rest ih =>
      calc
        (processRun (outcome :: rest) state).root =
            (processRun rest (processStep state outcome)).root := rfl
        _ = (processStep state outcome).root := ih (processStep state outcome)
        _ = state.root := process_step_preserves_root state outcome

theorem invoke_preserves_root {K : Type} (state : Rooted K)
    (process : Process) :
    (invoke state process).root = state.root := by
  exact process_step_preserves_root state (process state.periphery)

/-- Any constitutive property—including a universal-care interpretation—is
preserved parametrically.  The kernel need not know or rank values itself. -/
theorem every_root_property_is_invariant {K : Type}
    (Good : K → Prop) (outcomes : List (Outcome Periphery)) (state : Rooted K)
    (good : Good state.root) :
    Good (processRun outcomes state).root := by
  rwa [process_run_preserves_root]

/-! ### Semantic minimality

This is a uniqueness result, not a claim about source-code size.  The contract
has only two equations: admit every successful periphery without changing the
root, and make failure a stutter.  Root preservation is derived rather than
added as a third condition.
-/

abbrev Runner (K : Type) := Rooted K → Outcome Periphery → Rooted K

def ProcessContract {K : Type} (runner : Runner K) : Prop :=
  (∀ state target, runner state (.success target) =
    { state with periphery := target }) ∧
  (∀ state, runner state .failure = state)

theorem process_step_satisfies_contract {K : Type} :
    ProcessContract (@processStep K) := by
  exact ⟨fun _ _ => rfl, fun _ => rfl⟩

theorem contract_implies_root_preservation {K : Type}
    (runner : Runner K) (contract : ProcessContract runner)
    (state : Rooted K) (outcome : Outcome Periphery) :
    (runner state outcome).root = state.root := by
  cases outcome with
  | success target => rw [contract.1 state target]
  | failure => rw [contract.2 state]

/-- The weak process kernel adds no behavior beyond the contract.  Any other
runner with the same protection, plasticity, and failure laws is extensionally
equal to it. -/
theorem process_step_is_unique_contract_runner {K : Type}
    (runner : Runner K) (contract : ProcessContract runner) :
    runner = @processStep K := by
  funext state outcome
  cases outcome with
  | success target => exact contract.1 state target
  | failure => exact contract.2 state

/-- A source action is evaluated by its policy adapter, producing one new
periphery candidate.  No source-specific branch is added to `processStep`. -/
def compileOutcome {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (state : State K) (action : Action) :
    Outcome Periphery :=
  let next := step heartbeat execute state action
  .success ⟨next.development, next.life, next.coding, next.active⟩

theorem process_step_refines_source {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (state : State K) (action : Action) :
    processStep (pack state)
        (compileOutcome heartbeat execute state action) =
      pack (step heartbeat execute state action) := by
  cases action <;> rfl

/-- Compile a source trace while threading the state observed by each policy
adapter. -/
def compileTrace {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) :
    List Action → State K → List (Outcome Periphery)
  | [], _ => []
  | action :: rest, state =>
      compileOutcome heartbeat execute state action ::
        compileTrace heartbeat execute rest
          (step heartbeat execute state action)

/-- Running the tiny process kernel over compiled candidates reaches exactly
the fused source runner's final state for every mixed trace. -/
theorem process_run_refines_source {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (actions : List Action) (state : State K) :
    processRun (compileTrace heartbeat execute actions state) (pack state) =
      pack (run heartbeat execute actions state) := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      simp only [compileTrace, processRun, run]
      rw [process_step_refines_source]
      exact ih (step heartbeat execute state action)

/-- The generic process runner conservatively preserves Iter semantics. -/
theorem process_iter_projection {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (actions : List Action) (state : State K) :
    (processRun (compileTrace heartbeat execute actions state)
      (pack state)).periphery.development =
        IterArchitecture.applyTransformations
          (iterActions actions) state.development := by
  rw [process_run_refines_source]
  exact iter_projection heartbeat execute actions state

/-- The generic process runner conservatively preserves the living-agent
semantics, including its heartbeat parameter. -/
theorem process_agent_projection {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (actions : List Action) (state : State K) :
    (processRun (compileTrace heartbeat execute actions state)
      (pack state)).periphery.life =
        ProtectedPlasticity.lifeRun heartbeat
          (agentActions actions) state.life := by
  rw [process_run_refines_source]
  exact agent_projection heartbeat execute actions state

/-- The generic process runner conservatively preserves CodingAgent
request/broker/evidence semantics. -/
theorem process_coding_projection {K : Type} (heartbeat : Nat)
    (execute : CodingAgent.Executor) (actions : List Action) (state : State K) :
    (processRun (compileTrace heartbeat execute actions state)
      (pack state)).periphery.coding =
        CodingAgent.run execute (codingActions actions) state.coding := by
  rw [process_run_refines_source]
  exact coding_projection heartbeat execute actions state

end ThreePolicyFusion

/-! ## Axiom audit -/

#print axioms ThreePolicyFusion.run_preserves_kernel
#print axioms ThreePolicyFusion.iter_projection
#print axioms ThreePolicyFusion.agent_projection
#print axioms ThreePolicyFusion.coding_projection
#print axioms ThreePolicyFusion.selection_is_operational_stutter
#print axioms ThreePolicyFusion.transform_life_commute
#print axioms ThreePolicyFusion.transform_coding_commute
#print axioms ThreePolicyFusion.life_coding_commute
#print axioms ThreePolicyFusion.fused_action_is_hosted_by_weak_core
#print axioms ThreePolicyFusion.failed_process_is_transactional
#print axioms ThreePolicyFusion.process_run_preserves_root
#print axioms ThreePolicyFusion.every_root_property_is_invariant
#print axioms ThreePolicyFusion.process_step_is_unique_contract_runner
#print axioms ThreePolicyFusion.process_step_refines_source
#print axioms ThreePolicyFusion.process_run_refines_source
#print axioms ThreePolicyFusion.process_iter_projection
#print axioms ThreePolicyFusion.process_agent_projection
#print axioms ThreePolicyFusion.process_coding_projection
