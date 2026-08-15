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
