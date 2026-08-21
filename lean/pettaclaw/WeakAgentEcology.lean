import OpenEndedProcessCore
import ContextProjection

/-!
# WeakAgentEcology — one weak runner, an open ecology of agent policies

The ordinary kernel remains the two-equation process runner:

* a successful process replaces the plastic periphery; and
* a failed process is a stuttering step.

Agent, Iter, and Coding are not kernel cases.  They are replaceable policies
in an open ecology.  A policy may inspect a context selected from the event
history and propose an arbitrary next working state.  The selected policy,
the context selector, the policy table, and all working memory are themselves
plastic data.

This file proves four claims needed before simplifying the runtime:

1. arbitrary history-sensitive controllers and context selectors are hostable;
2. policies can be replaced, composed, selected, or added without changing the
   runner;
3. the existing Agent/Iter/Coding source semantics embed exactly; and
4. deleting either success replacement or failure stutter loses a stated
   desideratum.

No scheduler, memory format, retrieval method, mode catalogue, evaluator, or
effect policy is fixed here.  Physical external effects are outside the
transactional claim: a process must represent a proposed effect as plastic
data if it needs rollback before emission.
-/

namespace WeakAgentEcology

open WeakSelfHostingCore

abbrev Rooted (Root Periphery : Type) :=
  OpenEndedProcessCore.State Root Periphery

abbrev Process (Periphery : Type) :=
  OpenEndedProcessCore.Process Periphery

/-! ## A locally transactional process ecology -/

/-- Run replaceable processes in order.  Each process is committed through the
same two-equation runner before the next process observes the periphery. -/
def runProcesses {Root Periphery : Type} :
    List (Process Periphery) → Rooted Root Periphery → Rooted Root Periphery
  | [], state => state
  | process :: rest, state =>
      runProcesses rest (OpenEndedProcessCore.invoke state process)

theorem runProcesses_append {Root Periphery : Type}
    (left right : List (Process Periphery)) (state : Rooted Root Periphery) :
    runProcesses (left ++ right) state =
      runProcesses right (runProcesses left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons process rest ih =>
      simp only [List.cons_append, runProcesses]
      exact ih (OpenEndedProcessCore.invoke state process)

theorem runProcesses_preserves_root {Root Periphery : Type}
    (processes : List (Process Periphery)) (state : Rooted Root Periphery) :
    (runProcesses processes state).root = state.root := by
  induction processes generalizing state with
  | nil => rfl
  | cons process rest ih =>
      exact (ih (OpenEndedProcessCore.invoke state process)).trans
        (OpenEndedProcessCore.ordinary_processes_preserve_the_current_root
          state process)

def failingProcess {Periphery : Type} : Process Periphery :=
  fun _ => .failure

theorem failed_process_is_local_stutter {Root Periphery : Type}
    (state : Rooted Root Periphery) :
    OpenEndedProcessCore.invoke state
      (failingProcess : Process Periphery) = state := by
  rfl

/-- A failed extension may be inserted or removed from a process history
without changing its result. -/
theorem failed_process_erases_from_trace {Root Periphery : Type}
    (left right : List (Process Periphery))
    (state : Rooted Root Periphery) :
    runProcesses (left ++ failingProcess :: right) state =
      runProcesses (left ++ right) state := by
  rw [runProcesses_append, runProcesses_append]
  rfl

def hostChange {Periphery : Type} (change : Periphery → Periphery) :
    Process Periphery :=
  fun before => .success (change before)

theorem every_periphery_change_is_hostable {Root Periphery : Type}
    (change : Periphery → Periphery) (state : Rooted Root Periphery) :
    OpenEndedProcessCore.invoke state (hostChange change) =
      { state with periphery := change state.periphery } := by
  rfl

/-- Ordered composition remains observable outside the kernel.  The runner
does not impose commutativity on living processes. -/
theorem process_order_is_expressive :
    let state : Rooted Unit Nat := ⟨(), 1⟩
    let increment : Process Nat := hostChange (fun value => value + 1)
    let double : Process Nat := hostChange (fun value => value * 2)
    runProcesses [increment, double] state ≠
      runProcesses [double, increment] state := by
  simp [runProcesses, hostChange, OpenEndedProcessCore.invoke,
    OpenEndedProcessCore.step]

/-! ## Context is a replaceable policy, not a kernel coordinate -/

abbrev ContextPolicy (Event Context : Type) :=
  ContextProjection.ContextPolicy Event Context

abbrev Controller (Context Periphery : Type) :=
  Context → Periphery → Outcome Periphery

def contextualProcess {Event Context Periphery : Type}
    (select : ContextPolicy Event Context) (history : List Event)
    (controller : Controller Context Periphery) : Process Periphery :=
  fun before => controller (select history) before

def turn {Root Event Context Periphery : Type}
    (state : Rooted Root Periphery)
    (select : ContextPolicy Event Context) (history : List Event)
    (controller : Controller Context Periphery) : Rooted Root Periphery :=
  OpenEndedProcessCore.invoke state
    (contextualProcess select history controller)

theorem contextual_turn_preserves_root
    {Root Event Context Periphery : Type}
    (state : Rooted Root Periphery)
    (select : ContextPolicy Event Context) (history : List Event)
    (controller : Controller Context Periphery) :
    (turn state select history controller).root = state.root := by
  exact OpenEndedProcessCore.ordinary_processes_preserve_the_current_root
    state (contextualProcess select history controller)

theorem failed_contextual_turn_stutters
    {Root Event Context Periphery : Type}
    (state : Rooted Root Periphery)
    (select : ContextPolicy Event Context) (history : List Event)
    (controller : Controller Context Periphery)
    (failed : controller (select history) state.periphery = .failure) :
    turn state select history controller = state := by
  simp [turn, contextualProcess, OpenEndedProcessCore.invoke, failed,
    OpenEndedProcessCore.step]

def identityContext {Event : Type} : ContextPolicy Event (List Event) :=
  fun history => history

/-- Any history-sensitive agent transition factors through the context
interface.  Choosing the identity projection witnesses full expressiveness;
smaller projections are optimizations, not kernel obligations. -/
theorem every_history_sensitive_agent_is_hostable
    {Root Event Periphery : Type}
    (state : Rooted Root Periphery) (history : List Event)
    (agent : List Event → Periphery → Outcome Periphery) :
    turn state identityContext history agent =
      OpenEndedProcessCore.invoke state (agent history) := by
  rfl

theorem equal_selected_contexts_are_operationally_indistinguishable
    {Root Event Context Periphery : Type}
    (state : Rooted Root Periphery) (history : List Event)
    (left right : ContextPolicy Event Context)
    (controller : Controller Context Periphery)
    (same : left history = right history) :
    turn state left history controller = turn state right history controller := by
  unfold turn contextualProcess
  rw [same]

def frontierContext {Event Context : Type}
    (select : ContextPolicy Event Context) (frontier : Nat) :
    ContextPolicy Event Context :=
  fun history => select (history.take frontier)

/-- A request projected from a fixed causal prefix is unchanged by events
that arrive after that prefix. -/
theorem future_events_do_not_change_started_turn
    {Root Event Context Periphery : Type}
    (state : Rooted Root Periphery)
    (select : ContextPolicy Event Context) (controller : Controller Context Periphery)
    (past future : List Event) (frontier : Nat)
    (within : frontier ≤ past.length) :
    turn state (frontierContext select frontier) (past ++ future) controller =
      turn state (frontierContext select frontier) past controller := by
  unfold turn contextualProcess frontierContext
  rw [ContextProjection.take_append_before_boundary past future frontier within]

/-! The open context interface can supply information that the reference Iter
request surface leaves to tools and transformations once its aggregate memory
budget is exceeded. -/

def memoryContentContext
    (artifacts : List IterArchitecture.MemoryArtifact) : List Nat :=
  artifacts.flatMap IterArchitecture.MemoryArtifact.content

theorem replaceable_context_can_observe_memory_content
    (leftContent rightContent : List Nat)
    (different : leftContent ≠ rightContent)
    (leftLarge : IterArchitecture.maxMemoryChars < leftContent.length)
    (rightLarge : IterArchitecture.maxMemoryChars < rightContent.length) :
    let left : List IterArchitecture.MemoryArtifact :=
      [⟨7, leftContent⟩]
    let right : List IterArchitecture.MemoryArtifact :=
      [⟨7, rightContent⟩]
    IterArchitecture.memorySurface left = IterArchitecture.memorySurface right ∧
      memoryContentContext left ≠ memoryContentContext right := by
  dsimp
  constructor
  · exact (IterArchitecture.large_memory_contents_are_not_automatically_visible
      leftContent rightContent different leftLarge rightLarge).2
  · simpa [memoryContentContext] using different

/-! ## An open, self-replaceable policy ecology -/

/-- The table is open in `Name`; three conventional names are one
instantiation, not a closed kernel enumeration. -/
structure Ecology (Name Event Context Working : Type) where
  active : Name
  context : ContextPolicy Event Context
  policies : Name → Controller Context Working
  working : Working

def selectPolicy {Name Event Context Working : Type}
    (selected : Name) : Process (Ecology Name Event Context Working) :=
  hostChange (fun ecology => { ecology with active := selected })

def installContext {Name Event Context Working : Type}
    (select : ContextPolicy Event Context) :
    Process (Ecology Name Event Context Working) :=
  hostChange (fun ecology => { ecology with context := select })

def installPolicy {Name Event Context Working : Type} [DecidableEq Name]
    (selected : Name) (controller : Controller Context Working) :
    Process (Ecology Name Event Context Working) :=
  hostChange (fun ecology =>
    { ecology with
      policies := fun name =>
        if name = selected then controller else ecology.policies name })

/-- Execute whichever policy is selected.  A failed policy returns failure to
the same weak runner, so the entire ecology remains unchanged. -/
def runSelected {Name Event Context Working : Type}
    (history : List Event) : Process (Ecology Name Event Context Working) :=
  fun ecology =>
    match ecology.policies ecology.active (ecology.context history)
        ecology.working with
    | .success next => .success { ecology with working := next }
    | .failure => .failure

theorem selection_changes_no_policy_or_work
    {Root Name Event Context Working : Type}
    (state : Rooted Root (Ecology Name Event Context Working))
    (selected : Name) :
    let next := OpenEndedProcessCore.invoke state (selectPolicy selected)
    next.periphery.context = state.periphery.context ∧
      next.periphery.policies = state.periphery.policies ∧
      next.periphery.working = state.periphery.working := by
  exact ⟨rfl, rfl, rfl⟩

theorem arbitrary_context_policy_is_replaceable
    {Root Name Event Context Working : Type}
    (state : Rooted Root (Ecology Name Event Context Working))
    (select : ContextPolicy Event Context) :
    (OpenEndedProcessCore.invoke state
      (installContext select)).periphery.context = select := by
  rfl

theorem arbitrary_named_policy_is_installable
    {Root Name Event Context Working : Type} [DecidableEq Name]
    (state : Rooted Root (Ecology Name Event Context Working))
    (selected : Name) (controller : Controller Context Working) :
    (OpenEndedProcessCore.invoke state
      (installPolicy selected controller)).periphery.policies selected =
        controller := by
  simp [OpenEndedProcessCore.invoke, installPolicy, hostChange,
    OpenEndedProcessCore.step]

theorem failed_selected_policy_stutters
    {Root Name Event Context Working : Type}
    (state : Rooted Root (Ecology Name Event Context Working))
    (history : List Event)
    (failed : state.periphery.policies state.periphery.active
      (state.periphery.context history) state.periphery.working = .failure) :
    OpenEndedProcessCore.invoke state (runSelected history) = state := by
  simp [OpenEndedProcessCore.invoke, runSelected, failed,
    OpenEndedProcessCore.step]

/-- Local composition gives each component Iter-style failure isolation: a
failed component contributes a stutter and the next component still runs. -/
def composeControllers {Context Working : Type}
    (left right : Controller Context Working) : Controller Context Working :=
  fun context before =>
    let middle := resolve before (left context before)
    .success (resolve middle (right context middle))

theorem composed_controller_has_local_failure_stutter
    {Context Working : Type}
    (left right : Controller Context Working) (context : Context)
    (before : Working) (leftFails : left context before = .failure) :
    composeControllers left right context before =
      .success (resolve before (right context before)) := by
  simp [composeControllers, leftFails, resolve]

theorem arbitrary_composite_policy_is_installable
    {Root Name Event Context Working : Type} [DecidableEq Name]
    (state : Rooted Root (Ecology Name Event Context Working))
    (selected : Name) (left right : Controller Context Working) :
    (OpenEndedProcessCore.invoke state
      (installPolicy selected (composeControllers left right))).periphery.policies
        selected = composeControllers left right := by
  exact arbitrary_named_policy_is_installable state selected
    (composeControllers left right)

/-! ## Exact hosting of the existing three source policies -/

/-- The already-proved three-policy adapter is one ecology working state. -/
abbrev ThreeWorking := ThreePolicyFusion.Periphery

/-- Existing projection theorems pass directly through the generic weak
runner.  This section names the result at the ecology boundary; it adds no
fourth source semantics. -/
theorem weak_runner_preserves_iter
    {K : Type} (heartbeat : Nat) (execute : CodingAgent.Executor)
    (actions : List ThreePolicyFusion.Action) (state : ThreePolicyFusion.State K) :
    (ThreePolicyFusion.processRun
      (ThreePolicyFusion.compileTrace heartbeat execute actions state)
      (ThreePolicyFusion.pack state)).periphery.development =
        IterArchitecture.applyTransformations
          (ThreePolicyFusion.iterActions actions) state.development := by
  exact ThreePolicyFusion.process_iter_projection heartbeat execute actions state

theorem weak_runner_preserves_agent
    {K : Type} (heartbeat : Nat) (execute : CodingAgent.Executor)
    (actions : List ThreePolicyFusion.Action) (state : ThreePolicyFusion.State K) :
    (ThreePolicyFusion.processRun
      (ThreePolicyFusion.compileTrace heartbeat execute actions state)
      (ThreePolicyFusion.pack state)).periphery.life =
        ProtectedPlasticity.lifeRun heartbeat
          (ThreePolicyFusion.agentActions actions) state.life := by
  exact ThreePolicyFusion.process_agent_projection heartbeat execute actions state

theorem weak_runner_preserves_coding
    {K : Type} (heartbeat : Nat) (execute : CodingAgent.Executor)
    (actions : List ThreePolicyFusion.Action) (state : ThreePolicyFusion.State K) :
    (ThreePolicyFusion.processRun
      (ThreePolicyFusion.compileTrace heartbeat execute actions state)
      (ThreePolicyFusion.pack state)).periphery.coding =
        CodingAgent.run execute
          (ThreePolicyFusion.codingActions actions) state.coding := by
  exact ThreePolicyFusion.process_coding_projection heartbeat execute actions state

/-! Agent is not an alias for Iter.  It contributes living distinctions that
the current reference Iter control loop erases or does not persist. -/

theorem agent_contributes_distinctions_absent_from_reference_iter
    (pace : IterArchitecture.Pace)
    (working : PresentMoment.Working)
    (within : working.lastResults.length ≤ PresentMoment.cap) :
    IterArchitecture.beginCycle pace (some .human) =
        IterArchitecture.beginCycle pace (some .sibling) ∧
      (Claws.wakeMax 60 ⟨5, 0⟩ (.human 10)).1 ≠
        (Claws.wake 60 ⟨5, 0⟩ .work).1 ∧
      (IterArchitecture.finishCycle pace false true).2 = .slow ∧
      (Claws.wake 60 ⟨5, 0⟩ .rest).1.energy = 0 ∧
      PresentMoment.resetH working = working := by
  exact ⟨IterArchitecture.event_origins_indistinguishable pace .human .sibling,
    IterArchitecture.pettaclaw_is_origin_sensitive,
    (IterArchitecture.nop_is_not_stable_rest pace).1,
    IterArchitecture.pettaclaw_rest_zeroes_current_burst,
    IterArchitecture.pettaclaw_healthy_restart_preserves_present_moment
      working within⟩

/-! ## Iter is preserved as a process family, not privileged as the kernel -/

def fromIter (transformation : IterArchitecture.Transformation) :
    Process IterArchitecture.Boundary :=
  fun boundary =>
    match transformation boundary with
    | some next => .success next
    | none => .failure

theorem one_iter_process_is_exact {Root : Type}
    (root : Root) (boundary : IterArchitecture.Boundary)
    (transformation : IterArchitecture.Transformation) :
    OpenEndedProcessCore.invoke
      ({ root := root, periphery := boundary } : Rooted Root IterArchitecture.Boundary)
      (fromIter transformation) =
        ({ root := root
           periphery := IterArchitecture.applyTransformation boundary transformation } :
          Rooted Root IterArchitecture.Boundary) := by
  cases result : transformation boundary <;>
    simp [OpenEndedProcessCore.invoke, fromIter,
      IterArchitecture.applyTransformation, result, OpenEndedProcessCore.step]

theorem one_iter_transformation_is_exact {Root : Type}
    (root : Root) (boundary : IterArchitecture.Boundary)
    (transformation : IterArchitecture.Transformation) :
    (OpenEndedProcessCore.invoke
      ({ root := root, periphery := boundary } : Rooted Root IterArchitecture.Boundary)
      (fromIter transformation)).periphery =
        IterArchitecture.applyTransformation boundary transformation := by
  rw [one_iter_process_is_exact]

theorem iter_pipeline_is_exact {Root : Type}
    (root : Root) (boundary : IterArchitecture.Boundary)
    (transformations : List IterArchitecture.Transformation) :
    (runProcesses (transformations.map fromIter)
      ({ root := root, periphery := boundary } :
        Rooted Root IterArchitecture.Boundary)).periphery =
        IterArchitecture.applyTransformations transformations boundary := by
  induction transformations generalizing boundary with
  | nil => rfl
  | cons transformation rest ih =>
      simp only [List.map_cons, runProcesses,
        IterArchitecture.applyTransformations]
      rw [one_iter_process_is_exact]
      exact ih (IterArchitecture.applyTransformation boundary transformation)

/-! ## Semantic minimality by uniqueness and erasure -/

theorem weak_runner_is_unique
    {Root Periphery : Type}
    (runner : OpenEndedProcessCore.Runner Root Periphery)
    (contract : OpenEndedProcessCore.Contract runner) :
    runner = @OpenEndedProcessCore.step Root Periphery := by
  exact OpenEndedProcessCore.step_is_unique_contract_runner runner contract

def frozenRunner {Periphery : Type}
    (before : Periphery) (_ : Outcome Periphery) : Periphery :=
  before

theorem erasing_success_replacement_loses_plasticity :
    frozenRunner false (.success true) ≠ true := by
  decide

def destructiveFailureRunner {Periphery : Type}
    (fallback : Periphery) (_before : Periphery) : Outcome Periphery → Periphery
  | .success next => next
  | .failure => fallback

theorem erasing_failure_stutter_loses_recovery :
    destructiveFailureRunner false true .failure ≠ true := by
  decide

end WeakAgentEcology

/-! ## Axiom audit -/

#print axioms WeakAgentEcology.runProcesses_append
#print axioms WeakAgentEcology.failed_process_erases_from_trace
#print axioms WeakAgentEcology.every_history_sensitive_agent_is_hostable
#print axioms WeakAgentEcology.future_events_do_not_change_started_turn
#print axioms WeakAgentEcology.replaceable_context_can_observe_memory_content
#print axioms WeakAgentEcology.arbitrary_context_policy_is_replaceable
#print axioms WeakAgentEcology.arbitrary_named_policy_is_installable
#print axioms WeakAgentEcology.failed_selected_policy_stutters
#print axioms WeakAgentEcology.arbitrary_composite_policy_is_installable
#print axioms WeakAgentEcology.weak_runner_preserves_iter
#print axioms WeakAgentEcology.weak_runner_preserves_agent
#print axioms WeakAgentEcology.weak_runner_preserves_coding
#print axioms WeakAgentEcology.agent_contributes_distinctions_absent_from_reference_iter
#print axioms WeakAgentEcology.iter_pipeline_is_exact
#print axioms WeakAgentEcology.weak_runner_is_unique
#print axioms WeakAgentEcology.erasing_success_replacement_loses_plasticity
#print axioms WeakAgentEcology.erasing_failure_stutter_loses_recovery
