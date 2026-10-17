import Mettapedia.Languages.MeTTa.HE.RecursiveTasks
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Executable retained control for recursive HE evaluation

Each advance enters one request or consumes one first-order continuation.
Recursive evaluator calls become retained requests. Selected head values and
their bindings are used by the remaining branch without evaluating that head
again. Matching, type checks and grounded dispatch retain their own coarser
granularity. Successful evaluation is drained as ordered result occurrences.
-/

open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory (aliasConstraints)

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveMachine

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Expansion does not call any of the six recursive evaluator functions. -/
def enter (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (lookup : TypeLookup := rawTypeLookup space) : Control × List Frame :=
  match task with
  | .atom _ _ _ 0 _ => (.returning [], [])
  | .atom value expected bindings (n + 1) live =>
      if isEmptyOrError value then (.returning [(value, bindings)], [])
      else if expected == Atom.atomType || expected == getMetaType value ||
          getMetaType value == Atom.variableType then (.returning [(value, bindings)], [])
      else if getMetaType value == Atom.symbolType || getMetaType value == Atom.groundedType ||
          value == Atom.unit then (.returning (typeCast value expected space bindings n lookup), [])
      else if getMetaType value == Atom.expressionType then
        (.work (.expression value expected bindings n live), [.filter])
      else (.returning [(value, bindings)], [])
  | .expression _ _ _ 0 _ => (.returning [], [])
  | .expression value expected bindings (n + 1) live =>
      match value with
      | .expression (operator :: _) =>
          let types := lookup bindings operator expected
          let continuation :=
            if types.any (fun type => !isFunctionType type || type == Atom.undefinedType)
            then Frame.append (.tupleCalls value expected bindings n live)
            else .fallback value expected bindings n types
          (.work (.functions value expected bindings n types live), [continuation])
      | _ => (.returning [], [])
  | .func _ _ _ 0 _ => (.returning [], [])
  | .func value operatorType bindings (n + 1) live =>
      match value with
      | .expression (operator :: arguments) =>
          (.work (.atom operator operatorType bindings n (operatorType :: arguments ++ live)),
            [.heads operatorType arguments n live])
      | _ => (.returning [], [])
  | .args _ _ _ 0 _ => (.returning [], [])
  | .args values types bindings (n + 1) live =>
      match values, types with
      | [], [] => (.returning [(argumentPacket [], bindings)], [])
      | value :: remaining, type :: remainingTypes =>
          (.work (.atom value type bindings n (remaining ++ remainingTypes ++ live)),
            [.argumentHeads value remaining remainingTypes n live])
      | _, _ => (.returning [], [])
  | .tuple _ _ 0 _ => (.returning [], [])
  | .tuple value bindings (n + 1) live =>
      match value with
      | .expression [] => (.returning [(Atom.unit, bindings)], [])
      | .expression [single] =>
          (.work (.atom single Atom.undefinedType bindings n live), [.tupleSingleton])
      | .expression (head :: second :: remaining) =>
          (.work (.atom head Atom.undefinedType bindings n
              (.expression (second :: remaining) :: live)),
            [.tupleHeads (.expression (second :: remaining)) n live])
      | _ => (.returning [], [])
  | .call value expected bindings fuel live =>
      (.work (.invocation (.ordinary expected) value bindings fuel live), [])
  | .functions _ _ _ _ [] _ => (.returning [], [])
  | .functions value expected bindings fuel (operatorType :: remaining) live =>
      let rest := Frame.append (.functions value expected bindings fuel remaining live)
      if isFunctionType operatorType then
        match checkIfFunctionTypeIsApplicable value operatorType expected space bindings fuel lookup with
        | .inl _ => (.returning [], [rest])
        | .inr alternatives =>
            (.work (.bindingAlternatives value operatorType (resultType operatorType) fuel
              alternatives live), [rest])
      else (.returning [], [rest])
  | .bindingAlternatives _ _ _ _ [] _ => (.returning [], [])
  | .bindingAlternatives value operatorType expected fuel (selected :: remaining) live =>
      (.work (.func value operatorType selected fuel (expected :: live)),
        [.calls expected fuel live,
          .append (.bindingAlternatives value operatorType expected fuel remaining live)])
  | .heads _ _ _ [] _ => (.returning [], [])
  | .heads operatorType arguments fuel ((head, selected) :: remaining) live =>
      let rest := Frame.append (.heads operatorType arguments fuel remaining live)
      if isEmptyOrError head then (.returning [(head, selected)], [rest])
      else match getFunctionArgTypes operatorType with
        | none => (.returning [], [rest])
        | some types =>
            (.work (.args arguments types selected fuel (head :: live)), [.functionTail head, rest])
  | .argumentHeads _ _ _ _ [] _ => (.returning [], [])
  | .argumentHeads original remaining types fuel ((head, selected) :: alternatives) live =>
      let rest := Frame.append (.argumentHeads original remaining types fuel alternatives live)
      if head != original && isEmptyOrError head then (.returning [(head, selected)], [rest])
      else (.work (.args remaining types selected fuel (head :: live)), [.argumentTail head, rest])
  | .tupleHeads _ _ [] _ => (.returning [], [])
  | .tupleHeads tail fuel ((head, selected) :: remaining) live =>
      let rest := Frame.append (.tupleHeads tail fuel remaining live)
      if isEmptyOrError head then (.returning [(head, selected)], [rest])
      else (.work (.tuple tail selected fuel (head :: live)), [.tupleTail head, rest])
  | .calls _ _ [] _ => (.returning [], [])
  | .calls expected fuel ((value, bindings) :: remaining) live =>
      (.work (.call value expected bindings fuel live),
        [.append (.calls expected fuel remaining live)])
  | .atoms _ _ [] _ => (.returning [], [])
  | .atoms expected fuel ((value, bindings) :: remaining) live =>
      (.work (.atom value expected bindings fuel live),
        [.append (.atoms expected fuel remaining live)])
  | .returned original value expected bindings fuel live =>
      if value == Atom.notReducible then (.returning [(original, bindings)], [])
      else if isEmptyOrError value then (.returning [(value, bindings)], [])
      else (.work (.atom value expected bindings fuel live), [])
  | .returns _ _ _ [] _ => (.returning [], [])
  | .returns original expected fuel ((value, bindings) :: remaining) live =>
      (.work (.returned original value expected bindings fuel live),
        [.append (.returns original expected fuel remaining live)])
  | .equations _ _ _ _ [] _ => (.returning [], [])
  | .equations original expected incoming fuel ((rhs, selected) :: remaining) live =>
      let alternatives := (mergeBindings selected (aliasConstraints incoming) fuel).filterMap fun merged =>
        if merged.hasLoop then none else some (merged.applyFull rhs fuel, merged)
      (.returning alternatives,
        [.append (.equations original expected incoming fuel remaining live)])
  | .grounded _ _ _ _ [] _ => (.returning [], [])
  | .grounded original expected incoming fuel ((value, selected) :: remaining) live =>
      (.returning ((mergeBindings selected incoming fuel).map fun merged =>
          (merged.applyFull value fuel, merged)),
        [.append (.grounded original expected incoming fuel remaining live)])
  | .tupleCalls value expected bindings fuel live =>
      (.work (.tuple value bindings fuel (expected :: live)), [.calls expected fuel live])
  | .invocation _ _ _ 0 _ _ => (.returning [], [])
  | .invocation mode value bindings (n + 1) live caller =>
      if mode.errorPassthrough value then
        (.returning [(value, bindings)], [])
      else match value with
      | .expression (operator :: arguments) =>
        if dispatch.isExecutable operator then
          match dispatch.execute operator arguments with
          | .ok results =>
              (.work (.grounded value mode.expected bindings n results live),
                [.producerResults mode value bindings n live Atom.empty])
          | .runtimeError message =>
              (.returning [(Atom.error value (.symbol message), bindings)],
                [.invocationReturn mode value n live])
          | .noReduce | .incorrectArgument =>
              (.returning [(Atom.notReducible, bindings)], [.invocationReturn mode value n live])
        else if minimalInstruction value then
          (.work (.minimal value bindings n (mode.pendingScope live) caller),
            [.invocationReturn mode value n live])
        else
          (.work (.equations value mode.expected bindings n
            (queryEquationsAvoiding (equationScope live value mode.expected bindings) space value n) live),
              [.producerResults mode value bindings n live Atom.notReducible])
      | _ =>
          (.work (.equations value mode.expected bindings n
            (queryEquationsAvoiding (equationScope live value mode.expected bindings) space value n) live),
              [.producerResults mode value bindings n live Atom.notReducible])
  | .produced _ _ 0 _ _ _ => (.returning [], [])
  | .produced value bindings (n + 1) live caller provenance =>
      if provenance == .completed then (.returning [(value, bindings)], []) else
      match value with
      | .expression [.symbol "function", _] => (.work (.primitive value bindings n live caller), [])
      | _ => (.returning [(value, bindings)], [])
  | .productions _ [] _ _ _ => (.returning [], [])
  | .productions fuel ((value, bindings) :: remaining) live caller provenance =>
      (.work (.produced value bindings fuel live caller provenance),
        [.append (.productions fuel remaining live caller provenance)])
  | .minimal _ _ 0 _ _ => (.returning [], [])
  | .minimal value bindings (n + 1) live caller =>
      if minimalInstruction value then
        match value with
        | .expression (.symbol "chain" :: _) =>
            (.work (.primitive value bindings n live caller), [.minimalResults n live caller])
        | _ => (.work (.primitive value bindings n live caller), [])
      else (.returning [(value, bindings)], [])
  | .minimals _ [] _ _ => (.returning [], [])
  | .minimals fuel ((value, bindings) :: remaining) live caller =>
      (.work (.minimal value bindings fuel live caller), [.append (.minimals fuel remaining live caller)])
  | .primitive _ _ 0 _ _ => (.returning [], [])
  | .primitive value bindings (n + 1) live caller =>
      match value with
      | .expression [.symbol "eval", atom] =>
          (.work (.invocation .raw (bindings.applyFull atom n) bindings n live caller), [])
      | .expression [.symbol "chain", atom, .var name, template] =>
          (.work (.minimal atom bindings n (value :: live) (some value)),
            [.chainResults name template n])
      | .expression [.symbol "unify", target, pattern, yes, no] =>
          let results := unifySuccessResults target pattern yes bindings n
          (.returning (if results.isEmpty then [(no, bindings)] else results), [])
      | .expression (.symbol "unify" :: _) => (.returning [(mkUnifyBadArityError value, bindings)], [])
      | .expression [.symbol "cons-atom", head, .expression tail] =>
          (.returning [(.expression (head :: tail), bindings)], [])
      | .expression [.symbol "decons-atom", .expression (head :: tail)] =>
          (.returning [(.expression [head, .expression tail], bindings)], [])
      | .expression [.symbol "function", body@(.expression _)] =>
          (.work (.functionBody body bindings n (value :: live) (some value)),
            [.functionTerminal caller])
      | _ => (.returning [], [])
  | .chainRows _ _ _ [] => (.returning [], [])
  | .chainRows name template fuel ((value, bindings) :: remaining) =>
      (.returning [(chainSubstitute name (bindings.applyFull value fuel) template, bindings)],
        [.append (.chainRows name template fuel remaining)])
  | .functionBody _ _ 0 _ _ => (.returning [], [])
  | .functionBody value bindings (n + 1) live caller =>
      (.work (.minimal value bindings n live caller), [.bodyResults n live caller])
  | .bodyResults _ [] _ _ => (.returning [], [])
  | .bodyResults fuel ((value, bindings) :: remaining) live caller =>
      let materialized := bindings.applyFull value fuel
      let rest := Frame.append (.bodyResults fuel remaining live caller)
      if minimalInstruction materialized then
        (.work (.functionBody materialized bindings fuel live caller), [rest])
      else (.returning [(materialized, bindings)], [rest])
  | .producerResults mode original incoming fuel live emptyReply results =>
      let returned := Frame.invocationReturn mode original fuel live
      if results.isEmpty then (.returning [(emptyReply, incoming)], [returned])
      else (.work (.productions fuel results (mode.pendingScope live) (some original)), [returned])
  | .completed value expected bindings fuel =>
      (.returning (completedCallReturn space value expected bindings fuel lookup), [])

def resume (space : Space) (frame : Frame) (results : ResultSet)
    (lookup : TypeLookup := rawTypeLookup space) : Control × List Frame :=
  match frame with
  | .filter => (.returning (successPriority results), [])
  | .heads operatorType arguments fuel live =>
      (.work (.heads operatorType arguments fuel results live), [])
  | .argumentHeads original remaining types fuel live =>
      (.work (.argumentHeads original remaining types fuel results live), [])
  | .tupleHeads tail fuel live => (.work (.tupleHeads tail fuel results live), [])
  | .calls expected fuel live => (.work (.calls expected fuel results live), [])
  | .functionTail head => (.returning (RecursiveTasks.functionTail head results), [])
  | .argumentTail head => (.returning (RecursiveTasks.argumentTail head results), [])
  | .tupleSingleton => (.returning (results.map HE.tupleSingleton), [])
  | .tupleTail head => (.returning (RecursiveTasks.tupleTail head results), [])
  | .append remaining => (.work remaining, [.prepend results])
  | .prepend selected => (.returning (selected ++ results), [])
  | .fallback value expected bindings fuel types =>
      (.returning (functionFallback space value expected bindings fuel types results lookup), [])
  | .invocationReturn mode original fuel live =>
      match mode with
      | .raw => (.returning results, [])
      | .ordinary expected => (.work (.returns original expected fuel results live), [])
  | .producerResults mode original incoming fuel live emptyReply =>
      (.work (.producerResults mode original incoming fuel live emptyReply results), [])
  | .minimalResults fuel live caller => (.work (.minimals fuel results live caller), [])
  | .chainResults name template fuel => (.work (.chainRows name template fuel results), [])
  | .functionTerminal caller =>
      (.returning (results.map fun (value, bindings) => (HE.functionTerminal caller value, bindings)), [])
  | .bodyResults fuel live caller => (.work (.bodyResults fuel results live caller), [])

/-- One internal advance, retaining the surrounding continuation and history. -/
def next (dispatch : GroundedDispatch) (state : Configuration) : Option Configuration :=
  match state.control, state.stack with
  | .work task, stack =>
      let entered := enter state.space dispatch task
      some {state with control := entered.1, stack := entered.2 ++ stack}
  | .returning results, frame :: remaining =>
      let resumed := resume state.space frame results
      some {state with control := resumed.1, stack := resumed.2 ++ remaining}
  | .returning _, [] => none

/-- Execute the finite-depth approximation and drain each occurrence once.
An empty approximation is not evidence of completed source-level failure; use
`Checked.machine` when a caller must distinguish exhaustion from completion. -/
def machine (dispatch : GroundedDispatch) : Machine Configuration ResultPair Configuration Empty where
  step state :=
    match next dispatch state with
    | some after => some (.silent after)
    | none => match state.control with
      | .work _ => none
      | .returning [] => some (.finish state)
      | .returning (result :: remaining) =>
          let saved := {state with
            control := .returning remaining
            emitted := state.emitted ++ [result]}
          some (.publish [result] saved)

theorem resume_prefix (dispatch : GroundedDispatch) (state saved : Configuration)
    (first second : Nat) (observed : ResultSet)
    (paused : ((machine dispatch).run first state) = (observed, .exhausted saved)) :
    (machine dispatch).run (first + second) state =
      (observed ++ ((machine dispatch).run second saved).1,
        ((machine dispatch).run second saved).2) :=
  (machine dispatch).established_and_pending first second state saved observed paused

/-! ## Resource-checked retained execution

The earlier machine realizes a finite evaluator approximation. This interface
checks every bounded leaf before consuming its reply. Insufficient evaluator
or leaf depth suspends the retained request; it is never an empty answer.
-/

namespace Checked

inductive ResourceRequest where
  | evaluationDepth
  | leafDepth
  | primitiveService (instruction : Atom)
  deriving DecidableEq, Repr

/-- All bounded operations which this request will execute have coverage.
Recursive evaluator calls are checked when their own retained request is entered. -/
def taskReady (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (lookup : TypeLookup := rawTypeLookup space) : Bool :=
  match task with
  | .atom _ _ _ 0 _ | .expression _ _ _ 0 _ | .func _ _ _ 0 _
  | .args _ _ _ 0 _ | .tuple _ _ 0 _
  | .invocation _ _ _ 0 _ _ | .produced _ _ 0 _ _ _ | .minimal _ _ 0 _ _
  | .primitive _ _ 0 _ _ | .functionBody _ _ 0 _ _ => false
  | .atom value expected bindings (depth + 1) _ =>
      if isEmptyOrError value then true
      else if expected == Atom.atomType || expected == getMetaType value ||
          getMetaType value == Atom.variableType then true
      else if getMetaType value == Atom.symbolType || getMetaType value == Atom.groundedType ||
          value == Atom.unit then typeCastCovered value expected space bindings depth lookup
      else true
  | .invocation mode value bindings (depth + 1) live _ =>
      if mode.errorPassthrough value then true
      else match value with
      | .expression (operator :: _) =>
          if dispatch.isExecutable operator then true
          else if minimalInstruction value then true
          else queryEquationsCovered (equationScope live value mode.expected bindings) space value depth
      | _ => queryEquationsCovered (equationScope live value mode.expected bindings) space value depth
  | .primitive value bindings (depth + 1) _ _ =>
      if minimalCoreSupported value then
        match value with
        | .expression [.symbol "eval", atom] => bindings.applyFullCovered atom depth
        | .expression [.symbol "unify", target, pattern, _, _] =>
            unifyMatchesCovered target pattern bindings depth
        | _ => true
      else false
  | .functions value expected bindings depth (operatorType :: _) _ =>
      if isFunctionType operatorType then
        functionTypeCovered value operatorType expected space bindings depth lookup
      else true
  | .equations _ _ incoming depth ((rhs, selected) :: _) _ =>
      matchCovered depth (.merge selected (aliasConstraints incoming)) &&
        (mergeBindings selected (aliasConstraints incoming) depth).all fun merged =>
          (merged.hasLoop || merged.applyFullCovered rhs depth)
  | .grounded _ _ incoming depth ((value, selected) :: _) _ =>
      matchCovered depth (.merge selected incoming) &&
        (mergeBindings selected incoming depth).all fun merged => merged.applyFullCovered value depth
  | .chainRows _ _ depth ((value, bindings) :: _)
  | .bodyResults depth ((value, bindings) :: _) _ _ => bindings.applyFullCovered value depth
  | .completed value expected bindings depth =>
      if isEmptyOrError value || expected == Atom.undefinedType || expected == Atom.atomType ||
          expected == getMetaType value || getMetaType value == Atom.variableType then true
      else typeCastCovered value expected space bindings depth lookup
  | _ => true

/-- The fallback frame repeats applicability queries only when all preceding
function alternatives failed. Those negative queries need coverage too. -/
def frameReady (space : Space) (results : ResultSet) (frame : Frame)
    (lookup : TypeLookup := rawTypeLookup space) : Bool :=
  match frame with
  | .fallback value expected bindings depth types =>
      !results.isEmpty || types.all fun operatorType =>
        !isFunctionType operatorType ||
          functionTypeCovered value operatorType expected space bindings depth lookup
  | _ => true

def blocked (dispatch : GroundedDispatch) (state : Configuration) : Option ResourceRequest :=
  match state.control, state.stack with
  | .work task, _ =>
      if taskReady state.space dispatch task then none
      else some (match task with
        | .primitive value _ (_ + 1) _ _ =>
            if minimalCoreSupported value then .leafDepth else .primitiveService value
        | _ => if task.depth == 0 then .evaluationDepth else .leafDepth)
  | .returning results, frame :: _ =>
      if frameReady state.space results frame then none else some .leafDepth
  | .returning _, [] => none

/-- Add resource suspension to an existing recursive worker. The complete
configuration is the request's retained receiver. -/
def guardMachine (base : Machine Configuration ResultPair Configuration Empty)
    (blocking : Configuration → Option ResourceRequest) :
    Machine Configuration ResultPair Configuration ResourceRequest where
  step state :=
    match blocking state with
    | some request => some (.call request state)
    | none => (base.step state).map (Transition.relabel id id Empty.elim)

/-- Every completed guarded run follows covered transitions. Any map that
commutes with those transitions preserves its full run and final receiver. -/
theorem guard_completed_map
    (base : Machine Configuration ResultPair Configuration Empty)
    (blocking : Configuration → Option ResourceRequest)
    (stateMap : Configuration → Configuration)
    (stepMap : ∀ state, blocking state = none →
      base.step (stateMap state) = (base.step state).map (fun transition =>
        (transition.mapState stateMap).relabel id stateMap id)) (budget : Nat)
    (state final : Configuration) (events : ResultSet)
    (completed : (guardMachine base blocking).run budget state = (events, .finished final)) :
    base.run budget (stateMap state) =
      (events, .finished (stateMap final)) := by
  induction budget generalizing state final events with
  | zero => simp [Machine.run] at completed
  | succ budget ih =>
      cases blockedHere : blocking state with
      | some request => simp [Machine.run, guardMachine, blockedHere] at completed
      | none =>
          have commute := stepMap state blockedHere
          cases stepped : base.step state with
          | none => simp [Machine.run, guardMachine, blockedHere, stepped] at completed
          | some transition =>
              have checkedStep : (guardMachine base blocking).step state =
                  some (transition.relabel id id Empty.elim) := by
                simp [guardMachine, blockedHere, stepped]
              cases transition with
              | silent next =>
                  have tail : (guardMachine base blocking).run budget next = (events, .finished final) := by
                    simpa only [Machine.run, checkedStep, Transition.relabel] using completed
                  have targetStep : base.step (stateMap state) =
                      some (.silent (stateMap next)) := by
                    rw [commute, stepped]
                    rfl
                  rw [Machine.run_succ_silent _ targetStep]
                  exact ih next final events tail
              | publish published next =>
                  rw [Machine.run_succ_publish _ checkedStep] at completed
                  cases later : (guardMachine base blocking).run budget next with
                  | mk remaining outcome =>
                      cases outcome with
                      | finished terminal =>
                          have same : published ++ remaining = events ∧ terminal = final := by
                            simpa only [later, Transition.relabel, Prod.fst, Prod.snd,
                              List.map_id, id_eq, Prod.mk.injEq, Outcome.finished.injEq] using completed
                          obtain ⟨rfl, rfl⟩ := same
                          have targetStep : base.step (stateMap state) =
                              some (.publish published (stateMap next)) := by
                            rw [commute, stepped]
                            simp [Transition.mapState, Transition.relabel]
                          rw [Machine.run_succ_publish _ targetStep, ih next terminal remaining later]
                      | faulted | suspended _ _ | stuck _ | exhausted _ => simp [later] at completed
              | finish terminal =>
                  have same : events = [] ∧ terminal = final := by
                    simpa only [Machine.run, checkedStep, Transition.relabel,
                      Prod.mk.injEq, Outcome.finished.injEq, id_eq, eq_comm] using completed
                  obtain ⟨rfl, rfl⟩ := same
                  have targetStep : base.step (stateMap state) =
                      some (.finish (stateMap terminal)) := by
                    rw [commute, stepped]
                    rfl
                  exact base.run_succ_finish targetStep
              | fail faults => simp [Machine.run, checkedStep, Transition.relabel] at completed
              | call request saved => exact request.elim

/-- In particular, the guard cannot invent a successful execution. -/
theorem guard_finished_refines
    (base : Machine Configuration ResultPair Configuration Empty)
    (blocking : Configuration → Option ResourceRequest)
    (budget : Nat) (state final : Configuration) (events : ResultSet)
    (completed : (guardMachine base blocking).run budget state = (events, .finished final)) :
    base.run budget state = (events, .finished final) := by
  apply guard_completed_map base blocking id (fun state _ => ?_) budget state final events completed
  simp [Transition.relabel_id]


/-- A covered transition uses the existing machine. A blocked one saves the
whole configuration without evaluating or publishing anything. -/
def machine (dispatch : GroundedDispatch) :
    Machine Configuration ResultPair Configuration ResourceRequest :=
  guardMachine (RecursiveMachine.machine dispatch) (blocked dispatch)

/-- Replenish only the suspended operation. Its caller, earlier results,
remaining alternatives, world and publication history stay retained. -/
def replenish (extra : Nat) (state : Configuration) : Configuration :=
  match state.control, state.stack with
  | .work task, _ => {state with control := .work (task.replenish extra)}
  | .returning _, .fallback value expected bindings depth types :: remaining =>
      {state with stack := .fallback value expected bindings (depth + extra) types :: remaining}
  | _, _ => state

theorem replenish_zero (state : Configuration) : replenish 0 state = state := by
  rcases state with ⟨space, control, stack, emitted⟩
  cases control with
  | work task => simp [replenish, Task.replenish_zero]
  | returning results =>
      cases stack with
      | nil => rfl
      | cons frame remaining => cases frame <;> simp [replenish]

theorem replenish_add (first second : Nat) (state : Configuration) :
    replenish second (replenish first state) = replenish (first + second) state := by
  rcases state with ⟨space, control, stack, emitted⟩
  cases control with
  | work task => simp [replenish, Task.replenish_add]
  | returning results =>
      cases stack with
      | nil => rfl
      | cons frame remaining => cases frame <;> simp [replenish, Nat.add_assoc]

theorem replenish_space (extra : Nat) (state : Configuration) :
    (replenish extra state).space = state.space := by
  unfold replenish
  split <;> rfl

theorem replenish_emitted (extra : Nat) (state : Configuration) :
    (replenish extra state).emitted = state.emitted := by
  unfold replenish
  split <;> rfl

theorem replenish_work_stack (extra : Nat) (state : Configuration) (task : Task)
    (pending : state.control = .work task) :
    (replenish extra state).stack = state.stack := by simp [replenish, pending]

theorem blocked_run (dispatch : GroundedDispatch) (state : Configuration)
    (request : ResourceRequest) (budget : Nat)
    (pending : blocked dispatch state = some request) :
    (machine dispatch).run (budget + 1) state = ([], .suspended request state) := by
  exact (machine dispatch).run_succ_call (by simp [machine, guardMachine, pending])

/-- Pausing for scheduler budget and continuing from the residual is exact. -/
theorem resume_prefix (dispatch : GroundedDispatch) (state saved : Configuration)
    (first second : Nat) (observed : ResultSet)
    (paused : (machine dispatch).run first state = (observed, .exhausted saved)) :
    (machine dispatch).run (first + second) state =
      (observed ++ ((machine dispatch).run second saved).1,
        ((machine dispatch).run second saved).2) :=
  (machine dispatch).established_and_pending first second state saved observed paused

/-- Continue a pending resource request from its saved configuration after a
depth grant. Scheduler exhaustion resumes with the same evaluator depth.
Binding materialization uses its proved structural depth; the grant applies
to the selected pending evaluation or search operation. -/
def continueRun (dispatch : GroundedDispatch) (budget extra : Nat) :
    ResultSet × Outcome Configuration Configuration ResourceRequest →
      ResultSet × Outcome Configuration Configuration ResourceRequest
  | (events, .suspended _ saved) =>
      let later := (machine dispatch).run budget (replenish extra saved)
      (events ++ later.1, later.2)
  | result => (machine dispatch).continueRun budget result

/-- Completion of the checked machine also completes the original finite
approximation with precisely the same occurrences and retained final state.
The checked machine can additionally suspend, but cannot invent a completion. -/
theorem finished_refines (dispatch : GroundedDispatch) (budget : Nat)
    (state : Configuration) (events : ResultSet) (final : Configuration)
    (completed : (machine dispatch).run budget state = (events, .finished final)) :
    (RecursiveMachine.machine dispatch).run budget state = (events, .finished final) :=
  guard_finished_refines (RecursiveMachine.machine dispatch) (blocked dispatch)
    budget state final events completed

/-! ### Stability after checked completion

Increasing residual evaluator depths commutes with every covered advance.
The proof uses the actual leaf-coverage laws and never infers completeness
from equality of two finite approximations. Publication and saved callers
remain intact. The target is the separately implemented finite evaluator
machine; its logical step count does not include the physical cost of leaves.
-/

def deepenExpansion (extra : Nat) (expanded : Control × List Frame) : Control × List Frame :=
  (expanded.1.deepen extra, expanded.2.map (Frame.deepen extra))

theorem enter_atom_deepen (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (depth extra : Nat) (live : List Atom) {lookup : TypeLookup}
    (ready : taskReady space dispatch (.atom value expected bindings depth live) lookup = true) :
    enter space dispatch (.atom value expected bindings (depth + extra) live) lookup =
      deepenExpansion extra (enter space dispatch (.atom value expected bindings depth live) lookup) := by
  cases depth with
  | zero => simp [taskReady] at ready
  | succ depth =>
      by_cases empty : isEmptyOrError value = true
      · simp [Nat.succ_add, enter, empty, deepenExpansion, Control.deepen]
      · by_cases trivial : (expected == Atom.atomType || expected == getMetaType value ||
            getMetaType value == Atom.variableType) = true
        · simp [Nat.succ_add, enter, empty, trivial, deepenExpansion, Control.deepen]
        · by_cases scalar : (getMetaType value == Atom.symbolType ||
              getMetaType value == Atom.groundedType || value == Atom.unit) = true
          · have covered : typeCastCovered value expected space bindings depth lookup = true := by
              simpa [taskReady, empty, trivial, scalar] using ready
            simp [Nat.succ_add, enter, empty, trivial, scalar, deepenExpansion, Control.deepen,
              typeCastCovered_stable value expected space bindings depth extra covered]
          · by_cases expression : (getMetaType value == Atom.expressionType) = true
            · simp [Nat.succ_add, enter, empty, trivial, scalar, expression, deepenExpansion, Control.deepen,
                Frame.deepen, Task.replenish]
            · simp [Nat.succ_add, enter, empty, trivial, scalar, expression, deepenExpansion, Control.deepen]

theorem enter_deepen (space : Space) (dispatch : GroundedDispatch)
    (task : Task) (extra : Nat) {lookup : TypeLookup} (ready : taskReady space dispatch task lookup = true) :
    enter space dispatch (task.replenish extra) lookup =
      deepenExpansion extra (enter space dispatch task lookup) := by
  cases task with
  | atom value expected bindings depth live =>
      exact enter_atom_deepen space dispatch value expected bindings depth extra live ready
  | call value expected bindings depth live => rfl
  | invocation mode value bindings depth live caller =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          simp only [taskReady] at ready
          by_cases stopped : mode.errorPassthrough value = true
          · simp only [stopped, ↓reduceIte]
            rfl
          · simp only [stopped, Bool.false_eq_true, ↓reduceIte] at ready ⊢
            split at ready
            · split at ready
              · simp_all only [↓reduceIte]
                repeat' split
                all_goals rfl
              · split at ready
                · simp_all [deepenExpansion, Control.deepen, Task.replenish, Frame.deepen]
                · have stable := queryEquationsCovered_stable _ _ _ depth extra ready
                  simp_all [deepenExpansion, Control.deepen, Task.replenish, Frame.deepen]
            · have stable := queryEquationsCovered_stable _ _ _ depth extra ready
              simp_all [deepenExpansion, Control.deepen, Task.replenish, Frame.deepen]
  | functions value expected bindings depth types live =>
      cases types with
      | nil => rfl
      | cons operatorType remaining =>
          by_cases function : isFunctionType operatorType = true
          · have covered : functionTypeCovered value operatorType expected space bindings depth lookup = true := by
              simpa [taskReady, function] using ready
            have stable := functionTypeCovered_stable value operatorType expected space bindings
              depth extra covered
            simp only [Task.replenish, enter, function, ↓reduceIte, stable]
            cases checkIfFunctionTypeIsApplicable value operatorType expected space bindings depth lookup <;> rfl
          · simp [Task.replenish, enter, function, deepenExpansion, Control.deepen, Frame.deepen]
  | equations original expected incoming depth alternatives live =>
      cases alternatives with
      | nil => rfl
      | cons alternative remaining =>
          rcases alternative with ⟨rhs, selected⟩
          have matching := (Bool.and_eq_true_iff.mp ready).1
          have sameMerge : mergeBindings selected (aliasConstraints incoming) (depth + extra) =
              mergeBindings selected (aliasConstraints incoming) depth := matchCovered_stable depth extra _ matching
          have payload : (mergeBindings selected (aliasConstraints incoming) (depth + extra)).filterMap
                (fun merged => if merged.hasLoop then none else some (merged.applyFull rhs (depth + extra), merged)) =
              (mergeBindings selected (aliasConstraints incoming) depth).filterMap
                (fun merged => if merged.hasLoop then none else some (merged.applyFull rhs depth, merged)) := by
            rw [sameMerge]
            apply List.filterMap_congr
            intro merged member
            have checked := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ready).2 merged member
            by_cases loop : merged.hasLoop = true
            · simp [loop]
            · have covered : merged.applyFullCovered rhs depth = true := by
                simpa [loop] using checked
              rw [merged.applyFullCovered_stable rhs depth extra covered]
          simp only [Task.replenish, enter, payload]
          rfl
  | grounded original expected incoming depth alternatives live =>
      cases alternatives with
      | nil => rfl
      | cons alternative remaining =>
          rcases alternative with ⟨value, selected⟩
          obtain ⟨matching, readings⟩ := Bool.and_eq_true_iff.mp ready
          have same : mergeBindings selected incoming (depth + extra) = mergeBindings selected incoming depth :=
            matchCovered_stable depth extra _ matching
          have payload : (mergeBindings selected incoming (depth + extra)).map
                (fun merged => (merged.applyFull value (depth + extra), merged)) =
              (mergeBindings selected incoming depth).map
                (fun merged => (merged.applyFull value depth, merged)) := by
            rw [same]
            apply List.map_congr_left
            intro merged member
            rw [merged.applyFullCovered_stable value depth extra
              (List.all_eq_true.mp readings merged member)]
          simp only [Task.replenish, enter, payload]
          rfl
  | expression value expected bindings depth live =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          repeat' split
          all_goals simp [deepenExpansion, Control.deepen, Frame.deepen, Task.replenish]
  | func value operatorType bindings depth live =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          split <;> rfl
  | args values types bindings depth live =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          split <;> rfl
  | tuple value bindings depth live =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          split <;> rfl
  | heads operatorType arguments depth alternatives live =>
      cases alternatives <;> simp only [Task.replenish, enter]
      · rfl
      · repeat' split
        all_goals rfl
  | argumentHeads original remaining types depth alternatives live =>
      cases alternatives <;> simp only [Task.replenish, enter]
      · rfl
      · split <;> rfl
  | tupleHeads tail depth alternatives live =>
      cases alternatives <;> simp only [Task.replenish, enter]
      · rfl
      · split <;> rfl
  | bindingAlternatives value operatorType expected depth alternatives live =>
      cases alternatives <;> rfl
  | calls expected depth alternatives live => cases alternatives <;> rfl
  | atoms expected depth alternatives live => cases alternatives <;> rfl
  | returned original value expected bindings depth live =>
      simp only [Task.replenish, enter]
      split <;> try rfl
      split <;> rfl
  | returns original expected depth alternatives live => cases alternatives <;> rfl
  | tupleCalls value expected bindings depth live => rfl
  | produced value bindings depth live caller provenance =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          repeat' split
          all_goals rfl
  | productions depth alternatives live caller provenance => cases alternatives <;> rfl
  | minimal value bindings depth live caller =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          repeat' split
          all_goals rfl
  | minimals depth alternatives live caller => cases alternatives <;> rfl
  | primitive value bindings depth live caller =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          split <;> try rfl
          · rename_i atom
            have checked : bindings.applyFullCovered atom depth = true := by
              simpa [taskReady, minimalCoreSupported] using ready
            rw [bindings.applyFullCovered_stable atom depth extra checked]
            rfl
          · rename_i target pattern yes no
            have checked : unifyMatchesCovered target pattern bindings depth = true := by
              simpa [taskReady, minimalCoreSupported] using ready
            have stable := unifyMatchesCovered_stable target pattern yes bindings depth extra checked
            rw [stable]
            rfl
  | chainRows name template depth alternatives =>
      cases alternatives with
      | nil => rfl
      | cons pair remaining =>
          rcases pair with ⟨value, bindings⟩
          have same := bindings.applyFullCovered_stable value depth extra ready
          simp only [Task.replenish, enter, same]
          rfl
  | functionBody value bindings depth live caller =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          rfl
  | bodyResults depth alternatives live caller =>
      cases alternatives with
      | nil => rfl
      | cons pair remaining =>
          rcases pair with ⟨value, bindings⟩
          have same := bindings.applyFullCovered_stable value depth extra ready
          simp only [Task.replenish, enter, same]
          split <;> rfl
  | producerResults mode original incoming fuel live emptyReply results =>
      cases results <;> rfl
  | completed value expected bindings depth =>
      simp only [taskReady] at ready
      simp only [Task.replenish, enter, completedCallReturn]
      split at ready
      · simp_all [deepenExpansion, Control.deepen]
      · have stable := typeCastCovered_stable value expected space bindings depth extra ready
        simp_all [deepenExpansion, Control.deepen]

theorem functionFallback_deepen (space : Space) (value expected : Atom) (bindings : Bindings)
    (depth extra : Nat) (types : List Atom) (results : ResultSet) {lookup : TypeLookup}
    (ready : frameReady space results (.fallback value expected bindings depth types) lookup = true) :
    functionFallback space value expected bindings (depth + extra) types results lookup =
      functionFallback space value expected bindings depth types results lookup := by
  by_cases nonempty : results.isEmpty = false
  · simp [functionFallback, nonempty]
  · have coveredTypes : (types.all fun operatorType => !isFunctionType operatorType ||
          functionTypeCovered value operatorType expected space bindings depth lookup) = true := by
      have empty : results.isEmpty = true := by cases found : results.isEmpty <;> simp_all
      simpa [frameReady, empty] using ready
    have stable (operatorType : Atom) (member : operatorType ∈ types)
        (function : isFunctionType operatorType = true) :
        checkIfFunctionTypeIsApplicable value operatorType expected space bindings (depth + extra) lookup =
          checkIfFunctionTypeIsApplicable value operatorType expected space bindings depth lookup := by
      apply functionTypeCovered_stable
      simpa [function] using List.all_eq_true.mp coveredTypes operatorType member
    have tests :
        types.map (fun operatorType => if isFunctionType operatorType then
          match checkIfFunctionTypeIsApplicable value operatorType expected space bindings (depth + extra) lookup with
          | .inl _ => true
          | .inr _ => false
        else true) =
        types.map (fun operatorType => if isFunctionType operatorType then
          match checkIfFunctionTypeIsApplicable value operatorType expected space bindings depth lookup with
          | .inl _ => true
          | .inr _ => false
        else true) := by
      apply List.map_congr_left
      intro operatorType member
      by_cases function : isFunctionType operatorType = true
      · rw [if_pos function, if_pos function, stable operatorType member function]
      · rw [if_neg function, if_neg function]
    have checks := congrArg (fun answers : List Bool => answers.all id) tests
    simp only [List.all_map, Function.comp_def, id_eq] at checks
    have blocks : types.flatMap (fun operatorType => if isFunctionType operatorType then
          match checkIfFunctionTypeIsApplicable value operatorType expected space bindings (depth + extra) lookup with
          | .inl errors => errors.map fun error => (error, bindings)
          | .inr _ => []
        else []) =
        types.flatMap (fun operatorType => if isFunctionType operatorType then
          match checkIfFunctionTypeIsApplicable value operatorType expected space bindings depth lookup with
          | .inl errors => errors.map fun error => (error, bindings)
          | .inr _ => []
        else []) := by
      apply List.flatMap_congr
      intro operatorType member
      by_cases function : isFunctionType operatorType = true
      · rw [if_pos function, if_pos function, stable operatorType member function]
      · rw [if_neg function, if_neg function]
    dsimp only [functionFallback]
    congr 1
    congr 1
    congr 1

theorem resume_deepen (space : Space) (frame : Frame) (results : ResultSet)
    (extra : Nat) {lookup : TypeLookup} (ready : frameReady space results frame lookup = true) :
    resume space (frame.deepen extra) results lookup = deepenExpansion extra (resume space frame results lookup) := by
  cases frame with
  | fallback value expected bindings depth types =>
      simp only [Frame.deepen, resume, deepenExpansion, Control.deepen, List.map_nil]
      rw [functionFallback_deepen space value expected bindings depth extra types results ready]
  | invocationReturn mode original fuel live => cases mode <;> rfl
  | producerResults mode original incoming fuel live emptyReply =>
      cases results <;> rfl
  | _ => rfl

theorem step_deepen (dispatch : GroundedDispatch) (state : Configuration) (extra : Nat)
    (ready : blocked dispatch state = none) :
    (RecursiveMachine.machine dispatch).step (state.deepen extra) =
      ((RecursiveMachine.machine dispatch).step state).map (fun transition =>
        (transition.mapState (Configuration.deepen extra)).relabel id (Configuration.deepen extra) id) := by
  rcases state with ⟨space, control, stack, emitted⟩
  cases control with
  | work task =>
      have covered : taskReady space dispatch task = true := by
        simpa [blocked] using ready
      have commute := enter_deepen space dispatch task extra covered
      simp only [RecursiveMachine.machine, next, Configuration.deepen, Control.deepen, commute,
        deepenExpansion, List.map_append, Option.map_some, Transition.mapState, Transition.relabel]
  | returning results =>
      cases stack with
      | nil => cases results <;> rfl
      | cons frame remaining =>
          have covered : frameReady space results frame = true := by
            simpa [blocked] using ready
          have commute := resume_deepen space frame results extra covered
          simp only [RecursiveMachine.machine, next, Configuration.deepen, Control.deepen,
            List.map_cons, commute, deepenExpansion, List.map_append,
            Option.map_some, Transition.mapState, Transition.relabel]

/-- A completed checked run earns the same result at every greater residual
depth. The statement follows arbitrary actual configurations, not only fresh
top-level requests, and keeps the complete final continuation. -/
theorem completed_deepen (dispatch : GroundedDispatch) (extra budget : Nat)
    (state final : Configuration) (events : ResultSet)
    (completed : (machine dispatch).run budget state = (events, .finished final)) :
    (RecursiveMachine.machine dispatch).run budget (state.deepen extra) =
      (events, .finished (final.deepen extra)) :=
  guard_completed_map (RecursiveMachine.machine dispatch) (blocked dispatch)
    (Configuration.deepen extra) (fun state ready => step_deepen dispatch state extra ready)
    budget state final events completed

end Checked

end Mettapedia.Languages.MeTTa.HE.RecursiveMachine
