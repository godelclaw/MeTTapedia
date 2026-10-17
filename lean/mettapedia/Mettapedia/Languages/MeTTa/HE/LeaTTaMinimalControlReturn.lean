import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlContinuation
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Return and sequencing inside an existing caller

The laws retain arbitrary caller frames, queued work and previous answers.
Returned operands are materialized by the existing interpreter. No assumption
about a caller's eventual result is needed to resume that caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution

open Metta Metta.Minimal FuelConvergenceInterpreter

/-- A completed frame no longer uses its variable-retention list. The caller and
all scheduling observations are unchanged. -/
theorem finished_frame_scope_irrelevant (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (result : Atom) (scope : List VarName)
    (parent : Frame) (continuation : Stack) (fuel : Nat) (rest : List Item)
    (done : List (Atom × Metta.Bindings)) :
    interpretFuel environment fuel state
      (⟨{ atom := result, fin := true, vars := scope } :: parent :: continuation,
        bindings⟩ :: rest) done =
    interpretFuel environment fuel state
      (finItem (parent :: continuation) result bindings :: rest) done := by
  cases fuel with
  | zero =>
    rw [FuelConvergenceInterpreter.interpretFuel_zero_cons,
      FuelConvergenceInterpreter.interpretFuel_zero_cons]
    rfl
  | succ fuel =>
    rw [interpretFuel_succ, interpretFuel_succ]
    simp only [interpretStack1, finItem, if_true]

/-- A return becomes ready for the enclosing function handler, including when
that function has no caller. -/
theorem return_enters_handler (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody value : Atom) (scope : List VarName)
    (continuation : Stack) (fuel : Nat) (rest : List Item)
    (done : List (Atom × Metta.Bindings)) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 1) state
      (⟨atomToStack (.expr [.sym "return", value]) (parent :: continuation), bindings⟩ :: rest) done =
    interpretFuel environment fuel state
      (finItem (parent :: continuation) (.expr [.sym "return", value]) bindings :: rest) done := by
  intro parent
  let next : Item := ⟨{ atom := .expr [.sym "return", value], fin := true, vars := scope } ::
    parent :: continuation, bindings⟩
  have step : interpretStack1 environment fuel state
      ⟨atomToStack (.expr [.sym "return", value]) (parent :: continuation), bindings⟩ =
      ([next], state) := by
    simp [interpretStack1, atomToStack, parent, varsCopy, isEmbeddedOp, next]
  rw [driver_singleton_step environment fuel state state _ next rest done step (by rfl)]
  exact finished_frame_scope_irrelevant environment state bindings _ scope parent continuation
    fuel rest done

/-- The outermost function return becomes exactly one public result. -/
theorem selected_closed_return_finishes (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody value : Atom) (scope : List VarName)
    (fuel : Nat) (closed : value.vars = []) (visible : (value != emptyA) = true) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 1) state
      [finItem [parent] (.expr [.sym "return", value]) bindings] [] =
      ([(value, bindings)], state) := by
  intro parent
  have step := step_function_return environment fuel state [] scope parentBody value bindings
  rw [instantiate_of_closed bindings value closed] at step
  rw [interpretFuel_succ_of environment fuel state state _ [] _ [] step]
  change interpretFuel environment fuel state [] [(instantiate bindings value, bindings)] = _
  rw [FuelConvergenceInterpreter.interpretFuel_nil, instantiate_of_closed bindings value closed]
  simp [visible]

/-- An exhausted recursive computation returns to its caller through the
same guard as a top-level request. It preserves bindings, runtime state,
queued work and accumulated answers, without evaluating the fallback. -/
theorem integer_zero_guard_to_caller_in_frame (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name marker : String) (otherwise : Atom) (fuel : Nat)
    (parentBody : Atom) (scope : List VarName) (caller : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Atom × Metta.Bindings))
    (groundings : environment.gt = Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    let equality := Atom.expr [.sym "eval", .expr [.sym "==", .gnd (.int 0), .gnd (.int 0)]]
    let template := Atom.expr [.sym "unify", .var name, .gnd (.bool true),
      .expr [.sym "return", .sym marker], otherwise]
    let body := Atom.expr [.sym "chain", equality, .var name, template]
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 5) state
        (⟨atomToStack body (parent :: caller :: continuation),
          bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation) (.sym marker) bindings :: rest) done := by
  intro equality template body parent
  let selected := finItem (parent :: caller :: continuation)
    (.expr [.sym "return", .sym marker]) bindings
  rw [show fuel + 5 = (fuel + 1) + 4 by omega,
    integer_zero_guard_selects_in_frame environment state bindings name marker otherwise
      (fuel + 1) parent (caller :: continuation) rest done groundings acyclic]
  change interpretFuel environment (fuel + 1) state (selected :: rest) done = _
  apply driver_singleton_step
  · simpa [selected, parent, instantiate, Bindings.resolveAtom] using
      step_function_return environment fuel state (caller :: continuation)
        scope parentBody
        (.sym marker) bindings
  · rfl

/-- Opening a recursive function specializes the retained-frame exhaustion
law; the fallback is still never evaluated. -/
theorem integer_zero_guard_to_caller (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name marker : String) (otherwise : Atom) (fuel : Nat)
    (caller : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Atom × Metta.Bindings))
    (groundings : environment.gt = Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    let equality := Atom.expr [.sym "eval", .expr [.sym "==", .gnd (.int 0), .gnd (.int 0)]]
    let template := Atom.expr [.sym "unify", .var name, .gnd (.bool true),
      .expr [.sym "return", .sym marker], otherwise]
    let body := Atom.expr [.sym "chain", equality, .var name, template]
    interpretFuel environment (fuel + 5) state
        (⟨atomToStack (.expr [.sym "function", body]) (caller :: continuation),
          bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation) (.sym marker) bindings :: rest) done := by
  intro equality template body
  simpa only [body, equality, template, atomToStack] using
    integer_zero_guard_to_caller_in_frame environment state bindings name marker otherwise fuel
      (.expr [.sym "function", body]) (varsCopy (caller :: continuation)) caller continuation
      rest done groundings acyclic

/-- Returning from a nested function preserves its caller and the rest of the
driver. The returned atom is exactly the runtime's instantiated operand. -/
theorem return_to_caller (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody value : Atom) (scope : List VarName)
    (caller : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings)) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 2) state
        (⟨atomToStack (.expr [.sym "return", value])
          (parent :: caller :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation) (instantiate bindings value) bindings :: rest) done := by
  intro parent
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    return_enters_handler environment state bindings parentBody value scope
      (caller :: continuation) (fuel + 1) rest done]
  exact driver_singleton_step environment fuel state state _ _ rest done
    (step_function_return environment fuel state (caller :: continuation) scope parentBody
      value bindings) (by rfl)

/-- A finished argument enters its actual `chain` continuation. Binding
resolution precedes substitution, and every surrounding frame is retained. -/
theorem chain_result_enters (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (source result template : Atom) (name : VarName)
    (scope : List VarName) (parent : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings)) :
    let caller : Frame := { atom := .expr [.sym "chain", source, .var name, template], ret := .chain, vars := scope }
    interpretFuel environment (fuel + 2) state
        (finItem (caller :: parent :: continuation) result bindings :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (Subst.apply [(name, instantiate bindings result)] template)
          (parent :: continuation), bindings⟩ :: rest) done := by
  intro caller
  let middle : Item := ⟨{ atom := .expr [.sym "chain", instantiate bindings result,
    .var name, template], ret := .chain, vars := scope } :: parent :: continuation, bindings⟩
  have firstStep (budget : Nat) : interpretStack1 environment budget state
      (finItem (caller :: parent :: continuation) result bindings) = ([middle], state) := by
    exact step_chain_result environment budget state (parent :: continuation) scope
      source result template name bindings
  have lastStep (budget : Nat) : interpretStack1 environment budget state middle =
      ([⟨atomToStack (Subst.apply [(name, instantiate bindings result)] template)
        (parent :: continuation), bindings⟩], state) := by
    exact step_chain_apply environment budget state (parent :: continuation) scope
      (instantiate bindings result) template name bindings
  rw [driver_singleton_step environment (fuel + 1) state state _ middle rest done
    (firstStep _) (by rfl)]
  exact driver_singleton_step environment fuel state state middle _ rest done
    (lastStep _) (atomToStack_pending _ _ _ _)

/-- A closed return from a nested function enters the caller's template.
This composes the function and sequencing laws without a new execution model. -/
theorem closed_return_chain_enters (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody value source template : Atom)
    (name : VarName) (functionScope chainScope : List VarName)
    (parent : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings))
    (closed : value.vars = []) :
    let function : Frame := { atom := parentBody, ret := .function, vars := functionScope }
    let caller : Frame := { atom := .expr [.sym "chain", source, .var name, template], ret := .chain, vars := chainScope }
    interpretFuel environment (fuel + 4) state
        (⟨atomToStack (.expr [.sym "return", value])
          (function :: caller :: parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (Subst.apply [(name, value)] template)
          (parent :: continuation), bindings⟩ :: rest) done := by
  intro function caller
  rw [show fuel + 4 = (fuel + 2) + 2 by omega,
    return_to_caller environment state bindings parentBody value functionScope caller
      (parent :: continuation) (fuel + 2) rest done,
    Metta.instantiate_of_closed bindings value closed]
  rw [chain_result_enters environment state bindings source value template name chainScope
    parent continuation fuel rest done, Metta.instantiate_of_closed bindings value closed]

/-- A pending local worklist carries the interpreter's remaining budget.
Nested instructions inspect that budget, so it is part of the actual state,
not a separate uniform padding parameter. -/
abbrev PendingState := Nat × St × List Item

/-- One actual interpreter step before any local branch reaches the public
result boundary. Native state and the entire local worklist are retained. -/
def pendingStep (environment : MinEnv) (before after : PendingState) : Prop :=
  ∃ fuel state nextState item rest results,
    before = (fuel + 1, state, item :: rest) ∧
    after = (fuel, nextState, results ++ rest) ∧
    interpretStack1 environment fuel state item = (results, nextState) ∧
    ∀ result ∈ results, isFinal result = false

/-- Finite paths use the common reflexive-transitive closure. This is an
execution relation over actual steps, not another interpreter. -/
abbrev PendingSteps (environment : MinEnv) := Relation.ReflTransGen (pendingStep environment)

theorem pendingStep_replay {environment : MinEnv} {before after : PendingState}
    (advanced : pendingStep environment before after) (queued : List Item)
    (done : List (Atom × Metta.Bindings)) :
    interpretFuel environment before.1 before.2.1 (before.2.2 ++ queued) done =
      interpretFuel environment after.1 after.2.1 (after.2.2 ++ queued) done := by
  obtain ⟨fuel, state, nextState, item, rest, results, rfl, rfl, step, pending⟩ := advanced
  have filters : results.filter isFinal = [] ∧
      results.filter (fun result => !isFinal result) = results := by
    clear step
    induction results with
    | nil => simp
    | cons result results ih =>
        have first := pending result (by simp)
        have later := ih (fun result member => pending result (by simp [member]))
        simp [first, later.1, later.2]
  simp only [List.cons_append]
  rw [interpretFuel_succ_of environment fuel state nextState item
    (rest ++ queued) results done step, filters.1, filters.2]
  simp only [List.map_nil, List.reverse_nil, List.nil_append, List.append_assoc]

/-- A local pending path replays with the original queued suffix and result
accumulator. Its state endpoint includes any actual intermediate effects. -/
theorem pendingSteps_replay {environment : MinEnv} {before after : PendingState}
    (path : PendingSteps environment before after) (queued : List Item)
    (done : List (Atom × Metta.Bindings)) :
    interpretFuel environment before.1 before.2.1 (before.2.2 ++ queued) done =
      interpretFuel environment after.1 after.2.1 (after.2.2 ++ queued) done := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head advanced _ ih => exact (pendingStep_replay advanced queued done).trans ih

/-- Any actual finite body computation reaching a return marker completes
through the existing function handler. The native return operand is
instantiated exactly once at this boundary. At an outermost function the
ordinary driver collects the result; otherwise it remains pending for its
saved caller. Neither queued work nor earlier results are discarded. -/
theorem function_return_after_pending_prefix
    {environment : MinEnv} {before : PendingState} {state : St}
    {fuel : Nat} {bindings : Metta.Bindings} {parentBody value : Atom}
    {scope returnScope : List VarName} {previous : Stack} {retained : List Item}
    (path : PendingSteps environment before
      (fuel + 1, state,
        ⟨{ atom := .expr [.sym "return", value], vars := returnScope, fin := true } ::
          { atom := parentBody, ret := .function, vars := scope } :: previous, bindings⟩ :: retained))
    (queued : List Item) (done : List (Atom × Metta.Bindings)) :
    interpretFuel environment before.1 before.2.1 (before.2.2 ++ queued) done =
      interpretFuel environment fuel state
        (([finItem previous (instantiate bindings value) bindings].filter
          (fun result => !isFinal result)) ++ retained ++ queued)
        ((([finItem previous (instantiate bindings value) bindings].filter isFinal).map
          finalPair).reverse ++ done) := by
  rw [pendingSteps_replay path queued done]
  simp only [List.cons_append]
  rw [finished_frame_scope_irrelevant environment state bindings _ returnScope
    { atom := parentBody, ret := .function, vars := scope } previous (fuel + 1)
    (retained ++ queued) done]
  simpa only [List.append_assoc] using
    interpretFuel_succ_of environment fuel state state _ (retained ++ queued) _ done
      (step_function_return environment fuel state previous scope parentBody value bindings)

/-- Raw emitted data is already a finished result. The guard follows the
runtime's actual head test, which is broader than exact function syntax. -/
theorem evalResult_raw_of_not_function_head (previous : Stack) (value : Atom)
    (bindings : Metta.Bindings)
    (raw : ∀ tail, value ≠ .expr (.sym "function" :: tail)) :
    evalResult previous value bindings = finItem previous value bindings := by
  cases value with
  | sym | var | gnd => rfl
  | expr atoms =>
      cases atoms with
      | nil => rfl
      | cons head tail =>
          cases head with
          | var | gnd | expr => rfl
          | sym name =>
              by_cases functionName : name = "function"
              · subst name
                exact (raw tail rfl).elim
              · simp [evalResult]

/-- An immediate return supplies a constructed local prefix for every
operand, including open terms and nonempty caller scopes. The subsequent
function handler still performs its actual instantiation. -/
theorem immediate_return_pending_prefix (environment : MinEnv) (state : St)
    (fuel : Nat) (previous : Stack) (value : Atom) (bindings : Metta.Bindings) :
    let functionValue := Atom.expr [.sym "function", .expr [.sym "return", value]]
    let parent : Frame := { atom := functionValue, ret := .function, vars := varsCopy previous }
    PendingSteps environment
      (fuel + 2, state, [evalResult previous functionValue bindings])
      (fuel + 1, state,
        [⟨{ atom := .expr [.sym "return", value], vars := varsCopy previous, fin := true } ::
          parent :: previous, bindings⟩]) := by
  intro functionValue parent
  let returned : Item :=
    ⟨{ atom := .expr [.sym "return", value], vars := varsCopy previous, fin := true } ::
      parent :: previous, bindings⟩
  apply Relation.ReflTransGen.single
  refine ⟨fuel + 1, state, state, evalResult previous functionValue bindings, [], [returned],
    rfl, rfl, ?_, ?_⟩
  · simp [functionValue, parent, returned, evalResult, atomToStack, interpretStack1,
      varsCopy, isEmbeddedOp]
  · intro result member
    have same : result = returned := List.mem_singleton.mp member
    rw [same]
    rfl

/-- A successful actual singleton step supplies a common finite-path edge. -/
theorem pendingStep_singleton {environment : MinEnv} {fuel : Nat} {state nextState : St}
    {item next : Item}
    (step : interpretStack1 environment fuel state item = ([next], nextState))
    (pending : isFinal next = false) :
    pendingStep environment (fuel + 1, state, [item]) (fuel, nextState, [next]) := by
  refine ⟨fuel, state, nextState, item, [], [next], rfl, rfl, step, ?_⟩
  intro result member
  simpa only [List.mem_singleton.mp member] using pending

/-- Constructor primitives consume the syntax already present at the top
frame. They do not silently instantiate open operands at this step. -/
theorem step_cons_atom (environment : MinEnv) (fuel : Nat) (state : St)
    (previous : Stack) (scope : List VarName) (head : Atom) (tail : List Atom)
    (bindings : Metta.Bindings) :
    interpretStack1 environment fuel state
      ⟨{ atom := .expr [.sym "cons-atom", head, .expr tail], vars := scope } :: previous,
        bindings⟩ =
      ([finItem previous (.expr (head :: tail)) bindings], state) := by
  simp [interpretStack1]

theorem step_decons_atom (environment : MinEnv) (fuel : Nat) (state : St)
    (previous : Stack) (scope : List VarName) (head : Atom) (tail : List Atom)
    (bindings : Metta.Bindings) :
    interpretStack1 environment fuel state
      ⟨{ atom := .expr [.sym "decons-atom", .expr (head :: tail)], vars := scope } :: previous,
        bindings⟩ =
      ([finItem previous (.expr [head, .expr tail]) bindings], state) := by
  simp [interpretStack1]

/-- Invalid constructor operands retain the runtime's actual diagnostic;
a later binding assignment is not consulted by primitive dispatch. -/
theorem step_cons_atom_invalid_tail (environment : MinEnv) (fuel : Nat) (state : St)
    (previous : Stack) (scope : List VarName) (head tail : Atom)
    (bindings : Metta.Bindings) (invalid : ∀ values, tail ≠ .expr values) :
    interpretStack1 environment fuel state
      ⟨{ atom := .expr [.sym "cons-atom", head, tail], vars := scope } :: previous,
        bindings⟩ =
      ([finItem previous (errAtom (.expr [.sym "cons-atom", head, tail])
        "cons-atom: expected (cons-atom <head> <expression>)") bindings], state) := by
  cases tail with
  | sym | var | gnd => simp [interpretStack1]
  | expr values => exact (invalid values rfl).elim

/-- Empty and nonexpression deconstruction operands keep the same native
fault subject and message, without evaluating the invalid operand. -/
theorem step_decons_atom_invalid (environment : MinEnv) (fuel : Nat) (state : St)
    (previous : Stack) (scope : List VarName) (value : Atom)
    (bindings : Metta.Bindings)
    (invalid : ∀ head tail, value ≠ .expr (head :: tail)) :
    interpretStack1 environment fuel state
      ⟨{ atom := .expr [.sym "decons-atom", value], vars := scope } :: previous, bindings⟩ =
      ([finItem previous (errAtom (.expr [.sym "decons-atom", value])
        "decons-atom: expected (decons-atom <non-empty-expression>)") bindings], state) := by
  cases value with
  | sym | var | gnd => simp [interpretStack1]
  | expr values =>
      cases values with
      | nil => simp [interpretStack1]
      | cons head tail => exact (invalid head tail rfl).elim

/-- An open constructor result remains pending for its saved caller; no
closedness premise is imposed on its head or its elements. -/
theorem cons_atom_pending_prefix (environment : MinEnv) (fuel : Nat) (state : St)
    (parent : Frame) (previous : Stack) (scope : List VarName)
    (head : Atom) (tail : List Atom) (bindings : Metta.Bindings) :
    PendingSteps environment
      (fuel + 1, state,
        [⟨{ atom := .expr [.sym "cons-atom", head, .expr tail], vars := scope } ::
          parent :: previous, bindings⟩])
      (fuel, state, [finItem (parent :: previous) (.expr (head :: tail)) bindings]) :=
  Relation.ReflTransGen.single
    (pendingStep_singleton
      (step_cons_atom environment fuel state (parent :: previous) scope head tail bindings)
      (by rfl))

theorem decons_atom_pending_prefix (environment : MinEnv) (fuel : Nat) (state : St)
    (parent : Frame) (previous : Stack) (scope : List VarName)
    (head : Atom) (tail : List Atom) (bindings : Metta.Bindings) :
    PendingSteps environment
      (fuel + 1, state,
        [⟨{ atom := .expr [.sym "decons-atom", .expr (head :: tail)], vars := scope } ::
          parent :: previous, bindings⟩])
      (fuel, state, [finItem (parent :: previous) (.expr [head, .expr tail]) bindings]) :=
  Relation.ReflTransGen.single
    (pendingStep_singleton
      (step_decons_atom environment fuel state (parent :: previous) scope head tail bindings)
      (by rfl))

/-- A proved primitive advance composes with the real chain and return
handlers. The primitive emits its raw result; only the finished chain handler
materializes it, retaining any correlated residual variables. -/
theorem primitive_chain_return_pending_prefix (environment : MinEnv) (state : St)
    (fuel : Nat) (previous : Stack) (source result : Atom) (name : String)
    (bindings : Metta.Bindings)
    (step : ∀ continuation,
      interpretStack1 environment (fuel + 4) state
        ⟨atomToStack source continuation, bindings⟩ =
        ([finItem continuation result bindings], state)) :
    let template := Atom.expr [.sym "return", .var name]
    let body := Atom.expr [.sym "chain", source, .var name, template]
    let functionValue := Atom.expr [.sym "function", body]
    let parent : Frame := { atom := functionValue, ret := .function, vars := varsCopy previous }
    PendingSteps environment
      (fuel + 5, state, [evalResult previous functionValue bindings])
      (fuel + 1, state,
        [⟨{ atom := .expr [.sym "return", instantiate bindings result],
            vars := varsCopy previous, fin := true } ::
          parent :: previous, bindings⟩]) := by
  intro template body functionValue parent
  let chainScope := chainFrameVars (parent :: previous) source template
  let chain : Frame := { atom := body, ret := .chain, vars := chainScope }
  let first := finItem (chain :: parent :: previous) result bindings
  let second : Item :=
    ⟨({ atom := .expr [.sym "chain", instantiate bindings result, .var name, template],
        ret := .chain, vars := chainScope } : Frame) :: parent :: previous, bindings⟩
  let third : Item := ⟨atomToStack (.expr [.sym "return", instantiate bindings result])
    (parent :: previous), bindings⟩
  let fourth : Item :=
    ⟨({ atom := .expr [.sym "return", instantiate bindings result],
        vars := varsCopy previous, fin := true } : Frame) :: parent :: previous, bindings⟩
  have firstStep : interpretStack1 environment (fuel + 4) state
      (evalResult previous functionValue bindings) = ([first], state) := by
    simpa only [functionValue, body, template, parent, chain, chainScope, first,
      evalResult, atomToStack] using step (chain :: parent :: previous)
  have secondStep : interpretStack1 environment (fuel + 3) state first = ([second], state) := by
    simpa only [first, second, chain, body] using
      step_chain_result environment (fuel + 3) state (parent :: previous) chainScope
        source result template name bindings
  have thirdStep : interpretStack1 environment (fuel + 2) state second = ([third], state) := by
    simpa [second, third, template, Subst.apply, Subst.lookup] using
      step_chain_apply environment (fuel + 2) state (parent :: previous) chainScope
        (instantiate bindings result) template name bindings
  have fourthStep : interpretStack1 environment (fuel + 1) state third = ([fourth], state) := by
    simp [third, fourth, parent, atomToStack, interpretStack1, varsCopy, isEmbeddedOp]
  exact Relation.ReflTransGen.head (pendingStep_singleton firstStep (by rfl))
    (Relation.ReflTransGen.head (pendingStep_singleton secondStep (by rfl))
      (Relation.ReflTransGen.head (pendingStep_singleton thirdStep
        (atomToStack_pending _ _ _ _))
        (Relation.ReflTransGen.single (pendingStep_singleton fourthStep (by rfl)))))

/-- Cons/chain/return admits arbitrary open fixed operands, not just closed
heads and empty tails. The fixedness belongs to the materialized result. -/
theorem cons_chain_return_pending_prefix_of_fixed (environment : MinEnv) (state : St)
    (fuel : Nat) (previous : Stack) (head : Atom) (tail : List Atom) (name : String)
    (bindings : Metta.Bindings)
    (fixed : instantiate bindings (.expr (head :: tail)) = .expr (head :: tail)) :
    let source := Atom.expr [.sym "cons-atom", head, .expr tail]
    let template := Atom.expr [.sym "return", .var name]
    let body := Atom.expr [.sym "chain", source, .var name, template]
    let functionValue := Atom.expr [.sym "function", body]
    let parent : Frame := { atom := functionValue, ret := .function, vars := varsCopy previous }
    PendingSteps environment
      (fuel + 5, state, [evalResult previous functionValue bindings])
      (fuel + 1, state,
        [⟨{ atom := .expr [.sym "return", .expr (head :: tail)],
            vars := varsCopy previous, fin := true } :: parent :: previous, bindings⟩]) := by
  simpa only [fixed] using
    primitive_chain_return_pending_prefix environment state fuel previous
      (.expr [.sym "cons-atom", head, .expr tail]) (.expr (head :: tail)) name bindings
      (fun continuation => by simp [atomToStack, interpretStack1])

/-- Decons has the same constructed continuation prefix and retains open
correlated fields when the materialized result is fixed by its bindings. -/
theorem decons_chain_return_pending_prefix_of_fixed (environment : MinEnv) (state : St)
    (fuel : Nat) (previous : Stack) (head : Atom) (tail : List Atom) (name : String)
    (bindings : Metta.Bindings)
    (fixed : instantiate bindings (.expr [head, .expr tail]) = .expr [head, .expr tail]) :
    let source := Atom.expr [.sym "decons-atom", .expr (head :: tail)]
    let template := Atom.expr [.sym "return", .var name]
    let body := Atom.expr [.sym "chain", source, .var name, template]
    let functionValue := Atom.expr [.sym "function", body]
    let parent : Frame := { atom := functionValue, ret := .function, vars := varsCopy previous }
    PendingSteps environment
      (fuel + 5, state, [evalResult previous functionValue bindings])
      (fuel + 1, state,
        [⟨{ atom := .expr [.sym "return", .expr [head, .expr tail]],
            vars := varsCopy previous, fin := true } :: parent :: previous, bindings⟩]) := by
  simpa only [fixed] using
    primitive_chain_return_pending_prefix environment state fuel previous
      (.expr [.sym "decons-atom", .expr (head :: tail)]) (.expr [head, .expr tail]) name bindings
      (fun continuation => by simp [atomToStack, interpretStack1])

/-- The original closed empty-tail instance follows from the general fixed
result law; no separate chain interpreter is retained. -/
theorem cons_chain_return_pending_prefix (environment : MinEnv) (state : St)
    (fuel : Nat) (previous : Stack) (head : Atom) (name : String)
    (bindings : Metta.Bindings) (closed : head.vars = []) :
    let source := Atom.expr [.sym "cons-atom", head, .expr []]
    let template := Atom.expr [.sym "return", .var name]
    let body := Atom.expr [.sym "chain", source, .var name, template]
    let functionValue := Atom.expr [.sym "function", body]
    let parent : Frame := { atom := functionValue, ret := .function, vars := varsCopy previous }
    PendingSteps environment
      (fuel + 5, state, [evalResult previous functionValue bindings])
      (fuel + 1, state,
        [⟨{ atom := .expr [.sym "return", .expr [head]], vars := varsCopy previous, fin := true } ::
          parent :: previous, bindings⟩]) :=
  cons_chain_return_pending_prefix_of_fixed environment state fuel previous head [] name bindings
    (Metta.instantiate_of_closed bindings _ (by simp [Atom.vars, closed]))

namespace Controls

private def bindings : Metta.Bindings := [.val "bound" (.sym "answer")]

private theorem correlated_cons_materialization :
    instantiate bindings (.expr [.var "bound", .var "free", .var "free"]) =
      .expr [.sym "answer", .var "free", .var "free"] := by
  have bound := Metta.instantiate_singleton_val_var_of_not_mem "bound" (.sym "answer")
    (by simp [Atom.vars])
  have free := Metta.instantiate_singleton_val_inert "bound" (.sym "answer") (.var "free")
    (by simp [Atom.vars])
  simp only [bindings, instantiate, Bindings.resolveAtom, List.map_cons, List.map_nil]
    at bound free ⊢
  simp only [bound, free]

private theorem correlated_decons_materialization :
    instantiate bindings (.expr [.var "bound", .expr [.var "free", .var "free"]]) =
      .expr [.sym "answer", .expr [.var "free", .var "free"]] := by
  have bound := Metta.instantiate_singleton_val_var_of_not_mem "bound" (.sym "answer")
    (by simp [Atom.vars])
  have free := Metta.instantiate_singleton_val_inert "bound" (.sym "answer") (.var "free")
    (by simp [Atom.vars])
  simp only [bindings, instantiate, Bindings.resolveAtom, List.map_cons, List.map_nil]
    at bound free ⊢
  simp only [bound, free]

/-- The primitive really emits an unresolved bound field. The later chain
handler resolves it while retaining two occurrences of the same free field;
requiring the raw primitive result to be fixed would exclude this execution. -/
theorem raw_cons_chain_materializes_correlated_result
    (environment : MinEnv) (state : St) (fuel : Nat) (previous : Stack)
    (scope : List VarName) (name : String) :
    let source := Atom.expr [.sym "cons-atom", .var "bound", .expr [.var "free", .var "free"]]
    let raw := Atom.expr [.var "bound", .var "free", .var "free"]
    let result := Atom.expr [.sym "answer", .var "free", .var "free"]
    let template := Atom.expr [.sym "return", .var name]
    let body := Atom.expr [.sym "chain", source, .var name, template]
    let functionValue := Atom.expr [.sym "function", body]
    let parent : Frame := { atom := functionValue, ret := .function, vars := varsCopy previous }
    interpretStack1 environment (fuel + 4) state
        ⟨{ atom := source, vars := scope } :: previous, bindings⟩ =
      ([finItem previous raw bindings], state) ∧
    PendingSteps environment
      (fuel + 5, state, [evalResult previous functionValue bindings])
      (fuel + 1, state,
        [⟨{ atom := .expr [.sym "return", result], vars := varsCopy previous, fin := true } ::
          parent :: previous, bindings⟩]) ∧
    instantiate bindings raw ≠ raw ∧ result.vars = ["free", "free"] := by
  intro source raw result template body functionValue parent
  refine ⟨step_cons_atom environment (fuel + 4) state previous scope _ _ bindings, ?_, ?_, ?_⟩
  · simpa only [raw, result, correlated_cons_materialization] using
      primitive_chain_return_pending_prefix environment state fuel previous source raw name bindings
        (fun continuation => by simp [source, raw, atomToStack, interpretStack1])
  · rw [show raw = .expr [.var "bound", .var "free", .var "free"] from rfl,
      correlated_cons_materialization]
    simp
  · simp [result, Atom.vars]

/-- Deconstruction has the same delayed materialization boundary. Its tail
remains a nested expression with both correlated residual occurrences. -/
theorem raw_decons_chain_materializes_correlated_result
    (environment : MinEnv) (state : St) (fuel : Nat) (previous : Stack) (name : String) :
    let source := Atom.expr [.sym "decons-atom", .expr [.var "bound", .var "free", .var "free"]]
    let raw := Atom.expr [.var "bound", .expr [.var "free", .var "free"]]
    let result := Atom.expr [.sym "answer", .expr [.var "free", .var "free"]]
    let template := Atom.expr [.sym "return", .var name]
    let body := Atom.expr [.sym "chain", source, .var name, template]
    let functionValue := Atom.expr [.sym "function", body]
    let parent : Frame := { atom := functionValue, ret := .function, vars := varsCopy previous }
    PendingSteps environment
      (fuel + 5, state, [evalResult previous functionValue bindings])
      (fuel + 1, state,
        [⟨{ atom := .expr [.sym "return", result], vars := varsCopy previous, fin := true } ::
          parent :: previous, bindings⟩]) ∧
    instantiate bindings raw ≠ raw ∧ result.vars = ["free", "free"] := by
  intro source raw result template body functionValue parent
  refine ⟨?_, ?_, ?_⟩
  · simpa only [raw, result, correlated_decons_materialization] using
      primitive_chain_return_pending_prefix environment state fuel previous source raw name bindings
        (fun continuation => by simp [source, raw, atomToStack, interpretStack1])
  · rw [show raw = .expr [.var "bound", .expr [.var "free", .var "free"]] from rfl,
      correlated_decons_materialization]
    simp
  · simp [result, Atom.vars]

end Controls


/-! ## Covered retained native execution -/

namespace Retained

open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- These instructions invoke a nested fuel-indexed evaluator. Other native
instruction steps have no dependence on that nested evaluation budget. -/
def nestedBudgetInstruction : Atom → Bool
  | .expr (.sym head :: _) =>
      ["get-type", "get-type-space", "metta", "capture", "metta-thread", "collapse-bind", "import!"].contains head
  | _ => false

/-- Finished frames use their saved return handler. An unfinished nested
interpretation needs its own coverage before this region can advance it. -/
def stepReady (item : Item) : Bool :=
  match item.stack with
  | [] => true
  | top :: _ => top.fin || !nestedBudgetInstruction top.atom

/-- The readiness test is justified against the actual interpreter step.
No equality of two finite approximations is used as a readiness criterion. -/
theorem stepReady_independent (environment : MinEnv) (state : St) (item : Item)
    (first second : Nat) (ready : stepReady item = true) :
    interpretStack1 environment first state item = interpretStack1 environment second state item := by
  rcases item with ⟨stack, bindings⟩
  cases stack with
  | nil => simp [interpretStack1]
  | cons top previous =>
    by_cases finished : top.fin = true
    · simp only [interpretStack1, finished, if_true]
    · have unfinished : top.fin = false := Bool.eq_false_iff.mpr finished
      have simple : nestedBudgetInstruction top.atom = false := by
        simpa [stepReady, unfinished] using ready
      simp only [interpretStack1, unfinished, Bool.false_eq_true, if_false]
      split <;> try rfl
      all_goals simp_all [nestedBudgetInstruction]

/-- An actual instruction occurrence, including its saved caller and binding
frame. Equal payloads at different positions remain separate receipts. -/
structure Receipt where
  before : St
  instruction : Item
  spawned : List Item
  after : St

/-- Coverage makes the receipt a local execution equation at every nested
budget; this property is proved for each recorded step. -/
def Receipt.Valid (environment : MinEnv) (receipt : Receipt) : Prop :=
  stepReady receipt.instruction = true ∧
    ∀ fuel, interpretStack1 environment fuel receipt.before receipt.instruction =
      (receipt.spawned, receipt.after)

/-- The native runtime state and complete pending work are retained. Completed
pairs are chronological and keep internal Empty sentinels; public observation
applies the interpreter's existing Empty filter. -/
structure Configuration where
  depth : Nat
  runtime : St
  pending : List Item
  completed : List (Atom × Bindings)
  receipts : List Receipt := []

def Configuration.published (state : Configuration) : List (Atom × Bindings) :=
  state.completed.filter fun pair => pair.1 != emptyA

def Configuration.deepen (extra : Nat) (state : Configuration) : Configuration :=
  { state with depth := state.depth + extra }

@[simp] theorem Configuration.deepen_zero (state : Configuration) : state.deepen 0 = state := rfl

theorem Configuration.deepen_add (first second : Nat) (state : Configuration) :
    (state.deepen first).deepen second = state.deepen (first + second) := by
  cases state
  simp [Configuration.deepen, Nat.add_assoc]

inductive Request where
  | interpreterDepth
  | nestedEvaluation
  deriving DecidableEq, Repr

/-- One native step's final pairs, before public Empty filtering. -/
def finals (results : List Item) : List (Atom × Bindings) :=
  (results.filter isFinal).map finalPair

/-- The actual next queue and world after processing its first item. -/
def advance (environment : MinEnv) (state : Configuration) (fuel : Nat)
    (item : Item) (rest : List Item) : Configuration :=
  let executed := interpretStack1 environment fuel state.runtime item
  { depth := fuel
    runtime := executed.2
    pending := executed.1.filter (fun result => !isFinal result) ++ rest
    completed := state.completed ++ finals executed.1
    receipts := state.receipts ++ [⟨state.runtime, item, executed.1, executed.2⟩] }

def emitted (environment : MinEnv) (state : Configuration) (fuel : Nat)
    (item : Item) : List (Atom × Bindings) :=
  (finals (interpretStack1 environment fuel state.runtime item).1).filter fun pair => pair.1 != emptyA

/-- A regional adapter of the existing native step, not another evaluator.
A blocked operation and every original caller stay in the saved configuration. -/
def machine (environment : MinEnv) :
    Machine Configuration (Atom × Bindings) Configuration Request where
  step state :=
    match state.pending with
    | [] => some (.finish state)
    | item :: rest =>
      match state.depth with
      | 0 => some (.call .interpreterDepth state)
      | fuel + 1 =>
        if stepReady item then
          let next := advance environment state fuel item rest
          match emitted environment state fuel item with
          | [] => some (.silent next)
          | head :: tail => some (.publish (head :: tail) next)
        else some (.call .nestedEvaluation state)

theorem empty_finished (environment : MinEnv) (state : Configuration)
    (empty : state.pending = []) (budget : Nat) :
    (machine environment).run (budget + 1) state = ([], .finished state) :=
  (machine environment).run_succ_finish (by simp [machine, empty])

theorem depth_blocked (environment : MinEnv) (state : Configuration)
    (item : Item) (rest : List Item) (pending : state.pending = item :: rest)
    (depth : state.depth = 0) (budget : Nat) :
    (machine environment).run (budget + 1) state = ([], .suspended .interpreterDepth state) :=
  (machine environment).run_succ_call (by simp [machine, pending, depth])

theorem nested_blocked (environment : MinEnv) (state : Configuration)
    (item : Item) (rest : List Item) (pending : state.pending = item :: rest)
    (fuel : Nat) (depth : state.depth = fuel + 1) (uncovered : stepReady item = false) (budget : Nat) :
    (machine environment).run (budget + 1) state = ([], .suspended .nestedEvaluation state) :=
  (machine environment).run_succ_call (by simp [machine, pending, depth, uncovered])

theorem run_succ_ready (environment : MinEnv) (state : Configuration)
    (item : Item) (rest : List Item) (pending : state.pending = item :: rest)
    (fuel : Nat) (depth : state.depth = fuel + 1) (ready : stepReady item = true) (budget : Nat) :
    (machine environment).run (budget + 1) state =
      let later := (machine environment).run budget (advance environment state fuel item rest)
      (emitted environment state fuel item ++ later.1, later.2) := by
  simp only [Machine.run, machine, pending, depth, ready, if_true]
  cases emitted environment state fuel item <;> simp

theorem advance_published (environment : MinEnv) (state : Configuration)
    (fuel : Nat) (item : Item) (rest : List Item) :
    (advance environment state fuel item rest).published =
      state.published ++ emitted environment state fuel item := by
  simp [Configuration.published, advance, emitted, List.filter_append]

theorem advance_replay (environment : MinEnv) (state : Configuration)
    (item : Item) (rest : List Item) (pending : state.pending = item :: rest)
    (fuel : Nat) (depth : state.depth = fuel + 1) :
    interpretFuel environment state.depth state.runtime state.pending state.completed.reverse =
      let after := advance environment state fuel item rest
      interpretFuel environment after.depth after.runtime after.pending after.completed.reverse := by
  rw [pending, depth, FuelConvergenceInterpreter.interpretFuel_succ]
  simp only [advance, finals, List.reverse_append]

theorem advance_receipt_valid (environment : MinEnv) (state : Configuration)
    (fuel : Nat) (item : Item) (ready : stepReady item = true) :
    Receipt.Valid environment
      ⟨state.runtime, item, (interpretStack1 environment fuel state.runtime item).1,
        (interpretStack1 environment fuel state.runtime item).2⟩ := by
  refine ⟨ready, ?_⟩
  intro other
  exact (stepReady_independent environment state.runtime item other fuel ready).trans (Prod.eta _).symm

theorem advance_deepen (environment : MinEnv) (state : Configuration) (extra fuel : Nat)
    (item : Item) (rest : List Item) (ready : stepReady item = true) :
    advance environment (state.deepen extra) (fuel + extra) item rest =
      (advance environment state fuel item rest).deepen extra := by
  simp only [advance, Configuration.deepen]
  rw [stepReady_independent environment state.runtime item (fuel + extra) fuel ready]

theorem emitted_deepen (environment : MinEnv) (state : Configuration) (extra fuel : Nat)
    (item : Item) (ready : stepReady item = true) :
    emitted environment (state.deepen extra) (fuel + extra) item = emitted environment state fuel item := by
  simp only [emitted, Configuration.deepen]
  rw [stepReady_independent environment state.runtime item (fuel + extra) fuel ready]

/-- Completed execution agrees with the original interpreter and carries the
exact chronological publication and newly checked instruction receipts. -/
theorem completed_replay (environment : MinEnv) (budget : Nat)
    (state final : Configuration) (events : List (Atom × Bindings))
    (ran : (machine environment).run budget state = (events, .finished final)) :
    final.pending = [] ∧
    interpretFuel environment state.depth state.runtime state.pending state.completed.reverse =
      (final.published, final.runtime) ∧
    final.published = state.published ++ events ∧
    ∃ receipts, final.receipts = state.receipts ++ receipts ∧
      ∀ receipt ∈ receipts, Receipt.Valid environment receipt := by
  induction budget generalizing state events with
  | zero => cases ran
  | succ budget ih =>
    cases pending : state.pending with
    | nil =>
      rw [empty_finished environment state pending budget] at ran
      obtain ⟨rfl, same⟩ := Prod.mk.inj ran
      cases same
      refine ⟨pending, ?_, by simp, [], by simp, by simp⟩
      rw [FuelConvergenceInterpreter.interpretFuel_nil]
      simp [Configuration.published]
    | cons item rest =>
      cases depth : state.depth with
      | zero =>
        rw [depth_blocked environment state item rest pending depth budget] at ran
        cases ran
      | succ fuel =>
        cases ready : stepReady item with
        | false =>
          rw [nested_blocked environment state item rest pending fuel depth ready budget] at ran
          cases ran
        | true =>
          rw [run_succ_ready environment state item rest pending fuel depth ready budget] at ran
          cases later : (machine environment).run budget (advance environment state fuel item rest) with
          | mk after outcome =>
            rw [later] at ran
            obtain ⟨sameEvents, sameOutcome⟩ := Prod.mk.inj ran
            cases sameOutcome
            obtain ⟨empty, replay, published, receipts, history, valid⟩ :=
              ih (advance environment state fuel item rest) after later
            refine ⟨empty, ?_,
              ?_, ⟨state.runtime, item, (interpretStack1 environment fuel state.runtime item).1,
                (interpretStack1 environment fuel state.runtime item).2⟩ :: receipts, ?_, ?_⟩
            · simpa only [depth, pending] using
                (advance_replay environment state item rest pending fuel depth).trans replay
            · rw [published, advance_published, List.append_assoc, sameEvents]
            · rw [history]
              simp only [advance, List.append_assoc, List.singleton_append]
            · intro receipt member
              rcases List.mem_cons.mp member with rfl | member
              · exact advance_receipt_valid environment state fuel item ready
              · exact valid receipt member

/-- Raising the native budget preserves a completed covered run, including
its original instruction receipts and complete runtime world. -/
theorem completed_deepen (environment : MinEnv) (budget : Nat)
    (state final : Configuration) (events : List (Atom × Bindings))
    (ran : (machine environment).run budget state = (events, .finished final)) (extra : Nat) :
    (machine environment).run budget (state.deepen extra) = (events, .finished (final.deepen extra)) := by
  induction budget generalizing state events with
  | zero => cases ran
  | succ budget ih =>
    cases pending : state.pending with
    | nil =>
      rw [empty_finished environment state pending budget] at ran
      obtain ⟨rfl, same⟩ := Prod.mk.inj ran
      cases same
      exact empty_finished environment (final.deepen extra) pending budget
    | cons item rest =>
      cases depth : state.depth with
      | zero =>
        rw [depth_blocked environment state item rest pending depth budget] at ran
        cases ran
      | succ fuel =>
        cases ready : stepReady item with
        | false =>
          rw [nested_blocked environment state item rest pending fuel depth ready budget] at ran
          cases ran
        | true =>
          rw [run_succ_ready environment state item rest pending fuel depth ready budget] at ran
          cases later : (machine environment).run budget (advance environment state fuel item rest) with
          | mk after outcome =>
            rw [later] at ran
            obtain ⟨sameEvents, sameOutcome⟩ := Prod.mk.inj ran
            cases sameOutcome
            rw [run_succ_ready environment (state.deepen extra) item rest pending (fuel + extra)
              (by simp [Configuration.deepen, depth, Nat.add_right_comm]) ready budget,
              advance_deepen environment state extra fuel item rest ready,
              ih (advance environment state fuel item rest) after later,
              emitted_deepen environment state extra fuel item ready]
            exact Prod.ext sameEvents rfl

/-- A completed guarded run fixes the original interpreter's output at every
larger native budget. Its full final state, including the world, is fixed too. -/
theorem completed_interpreter_all_depths (environment : MinEnv) (budget : Nat)
    (state final : Configuration) (events : List (Atom × Bindings))
    (ran : (machine environment).run budget state = (events, .finished final)) (extra : Nat) :
    interpretFuel environment (state.depth + extra) state.runtime state.pending state.completed.reverse =
      (final.published, final.runtime) :=
  (completed_replay environment budget (state.deepen extra) (final.deepen extra) events
    (completed_deepen environment budget state final events ran extra)).2.1

/-- Scheduler continuation uses the common saved-result interface. -/
theorem resume_add (environment : MinEnv) (first second : Nat) (state : Configuration) :
    (machine environment).run (first + second) state =
      (machine environment).continueRun second ((machine environment).run first state) :=
  (machine environment).run_add first second state

/-- A depth grant changes only the pending native budget. An uncovered nested
operation remains a separate request, with no invented completion. -/
def continueRun (environment : MinEnv) (budget extra : Nat) :
    List (Atom × Bindings) × Outcome Configuration Configuration Request →
    List (Atom × Bindings) × Outcome Configuration Configuration Request
  | (events, .suspended .interpreterDepth saved) =>
      let later := (machine environment).run budget (saved.deepen extra)
      (events ++ later.1, later.2)
  | result => (machine environment).continueRun budget result

theorem continueRun_events_prefix (environment : MinEnv) (budget extra : Nat)
    (result : List (Atom × Bindings) × Outcome Configuration Configuration Request) :
    result.1 <+: (continueRun environment budget extra result).1 := by
  rcases result with ⟨events, outcome⟩
  cases outcome with
  | suspended request saved =>
    cases request <;> simp only [continueRun, Machine.continueRun]
    · exact List.prefix_append _ _
    · exact List.prefix_rfl
  | _ => exact (machine environment).continueRun_events_prefix budget _

/-- A depth grant cannot silently authorize an uncovered nested evaluator. -/
theorem nested_request_retained (environment : MinEnv) (budget extra : Nat)
    (events : List (Atom × Bindings)) (saved : Configuration) :
    continueRun environment budget extra (events, .suspended .nestedEvaluation saved) =
      (events, .suspended .nestedEvaluation saved) := rfl

/-- Local coverage refines the existing native pending-step relation. -/
def coveredPendingStep (environment : MinEnv) (before after : PendingState) : Prop :=
  pendingStep environment before after ∧
    ∀ item rest, before.2.2 = item :: rest → stepReady item = true

abbrev CoveredPendingSteps (environment : MinEnv) :=
  Relation.ReflTransGen (coveredPendingStep environment)

theorem CoveredPendingSteps.pending {environment : MinEnv} {before after : PendingState}
    (path : CoveredPendingSteps environment before after) : PendingSteps environment before after :=
  by
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | head step _ ih => exact .head step.1 ih

theorem coveredPendingStep_singleton {environment : MinEnv} {fuel : Nat} {state nextState : St}
    {item next : Item} (ready : stepReady item = true)
    (step : interpretStack1 environment fuel state item = ([next], nextState))
    (pending : isFinal next = false) :
    coveredPendingStep environment (fuel + 1, state, [item]) (fuel, nextState, [next]) := by
  refine ⟨pendingStep_singleton step pending, ?_⟩
  intro other rest same
  have head : item = other := (List.cons.inj same).1
  simpa only [← head] using ready

def ofPending (state : PendingState) (queued : List Item)
    (completed : List (Atom × Bindings)) (receipts : List Receipt) : Configuration :=
  ⟨state.1, state.2.1, state.2.2 ++ queued, completed, receipts⟩

theorem coveredPendingStep_run {environment : MinEnv} {before after : PendingState}
    (step : coveredPendingStep environment before after) (queued : List Item)
    (completed : List (Atom × Bindings)) (receipts : List Receipt) :
    ∃ receipt, Receipt.Valid environment receipt ∧
      (machine environment).run 1 (ofPending before queued completed receipts) =
        ([], .exhausted (ofPending after queued completed (receipts ++ [receipt]))) := by
  obtain ⟨⟨fuel, state, nextState, item, rest, results, rfl, rfl, step, pending⟩, ready⟩ := step
  have covered := ready item rest rfl
  have filters : results.filter isFinal = [] ∧
      results.filter (fun result => !isFinal result) = results := by
    clear step
    induction results with
    | nil => simp
    | cons result results ih =>
      have first := pending result (by simp)
      have later := ih (fun result member => pending result (by simp [member]))
      simp [first, later.1, later.2]
  let receipt : Receipt := ⟨state, item, results, nextState⟩
  refine ⟨receipt, ⟨covered, ?_⟩, ?_⟩
  · intro budget
    exact (stepReady_independent environment state item budget fuel covered).trans step
  · rw [run_succ_ready environment (ofPending (fuel + 1, state, item :: rest)
      queued completed receipts) item (rest ++ queued) rfl fuel rfl covered 0]
    simp [Machine.run, advance, emitted, ofPending, step, finals, filters.1, filters.2,
      List.append_assoc, receipt]

theorem CoveredPendingSteps.retained {environment : MinEnv} {before after : PendingState}
    (path : CoveredPendingSteps environment before after) (queued : List Item)
    (completed : List (Atom × Bindings)) (receipts : List Receipt) :
    ∃ ticks added, (∀ receipt ∈ added, Receipt.Valid environment receipt) ∧
      (machine environment).run ticks (ofPending before queued completed receipts) =
        ([], .exhausted (ofPending after queued completed (receipts ++ added))) := by
  induction path using Relation.ReflTransGen.head_induction_on generalizing receipts with
  | refl => exact ⟨0, [], by simp, by simp [Machine.run]⟩
  | head step _ ih =>
    obtain ⟨receipt, valid, first⟩ := coveredPendingStep_run step queued completed receipts
    obtain ⟨ticks, added, checked, later⟩ := ih (receipts ++ [receipt])
    refine ⟨1 + ticks, receipt :: added, ?_, ?_⟩
    · intro chosen member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid
      · exact checked chosen member
    · rw [(machine environment).run_add, first]
      simp only [Machine.continueRun, later, List.nil_append]
      simp only [List.append_assoc, List.singleton_append]

end Retained

end Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
