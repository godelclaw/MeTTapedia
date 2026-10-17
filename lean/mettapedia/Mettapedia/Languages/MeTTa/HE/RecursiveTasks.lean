import Mettapedia.Languages.MeTTa.HE.Eval

/-!
# First-order control for the recursive HE evaluator

Requests cover all six mutually recursive evaluator functions and the finite
list traversals between their calls. Continuations retain the selected value,
bindings, remaining alternatives and argument types as data. Every request that
leads to evaluation also retains the atoms its continuation holds, which equation
instances must avoid. The meanings below
refer to the existing recursive evaluator; the executable control machine is
constructed separately. Grounded dispatch, matching and type checks remain
their existing interfaces. The space is read-only in this evaluator profile.

The profile retains the evaluator's explicit fuel and its accumulation of all
applicable function types. It is not an identification with a native runtime
that selects only its first applicable type, or with effectful evaluation.
-/

open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory (aliasConstraints)

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveTasks

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive Task where
  | atom (value expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom := [])
  | expression (value expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom := [])
  | func (value operatorType : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom := [])
  | args (values types : List Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom := [])
  | tuple (value : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom := [])
  | call (value expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom := [])
  | functions (value expected : Atom) (bindings : Bindings) (fuel : Nat) (types : List Atom)
      (live : List Atom := [])
  | bindingAlternatives (value operatorType resultType : Atom) (fuel : Nat)
      (alternatives : List Bindings) (live : List Atom := [])
  | heads (operatorType : Atom) (arguments : List Atom) (fuel : Nat) (alternatives : ResultSet)
      (live : List Atom := [])
  | argumentHeads (original : Atom) (remaining types : List Atom) (fuel : Nat)
      (alternatives : ResultSet) (live : List Atom := [])
  | tupleHeads (tail : Atom) (fuel : Nat) (alternatives : ResultSet) (live : List Atom := [])
  | calls (expected : Atom) (fuel : Nat) (alternatives : ResultSet) (live : List Atom := [])
  | atoms (expected : Atom) (fuel : Nat) (alternatives : ResultSet) (live : List Atom := [])
  | returned (original value expected : Atom) (bindings : Bindings) (fuel : Nat)
      (live : List Atom := [])
  | returns (original expected : Atom) (fuel : Nat) (alternatives : ResultSet)
      (live : List Atom := [])
  | equations (original expected : Atom) (incoming : Bindings) (fuel : Nat) (alternatives : ResultSet)
      (live : List Atom := [])
  | grounded (original expected : Atom) (incoming : Bindings) (fuel : Nat) (alternatives : ResultSet)
      (live : List Atom := [])
  | tupleCalls (value expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom := [])
  | invocation (mode : InvocationMode) (value : Atom) (bindings : Bindings) (fuel : Nat)
      (live : List Atom := []) (caller : Option Atom := none)
  | produced (value : Atom) (bindings : Bindings) (fuel : Nat)
      (live : List Atom := []) (caller : Option Atom := none)
      (provenance : InvocationProvenance := .emitted)
  | productions (fuel : Nat) (alternatives : ResultSet)
      (live : List Atom := []) (caller : Option Atom := none)
      (provenance : InvocationProvenance := .emitted)
  | minimal (value : Atom) (bindings : Bindings) (fuel : Nat)
      (live : List Atom := []) (caller : Option Atom := none)
  | minimals (fuel : Nat) (alternatives : ResultSet)
      (live : List Atom := []) (caller : Option Atom := none)
  | primitive (value : Atom) (bindings : Bindings) (fuel : Nat)
      (live : List Atom := []) (caller : Option Atom := none)
  | chainRows (name : String) (template : Atom) (fuel : Nat) (alternatives : ResultSet)
  | functionBody (value : Atom) (bindings : Bindings) (fuel : Nat)
      (live : List Atom := []) (caller : Option Atom := none)
  | bodyResults (fuel : Nat) (alternatives : ResultSet)
      (live : List Atom := []) (caller : Option Atom := none)
  | producerResults (mode : InvocationMode) (original : Atom) (incoming : Bindings)
      (fuel : Nat) (live : List Atom) (emptyReply : Atom) (alternatives : ResultSet)
  | completed (value expected : Atom) (bindings : Bindings) (fuel : Nat)
  deriving Repr, DecidableEq

/-- Remaining evaluator depth of a suspended request. -/
def Task.depth : Task → Nat
  | .atom _ _ _ fuel _ => fuel
  | .expression _ _ _ fuel _ => fuel
  | .func _ _ _ fuel _ => fuel
  | .args _ _ _ fuel _ => fuel
  | .tuple _ _ fuel _ => fuel
  | .call _ _ _ fuel _ => fuel
  | .functions _ _ _ fuel _ _ => fuel
  | .bindingAlternatives _ _ _ fuel _ _ => fuel
  | .heads _ _ fuel _ _ => fuel
  | .argumentHeads _ _ _ fuel _ _ => fuel
  | .tupleHeads _ fuel _ _ => fuel
  | .calls _ fuel _ _ => fuel
  | .atoms _ fuel _ _ => fuel
  | .returned _ _ _ _ fuel _ => fuel
  | .returns _ _ fuel _ _ => fuel
  | .equations _ _ _ fuel _ _ => fuel
  | .grounded _ _ _ fuel _ _ => fuel
  | .tupleCalls _ _ _ fuel _ => fuel
  | .invocation _ _ _ fuel _ _ => fuel
  | .produced _ _ fuel _ _ _ => fuel
  | .productions fuel _ _ _ _ => fuel
  | .minimal _ _ fuel _ _ => fuel
  | .minimals fuel _ _ _ => fuel
  | .primitive _ _ fuel _ _ => fuel
  | .chainRows _ _ fuel _ => fuel
  | .functionBody _ _ fuel _ _ => fuel
  | .bodyResults fuel _ _ _ => fuel
  | .producerResults _ _ _ fuel _ _ _ => fuel
  | .completed _ _ _ fuel => fuel

/-- Grant more depth to this pending request, keeping every selected value,
remaining alternative and visible name unchanged. -/
def Task.replenish (extra : Nat) : Task → Task
  | .atom value expected bindings fuel live => .atom value expected bindings (fuel + extra) live
  | .expression value expected bindings fuel live => .expression value expected bindings (fuel + extra) live
  | .func value operatorType bindings fuel live => .func value operatorType bindings (fuel + extra) live
  | .args values types bindings fuel live => .args values types bindings (fuel + extra) live
  | .tuple value bindings fuel live => .tuple value bindings (fuel + extra) live
  | .call value expected bindings fuel live => .call value expected bindings (fuel + extra) live
  | .functions value expected bindings fuel types live => .functions value expected bindings (fuel + extra) types live
  | .bindingAlternatives value operatorType resultType fuel alternatives live => .bindingAlternatives value operatorType resultType (fuel + extra) alternatives live
  | .heads operatorType arguments fuel alternatives live => .heads operatorType arguments (fuel + extra) alternatives live
  | .argumentHeads original remaining types fuel alternatives live => .argumentHeads original remaining types (fuel + extra) alternatives live
  | .tupleHeads tail fuel alternatives live => .tupleHeads tail (fuel + extra) alternatives live
  | .calls expected fuel alternatives live => .calls expected (fuel + extra) alternatives live
  | .atoms expected fuel alternatives live => .atoms expected (fuel + extra) alternatives live
  | .returned original value expected bindings fuel live =>
      .returned original value expected bindings (fuel + extra) live
  | .returns original expected fuel alternatives live => .returns original expected (fuel + extra) alternatives live
  | .equations original expected incoming fuel alternatives live => .equations original expected incoming (fuel + extra) alternatives live
  | .grounded original expected incoming fuel alternatives live => .grounded original expected incoming (fuel + extra) alternatives live
  | .tupleCalls value expected bindings fuel live => .tupleCalls value expected bindings (fuel + extra) live
  | .invocation mode value bindings fuel live caller =>
      .invocation mode value bindings (fuel + extra) live caller
  | .produced value bindings fuel live caller provenance =>
      .produced value bindings (fuel + extra) live caller provenance
  | .productions fuel alternatives live caller provenance =>
      .productions (fuel + extra) alternatives live caller provenance
  | .minimal value bindings fuel live caller =>
      .minimal value bindings (fuel + extra) live caller
  | .minimals fuel alternatives live caller => .minimals (fuel + extra) alternatives live caller
  | .primitive value bindings fuel live caller =>
      .primitive value bindings (fuel + extra) live caller
  | .chainRows name template fuel alternatives => .chainRows name template (fuel + extra) alternatives
  | .functionBody value bindings fuel live caller =>
      .functionBody value bindings (fuel + extra) live caller
  | .bodyResults fuel alternatives live caller => .bodyResults (fuel + extra) alternatives live caller
  | .producerResults mode original incoming fuel live emptyReply alternatives =>
      .producerResults mode original incoming (fuel + extra) live emptyReply alternatives
  | .completed value expected bindings fuel => .completed value expected bindings (fuel + extra)

theorem Task.replenish_zero (task : Task) : task.replenish 0 = task := by
  cases task <;> rfl

theorem Task.replenish_add (first second : Nat) (task : Task) :
    (task.replenish first).replenish second = task.replenish (first + second) := by
  cases task <;> simp only [Task.replenish, Nat.add_assoc]

def resultType (operatorType : Atom) : Atom :=
  if getFunctionRetType operatorType == some Atom.expressionType
  then Atom.undefinedType
  else (getFunctionRetType operatorType).getD Atom.undefinedType

def functionTail (head : Atom) (results : ResultSet) : ResultSet :=
  results.map fun (value, bindings) =>
    if argumentsSucceeded value = false then (value, bindings)
    else (.expression (head :: argumentValues value), bindings)

def argumentTail (head : Atom) (results : ResultSet) : ResultSet :=
  results.map fun (value, bindings) =>
    if argumentsSucceeded value = false then (value, bindings)
    else (argumentPacket (head :: argumentValues value), bindings)

def tupleTail (head : Atom) (results : ResultSet) : ResultSet :=
  results.map fun (value, bindings) =>
    if isEmptyOrError value then (value, bindings)
    else (.expression (head :: atomElements value), bindings)

def successPriority (results : ResultSet) : ResultSet :=
  let successes := results.filter fun (value, _) => !isErrorAtom value
  if !successes.isEmpty then successes
  else results.filter fun (value, _) => isErrorAtom value

def functionFallback (space : Space) (value expected : Atom) (bindings : Bindings)
    (fuel : Nat) (types : List Atom) (results : ResultSet)
    (lookup : TypeLookup := rawTypeLookup space) : ResultSet :=
  if !results.isEmpty then results
  else
    let checksFailed := types.all fun operatorType =>
      if isFunctionType operatorType then
        match checkIfFunctionTypeIsApplicable value operatorType expected space bindings fuel lookup with
        | .inl _ => true
        | .inr _ => false
      else true
    if checksFailed then
      types.flatMap fun operatorType =>
        if isFunctionType operatorType then
          match checkIfFunctionTypeIsApplicable value operatorType expected space bindings fuel lookup with
          | .inl errors => errors.map fun error => (error, bindings)
          | .inr _ => []
        else []
    else []

/-- A raw reply and an ordinary typed reply have different saved consumers. -/
def invocationFinish (space : Space) (dispatch : GroundedDispatch)
    (mode : InvocationMode) (original : Atom) (fuel : Nat) (live : List Atom)
    (results : ResultSet) : ResultSet :=
  match mode with
  | .raw => results
  | .ordinary expected => results.flatMap fun (value, bindings) =>
      ordinaryCallReturn original value bindings
        (fun value bindings => evalAtom space dispatch value expected bindings fuel live)

/-- Ordered meanings of requests, using the existing evaluator for recursive
calls rather than the new machine's transition function. -/
def Task.denote (space : Space) (dispatch : GroundedDispatch) : Task → ResultSet
  | .atom value expected bindings fuel live => evalAtom space dispatch value expected bindings fuel live
  | .expression value expected bindings fuel live =>
      interpretExpression space dispatch value expected bindings fuel live
  | .func value operatorType bindings fuel live =>
      interpretFunction space dispatch value operatorType bindings fuel live
  | .args values types bindings fuel live =>
      interpretArgs space dispatch values types bindings fuel live
  | .tuple value bindings fuel live => interpretTuple space dispatch value bindings fuel live
  | .call value expected bindings fuel live =>
      mettaCall space dispatch value expected bindings fuel live
  | .functions value expected bindings fuel types live =>
      types.flatMap fun operatorType =>
        if isFunctionType operatorType then
          match checkIfFunctionTypeIsApplicable value operatorType expected space bindings fuel with
          | .inr alternatives => alternatives.flatMap fun selected =>
              (interpretFunction space dispatch value operatorType selected fuel
                (resultType operatorType :: live)).flatMap fun (result, output) =>
                mettaCall space dispatch result (resultType operatorType) output fuel live
          | .inl _ => []
        else []
  | .bindingAlternatives value operatorType expected fuel alternatives live =>
      alternatives.flatMap fun selected =>
        (interpretFunction space dispatch value operatorType selected fuel
          (expected :: live)).flatMap fun (result, output) =>
          mettaCall space dispatch result expected output fuel live
  | .heads operatorType arguments fuel alternatives live =>
      alternatives.flatMap fun (head, selected) =>
        if isEmptyOrError head then [(head, selected)]
        else match getFunctionArgTypes operatorType with
          | some types => functionTail head
              (interpretArgs space dispatch arguments types selected fuel (head :: live))
          | none => []
  | .argumentHeads original remaining types fuel alternatives live =>
      alternatives.flatMap fun (head, selected) =>
        if head != original && isEmptyOrError head then [(head, selected)]
        else argumentTail head
          (interpretArgs space dispatch remaining types selected fuel (head :: live))
  | .tupleHeads tail fuel alternatives live =>
      alternatives.flatMap fun (head, selected) =>
        if isEmptyOrError head then [(head, selected)]
        else tupleTail head (interpretTuple space dispatch tail selected fuel (head :: live))
  | .calls expected fuel alternatives live =>
      alternatives.flatMap fun (value, bindings) =>
        mettaCall space dispatch value expected bindings fuel live
  | .atoms expected fuel alternatives live =>
      alternatives.flatMap fun (value, bindings) =>
        evalAtom space dispatch value expected bindings fuel live
  | .returned original value expected bindings fuel live =>
      ordinaryCallReturn original value bindings
        (fun value bindings => evalAtom space dispatch value expected bindings fuel live)
  | .returns original expected fuel alternatives live =>
      alternatives.flatMap fun (value, bindings) =>
        ordinaryCallReturn original value bindings
          (fun value bindings => evalAtom space dispatch value expected bindings fuel live)
  | .equations _ _ incoming fuel alternatives _ =>
      alternatives.flatMap fun (rhs, selected) =>
        (mergeBindings selected (aliasConstraints incoming) fuel).filterMap fun merged =>
          if merged.hasLoop then none else some (merged.applyFull rhs fuel, merged)
  | .grounded _ _ incoming fuel alternatives _ =>
      alternatives.flatMap fun (value, selected) =>
        (mergeBindings selected incoming fuel).map fun merged => (merged.applyFull value fuel, merged)
  | .tupleCalls value expected bindings fuel live =>
      (interpretTuple space dispatch value bindings fuel (expected :: live)).flatMap
        fun (result, output) => mettaCall space dispatch result expected output fuel live
  | .invocation mode value bindings fuel live caller =>
      invoke space dispatch mode value bindings fuel live caller
  | .produced value bindings fuel live caller provenance =>
      invocationResult space dispatch value bindings fuel live caller provenance
  | .productions fuel alternatives live caller provenance =>
      alternatives.flatMap fun (value, bindings) =>
        invocationResult space dispatch value bindings fuel live caller provenance
  | .minimal value bindings fuel live caller =>
      minimalRun space dispatch value bindings fuel live caller
  | .minimals fuel alternatives live caller =>
      alternatives.flatMap fun (value, bindings) => minimalRun space dispatch value bindings fuel live caller
  | .primitive value bindings fuel live caller =>
      minimalStep space dispatch value bindings fuel live caller
  | .chainRows name template fuel alternatives =>
      alternatives.map fun (value, bindings) =>
        (chainSubstitute name (bindings.applyFull value fuel) template, bindings)
  | .functionBody value bindings fuel live caller =>
      HE.functionBody space dispatch value bindings fuel live caller
  | .bodyResults fuel alternatives live caller =>
      alternatives.flatMap fun (value, bindings) =>
        let materialized := bindings.applyFull value fuel
        if minimalInstruction materialized then
          HE.functionBody space dispatch materialized bindings fuel live caller
        else [(materialized, bindings)]
  | .producerResults mode original incoming fuel live emptyReply results =>
      invocationFinish space dispatch mode original fuel live
        (if results.isEmpty then [(emptyReply, incoming)] else
          results.flatMap fun (value, bindings) =>
            invocationResult space dispatch value bindings fuel (mode.pendingScope live) (some original))
  | .completed value expected bindings fuel => completedCallReturn space value expected bindings fuel


inductive Frame where
  | filter
  | heads (operatorType : Atom) (arguments : List Atom) (fuel : Nat) (live : List Atom := [])
  | argumentHeads (original : Atom) (remaining types : List Atom) (fuel : Nat) (live : List Atom := [])
  | tupleHeads (tail : Atom) (fuel : Nat) (live : List Atom := [])
  | calls (expected : Atom) (fuel : Nat) (live : List Atom := [])
  | functionTail (head : Atom)
  | argumentTail (head : Atom)
  | tupleSingleton
  | tupleTail (head : Atom)
  | append (remaining : Task)
  | prepend (selected : ResultSet)
  | fallback (value expected : Atom) (bindings : Bindings) (fuel : Nat) (types : List Atom)
  | invocationReturn (mode : InvocationMode) (original : Atom) (fuel : Nat) (live : List Atom)
  | producerResults (mode : InvocationMode) (original : Atom) (incoming : Bindings)
      (fuel : Nat) (live : List Atom) (emptyReply : Atom)
  | minimalResults (fuel : Nat) (live : List Atom) (caller : Option Atom)
  | chainResults (name : String) (template : Atom) (fuel : Nat)
  | functionTerminal (caller : Option Atom)
  | bodyResults (fuel : Nat) (live : List Atom) (caller : Option Atom)
  deriving Repr, DecidableEq

/-- Raise every still-pending evaluator depth in a continuation. Already
selected atoms, bindings, alternatives and live syntax are unchanged. -/
def Frame.deepen (extra : Nat) : Frame → Frame
  | .heads operatorType arguments fuel live => .heads operatorType arguments (fuel + extra) live
  | .argumentHeads original remaining types fuel live =>
      .argumentHeads original remaining types (fuel + extra) live
  | .tupleHeads tail fuel live => .tupleHeads tail (fuel + extra) live
  | .calls expected fuel live => .calls expected (fuel + extra) live
  | .append remaining => .append (remaining.replenish extra)
  | .fallback value expected bindings fuel types =>
      .fallback value expected bindings (fuel + extra) types
  | .invocationReturn mode original fuel live => .invocationReturn mode original (fuel + extra) live
  | .producerResults mode original incoming fuel live emptyReply =>
      .producerResults mode original incoming (fuel + extra) live emptyReply
  | .minimalResults fuel live caller => .minimalResults (fuel + extra) live caller
  | .chainResults name template fuel => .chainResults name template (fuel + extra)
  | .bodyResults fuel live caller => .bodyResults (fuel + extra) live caller
  | frame => frame

@[simp] theorem Frame.deepen_zero (frame : Frame) : frame.deepen 0 = frame := by
  cases frame <;> simp [deepen, Task.replenish_zero]

theorem Frame.deepen_add (first second : Nat) (frame : Frame) :
    (frame.deepen first).deepen second = frame.deepen (first + second) := by
  cases frame <;> simp [deepen, Task.replenish_add, Nat.add_assoc]

def Frame.denote (space : Space) (dispatch : GroundedDispatch) : Frame → ResultSet → ResultSet
  | .filter, results => successPriority results
  | .heads operatorType arguments fuel live, results =>
      (Task.heads operatorType arguments fuel results live).denote space dispatch
  | .argumentHeads original remaining types fuel live, results =>
      (Task.argumentHeads original remaining types fuel results live).denote space dispatch
  | .tupleHeads tail fuel live, results =>
      (Task.tupleHeads tail fuel results live).denote space dispatch
  | .calls expected fuel live, results =>
      (Task.calls expected fuel results live).denote space dispatch
  | .functionTail head, results => RecursiveTasks.functionTail head results
  | .argumentTail head, results => RecursiveTasks.argumentTail head results
  | .tupleSingleton, results => results.map HE.tupleSingleton
  | .tupleTail head, results => RecursiveTasks.tupleTail head results
  | .append remaining, results => results ++ remaining.denote space dispatch
  | .prepend selected, results => selected ++ results
  | .fallback value expected bindings fuel types, results =>
      functionFallback space value expected bindings fuel types results
  | .invocationReturn mode original fuel live, results =>
      invocationFinish space dispatch mode original fuel live results
  | .producerResults mode original incoming fuel live emptyReply, results =>
      (Task.producerResults mode original incoming fuel live emptyReply results).denote space dispatch
  | .minimalResults fuel live caller, results =>
      (Task.minimals fuel results live caller).denote space dispatch
  | .chainResults name template fuel, results =>
      (Task.chainRows name template fuel results).denote space dispatch
  | .functionTerminal caller, results => results.map fun (value, bindings) =>
      (HE.functionTerminal caller value, bindings)
  | .bodyResults fuel live caller, results =>
      (Task.bodyResults fuel results live caller).denote space dispatch

inductive Control where
  | work (task : Task)
  | returning (results : ResultSet)
  deriving Repr, DecidableEq

def Control.deepen (extra : Nat) : Control → Control
  | .work task => .work (task.replenish extra)
  | .returning results => .returning results

def Control.denote (space : Space) (dispatch : GroundedDispatch) : Control → ResultSet
  | .work task => task.denote space dispatch
  | .returning results => results

structure Configuration where
  space : Space
  control : Control
  stack : List Frame
  emitted : ResultSet
  deriving Repr, DecidableEq

def Configuration.initial (space : Space) (task : Task) : Configuration :=
  ⟨space, .work task, [], []⟩

/-- Increase all residual depth allowances, retaining the current world and
publication. This differs from a local grant to just one suspended request. -/
def Configuration.deepen (extra : Nat) (state : Configuration) : Configuration :=
  {state with control := state.control.deepen extra, stack := state.stack.map (Frame.deepen extra)}

@[simp] theorem Configuration.deepen_initial (extra : Nat) (space : Space) (task : Task) :
    (Configuration.initial space task).deepen extra =
      Configuration.initial space (task.replenish extra) := rfl

@[simp] theorem Configuration.deepen_emitted (extra : Nat) (state : Configuration) :
    (state.deepen extra).emitted = state.emitted := rfl

@[simp] theorem Configuration.deepen_space (extra : Nat) (state : Configuration) :
    (state.deepen extra).space = state.space := rfl

def Configuration.remaining (dispatch : GroundedDispatch) (state : Configuration) : ResultSet :=
  state.stack.foldl (fun results frame => frame.denote state.space dispatch results)
    (state.control.denote state.space dispatch)

def Configuration.denote (dispatch : GroundedDispatch) (state : Configuration) : ResultSet :=
  state.emitted ++ state.remaining dispatch

@[simp] theorem denote_initial (space : Space) (dispatch : GroundedDispatch) (task : Task) :
    (Configuration.initial space task).denote dispatch = task.denote space dispatch := rfl

end Mettapedia.Languages.MeTTa.HE.RecursiveTasks

namespace Mettapedia.Languages.MeTTa.HE.RecursiveScope

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks

def bindingAtoms (bindings : Bindings) : List Atom :=
  bindings.assignments.flatMap (fun entry => [.var entry.1, entry.2]) ++
    bindings.equalities.flatMap (fun edge => [.var edge.1, .var edge.2])

def resultAtoms (results : ResultSet) : List Atom :=
  results.flatMap fun entry => entry.1 :: bindingAtoms entry.2

/-- Every atom and binding field retained by a request. -/
def taskAtoms : Task → List Atom
  | .atom value expected bindings _ live
  | .expression value expected bindings _ live
  | .func value expected bindings _ live
  | .call value expected bindings _ live
  | .tupleCalls value expected bindings _ live =>
      [value, expected] ++ bindingAtoms bindings ++ live
  | .args values types bindings _ live => values ++ types ++ bindingAtoms bindings ++ live
  | .tuple value bindings _ live => value :: (bindingAtoms bindings ++ live)
  | .functions value expected bindings _ types live =>
      [value, expected] ++ types ++ bindingAtoms bindings ++ live
  | .bindingAlternatives value operatorType resultType _ alternatives live =>
      [value, operatorType, resultType] ++ alternatives.flatMap bindingAtoms ++ live
  | .heads operatorType arguments _ alternatives live =>
      operatorType :: (arguments ++ resultAtoms alternatives ++ live)
  | .argumentHeads original remaining types _ alternatives live =>
      original :: (remaining ++ types ++ resultAtoms alternatives ++ live)
  | .tupleHeads tail _ alternatives live => tail :: (resultAtoms alternatives ++ live)
  | .calls expected _ alternatives live
  | .atoms expected _ alternatives live => expected :: (resultAtoms alternatives ++ live)
  | .returned original value expected bindings _ live =>
      [original, value, expected] ++ bindingAtoms bindings ++ live
  | .returns original expected _ alternatives live =>
      [original, expected] ++ resultAtoms alternatives ++ live
  | .equations original expected incoming _ alternatives live
  | .grounded original expected incoming _ alternatives live =>
      [original, expected] ++ bindingAtoms incoming ++ resultAtoms alternatives ++ live

  | .invocation mode value bindings _ live caller =>
      [value, mode.expected] ++ bindingAtoms bindings ++ live ++ caller.toList
  | .produced value bindings _ live caller _
  | .minimal value bindings _ live caller
  | .primitive value bindings _ live caller
  | .functionBody value bindings _ live caller =>
      value :: (bindingAtoms bindings ++ live ++ caller.toList)
  | .productions _ alternatives live caller _
  | .minimals _ alternatives live caller
  | .bodyResults _ alternatives live caller => resultAtoms alternatives ++ live ++ caller.toList
  | .chainRows name template _ alternatives => [.var name, template] ++ resultAtoms alternatives
  | .producerResults mode original incoming _ live emptyReply alternatives =>
      [mode.expected, original, emptyReply] ++ bindingAtoms incoming ++ resultAtoms alternatives ++ live
  | .completed value expected bindings _ => [value, expected] ++ bindingAtoms bindings

/-- Every atom and binding field retained by a continuation. -/
def frameAtoms : Frame → List Atom
  | .filter | .tupleSingleton => []
  | .heads operatorType arguments _ live => operatorType :: (arguments ++ live)
  | .argumentHeads original remaining types _ live => original :: (remaining ++ types ++ live)
  | .tupleHeads tail _ live => tail :: live
  | .calls expected _ live => expected :: live
  | .functionTail head
  | .argumentTail head
  | .tupleTail head => [head]
  | .append remaining => taskAtoms remaining
  | .prepend selected => resultAtoms selected
  | .fallback value expected bindings _ types =>
      [value, expected] ++ types ++ bindingAtoms bindings

  | .invocationReturn mode original _ live => [mode.expected, original] ++ live
  | .producerResults mode original incoming _ live emptyReply =>
      [mode.expected, original, emptyReply] ++ bindingAtoms incoming ++ live
  | .minimalResults _ live caller | .bodyResults _ live caller => live ++ caller.toList
  | .chainResults name template _ => [.var name, template]
  | .functionTerminal caller => caller.toList

def controlAtoms : Control → List Atom
  | .work task => taskAtoms task
  | .returning results => resultAtoms results

/-- The current control, entire continuation stack, and ordered answer prefix. -/
def liveAtoms (configuration : Configuration) : List Atom :=
  controlAtoms configuration.control ++
    configuration.stack.flatMap frameAtoms ++ resultAtoms configuration.emitted

def configurationNames (configuration : Configuration) : List String :=
  atomListVariables (liveAtoms configuration)

@[simp] theorem taskAtoms_replenish (extra : Nat) (task : Task) :
    taskAtoms (task.replenish extra) = taskAtoms task := by
  cases task <;> rfl

@[simp] theorem frameAtoms_deepen (extra : Nat) (frame : Frame) :
    frameAtoms (frame.deepen extra) = frameAtoms frame := by
  cases frame <;> simp [Frame.deepen, frameAtoms]

@[simp] theorem controlAtoms_deepen (extra : Nat) (control : Control) :
    controlAtoms (control.deepen extra) = controlAtoms control := by
  cases control <;> simp [Control.deepen, controlAtoms]

@[simp] theorem liveAtoms_deepen (extra : Nat) (configuration : Configuration) :
    liveAtoms (configuration.deepen extra) = liveAtoms configuration := by
  simp [liveAtoms, Configuration.deepen, List.flatMap_map]

@[simp] theorem configurationNames_deepen (extra : Nat) (configuration : Configuration) :
    configurationNames (configuration.deepen extra) = configurationNames configuration := by
  simp only [configurationNames, liveAtoms_deepen]

end Mettapedia.Languages.MeTTa.HE.RecursiveScope
