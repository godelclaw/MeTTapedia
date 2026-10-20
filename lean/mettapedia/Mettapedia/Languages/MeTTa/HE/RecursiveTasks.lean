import Mettapedia.Languages.MeTTa.HE.Eval
import Mettapedia.Languages.MeTTa.HE.Spec.Eval

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

namespace Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (Policy Result)
open Mettapedia.Machines.OrderedProtocol.Completion

/-! ## Retained control for contextual source phases

The work items below retain values and certified logical activations. They
do not contain recursive evaluation proofs. Their source readings are used
only in correspondence proofs; machine transitions inspect work and consume
primitive casting, matching and complete-query evidence separately.
-/

inductive Task where
  | atom (live : List Atom) (scope : List String) (value : Entry.Value)
      (expected : Atom) (activation : Spec.Eval.Completed.Frame)
  | tuple (live : List Atom) (scope : List String) (values : List Entry.Value)
      (activation : Spec.Eval.Completed.Frame)
  | branches (live : List Atom) (scope : List String) (tail : List Entry.Value)
      (heads : List Result)
  | arguments (live : List Atom) (scope : List String) (requests : List Completed.ArgumentRequest)
      (activation : Completed.Frame)
  | argumentBranches (live : List Atom) (scope : List String) (original : Entry.Value)
      (requests : List Completed.ArgumentRequest) (heads : List Result)
  | function (live : List Atom) (scope : List String) (expected : Atom) (signature : SelectedTypePolicy)
      (operator : Entry.Value) (arguments : List Entry.Value) (activation : Completed.Frame)
  | functionBranches (live : List Atom) (scope : List String) (requests : List Completed.ArgumentRequest)
      (heads : List Result)
  | invocations (live : List Atom) (scope : List String) (expected : Atom) (signature : SelectedTypePolicy)
      (operator : Entry.Value) (arguments : List Entry.Value) (activations : List Completed.Frame)
  | minimal (live : List Atom) (scope : List String) (caller : Option Atom) (value : Entry.Value) (activation : Completed.Frame)
  | body (live : List Atom) (scope : List String) (caller : Option Atom) (value : Entry.Value) (activation : Completed.Frame)
  | invocation (live : List Atom) (scope : List String) (caller : Option Atom) (value : Entry.Value) (activation : Completed.Frame)
  | invocationEquations (live : List Atom) (scope : List String) (original : Entry.Value)
      (activation : Completed.Frame) (works : List Spec.Eval.Steps.EquationWork)
  | boundary (live : List Atom) (scope : List String) (caller : Option Atom) (site : Completed.Boundary)
      (value : Entry.Value) (activation : Completed.Frame)
  | boundaryBatch (live : List Atom) (scope : List String) (caller : Option Atom) (site : Completed.Boundary) (rows : List Result)
  | calls (live : List Atom) (scope : List String) (expected : Atom) (rows : List Result)
  | call (live : List Atom) (scope : List String) (value : Entry.Value)
      (expected : Atom) (activation : Spec.Eval.Completed.Frame)
  | equations (live : List Atom) (scope : List String) (original : Entry.Value)
      (expected : Atom) (activation : Spec.Eval.Completed.Frame)
      (works : List Spec.Eval.Steps.EquationWork)
  | returned (live : List Atom) (scope : List String) (original : Entry.Value)
      (expected : Atom) (value : Entry.Value) (activation : Spec.Eval.Completed.Frame)

  | capture (rows : List Result) (saved : List Entry.Value) (caller : Completed.Frame)
  | restore (pairs : List Entry.Value) (saved : List Result) (caller : Completed.Frame)

/-- Independent source meaning for each pending work mode. No transition
consults this predicate. -/
def Task.SourceRel (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Spec.Eval.Completed.CastLookup) (policy : Policy) : Task → List Result → Prop
  | .atom live scope value expected activation, results =>
      Spec.Eval.Completed.AtomRel space dispatch lookup live scope value expected activation results
        (policy := policy)
  | .tuple live scope values activation, results =>
      Spec.Eval.Completed.TupleRel space dispatch lookup live scope values activation results (policy := policy)
  | .branches live scope tail heads, results =>
      Spec.Eval.Completed.TupleBranchesRel space dispatch lookup live scope tail heads results (policy := policy)
  | .arguments live scope requests activation, results =>
      Completed.ArgumentsRel space dispatch lookup live scope requests activation results (policy := policy)
  | .argumentBranches live scope original requests heads, results =>
      Completed.ArgumentBranchesRel space dispatch lookup live scope original requests heads results (policy := policy)
  | .function live scope expected signature operator operands activation, results =>
      Completed.FunctionRel space dispatch lookup live scope expected signature operator operands activation results (policy := policy)
  | .functionBranches live scope requests heads, results =>
      Completed.FunctionBranchesRel space dispatch lookup live scope requests heads results (policy := policy)
  | .invocations live scope expected signature operator operands activations, results =>
      Completed.InvocationsRel space dispatch lookup live scope expected signature operator operands activations results (policy := policy)
  | .minimal live scope caller value activation, results =>
      Completed.MinimalRel space dispatch lookup live scope caller value activation results (policy := policy)
  | .body live scope caller value activation, results =>
      Completed.BodyRel space dispatch lookup live scope caller value activation results (policy := policy)
  | .invocation live scope caller value activation, results =>
      Completed.InvocationRel space dispatch lookup live scope caller value activation results (policy := policy)
  | .invocationEquations live scope original activation works, results =>
      Completed.InvocationEquationsRel space dispatch lookup live scope original activation works results (policy := policy)
  | .boundary live scope caller site value activation, results =>
      Completed.BoundaryRel space dispatch lookup live scope caller site value activation results (policy := policy)
  | .boundaryBatch live scope caller site rows, results =>
      Completed.BoundaryBatchRel space dispatch lookup live scope caller site rows results (policy := policy)
  | .calls live scope expected rows, results =>
      Spec.Eval.Completed.CallsRel space dispatch lookup live scope expected rows results (policy := policy)
  | .call live scope value expected activation, results =>
      Spec.Eval.Completed.CallRel space dispatch lookup live scope value expected activation results (policy := policy)
  | .equations live scope original expected activation works, results =>
      Spec.Eval.Completed.EquationBodiesRel space dispatch lookup live scope original expected activation works results
        (policy := policy)
  | .returned live scope original expected value activation, results =>
      Spec.Eval.Completed.ReturnRel space dispatch lookup live scope original expected value activation results
        (policy := policy)

  | .capture _ _ _, _ | .restore _ _ _, _ => False

/-- First-order continuations retain pending source occurrences and values.
Publication is a separate boundary after all caller work has returned. -/
inductive Continuation where
  | publish (original : Atom)
  | singleton
  | branches (live : List Atom) (scope : List String) (tail : List Entry.Value)
  | tupleTail (head : Entry.Value)
  | arguments (live : List Atom) (scope : List String) (original : Entry.Value)
      (requests : List Completed.ArgumentRequest)
  | argumentTail (head : Entry.Value)
  | functionHeads (live : List Atom) (scope : List String) (requests : List Completed.ArgumentRequest)
  | functionAssemble (head : Entry.Value)
  | diagnostics (errors : List Atom) (activation : Completed.Frame)
  | boundaryBatch (live : List Atom) (scope : List String) (caller : Option Atom) (site : Completed.Boundary)
  | calls (live : List Atom) (scope : List String) (expected : Atom)
  | append (remaining : Task)
  | prepend (selected : List Result)

  | collect (caller : Completed.Frame)

/-- Context labels are separate from their current space contents. The
read-only instance uses snapshots; a live world uses stable identities. -/
inductive Control (Context : Type := Space) where
  | work (task : Task)
  | returning (results : List Result)
  | context (label : Context) (child : Control Context) (stack : List Continuation)

/-- Resolve only saved context labels. Values, bindings, continuation frames
and answer occurrences are retained without reconstruction. -/
def Control.mapContexts {Context Other : Type} (view : Context → Other) : Control Context → Control Other
  | .work task => .work task
  | .returning results => .returning results
  | .context label child stack => .context (view label) (child.mapContexts view) stack

theorem Control.mapContexts_id {Context : Type} (control : Control Context) :
    control.mapContexts id = control := by
  induction control with
  | work => rfl
  | returning => rfl
  | context label child stack ih => simp only [mapContexts, id_eq, ih]

theorem Control.mapContexts_comp {Context Middle Other : Type}
    (first : Context → Middle) (second : Middle → Other) (control : Control Context) :
    (control.mapContexts first).mapContexts second = control.mapContexts (second ∘ first) := by
  induction control with
  | work => rfl
  | returning => rfl
  | context label child stack ih => simp only [mapContexts, Function.comp_apply, ih]

structure Configuration where
  space : Space
  control : Control
  stack : List Continuation
  emitted : List Result

def Configuration.initial (space : Space) (task : Task) : Configuration :=
  ⟨space,.work task,[],[]⟩

/-- The source reading of a continuation. Recursive premises describe its
pending work, rather than an atomic operation available to the machine. -/
inductive Continuation.Applies (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Spec.Eval.Completed.CastLookup) (policy : Policy) :
    Continuation → List Result → List Result → Prop where
  | publish {original raw selected} :
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (Spec.Eval.Completed.readResult policy)) selected →
      Applies space dispatch lookup policy (.publish original) raw
        (selected.map (Spec.Eval.Completed.publishResult policy original))
  | singleton (results) :
      Applies space dispatch lookup policy .singleton results
        (results.map Spec.Eval.Completed.tupleSingleton)
  | branches {live scope tail heads results} :
      Spec.Eval.Completed.TupleBranchesRel space dispatch lookup live scope tail heads results (policy := policy) →
      Applies space dispatch lookup policy (.branches live scope tail) heads results
  | tupleTail (head) (results) :
      Applies space dispatch lookup policy (.tupleTail head) results
        (results.map (Spec.Eval.Completed.tuplePrepend head))
  | arguments {live scope original requests heads results} :
      Completed.ArgumentBranchesRel space dispatch lookup live scope original requests heads results (policy := policy) →
      Applies space dispatch lookup policy (.arguments live scope original requests) heads results
  | argumentTail (head) (results) :
      Applies space dispatch lookup policy (.argumentTail head) results
        (results.map (Completed.argumentPrepend head))
  | functionHeads {live scope requests heads results} :
      Completed.FunctionBranchesRel space dispatch lookup live scope requests heads results (policy := policy) →
      Applies space dispatch lookup policy (.functionHeads live scope requests) heads results
  | functionAssemble (head) (results) :
      Applies space dispatch lookup policy (.functionAssemble head) results
        (results.map (Completed.functionAssemble head))
  | diagnostics (errors) (activation) (results) :
      Applies space dispatch lookup policy (.diagnostics errors activation) results
        (results ++ Completed.diagnosticResults errors activation)
  | boundaryBatch {live scope caller site rows results} :
      Completed.BoundaryBatchRel space dispatch lookup live scope caller site rows results (policy := policy) →
      Applies space dispatch lookup policy (.boundaryBatch live scope caller site) rows results
  | calls {live scope expected rows results} :
      Spec.Eval.Completed.CallsRel space dispatch lookup live scope expected rows results (policy := policy) →
      Applies space dispatch lookup policy (.calls live scope expected) rows results
  | append {remaining before after} :
      remaining.SourceRel space dispatch lookup policy after →
      Applies space dispatch lookup policy (.append remaining) before (before ++ after)
  | prepend (selected results) :
      Applies space dispatch lookup policy (.prepend selected) results (selected ++ results)

inductive StackRel (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Spec.Eval.Completed.CastLookup) (policy : Policy) :
    List Continuation → List Result → List Result → Prop where
  | nil (results) : StackRel space dispatch lookup policy [] results results
  | cons {frame stack before middle after} :
      frame.Applies space dispatch lookup policy before middle →
      StackRel space dispatch lookup policy stack middle after →
      StackRel space dispatch lookup policy (frame :: stack) before after

inductive Control.SourceRel : Space → Spec.Eval.GroundedDispatch →
    Spec.Eval.Completed.CastLookup → Policy → Control → List Result → Prop where
  | work {space dispatch lookup policy task results} : task.SourceRel space dispatch lookup policy results →
      SourceRel space dispatch lookup policy (.work task) results
  | returning {space dispatch lookup policy} (results) :
      SourceRel space dispatch lookup policy (.returning results) results
  | context {space childSpace dispatch lookup policy child stack current results} :
      SourceRel childSpace dispatch lookup policy child current →
      StackRel childSpace dispatch lookup policy stack current results →
      SourceRel space dispatch lookup policy (.context childSpace child stack) results

/-- Complete source meaning of the current work, its actual continuation and
the already published prefix. It does not assert that the machine terminates. -/
def Configuration.SourceRel (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Spec.Eval.Completed.CastLookup) (policy : Policy)
    (state : Configuration) (answers : List Result) : Prop :=
  ∃ current pending,
    state.control.SourceRel state.space dispatch lookup policy current ∧
    StackRel state.space dispatch lookup policy state.stack current pending ∧
    answers = state.emitted ++ pending

end Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual


namespace Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual

open Spec.Eval.Completed (Result)

/-- The context labels currently retained as operational scopes. Opaque
handles inside source syntax remain syntax until their own entry boundary. -/
def Control.contexts {Context : Type} : Control Context → List Context
  | .work _ | .returning _ => []
  | .context label child _ => label :: child.contexts

theorem Control.mapContexts_congr {Context Other : Type} (first second : Context → Other)
    (control : Control Context) (same : ∀ label ∈ control.contexts, first label = second label) :
    control.mapContexts first = control.mapContexts second := by
  induction control with
  | work => rfl
  | returning => rfl
  | context label child stack ih =>
      have here := same label List.mem_cons_self
      have below := ih (fun name present => same name (List.mem_cons_of_mem _ present))
      simp only [mapContexts, here, below]

/-- A shared world and stable context labels surround the existing control.
Bindings and continuation frames do not capture a private copy of the world.
The read-only snapshot configuration remains its existing explicit instance. -/
structure WorldConfiguration (Context World : Type) where
  world : World
  context : Context
  control : Control Context
  stack : List Continuation
  emitted : List Result

namespace WorldConfiguration

/-- Read all operational scope views from the reached world. This projection
is a phase observation; it does not identify contexts with equal contents. -/
def snapshot {Context World : Type} (view : World → Context → Space)
    (state : WorldConfiguration Context World) : Configuration :=
  ⟨view state.world state.context, state.control.mapContexts (view state.world), state.stack, state.emitted⟩

/-- A local world operation preserves the entire saved evaluator state. Its
next phase obtains fresh views through `snapshot`, rather than cached spaces. -/
def withWorld {Context World : Type} (state : WorldConfiguration Context World) (world : World) :
    WorldConfiguration Context World := {state with world}

/-- Only agreement on actually retained operational context labels is needed
for equal current snapshots. This is not equivalence of future mutable worlds. -/
theorem snapshot_congr {Context World : Type} (view : World → Context → Space)
    (state : WorldConfiguration Context World) (other : World)
    (root : view state.world state.context = view other state.context)
    (saved : ∀ label ∈ state.control.contexts, view state.world label = view other label) :
    state.snapshot view = (state.withWorld other).snapshot view := by
  simp only [snapshot, withWorld, root, Control.mapContexts_congr _ _ _ saved]

theorem withWorld_retains_control {Context World : Type} (state : WorldConfiguration Context World) (world : World) :
    (state.withWorld world).context = state.context ∧
    (state.withWorld world).control = state.control ∧
    (state.withWorld world).stack = state.stack ∧
    (state.withWorld world).emitted = state.emitted := ⟨rfl, rfl, rfl, rfl⟩

/-- The existing read-only evaluator embeds as a world with no mutation.
Its context labels are the declared space snapshots. -/
def ofReadOnly (state : Configuration) : WorldConfiguration Space Unit :=
  ⟨(), state.space, state.control, state.stack, state.emitted⟩

theorem snapshot_ofReadOnly (state : Configuration) :
    (ofReadOnly state).snapshot (fun _ context => context) = state := by
  cases state with
  | mk space control stack emitted =>
      change Configuration.mk space (control.mapContexts id) stack emitted =
        Configuration.mk space control stack emitted
      rw [Control.mapContexts_id]

end WorldConfiguration
end Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual


namespace Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Eval.Completed (Frame Result WorldServices)

/-- Ordinary control nodes have no operational context label to decode.
This relation transports them without identifying different context handles. -/
inductive UnscopedControl {Context : Type} : Control Context → Control → Prop where
  | work (task : Task) : UnscopedControl (.work task) (.work task)
  | returning (results : List Result) : UnscopedControl (.returning results) (.returning results)

theorem UnscopedControl.same {before after : Control} (same : UnscopedControl before after) :
    before = after := by cases same <;> rfl

/-- Context-space is served by the live context boundary. Delegating it to
an old snapshot service would encode contents where identity is required. -/
def managedContextControl {Context : Type} : Control Context → Bool
  | .work (.minimal _ _ _ (.expression _ [.symbol "context-space"]) _) => true
  | _ => false

end Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual


namespace Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (Policy Result WorldEnvironment)
open Mettapedia.Machines.OrderedProtocol.Completion

/-- Pending work reads the independent stateful source judgment. Neither
primitive transitions nor host contracts consult this completed evidence. -/
def Task.WorldSourceRel {Context World : Type}
    (environment : WorldEnvironment Context World) (policy : Policy) (label : Context) (world : World) :
    Task → List Result → World → Prop
  | .atom live scope value expected activation, results, afterWorld =>
      Completed.Stateful.AtomRel environment label world live scope value expected activation results
        afterWorld (policy := policy)
  | .tuple live scope values activation, results, afterWorld =>
      Completed.Stateful.TupleRel environment label world live scope values activation results afterWorld (policy := policy)
  | .branches live scope tail heads, results, afterWorld =>
      Completed.Stateful.TupleBranchesRel environment label world live scope tail heads results afterWorld (policy := policy)
  | .arguments live scope requests activation, results, afterWorld =>
      Completed.Stateful.ArgumentsRel environment label world live scope requests activation results afterWorld (policy := policy)
  | .argumentBranches live scope original requests heads, results, afterWorld =>
      Completed.Stateful.ArgumentBranchesRel environment label world live scope original requests heads results afterWorld (policy := policy)
  | .function live scope expected signature operator operands activation, results, afterWorld =>
      Completed.Stateful.FunctionRel environment label world live scope expected signature operator operands activation results afterWorld (policy := policy)
  | .functionBranches live scope requests heads, results, afterWorld =>
      Completed.Stateful.FunctionBranchesRel environment label world live scope requests heads results afterWorld (policy := policy)
  | .invocations live scope expected signature operator operands activations, results, afterWorld =>
      Completed.Stateful.InvocationsRel environment label world live scope expected signature operator operands activations results afterWorld (policy := policy)
  | .minimal live scope caller value activation, results, afterWorld =>
      Completed.Stateful.MinimalRel environment label world live scope caller value activation results afterWorld (policy := policy)
  | .body live scope caller value activation, results, afterWorld =>
      Completed.Stateful.BodyRel environment label world live scope caller value activation results afterWorld (policy := policy)
  | .invocation live scope caller value activation, results, afterWorld =>
      Completed.Stateful.InvocationRel environment label world live scope caller value activation results afterWorld (policy := policy)
  | .invocationEquations live scope original activation works, results, afterWorld =>
      Completed.Stateful.InvocationEquationsRel environment label world live scope original activation works results afterWorld (policy := policy)
  | .boundary live scope caller site value activation, results, afterWorld =>
      Completed.Stateful.BoundaryRel environment label world live scope caller site value activation results afterWorld (policy := policy)
  | .boundaryBatch live scope caller site rows, results, afterWorld =>
      Completed.Stateful.BoundaryBatchRel environment label world live scope caller site rows results afterWorld (policy := policy)
  | .calls live scope expected rows, results, afterWorld =>
      Completed.Stateful.CallsRel environment label world live scope expected rows results afterWorld (policy := policy)
  | .call live scope value expected activation, results, afterWorld =>
      Completed.Stateful.CallRel environment label world live scope value expected activation results afterWorld (policy := policy)
  | .equations live scope original expected activation works, results, afterWorld =>
      Completed.Stateful.EquationBodiesRel environment label world live scope original expected activation works results
        afterWorld (policy := policy)
  | .returned live scope original expected value activation, results, afterWorld =>
      Completed.Stateful.ReturnRel environment label world live scope original expected value activation results
        afterWorld (policy := policy)


  | .capture rows saved caller, results, afterWorld =>
      ∃ snapshots packed, environment.services.snapshots = some snapshots ∧
        Completed.CaptureRowsRel snapshots label world rows saved packed afterWorld ∧ results = [(packed,caller)]
  | .restore pairs saved caller, results, afterWorld =>
      ∃ snapshots, environment.services.snapshots = some snapshots ∧ afterWorld = world ∧
        Completed.RestoreRowsRel snapshots label world policy caller pairs saved results

/-- A saved continuation resumes in its child's reached world. -/
inductive Continuation.WorldApplies {Context World : Type}
    (environment : WorldEnvironment Context World) (policy : Policy) :
    Context → World → Continuation → List Result → List Result → World → Prop where
  | publish {label world original raw selected} :
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (Completed.readResult policy)) selected →
      WorldApplies environment policy label world (.publish original) raw
        (selected.map (Completed.publishResult policy original)) world
  | singleton {label world} (results) :
      WorldApplies environment policy label world .singleton results
        (results.map Completed.tupleSingleton) world
  | branches {label world afterWorld live scope tail heads results} :
      Completed.Stateful.TupleBranchesRel environment label world live scope tail heads results afterWorld (policy := policy) →
      WorldApplies environment policy label world (.branches live scope tail) heads results afterWorld
  | tupleTail {label world} (head) (results) :
      WorldApplies environment policy label world (.tupleTail head) results
        (results.map (Completed.tuplePrepend head)) world
  | arguments {label world afterWorld live scope original requests heads results} :
      Completed.Stateful.ArgumentBranchesRel environment label world live scope original requests heads results afterWorld (policy := policy) →
      WorldApplies environment policy label world (.arguments live scope original requests) heads results afterWorld
  | argumentTail {label world} (head) (results) :
      WorldApplies environment policy label world (.argumentTail head) results
        (results.map (Completed.argumentPrepend head)) world
  | functionHeads {label world afterWorld live scope requests heads results} :
      Completed.Stateful.FunctionBranchesRel environment label world live scope requests heads results afterWorld (policy := policy) →
      WorldApplies environment policy label world (.functionHeads live scope requests) heads results afterWorld
  | functionAssemble {label world} (head) (results) :
      WorldApplies environment policy label world (.functionAssemble head) results
        (results.map (Completed.functionAssemble head)) world
  | diagnostics {label world} (errors) (activation) (results) :
      WorldApplies environment policy label world (.diagnostics errors activation) results
        (results ++ Completed.diagnosticResults errors activation) world
  | boundaryBatch {label world afterWorld live scope caller site rows results} :
      Completed.Stateful.BoundaryBatchRel environment label world live scope caller site rows results afterWorld (policy := policy) →
      WorldApplies environment policy label world (.boundaryBatch live scope caller site) rows results afterWorld
  | calls {label world afterWorld live scope expected rows results} :
      Completed.Stateful.CallsRel environment label world live scope expected rows results afterWorld (policy := policy) →
      WorldApplies environment policy label world (.calls live scope expected) rows results afterWorld
  | append {label world afterWorld remaining before after} :
      remaining.WorldSourceRel environment policy label world after afterWorld →
      WorldApplies environment policy label world (.append remaining) before (before ++ after) afterWorld
  | prepend {label world} (selected results) :
      WorldApplies environment policy label world (.prepend selected) results (selected ++ results) world
  | collect {label world afterWorld caller rows packed snapshots} :
      environment.services.snapshots = some snapshots →
      Completed.CaptureRowsRel snapshots label world rows [] packed afterWorld →
      WorldApplies environment policy label world (.collect caller) rows [(packed,caller)] afterWorld

inductive WorldStackRel {Context World : Type}
    (environment : WorldEnvironment Context World) (policy : Policy) (label : Context) :
    World → List Continuation → List Result → List Result → World → Prop where
  | nil {world} (results) : WorldStackRel environment policy label world [] results results world
  | cons {world middleWorld afterWorld frame stack before middle after} :
      frame.WorldApplies environment policy label world before middle middleWorld →
      WorldStackRel environment policy label middleWorld stack middle after afterWorld →
      WorldStackRel environment policy label world (frame :: stack) before after afterWorld

inductive Control.WorldSourceRel {Context World : Type}
    (environment : WorldEnvironment Context World) (policy : Policy) :
    Context → World → Control Context → List Result → World → Prop where
  | work {label world afterWorld task results} :
      task.WorldSourceRel environment policy label world results afterWorld →
      WorldSourceRel environment policy label world (.work task) results afterWorld
  | returning {label world} (results) :
      WorldSourceRel environment policy label world (.returning results) results world
  | context {label childLabel world childWorld afterWorld child stack current results} :
      WorldSourceRel environment policy childLabel world child current childWorld →
      WorldStackRel environment policy childLabel childWorld stack current results afterWorld →
      WorldSourceRel environment policy label world (.context childLabel child stack) results afterWorld

/-- The retained source meaning includes the final reached world and the
already emitted ordered prefix. It does not postulate termination. -/
def WorldConfiguration.SourceRel {Context World : Type}
    (environment : WorldEnvironment Context World) (policy : Policy)
    (state : WorldConfiguration Context World) (answers : List Result) (afterWorld : World) : Prop :=
  ∃ current pending childWorld,
    state.control.WorldSourceRel environment policy state.context state.world current childWorld ∧
    WorldStackRel environment policy state.context childWorld state.stack current pending afterWorld ∧
    answers = state.emitted ++ pending

/-! ## Simultaneous Variable Renaming on Retained Contextual Control and Configurations -/

open Mettapedia.Languages.MeTTa.HE
open Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.ScopeObservation

private theorem perm_symm_mul_self (p : Equiv.Perm String) :
    p.symm * p = Equiv.refl String := by
  ext x
  simp

def Task.rename (p : Equiv.Perm String) : Task → Task
  | .atom live scope value expected activation =>
      .atom (live.map (renameTypeVars p)) (scope.map p) (value.rename p)
        (renameTypeVars p expected) (activation.rename p)
  | .tuple live scope values activation =>
      .tuple (live.map (renameTypeVars p)) (scope.map p)
        (values.map (Entry.Value.rename p)) (activation.rename p)
  | .branches live scope tail heads =>
      .branches (live.map (renameTypeVars p)) (scope.map p)
        (tail.map (Entry.Value.rename p)) (heads.map (Completed.Result.rename p))
  | .arguments live scope requests activation =>
      .arguments (live.map (renameTypeVars p)) (scope.map p)
        (requests.map (Completed.ArgumentRequest.rename p)) (activation.rename p)
  | .argumentBranches live scope original requests heads =>
      .argumentBranches (live.map (renameTypeVars p)) (scope.map p)
        (original.rename p) (requests.map (Completed.ArgumentRequest.rename p))
        (heads.map (Completed.Result.rename p))
  | .function live scope expected signature operator operands activation =>
      .function (live.map (renameTypeVars p)) (scope.map p)
        (renameTypeVars p expected) (Spec.Eval.Renaming.policy p signature)
        (operator.rename p) (operands.map (Entry.Value.rename p)) (activation.rename p)
  | .functionBranches live scope requests heads =>
      .functionBranches (live.map (renameTypeVars p)) (scope.map p)
        (requests.map (Completed.ArgumentRequest.rename p))
        (heads.map (Completed.Result.rename p))
  | .invocations live scope expected signature operator operands activations =>
      .invocations (live.map (renameTypeVars p)) (scope.map p)
        (renameTypeVars p expected) (Spec.Eval.Renaming.policy p signature)
        (operator.rename p) (operands.map (Entry.Value.rename p))
        (activations.map (Completed.Frame.rename p))
  | .minimal live scope caller value activation =>
      .minimal (live.map (renameTypeVars p)) (scope.map p)
        (caller.map (renameTypeVars p)) (value.rename p) (activation.rename p)
  | .body live scope caller value activation =>
      .body (live.map (renameTypeVars p)) (scope.map p)
        (caller.map (renameTypeVars p)) (value.rename p) (activation.rename p)
  | .invocation live scope caller value activation =>
      .invocation (live.map (renameTypeVars p)) (scope.map p)
        (caller.map (renameTypeVars p)) (value.rename p) (activation.rename p)
  | .invocationEquations live scope original activation works =>
      .invocationEquations (live.map (renameTypeVars p)) (scope.map p)
        (original.rename p) (activation.rename p)
        (works.map (Spec.Eval.Steps.EquationWork.rename p))
  | .boundary live scope caller site value activation =>
      .boundary (live.map (renameTypeVars p)) (scope.map p)
        (caller.map (renameTypeVars p)) (site.rename p)
        (value.rename p) (activation.rename p)
  | .boundaryBatch live scope caller site rows =>
      .boundaryBatch (live.map (renameTypeVars p)) (scope.map p)
        (caller.map (renameTypeVars p)) (site.rename p)
        (rows.map (Completed.Result.rename p))
  | .calls live scope expected rows =>
      .calls (live.map (renameTypeVars p)) (scope.map p)
        (renameTypeVars p expected) (rows.map (Completed.Result.rename p))
  | .call live scope value expected activation =>
      .call (live.map (renameTypeVars p)) (scope.map p)
        (value.rename p) (renameTypeVars p expected) (activation.rename p)
  | .equations live scope original expected activation works =>
      .equations (live.map (renameTypeVars p)) (scope.map p)
        (original.rename p) (renameTypeVars p expected) (activation.rename p)
        (works.map (Spec.Eval.Steps.EquationWork.rename p))
  | .returned live scope original expected value activation =>
      .returned (live.map (renameTypeVars p)) (scope.map p)
        (original.rename p) (renameTypeVars p expected)
        (value.rename p) (activation.rename p)
  | .capture rows saved caller =>
      .capture (rows.map (Completed.Result.rename p))
        (saved.map (Entry.Value.rename p)) (caller.rename p)
  | .restore pairs saved caller =>
      .restore (pairs.map (Entry.Value.rename p))
        (saved.map (Completed.Result.rename p)) (caller.rename p)

@[simp] theorem Task.rename_id (task : Task) :
    task.rename (Equiv.refl String) = task := by
  cases task <;>
    simp [Task.rename, show (Equiv.refl String : String → String) = id from rfl]

@[simp] theorem Task.rename_id_fun :
    Task.rename (Equiv.refl String) = id := by
  funext task
  exact Task.rename_id task

theorem Task.rename_comp (p q : Equiv.Perm String) (task : Task) :
    (task.rename p).rename q = task.rename (q * p) := by
  cases task <;>
    simp [Task.rename, List.map_map, Option.map_map, Function.comp_def,
      renameTypeVars_comp, Entry.Value.rename_comp, Completed.Frame.rename_comp,
      Completed.Result.rename_comp, Completed.ArgumentRequest.rename_comp,
      Completed.Boundary.rename_comp, Spec.Eval.Steps.EquationWork.rename_comp,
      Equiv.Perm.coe_mul]

@[simp] theorem Task.rename_cancel (p : Equiv.Perm String) (task : Task) :
    (task.rename p).rename p.symm = task := by
  rw [Task.rename_comp, perm_symm_mul_self, Task.rename_id]

@[simp] theorem Task.rename_cancel_reverse (p : Equiv.Perm String) (task : Task) :
    (task.rename p.symm).rename p = task :=
  Task.rename_cancel p.symm task

def Continuation.rename (p : Equiv.Perm String) : Continuation → Continuation
  | .publish original => .publish (renameTypeVars p original)
  | .singleton => .singleton
  | .branches live scope tail =>
      .branches (live.map (renameTypeVars p)) (scope.map p)
        (tail.map (Entry.Value.rename p))
  | .tupleTail head => .tupleTail (head.rename p)
  | .arguments live scope original requests =>
      .arguments (live.map (renameTypeVars p)) (scope.map p)
        (original.rename p) (requests.map (Completed.ArgumentRequest.rename p))
  | .argumentTail head => .argumentTail (head.rename p)
  | .functionHeads live scope requests =>
      .functionHeads (live.map (renameTypeVars p)) (scope.map p)
        (requests.map (Completed.ArgumentRequest.rename p))
  | .functionAssemble head => .functionAssemble (head.rename p)
  | .diagnostics errors activation =>
      .diagnostics (errors.map (renameTypeVars p)) (activation.rename p)
  | .boundaryBatch live scope caller site =>
      .boundaryBatch (live.map (renameTypeVars p)) (scope.map p)
        (caller.map (renameTypeVars p)) (site.rename p)
  | .calls live scope expected =>
      .calls (live.map (renameTypeVars p)) (scope.map p) (renameTypeVars p expected)
  | .append remaining => .append (remaining.rename p)
  | .prepend selected => .prepend (selected.map (Completed.Result.rename p))
  | .collect caller => .collect (caller.rename p)

@[simp] theorem Continuation.rename_id (frame : Continuation) :
    frame.rename (Equiv.refl String) = frame := by
  cases frame <;>
    simp [Continuation.rename, show (Equiv.refl String : String → String) = id from rfl]

@[simp] theorem Continuation.rename_id_fun :
    Continuation.rename (Equiv.refl String) = id := by
  funext frame
  exact Continuation.rename_id frame

theorem Continuation.rename_comp (p q : Equiv.Perm String) (frame : Continuation) :
    (frame.rename p).rename q = frame.rename (q * p) := by
  cases frame <;>
    simp [Continuation.rename, List.map_map, Option.map_map, Function.comp_def,
      renameTypeVars_comp, Entry.Value.rename_comp, Completed.Frame.rename_comp,
      Completed.Result.rename_comp, Completed.ArgumentRequest.rename_comp,
      Completed.Boundary.rename_comp, Task.rename_comp, Equiv.Perm.coe_mul]

@[simp] theorem Continuation.rename_cancel (p : Equiv.Perm String) (frame : Continuation) :
    (frame.rename p).rename p.symm = frame := by
  rw [Continuation.rename_comp, perm_symm_mul_self, Continuation.rename_id]

@[simp] theorem Continuation.rename_cancel_reverse (p : Equiv.Perm String) (frame : Continuation) :
    (frame.rename p.symm).rename p = frame :=
  Continuation.rename_cancel p.symm frame

def Control.rename (p : Equiv.Perm String) : Control → Control
  | .work task => .work (task.rename p)
  | .returning results => .returning (results.map (Completed.Result.rename p))
  | .context label child stack =>
      .context (Spec.Eval.Renaming.space p label) (child.rename p)
        (stack.map (Continuation.rename p))

@[simp] theorem Control.rename_id (control : Control) :
    control.rename (Equiv.refl String) = control := by
  induction control with
  | work task => simp [Control.rename]
  | returning results => simp [Control.rename]
  | context label child stack ih =>
      simp [Control.rename, ih]

theorem Control.rename_comp (p q : Equiv.Perm String) (control : Control) :
    (control.rename p).rename q = control.rename (q * p) := by
  induction control with
  | work task => simp [Control.rename, Task.rename_comp]
  | returning results =>
      simp [Control.rename, List.map_map, Function.comp_def, Completed.Result.rename_comp]
  | context label child stack ih =>
      simp [Control.rename, ih, List.map_map, Function.comp_def, Continuation.rename_comp]

@[simp] theorem Control.rename_cancel (p : Equiv.Perm String) (control : Control) :
    (control.rename p).rename p.symm = control := by
  rw [Control.rename_comp, perm_symm_mul_self, Control.rename_id]

@[simp] theorem Control.rename_cancel_reverse (p : Equiv.Perm String) (control : Control) :
    (control.rename p.symm).rename p = control :=
  Control.rename_cancel p.symm control

def Configuration.rename (p : Equiv.Perm String) (state : Configuration) : Configuration :=
  ⟨Spec.Eval.Renaming.space p state.space,
   state.control.rename p,
   state.stack.map (Continuation.rename p),
   state.emitted.map (Completed.Result.rename p)⟩

@[simp] theorem Configuration.initial_rename (p : Equiv.Perm String) (space : Space) (task : Task) :
    (Configuration.initial space task).rename p =
      Configuration.initial (Spec.Eval.Renaming.space p space) (task.rename p) := rfl

@[simp] theorem Configuration.rename_id (state : Configuration) :
    state.rename (Equiv.refl String) = state := by
  cases state
  simp [Configuration.rename]

theorem Configuration.rename_comp (p q : Equiv.Perm String) (state : Configuration) :
    (state.rename p).rename q = state.rename (q * p) := by
  cases state
  simp [Configuration.rename, Control.rename_comp, Continuation.rename_comp,
    Completed.Result.rename_comp, List.map_map, Function.comp_def]

@[simp] theorem Configuration.rename_cancel (p : Equiv.Perm String) (state : Configuration) :
    (state.rename p).rename p.symm = state := by
  rw [Configuration.rename_comp, perm_symm_mul_self, Configuration.rename_id]

@[simp] theorem Configuration.rename_cancel_reverse (p : Equiv.Perm String) (state : Configuration) :
    (state.rename p.symm).rename p = state :=
  Configuration.rename_cancel p.symm state

end Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual

