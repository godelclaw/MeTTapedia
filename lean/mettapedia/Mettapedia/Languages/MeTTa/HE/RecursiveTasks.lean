import Mettapedia.Languages.MeTTa.HE.Eval

/-!
# First-order control for the recursive HE evaluator

Requests cover all six mutually recursive evaluator functions and the finite
list traversals between their calls. Continuations retain the selected value,
bindings, remaining alternatives and argument types as data. The meanings below
refer to the existing recursive evaluator; the executable control machine is
constructed separately. Grounded dispatch, matching and type checks remain
their existing interfaces. The space is read-only in this evaluator profile.

The profile retains the evaluator's explicit fuel and its accumulation of all
applicable function types. It is not an identification with a native runtime
that selects only its first applicable type, or with effectful evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveTasks

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive Task where
  | atom (value expected : Atom) (bindings : Bindings) (fuel : Nat)
  | expression (value expected : Atom) (bindings : Bindings) (fuel : Nat)
  | func (value operatorType : Atom) (bindings : Bindings) (fuel : Nat)
  | args (values types : List Atom) (bindings : Bindings) (fuel : Nat)
  | tuple (value : Atom) (bindings : Bindings) (fuel : Nat)
  | call (value expected : Atom) (bindings : Bindings) (fuel : Nat)
  | functions (value expected : Atom) (bindings : Bindings) (fuel : Nat) (types : List Atom)
  | bindingAlternatives (value operatorType resultType : Atom) (fuel : Nat) (alternatives : List Bindings)
  | heads (operatorType : Atom) (arguments : List Atom) (fuel : Nat) (alternatives : ResultSet)
  | argumentHeads (original : Atom) (remaining types : List Atom) (fuel : Nat) (alternatives : ResultSet)
  | tupleHeads (tail : Atom) (fuel : Nat) (alternatives : ResultSet)
  | calls (expected : Atom) (fuel : Nat) (alternatives : ResultSet)
  | atoms (expected : Atom) (fuel : Nat) (alternatives : ResultSet)
  | equations (expected : Atom) (incoming : Bindings) (fuel : Nat) (alternatives : ResultSet)
  | grounded (expected : Atom) (incoming : Bindings) (fuel : Nat) (alternatives : ResultSet)
  | tupleCalls (value expected : Atom) (bindings : Bindings) (fuel : Nat)
  deriving Repr, DecidableEq

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
    (fuel : Nat) (types : List Atom) (results : ResultSet) : ResultSet :=
  if !results.isEmpty then results
  else
    let checksFailed := types.all fun operatorType =>
      if isFunctionType operatorType then
        match checkIfFunctionTypeIsApplicable value operatorType expected space bindings fuel with
        | .inl _ => true
        | .inr _ => false
      else true
    if checksFailed then
      types.flatMap fun operatorType =>
        if isFunctionType operatorType then
          match checkIfFunctionTypeIsApplicable value operatorType expected space bindings fuel with
          | .inl errors => errors.map fun error => (error, bindings)
          | .inr _ => []
        else []
    else []

/-- Ordered meanings of requests, using the existing evaluator for recursive
calls rather than the new machine's transition function. -/
def Task.denote (space : Space) (dispatch : GroundedDispatch) : Task → ResultSet
  | .atom value expected bindings fuel => evalAtom space dispatch value expected bindings fuel
  | .expression value expected bindings fuel =>
      interpretExpression space dispatch value expected bindings fuel
  | .func value operatorType bindings fuel =>
      interpretFunction space dispatch value operatorType bindings fuel
  | .args values types bindings fuel => interpretArgs space dispatch values types bindings fuel
  | .tuple value bindings fuel => interpretTuple space dispatch value bindings fuel
  | .call value expected bindings fuel => mettaCall space dispatch value expected bindings fuel
  | .functions value expected bindings fuel types =>
      types.flatMap fun operatorType =>
        if isFunctionType operatorType then
          match checkIfFunctionTypeIsApplicable value operatorType expected space bindings fuel with
          | .inr alternatives => alternatives.flatMap fun selected =>
              (interpretFunction space dispatch value operatorType selected fuel).flatMap fun (result, output) =>
                mettaCall space dispatch result (resultType operatorType) output fuel
          | .inl _ => []
        else []
  | .bindingAlternatives value operatorType expected fuel alternatives =>
      alternatives.flatMap fun selected =>
        (interpretFunction space dispatch value operatorType selected fuel).flatMap fun (result, output) =>
          mettaCall space dispatch result expected output fuel
  | .heads operatorType arguments fuel alternatives =>
      alternatives.flatMap fun (head, selected) =>
        if isEmptyOrError head then [(head, selected)]
        else match getFunctionArgTypes operatorType with
          | some types => functionTail head (interpretArgs space dispatch arguments types selected fuel)
          | none => []
  | .argumentHeads original remaining types fuel alternatives =>
      alternatives.flatMap fun (head, selected) =>
        if head != original && isEmptyOrError head then [(head, selected)]
        else argumentTail head (interpretArgs space dispatch remaining types selected fuel)
  | .tupleHeads tail fuel alternatives =>
      alternatives.flatMap fun (head, selected) =>
        if isEmptyOrError head then [(head, selected)]
        else tupleTail head (interpretTuple space dispatch tail selected fuel)
  | .calls expected fuel alternatives =>
      alternatives.flatMap fun (value, bindings) => mettaCall space dispatch value expected bindings fuel
  | .atoms expected fuel alternatives =>
      alternatives.flatMap fun (value, bindings) => evalAtom space dispatch value expected bindings fuel
  | .equations expected incoming fuel alternatives =>
      alternatives.flatMap fun (rhs, selected) =>
        (mergeBindings selected incoming fuel).flatMap fun merged =>
          if merged.hasLoop then []
          else evalAtom space dispatch (merged.applyFull rhs fuel) expected merged fuel
  | .grounded expected incoming fuel alternatives =>
      alternatives.flatMap fun (value, selected) =>
        (mergeBindings selected incoming fuel).flatMap fun merged =>
          evalAtom space dispatch value expected merged fuel
  | .tupleCalls value expected bindings fuel =>
      (interpretTuple space dispatch value bindings fuel).flatMap fun (result, output) =>
        mettaCall space dispatch result expected output fuel

inductive Frame where
  | filter
  | heads (operatorType : Atom) (arguments : List Atom) (fuel : Nat)
  | argumentHeads (original : Atom) (remaining types : List Atom) (fuel : Nat)
  | tupleHeads (tail : Atom) (fuel : Nat)
  | calls (expected : Atom) (fuel : Nat)
  | functionTail (head : Atom)
  | argumentTail (head : Atom)
  | tupleSingleton
  | tupleTail (head : Atom)
  | append (remaining : Task)
  | prepend (selected : ResultSet)
  | fallback (value expected : Atom) (bindings : Bindings) (fuel : Nat) (types : List Atom)
  deriving Repr, DecidableEq

def Frame.denote (space : Space) (dispatch : GroundedDispatch) : Frame → ResultSet → ResultSet
  | .filter, results => successPriority results
  | .heads operatorType arguments fuel, results =>
      (Task.heads operatorType arguments fuel results).denote space dispatch
  | .argumentHeads original remaining types fuel, results =>
      (Task.argumentHeads original remaining types fuel results).denote space dispatch
  | .tupleHeads tail fuel, results => (Task.tupleHeads tail fuel results).denote space dispatch
  | .calls expected fuel, results => (Task.calls expected fuel results).denote space dispatch
  | .functionTail head, results => RecursiveTasks.functionTail head results
  | .argumentTail head, results => RecursiveTasks.argumentTail head results
  | .tupleSingleton, results => results.map HE.tupleSingleton
  | .tupleTail head, results => RecursiveTasks.tupleTail head results
  | .append remaining, results => results ++ remaining.denote space dispatch
  | .prepend selected, results => selected ++ results
  | .fallback value expected bindings fuel types, results =>
      functionFallback space value expected bindings fuel types results

inductive Control where
  | work (task : Task)
  | returning (results : ResultSet)
  deriving Repr, DecidableEq

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

def Configuration.remaining (dispatch : GroundedDispatch) (state : Configuration) : ResultSet :=
  state.stack.foldl (fun results frame => frame.denote state.space dispatch results)
    (state.control.denote state.space dispatch)

def Configuration.denote (dispatch : GroundedDispatch) (state : Configuration) : ResultSet :=
  state.emitted ++ state.remaining dispatch

@[simp] theorem denote_initial (space : Space) (dispatch : GroundedDispatch) (task : Task) :
    (Configuration.initial space task).denote dispatch = task.denote space dispatch := rfl

end Mettapedia.Languages.MeTTa.HE.RecursiveTasks
