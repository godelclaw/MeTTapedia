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

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveMachine

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Expansion does not call any of the six recursive evaluator functions. -/
def enter (space : Space) (dispatch : GroundedDispatch) : Task → Control × List Frame
  | .atom _ _ _ 0 => (.returning [], [])
  | .atom value expected bindings (n + 1) =>
      if isEmptyOrError value then (.returning [(value, bindings)], [])
      else if expected == Atom.atomType || expected == getMetaType value ||
          getMetaType value == Atom.variableType then (.returning [(value, bindings)], [])
      else if getMetaType value == Atom.symbolType || getMetaType value == Atom.groundedType ||
          value == Atom.unit then (.returning (typeCast value expected space bindings n), [])
      else if getMetaType value == Atom.expressionType then
        (.work (.expression value expected bindings n), [.filter])
      else (.returning [(value, bindings)], [])
  | .expression _ _ _ 0 => (.returning [], [])
  | .expression value expected bindings (n + 1) =>
      match value with
      | .expression (operator :: _) =>
          let types := getAtomTypes space operator
          let continuation :=
            if types.any (fun type => !isFunctionType type || type == Atom.undefinedType)
            then Frame.append (.tupleCalls value expected bindings n)
            else .fallback value expected bindings n types
          (.work (.functions value expected bindings n types), [continuation])
      | _ => (.returning [], [])
  | .func _ _ _ 0 => (.returning [], [])
  | .func value operatorType bindings (n + 1) =>
      match value with
      | .expression (operator :: arguments) =>
          (.work (.atom operator operatorType bindings n), [.heads operatorType arguments n])
      | _ => (.returning [], [])
  | .args _ _ _ 0 => (.returning [], [])
  | .args values types bindings (n + 1) =>
      match values, types with
      | [], [] => (.returning [(argumentPacket [], bindings)], [])
      | value :: remaining, type :: remainingTypes =>
          (.work (.atom value type bindings n), [.argumentHeads value remaining remainingTypes n])
      | _, _ => (.returning [], [])
  | .tuple _ _ 0 => (.returning [], [])
  | .tuple value bindings (n + 1) =>
      match value with
      | .expression [] => (.returning [(Atom.unit, bindings)], [])
      | .expression [single] => (.work (.atom single Atom.undefinedType bindings n), [.tupleSingleton])
      | .expression (head :: second :: remaining) =>
          (.work (.atom head Atom.undefinedType bindings n), [.tupleHeads (.expression (second :: remaining)) n])
      | _ => (.returning [], [])
  | .call _ _ _ 0 => (.returning [], [])
  | .call value expected bindings (n + 1) =>
      if isErrorAtom value then (.returning [(value, bindings)], [])
      else match value with
      | .expression [.symbol "unify", target, pattern, thenBranch, elseBranch] =>
          let results := unifySuccessResults target pattern thenBranch bindings n
          (.returning (if results.isEmpty then [(elseBranch, bindings)] else results), [])
      | .expression (.symbol "unify" :: _) =>
          (.returning [(mkUnifyBadArityError value, bindings)], [])
      | .expression [.symbol "switch-minimal", scrutinee, .expression branches] =>
          (.returning (switchMinimalResults scrutinee branches bindings n), [])
      | .expression (.symbol "switch-minimal" :: _) =>
          (.returning [(mkError value .incorrectNumberOfArguments, bindings)], [])
      | .expression (operator :: arguments) =>
          if dispatch.isExecutable operator then
            match dispatch.execute operator arguments with
            | .ok results =>
                if results.isEmpty then (.returning [(Atom.empty, bindings)], [])
                else (.work (.grounded expected bindings n results), [])
            | .runtimeError message => (.returning [(Atom.error value (.symbol message), bindings)], [])
            | .noReduce | .incorrectArgument => (.returning [(value, bindings)], [])
          else
            let equations := queryEquations space value n
            if equations.isEmpty then (.returning [(value, bindings)], [])
            else (.work (.equations expected bindings n equations), [])
      | _ =>
          let equations := queryEquations space value n
          if equations.isEmpty then (.returning [(value, bindings)], [])
          else (.work (.equations expected bindings n equations), [])
  | .functions _ _ _ _ [] => (.returning [], [])
  | .functions value expected bindings fuel (operatorType :: remaining) =>
      let rest := Frame.append (.functions value expected bindings fuel remaining)
      if isFunctionType operatorType then
        match checkIfFunctionTypeIsApplicable value operatorType expected space bindings fuel with
        | .inl _ => (.returning [], [rest])
        | .inr alternatives =>
            (.work (.bindingAlternatives value operatorType (resultType operatorType) fuel alternatives), [rest])
      else (.returning [], [rest])
  | .bindingAlternatives _ _ _ _ [] => (.returning [], [])
  | .bindingAlternatives value operatorType expected fuel (selected :: remaining) =>
      (.work (.func value operatorType selected fuel),
        [.calls expected fuel, .append (.bindingAlternatives value operatorType expected fuel remaining)])
  | .heads _ _ _ [] => (.returning [], [])
  | .heads operatorType arguments fuel ((head, selected) :: remaining) =>
      let rest := Frame.append (.heads operatorType arguments fuel remaining)
      if isEmptyOrError head then (.returning [(head, selected)], [rest])
      else match getFunctionArgTypes operatorType with
        | none => (.returning [], [rest])
        | some types => (.work (.args arguments types selected fuel), [.functionTail head, rest])
  | .argumentHeads _ _ _ _ [] => (.returning [], [])
  | .argumentHeads original remaining types fuel ((head, selected) :: alternatives) =>
      let rest := Frame.append (.argumentHeads original remaining types fuel alternatives)
      if head != original && isEmptyOrError head then (.returning [(head, selected)], [rest])
      else (.work (.args remaining types selected fuel), [.argumentTail head, rest])
  | .tupleHeads _ _ [] => (.returning [], [])
  | .tupleHeads tail fuel ((head, selected) :: remaining) =>
      let rest := Frame.append (.tupleHeads tail fuel remaining)
      if isEmptyOrError head then (.returning [(head, selected)], [rest])
      else (.work (.tuple tail selected fuel), [.tupleTail head, rest])
  | .calls _ _ [] => (.returning [], [])
  | .calls expected fuel ((value, bindings) :: remaining) =>
      (.work (.call value expected bindings fuel), [.append (.calls expected fuel remaining)])
  | .atoms _ _ [] => (.returning [], [])
  | .atoms expected fuel ((value, bindings) :: remaining) =>
      (.work (.atom value expected bindings fuel), [.append (.atoms expected fuel remaining)])
  | .equations _ _ _ [] => (.returning [], [])
  | .equations expected incoming fuel ((rhs, selected) :: remaining) =>
      let alternatives := (mergeBindings selected incoming fuel).filterMap fun merged =>
        if merged.hasLoop then none else some (merged.applyFull rhs fuel, merged)
      (.work (.atoms expected fuel alternatives), [.append (.equations expected incoming fuel remaining)])
  | .grounded _ _ _ [] => (.returning [], [])
  | .grounded expected incoming fuel ((value, selected) :: remaining) =>
      (.work (.atoms expected fuel ((mergeBindings selected incoming fuel).map fun merged => (value, merged))),
        [.append (.grounded expected incoming fuel remaining)])
  | .tupleCalls value expected bindings fuel =>
      (.work (.tuple value bindings fuel), [.calls expected fuel])

def resume (space : Space) (frame : Frame) (results : ResultSet) : Control × List Frame :=
  match frame with
  | .filter => (.returning (successPriority results), [])
  | .heads operatorType arguments fuel => (.work (.heads operatorType arguments fuel results), [])
  | .argumentHeads original remaining types fuel =>
      (.work (.argumentHeads original remaining types fuel results), [])
  | .tupleHeads tail fuel => (.work (.tupleHeads tail fuel results), [])
  | .calls expected fuel => (.work (.calls expected fuel results), [])
  | .functionTail head => (.returning (RecursiveTasks.functionTail head results), [])
  | .argumentTail head => (.returning (RecursiveTasks.argumentTail head results), [])
  | .tupleSingleton => (.returning (results.map HE.tupleSingleton), [])
  | .tupleTail head => (.returning (RecursiveTasks.tupleTail head results), [])
  | .append remaining => (.work remaining, [.prepend results])
  | .prepend selected => (.returning (selected ++ results), [])
  | .fallback value expected bindings fuel types =>
      (.returning (functionFallback space value expected bindings fuel types results), [])

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

/-- Completion drains each occurrence once; an empty result list is ordinary
completion of this evaluator, not a committed external effect. -/
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

end Mettapedia.Languages.MeTTa.HE.RecursiveMachine
