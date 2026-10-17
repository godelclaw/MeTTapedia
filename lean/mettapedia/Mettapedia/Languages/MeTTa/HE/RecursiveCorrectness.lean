import Mettapedia.Languages.MeTTa.HE.RecursiveMachine

/-!
# Ordered correspondence for retained recursive HE control

The machine's first-order expansion and the existing recursive evaluator
are separate computations. Their meanings agree at each internal advance.
Result publication transfers one retained occurrence into the observed history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine

def expandedDenote (space : Space) (dispatch : GroundedDispatch)
    (expanded : Control × List Frame) : ResultSet :=
  expanded.2.foldl (fun results frame => frame.denote space dispatch results)
    (expanded.1.denote space dispatch)

theorem resume_denote (space : Space) (dispatch : GroundedDispatch)
    (frame : Frame) (results : ResultSet) :
    expandedDenote space dispatch (resume space frame results) = frame.denote space dispatch results := by
  cases frame with
  | invocationReturn mode original fuel live => cases mode <;> rfl
  | producerResults mode original incoming fuel live emptyReply => cases results <;> rfl
  | _ => rfl

private theorem keep_nonempty (results : ResultSet) :
    (if !results.isEmpty then results else []) = results := by
  cases results <;> rfl

theorem enter_atom_denote (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    expandedDenote space dispatch (enter space dispatch (.atom value expected bindings fuel live)) =
      (Task.atom value expected bindings fuel live).denote space dispatch := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      by_cases empty : isEmptyOrError value = true
      · simp only [enter, Task.denote, evalAtom, empty, if_true]
        rfl
      · by_cases trivial : (expected == Atom.atomType || expected == getMetaType value ||
            getMetaType value == Atom.variableType) = true
        · simp only [enter, Task.denote, evalAtom, empty, trivial, if_true]
          rfl
        · by_cases scalar : (getMetaType value == Atom.symbolType ||
              getMetaType value == Atom.groundedType || value == Atom.unit) = true
          · simp only [enter, Task.denote, evalAtom, empty, trivial, scalar, if_true]
            rfl
          · by_cases expression : (getMetaType value == Atom.expressionType) = true
            · simp only [enter, Task.denote, evalAtom, empty, trivial, scalar, expression, if_true]
              rfl
            · simp only [enter, Task.denote, evalAtom, empty, trivial, scalar, expression]
              rfl

theorem enter_expression_denote (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    expandedDenote space dispatch (enter space dispatch (.expression value expected bindings fuel live)) =
      (Task.expression value expected bindings fuel live).denote space dispatch := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases value with
      | symbol name => rfl
      | var name => rfl
      | grounded value => rfl
      | expression elements =>
          cases elements with
          | nil => rfl
          | cons operator arguments =>
              let value := Atom.expression (operator :: arguments)
              let types := getAtomTypes space operator
              let functions := (Task.functions value expected bindings fuel types live).denote space dispatch
              let tuples := (Task.tupleCalls value expected bindings fuel live).denote space dispatch
              cases selected : (getAtomTypes space operator).any
                  (fun type => !isFunctionType type || type == Atom.undefinedType) with
              | true =>
                  simp only [enter, rawTypeLookup, Task.denote, interpretExpression, selected, Bool.not_true,
                    Bool.false_eq_true, if_false, if_true, expandedDenote, List.foldl_cons,
                    List.foldl_nil, Frame.denote, Control.denote]
                  change functions ++ tuples = (if !(functions ++ tuples).isEmpty then functions ++ tuples else [])
                  exact (keep_nonempty (functions ++ tuples)).symm
              | false =>
                  simp only [enter, rawTypeLookup, Task.denote, interpretExpression, selected, Bool.false_eq_true,
                    if_false, Bool.not_false, if_true, expandedDenote, List.foldl_cons,
                    List.foldl_nil, Frame.denote, Control.denote, List.append_nil]
                  rfl

theorem enter_call_denote (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    expandedDenote space dispatch (enter space dispatch (.call value expected bindings fuel live)) =
      (Task.call value expected bindings fuel live).denote space dispatch := by
  rfl

set_option maxHeartbeats 1200000 in
theorem enter_invocation_denote (space : Space) (dispatch : GroundedDispatch)
    (mode : InvocationMode) (value : Atom) (bindings : Bindings) (fuel : Nat)
    (live : List Atom) (caller : Option Atom) :
    expandedDenote space dispatch (enter space dispatch (.invocation mode value bindings fuel live caller)) =
      (Task.invocation mode value bindings fuel live caller).denote space dispatch := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      change expandedDenote space dispatch (enter space dispatch
        (.invocation mode value bindings (fuel + 1) live caller)) =
        invoke space dispatch mode value bindings (fuel + 1) live caller
      rw [invoke]
      generalize expanded : enter space dispatch (.invocation mode value bindings (fuel + 1) live caller) = entered
      simp only [enter] at expanded
      repeat' split at expanded
      all_goals subst entered
      all_goals cases mode
      all_goals simp_all [expandedDenote, Control.denote, Frame.denote,
        Task.denote, rawQueryResults, invocationFinish, List.flatMap_assoc]
      all_goals simp only [List.isEmpty_iff]
      all_goals split <;> simp_all [List.flatMap_assoc]

theorem equation_candidates_denote (space : Space) (dispatch : GroundedDispatch)
    (original rhs expected : Atom) (fuel : Nat) (live : List Atom) (alternatives : List Bindings) :
    ((alternatives.filterMap fun merged =>
      if merged.hasLoop then none else some (merged.applyFull rhs fuel, merged)).flatMap
        fun (value, bindings) => ordinaryCallReturn original value bindings
          (fun value bindings => evalAtom space dispatch value expected bindings fuel live)) =
      alternatives.flatMap (fun merged =>
        if merged.hasLoop then []
        else ordinaryCallReturn original (merged.applyFull rhs fuel) merged
          (fun value bindings => evalAtom space dispatch value expected bindings fuel live)) := by
  induction alternatives with
  | nil => rfl
  | cons bindings remaining ih =>
      cases loop : bindings.hasLoop <;> simp [loop, ih]

set_option maxHeartbeats 1200000 in
theorem enter_denote (space : Space) (dispatch : GroundedDispatch) (task : Task) :
    expandedDenote space dispatch (enter space dispatch task) = task.denote space dispatch := by
  cases task with
  | atom value expected bindings fuel live =>
      exact enter_atom_denote space dispatch value expected bindings fuel live
  | expression value expected bindings fuel live =>
      exact enter_expression_denote space dispatch value expected bindings fuel live
  | func value operatorType bindings fuel live =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases value with
          | symbol name => rfl
          | var name => rfl
          | grounded value => rfl
          | expression elements => cases elements <;> rfl
  | args values types bindings fuel live =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases values <;> cases types <;> rfl
  | tuple value bindings fuel live =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases value with
          | symbol name => rfl
          | var name => rfl
          | grounded value => rfl
          | expression elements =>
              cases elements with
              | nil => rfl
              | cons head rest => cases rest <;> rfl
  | call value expected bindings fuel live =>
      exact enter_call_denote space dispatch value expected bindings fuel live
  | functions value expected bindings fuel types live =>
      cases types with
      | nil => rfl
      | cons operatorType remaining =>
          simp only [enter]
          repeat' split
          all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | bindingAlternatives value operatorType expected fuel alternatives live =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | heads operatorType arguments fuel alternatives live =>
      cases alternatives with
      | nil => rfl
      | cons head remaining =>
          rcases head with ⟨value, bindings⟩
          simp only [enter]
          repeat' split
          all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | argumentHeads original remaining types fuel alternatives live =>
      cases alternatives with
      | nil => rfl
      | cons head rest =>
          rcases head with ⟨value, bindings⟩
          simp only [enter]
          split <;> simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | tupleHeads tail fuel alternatives live =>
      cases alternatives with
      | nil => rfl
      | cons head rest =>
          rcases head with ⟨value, bindings⟩
          simp only [enter]
          split <;> simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | calls expected fuel alternatives live =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | atoms expected fuel alternatives live =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | returned original value expected bindings fuel live =>
      simp only [enter]
      repeat' split
      all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote, ordinaryCallReturn]
  | returns original expected fuel alternatives live =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | equations original expected incoming fuel alternatives live =>
      cases alternatives <;> rfl
  | grounded original expected incoming fuel alternatives live =>
      cases alternatives <;> rfl
  | tupleCalls value expected bindings fuel live => rfl
  | invocation mode value bindings fuel live caller =>
      exact enter_invocation_denote space dispatch mode value bindings fuel live caller
  | produced value bindings fuel live caller provenance =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [enter, Task.denote, invocationResult]
          repeat' split
          all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | productions fuel alternatives live caller provenance =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | minimal value bindings fuel live caller =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [enter, Task.denote, minimalRun]
          repeat' split
          all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | minimals fuel alternatives live caller =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | primitive value bindings fuel live caller =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [enter, Task.denote, minimalStep]
          repeat' split
          all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
          all_goals
            exfalso
            rename_i impossible same
            exact impossible _ _ _ _ same.symm
  | chainRows name template fuel alternatives => cases alternatives <;> rfl
  | functionBody value bindings fuel live caller => cases fuel <;> rfl
  | bodyResults fuel alternatives live caller =>
      cases alternatives with
      | nil => rfl
      | cons pair remaining =>
          rcases pair with ⟨value, bindings⟩
          simp only [enter]
          split <;> simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | producerResults mode original incoming fuel live emptyReply results =>
      cases results <;> rfl
  | completed value expected bindings fuel => rfl

end Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness
