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
  cases frame <;> rfl

private theorem keep_nonempty (results : ResultSet) :
    (if !results.isEmpty then results else []) = results := by
  cases results <;> rfl

theorem enter_atom_denote (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel : Nat) :
    expandedDenote space dispatch (enter space dispatch (.atom value expected bindings fuel)) =
      (Task.atom value expected bindings fuel).denote space dispatch := by
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
    (value expected : Atom) (bindings : Bindings) (fuel : Nat) :
    expandedDenote space dispatch (enter space dispatch (.expression value expected bindings fuel)) =
      (Task.expression value expected bindings fuel).denote space dispatch := by
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
              let functions := (Task.functions value expected bindings fuel types).denote space dispatch
              let tuples := (Task.tupleCalls value expected bindings fuel).denote space dispatch
              cases selected : (getAtomTypes space operator).any
                  (fun type => !isFunctionType type || type == Atom.undefinedType) with
              | true =>
                  simp only [enter, Task.denote, interpretExpression, selected, Bool.not_true,
                    Bool.false_eq_true, if_false, if_true, expandedDenote, List.foldl_cons,
                    List.foldl_nil, Frame.denote, Control.denote]
                  change functions ++ tuples = (if !(functions ++ tuples).isEmpty then functions ++ tuples else [])
                  exact (keep_nonempty (functions ++ tuples)).symm
              | false =>
                  simp only [enter, Task.denote, interpretExpression, selected, Bool.false_eq_true,
                    if_false, Bool.not_false, if_true, expandedDenote, List.foldl_cons,
                    List.foldl_nil, Frame.denote, Control.denote, List.append_nil]
                  rfl

theorem enter_call_denote (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel : Nat) :
    expandedDenote space dispatch (enter space dispatch (.call value expected bindings fuel)) =
      (Task.call value expected bindings fuel).denote space dispatch := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      generalize expanded : enter space dispatch (.call value expected bindings (fuel + 1)) = entered
      simp only [enter] at expanded
      repeat' split at expanded
      all_goals subst entered
      all_goals simp_all [expandedDenote, Control.denote, Task.denote, mettaCall]

theorem equation_candidates_denote (space : Space) (dispatch : GroundedDispatch)
    (rhs expected : Atom) (fuel : Nat) (alternatives : List Bindings) :
    ((alternatives.filterMap fun merged =>
      if merged.hasLoop then none else some (merged.applyFull rhs fuel, merged)).flatMap
        fun (value, bindings) => evalAtom space dispatch value expected bindings fuel) =
      alternatives.flatMap (fun merged =>
        if merged.hasLoop then [] else evalAtom space dispatch (merged.applyFull rhs fuel) expected merged fuel) := by
  induction alternatives with
  | nil => rfl
  | cons bindings remaining ih =>
      cases loop : bindings.hasLoop <;> simp [loop, ih]

theorem enter_denote (space : Space) (dispatch : GroundedDispatch) (task : Task) :
    expandedDenote space dispatch (enter space dispatch task) = task.denote space dispatch := by
  cases task with
  | atom value expected bindings fuel =>
      exact enter_atom_denote space dispatch value expected bindings fuel
  | expression value expected bindings fuel =>
      exact enter_expression_denote space dispatch value expected bindings fuel
  | func value operatorType bindings fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases value with
          | symbol name => rfl
          | var name => rfl
          | grounded value => rfl
          | expression elements => cases elements <;> rfl
  | args values types bindings fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases values <;> cases types <;> rfl
  | tuple value bindings fuel =>
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
  | call value expected bindings fuel =>
      exact enter_call_denote space dispatch value expected bindings fuel
  | functions value expected bindings fuel types =>
      cases types with
      | nil => rfl
      | cons operatorType remaining =>
          simp only [enter]
          repeat' split
          all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | bindingAlternatives value operatorType expected fuel alternatives =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | heads operatorType arguments fuel alternatives =>
      cases alternatives with
      | nil => rfl
      | cons head remaining =>
          rcases head with ⟨value, bindings⟩
          simp only [enter]
          repeat' split
          all_goals simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | argumentHeads original remaining types fuel alternatives =>
      cases alternatives with
      | nil => rfl
      | cons head rest =>
          rcases head with ⟨value, bindings⟩
          simp only [enter]
          split <;> simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | tupleHeads tail fuel alternatives =>
      cases alternatives with
      | nil => rfl
      | cons head rest =>
          rcases head with ⟨value, bindings⟩
          simp only [enter]
          split <;> simp_all [expandedDenote, Control.denote, Frame.denote, Task.denote]
  | calls expected fuel alternatives =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | atoms expected fuel alternatives =>
      cases alternatives <;> simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote]
  | equations expected incoming fuel alternatives =>
      cases alternatives with
      | nil => rfl
      | cons head rest =>
          rcases head with ⟨value, selected⟩
          simp only [expandedDenote, enter, Control.denote, Frame.denote, Task.denote,
            List.foldl_cons, List.foldl_nil, List.flatMap_cons]
          rw [equation_candidates_denote]
  | grounded expected incoming fuel alternatives =>
      cases alternatives with
      | nil => rfl
      | cons head remaining =>
          rcases head with ⟨value, selected⟩
          simp [expandedDenote, enter, Control.denote, Frame.denote, Task.denote, List.flatMap_map]
  | tupleCalls value expected bindings fuel => rfl

end Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness
