import Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness

/-!
# Well-founded dependencies of retained evaluator requests

Entering a request produces smaller requests: recursive evaluator fuel falls,
or a finite traversal moves to a lower layer, or its remaining list shortens.
The order does not require source evaluation to terminate without fuel.
Continuation requests use the retained selected results, including bindings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveTaskOrder

open RecursiveTasks RecursiveMachine RecursiveCorrectness

def taskKey : Task → Nat × Nat × Nat
  | .atom _ _ _ fuel | .expression _ _ _ fuel | .func _ _ _ fuel
  | .args _ _ _ fuel | .tuple _ _ fuel | .call _ _ _ fuel => (fuel, 0, 0)
  | .functions _ _ _ fuel types => (fuel, 3, types.length)
  | .bindingAlternatives _ _ _ fuel alternatives => (fuel, 2, alternatives.length)
  | .heads _ _ fuel alternatives | .argumentHeads _ _ _ fuel alternatives
  | .tupleHeads _ fuel alternatives | .equations _ _ fuel alternatives
  | .grounded _ _ fuel alternatives => (fuel, 2, alternatives.length)
  | .calls _ fuel alternatives | .atoms _ fuel alternatives => (fuel, 1, alternatives.length)
  | .tupleCalls _ _ _ fuel => (fuel, 2, 0)

def Smaller (child parent : Task) : Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) (taskKey child) (taskKey parent)

theorem smaller_wellFounded : WellFounded Smaller :=
  InvImage.wf taskKey (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

def controlRequests : Control → List Task
  | .work task => [task]
  | .returning _ => []

def frameRequests : Frame → ResultSet → List Task
  | .heads operatorType arguments fuel, results => [.heads operatorType arguments fuel results]
  | .argumentHeads original remaining types fuel, results =>
      [.argumentHeads original remaining types fuel results]
  | .tupleHeads tail fuel, results => [.tupleHeads tail fuel results]
  | .calls expected fuel, results => [.calls expected fuel results]
  | .append remaining, _ => [remaining]
  | _, _ => []

def requests (space : Space) (dispatch : GroundedDispatch) : List Frame → ResultSet → List Task
  | [], _ => []
  | frame :: remaining, results =>
      frameRequests frame results ++ requests space dispatch remaining (frame.denote space dispatch results)

def dependencies (space : Space) (dispatch : GroundedDispatch) (task : Task) : List Task :=
  let expanded := enter space dispatch task
  controlRequests expanded.1 ++ requests space dispatch expanded.2 (expanded.1.denote space dispatch)

theorem dependency_smaller (space : Space) (dispatch : GroundedDispatch) (parent child : Task)
    (dependent : child ∈ dependencies space dispatch parent) : Smaller child parent := by
  cases parent with
  | atom value expected bindings fuel =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
  | expression value expected bindings fuel =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | func value operatorType bindings fuel =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | args values types bindings fuel =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | tuple value bindings fuel =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | call value expected bindings fuel =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, Smaller, taskKey, Prod.lex_def]
  | functions value expected bindings fuel types =>
      cases types with
      | nil => simp [dependencies, enter, controlRequests, requests] at dependent
      | cons operatorType remaining =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | bindingAlternatives value operatorType expected fuel alternatives =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all
  | heads operatorType arguments fuel alternatives =>
      cases alternatives with
      | nil => simp [dependencies, enter, controlRequests, requests] at dependent
      | cons head remaining =>
          rcases head with ⟨value, bindings⟩
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | argumentHeads original remaining types fuel alternatives =>
      cases alternatives with
      | nil => simp [dependencies, enter, controlRequests, requests] at dependent
      | cons head rest =>
          rcases head with ⟨value, bindings⟩
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | tupleHeads tail fuel alternatives =>
      cases alternatives with
      | nil => simp [dependencies, enter, controlRequests, requests] at dependent
      | cons head rest =>
          rcases head with ⟨value, bindings⟩
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | calls expected fuel alternatives =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all
  | atoms expected fuel alternatives =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all
  | equations expected incoming fuel alternatives =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all
  | grounded expected incoming fuel alternatives =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all
  | tupleCalls value expected bindings fuel =>
      simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all

end Mettapedia.Languages.MeTTa.HE.RecursiveTaskOrder
