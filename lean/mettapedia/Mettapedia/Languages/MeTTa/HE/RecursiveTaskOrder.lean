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
  | .atom _ _ _ fuel _ | .expression _ _ _ fuel _ | .func _ _ _ fuel _
  | .args _ _ _ fuel _ | .tuple _ _ fuel _ => (fuel, 0, 0)
  | .call _ _ _ fuel _ => (fuel, 1, 0)
  | .functions _ _ _ fuel types _ => (fuel, 5, types.length)
  | .bindingAlternatives _ _ _ fuel alternatives _ => (fuel, 4, alternatives.length)
  | .heads _ _ fuel alternatives _ | .argumentHeads _ _ _ fuel alternatives _
  | .tupleHeads _ fuel alternatives _ => (fuel, 3, alternatives.length)
  | .returned _ _ _ _ fuel _ => (fuel, 1, 0)
  | .returns _ _ fuel alternatives _ => (fuel, 2, alternatives.length)
  | .equations _ _ _ fuel alternatives _
  | .grounded _ _ _ fuel alternatives _ => (fuel, 1, alternatives.length)
  | .calls _ fuel alternatives _ | .atoms _ fuel alternatives _ => (fuel, 2, alternatives.length)
  | .tupleCalls _ _ _ fuel _ => (fuel, 3, 0)
  | .invocation _ _ _ fuel _ _ | .produced _ _ fuel _ _ _
  | .minimal _ _ fuel _ _ | .primitive _ _ fuel _ _
  | .functionBody _ _ fuel _ _ | .completed _ _ _ fuel => (fuel, 0, 0)
  | .productions fuel alternatives _ _ _ | .minimals fuel alternatives _ _
  | .chainRows _ _ fuel alternatives | .bodyResults fuel alternatives _ _ =>
      (fuel, 1, alternatives.length)
  | .producerResults _ _ _ fuel _ _ _ => (fuel, 4, 0)

def Smaller (child parent : Task) : Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) (taskKey child) (taskKey parent)

theorem smaller_wellFounded : WellFounded Smaller :=
  InvImage.wf taskKey (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

def controlRequests : Control → List Task
  | .work task => [task]
  | .returning _ => []

def frameRequests : Frame → ResultSet → List Task
  | .heads operatorType arguments fuel live, results =>
      [.heads operatorType arguments fuel results live]
  | .argumentHeads original remaining types fuel live, results =>
      [.argumentHeads original remaining types fuel results live]
  | .tupleHeads tail fuel live, results => [.tupleHeads tail fuel results live]
  | .calls expected fuel live, results => [.calls expected fuel results live]
  | .append remaining, _ => [remaining]
  | .invocationReturn mode original fuel live, results =>
      match mode with
      | .raw => []
      | .ordinary expected => [.returns original expected fuel results live]
  | .producerResults mode original incoming fuel live emptyReply, results =>
      [.producerResults mode original incoming fuel live emptyReply results]
  | .minimalResults fuel live caller, results => [.minimals fuel results live caller]
  | .chainResults name template fuel, results => [.chainRows name template fuel results]
  | .bodyResults fuel live caller, results => [.bodyResults fuel results live caller]
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
  | atom value expected bindings fuel live =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
  | expression value expected bindings fuel live =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | func value operatorType bindings fuel live =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | args values types bindings fuel live =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | tuple value bindings fuel live =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | call value expected bindings fuel live =>
      simp_all [dependencies, enter, controlRequests, requests, Smaller, taskKey, Prod.lex_def]
  | functions value expected bindings fuel types live =>
      cases types with
      | nil => simp [dependencies, enter, controlRequests, requests] at dependent
      | cons operatorType remaining =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | bindingAlternatives value operatorType expected fuel alternatives live =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all
  | heads operatorType arguments fuel alternatives live =>
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
  | argumentHeads original remaining types fuel alternatives live =>
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
  | tupleHeads tail fuel alternatives live =>
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
  | calls expected fuel alternatives live =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all
  | atoms expected fuel alternatives live =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all
  | returned original value expected bindings fuel live =>
      simp only [dependencies, enter] at dependent
      repeat' split at dependent
      all_goals
        simp_all [controlRequests, requests, Smaller, taskKey, Prod.lex_def]
  | returns original expected fuel alternatives live =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all
  | equations original expected incoming fuel alternatives live =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
  | grounded original expected incoming fuel alternatives live =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
  | tupleCalls value expected bindings fuel live =>
      simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all
  | invocation mode value bindings fuel live caller =>
      cases mode <;> cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | produced value bindings fuel live caller provenance =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, Smaller, taskKey, Prod.lex_def]
  | minimal value bindings fuel live caller =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | primitive value bindings fuel live caller =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | functionBody value bindings fuel live caller =>
      cases fuel with
      | zero => simp [dependencies, enter, controlRequests, requests] at dependent
      | succ fuel =>
          simp only [dependencies, enter] at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | productions fuel alternatives live caller provenance =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all
  | minimals fuel alternatives live caller =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      repeat' rcases dependent with rfl | dependent
      all_goals simp_all
  | chainRows name template fuel alternatives =>
      cases alternatives <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
  | bodyResults fuel alternatives live caller =>
      cases alternatives with
      | nil => simp [dependencies, enter, controlRequests, requests] at dependent
      | cons pair remaining =>
          rcases pair with ⟨value, bindings⟩
          simp only [dependencies, enter] at dependent
          repeat' split at dependent
          all_goals
            simp_all [controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
            repeat' rcases dependent with rfl | dependent
            all_goals simp_all
  | producerResults mode original incoming fuel live emptyReply results =>
      cases mode <;> cases results <;>
        simp_all [dependencies, enter, controlRequests, requests, frameRequests, Smaller, taskKey, Prod.lex_def]
      all_goals
        repeat' rcases dependent with rfl | dependent
        all_goals simp_all
  | completed value expected bindings fuel =>
      simp [dependencies, enter, controlRequests, requests] at dependent

end Mettapedia.Languages.MeTTa.HE.RecursiveTaskOrder
