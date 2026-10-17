import Mettapedia.Languages.MeTTa.HE.RecursiveTaskOrder
import Mettapedia.Languages.MeTTa.HE.RecursiveExecution

/-!
# Constructed work accounts for retained HE evaluation

The request dependency order supplies a finite work account. Continuations add
their own advances and the work of their retained requests. The account is
derived from the executable expansion and the independent evaluator meanings;
it is not a termination premise supplied by a client.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveWork

open RecursiveTasks RecursiveMachine RecursiveCorrectness RecursiveTaskOrder RecursiveExecution

def frameOverhead : Frame → Nat
  | .append _ => 2
  | _ => 1

/-- All spawned requests are smaller in the constructed dependency order. -/
def taskWork (space : Space) (dispatch : GroundedDispatch) : Task → Nat :=
  smaller_wellFounded.fix fun parent recur =>
    1 + ((enter space dispatch parent).2.map frameOverhead).sum +
      ((dependencies space dispatch parent).attach.map fun child =>
        recur child.val (dependency_smaller space dispatch parent child.val child.property)).sum

theorem taskWork_unfold (space : Space) (dispatch : GroundedDispatch) (task : Task) :
    taskWork space dispatch task =
      1 + ((enter space dispatch task).2.map frameOverhead).sum +
        ((dependencies space dispatch task).map (taskWork space dispatch)).sum := by
  conv_lhs => rw [taskWork, WellFounded.fix_eq]
  change 1 + _ + ((dependencies space dispatch task).attach.map
    (fun child => taskWork space dispatch child.val)).sum = _
  rw [List.attach_map_val]

def controlWork (work : Task → Nat) : Control → Nat
  | .work task => work task
  | .returning _ => 0

def frameWork (work : Task → Nat) (frame : Frame) (results : ResultSet) : Nat :=
  frameOverhead frame + ((frameRequests frame results).map work).sum

def stackWork (space : Space) (dispatch : GroundedDispatch) (work : Task → Nat) :
    List Frame → ResultSet → Nat
  | [], _ => 0
  | frame :: remaining, results =>
      frameWork work frame results + stackWork space dispatch work remaining (frame.denote space dispatch results)

def expandedWork (space : Space) (dispatch : GroundedDispatch) (work : Task → Nat)
    (expanded : Control × List Frame) : Nat :=
  controlWork work expanded.1 +
    stackWork space dispatch work expanded.2 (expanded.1.denote space dispatch)

theorem controlWork_requests (work : Task → Nat) (control : Control) :
    controlWork work control = ((controlRequests control).map work).sum := by
  cases control <;> rfl

theorem stackWork_requests (space : Space) (dispatch : GroundedDispatch) (work : Task → Nat)
    (frames : List Frame) (results : ResultSet) :
    stackWork space dispatch work frames results =
      (frames.map frameOverhead).sum + ((requests space dispatch frames results).map work).sum := by
  induction frames generalizing results with
  | nil => rfl
  | cons frame remaining ih =>
      simp only [stackWork, requests, List.map_cons, List.sum_cons, List.map_append, List.sum_append,
        ih, frameWork]
      omega

theorem expandedWork_requests (space : Space) (dispatch : GroundedDispatch) (work : Task → Nat)
    (task : Task) :
    expandedWork space dispatch work (enter space dispatch task) =
      ((enter space dispatch task).2.map frameOverhead).sum +
        ((dependencies space dispatch task).map work).sum := by
  simp only [expandedWork, controlWork_requests, stackWork_requests, dependencies,
    List.map_append, List.sum_append]
  omega

theorem taskWork_enter (space : Space) (dispatch : GroundedDispatch) (task : Task) :
    taskWork space dispatch task =
      1 + expandedWork space dispatch (taskWork space dispatch) (enter space dispatch task) := by
  rw [taskWork_unfold, expandedWork_requests]
  omega

theorem frameWork_resume (space : Space) (dispatch : GroundedDispatch) (work : Task → Nat)
    (frame : Frame) (results : ResultSet) :
    frameWork work frame results =
      1 + expandedWork space dispatch work (resume space frame results) := by
  cases frame with
  | invocationReturn mode original fuel live =>
      cases mode <;>
        simp [frameWork, frameOverhead, frameRequests, expandedWork, resume, controlWork, stackWork]
  | _ =>
      simp [frameWork, frameOverhead, frameRequests, expandedWork, resume, controlWork, stackWork,
        Nat.add_comm] <;> omega

theorem stackWork_append (space : Space) (dispatch : GroundedDispatch) (work : Task → Nat)
    (first second : List Frame) (results : ResultSet) :
    stackWork space dispatch work (first ++ second) results =
      stackWork space dispatch work first results +
        stackWork space dispatch work second
          (first.foldl (fun results frame => frame.denote space dispatch results) results) := by
  induction first generalizing results with
  | nil => simp [stackWork]
  | cons frame remaining ih =>
      simp only [List.cons_append, stackWork, List.foldl_cons, ih]
      omega

def configurationWork (dispatch : GroundedDispatch) (state : Configuration) : Nat :=
  controlWork (taskWork state.space dispatch) state.control +
    stackWork state.space dispatch (taskWork state.space dispatch) state.stack
      (state.control.denote state.space dispatch)

theorem next_work (dispatch : GroundedDispatch) (state after : Configuration)
    (advanced : next dispatch state = some after) :
    configurationWork dispatch after + 1 = configurationWork dispatch state := by
  cases state with
  | mk space control stack emitted =>
      cases control with
      | work task =>
          cases advanced
          simp only [configurationWork, stackWork_append, controlWork]
          rw [taskWork_enter]
          change _ + (_ + stackWork space dispatch _ stack
            (expandedDenote space dispatch (enter space dispatch task))) + 1 = _
          rw [enter_denote]
          simp only [expandedWork, controlWork, Control.denote]
          omega
      | returning results =>
          cases stack with
          | nil => simp [next] at advanced
          | cons frame remaining =>
              cases advanced
              simp only [configurationWork, stackWork_append, controlWork, Control.denote, stackWork]
              change _ + (_ + stackWork space dispatch _ remaining
                (expandedDenote space dispatch (resume space frame results))) + 1 = _
              rw [resume_denote, frameWork_resume space dispatch (taskWork space dispatch) frame results]
              simp only [expandedWork, controlWork, Control.denote]
              omega

end Mettapedia.Languages.MeTTa.HE.RecursiveWork
