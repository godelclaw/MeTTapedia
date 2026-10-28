import Mettapedia.Machines.OwnedPullDriver

/-!
# Transporting an entered job and its untried equation frontier

The source observes the actual entered residual, then remaining equations from
inner frames before outer frames. The target walks retained equation positions,
attaches each frame's captured caller, pushes outer choices first, and leaves
the entered residual on top. No source entrance is reconstructed.

The refinement is parametric in executable jobs and their complete event
traces. It preserves duplicate equations and caller captures, including empty
frames and split driver execution. Pointer ownership, snapshot validation,
foreign solver correctness and C/source-fuel correspondence are separate duties.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedFrontierTransfer

open OwnedPullDriver

structure Frame (Job : Type) where
  equations : List Job
  next : Nat
  resume : Job → Job

variable {Job : Type}

def remaining (frame : Frame Job) : List Job :=
  (frame.equations.drop frame.next).map frame.resume

/-- Recursive source observation of a retained call stack. -/
def reference (entered : Job) (outerFirst : List (Frame Job)) : List Job :=
  entered :: outerFirst.reverse.flatMap remaining

/-- The target walks source positions before emitting captured equation jobs. -/
def lowerFrame (resume : Job → Job) : List Job → Nat → List Job → List Job
  | [], _, stack => stack
  | _ :: rest, next + 1, stack => lowerFrame resume rest next stack
  | equation :: rest, 0, stack => resume equation :: lowerFrame resume rest 0 stack

/-- A later, inner frame is pushed above previously installed outer choices. -/
def installFrames : List (Frame Job) → List Job → List Job
  | [], stack => stack
  | frame :: rest, stack => installFrames rest
      (lowerFrame frame.resume frame.equations frame.next stack)

def install (entered : Job) (outerFirst : List (Frame Job)) : List Job :=
  entered :: installFrames outerFirst []

theorem lowerFrame_refines (resume : Job → Job) (equations : List Job)
    (next : Nat) (stack : List Job) :
    lowerFrame resume equations next stack = (equations.drop next).map resume ++ stack := by
  induction equations generalizing next with
  | nil => simp [lowerFrame]
  | cons equation rest ih =>
      cases next <;> simp [lowerFrame, ih]

theorem installFrames_refines (frames : List (Frame Job)) (stack : List Job) :
    installFrames frames stack = frames.reverse.flatMap remaining ++ stack := by
  induction frames generalizing stack with
  | nil => rfl
  | cons frame rest ih =>
      simp [installFrames, ih, lowerFrame_refines, List.reverse_cons,
        List.flatMap_append, remaining, List.append_assoc]

theorem installation_refines (entered : Job) (frames : List (Frame Job)) :
    install entered frames = reference entered frames := by
  simp [install, reference, installFrames_refines]

theorem committed_equations_skipped (resume : Job → Job)
    (committed future stack : List Job) :
    lowerFrame resume (committed ++ future) committed.length stack = future.map resume ++ stack := by
  simp [lowerFrame_refines]

theorem exhausted_frame_has_no_alternatives (frame : Frame Job)
    (exhausted : frame.equations.length ≤ frame.next) (stack : List Job) :
    lowerFrame frame.resume frame.equations frame.next stack = stack := by
  simp [lowerFrame_refines, List.drop_eq_nil_iff.mpr exhausted]

/-- Exhausting every ordinary frame leaves the target's earlier stack intact. -/
theorem exhausted_frames_preserve_stack (frames : List (Frame Job)) (stack : List Job)
    (exhausted : ∀ frame ∈ frames, frame.equations.length ≤ frame.next) :
    installFrames frames stack = stack := by
  induction frames generalizing stack with
  | nil => rfl
  | cons frame rest ih =>
      have current : frame.equations.length ≤ frame.next := exhausted frame (by simp)
      have future : ∀ item ∈ rest, item.equations.length ≤ item.next := by
        intro item member
        exact exhausted item (by simp [member])
      simp only [installFrames]
      rw [exhausted_frame_has_no_alternatives frame current]
      exact ih stack future

/-- With no ordinary alternatives, installation retains exactly the actual
entered job. It does not recreate the call which produced that job. -/
theorem exhausted_frontier_is_entered_only (entered : Job) (frames : List (Frame Job))
    (exhausted : ∀ frame ∈ frames, frame.equations.length ≤ frame.next) :
    install entered frames = [entered] := by
  simp [install, exhausted_frames_preserve_stack frames [] exhausted]

/-- A stale source may transfer a tail receipt only if its adapter reports
no saved caller and every ordinary frame is exhausted. -/
def staleTailAdmitted (frames : List (Frame Job)) (hasCaller : Bool) : Bool :=
  !hasCaller && frames.all (fun frame => decide (frame.equations.length ≤ frame.next))

theorem stale_tail_admission_retains_only_entered_job (entered : Job)
    (frames : List (Frame Job)) (hasCaller : Bool)
    (admitted : staleTailAdmitted frames hasCaller = true) :
    hasCaller = false ∧ install entered frames = [entered] := by
  simp [staleTailAdmitted] at admitted
  exact ⟨admitted.1, exhausted_frontier_is_entered_only entered frames admitted.2⟩

variable {Event : Type}

/-- Independent sequential semantics for executable source jobs. -/
inductive SourceRuns : List (Program Unit Event) → List Event → Prop where
  | nil : SourceRuns [] []
  | cons {job : Program Unit Event} {rest : List (Program Unit Event)}
      {first later : List Event}
      (current : Runs job first ()) (tail : SourceRuns rest later) :
      SourceRuns (job :: rest) (first ++ later)

/-- Executable work enters the shared explicit-frame driver after installation. -/
def sequence : List (Program Unit Event) → Program Unit Event
  | [] => .done ()
  | job :: rest => .child job (fun _ => sequence rest)

theorem sequence_runs {jobs : List (Program Unit Event)} {events : List Event}
    (source : SourceRuns jobs events) : Runs (sequence jobs) events () := by
  induction source with
  | nil => exact .done
  | cons current _ ih => exact .child current ih

theorem transported_jobs_refine (entered : Program Unit Event)
    (frames : List (Frame (Program Unit Event))) (events : List Event)
    (source : SourceRuns (reference entered frames) events) :
    Runs (sequence (install entered frames)) events () := by
  rw [installation_refines]
  exact sequence_runs source

theorem driver_refines (entered : Program Unit Event)
    (frames : List (Frame (Program Unit Event))) (events : List Event)
    (source : SourceRuns (reference entered frames) events) :
    ∃ allowance, advance allowance ⟨sequence (install entered frames), []⟩ =
      (events, ⟨.done (), []⟩) :=
  advance_refines_runs (transported_jobs_refine entered frames events source)

/-- A completed ordinary frontier drives the retained job with its own event
trace, even if that job records a source-authority change. -/
theorem exhausted_frontier_drives_retained_job (entered : Program Unit Event)
    (frames : List (Frame (Program Unit Event))) (events : List Event)
    (exhausted : ∀ frame ∈ frames, frame.equations.length ≤ frame.next)
    (retained : Runs entered events ()) :
    ∃ allowance, advance allowance ⟨sequence (install entered frames), []⟩ =
      (events, ⟨.done (), []⟩) := by
  rw [exhausted_frontier_is_entered_only entered frames exhausted]
  apply advance_refines_runs
  simpa [sequence] using SourceRuns.cons retained SourceRuns.nil |> sequence_runs

theorem split_keeps_actual_work {World : Type}
    (action : Event → World → World) (entered : Program Unit Event)
    (frames : List (Frame (Program Unit Event))) (world : World) (first later : Nat) :
    Session.resume action (first + later)
        (Session.begin (sequence (install entered frames)) world) =
      Session.resume action later (Session.resume action first
        (Session.begin (sequence (install entered frames)) world)) :=
  Session.resume_add action first later _

/-- Costs of the untried source frames; multiplicity within one frame does
not require another copy of its caller suffix. -/
def pendingSuffixes (frames : List (Frame Job)) (cost : Frame Job → Nat) : List Nat :=
  frames.filterMap fun frame =>
    if frame.next < frame.equations.length then some (cost frame) else none

def bounded (frames : List (Frame Job)) (cost : Frame Job → Nat) : Bool :=
  decide ((pendingSuffixes frames cost).length ≤ 1)

private theorem one_sum_le (sizes : List Nat) (bound : Nat)
    (size : sizes.length ≤ 1) (members : ∀ n ∈ sizes, n ≤ bound) : sizes.sum ≤ bound := by
  cases sizes with
  | nil => simp
  | cons n rest =>
      cases rest with
      | nil => simpa using members n (by simp)
      | cons m rest => simp at size

/-- With one unfinished frame, the work for its saved suffix is at most the
largest one-suffix cost, independently of how many equations that frame has. -/
theorem bounded_suffix_work (frames : List (Frame Job)) (cost : Frame Job → Nat)
    (maximum : Nat) (admitted : bounded frames cost = true)
    (members : ∀ n ∈ pendingSuffixes frames cost, n ≤ maximum) :
    (pendingSuffixes frames cost).sum ≤ maximum := by
  apply one_sum_le _ maximum
  · exact of_decide_eq_true admitted
  · exact members

/-- Including the already-entered caller, no more than two full suffix
reconstructions are performed by the bounded region. -/
theorem bounded_total_suffix_work (frames : List (Frame Job)) (cost : Frame Job → Nat)
    (maximum active : Nat) (admitted : bounded frames cost = true)
    (activeBound : active ≤ maximum)
    (members : ∀ n ∈ pendingSuffixes frames cost, n ≤ maximum) :
    active + (pendingSuffixes frames cost).sum ≤ 2 * maximum := by
  have h := bounded_suffix_work frames cost maximum admitted members
  omega

inductive Route (Job : Type) where
  | parent (entered : Job) (frames : List (Frame Job))
  | retained (entered : Job) (frames : List (Frame Job))

def choose (entered : Job) (frames : List (Frame Job)) (cost : Frame Job → Nat) : Route Job :=
  if bounded frames cost then .parent entered frames else .retained entered frames

/-- Refusal leaves the entered residual and every frame with their owner. -/
theorem refusal_retains_actual_frontier (entered : Job) (frames : List (Frame Job))
    (cost : Frame Job → Nat) (refused : bounded frames cost = false) :
    choose entered frames cost = .retained entered frames := by
  simp [choose, refused]

/-- When a frame remains, the current lowering accepts a short caller
chain. A completed frontier does not need this additional bound. -/
def eligible (frames : List (Frame Job)) (cost : Frame Job → Nat) (callers : Nat) : Bool :=
  bounded frames cost && decide (pendingSuffixes frames cost = [] ∨ callers ≤ 2)

theorem eligible_suffix_work (frames : List (Frame Job)) (cost : Frame Job → Nat)
    (maximum callers : Nat) (admitted : eligible frames cost callers = true)
    (members : ∀ n ∈ pendingSuffixes frames cost, n ≤ maximum) :
    (pendingSuffixes frames cost).sum ≤ maximum := by
  have both : bounded frames cost = true ∧
      (pendingSuffixes frames cost = [] ∨ callers ≤ 2) := by
    simpa [eligible] using admitted
  exact bounded_suffix_work frames cost maximum both.1 members

theorem eligible_pending_caller_limit (frames : List (Frame Job)) (cost : Frame Job → Nat)
    (callers : Nat) (admitted : eligible frames cost callers = true)
    (pending : pendingSuffixes frames cost ≠ []) : callers ≤ 2 := by
  have both : bounded frames cost = true ∧
      (pendingSuffixes frames cost = [] ∨ callers ≤ 2) := by
    simpa [eligible] using admitted
  exact both.2.resolve_left pending

theorem exhausted_frontier_has_no_caller_limit (frames : List (Frame Job))
    (cost : Frame Job → Nat) (callers : Nat) (empty : pendingSuffixes frames cost = []) :
    eligible frames cost callers = true := by
  simp [eligible, bounded, empty]

def chooseEligible (entered : Job) (frames : List (Frame Job))
    (cost : Frame Job → Nat) (callers : Nat) : Route Job :=
  if eligible frames cost callers then .parent entered frames else .retained entered frames

theorem ineligible_retains_actual_frontier (entered : Job) (frames : List (Frame Job))
    (cost : Frame Job → Nat) (callers : Nat) (refused : eligible frames cost callers = false) :
    chooseEligible entered frames cost callers = .retained entered frames := by
  simp [chooseEligible, refused]

namespace CallerSlot

/-- The current goal and the overwrite trail belonging to older choices. -/
structure Slot (Job : Type) where
  current : Job
  history : List Job

variable {Job : Type}

def write (slot : Slot Job) (caller : Job) : Slot Job :=
  ⟨caller, slot.current :: slot.history⟩

def writes : Slot Job → List Job → Slot Job
  | slot, [] => slot
  | slot, caller :: rest => writes (write slot caller) rest

def unwind : Nat → Slot Job → Slot Job
  | 0, slot => slot
  | _ + 1, ⟨current, []⟩ => ⟨current, []⟩
  | count + 1, ⟨_, previous :: rest⟩ => unwind count ⟨previous, rest⟩

def rollback (mark : Nat) (slot : Slot Job) : Slot Job :=
  unwind (slot.history.length - mark) slot

theorem unwind_add (first later : Nat) (slot : Slot Job) :
    unwind (first + later) slot = unwind later (unwind first slot) := by
  induction first generalizing slot with
  | zero => simp [unwind]
  | succ first ih =>
      rcases slot with ⟨current, history⟩
      cases history with
      | nil => cases later <;> rfl
      | cons previous rest => simpa [Nat.succ_add, unwind] using ih ⟨previous, rest⟩

theorem writes_history_length (slot : Slot Job) (later : List Job) :
    (writes slot later).history.length = slot.history.length + later.length := by
  induction later generalizing slot with
  | nil => simp [writes]
  | cons caller rest ih => simp [writes, ih, write, Nat.add_comm, Nat.add_left_comm]

theorem unwind_writes (slot : Slot Job) (later : List Job) :
    unwind later.length (writes slot later) = slot := by
  induction later generalizing slot with
  | nil => rfl
  | cons caller rest ih =>
      rw [List.length_cons, writes, unwind_add, ih]
      rfl

theorem rollback_later_writes (slot : Slot Job) (later : List Job) :
    rollback slot.history.length (writes slot later) = slot := by
  simp [rollback, writes_history_length, unwind_writes]

/-- A transferred choice owns the installed caller, after any older choice
has logged the entrance goal that occupied its slot. -/
theorem installed_checkpoint_restores_caller (entrance : Slot Job) (caller : Job)
    (later : List Job) :
    rollback (write entrance caller).history.length (writes (write entrance caller) later) =
      write entrance caller := rollback_later_writes _ _

/-- Saving the older mark instead reinstates the entrance computation. -/
theorem entrance_checkpoint_restores_entrance (entrance : Slot Job) (caller : Job) :
    rollback entrance.history.length (write entrance caller) = entrance := by
  rcases entrance with ⟨current, history⟩
  simp [rollback, write, unwind]

end CallerSlot

namespace Controls

abbrev Work := Program Unit Nat

def equation (tag : Nat) : Work := .emit tag (.done ())
def captured (tag : Nat) (job : Work) : Work := .emit tag job

def outer : Frame Work := ⟨[equation 10, equation 11, equation 11], 1, captured 100⟩
def inner : Frame Work := ⟨[equation 20, equation 21], 1, captured 200⟩
def active : Work := equation 1

theorem one_frame_may_have_duplicate_equations :
    bounded [outer] (fun _ => 100) = true := rfl

theorem two_unfinished_frames_keep_the_owned_cursor :
    choose active [outer, inner] (fun _ => 100) = .retained active [outer, inner] := rfl

theorem short_caller_with_many_equations_is_eligible :
    eligible [outer] (fun _ => 100) 2 = true := rfl

theorem longer_unshared_caller_keeps_the_cursor :
    chooseEligible active [outer] (fun _ => 100) 3 = .retained active [outer] := rfl

theorem exhausted_frontier_keeps_existing_path :
    eligible [] (fun _ : Frame Work => 100) 1000 = true := rfl

theorem native_residual_precedes_inner_then_outer :
    install active [outer, inner] =
      [active, captured 200 (equation 21),
       captured 100 (equation 11), captured 100 (equation 11)] := rfl

theorem completed_native_is_not_a_new_entrance :
    (advance 20 ⟨sequence (install active [inner]), []⟩).1 = [1, 200, 21] := rfl

theorem exhausted_native_frontier_runs_only_retained_job :
    (advance 20 ⟨sequence (install active [{inner with next := 2}]), []⟩).1 = [1] := rfl

theorem stale_tail_accepts_exhausted_caller_free_frontier :
    staleTailAdmitted [{inner with next := 2}] false = true := rfl

theorem stale_tail_refuses_saved_caller :
    staleTailAdmitted [{inner with next := 2}] true = false := rfl

theorem stale_tail_refuses_untried_equation :
    staleTailAdmitted [inner] false = false := rfl

theorem restarting_an_equation_replays_committed_work :
    (advance 30 ⟨sequence (install active [{inner with next := 0}]), []⟩).1 =
      [1, 200, 20, 200, 21] := rfl

theorem dropping_captured_caller_changes_the_trace :
    (advance 20 ⟨sequence (install active [{inner with resume := id}]), []⟩).1 = [1, 21] := rfl

theorem outer_first_installation_preserves_duplicate_occurrences :
    (advance 40 ⟨sequence (install active [outer, inner]), []⟩).1 =
      [1, 200, 21, 100, 11, 100, 11] := rfl

end Controls
end Mettapedia.Machines.PreparedFrontierTransfer
