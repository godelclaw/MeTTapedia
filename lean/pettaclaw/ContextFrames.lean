/-!
# ContextFrames — per-task frames, modes and priority selection

`singnet/Omega` pull request #284 (head `a72837e`, open) makes Context Frames the
loop's working state. Every new user message becomes a `UserDirective` frame
with priority `1.0` in `Fast` mode; autonomous work runs in `AgentDirective`
frames, by default priority `0.5` in `Slow` mode. The root frame has a mode,
and a frame can be loaded only when its mode equals the root mode. When no
frame is current, the next one is the active frame of highest priority in the
root mode, the earliest on ties. A frame stays active until the model calls a
completion skill. The prompt contains the current frame, including its history
summary, and each frame note appends `| kind : summary` to that summary. A note
is compacted to at most 1200 characters; the summary itself has no bound.

Results:
* `completed_never_selected` and `selected_matches_mode`: completed frames are
  never selected again, and a selected frame has the root mode. This is what
  stops completed requests from being repeated.
* `lower_priority_starves`: while a higher-priority frame stays active, a
  lower-priority frame of the same mode is never selected, however many cycles
  pass.
* `older_user_frame_wins`: user frames share one priority, so the oldest active
  one is selected and later user requests wait until the model completes it.
* `user_input_preempts_slow_work` and `user_input_waits_behind_user_work`: a
  user message preempts autonomous work in `Slow` mode, but not an earlier user
  frame in `Fast` mode.
* `history_summary_unbounded`: `n` notes add at least `4 n` characters to the
  history summary in the prompt, for every per-note bound.

Frames solve request lifecycle tracking: completed work is not repeated and
user work precedes autonomous work. Liveness rests on the model: nothing
bounds how long a frame waits. In CeTTa frames correspond to topics with owned
requests (`TopicAsync.lean`) scheduled by weighted service
(`FairGoalScheduling.lean`), which bounds the waiting of every active topic
with a positive share. The frame's history is a bounded window over its own
journal (`ContextWindow.lean`); completion is an atom in the request ledger.
-/

namespace ContextFrames

inductive Mode
  | fast
  | slow
deriving Repr, DecidableEq

inductive Status
  | active
  | completed
deriving Repr, DecidableEq

/-- A frame reference in the index: identity, priority (tenths), mode and
status. -/
structure Frame where
  id : Nat
  priority : Nat
  mode : Mode
  status : Status
deriving Repr, DecidableEq

/-- `cfv2_select_next_frame_id`: the first frame of maximal priority among the
active frames in the root mode. -/
def best : List Frame → Option Frame
  | [] => none
  | f :: rest =>
      match best rest with
      | none => some f
      | some g => if f.priority < g.priority then some g else some f

def select (frames : List Frame) (root : Mode) : Option Frame :=
  best (frames.filter (fun f => f.status == .active && f.mode == root))

theorem best_mem : ∀ (fs : List Frame) (f : Frame), best fs = some f → f ∈ fs
  | [], f, h => by simp [best] at h
  | g :: rest, f, h => by
    simp only [best] at h
    split at h
    · cases h; simp
    · rename_i g' hg'
      split at h
      · cases h; exact List.mem_cons_of_mem _ (best_mem rest f hg')
      · cases h; simp

theorem completed_never_selected (frames : List Frame) (root : Mode) (f : Frame)
    (h : select frames root = some f) : f.status = .active := by
  have hm := best_mem _ _ h
  simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hm
  exact hm.2.1

theorem selected_matches_mode (frames : List Frame) (root : Mode) (f : Frame)
    (h : select frames root = some f) : f.mode = root := by
  have hm := best_mem _ _ h
  simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hm
  exact hm.2.2

def hi : Frame := ⟨1, 10, .fast, .active⟩
def lo : Frame := ⟨2, 5, .fast, .active⟩

/-- Selection is a function of the frame index, which changes only when the model
completes or creates a frame. While `hi` stays active, `lo` is never chosen. -/
theorem lower_priority_starves (cycles : Nat) :
    (List.replicate cycles (select [hi, lo] .fast)).all (· = some hi) = true := by
  induction cycles with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.all_cons, ih, Bool.and_true]
    decide

def olderUser : Frame := ⟨3, 10, .fast, .active⟩
def newerUser : Frame := ⟨4, 10, .fast, .active⟩

theorem older_user_frame_wins : select [olderUser, newerUser] .fast = some olderUser := by
  decide

/-- Root mode and the current frame. -/
structure Root where
  mode : Mode
  current : Option Nat
deriving Repr, DecidableEq

/-- `cfv2-create-frame` for a user message: in `Slow` mode switch to `Fast` and
load the new frame; in `Fast` mode only index it. -/
def admitUser (r : Root) (id : Nat) : Root :=
  match r.mode with
  | .slow => ⟨.fast, some id⟩
  | .fast => if r.current.isNone then ⟨.fast, some id⟩ else r

theorem user_input_preempts_slow_work :
    admitUser ⟨.slow, some 7⟩ 8 = ⟨.fast, some 8⟩ := by
  decide

theorem user_input_waits_behind_user_work :
    admitUser ⟨.fast, some 3⟩ 4 = ⟨.fast, some 3⟩ := by
  decide

/-- `cfv2-update-current-history-summary`: append ` | kind : summary`, with a
note of length `len` (at least four characters of separators). -/
def appendNote (summary len : Nat) : Nat := summary + 4 + len

theorem history_summary_unbounded (summary : Nat) (notes : List Nat) :
    summary + 4 * notes.length ≤ notes.foldl appendNote summary := by
  induction notes generalizing summary with
  | nil => simp
  | cons n rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (appendNote summary n)
    have h2 : appendNote summary n = summary + 4 + n := rfl
    omega

end ContextFrames

/-! ## Axiom audit -/
#print axioms ContextFrames.best_mem
#print axioms ContextFrames.completed_never_selected
#print axioms ContextFrames.selected_matches_mode
#print axioms ContextFrames.lower_priority_starves
#print axioms ContextFrames.older_user_frame_wins
#print axioms ContextFrames.user_input_preempts_slow_work
#print axioms ContextFrames.user_input_waits_behind_user_work
#print axioms ContextFrames.history_summary_unbounded
