/-!
# IterBranches — background branches, merging and shutdown

`bgoertzel-sing/iter` master (`3399366`) lets a model call that outlives a
deadline continue as a background branch. The branch thread keeps a deep copy
of the request, finishes the call, then runs up to 25 more steps, executing
each response's tool calls (at most `MAX_TOOL_CALLS`) and pushing every
assistant message and tool result to a merge queue. The main loop drains the
queue into its transcript at the top of each cycle and again before building
each request. On `SIGTERM` it waits up to five seconds, drains, saves and
exits, killing branch threads.

On master a single variable holds the active branch, and abandoning a branch
after its idle deadline only frees that variable. Branch
`agent/protocosmo2-multi-branch` (`6ea3dd6`) keeps a set of at most `M`
branches, waits in the foreground when the set is full, stops an abandoned
branch at its next step, caps concurrent model calls with a semaphore, and
binds each branch to the user request it was started from.

Results:
* `master_orphans_branch`: a second promotion on master overwrites the active
  branch; the first keeps running untracked, invisible to the deadline check
  and to shutdown. `multi_tracks_running` and `multi_bounded`: the branch set
  tracks every running branch and never exceeds `M`.
* `semaphore_bound`: the concurrency cap is an invariant of acquire/release.
* `master_abandon_leak` and `multi_abandon_leak_le`: after abandonment a master
  branch can still execute 249 tool calls; a multi-branch branch finishes only
  the step it is in, at most `MAX_TOOL_CALLS` calls. `abandoned_results_merged`:
  results pushed after abandonment still enter the transcript, although the
  abandonment marker says they were discarded.
* `interleaved_merge_breaks_protocol`: merging per message can place a branch's
  tool-call message and its results on either side of the main loop's own
  turn. The transcript then violates the chat protocol, which requires the
  results to follow their call. `wf_append` and `group_merge_preserves`:
  merging a call together with all its results keeps a well-formed
  transcript well-formed.
* `shutdown_loses_record`: a branch killed between executing a tool and queuing
  its result leaves an effect with no record. `intent_covers_effects`: when a
  durable intent precedes every execution, every executed effect in any prefix
  of the trace has its intent recorded.

A CeTTa-native runtime never abandons an owned call. Each call keeps its
owner, generation and serial (`EventPump.lean`, `AsyncWait.lean`); a late
result stays evidence while changed context blocks stale commands
(`TopicAsync.lean`). A call and its results are published in one atomic
transition (`ChannelJoin.lean`). Effects are journaled as intents before they
run, and recovery marks an intent without a result as uncertain instead of
dropping it.
-/

namespace IterBranches

/-! ## Tracking running branches -/

inductive BranchEvent
  | promote (b : Nat)
  | finish (b : Nat)
deriving Repr, DecidableEq

/-- Master: running threads, and the single active-branch variable, which a
promotion overwrites. A finishing branch clears the variable only if it is the
one recorded there. -/
def stepMaster (st : List Nat × Option Nat) : BranchEvent → List Nat × Option Nat
  | .promote b => (b :: st.1, some b)
  | .finish b => (st.1.erase b, if st.2 = some b then none else st.2)

def runMaster (st : List Nat × Option Nat) : List BranchEvent → List Nat × Option Nat
  | [] => st
  | e :: rest => runMaster (stepMaster st e) rest

/-- After two promotions the first branch still runs, but the deadline check and
the shutdown wait see only the second. When the second finishes, nothing is
tracked while the first keeps running. -/
theorem master_orphans_branch :
    runMaster ([], none) [.promote 1, .promote 2] = ([2, 1], some 2) ∧
      runMaster ([], none) [.promote 1, .promote 2, .finish 2] = ([1], none) := by
  decide

/-- Multi-branch: promote only into a free slot; otherwise the call stays in the
foreground (`none`). -/
def promoteMulti (cap : Nat) (active : List Nat) (b : Nat) : Option (List Nat) :=
  if active.length < cap then some (b :: active) else none

/-- A branch leaves the set when it completes, fails or is abandoned. -/
def finish (active : List Nat) (b : Nat) : List Nat := active.erase b

/-- Running threads and the tracked set evolve together: a promotion refused
for lack of a slot starts no thread. -/
def stepMulti (cap : Nat) (st : List Nat × List Nat) : BranchEvent → List Nat × List Nat
  | .promote b =>
      match promoteMulti cap st.2 b with
      | some active => (b :: st.1, active)
      | none => st
  | .finish b => (st.1.erase b, finish st.2 b)

def runMulti (cap : Nat) (st : List Nat × List Nat) : List BranchEvent → List Nat × List Nat
  | [] => st
  | e :: rest => runMulti cap (stepMulti cap st e) rest

theorem multi_tracks_running (cap : Nat) (events : List BranchEvent) :
    (runMulti cap ([], []) events).1 = (runMulti cap ([], []) events).2 := by
  suffices h : ∀ st : List Nat × List Nat, st.1 = st.2 →
      (runMulti cap st events).1 = (runMulti cap st events).2 from h ([], []) rfl
  induction events with
  | nil => intro st h; exact h
  | cons e rest ih =>
    intro st h
    apply ih
    cases e with
    | promote b =>
      simp only [stepMulti, promoteMulti]
      split
      · rename_i active hsome
        split at hsome
        · cases hsome; simp [h]
        · cases hsome
      · exact h
    | finish b => simp [stepMulti, finish, h]

theorem multi_bounded (cap : Nat) (events : List BranchEvent) :
    (runMulti cap ([], []) events).2.length ≤ cap := by
  suffices h : ∀ st : List Nat × List Nat, st.2.length ≤ cap →
      (runMulti cap st events).2.length ≤ cap from h ([], []) (Nat.zero_le _)
  induction events with
  | nil => intro st h; exact h
  | cons e rest ih =>
    intro st h
    apply ih
    cases e with
    | promote b =>
      simp only [stepMulti, promoteMulti]
      split
      · rename_i active hsome
        split at hsome
        · rename_i hlt
          cases hsome
          simp only [List.length_cons]
          omega
        · cases hsome
      · exact h
    | finish b =>
      simp only [stepMulti, finish]
      exact Nat.le_trans List.length_erase_le h

/-! ## The model-call semaphore -/

def acquire (limit inFlight : Nat) : Option Nat :=
  if inFlight < limit then some (inFlight + 1) else none

def release (inFlight : Nat) : Nat := inFlight - 1

theorem semaphore_bound (limit inFlight : Nat) (h : inFlight ≤ limit) :
    (∀ n, acquire limit inFlight = some n → n ≤ limit) ∧ release inFlight ≤ limit := by
  constructor
  · intro n hn
    unfold acquire at hn
    split at hn
    · cases hn; omega
    · cases hn
  · unfold release; omega

/-! ## Abandonment -/

def maxToolCalls : Nat := 10
def branchSteps : Nat := 25

/-- Tool calls a master branch still executes after it is abandoned during step
`k`, after `j` calls of that step: the rest of the step and every later step. -/
def leakMaster (steps : List Nat) (k j : Nat) : Nat := (steps.drop k).sum - j

/-- Multi-branch checks the abandonment flag before each step: only the rest of
the current step runs. -/
def leakMulti (steps : List Nat) (k j : Nat) : Nat := steps.getD k 0 - j

theorem master_abandon_leak :
    leakMaster (List.replicate branchSteps maxToolCalls) 0 1 = 249 := by
  decide

theorem multi_abandon_leak_le (steps : List Nat) (k j : Nat)
    (hstep : ∀ n ∈ steps, n ≤ maxToolCalls) : leakMulti steps k j ≤ maxToolCalls := by
  unfold leakMulti
  have : steps.getD k 0 ≤ maxToolCalls := by
    rw [List.getD_eq_getElem?_getD]
    cases h : steps[k]? with
    | none => simp [maxToolCalls]
    | some n =>
      simp only [Option.getD_some]
      exact hstep n (List.mem_of_getElem? h)
  omega

/-- The drain appends every queued entry, whether or not its branch was
abandoned in the meantime. -/
def drain (transcript queue : List Nat) : List Nat := transcript ++ queue

theorem abandoned_results_merged (transcript : List Nat) (late : Nat) :
    late ∈ drain transcript [late] := by
  simp [drain]

/-! ## Transcript protocol -/

/-- Transcript entries: a user message, an assistant message with tool calls
(from branch `b`, with call identities), and a tool result. -/
inductive Entry
  | user (n : Nat)
  | call (b : Nat) (ids : List Nat)
  | result (b : Nat) (id : Nat)
deriving Repr, DecidableEq

/-- Scan a transcript against the chat protocol, tracking the tool results
still owed (branch and call identity, in order). A user message or a new call
message may only appear when nothing is owed; a result must be the next one
owed. `none` reports a violation. -/
def scan : List (Nat × Nat) → List Entry → Option (List (Nat × Nat))
  | p, [] => some p
  | p, .user _ :: rest => if p.isEmpty then scan [] rest else none
  | p, .call b ids :: rest => if p.isEmpty then scan (ids.map (fun i => (b, i))) rest else none
  | p, .result b i :: rest =>
      match p with
      | (b', i') :: ps => if b = b' ∧ i = i' then scan ps rest else none
      | [] => none

/-- A well-formed transcript: every call's results follow it immediately, in
order, and no result appears elsewhere. -/
def wf (l : List Entry) : Bool := scan [] l == some []

/-- A branch pushes its call message, the main loop drains it and completes a
turn of its own, then the branch's result arrives. -/
theorem interleaved_merge_breaks_protocol :
    let mainTurn := [Entry.call 0 [5], Entry.result 0 5]
    let branchTurn := [Entry.call 9 [100], Entry.result 9 100]
    wf mainTurn = true ∧ wf branchTurn = true ∧
      wf ([Entry.user 1, Entry.call 9 [100]] ++ mainTurn ++ [Entry.result 9 100]) = false := by
  decide

theorem scan_append (p : List (Nat × Nat)) (xs ys : List Entry) :
    scan p (xs ++ ys) = (scan p xs).bind (fun q => scan q ys) := by
  induction xs generalizing p with
  | nil => rfl
  | cons x rest ih =>
    cases x with
    | user n =>
      simp only [List.cons_append, scan]
      split <;> simp [ih]
    | call b ids =>
      simp only [List.cons_append, scan]
      split <;> simp [ih]
    | result b i =>
      cases p with
      | nil => simp [scan]
      | cons q ps =>
        obtain ⟨b', i'⟩ := q
        simp only [List.cons_append, scan]
        split <;> simp [ih]

theorem wf_append (xs ys : List Entry) (hx : wf xs = true) (hy : wf ys = true) :
    wf (xs ++ ys) = true := by
  simp only [wf, beq_iff_eq] at hx hy ⊢
  rw [scan_append, hx]
  exact hy

theorem scan_results (b : Nat) (ids : List Nat) :
    scan (ids.map (fun i => (b, i))) (ids.map (Entry.result b)) = some [] := by
  induction ids with
  | nil => rfl
  | cons i rest ih => simp [scan, ih]

/-- Merging a branch's call message together with all its results keeps a
well-formed transcript well-formed. -/
theorem group_merge_preserves (transcript : List Entry) (b : Nat) (ids : List Nat)
    (h : wf transcript = true) :
    wf (transcript ++ (Entry.call b ids :: ids.map (Entry.result b))) = true := by
  apply wf_append _ _ h
  simp [wf, scan, scan_results]

/-! ## Shutdown -/

/-- What a branch thread does with one tool call. -/
inductive Act
  | intent (e : Nat)
  | exec (e : Nat)
  | push (e : Nat)
deriving Repr, DecidableEq

/-- Upstream: execute, then queue the result. A kill after `exec` leaves the
effect without a record. -/
theorem shutdown_loses_record :
    let trace := [Act.exec 1, Act.push 1, Act.exec 2, Act.push 2]
    let beforeKill := trace.take 3
    Act.exec 2 ∈ beforeKill ∧ Act.push 2 ∉ beforeKill := by
  decide

/-- Journal the intent durably, then execute, then record the result. -/
def block (e : Nat) : List Act := [Act.intent e, Act.exec e, Act.push e]

theorem intent_covers_effects (es : List Nat) (k e : Nat)
    (h : Act.exec e ∈ ((es.map block).flatten).take k) :
    Act.intent e ∈ ((es.map block).flatten).take k := by
  induction es generalizing k with
  | nil => simp at h
  | cons x rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.take_append] at h ⊢
    rcases List.mem_append.mp h with h1 | h2
    · apply List.mem_append_left
      simp only [block] at h1 ⊢
      match k, h1 with
      | 0, h1 => simp at h1
      | 1, h1 => simp at h1
      | k + 2, h1 =>
        simp only [List.take_succ_cons, List.mem_cons] at h1 ⊢
        rcases h1 with h1 | h1 | h1
        · cases h1
        · cases h1; left; rfl
        · cases k with
          | zero => simp at h1
          | succ k => simp at h1
    · apply List.mem_append_right
      exact ih _ h2

end IterBranches

/-! ## Axiom audit -/
#print axioms IterBranches.master_orphans_branch
#print axioms IterBranches.multi_tracks_running
#print axioms IterBranches.multi_bounded
#print axioms IterBranches.semaphore_bound
#print axioms IterBranches.master_abandon_leak
#print axioms IterBranches.multi_abandon_leak_le
#print axioms IterBranches.abandoned_results_merged
#print axioms IterBranches.interleaved_merge_breaks_protocol
#print axioms IterBranches.wf_append
#print axioms IterBranches.group_merge_preserves
#print axioms IterBranches.shutdown_loses_record
#print axioms IterBranches.intent_covers_effects
