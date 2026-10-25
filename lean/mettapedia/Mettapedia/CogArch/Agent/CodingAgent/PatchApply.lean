import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Applying a multi-file patch

Coding agents edit files with patches: a list of operations, each adding,
deleting or updating one file, where an update locates its hunks by matching
lines. Two implementations of the same patch format share a two-phase design:
every operation is computed against the files as they are (verification), and
only then are the files written one after another (application). Three
questions decide whether this design does what its users expect.

* **Does verification predict application?** Verification computes every
  result from one snapshot; application writes in order. They agree exactly
  when no two operations target the same path (`plan_commit_eq_seq`). With a
  repeated target, the snapshot plan silently drops the earlier update
  (`snapshot_loses_update`), so the duplicate check that one implementation
  performs during verification is necessary, not cosmetic.
* **Is a patch all or nothing?** Not when files are written one after another:
  an I/O error on the second write leaves the first applied
  (`direct_partial`), even if each single write is atomic. Staging every new
  content under a fresh name first, and renaming only after all staging has
  succeeded, makes the visible files either unchanged or fully patched for
  every staging failure (`staged_all_or_nothing`). The renames themselves are
  assumed not to fail; a crash in the middle of them is outside this model.
* **Does an edit land where it was meant?** A hunk is meant for an occurrence
  of its lines in the file. Taking the first match from a cursor applies an
  ambiguous hunk at one occurrence chosen by position (`firstMatch_ambiguous`).
  Trying looser matchers and accepting the first candidate whose text is
  unique can land the edit on a line that is not an exact occurrence at all,
  although exact occurrences exist (`spanCascade_leaves_exact`). Deciding with
  the first matcher that finds anything, and applying only a unique match,
  never does either (`safeCascade_exact`), and still applies every hunk whose
  exact match is unique (`safeCascade_complete`).

A matcher is a normalisation of lines: exact matching is the identity, and
looser passes compare lines after trimming or after mapping typographic
punctuation to ASCII.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.Agent.CodingAgent.PatchApply

universe u v w

/-! ## Files and operations -/

/-- A file system state: each path is absent (`none`) or holds content. -/
abbrev FS (Path : Type u) (Content : Type v) := Path → Option Content

/-- One operation of a patch: its target and a partial transformer of the
target's state. The transformer fails when the operation does not apply, for
example when a deleted file is missing or a hunk does not match. A move is two
operations: a write of the destination and a removal of the source. -/
structure Op (Path : Type u) (Content : Type v) where
  path : Path
  step : Option Content → Option (Option Content)

variable {Path : Type u} [DecidableEq Path] {Content : Type v}

/-- Write one path; `none` removes it. -/
def write (fs : FS Path Content) (p : Path) (c : Option Content) : FS Path Content :=
  Function.update fs p c

/-- Verification: compute every operation's result against the snapshot `fs`.
It fails if any operation fails, and then nothing is written. -/
def plan (fs : FS Path Content) : List (Op Path Content) → Option (List (Path × Option Content))
  | [] => some []
  | op :: ops =>
    match op.step (fs op.path), plan fs ops with
    | some c, some rest => some ((op.path, c) :: rest)
    | _, _ => none

/-- Write planned results in order. -/
def commit (fs : FS Path Content) : List (Path × Option Content) → FS Path Content
  | [] => fs
  | (p, c) :: ws => commit (write fs p c) ws

/-- Sequential application: each operation sees the results of the earlier
ones. -/
def seq (fs : FS Path Content) : List (Op Path Content) → Option (FS Path Content)
  | [] => some fs
  | op :: ops =>
    match op.step (fs op.path) with
    | some c => seq (write fs op.path c) ops
    | none => none

/-! ## Verification predicts application exactly for distinct targets -/

omit [DecidableEq Path] in
/-- A plan reads only its operations' targets. -/
theorem plan_congr (ops : List (Op Path Content)) (fs fs' : FS Path Content)
    (h : ∀ o ∈ ops, fs o.path = fs' o.path) : plan fs ops = plan fs' ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    have hop : fs op.path = fs' op.path := h op (by simp)
    have hrest : plan fs ops = plan fs' ops := ih (fun o ho => h o (by simp [ho]))
    simp only [plan, hop, hrest]

/-- With pairwise distinct targets, writing the snapshot plan gives exactly the
result of sequential application, and both fail together. -/
theorem plan_commit_eq_seq (ops : List (Op Path Content)) (fs : FS Path Content)
    (hd : (ops.map Op.path).Nodup) : (plan fs ops).map (commit fs) = seq fs ops := by
  induction ops generalizing fs with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hd
    obtain ⟨hnot, hd⟩ := hd
    cases hstep : op.step (fs op.path) with
    | none => simp [plan, seq, hstep]
    | some c =>
      have hsame : plan fs ops = plan (write fs op.path c) ops := by
        apply plan_congr
        intro o ho
        have hne : o.path ≠ op.path := fun heq => hnot ⟨o, ho, heq⟩
        simp [write, Function.update_of_ne hne]
      have hseq := ih (write fs op.path c) hd
      simp only [seq, hstep]
      rw [← hseq, ← hsame]
      cases hp : plan fs ops with
      | none => simp [plan, hstep, hp]
      | some rest => simp [plan, hstep, hp, commit]

/-- Two updates of one file: the snapshot plan computes both from the original
content, so the second write overwrites the first update, while sequential
application keeps both. -/
theorem snapshot_loses_update :
    let fs : FS Unit ℕ := fun _ => some 0
    let bump : Op Unit ℕ := ⟨(), fun c => some (c.map (· + 1))⟩
    ((plan fs [bump, bump]).map (commit fs)).map (· ()) = some (some 1) ∧
      (seq fs [bump, bump]).map (· ()) = some (some 2) := by
  simp [plan, commit, seq, write]

/-! ## All or nothing -/

/-- Writing planned results in order when the write with index `k` fails: the
earlier writes stay applied and the later ones never happen. Atomic single
writes do not change this, because the failure falls between files. -/
def commitUntil (fs : FS Path Content) (ws : List (Path × Option Content)) (k : ℕ) :
    FS Path Content :=
  commit fs (ws.take k)

/-- A failure on the second of two writes leaves a state that is neither the
original nor the patched one. -/
theorem direct_partial :
    let fs : FS Bool ℕ := fun _ => some 0
    let ws : List (Bool × Option ℕ) := [(false, some 1), (true, some 1)]
    commitUntil fs ws 1 ≠ fs ∧ commitUntil fs ws 1 ≠ commit fs ws := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrFun h false
    simp [commitUntil, commit, write] at this
  · have := congrFun h true
    simp [commitUntil, commit, write] at this

/-- Staged application over a file system with a separate namespace of fresh
names (`Sum.inr i` holds the `i`-th staged content). Staging writes fresh
names only; if staging fails at index `k < ws.length`, the staged names are
removed; otherwise every planned result is renamed into place. -/
def stagedApply (fs : FS Path Content) (ws : List (Path × Option Content)) (k : ℕ) :
    FS (Path ⊕ ℕ) Content :=
  let disk : FS (Path ⊕ ℕ) Content := fun
    | Sum.inl p => fs p
    | Sum.inr _ => none
  if k < ws.length then disk
  else fun
    | Sum.inl p => commit fs ws p
    | Sum.inr _ => none

/-- The files a reader sees: the original namespace. -/
def visible (disk : FS (Path ⊕ ℕ) Content) : FS Path Content := fun p => disk (Sum.inl p)

/-- **All or nothing.** For every staging failure, the visible files are
unchanged; when staging completes, they are exactly the patched files, and no
staged name is left behind. -/
theorem staged_all_or_nothing (fs : FS Path Content) (ws : List (Path × Option Content))
    (k : ℕ) :
    (k < ws.length → visible (stagedApply fs ws k) = fs) ∧
      (ws.length ≤ k → visible (stagedApply fs ws k) = commit fs ws) ∧
      (∀ i, stagedApply fs ws k (Sum.inr i) = none) := by
  refine ⟨fun hk => ?_, fun hk => ?_, fun i => ?_⟩
  · funext p; simp [visible, stagedApply, hk]
  · funext p; simp [visible, stagedApply, Nat.not_lt.mpr hk]
  · unfold stagedApply; split <;> rfl

/-! ## Where an edit lands -/

section Matching

variable {α : Type w} [DecidableEq α]

/-- Whether `pat` occurs at line `i` of `file` after normalising both sides. -/
def matchesAt (norm : α → α) (file pat : List α) (i : ℕ) : Bool :=
  decide (((file.drop i).take pat.length).map norm = pat.map norm)

/-- The lines at or after `start` where `pat` occurs under `norm`, in order. -/
def occ (norm : α → α) (file pat : List α) (start : ℕ) : List ℕ :=
  (List.range (file.length + 1)).filter (fun i => decide (start ≤ i) && matchesAt norm file pat i)

/-- The text a match at line `i` covers. -/
def span (file pat : List α) (i : ℕ) : List α := (file.drop i).take pat.length

/-- First match from the cursor, as both implementations seek a hunk. -/
def firstMatch (norm : α → α) (file pat : List α) (start : ℕ) : Option ℕ :=
  (occ norm file pat start).head?

/-- A cascade that tries every candidate of every matcher in order and applies
the first one whose covered text occurs exactly once in the file. -/
def spanCascade (norms : List (α → α)) (file pat : List α) : Option ℕ :=
  (norms.flatMap (fun n => occ n file pat 0)).find?
    (fun i => decide (occ id file (span file pat i) 0 = [i]))

/-- The first matcher that finds anything decides, and only a unique match is
applied. -/
def safeCascade (norms : List (α → α)) (file pat : List α) (start : ℕ) : Option ℕ :=
  match (norms.map (fun n => occ n file pat start)).find? (fun m => !m.isEmpty) with
  | some [i] => some i
  | _ => none

/-- With exact matching first: whenever the hunk occurs exactly, the safe
cascade applies only at the unique exact occurrence. -/
theorem safeCascade_exact (rest : List (α → α)) (file pat : List α) (start i : ℕ)
    (hex : occ id file pat start ≠ [])
    (h : safeCascade (id :: rest) file pat start = some i) :
    occ id file pat start = [i] := by
  have hne : (!(occ id file pat start).isEmpty) = true := by
    simpa [List.isEmpty_iff] using hex
  unfold safeCascade at h
  rw [List.map_cons, List.find?_cons_of_pos (p := fun m : List ℕ => !m.isEmpty) hne] at h
  generalize occ id file pat start = m at h ⊢
  rcases m with _ | ⟨j, _ | ⟨k, t⟩⟩
  · simp at h
  · simp only [Option.some.injEq] at h
    rw [h]
  · simp at h

/-- The safe cascade applies every hunk whose exact match is unique, at that
match. -/
theorem safeCascade_complete (rest : List (α → α)) (file pat : List α) (start i : ℕ)
    (h : occ id file pat start = [i]) :
    safeCascade (id :: rest) file pat start = some i := by
  unfold safeCascade
  rw [List.map_cons, h]
  simp

/-- Two kinds of line for the counterexamples: `plain` and the same line with
different indentation, which trimming identifies with it. -/
inductive Line where
  | plain
  | indented
  deriving DecidableEq

/-- Trimming: an indented line normalises to the plain one. -/
def trim : Line → Line
  | Line.plain => Line.plain
  | Line.indented => Line.plain

/-- First match applies an ambiguous hunk: the line occurs twice, and the edit
lands on the first occurrence whichever was meant. -/
theorem firstMatch_ambiguous :
    occ id [Line.plain, Line.plain] [Line.plain] 0 = [0, 1] ∧
      firstMatch id [Line.plain, Line.plain] [Line.plain] 0 = some 0 := by
  decide

/-- The per-candidate cascade leaves the exact occurrences: the hunk's line
occurs exactly twice, so both exact candidates are ambiguous, and trimming
then offers the indented line, whose own text is unique. The edit lands on
line 2, which is not an exact occurrence. The safe cascade refuses. -/
theorem spanCascade_leaves_exact :
    let file := [Line.plain, Line.plain, Line.indented]
    occ id file [Line.plain] 0 = [0, 1] ∧
      spanCascade [id, trim] file [Line.plain] = some 2 ∧
      safeCascade [id, trim] file [Line.plain] 0 = none := by
  decide

end Matching

end Mettapedia.CogArch.Agent.CodingAgent.PatchApply
