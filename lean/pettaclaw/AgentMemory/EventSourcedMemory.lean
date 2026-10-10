import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Function.Iterate

/-!
# Event-sourced memory operations and a draining consolidation queue

Mem0 (arXiv 2504.19413) consolidates memory in two phases. An LLM extracts
candidate facts from new messages. For each candidate it retrieves similar
memories and chooses one command: `ADD`, `UPDATE`, `DELETE` or `NOOP`. In the
paper, `DELETE` removes the memory and `UPDATE` overwrites it under the same
identifier.

This file keeps the four commands but changes their effect on storage. The store
is a fold over an append-only operation log. Each record keeps its full version
history, and a deletion appends a tombstone. Each operation carries an
idempotency key, so a retried delivery has no further effect. Each candidate
waits in a queue with a bounded deferral budget.

Store laws:
* `replay_append`: replaying a log equals replaying its tail from a snapshot.
* `apply_noop_history`, `apply_delete`, `apply_update`, `apply_add`: command
  effects. A deletion leaves a tombstone, and the old content stays in history.
  An update keeps the identifier and advances the revision by one.
* `add_never_reuses`: a used identifier, even a deleted one, cannot be added
  again.
* `apply_history_suffix`, `replay_history_suffix`: history is never lost.
* `execH_comm`, `apply_comm`: operations on distinct records commute.
* `apply_idempotent`, `replay_eq_replay_firstDeliveries` and `replay_retry`:
  a log with arbitrary retried deliveries replays to the same store as the log
  of first deliveries.
* `apply_history_of_ne`, `total_revisions_le` (quantitative): an operation
  writes at most one version, to its own record.

Queue laws:
* `drains` (liveness): for every decision oracle, including one that always
  defers, the queue is empty after at most `work` steps.
* `resolved_perm` and `nextOp_after_drain`: every candidate is resolved exactly
  once and consumes exactly one operation identity.
* `commit_takes_effect`: a committed decision is never discarded as a retry.
* `unbudgeted_never_drains`: without a deferral budget, an oracle that always
  defers keeps the queue nonempty forever.
-/

set_option autoImplicit false

namespace AgentMemory.EventLog

/-! ## Commands, operations and records -/

/-- The memory commands of Mem0's update phase. -/
inductive Cmd (Id C : Type) where
  | add (id : Id) (content : C)
  | update (id : Id) (content : C)
  | delete (id : Id)
  | noop
  deriving DecidableEq, Repr

/-- The record a command writes to, if any. -/
def Cmd.target {Id C : Type} : Cmd Id C → Option Id
  | .add id _ => some id
  | .update id _ => some id
  | .delete id => some id
  | .noop => none

/-- An operation is a command with an idempotency key. -/
structure Op (Id C : Type) where
  opId : ℕ
  cmd : Cmd Id C
  deriving DecidableEq, Repr

/-- One revision of a record. Content `none` is a tombstone. The revision cites
the operation that wrote it. -/
structure Version (C : Type) where
  content : Option C
  opId : ℕ
  deriving DecidableEq, Repr

/-- The store derived from a log: the version history of every record, newest
first, and the identities of the operations already decided. -/
@[ext]
structure Store (Id C : Type) where
  history : Id → List (Version C)
  applied : Finset ℕ

variable {Id C : Type}

def Store.empty : Store Id C := ⟨fun _ => [], ∅⟩

/-- The content of the newest revision. -/
def headContent : List (Version C) → Option C
  | [] => none
  | v :: _ => v.content

/-- The active view: the current content of a record, absent when the record was
never added or has been deleted. -/
def active (s : Store Id C) (id : Id) : Option C := headContent (s.history id)

/-- The revision number of a record is the length of its history. -/
def revision (s : Store Id C) (id : Id) : ℕ := (s.history id).length

/-- The version an operation writes, decided from its target's history alone. -/
def plan (h : List (Version C)) (o : Op Id C) : Option (Version C) :=
  match o.cmd with
  | .add _ c => if h.isEmpty then some ⟨some c, o.opId⟩ else none
  | .update _ c => if (headContent h).isSome then some ⟨some c, o.opId⟩ else none
  | .delete _ => if (headContent h).isSome then some ⟨none, o.opId⟩ else none
  | .noop => none

/-- The transition of one record's history. -/
def stepRecord (h : List (Version C)) (o : Op Id C) : List (Version C) :=
  match plan h o with
  | none => h
  | some v => v :: h

theorem stepRecord_suffix (h : List (Version C)) (o : Op Id C) : h <:+ stepRecord h o := by
  unfold stepRecord
  split
  · exact List.suffix_refl h
  · exact List.suffix_cons _ h

theorem length_stepRecord_le (h : List (Version C)) (o : Op Id C) :
    (stepRecord h o).length ≤ h.length + 1 := by
  unfold stepRecord
  split <;> simp

variable [DecidableEq Id]

/-- An operation transforms only the history of its own target. -/
def execH (h : Id → List (Version C)) (o : Op Id C) : Id → List (Version C) :=
  fun y => if o.cmd.target = some y then stepRecord (h y) o else h y

/-- Apply an operation once. An operation whose identity was already decided is
ignored, so a retried delivery has no further effect. -/
def apply (s : Store Id C) (o : Op Id C) : Store Id C :=
  if o.opId ∈ s.applied then s else ⟨execH s.history o, insert o.opId s.applied⟩

/-- The store is a fold over the log. -/
def replay (s : Store Id C) (log : List (Op Id C)) : Store Id C := log.foldl apply s

/-! ## Replay -/

theorem replay_nil (s : Store Id C) : replay s [] = s := rfl

theorem replay_cons (s : Store Id C) (o : Op Id C) (l : List (Op Id C)) :
    replay s (o :: l) = replay (apply s o) l := rfl

/-- Replaying a log equals replaying its tail from a snapshot of its prefix.
Recovery therefore costs one step per operation after the snapshot. -/
theorem replay_append (s : Store Id C) (l₁ l₂ : List (Op Id C)) :
    replay s (l₁ ++ l₂) = replay (replay s l₁) l₂ :=
  List.foldl_append

/-! ## Command effects -/

theorem apply_of_mem {s : Store Id C} {o : Op Id C} (h : o.opId ∈ s.applied) :
    apply s o = s := by
  simp [apply, h]

theorem apply_of_not_mem {s : Store Id C} {o : Op Id C} (h : o.opId ∉ s.applied) :
    apply s o = ⟨execH s.history o, insert o.opId s.applied⟩ := by
  simp [apply, h]

theorem apply_history_of_ne (s : Store Id C) (o : Op Id C) {y : Id}
    (hy : o.cmd.target ≠ some y) : (apply s o).history y = s.history y := by
  unfold apply
  split_ifs
  · rfl
  · simp [execH, hy]

/-- A `NOOP` changes no record. It only records that its decision was made. -/
theorem apply_noop_history (s : Store Id C) (i : ℕ) :
    (apply s ⟨i, .noop⟩).history = s.history := by
  funext y
  exact apply_history_of_ne s _ (by simp [Cmd.target])

/-- A deletion appends a tombstone. The record leaves the active view, its
revision advances and the old content stays in its history. -/
theorem apply_delete {s : Store Id C} {id : Id} {c : C} {i : ℕ} (hi : i ∉ s.applied)
    (hc : active s id = some c) :
    (apply s ⟨i, .delete id⟩).history id = ⟨none, i⟩ :: s.history id ∧
      active (apply s ⟨i, .delete id⟩) id = none ∧
      revision (apply s ⟨i, .delete id⟩) id = revision s id + 1 ∧
      ∃ j, (⟨some c, j⟩ : Version C) ∈ (apply s ⟨i, .delete id⟩).history id := by
  have hh : (apply s ⟨i, .delete id⟩).history id = ⟨none, i⟩ :: s.history id := by
    rw [apply_of_not_mem hi]
    simp [execH, Cmd.target, stepRecord, plan, show (headContent (s.history id)).isSome from by
      unfold active at hc; simp [hc]]
  refine ⟨hh, by simp [active, hh, headContent], by simp [revision, hh], ?_⟩
  unfold active at hc
  cases h : s.history id with
  | nil => simp [h, headContent] at hc
  | cons v rest =>
    rw [h, headContent] at hc
    exact ⟨v.opId, by rw [hh, h]; simp [← hc]⟩

/-- An update keeps the identifier, replaces the active content and advances the
revision by one. The old version stays in the history. -/
theorem apply_update {s : Store Id C} {id : Id} {c c' : C} {i : ℕ} (hi : i ∉ s.applied)
    (hc : active s id = some c) :
    (apply s ⟨i, .update id c'⟩).history id = ⟨some c', i⟩ :: s.history id ∧
      active (apply s ⟨i, .update id c'⟩) id = some c' ∧
      revision (apply s ⟨i, .update id c'⟩) id = revision s id + 1 := by
  have hh : (apply s ⟨i, .update id c'⟩).history id = ⟨some c', i⟩ :: s.history id := by
    rw [apply_of_not_mem hi]
    simp [execH, Cmd.target, stepRecord, plan, show (headContent (s.history id)).isSome from by
      unfold active at hc; simp [hc]]
  exact ⟨hh, by simp [active, hh, headContent], by simp [revision, hh]⟩

/-- An addition creates a record with a fresh identifier. -/
theorem apply_add {s : Store Id C} {id : Id} {c : C} {i : ℕ} (hi : i ∉ s.applied)
    (hfresh : s.history id = []) :
    (apply s ⟨i, .add id c⟩).history id = [⟨some c, i⟩] ∧
      active (apply s ⟨i, .add id c⟩) id = some c := by
  have hh : (apply s ⟨i, .add id c⟩).history id = [⟨some c, i⟩] := by
    rw [apply_of_not_mem hi]
    simp [execH, Cmd.target, stepRecord, plan, hfresh]
  exact ⟨hh, by simp [active, hh, headContent]⟩

/-- Identifiers are never reused. Once a record has any history, even only a
tombstone after deletion, an addition under its identifier changes nothing. -/
theorem add_never_reuses (s : Store Id C) {id : Id} (c : C) (i : ℕ)
    (hused : s.history id ≠ []) : (apply s ⟨i, .add id c⟩).history = s.history := by
  unfold apply
  split_ifs
  · rfl
  · funext y
    by_cases hy : id = y
    · subst hy
      cases h : s.history id with
      | nil => exact absurd h hused
      | cons v rest => simp [execH, Cmd.target, stepRecord, plan, h]
    · simp [execH, Cmd.target, hy]

/-- Updating or deleting a record that is not active writes nothing. -/
theorem apply_inactive {s : Store Id C} {id : Id} (hid : active s id = none) (i : ℕ)
    (cmd : Cmd Id C) (hcmd : cmd = .delete id ∨ ∃ c, cmd = .update id c) :
    (apply s ⟨i, cmd⟩).history = s.history := by
  unfold apply
  split_ifs
  · rfl
  · funext y
    unfold active at hid
    rcases hcmd with rfl | ⟨c, rfl⟩ <;>
      by_cases hy : id = y <;> simp_all [execH, Cmd.target, stepRecord, plan]

/-! ## History is never lost -/

theorem apply_history_suffix (s : Store Id C) (o : Op Id C) (y : Id) :
    s.history y <:+ (apply s o).history y := by
  unfold apply
  split_ifs
  · exact List.suffix_refl _
  · simp only [execH]
    split_ifs
    · exact stepRecord_suffix _ _
    · exact List.suffix_refl _

theorem replay_history_suffix (s : Store Id C) (l : List (Op Id C)) (y : Id) :
    s.history y <:+ (replay s l).history y := by
  induction l generalizing s with
  | nil => exact List.suffix_refl _
  | cons o l ih => exact (apply_history_suffix s o y).trans (ih (apply s o))

/-! ## Commutation -/

/-- Operations on distinct records commute on histories. -/
theorem execH_comm (h : Id → List (Version C)) (o₁ o₂ : Op Id C)
    (hd : ∀ y, o₁.cmd.target = some y → o₂.cmd.target ≠ some y) :
    execH (execH h o₁) o₂ = execH (execH h o₂) o₁ := by
  funext y
  by_cases h₁ : o₁.cmd.target = some y <;> by_cases h₂ : o₂.cmd.target = some y
  · exact absurd h₂ (hd y h₁)
  · simp [execH, h₁, h₂]
  · simp [execH, h₁, h₂]
  · simp [execH, h₁, h₂]

/-- Operations on distinct records with distinct identities commute. -/
theorem apply_comm (s : Store Id C) (o₁ o₂ : Op Id C) (hid : o₁.opId ≠ o₂.opId)
    (hd : ∀ y, o₁.cmd.target = some y → o₂.cmd.target ≠ some y) :
    apply (apply s o₁) o₂ = apply (apply s o₂) o₁ := by
  by_cases m₁ : o₁.opId ∈ s.applied <;> by_cases m₂ : o₂.opId ∈ s.applied
  · simp [apply, m₁, m₂]
  · simp [apply, m₁, m₂]
  · simp [apply, m₁, m₂]
  · have n₂ : o₂.opId ∉ insert o₁.opId s.applied := by simp [m₂, Ne.symm hid]
    have n₁ : o₁.opId ∉ insert o₂.opId s.applied := by simp [m₁, hid]
    simp only [apply, m₁, m₂, if_false, n₁, n₂]
    rw [execH_comm _ _ _ hd, Finset.insert_comm]

/-! ## Exactly once under retries -/

theorem mem_applied_apply (s : Store Id C) (o : Op Id C) : o.opId ∈ (apply s o).applied := by
  unfold apply
  split_ifs with h
  · exact h
  · exact Finset.mem_insert_self _ _

theorem applied_subset_apply (s : Store Id C) (o : Op Id C) :
    s.applied ⊆ (apply s o).applied := by
  unfold apply
  split_ifs
  · exact subset_rfl
  · exact Finset.subset_insert _ _

theorem applied_subset_replay (s : Store Id C) (l : List (Op Id C)) :
    s.applied ⊆ (replay s l).applied := by
  induction l generalizing s with
  | nil => exact subset_rfl
  | cons o l ih => exact (applied_subset_apply s o).trans (ih (apply s o))

theorem mem_applied_replay (s : Store Id C) {l : List (Op Id C)} {o : Op Id C} (h : o ∈ l) :
    o.opId ∈ (replay s l).applied := by
  induction l generalizing s with
  | nil => simp at h
  | cons x l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact applied_subset_replay _ l (mem_applied_apply s o)
    · exact ih (apply s x) h

/-- Applying an operation twice has the effect of applying it once. -/
theorem apply_idempotent (s : Store Id C) (o : Op Id C) : apply (apply s o) o = apply s o :=
  apply_of_mem (mem_applied_apply s o)

/-- The first delivery of each operation identity not yet decided. -/
def firstDeliveries : Finset ℕ → List (Op Id C) → List (Op Id C)
  | _, [] => []
  | seen, o :: l =>
    if o.opId ∈ seen then firstDeliveries seen l
    else o :: firstDeliveries (insert o.opId seen) l

/-- Exactly once: replaying a log with any retried deliveries gives the same
store as replaying only the first deliveries. -/
theorem replay_eq_replay_firstDeliveries (s : Store Id C) (l : List (Op Id C)) :
    replay s l = replay s (firstDeliveries s.applied l) := by
  induction l generalizing s with
  | nil => rfl
  | cons o l ih =>
    simp only [firstDeliveries]
    split_ifs with h
    · rw [replay_cons, apply_of_mem h, ih]
    · rw [replay_cons, replay_cons, ih (apply s o), apply_of_not_mem h]

/-- A retried delivery anywhere after the first has no effect. -/
theorem replay_retry (s : Store Id C) (l₁ l₂ : List (Op Id C)) {o : Op Id C} (h : o ∈ l₁) :
    replay s (l₁ ++ o :: l₂) = replay s (l₁ ++ l₂) := by
  rw [replay_append, replay_append, replay_cons, apply_of_mem (mem_applied_replay s h)]

/-! ## Bounded writes -/

/-- Each operation adds at most one version across all records. -/
theorem total_revisions_apply_le (s : Store Id C) (o : Op Id C) (ids : Finset Id) :
    ∑ y ∈ ids, revision (apply s o) y ≤ (∑ y ∈ ids, revision s y) + 1 := by
  unfold apply
  split_ifs
  · exact Nat.le_succ _
  · simp only [revision, execH]
    calc ∑ y ∈ ids, (if o.cmd.target = some y then stepRecord (s.history y) o
            else s.history y).length
        ≤ ∑ y ∈ ids, ((s.history y).length + if o.cmd.target = some y then 1 else 0) := by
          apply Finset.sum_le_sum
          intro y _
          split_ifs
          · exact length_stepRecord_le _ _
          · simp
      _ = (∑ y ∈ ids, (s.history y).length) +
            ∑ y ∈ ids, (if o.cmd.target = some y then 1 else 0) := Finset.sum_add_distrib
      _ ≤ (∑ y ∈ ids, (s.history y).length) + 1 := by
          apply Nat.add_le_add_left
          cases ht : o.cmd.target with
          | none => simp
          | some x =>
            simp only [Option.some.injEq]
            rw [Finset.sum_ite_eq]
            split_ifs <;> simp

/-- Total history grows by at most one version per logged operation. -/
theorem total_revisions_le (s : Store Id C) (l : List (Op Id C)) (ids : Finset Id) :
    ∑ y ∈ ids, revision (replay s l) y ≤ (∑ y ∈ ids, revision s y) + l.length := by
  induction l generalizing s with
  | nil => simp [replay_nil]
  | cons o l ih =>
    rw [replay_cons, List.length_cons]
    have := ih (apply s o)
    have := total_revisions_apply_le s o ids
    omega

/-! ## Examples -/

/-- Record 7 is added, updated (the update is delivered twice), deleted, and then
an addition tries to reuse its identifier. The deletion is also delivered twice. -/
def exampleLog : List (Op ℕ ℕ) :=
  [⟨1, .add 7 10⟩, ⟨2, .update 7 20⟩, ⟨2, .update 7 20⟩, ⟨3, .delete 7⟩, ⟨4, .add 7 30⟩,
    ⟨3, .delete 7⟩]

example : (replay Store.empty exampleLog).history 7 = [⟨none, 3⟩, ⟨some 20, 2⟩, ⟨some 10, 1⟩] ∧
    active (replay Store.empty exampleLog) 7 = none ∧
    revision (replay Store.empty exampleLog) 7 = 3 := by
  decide

/-! ## A draining consolidation queue -/

/-- The decision on one candidate fact: a memory command, or a deferral (for
example while the model is unavailable). -/
inductive Decision (Id C : Type) where
  | commit (cmd : Cmd Id C)
  | defer

/-- Candidates waiting with their remaining deferral budget, the store, the next
operation identity and the candidates already resolved. -/
structure Pipeline (F Id C : Type) where
  pending : List (F × ℕ)
  store : Store Id C
  nextOp : ℕ
  resolved : List F

/-- One unit of work per remaining deferral plus one for the final decision. -/
def work {F : Type} (pending : List (F × ℕ)) : ℕ := (pending.map (fun x => x.2 + 1)).sum

variable {F : Type}

/-- One step on the head candidate. A command is committed under a fresh
operation identity. A deferral with remaining budget requeues the candidate with
a smaller budget. A deferral without budget expires the candidate as a recorded
`NOOP`. -/
def step (oracle : Store Id C → F → Decision Id C) (p : Pipeline F Id C) : Pipeline F Id C :=
  match p.pending with
  | [] => p
  | (f, b) :: rest =>
    match oracle p.store f, b with
    | .commit cmd, _ => ⟨rest, apply p.store ⟨p.nextOp, cmd⟩, p.nextOp + 1, f :: p.resolved⟩
    | .defer, 0 => ⟨rest, apply p.store ⟨p.nextOp, .noop⟩, p.nextOp + 1, f :: p.resolved⟩
    | .defer, b + 1 => ⟨rest ++ [(f, b)], p.store, p.nextOp, p.resolved⟩

theorem work_cons (f : F) (b : ℕ) (rest : List (F × ℕ)) :
    work ((f, b) :: rest) = b + 1 + work rest := by
  simp [work]

theorem work_append (l₁ l₂ : List (F × ℕ)) : work (l₁ ++ l₂) = work l₁ + work l₂ := by
  simp [work]

theorem work_eq_zero {pending : List (F × ℕ)} (h : work pending = 0) : pending = [] := by
  cases pending with
  | nil => rfl
  | cons x rest =>
    obtain ⟨f, b⟩ := x
    rw [work_cons] at h
    omega

theorem step_of_nil (oracle : Store Id C → F → Decision Id C) {p : Pipeline F Id C}
    (h : p.pending = []) : step oracle p = p := by
  unfold step
  rw [h]

/-- Every step on a nonempty queue strictly decreases the remaining work. -/
theorem work_step_lt (oracle : Store Id C → F → Decision Id C) {p : Pipeline F Id C}
    (h : p.pending ≠ []) : work (step oracle p).pending < work p.pending := by
  obtain ⟨pending, store, nextOp, resolved⟩ := p
  cases pending with
  | nil => exact absurd rfl h
  | cons x rest =>
    obtain ⟨f, b⟩ := x
    simp only [step]
    rcases oracle store f with cmd | _
    · simp only [work_cons]; omega
    · cases b with
      | zero => simp only [work_cons]; omega
      | succ b =>
        show work (rest ++ [(f, b)]) < work ((f, b + 1) :: rest)
        rw [work_append, work_cons, work_cons]
        simp only [work, List.map_nil, List.sum_nil]
        omega

theorem pending_iterate_of_work_le (oracle : Store Id C → F → Decision Id C) :
    ∀ (n : ℕ) (p : Pipeline F Id C), work p.pending ≤ n →
      ((step oracle)^[n] p).pending = [] := by
  intro n
  induction n with
  | zero => intro p h; exact work_eq_zero (Nat.le_zero.mp h)
  | succ n ih =>
    intro p h
    rw [Function.iterate_succ_apply]
    by_cases hp : p.pending = []
    · rw [step_of_nil oracle hp]
      exact ih p (by rw [hp]; simp [work])
    · exact ih _ (Nat.le_of_lt_succ (lt_of_lt_of_le (work_step_lt oracle hp) h))

/-- Liveness: whatever the oracle decides, including deferring forever, the
queue is empty after `work` steps. -/
theorem drains (oracle : Store Id C → F → Decision Id C) (p : Pipeline F Id C) :
    ((step oracle)^[work p.pending] p).pending = [] :=
  pending_iterate_of_work_le oracle _ p le_rfl

/-- Candidates are conserved: each step moves at most one candidate from the queue
to the resolved list, and none is lost or duplicated. -/
theorem step_perm (oracle : Store Id C → F → Decision Id C) (p : Pipeline F Id C) :
    ((step oracle p).pending.map Prod.fst ++ (step oracle p).resolved).Perm
      (p.pending.map Prod.fst ++ p.resolved) := by
  obtain ⟨pending, store, nextOp, resolved⟩ := p
  cases pending with
  | nil => exact List.Perm.refl _
  | cons x rest =>
    obtain ⟨f, b⟩ := x
    simp only [step]
    rcases oracle store f with cmd | _
    · simp
    · cases b with
      | zero => simp
      | succ b =>
        simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.cons_append]
        exact List.perm_middle

theorem iterate_perm (oracle : Store Id C → F → Decision Id C) (n : ℕ) (p : Pipeline F Id C) :
    (((step oracle)^[n] p).pending.map Prod.fst ++ ((step oracle)^[n] p).resolved).Perm
      (p.pending.map Prod.fst ++ p.resolved) := by
  induction n generalizing p with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact (ih (step oracle p)).trans (step_perm oracle p)

/-- After draining, every candidate has been resolved exactly once. -/
theorem resolved_perm (oracle : Store Id C → F → Decision Id C) (p : Pipeline F Id C) :
    ((step oracle)^[work p.pending] p).resolved.Perm (p.pending.map Prod.fst ++ p.resolved) := by
  have h := iterate_perm oracle (work p.pending) p
  rwa [drains oracle p, List.map_nil, List.nil_append] at h

theorem step_nextOp_add_length (oracle : Store Id C → F → Decision Id C) (p : Pipeline F Id C) :
    (step oracle p).nextOp + (step oracle p).pending.length = p.nextOp + p.pending.length := by
  obtain ⟨pending, store, nextOp, resolved⟩ := p
  cases pending with
  | nil => rfl
  | cons x rest =>
    obtain ⟨f, b⟩ := x
    simp only [step]
    rcases oracle store f with cmd | _
    · simp; omega
    · cases b with
      | zero => simp; omega
      | succ b => simp

/-- Each candidate consumes exactly one operation identity. -/
theorem nextOp_after_drain (oracle : Store Id C → F → Decision Id C) (p : Pipeline F Id C) :
    ((step oracle)^[work p.pending] p).nextOp = p.nextOp + p.pending.length := by
  have key : ∀ n (q : Pipeline F Id C), ((step oracle)^[n] q).nextOp +
      ((step oracle)^[n] q).pending.length = q.nextOp + q.pending.length := by
    intro n
    induction n with
    | zero => intro q; rfl
    | succ n ih =>
      intro q
      rw [Function.iterate_succ_apply, ih, step_nextOp_add_length]
  have := key (work p.pending) p
  rwa [drains oracle p, List.length_nil, Nat.add_zero] at this

/-- Operation identities are fresh: every decided identity is below `nextOp`. -/
def Fresh (p : Pipeline F Id C) : Prop := ∀ x ∈ p.store.applied, x < p.nextOp

theorem fresh_step (oracle : Store Id C → F → Decision Id C) {p : Pipeline F Id C}
    (hp : Fresh p) : Fresh (step oracle p) := by
  obtain ⟨pending, store, nextOp, resolved⟩ := p
  cases pending with
  | nil => exact hp
  | cons x rest =>
    obtain ⟨f, b⟩ := x
    have hfresh : ∀ (cmd : Cmd Id C), Fresh (⟨rest, apply store ⟨nextOp, cmd⟩, nextOp + 1,
        f :: resolved⟩ : Pipeline F Id C) := by
      intro cmd y hy
      have hn : nextOp ∉ store.applied := fun h => Nat.lt_irrefl _ (hp nextOp h)
      rw [apply_of_not_mem (s := store) (o := ⟨nextOp, cmd⟩) hn] at hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (hp y hy)
    simp only [step]
    rcases oracle store f with cmd | _
    · exact hfresh cmd
    · cases b with
      | zero => exact hfresh .noop
      | succ b => exact hp

/-- A committed decision is never discarded as a retry: the store applies the
command's transition. -/
theorem commit_takes_effect (oracle : Store Id C → F → Decision Id C) {p : Pipeline F Id C}
    (hp : Fresh p) {f : F} {b : ℕ} {rest : List (F × ℕ)} (hq : p.pending = (f, b) :: rest)
    {cmd : Cmd Id C} (hc : oracle p.store f = .commit cmd) :
    (step oracle p).store.history = execH p.store.history ⟨p.nextOp, cmd⟩ := by
  have hn : p.nextOp ∉ p.store.applied := fun h => Nat.lt_irrefl _ (hp p.nextOp h)
  unfold step
  rw [hq]
  simp only [hc]
  rw [apply_of_not_mem hn]

/-- An oracle that always defers still drains a queue with budget 2 in three
steps, resolving the candidate as a recorded `NOOP`. -/
example :
    let p : Pipeline ℕ ℕ ℕ := ⟨[(5, 2)], Store.empty, 0, []⟩
    let q := (step (fun _ _ => .defer))^[work p.pending] p
    q.pending = [] ∧ q.resolved = [5] ∧ q.nextOp = 1 ∧ 0 ∈ q.store.applied := by
  decide

/-! ## Without a budget the queue need not drain -/

/-- Deferral without a budget: the candidate returns to the queue unchanged. -/
def stepUnbudgeted (oracle : Store Id C → F → Decision Id C) (p : Pipeline F Id C) :
    Pipeline F Id C :=
  match p.pending with
  | [] => p
  | (f, b) :: rest =>
    match oracle p.store f with
    | .commit cmd => ⟨rest, apply p.store ⟨p.nextOp, cmd⟩, p.nextOp + 1, f :: p.resolved⟩
    | .defer => ⟨rest ++ [(f, b)], p.store, p.nextOp, p.resolved⟩

/-- With unbudgeted deferral, an oracle that always defers keeps every nonempty
queue nonempty forever. -/
theorem unbudgeted_never_drains (p : Pipeline F Id C) (hp : p.pending ≠ []) (n : ℕ) :
    ((stepUnbudgeted (fun _ _ => .defer))^[n] p).pending ≠ [] := by
  have hlen : ∀ (m : ℕ) (q : Pipeline F Id C),
      ((stepUnbudgeted (fun _ _ => (.defer : Decision Id C)))^[m] q).pending.length =
        q.pending.length := by
    intro m
    induction m with
    | zero => intro q; rfl
    | succ m ih =>
      intro q
      rw [Function.iterate_succ_apply, ih]
      obtain ⟨pending, store, nextOp, resolved⟩ := q
      cases pending with
      | nil => rfl
      | cons x rest => simp [stepUnbudgeted]
  intro h
  have := hlen n p
  rw [h, List.length_nil] at this
  exact hp (List.eq_nil_of_length_eq_zero this.symm)

end AgentMemory.EventLog
