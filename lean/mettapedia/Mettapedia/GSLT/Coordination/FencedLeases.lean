import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Commits
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Image

/-!
# Leases with fencing: a crash-tolerant take

A task is taken in three steps: a worker **claims** it and receives a lease, the lease either
**expires** (the task is live again) or the worker's **effect** is accepted (the task is done).
One location, the task's owner, runs these steps; workers talk to it by messages.

**Fault model.** Workers may crash at any point and never return. Messages may be delayed,
duplicated and reordered without bound, so any request may reach the owner at any time, including
a stale worker's late effect and repeated requests. The owner does not crash; its clock advances
by `tick`, and its timer issues `expire` requests. Senders are authenticated by the transport
(the `who` of a request); content is not trusted.

## The owner

Each task has a role (`live`, `claimed holder expiry`, `done holder`) and an **epoch**, a counter
that every change of role increases. A claim of a live task grants a lease until the owner's clock
reaches `clock + duration`, and its token is the new epoch. An effect is accepted only from the
holder, with the current epoch (`Current`): that check is the **fencing**.

## Safety, for every sequence of requests

* **At most one effect per task** (`effects_nodup`): no task appears twice among the accepted
  effects, however requests are duplicated, delayed or forged.
* **Only the current holder's effect is accepted** (`effect_from_grant`, `stale_rejected`): every
  accepted effect is from a worker the task was granted to, with that grant's epoch; a token whose
  epoch is no longer current is rejected. A token is a versioned capability
  (`AuthorityRoles.current_iff_valid`).
* **Refinement of the atomic take** (`step_refines`): read through `abstraction` (the done tasks
  and the effects), every step of the owner is either invisible or one atomic take of a task not
  yet taken. Claims, expiries and ticks are invisible.

## Each step is a commit of the occurrence store

The owner's state is a store of occurrences, one per task, whose identity is the task, its epoch
and its role (`encode`). Claim, expiry and effect each fire one positive commit that takes the
task's occurrence and makes its successor (`encode_step_effect`, `encode_step_claim`,
`encode_step_expire`), and **an effect request is accepted exactly when its commit is enabled**
(`effect_enabled_iff`). So the fencing token is an occurrence identity, and a stale token names an
occurrence that is gone: fencing is the identity check of the commit semantics, realized at the
owner. Leases are a program over commits, not a new primitive.

## Liveness, for infinite runs

* **No stuck claims** (`returns_or_done`): if the clock ticks and the timer fires infinitely
  often, a task that is not done is live again infinitely often. A crashed holder blocks nothing
  forever.
* **A timely worker completes** (`timely_worker_completes`): a worker whose claim reaches the owner
  while the task is live, and whose effect arrives before the owner's clock reaches the lease's
  expiry, finishes the task.
* **Eventually processed** (`eventually_done`): with ticks and timers infinitely often, and a timely
  worker whose claim is served at some moment when the task is live, the task is done.

## Controls

* `Controls.stale_fenced`: a worker whose lease expired and was granted to another has its late
  effect rejected; the new holder's effect is accepted.
* `Controls.unfenced_accepts_stale`: an owner that accepts any effect for a claimed task accepts
  the stale worker's effect while another worker holds the lease.
* `Controls.no_expiry_blocks`: without expiry, a crashed holder blocks the task forever, although
  another worker keeps asking.
* `Controls.starvation`: with expiry but without fair service, a faulty worker that always
  re-claims first starves a correct worker forever: fairness is a real hypothesis.
* `Controls.named_impersonation`: checking a holder name written in the request's content lets a
  non-holder who knows the epoch complete the task; the authenticated check refuses it.

## Effects outside the owner

When the effect is a write to another resource, the resource fences by the largest epoch it has
seen (`FencedResource.epochs_sorted`): accepted writes never go back to an older epoch. Without
the check a stale write lands after a newer one (`FencedResource.unfenced_stale_lands`).
Fencing alone allows one write per epoch, so two successive holders both write
(`FencedResource.fencing_allows_two`): fencing does not make an external effect exactly once. At
most one write per task needs the key at the effect's boundary: a sink that deduplicates by task
(`FencedResource.dedup_at_most_one`), fenced as well (`FencedResource.fenced_keyed_once`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.FencedLeases

universe u v

/-- The role of a task at its owner. -/
inductive Role (W : Type v) where
  | live
  | claimed (holder : W) (expiry : ℕ)
  | done (holder : W)
  deriving DecidableEq, Repr

namespace Role

variable {W : Type v} [DecidableEq W]

/-- Held by `who` as a lease. -/
def heldBy (who : W) : Role W → Bool
  | claimed holder _ => decide (holder = who)
  | _ => false

/-- A lease whose expiry the clock has reached. -/
def expiredAt (clock : ℕ) : Role W → Bool
  | claimed _ expiry => decide (expiry ≤ clock)
  | _ => false

theorem heldBy_eq_true {who : W} {role : Role W} :
    role.heldBy who = true ↔ ∃ expiry, role = claimed who expiry := by
  cases role <;> simp [heldBy]

omit [DecidableEq W] in
theorem expiredAt_eq_true {clock : ℕ} {role : Role W} :
    role.expiredAt clock = true ↔ ∃ holder expiry, role = claimed holder expiry ∧ expiry ≤ clock := by
  cases role <;> simp [expiredAt]

end Role

/-- A request reaching the owner. `who` is the authenticated sender. -/
inductive Request (X : Type u) (W : Type v) where
  | claim (who : W) (task : X)
  | tick
  | expire (task : X)
  | effect (who : W) (task : X) (epoch : ℕ)
  deriving DecidableEq

/-- The owner's state: roles, epochs, clock, the grants it issued and the effects it accepted. -/
structure Owner (X : Type u) (W : Type v) where
  role : X → Role W
  epoch : X → ℕ
  clock : ℕ
  grants : List (X × W × ℕ)
  effects : List (X × W × ℕ)

variable {X : Type u} [DecidableEq X] {W : Type v} [DecidableEq W]

/-- Every task live at epoch `0`, nothing granted or done. -/
def Owner.start : Owner X W := ⟨fun _ => .live, fun _ => 0, 0, [], []⟩

/-- The effect of `who` on `task` with token `epoch` is current: `who` holds the lease and the
token is the task's epoch. -/
def Current (s : Owner X W) (who : W) (task : X) (epoch : ℕ) : Prop :=
  (s.role task).heldBy who = true ∧ s.epoch task = epoch

instance (s : Owner X W) (who : W) (task : X) (epoch : ℕ) : Decidable (Current s who task epoch) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable (duration : ℕ)

/-- One request at the owner. -/
def step (s : Owner X W) : Request X W → Owner X W
  | .claim who task =>
      if s.role task = .live then
        { s with
          role := Function.update s.role task (.claimed who (s.clock + duration))
          epoch := Function.update s.epoch task (s.epoch task + 1)
          grants := s.grants ++ [(task, who, s.epoch task + 1)] }
      else s
  | .tick => { s with clock := s.clock + 1 }
  | .expire task =>
      if (s.role task).expiredAt s.clock = true then
        { s with
          role := Function.update s.role task .live
          epoch := Function.update s.epoch task (s.epoch task + 1) }
      else s
  | .effect who task epoch =>
      if Current s who task epoch then
        { s with
          role := Function.update s.role task (.done who)
          epoch := Function.update s.epoch task (s.epoch task + 1)
          effects := s.effects ++ [(task, who, epoch)] }
      else s

/-- A finite run. -/
def runList (s : Owner X W) : List (Request X W) → Owner X W
  | [] => s
  | r :: rs => runList (step duration s r) rs

/-! ## Safety -/

theorem nodup_append_singleton {α : Type*} {l : List α} {a : α} (nodup : l.Nodup) (fresh : a ∉ l) :
    (l ++ [a]).Nodup :=
  List.nodup_append.mpr ⟨nodup, List.nodup_singleton a, fun b inL c inC same => by
    rw [List.mem_singleton] at inC
    subst inC
    exact fresh (same ▸ inL)⟩

/-- The owner's invariant: a task is among the effects exactly when it is done, no task twice; a
lease is held only under a grant with the current epoch, and a done task's effect carries the
epoch just before the current one. -/
structure Inv (s : Owner X W) : Prop where
  nodup : (s.effects.map Prod.fst).Nodup
  done_iff : ∀ task, task ∈ s.effects.map Prod.fst ↔ ∃ who, s.role task = .done who
  granted : ∀ task who expiry, s.role task = .claimed who expiry →
    (task, who, s.epoch task) ∈ s.grants
  effect_granted : ∀ entry ∈ s.effects, entry ∈ s.grants

omit [DecidableEq X] [DecidableEq W] in
theorem inv_start : Inv (Owner.start : Owner X W) where
  nodup := List.nodup_nil
  done_iff _ := by simp [Owner.start]
  granted _ _ _ h := by simp [Owner.start] at h
  effect_granted _ h := by simp [Owner.start] at h

theorem inv_step {s : Owner X W} (inv : Inv s) (r : Request X W) : Inv (step duration s r) := by
  cases r with
  | claim who task =>
      simp only [step]
      split_ifs with isLive
      · refine ⟨inv.nodup, fun t => ?_, fun t w e h => ?_, fun entry h => ?_⟩
        · by_cases same : t = task
          · subst same
            have notDone : t ∉ s.effects.map Prod.fst := fun member => by
              obtain ⟨w, h⟩ := (inv.done_iff t).mp member
              rw [isLive] at h; cases h
            simp [notDone]
          · simpa [Function.update_of_ne same] using inv.done_iff t
        · by_cases same : t = task
          · subst same
            simp only [Function.update_self, Role.claimed.injEq] at h ⊢
            obtain ⟨rfl, -⟩ := h
            exact List.mem_append_right _ (List.mem_singleton_self _)
          · simp only [Function.update_of_ne same] at h ⊢
            exact List.mem_append_left _ (inv.granted t w e h)
        · exact List.mem_append_left _ (inv.effect_granted entry h)
      · exact inv
  | tick => exact ⟨inv.nodup, inv.done_iff, inv.granted, inv.effect_granted⟩
  | expire task =>
      simp only [step]
      split_ifs with expired
      · obtain ⟨holder, expiry, isClaimed, _⟩ := Role.expiredAt_eq_true.mp expired
        refine ⟨inv.nodup, fun t => ?_, fun t w e h => ?_, inv.effect_granted⟩
        · by_cases same : t = task
          · subst same
            have notDone : t ∉ s.effects.map Prod.fst := fun member => by
              obtain ⟨w, h⟩ := (inv.done_iff t).mp member
              rw [isClaimed] at h; cases h
            simp [notDone]
          · simpa [Function.update_of_ne same] using inv.done_iff t
        · by_cases same : t = task
          · subst same; simp at h
          · simp only [Function.update_of_ne same] at h ⊢
            exact inv.granted t w e h
      · exact inv
  | effect who task epoch =>
      simp only [step]
      split_ifs with current
      · obtain ⟨⟨expiry, isClaimed⟩, sameEpoch⟩ := And.imp_left Role.heldBy_eq_true.mp current
        have notDone : task ∉ s.effects.map Prod.fst := fun member => by
          obtain ⟨w, h⟩ := (inv.done_iff task).mp member
          rw [isClaimed] at h; cases h
        refine ⟨?_, fun t => ?_, fun t w e h => ?_, fun entry h => ?_⟩
        · rw [List.map_append]
          exact nodup_append_singleton inv.nodup notDone
        · by_cases same : t = task
          · subst same; simp
          · simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
              List.mem_singleton, Function.update_of_ne same, same, or_false]
            exact inv.done_iff t
        · by_cases same : t = task
          · subst same; simp at h
          · simp only [Function.update_of_ne same] at h ⊢
            exact inv.granted t w e h
        · rcases List.mem_append.mp h with old | new
          · exact inv.effect_granted entry old
          · rw [List.mem_singleton] at new
            subst new
            rw [← sameEpoch]
            exact inv.granted task who expiry isClaimed
      · exact inv

theorem inv_runList {s : Owner X W} (inv : Inv s) (requests : List (Request X W)) :
    Inv (runList duration s requests) := by
  induction requests generalizing s with
  | nil => exact inv
  | cons r rest ih => exact ih (inv_step duration inv r)

/-- **At most one effect per task**, for every sequence of requests. -/
theorem effects_nodup (requests : List (Request X W)) :
    ((runList duration Owner.start requests).effects.map Prod.fst).Nodup :=
  (inv_runList duration inv_start requests).nodup

/-- **Every accepted effect is from a grant**: the worker was granted the task with that epoch. -/
theorem effect_from_grant (requests : List (Request X W)) :
    ∀ entry ∈ (runList duration Owner.start requests).effects,
      entry ∈ (runList duration Owner.start requests).grants :=
  (inv_runList duration inv_start requests).effect_granted

/-- **A stale token is rejected**: an effect whose epoch is not the task's current epoch changes
nothing. -/
theorem stale_rejected (s : Owner X W) {who : W} {task : X} {epoch : ℕ}
    (stale : s.epoch task ≠ epoch) : step duration s (.effect who task epoch) = s := by
  simp only [step]
  rw [if_neg fun current => stale current.2]

/-! ## Refinement of the atomic take -/

/-- The atomic view: which tasks are taken, and by whom, in order. -/
structure Atomic (X : Type u) (W : Type v) where
  taken : Set X
  log : List (X × W)

/-- One atomic take. -/
def Atomic.take (a : Atomic X W) (who : W) (task : X) : Atomic X W :=
  ⟨insert task a.taken, a.log ++ [(task, who)]⟩

/-- What an owner's state shows of the atomic take. -/
def abstraction (s : Owner X W) : Atomic X W :=
  ⟨{task | ∃ who, s.role task = .done who}, s.effects.map fun entry => (entry.1, entry.2.1)⟩

/-- **Refinement**: every step of the owner is invisible in the atomic view, or is one atomic take
of a task not yet taken. -/
theorem step_refines (s : Owner X W) (r : Request X W) :
    abstraction (step duration s r) = abstraction s ∨
      ∃ who task, task ∉ (abstraction s).taken ∧
        abstraction (step duration s r) = (abstraction s).take who task := by
  have doneSame : ∀ (s' : Owner X W), s'.effects = s.effects →
      (∀ t, (∃ w, s'.role t = .done w) ↔ ∃ w, s.role t = .done w) → abstraction s' = abstraction s := by
    intro s' sameEffects sameDone
    simp only [abstraction, sameEffects, Atomic.mk.injEq, and_true]
    ext t
    exact sameDone t
  cases r with
  | claim who task =>
      left
      simp only [step]
      split_ifs with isLive
      · refine doneSame _ rfl fun t => ?_
        by_cases same : t = task
        · subst same; simp [isLive]
        · simp [Function.update_of_ne same]
      · rfl
  | tick => left; rfl
  | expire task =>
      left
      simp only [step]
      split_ifs with expired
      · obtain ⟨holder, expiry, isClaimed, _⟩ := Role.expiredAt_eq_true.mp expired
        refine doneSame _ rfl fun t => ?_
        by_cases same : t = task
        · subst same; simp [isClaimed]
        · simp [Function.update_of_ne same]
      · rfl
  | effect who task epoch =>
      simp only [step]
      split_ifs with current
      · right
        obtain ⟨⟨expiry, isClaimed⟩, _⟩ := And.imp_left Role.heldBy_eq_true.mp current
        refine ⟨who, task, fun ⟨w, h⟩ => ?_, ?_⟩
        · rw [isClaimed] at h; cases h
        · simp only [abstraction, Atomic.take, List.map_append, List.map_cons, List.map_nil,
            Atomic.mk.injEq, and_true]
          ext t
          by_cases same : t = task
          · subst same; simp
          · simp [same]
      · left; rfl

/-! ## Each step is a commit of the occurrence store -/

section Commits

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

/-- An occurrence of the owner's store: a task at an epoch in a role. Its label is its role. -/
structure LeaseOcc (X : Type u) (W : Type v) where
  task : X
  epoch : ℕ
  role : Role W
  deriving DecidableEq

variable [Fintype X]

/-- The owner's store: one occurrence per task. -/
def encode (s : Owner X W) : Finset (LeaseOcc X W) :=
  Finset.univ.image fun task => ⟨task, s.epoch task, s.role task⟩

theorem mem_encode {s : Owner X W} {o : LeaseOcc X W} :
    o ∈ encode s ↔ s.epoch o.task = o.epoch ∧ s.role o.task = o.role := by
  simp only [encode, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨task, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨sameEpoch, sameRole⟩
    refine ⟨o.task, ?_⟩
    cases o
    simp only at sameEpoch sameRole ⊢
    rw [sameEpoch, sameRole]

/-- The commit that moves a task from one role to the next, one epoch on. -/
def moveCommit (task : X) (epoch : ℕ) (old new : Role W) : Commit (LeaseOcc X W) (Role W) :=
  ⟨{⟨task, epoch, old⟩}, ∅, {⟨task, epoch + 1, new⟩}, []⟩

/-- **The move commit is enabled exactly when the task is at that epoch in that role.** -/
theorem move_enabled_iff {s : Owner X W} {task : X} {epoch : ℕ} {old new : Role W} :
    Enabled LeaseOcc.role (encode s) (moveCommit task epoch old new) ↔
      s.epoch task = epoch ∧ s.role task = old := by
  constructor
  · intro enabled
    have := enabled.taken_subset (Finset.mem_singleton_self _)
    exact mem_encode.mp this
  · rintro ⟨sameEpoch, sameRole⟩
    refine ⟨?_, by simp [moveCommit], by simp [moveCommit], ?_, by simp [moveCommit]⟩
    · intro o member
      rw [Finset.mem_singleton.mp member]
      exact mem_encode.mpr ⟨sameEpoch, sameRole⟩
    · refine Finset.disjoint_left.mpr fun o made inStore => ?_
      rw [Finset.mem_singleton.mp made] at inStore
      have := (mem_encode.mp inStore).1
      simp only at this
      omega

/-- Moving one task's entry of the owner's state is firing its move commit. -/
theorem encode_move {s s' : Owner X W} {task : X} {new : Role W}
    (roleMoved : s'.role = Function.update s.role task new)
    (epochMoved : s'.epoch = Function.update s.epoch task (s.epoch task + 1)) :
    encode s' = fire (encode s) (moveCommit task (s.epoch task) (s.role task) new) := by
  ext o
  rcases o with ⟨t, e, r⟩
  simp only [mem_fire, mem_encode, moveCommit, Finset.mem_singleton, roleMoved, epochMoved,
    LeaseOcc.mk.injEq]
  by_cases same : t = task
  · subst same
    simp only [Function.update_self, true_and]
    constructor
    · rintro ⟨h₁, h₂⟩; exact Or.inr ⟨h₁.symm, h₂.symm⟩
    · rintro (⟨⟨h₁, h₂⟩, notOld⟩ | ⟨h₁, h₂⟩)
      · exact absurd ⟨h₁.symm, h₂.symm⟩ notOld
      · exact ⟨h₁.symm, h₂.symm⟩
  · simp [same]

/-- **An effect request is accepted exactly when its commit is enabled**: the token names the
claim occurrence, and fencing is the commit's identity check. -/
theorem effect_enabled_iff (s : Owner X W) (who : W) (task : X) (epoch : ℕ) :
    Current s who task epoch ↔ ∃ expiry,
      Enabled LeaseOcc.role (encode s) (moveCommit task epoch (.claimed who expiry) (.done who)) := by
  simp only [move_enabled_iff, Current, Role.heldBy_eq_true]
  constructor
  · rintro ⟨⟨expiry, isClaimed⟩, sameEpoch⟩; exact ⟨expiry, sameEpoch, isClaimed⟩
  · rintro ⟨expiry, sameEpoch, isClaimed⟩; exact ⟨⟨expiry, isClaimed⟩, sameEpoch⟩

/-- An accepted effect fires its commit. -/
theorem encode_step_effect {s : Owner X W} {who : W} {task : X} {epoch : ℕ}
    (current : Current s who task epoch) :
    encode (step duration s (.effect who task epoch)) =
      fire (encode s) (moveCommit task (s.epoch task) (s.role task) (.done who)) := by
  simp only [step, if_pos current]
  exact encode_move rfl rfl

/-- An accepted claim fires its commit. -/
theorem encode_step_claim {s : Owner X W} {who : W} {task : X} (isLive : s.role task = .live) :
    encode (step duration s (.claim who task)) =
      fire (encode s) (moveCommit task (s.epoch task) (s.role task) (.claimed who (s.clock + duration))) := by
  simp only [step, if_pos isLive]
  exact encode_move rfl rfl

/-- An accepted expiry fires its commit. -/
theorem encode_step_expire {s : Owner X W} {task : X}
    (expired : (s.role task).expiredAt s.clock = true) :
    encode (step duration s (.expire task)) =
      fire (encode s) (moveCommit task (s.epoch task) (s.role task) .live) := by
  simp only [step, if_pos expired]
  exact encode_move rfl rfl

omit [DecidableEq X] [DecidableEq W] [Fintype X] in
/-- The owner's commits are positive: they take one occurrence and make one, and query no
region. -/
theorem moveCommit_positive (task : X) (epoch : ℕ) (old new : Role W) :
    (moveCommit task epoch old new).Positive := rfl

end Commits

/-! ## Liveness -/

/-- An infinite run: the state after the first `n` requests. -/
def trace (requests : ℕ → Request X W) : ℕ → Owner X W
  | 0 => Owner.start
  | n + 1 => step duration (trace requests n) (requests n)

theorem clock_step_ge (s : Owner X W) (r : Request X W) : s.clock ≤ (step duration s r).clock := by
  cases r <;> simp only [step] <;> (try split_ifs) <;> simp

theorem clock_mono (requests : ℕ → Request X W) {n m : ℕ} (le : n ≤ m) :
    (trace duration requests n).clock ≤ (trace duration requests m).clock := by
  induction le with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (clock_step_ge duration _ _)

/-- With ticks infinitely often, the clock passes every bound. -/
theorem clock_unbounded (requests : ℕ → Request X W)
    (ticks : ∀ n, ∃ m ≥ n, requests m = .tick) (n bound : ℕ) :
    ∃ m ≥ n, bound ≤ (trace duration requests m).clock := by
  induction bound with
  | zero => exact ⟨n, le_rfl, Nat.zero_le _⟩
  | succ bound ih =>
      obtain ⟨m, le, reached⟩ := ih
      obtain ⟨t, tickAfter, isTick⟩ := ticks m
      refine ⟨t + 1, by omega, ?_⟩
      have := clock_mono duration requests tickAfter
      simp only [trace, isTick, step]
      omega

/-- From a lease, one step leads to the same lease, to a live task, or to a done task. -/
theorem role_step_of_claimed {s : Owner X W} {task : X} {holder : W} {expiry : ℕ}
    (isClaimed : s.role task = .claimed holder expiry) (r : Request X W) :
    (step duration s r).role task = .claimed holder expiry ∨ (step duration s r).role task = .live ∨
      ∃ who, (step duration s r).role task = .done who := by
  cases r with
  | claim who t =>
      left
      simp only [step]
      split_ifs with isLive
      · have : t ≠ task := fun same => by subst same; rw [isClaimed] at isLive; cases isLive
        simp [Function.update_of_ne (Ne.symm this), isClaimed]
      · exact isClaimed
  | tick => left; exact isClaimed
  | expire t =>
      simp only [step]
      split_ifs
      · by_cases same : t = task
        · subst same; right; left; simp
        · left; simp [Function.update_of_ne (Ne.symm same), isClaimed]
      · left; exact isClaimed
  | effect who t epoch =>
      simp only [step]
      split_ifs
      · by_cases same : t = task
        · subst same; right; right; exact ⟨who, by simp⟩
        · left; simp [Function.update_of_ne (Ne.symm same), isClaimed]
      · left; exact isClaimed

/-- **No stuck claims**: with ticks and timer firings for the task infinitely often, a task is
live or done infinitely often. A crashed holder blocks nothing forever. -/
theorem returns_or_done (requests : ℕ → Request X W) (task : X)
    (ticks : ∀ n, ∃ m ≥ n, requests m = .tick)
    (expiries : ∀ n, ∃ m ≥ n, requests m = .expire task) (n : ℕ) :
    ∃ m ≥ n, (trace duration requests m).role task = .live ∨
      ∃ who, (trace duration requests m).role task = .done who := by
  by_contra never
  push Not at never
  obtain ⟨notLive, notDone⟩ := never n le_rfl
  -- At `n` the task is under some lease, and it stays under that lease.
  obtain ⟨holder, expiry, isClaimed⟩ : ∃ holder expiry,
      (trace duration requests n).role task = .claimed holder expiry := by
    cases h : (trace duration requests n).role task with
    | live => exact absurd h notLive
    | claimed holder expiry => exact ⟨holder, expiry, rfl⟩
    | done who => exact absurd h (notDone who)
  have stays : ∀ m ≥ n, (trace duration requests m).role task = .claimed holder expiry := by
    intro m le
    induction le with
    | refl => exact isClaimed
    | step le ih =>
        rcases role_step_of_claimed duration ih (requests _) with same | live | ⟨who, done⟩
        · exact same
        · exact absurd live (never _ (Nat.le_succ_of_le le)).1
        · exact absurd done ((never _ (Nat.le_succ_of_le le)).2 who)
  -- The clock reaches the expiry, and then the timer frees the task.
  obtain ⟨t, tAfter, reached⟩ := clock_unbounded duration requests ticks n expiry
  obtain ⟨m, mAfter, isExpire⟩ := expiries t
  have claimedAtM := stays m (tAfter.trans mAfter)
  have clockAtM := (clock_mono duration requests mAfter)
  have freed : (trace duration requests (m + 1)).role task = .live := by
    simp only [trace, isExpire, step]
    rw [if_pos (Role.expiredAt_eq_true.mpr ⟨holder, expiry, claimedAtM, reached.trans clockAtM⟩)]
    simp
  exact (never (m + 1) (by omega)).1 freed

/-- While a lease is held and the owner's clock is below its expiry, one step keeps the lease
held at the same epoch, or completes the task by the holder; a done task stays done. -/
theorem lease_step_holds {s : Owner X W} {task : X} {who : W} {expiry token : ℕ}
    (holds : (s.role task = .claimed who expiry ∧ s.epoch task = token) ∨ s.role task = .done who)
    (clockBelow : s.clock < expiry) (r : Request X W) :
    ((step duration s r).role task = .claimed who expiry ∧ (step duration s r).epoch task = token) ∨
      (step duration s r).role task = .done who := by
  have notLive : s.role task ≠ .live := by
    rcases holds with ⟨isClaimed, _⟩ | isDone
    · rw [isClaimed]; exact fun h => by cases h
    · rw [isDone]; exact fun h => by cases h
  cases r with
  | claim w t =>
      simp only [step]
      split_ifs with live
      · have : t ≠ task := fun same => by subst same; exact notLive live
        simpa [Function.update_of_ne (Ne.symm this)] using holds
      · exact holds
  | tick => exact holds
  | expire t =>
      simp only [step]
      split_ifs with expired
      · have : t ≠ task := fun same => by
          subst same
          rcases holds with ⟨isClaimed, _⟩ | isDone
          · rw [isClaimed] at expired
            simp only [Role.expiredAt, decide_eq_true_eq] at expired
            omega
          · rw [isDone] at expired; simp [Role.expiredAt] at expired
        simpa [Function.update_of_ne (Ne.symm this)] using holds
      · exact holds
  | effect w t e =>
      simp only [step]
      split_ifs with current
      · by_cases same : t = task
        · subst same
          right
          obtain ⟨⟨_, holderIs⟩, _⟩ := And.imp_left Role.heldBy_eq_true.mp current
          rcases holds with ⟨isClaimed, _⟩ | isDone
          · rw [isClaimed, Role.claimed.injEq] at holderIs
            simp [holderIs.1]
          · rw [isDone] at holderIs; cases holderIs
        · simpa [Function.update_of_ne (Ne.symm same)] using holds
      · exact holds

/-- **A timely worker completes the task.** Its claim reaches the owner at `n` while the task is
live; its effect, with the token it received, reaches the owner at `m` before the owner's clock
reaches the lease's expiry. -/
theorem timely_worker_completes (requests : ℕ → Request X W) {task : X} {who : W} {n m : ℕ}
    (isLive : (trace duration requests n).role task = .live)
    (claimAtN : requests n = .claim who task) (later : n < m)
    (effectAtM : requests m =
      .effect who task ((trace duration requests n).epoch task + 1))
    (timely : (trace duration requests m).clock < (trace duration requests n).clock + duration) :
    (trace duration requests (m + 1)).role task = .done who := by
  set expiry := (trace duration requests n).clock + duration
  set token := (trace duration requests n).epoch task + 1
  have granted : (trace duration requests (n + 1)).role task = .claimed who expiry ∧
      (trace duration requests (n + 1)).epoch task = token := by
    show (step duration (trace duration requests n) (requests n)).role task = _ ∧
      (step duration (trace duration requests n) (requests n)).epoch task = _
    rw [claimAtN]
    simp only [step, if_pos isLive]
    simp [expiry, token]
  -- Until `m`, the lease is held at the token's epoch, or the task is done by `who`.
  have holds : ∀ k, n + 1 ≤ k → k ≤ m →
      ((trace duration requests k).role task = .claimed who expiry ∧
        (trace duration requests k).epoch task = token) ∨
      (trace duration requests k).role task = .done who := by
    intro k low
    induction k, low using Nat.le_induction with
    | base => intro _; exact Or.inl granted
    | succ k' low ih =>
        intro high
        exact lease_step_holds duration (ih (by omega))
          (lt_of_le_of_lt (clock_mono duration requests (by omega)) timely) (requests k')
  have atM := holds m (by omega) le_rfl
  show (step duration (trace duration requests m) (requests m)).role task = _
  rw [effectAtM]
  rcases atM with ⟨isClaimed, sameEpoch⟩ | isDone
  · have current : Current (trace duration requests m) who task token :=
      ⟨Role.heldBy_eq_true.mpr ⟨expiry, isClaimed⟩, sameEpoch⟩
    simp only [step, if_pos current]
    simp
  · have notCurrent : ¬ Current (trace duration requests m) who task token := fun current => by
      rw [Current, isDone] at current; simp [Role.heldBy] at current
    simp only [step, if_neg notCurrent]
    exact isDone

/-- **Eventually processed**: with ticks and timer firings infinitely often, and a worker whose
claim is served at some moment the task is live and whose effect then arrives in time, the task is
done. -/
theorem eventually_done (requests : ℕ → Request X W) (task : X)
    (ticks : ∀ n, ∃ m ≥ n, requests m = .tick)
    (expiries : ∀ n, ∃ m ≥ n, requests m = .expire task)
    (fairService : ∀ n, (trace duration requests n).role task = .live →
      ∃ k ≥ n, ∃ who, (trace duration requests k).role task = .live ∧
        requests k = .claim who task ∧ ∃ m > k,
          requests m = .effect who task ((trace duration requests k).epoch task + 1) ∧
          (trace duration requests m).clock < (trace duration requests k).clock + duration) :
    ∃ m who, (trace duration requests m).role task = .done who := by
  obtain ⟨n, -, liveOrDone⟩ := returns_or_done duration requests task ticks expiries 0
  rcases liveOrDone with isLive | ⟨who, isDone⟩
  · obtain ⟨k, -, who, liveAtK, claimAtK, m, later, effectAtM, timely⟩ := fairService n isLive
    exact ⟨m + 1, who,
      timely_worker_completes duration requests liveAtK claimAtK later effectAtM timely⟩
  · exact ⟨n, who, isDone⟩

/-! ## Controls -/

namespace Controls

/-- One task; workers `true` (first holder) and `false` (second holder). -/
def staleRun : List (Request Unit Bool) :=
  [.claim true (), .tick, .expire (), .claim false (), .effect true () 1]

/-- **The stale worker is fenced**: worker `true` held epoch `1`, its lease expired and the task was
granted to `false` at epoch `3`; the late effect of `true` is rejected, the effect of `false` is
accepted. -/
theorem stale_fenced :
    (runList 1 Owner.start staleRun).effects = [] ∧
      (runList 1 Owner.start (staleRun ++ [.effect false () 3])).effects = [((), false, 3)] := by
  decide

/-- An owner without fencing: an effect is accepted whenever the task is claimed. -/
def stepUnfenced (s : Owner Unit Bool) : Request Unit Bool → Owner Unit Bool
  | .effect who task epoch =>
      match s.role task with
      | .claimed _ _ =>
          { s with role := Function.update s.role task (.done who),
                   effects := s.effects ++ [(task, who, epoch)] }
      | _ => s
  | r => step 1 s r

/-- **Without fencing the stale effect is accepted**, while worker `false` holds the lease. -/
theorem unfenced_accepts_stale :
    (staleRun.foldl stepUnfenced Owner.start).effects = [((), true, 1)] ∧
      (runList 1 Owner.start (staleRun.take 4)).role () = .claimed false 2 := by
  decide

/-- Worker `true` claims and crashes; afterwards only ticks and claims of worker `false` arrive,
and no timer fires. -/
def crashedHolder (n : ℕ) : Request Unit Bool :=
  if n = 0 then .claim true () else if n % 2 = 0 then .tick else .claim false ()

/-- **Without expiry a crashed holder blocks the task forever.** -/
theorem no_expiry_blocks (n : ℕ) : 1 ≤ n → (trace 1 crashedHolder n).role () = .claimed true 1 := by
  intro positive
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | pos
      · decide
      · have held := ih pos
        have request : crashedHolder n = if n % 2 = 0 then .tick else .claim false () := by
          simp [crashedHolder, show n ≠ 0 by omega]
        show (step 1 (trace 1 crashedHolder n) (crashedHolder n)).role () = _
        rw [request]
        split_ifs
        · exact held
        · simp only [step]
          rw [if_neg (by rw [held]; exact fun h => by cases h)]
          exact held

/-- A faulty worker `true` claims whenever the task is live and never completes; the correct
worker `false` asks right after it; then the clock ticks and the timer fires. -/
def faultyFirst (n : ℕ) : Request Unit Bool :=
  match n % 4 with
  | 0 => .claim true ()
  | 1 => .claim false ()
  | 2 => .tick
  | _ => .expire ()

theorem claim_of_live {s : Owner Unit Bool} (who : Bool) (isLive : s.role () = .live) :
    (step 1 s (.claim who ())).role () = .claimed who (s.clock + 1) ∧
      (step 1 s (.claim who ())).clock = s.clock ∧
        (step 1 s (.claim who ())).grants = s.grants ++ [((), who, s.epoch () + 1)] := by
  simp [step, isLive]

theorem claim_of_claimed {s : Owner Unit Bool} (who : Bool) {holder : Bool} {expiry : ℕ}
    (isClaimed : s.role () = .claimed holder expiry) : step 1 s (.claim who ()) = s := by
  simp [step, isClaimed]

theorem expire_due {s : Owner Unit Bool} {holder : Bool} {expiry : ℕ}
    (isClaimed : s.role () = .claimed holder expiry) (due : expiry ≤ s.clock) :
    (step 1 s (.expire ())).role () = .live ∧ (step 1 s (.expire ())).clock = s.clock ∧
      (step 1 s (.expire ())).grants = s.grants := by
  simp [step, isClaimed, Role.expiredAt, due]

theorem faultyFirst_requests (k : ℕ) :
    faultyFirst (4 * k) = .claim true () ∧ faultyFirst (4 * k + 1) = .claim false () ∧
      faultyFirst (4 * k + 2) = .tick ∧ faultyFirst (4 * k + 3) = .expire () := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [faultyFirst, Nat.add_mod]

/-- The four phases of one period: live, claimed by the faulty worker, the correct worker refused,
the clock ticks, the timer frees the task. -/
theorem faultyFirst_period (k : ℕ) :
    let at₀ := trace 1 faultyFirst (4 * k)
    at₀.role () = .live ∧ at₀.clock = k ∧ (∀ g ∈ at₀.grants, g.2.1 = true) := by
  induction k with
  | zero => simp [trace, Owner.start]
  | succ k ih =>
      obtain ⟨isLive, clockIs, grantsTrue⟩ := ih
      obtain ⟨r₀, r₁, r₂, r₃⟩ := faultyFirst_requests k
      set at₀ := trace 1 faultyFirst (4 * k)
      have at₁ : trace 1 faultyFirst (4 * k + 1) = step 1 at₀ (.claim true ()) := by
        show step 1 at₀ (faultyFirst (4 * k)) = _; rw [r₀]
      obtain ⟨role₁, clock₁, grants₁⟩ := claim_of_live true isLive
      have at₂ : trace 1 faultyFirst (4 * k + 2) = step 1 at₀ (.claim true ()) := by
        show step 1 (trace 1 faultyFirst (4 * k + 1)) (faultyFirst (4 * k + 1)) = _
        rw [r₁, at₁, claim_of_claimed false role₁]
      have at₃ : trace 1 faultyFirst (4 * k + 3) = step 1 (step 1 at₀ (.claim true ())) .tick := by
        show step 1 (trace 1 faultyFirst (4 * k + 2)) (faultyFirst (4 * k + 2)) = _
        rw [r₂, at₂]
      have at₄ : trace 1 faultyFirst (4 * (k + 1)) =
          step 1 (step 1 (step 1 at₀ (.claim true ())) .tick) (.expire ()) := by
        rw [show 4 * (k + 1) = 4 * k + 3 + 1 by ring]
        show step 1 (trace 1 faultyFirst (4 * k + 3)) (faultyFirst (4 * k + 3)) = _
        rw [r₃, at₃]
      obtain ⟨role₄, clock₄, grants₄⟩ := expire_due (s := step 1 (step 1 at₀ (.claim true ())) .tick)
        (holder := true) (expiry := at₀.clock + 1) role₁ (by
          show at₀.clock + 1 ≤ (step 1 at₀ (.claim true ())).clock + 1
          rw [clock₁])
      refine ⟨by rw [at₄, role₄], ?_, ?_⟩
      · rw [at₄, clock₄]
        show (step 1 at₀ (.claim true ())).clock + 1 = k + 1
        rw [clock₁, clockIs]
      · rw [at₄, grants₄]
        show ∀ g ∈ (step 1 at₀ (.claim true ())).grants, g.2.1 = true
        intro g member
        rw [grants₁, List.mem_append, List.mem_singleton] at member
        rcases member with old | rfl
        · exact grantsTrue g old
        · rfl

/-- **Starvation**: with expiry but without fair service, the correct worker is never granted the
task and the task is never done, although that worker asks infinitely often. -/
theorem starvation (n : ℕ) :
    (∀ who, (trace 1 faultyFirst n).role () ≠ .done who) ∧
      ∀ g ∈ (trace 1 faultyFirst n).grants, g.2.1 = true := by
  obtain ⟨k, r, rLt, rfl⟩ : ∃ k r, r < 4 ∧ n = 4 * k + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 4).symm⟩
  obtain ⟨isLive, _, grantsTrue⟩ := faultyFirst_period k
  obtain ⟨r₀, r₁, r₂, _⟩ := faultyFirst_requests k
  set at₀ := trace 1 faultyFirst (4 * k)
  obtain ⟨role₁, _, grants₁⟩ := claim_of_live true isLive
  have grantsAfter : ∀ g ∈ (step 1 at₀ (.claim true ())).grants, g.2.1 = true := by
    intro g member
    rw [grants₁, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact grantsTrue g old
    · rfl
  have at₁ : trace 1 faultyFirst (4 * k + 1) = step 1 at₀ (.claim true ()) := by
    show step 1 at₀ (faultyFirst (4 * k)) = _; rw [r₀]
  have at₂ : trace 1 faultyFirst (4 * k + 2) = step 1 at₀ (.claim true ()) := by
    show step 1 (trace 1 faultyFirst (4 * k + 1)) (faultyFirst (4 * k + 1)) = _
    rw [r₁, at₁, claim_of_claimed false role₁]
  have at₃ : trace 1 faultyFirst (4 * k + 3) = step 1 (step 1 at₀ (.claim true ())) .tick := by
    show step 1 (trace 1 faultyFirst (4 * k + 2)) (faultyFirst (4 * k + 2)) = _
    rw [r₂, at₂]
  have notDoneClaimed : ∀ who, Role.claimed true (at₀.clock + 1) ≠ .done who := fun _ h => by cases h
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
  · show (∀ who, at₀.role () ≠ .done who) ∧ ∀ g ∈ at₀.grants, g.2.1 = true
    refine ⟨fun who => ?_, grantsTrue⟩
    rw [isLive]
    exact fun h => by cases h
  · rw [at₁]; exact ⟨fun who => role₁ ▸ notDoneClaimed who, grantsAfter⟩
  · rw [at₂]; exact ⟨fun who => role₁ ▸ notDoneClaimed who, grantsAfter⟩
  · rw [at₃]; exact ⟨fun who => role₁ ▸ notDoneClaimed who, grantsAfter⟩

/-- An owner that checks a holder name written in the request instead of the authenticated
sender: `named sender claimedName task epoch`. -/
def stepNamed (s : Owner Unit Bool) (sender claimedName : Bool) (epoch : ℕ) : Owner Unit Bool :=
  if Current s claimedName () epoch then
    { s with role := Function.update s.role () (.done sender),
             effects := s.effects ++ [((), sender, epoch)] }
  else s

/-- **Names are not authority**: worker `false` holds the lease at epoch `1`; worker `true`
writes the holder's name and the epoch, which it can guess, and completes the task under the
named check. The authenticated check refuses the same request. -/
theorem named_impersonation :
    let s := runList 1 Owner.start [.claim false ()]
    (stepNamed s true false 1).effects = [((), true, 1)] ∧
      (step 1 s (.effect true () 1)).effects = [] := by
  decide

/-! ### Current effects -/

/-- The owner state in which `true` holds the lease until `5`, in epoch `2`. -/
def heldByTrue : Owner Unit Bool := ⟨fun _ => .claimed true 5, fun _ => 2, 0, [], []⟩

/-- **Positive control**: the holder's effect with the task's epoch is current. -/
theorem holder_current : Current heldByTrue true () 2 := by decide

/-- **Negative control**: the holder's effect with an older epoch is stale. -/
theorem stale_epoch_not_current : ¬ Current heldByTrue true () 1 := by decide

/-- **Negative control**: an effect of a process that does not hold the lease is not current,
though its epoch is the task's. -/
theorem nonholder_not_current : ¬ Current heldByTrue false () 2 := by decide

end Controls

/-! ## Effects outside the owner -/

namespace FencedResource

variable {X : Type u} [DecidableEq X] {V : Type v}

/-- A resource that remembers, per task, the largest epoch it has accepted, and the writes. -/
structure Resource (X : Type u) (V : Type v) where
  highest : X → ℕ
  writes : List (X × ℕ × V)

/-- A fenced write: accepted when its epoch is at least the largest seen. -/
def write (r : Resource X V) (task : X) (epoch : ℕ) (value : V) : Resource X V :=
  if r.highest task ≤ epoch then
    ⟨Function.update r.highest task epoch, r.writes ++ [(task, epoch, value)]⟩
  else r

/-- The epochs of the accepted writes to one task, in order. -/
def epochsOf (r : Resource X V) (task : X) : List ℕ :=
  (r.writes.filter fun w => w.1 = task).map fun w => w.2.1

/-- The resource's invariant: accepted epochs per task are sorted and bounded by the highest. -/
def Sorted' (r : Resource X V) : Prop :=
  ∀ task, (epochsOf r task).Pairwise (· ≤ ·) ∧ ∀ e ∈ epochsOf r task, e ≤ r.highest task

theorem write_sorted {r : Resource X V} (sorted : Sorted' r) (task : X) (epoch : ℕ) (value : V) :
    Sorted' (write r task epoch value) := by
  unfold write
  split_ifs with fresh
  · intro t
    obtain ⟨pairwise, bounded⟩ := sorted t
    by_cases same : t = task
    · subst same
      simp only [epochsOf, List.filter_append, List.filter_cons, List.filter_nil, decide_true,
        if_true, List.map_append, List.map_cons, List.map_nil, Function.update_self] at pairwise bounded ⊢
      refine ⟨List.pairwise_append.mpr ⟨pairwise, by simp, fun a member b inB => ?_⟩, fun e member => ?_⟩
      · rw [List.mem_singleton] at inB; subst inB
        exact (bounded a member).trans fresh
      · rcases List.mem_append.mp member with old | new
        · exact (bounded e old).trans fresh
        · rw [List.mem_singleton] at new; exact new.le
    · simp only [epochsOf] at pairwise bounded ⊢
      simpa [List.filter_append, Ne.symm same, Function.update_of_ne same] using
        And.intro pairwise bounded
  · exact sorted

/-- **Fenced writes never go back to an older epoch**, for every sequence of writes. -/
theorem epochs_sorted (writes : List (X × ℕ × V)) (task : X) :
    (epochsOf (writes.foldl (fun r w => write r w.1 w.2.1 w.2.2) (⟨fun _ => 0, []⟩ : Resource X V))
      task).Pairwise (· ≤ ·) := by
  suffices ∀ (r : Resource X V), Sorted' r →
      Sorted' (writes.foldl (fun r w => write r w.1 w.2.1 w.2.2) r) from
    (this _ fun t => by simp [epochsOf]) task |>.1
  induction writes with
  | nil => exact fun _ sorted => sorted
  | cons w rest ih => exact fun r sorted => ih _ (write_sorted sorted w.1 w.2.1 w.2.2)

/-- **Without the check a stale write lands after a newer one.** -/
theorem unfenced_stale_lands :
    let blind := fun (writes : List (Unit × ℕ × ℕ)) (w : Unit × ℕ × ℕ) => writes ++ [w]
    ([((), 3, 30), ((), 1, 10)].foldl blind []).map (fun w => w.2.1) = [3, 1] ∧
      ([((), 3, 30), ((), 1, 10)].foldl (fun r w => write r w.1 w.2.1 w.2.2)
        (⟨fun _ => 0, []⟩ : Resource Unit ℕ)).writes = [((), 3, 30)] := by
  decide

/-- A deduplicating resource: at most one write per task. -/
def writeOnce [DecidableEq V] (writes : List (X × ℕ × V)) (w : X × ℕ × V) : List (X × ℕ × V) :=
  if w.1 ∈ writes.map Prod.fst then writes else writes ++ [w]

/-- **Deduplication by task gives at most one write per task.** -/
theorem dedup_at_most_one [DecidableEq V] (writes : List (X × ℕ × V)) :
    ((writes.foldl writeOnce []).map Prod.fst).Nodup := by
  suffices ∀ start : List (X × ℕ × V), (start.map Prod.fst).Nodup →
      ((writes.foldl writeOnce start).map Prod.fst).Nodup from this [] List.nodup_nil
  induction writes with
  | nil => exact fun _ h => h
  | cons w rest ih =>
      intro start nodup
      apply ih
      unfold writeOnce
      split_ifs with seen
      · exact nodup
      · rw [List.map_append]
        exact nodup_append_singleton nodup seen

/-- A sink that fences and deduplicates: a write is accepted when its task was never written and its
epoch is not older than the largest seen. -/
def writeKeyed (r : Resource X V) (task : X) (epoch : ℕ) (value : V) : Resource X V :=
  if task ∈ r.writes.map Prod.fst then r else write r task epoch value

theorem write_tasks (r : Resource X V) (task : X) (epoch : ℕ) (value : V) :
    (write r task epoch value).writes = r.writes ∨
      (write r task epoch value).writes = r.writes ++ [(task, epoch, value)] := by
  unfold write
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **A fenced and keyed sink applies each task at most once.** Exactly-once external effects need
the key at the effect's boundary; fencing alone does not give them (`fencing_allows_two`). -/
theorem fenced_keyed_once (writes : List (X × ℕ × V)) :
    ((writes.foldl (fun r w => writeKeyed r w.1 w.2.1 w.2.2) (⟨fun _ => 0, []⟩ : Resource X V)).writes.map
      Prod.fst).Nodup := by
  suffices ∀ r : Resource X V, (r.writes.map Prod.fst).Nodup →
      ((writes.foldl (fun r w => writeKeyed r w.1 w.2.1 w.2.2) r).writes.map Prod.fst).Nodup from
    this _ List.nodup_nil
  induction writes with
  | nil => exact fun _ h => h
  | cons w rest ih =>
      intro r nodup
      apply ih
      show ((writeKeyed r w.1 w.2.1 w.2.2).writes.map Prod.fst).Nodup
      unfold writeKeyed
      split_ifs with seen
      · exact nodup
      · rcases write_tasks r w.1 w.2.1 w.2.2 with same | appended
        · rw [same]; exact nodup
        · rw [appended, List.map_append]
          exact nodup_append_singleton nodup seen

/-- Fencing alone allows one write per epoch: two holders of successive epochs both write. -/
theorem fencing_allows_two :
    ([((), 1, 10), ((), 3, 30)].foldl (fun r w => write r w.1 w.2.1 w.2.2)
      (⟨fun _ => 0, []⟩ : Resource Unit ℕ)).writes = [((), 1, 10), ((), 3, 30)] := by
  decide

end FencedResource

end Mettapedia.GSLT.Coordination.FencedLeases
