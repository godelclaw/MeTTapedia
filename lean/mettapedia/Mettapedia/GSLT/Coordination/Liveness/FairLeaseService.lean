import Mettapedia.GSLT.Timing.TimedLeases
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.FairRuns

/-!
# Every task is eventually done: fair claim service, eventual expiry, eventual synchrony

`FencedLeases.eventually_done` proves that a task is done when the owner's clock ticks, the timer
fires, and **some timely claim is served while the task is live**: a hypothesis on the arrival
order of requests. `FencedLeases.Controls.starvation` shows that without it a faulty worker that
always claims first starves a correct one. `Timing.TimedLeases` lets the owner read a real clock
(`catchUp`) and proves that one attempt completes when timing behaves (`timely_of_rates`). This
module joins the two with a **fair service policy at the owner**, and proves the infinite-run
theorem in which the arrival order is adversarial.

## The fair owner

The owner of `FencedLeases` with a **queue of claimants per task** (`FairOwner`). A claim enqueues
its sender once (`handle`); the owner's own **serve** event grants a live task to the head of its
queue, by the claim step of `FencedLeases` (first come, first served: aging by request time).
Requests arrive at real times; before handling one the owner's clock catches up with its real clock
(`timedHandle`, as in `Timing.TimedLeases`).

## Safety, inherited

Every run of the fair owner is a run of the owner of `FencedLeases` (`fairTrace_refines`): catching
up is ticking, a serve is a claim, and an enqueue changes nothing there. So at most one effect is
accepted per task (`fair_effects_nodup`), for every clock, every arrival order and every policy of
faulty workers.

## Liveness (`fifo_eventually_done`)

The task is done if:

* **eventual expiry**: the owner's clock passes every bound (`clockPasses`, which follows from a
  positive lower rate, `clockPasses_of_rates`) and its timer fires infinitely often (`expiries`);
* **fair service**: the owner serves the task infinitely often (`serves`), first come first served;
* **one correct worker**: some worker claims the task once after stabilization (`asksAfter`), and
  answers every grant it receives after stabilization with its token within `R` real ticks
  (`answers`);
* **eventual synchrony**: from real time `gst` on the owner's clock runs at most at `fast / den`,
  and `fast · R < den · duration` (`rates`, `margin`).

Faulty workers may claim at any time, crash, hold leases and never answer. No ticks arrive; the
owner's clock is its real clock.

The proof: a lease always ends, by expiry or by completion (`eventually_live`); a live task with a
waiting claimant is granted at the next serve (`grant_after`); every grant to another worker moves
the correct worker one place up the queue, and arrivals queue behind it (`queue_step`); so it is
granted, after stabilization, and its answer is accepted before the lease expires
(`granted_done`).

Compared with `FencedLeases.eventually_done`, the hypothesis "some timely claim is served at a live
moment" (a property of the arrival order) is replaced by a property of the owner (it serves in
order) and of one worker (it asks once and answers in time), against arbitrary faulty workers.
Each remaining hypothesis is needed: without expiry a crashed holder blocks forever
(`FencedLeases.Controls.no_expiry_blocks`); without fair service a faulty first claimer starves a
correct worker (`FencedLeases.Controls.starvation`); without eventual synchrony every duration
policy fails (`Timing.TimedLeases.Controls.async_never_completes`), and a fixed duration fails
under an unknown bound (`Timing.TimedLeases.Controls.fixed_duration_fails`).

`Controls.fifo_instance` is a run that meets every hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.Liveness.FairLeaseService

open Mettapedia.GSLT.Coordination.FencedLeases
open Mettapedia.GSLT.Timing
open Mettapedia.GSLT.Timing.TimedLeases
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
  (InfinitelyOften not_infinitelyOften_of_descent)

universe u v

variable {X : Type u} [DecidableEq X] {W : Type v} [DecidableEq W]

/-- An event at the owner: a request from the network, or the owner's own service of a task. -/
inductive Event (X : Type u) (W : Type v) where
  | request (r : Request X W)
  | serve (task : X)

/-- The owner of `FencedLeases` with a queue of claimants per task. -/
structure FairOwner (X : Type u) (W : Type v) where
  base : Owner X W
  queue : X → List W

/-- Every task live at epoch `0`, nothing granted, no claimant waiting. -/
def FairOwner.start : FairOwner X W := ⟨Owner.start, fun _ => []⟩

variable (duration : ℕ)

/-- One event at the fair owner. A claim enqueues its sender once; a serve grants a live task to
the head of its queue; every other request is the owner's step of `FencedLeases`. -/
def handle (s : FairOwner X W) : Event X W → FairOwner X W
  | .request (.claim who task) =>
      if who ∈ s.queue task then s
      else ⟨s.base, Function.update s.queue task (s.queue task ++ [who])⟩
  | .request .tick => ⟨step duration s.base .tick, s.queue⟩
  | .request (.expire task) => ⟨step duration s.base (.expire task), s.queue⟩
  | .request (.effect who task epoch) => ⟨step duration s.base (.effect who task epoch), s.queue⟩
  | .serve task =>
      match s.queue task with
      | [] => s
      | w :: rest =>
          if s.base.role task = .live then
            ⟨step duration s.base (.claim w task), Function.update s.queue task rest⟩
          else s

/-- An event arriving at a real time: the owner's clock catches up, then it handles the event. -/
def timedHandle (c : Clock) (s : FairOwner X W) (arrival : ℕ × Event X W) : FairOwner X W :=
  handle duration ⟨catchUp s.base (c arrival.1), s.queue⟩ arrival.2

/-- The run of the fair owner over an infinite sequence of arrivals. -/
def fairTrace (c : Clock) (arrivals : ℕ → ℕ × Event X W) : ℕ → FairOwner X W
  | 0 => FairOwner.start
  | n + 1 => timedHandle duration c (fairTrace c arrivals n) (arrivals n)

/-! ## Safety, inherited -/

/-- The owner's part of an event is unchanged, or one owner step. -/
theorem handle_base_cases (s : FairOwner X W) (e : Event X W) :
    (handle duration s e).base = s.base ∨ ∃ q, (handle duration s e).base = step duration s.base q := by
  cases e with
  | request r =>
      cases r with
      | claim who task =>
          left
          simp only [handle]
          split_ifs <;> rfl
      | tick => exact Or.inr ⟨.tick, rfl⟩
      | expire task => exact Or.inr ⟨.expire task, rfl⟩
      | effect who task epoch => exact Or.inr ⟨.effect who task epoch, rfl⟩
  | serve task =>
      cases queue : s.queue task with
      | nil => left; simp [handle, queue]
      | cons w rest =>
          simp only [handle, queue]
          split_ifs
          · exact Or.inr ⟨.claim w task, rfl⟩
          · exact Or.inl rfl

/-- **The fair owner refines the owner of `FencedLeases`**: its owner part is a run of
`runList` from the start. -/
theorem fairTrace_refines (c : Clock) (arrivals : ℕ → ℕ × Event X W) :
    ∀ n, ∃ requests, (fairTrace duration c arrivals n).base = runList duration Owner.start requests
  | 0 => ⟨[], rfl⟩
  | n + 1 => by
      obtain ⟨before, eq⟩ := fairTrace_refines c arrivals n
      have stepEq : (fairTrace duration c arrivals (n + 1)).base =
          (handle duration ⟨catchUp (fairTrace duration c arrivals n).base (c (arrivals n).1),
            (fairTrace duration c arrivals n).queue⟩ (arrivals n).2).base := rfl
      rcases handle_base_cases duration ⟨catchUp (fairTrace duration c arrivals n).base
          (c (arrivals n).1), (fairTrace duration c arrivals n).queue⟩ (arrivals n).2 with same | ⟨q, next⟩
      · rw [stepEq, same]
        show ∃ requests, catchUp (fairTrace duration c arrivals n).base (c (arrivals n).1) = _
        rw [catchUp_eq_runList duration, eq, ← runList_append]
        exact ⟨_, rfl⟩
      · rw [stepEq, next]
        show ∃ requests, step duration (catchUp (fairTrace duration c arrivals n).base
          (c (arrivals n).1)) q = _
        rw [catchUp_eq_runList duration, eq, ← runList_append]
        exact ⟨_, (runList_append duration Owner.start _ [q]).symm⟩

/-- **At most one effect per task**, for every clock and every arrival order. -/
theorem fair_effects_nodup (c : Clock) (arrivals : ℕ → ℕ × Event X W) (n : ℕ) :
    ((fairTrace duration c arrivals n).base.effects.map Prod.fst).Nodup := by
  obtain ⟨requests, eq⟩ := fairTrace_refines duration c arrivals n
  rw [eq]
  exact effects_nodup duration requests

/-! ## Steps of the fair owner -/

section Steps

variable {duration}

/-- Only ticks move the owner's clock. -/
theorem handle_clock (s : FairOwner X W) {e : Event X W} (notTick : e ≠ .request .tick) :
    (handle duration s e).base.clock = s.base.clock := by
  cases e with
  | request r =>
      cases r with
      | claim who task => simp only [handle]; split_ifs <;> rfl
      | tick => exact absurd rfl notTick
      | expire task => exact step_clock duration s.base (by simp)
      | effect who task epoch => exact step_clock duration s.base (by simp)
  | serve task =>
      cases queue : s.queue task with
      | nil => simp [handle, queue]
      | cons w rest =>
          simp only [handle, queue]
          split_ifs
          · exact step_clock duration s.base (by simp)
          · rfl

/-- From a live task, an event other than a serve of that task with a waiting claimant leaves it
live. -/
theorem handle_live (s : FairOwner X W) {task : X} (isLive : s.base.role task = .live)
    {e : Event X W} (notGrant : ¬ (e = .serve task ∧ s.queue task ≠ [])) :
    (handle duration s e).base.role task = .live := by
  cases e with
  | request r =>
      cases r with
      | claim who t => simp only [handle]; split_ifs <;> exact isLive
      | tick => exact isLive
      | expire t =>
          show (step duration s.base (.expire t)).role task = .live
          simp only [step]
          split_ifs with expired
          · by_cases same : t = task
            · subst same; rw [isLive] at expired; simp [Role.expiredAt] at expired
            · simp [Function.update_of_ne (Ne.symm same), isLive]
          · exact isLive
      | effect who t epoch =>
          show (step duration s.base (.effect who t epoch)).role task = .live
          simp only [step]
          split_ifs with current
          · by_cases same : t = task
            · subst same
              have := current.1
              rw [isLive] at this
              simp [Role.heldBy] at this
            · simp [Function.update_of_ne (Ne.symm same), isLive]
          · exact isLive
  | serve t =>
      cases queue : s.queue t with
      | nil => simp only [handle, queue]; exact isLive
      | cons w rest =>
          simp only [handle, queue]
          split_ifs with tLive
          · by_cases same : t = task
            · subst same
              exact absurd ⟨rfl, by rw [queue]; simp⟩ notGrant
            · show (step duration s.base (.claim w t)).role task = .live
              simp [step, tLive, Function.update_of_ne (Ne.symm same), isLive]
          · exact isLive

/-- A grant: the serve of a live task gives it to the head of its queue at the owner's clock plus
the duration, one epoch on. -/
theorem handle_grant (s : FairOwner X W) {task : X} {w : W} {rest : List W}
    (isLive : s.base.role task = .live) (queue : s.queue task = w :: rest) :
    (handle duration s (.serve task)).base.role task = .claimed w (s.base.clock + duration) ∧
      (handle duration s (.serve task)).base.epoch task = s.base.epoch task + 1 ∧
      (handle duration s (.serve task)).queue task = rest := by
  simp [handle, queue, isLive, step]

/-- A claimant stays in the queue, at a place that does not go down, unless it is granted; every
grant to another claimant moves it one place up. -/
theorem queue_step (s : FairOwner X W) {task : X} {w : W} (waiting : w ∈ s.queue task)
    (e : Event X W) (notGranted : ¬ (e = .serve task ∧ s.base.role task = .live ∧
      ∃ rest, s.queue task = w :: rest)) :
    w ∈ (handle duration s e).queue task ∧
      List.idxOf w ((handle duration s e).queue task) ≤ List.idxOf w (s.queue task) ∧
      ((e = .serve task ∧ s.base.role task = .live) →
        ((handle duration s e).queue task).idxOf w < (s.queue task).idxOf w) := by
  cases e with
  | request r =>
      have serveNo : ¬ (Event.request r = Event.serve task ∧ s.base.role task = .live) :=
        fun h => by cases h.1
      cases r with
      | claim who t =>
          simp only [handle]
          split_ifs with present
          · exact ⟨waiting, le_rfl, fun h => h.1.elim⟩
          · by_cases same : t = task
            · subst same
              simp only [Function.update_self]
              exact ⟨List.mem_append_left _ waiting, by rw [List.idxOf_append_of_mem waiting],
                fun h => h.1.elim⟩
            · simp only [Function.update_of_ne (Ne.symm same)]
              exact ⟨waiting, le_rfl, fun h => h.1.elim⟩
      | tick => exact ⟨waiting, le_rfl, fun h => absurd h serveNo⟩
      | expire t => exact ⟨waiting, le_rfl, fun h => absurd h serveNo⟩
      | effect who t epoch => exact ⟨waiting, le_rfl, fun h => absurd h serveNo⟩
  | serve t =>
      cases queue : s.queue t with
      | nil =>
          simp only [handle, queue]
          refine ⟨waiting, le_rfl, fun ⟨same, _⟩ => ?_⟩
          cases same
          rw [queue] at waiting
          cases waiting
      | cons h rest =>
          simp only [handle, queue]
          split_ifs with tLive
          · by_cases same : t = task
            · subst same
              have different : h ≠ w := fun hw => notGranted ⟨rfl, tLive, rest, by rw [queue, hw]⟩
              rw [queue] at waiting
              have inRest : w ∈ rest := by
                rcases List.mem_cons.mp waiting with first | later
                · exact absurd first.symm different
                · exact later
              simp only [Function.update_self, queue]
              rw [List.idxOf_cons_ne rest different]
              exact ⟨inRest, Nat.le_succ _, fun _ => Nat.lt_succ_self _⟩
            · simp only [Function.update_of_ne (Ne.symm same)]
              exact ⟨waiting, le_rfl, fun ⟨eq, _⟩ => absurd (Event.serve.inj eq) same⟩
          · refine ⟨waiting, le_rfl, fun ⟨eq, isLive⟩ => ?_⟩
            have same := Event.serve.inj eq
            subst same
            exact absurd isLive tLive

/-- A claim puts its sender in the queue. -/
theorem queue_of_claim (s : FairOwner X W) (w : W) (task : X) :
    w ∈ (handle duration s (.request (.claim w task))).queue task := by
  simp only [handle]
  split_ifs with present
  · exact present
  · simp

end Steps

/-! ## Liveness -/

section Liveness

variable {duration} {c : Clock} {arrivals : ℕ → ℕ × Event X W}

/-- The owner's clock is the latest reading of its real clock, when no ticks arrive. -/
theorem fairTrace_clock (noTicks : ∀ n, (arrivals n).2 ≠ .request .tick) (n : ℕ) :
    (fairTrace duration c arrivals (n + 1)).base.clock =
      max (fairTrace duration c arrivals n).base.clock (c (arrivals n).1) :=
  handle_clock _ (noTicks n)

theorem fairTrace_clock_le (noTicks : ∀ n, (arrivals n).2 ≠ .request .tick)
    (timesMono : Monotone fun n => (arrivals n).1) (clockMono : Monotone c) :
    ∀ n, (fairTrace duration c arrivals n).base.clock ≤ c (arrivals n).1 := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      rw [fairTrace_clock noTicks n]
      exact max_le (ih.trans (clockMono (timesMono (Nat.le_succ n))))
        (clockMono (timesMono (Nat.le_succ n)))

/-- A grant of `task` at time `n` to some claimant. -/
def GrantAt (duration : ℕ) (c : Clock) (arrivals : ℕ → ℕ × Event X W) (task : X) (n : ℕ) : Prop :=
  (arrivals n).2 = .serve task ∧ (fairTrace duration c arrivals n).base.role task = .live ∧
    (fairTrace duration c arrivals n).queue task ≠ []

/-- A grant of `task` at time `n` to `w`. -/
def GrantsTo (duration : ℕ) (c : Clock) (arrivals : ℕ → ℕ × Event X W) (task : X) (w : W) (n : ℕ) :
    Prop :=
  (arrivals n).2 = .serve task ∧ (fairTrace duration c arrivals n).base.role task = .live ∧
    ∃ rest, (fairTrace duration c arrivals n).queue task = w :: rest

/-- One step of the fair owner, seen through its owner part: unchanged after catching up, or one
owner step from there. -/
theorem fairTrace_base_cases (n : ℕ) :
    (fairTrace duration c arrivals (n + 1)).base =
        catchUp (fairTrace duration c arrivals n).base (c (arrivals n).1) ∨
      ∃ q, (fairTrace duration c arrivals (n + 1)).base =
        step duration (catchUp (fairTrace duration c arrivals n).base (c (arrivals n).1)) q :=
  handle_base_cases duration ⟨catchUp (fairTrace duration c arrivals n).base (c (arrivals n).1),
    (fairTrace duration c arrivals n).queue⟩ (arrivals n).2

/-- A done task stays done. -/
theorem fairTrace_done {task : X} {who : W} {n : ℕ}
    (isDone : (fairTrace duration c arrivals n).base.role task = .done who) :
    ∀ m ≥ n, (fairTrace duration c arrivals m).base.role task = .done who := by
  intro m le
  induction m, le using Nat.le_induction with
  | base => exact isDone
  | succ m _ ih =>
      have caught : (catchUp (fairTrace duration c arrivals m).base (c (arrivals m).1)).role task =
          .done who := ih
      rcases fairTrace_base_cases (duration := duration) (c := c) (arrivals := arrivals) m with same | ⟨q, next⟩
      · rw [same]; exact caught
      · rw [next]
        cases q with
        | claim w' t =>
            simp only [step]
            split_ifs with isLive
            · by_cases same : t = task
              · subst same; rw [caught] at isLive; cases isLive
              · simp [Function.update_of_ne (Ne.symm same), caught]
            · exact caught
        | tick => exact caught
        | expire t =>
            simp only [step]
            split_ifs with expired
            · by_cases same : t = task
              · subst same; rw [caught] at expired; simp [Role.expiredAt] at expired
              · simp [Function.update_of_ne (Ne.symm same), caught]
            · exact caught
        | effect w' t e =>
            simp only [step]
            split_ifs with current
            · by_cases same : t = task
              · subst same
                have := current.1
                rw [caught] at this
                simp [Role.heldBy] at this
              · simp [Function.update_of_ne (Ne.symm same), caught]
            · exact caught

/-- **A lease always ends**: with the owner's clock passing every bound and the timer firing
infinitely often, a task that is never done is live infinitely often. -/
theorem eventually_live {task : X} (timesMono : Monotone fun n => (arrivals n).1)
    (clockMono : Monotone c) (clockPasses : ∀ b n, ∃ m ≥ n, b ≤ c (arrivals m).1)
    (expiries : ∀ n, ∃ m ≥ n, (arrivals m).2 = .request (.expire task))
    (never : ∀ n who, (fairTrace duration c arrivals n).base.role task ≠ .done who) (n : ℕ) :
    ∃ m ≥ n, (fairTrace duration c arrivals m).base.role task = .live := by
  by_contra notLive
  push Not at notLive
  obtain ⟨holder, expiry, isClaimed⟩ : ∃ holder expiry,
      (fairTrace duration c arrivals n).base.role task = .claimed holder expiry := by
    cases h : (fairTrace duration c arrivals n).base.role task with
    | live => exact absurd h (notLive n le_rfl)
    | claimed holder expiry => exact ⟨holder, expiry, rfl⟩
    | done who => exact absurd h (never n who)
  have stays : ∀ m ≥ n, (fairTrace duration c arrivals m).base.role task = .claimed holder expiry := by
    intro m le
    induction m, le using Nat.le_induction with
    | base => exact isClaimed
    | succ m le ih =>
        have caught : (catchUp (fairTrace duration c arrivals m).base (c (arrivals m).1)).role task =
            .claimed holder expiry := ih
        rcases fairTrace_base_cases (duration := duration) (c := c) (arrivals := arrivals) m with same | ⟨q, next⟩
        · rw [same]; exact caught
        · rcases role_step_of_claimed duration caught q with kept | live | ⟨who, done⟩
          · rw [next]; exact kept
          · exact absurd (by rw [next]; exact live) (notLive (m + 1) (by omega))
          · exact absurd (by rw [next]; exact done) (never (m + 1) who)
  obtain ⟨m₁, le₁, passed⟩ := clockPasses expiry n
  obtain ⟨m₂, le₂, isExpire⟩ := expiries m₁
  have caught : (catchUp (fairTrace duration c arrivals m₂).base (c (arrivals m₂).1)).role task =
      .claimed holder expiry := stays m₂ (le₁.trans le₂)
  have due : ((catchUp (fairTrace duration c arrivals m₂).base (c (arrivals m₂).1)).role task).expiredAt
      (catchUp (fairTrace duration c arrivals m₂).base (c (arrivals m₂).1)).clock = true := by
    rw [caught]
    simp only [Role.expiredAt, catchUp]
    exact decide_eq_true (le_max_of_le_right (passed.trans (clockMono (timesMono le₂))))
  have freed : (fairTrace duration c arrivals (m₂ + 1)).base.role task = .live := by
    show (handle duration ⟨catchUp (fairTrace duration c arrivals m₂).base (c (arrivals m₂).1),
      (fairTrace duration c arrivals m₂).queue⟩ (arrivals m₂).2).base.role task = _
    rw [isExpire]
    show (step duration (catchUp (fairTrace duration c arrivals m₂).base (c (arrivals m₂).1))
      (.expire task)).role task = _
    simp only [step, if_pos due, Function.update_self]
  exact notLive (m₂ + 1) (by omega) freed

/-- **A live task with a waiting claimant is granted**, at the next serve at the latest. -/
theorem grant_after {task : X} (timesMono : Monotone fun n => (arrivals n).1)
    (clockMono : Monotone c) (clockPasses : ∀ b n, ∃ m ≥ n, b ≤ c (arrivals m).1)
    (expiries : ∀ n, ∃ m ≥ n, (arrivals m).2 = .request (.expire task))
    (serves : ∀ n, ∃ m ≥ n, (arrivals m).2 = .serve task)
    (never : ∀ n who, (fairTrace duration c arrivals n).base.role task ≠ .done who) {n : ℕ}
    (waiting : ∀ m ≥ n, (fairTrace duration c arrivals m).queue task ≠ []) :
    ∃ m ≥ n, GrantAt duration c arrivals task m := by
  obtain ⟨m₁, le₁, live₁⟩ := eventually_live timesMono clockMono clockPasses expiries never n
  obtain ⟨m₂, le₂, isServe⟩ := serves m₁
  by_contra none
  push Not at none
  have liveUntil : ∀ j, m₁ ≤ j → j ≤ m₂ →
      (fairTrace duration c arrivals j).base.role task = .live := by
    intro j le
    induction j, le using Nat.le_induction with
    | base => exact fun _ => live₁
    | succ j le ih =>
        intro hj
        have liveJ := ih (by omega)
        exact handle_live (duration := duration) ⟨catchUp (fairTrace duration c arrivals j).base
          (c (arrivals j).1), (fairTrace duration c arrivals j).queue⟩ liveJ
          fun ⟨isServeJ, nonempty⟩ => none j (by omega) ⟨isServeJ, liveJ, nonempty⟩
  exact none m₂ (by omega) ⟨isServe, liveUntil m₂ le₂ le_rfl, waiting m₂ (by omega)⟩

/-- **A grant after stabilization, answered in time, finishes the task.** -/
theorem granted_done {task : X} {w : W} (noTicks : ∀ n, (arrivals n).2 ≠ .request .tick)
    (timesMono : Monotone fun n => (arrivals n).1) (clockMono : Monotone c)
    {gst den slow fast R : ℕ} (rates : RateBoundsAfter c gst den slow fast)
    (margin : fast * R < den * duration) {k m : ℕ} (grant : GrantsTo duration c arrivals task w k)
    (stable : gst ≤ (arrivals k).1) (later : k < m)
    (effectAt : (arrivals m).2 =
      .request (.effect w task ((fairTrace duration c arrivals k).base.epoch task + 1)))
    (roundTrip : (arrivals m).1 ≤ (arrivals k).1 + R) :
    (fairTrace duration c arrivals (m + 1)).base.role task = .done w := by
  obtain ⟨isServe, isLive, rest, queue⟩ := grant
  set expiry := c (arrivals k).1 + duration with expiryDef
  set token := (fairTrace duration c arrivals k).base.epoch task + 1 with tokenDef
  have clockLe := fairTrace_clock_le (duration := duration) noTicks timesMono clockMono
  have granted : (fairTrace duration c arrivals (k + 1)).base.role task = .claimed w expiry ∧
      (fairTrace duration c arrivals (k + 1)).base.epoch task = token := by
    have facts := handle_grant (duration := duration)
      ⟨catchUp (fairTrace duration c arrivals k).base (c (arrivals k).1),
        (fairTrace duration c arrivals k).queue⟩ isLive queue
    show (handle duration ⟨_, _⟩ (arrivals k).2).base.role task = _ ∧
      (handle duration ⟨_, _⟩ (arrivals k).2).base.epoch task = _
    rw [isServe]
    refine ⟨?_, facts.2.1⟩
    rw [facts.1]
    simp only [catchUp, expiryDef, max_eq_right (clockLe k)]
  have timely : c (arrivals m).1 < expiry :=
    timely_of_rates rates stable (timesMono later.le) roundTrip margin
  have below : ∀ j ≤ m, (catchUp (fairTrace duration c arrivals j).base (c (arrivals j).1)).clock <
      expiry := fun j le =>
    lt_of_le_of_lt (max_le ((clockLe j).trans (clockMono (timesMono le)))
      (clockMono (timesMono le))) timely
  have holds : ∀ j, k + 1 ≤ j → j ≤ m →
      ((fairTrace duration c arrivals j).base.role task = .claimed w expiry ∧
        (fairTrace duration c arrivals j).base.epoch task = token) ∨
      (fairTrace duration c arrivals j).base.role task = .done w := by
    intro j le
    induction j, le using Nat.le_induction with
    | base => exact fun _ => Or.inl granted
    | succ j le ih =>
        intro hj
        have before := ih (by omega)
        rcases fairTrace_base_cases (duration := duration) (c := c) (arrivals := arrivals) j with same | ⟨q, next⟩
        · rw [same]; exact before
        · rw [next]
          exact lease_step_holds duration
            (s := catchUp (fairTrace duration c arrivals j).base (c (arrivals j).1)) before
            (below j (by omega)) q
  have atM := holds m (by omega) le_rfl
  show (handle duration ⟨catchUp (fairTrace duration c arrivals m).base (c (arrivals m).1),
    (fairTrace duration c arrivals m).queue⟩ (arrivals m).2).base.role task = _
  rw [effectAt]
  show (step duration (catchUp (fairTrace duration c arrivals m).base (c (arrivals m).1))
    (.effect w task token)).role task = _
  rcases atM with ⟨isClaimed, sameEpoch⟩ | isDone
  · have current : Current (catchUp (fairTrace duration c arrivals m).base (c (arrivals m).1)) w task
        token := ⟨Role.heldBy_eq_true.mpr ⟨expiry, isClaimed⟩, sameEpoch⟩
    simp only [step, if_pos current]
    simp
  · have notCurrent : ¬ Current (catchUp (fairTrace duration c arrivals m).base (c (arrivals m).1))
        w task token := fun current => by
      have := current.1
      rw [catchUp_role, isDone] at this
      simp [Role.heldBy] at this
    simp only [step, if_neg notCurrent]
    exact isDone

/-- **Every task is eventually done**, under eventual expiry, first-come-first-served service, one
correct worker that asks once after stabilization and answers its grants in time, and eventual
synchrony of the owner's clock. Faulty workers are arbitrary. -/
theorem fifo_eventually_done {task : X} {w : W}
    (noTicks : ∀ n, (arrivals n).2 ≠ .request .tick)
    (timesMono : Monotone fun n => (arrivals n).1) (clockMono : Monotone c)
    (clockPasses : ∀ b n, ∃ m ≥ n, b ≤ c (arrivals m).1)
    (expiries : ∀ n, ∃ m ≥ n, (arrivals m).2 = .request (.expire task))
    (serves : ∀ n, ∃ m ≥ n, (arrivals m).2 = .serve task)
    {gst den slow fast R : ℕ} (rates : RateBoundsAfter c gst den slow fast)
    (margin : fast * R < den * duration)
    (asksAfter : ∃ n, gst ≤ (arrivals n).1 ∧ (arrivals n).2 = .request (.claim w task))
    (answers : ∀ k, gst ≤ (arrivals k).1 → GrantsTo duration c arrivals task w k →
      ∃ m > k, (arrivals m).2 =
          .request (.effect w task ((fairTrace duration c arrivals k).base.epoch task + 1)) ∧
        (arrivals m).1 ≤ (arrivals k).1 + R) :
    ∃ n who, (fairTrace duration c arrivals n).base.role task = .done who := by
  by_contra notDone
  push Not at notDone
  obtain ⟨n₀, stable₀, asks⟩ := asksAfter
  have stableAfter : ∀ n ≥ n₀, gst ≤ (arrivals n).1 := fun n le => stable₀.trans (timesMono le)
  have neverGranted : ∀ k ≥ n₀, ¬ GrantsTo duration c arrivals task w k := by
    intro k le grant
    obtain ⟨m, later, effectAt, roundTrip⟩ := answers k (stableAfter k le) grant
    exact notDone (m + 1) w (granted_done noTicks timesMono clockMono rates margin grant
      (stableAfter k le) later effectAt roundTrip)
  have notGranted : ∀ m ≥ n₀, ¬ ((arrivals m).2 = .serve task ∧
      (fairTrace duration c arrivals m).base.role task = .live ∧
      ∃ rest, (fairTrace duration c arrivals m).queue task = w :: rest) :=
    fun m le grant => neverGranted m le grant
  have waiting : ∀ m ≥ n₀ + 1, w ∈ (fairTrace duration c arrivals m).queue task := by
    intro m le
    induction m, le using Nat.le_induction with
    | base =>
        show w ∈ (handle duration ⟨_, _⟩ (arrivals n₀).2).queue task
        rw [asks]
        exact queue_of_claim _ w task
    | succ m le ih =>
        exact (queue_step (duration := duration) ⟨catchUp (fairTrace duration c arrivals m).base
          (c (arrivals m).1), (fairTrace duration c arrivals m).queue⟩ ih (arrivals m).2
          (notGranted m (by omega))).1
  have often : InfinitelyOften (GrantAt duration c arrivals task) := fun N => by
    obtain ⟨m, le, grant⟩ := grant_after (n := max N (n₀ + 1)) timesMono clockMono clockPasses
      expiries serves notDone fun m le => List.ne_nil_of_mem (waiting m (by omega))
    exact ⟨m, by omega, grant⟩
  exact not_infinitelyOften_of_descent
    (fun m => ((fairTrace duration c arrivals m).queue task).idxOf w) (n₀ + 1)
    (fun m le => (queue_step (duration := duration) ⟨catchUp (fairTrace duration c arrivals m).base
      (c (arrivals m).1), (fairTrace duration c arrivals m).queue⟩ (waiting m le) (arrivals m).2
      (notGranted m (by omega))).2.1)
    (fun m le grant => (queue_step (duration := duration) ⟨catchUp (fairTrace duration c arrivals m).base
      (c (arrivals m).1), (fairTrace duration c arrivals m).queue⟩ (waiting m le) (arrivals m).2
      (notGranted m (by omega))).2.2 ⟨grant.1, grant.2.1⟩) often

omit [DecidableEq X] [DecidableEq W] in
/-- A positive lower rate after stabilization, and real times that pass every bound, make the
owner's clock pass every bound. -/
theorem clockPasses_of_rates {gst den slow fast : ℕ} (rates : RateBoundsAfter c gst den slow fast)
    (slowPos : 0 < slow) (clockMono : Monotone c)
    (timesUnbounded : ∀ b n, ∃ m ≥ n, b ≤ (arrivals m).1) :
    ∀ b n, ∃ m ≥ n, b ≤ c (arrivals m).1 := by
  intro b n
  obtain ⟨m, le, late⟩ := timesUnbounded (gst + den * b) n
  refine ⟨m, le, ?_⟩
  have denPos : 0 < den := by
    rcases Nat.eq_zero_or_pos den with zero | pos
    · have := rates.lower gst 1 le_rfl
      rw [zero] at this
      omega
    · exact pos
  have : den * b ≤ den * c (arrivals m).1 :=
    calc den * b ≤ slow * (den * b) := Nat.le_mul_of_pos_left _ slowPos
      _ ≤ den * c gst + slow * (den * b) := Nat.le_add_left _ _
      _ ≤ den * c (gst + den * b) := rates.lower gst (den * b) le_rfl
      _ ≤ den * c (arrivals m).1 := Nat.mul_le_mul_left _ (clockMono late)
  exact Nat.le_of_mul_le_mul_left this denPos

end Liveness


/-! ## Control: the hypotheses can all hold -/

namespace Controls

/-- One task; worker `true` claims, is served, answers; then the timer and the server keep firing. -/
def instanceEvent : ℕ → Event Unit Bool
  | 0 => .request (.claim true ())
  | 1 => .serve ()
  | 2 => .request (.effect true () 1)
  | n + 3 => if n % 2 = 0 then .request (.expire ()) else .serve ()

/-- The arrivals: event `n` at real time `n`. -/
def instanceArrivals (n : ℕ) : ℕ × Event Unit Bool := (n, instanceEvent n)

/-- A perfect clock. -/
def perfectClock : Clock := fun t => t

theorem instance_done_at_three :
    (fairTrace 2 perfectClock instanceArrivals 3).base.role () = .done true := by
  decide

/-- **Every hypothesis of `fifo_eventually_done` holds in one run**, with a perfect clock, a lease
of `2`, a round trip of `1` and stabilization at `0`. -/
theorem fifo_instance :
    ∃ n who, (fairTrace 2 perfectClock instanceArrivals n).base.role () = .done who := by
  refine fifo_eventually_done (task := ()) (w := true) (gst := 0) (den := 1) (slow := 1) (fast := 1)
    (R := 1) ?noTicks (fun _ _ h => h) (fun _ _ h => h)
    (fun b n => ⟨max b n, le_max_right _ _, le_max_left _ _⟩) ?expiries ?serves
    ((Mettapedia.GSLT.Timing.RateBounds.perfect 1).after 0) (by decide) ⟨0, le_rfl, rfl⟩ ?answers
  case noTicks =>
    intro n isTick
    match n, isTick with
    | 0, h => cases h
    | 1, h => cases h
    | 2, h => cases h
    | n + 3, h =>
        simp only [instanceArrivals, instanceEvent] at h
        split_ifs at h
        cases h
  case expiries =>
    intro n
    refine ⟨2 * n + 3, by omega, ?_⟩
    simp only [instanceArrivals, instanceEvent]
    rw [if_pos (by omega)]
  case serves =>
    intro n
    refine ⟨2 * n + 1 + 3, by omega, ?_⟩
    simp only [instanceArrivals, instanceEvent]
    rw [if_neg (by omega)]
  case answers =>
    intro k _ grant
    obtain ⟨isServe, isLive, _⟩ := grant
    match k, isServe, isLive with
    | 0, h, _ => cases h
    | 1, _, _ => exact ⟨2, by omega, rfl, by decide⟩
    | 2, h, _ => cases h
    | k + 3, _, live =>
        have done := fairTrace_done instance_done_at_three (k + 3) (by omega)
        rw [done] at live
        cases live

end Controls

end Mettapedia.GSLT.Coordination.Liveness.FairLeaseService
