import Mettapedia.GSLT.Timing.ClockModels
import Mettapedia.GSLT.Coordination.FencedLeases

/-!
# Leases in real time: safety needs no clock, liveness needs eventual synchrony

`Coordination.FencedLeases` counts the owner's clock by `tick` requests. Here the owner reads a
real clock `c` (any function of real time): when a request arrives at real time `t`, its clock
catches up to `c t` (`catchUp`, never backwards) and it handles the request (`timedStep`). The
lease duration may depend on the owner's state (`Policy`): fixed, or growing with the epoch.

## Safety, in the asynchronous model

* **A timed owner is an untimed owner** (`timedRun_refines`): every timed run with a fixed
  duration is a run of `FencedLeases.runList`, catching up being a sequence of ticks. So every
  safety theorem of `FencedLeases` holds for every clock and every arrival schedule.
* **With any duration policy** the owner's invariant holds (`inv_timedRun`): at most one effect
  per task (`timed_effects_nodup`), each from a grant with its epoch, for every clock, every
  schedule and every policy. No clock appears in the hypotheses: safety needs none.
* **A token expired by the owner's clock is dead, whatever the worker's clock says**
  (`expired_token_dead`): once the owner has expired a lease, no effect carrying that lease's
  token is ever accepted. A worker's clock does not enter the owner's step; a slow worker that
  still believes in its lease is fenced out.

## Without fencing, safety needs bounded drift and bounded delay

When the holder writes to another resource and nobody checks the epoch there, safety rests on the
holder stopping in time by its own clock, as in Gray and Cheriton's leases: the holder starts
counting when it sends its claim, uses the lease only while its clock shows less than `usable`,
and its writes take at most `Δ` to land.

* **Bounded drift and delay suffice** (`write_lands_before_next_grant`): if the holder's clock runs
  at least at `slow / den`, the owner's at most at `fast / den`, and
  `fast · (den · usable + slow · Δ) ≤ slow · den · duration`, every write of a holder lands
  before the owner grants the lease again, so before every write of the next holder.
* **A fast owner and a slow worker** (`Controls.fast_owner_slow_worker`): both clocks within
  drift `1` of the nominal rate `2`, the owner's at `3`, the worker's at `1`; the worker's write
  lands after the next holder's write, so an unfenced resource takes two writes for one task and
  keeps the stale one last, while a fencing resource refuses it. A paused worker
  (`Controls.paused_worker`) has no positive lower rate at all, and believes in its lease forever.
  Positive control: a margin that covers the drift (`Controls.margin_suffices`).
* **Perfect clocks and a delayed write** (`Controls.delayed_write_lands_late`): with both clocks
  perfect, a write in flight longer than the margin lands after the next grant.

## Liveness needs eventual synchrony

* **A timely attempt completes** (`timely_attempt_completes`): a claim served while the task is
  live, followed by the holder's effect before the owner's clock reaches the expiry, finishes the
  task, whatever else arrives in between.
* **Synchrony makes an attempt timely** (`timely_of_rates`, `synchronous_attempt_completes`): with
  the owner's clock at most at `fast / den`, a round trip of at most `R` and `fast · R < den · d`,
  the effect arrives in time. Under `eventualBound` the same holds for attempts made after
  stabilization.
* **A fixed duration fails under an unknown bound** (`Controls.fixed_duration_fails`): for every
  duration `d`, with perfect clocks and a round trip of `d`, a correct worker that answers every
  grant never completes: each effect arrives as the lease expires.
* **Growing durations succeed under an unknown bound** (`growing_attempt_completes`,
  `growing_eventually_long`): when the duration grows with the epoch, every failed attempt raises
  the epoch, and from some epoch on every attempt is timely, whatever the unknown bound.
* **No duration policy is live in the asynchronous model** (`Controls.async_never_completes`): for
  every duration chosen from the epoch, an owner clock that advances by the duration while the
  effect is in flight defeats a correct worker forever, although every message is delivered and
  the timer fires.

So leases put timing only where it is harmless: safety holds in every model, and liveness holds
exactly when timing eventually behaves. This is the principle of Dwork, Lynch and Stockmeyer, and
the reverse of the winner rule (`WinnerRuleClocks`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Timing.TimedLeases

open Mettapedia.GSLT.Timing
open Mettapedia.GSLT.Coordination.FencedLeases

universe u v

variable {X : Type u} [DecidableEq X] {W : Type v} [DecidableEq W]

/-! ## The owner reads a real clock -/

/-- The owner's clock catches up with a reading; it never goes back. -/
def catchUp (s : Owner X W) (reading : ℕ) : Owner X W := { s with clock := max s.clock reading }

/-- A duration policy: the lease duration the owner grants, from its state and the request. -/
abbrev Policy (X : Type u) (W : Type v) := Owner X W → Request X W → ℕ

/-- A fixed duration. -/
def fixed (d : ℕ) : Policy X W := fun _ _ => d

/-- A request arrives at real time `arrival.1`: the owner reads its clock `c`, then handles it. -/
def timedStep (policy : Policy X W) (c : Clock) (s : Owner X W) (arrival : ℕ × Request X W) :
    Owner X W :=
  step (policy (catchUp s (c arrival.1)) arrival.2) (catchUp s (c arrival.1)) arrival.2

/-- A timed run: requests with their arrival times, in arrival order. -/
def timedRun (policy : Policy X W) (c : Clock) : Owner X W → List (ℕ × Request X W) → Owner X W
  | s, [] => s
  | s, a :: rest => timedRun policy c (timedStep policy c s a) rest

theorem timedRun_append (policy : Policy X W) (c : Clock) (s : Owner X W)
    (first second : List (ℕ × Request X W)) :
    timedRun policy c s (first ++ second) = timedRun policy c (timedRun policy c s first) second := by
  induction first generalizing s with
  | nil => rfl
  | cons a rest ih => exact ih _

/-! ## A timed owner is an untimed owner -/

theorem runList_append (duration : ℕ) (s : Owner X W) (first second : List (Request X W)) :
    runList duration s (first ++ second) = runList duration (runList duration s first) second := by
  induction first generalizing s with
  | nil => rfl
  | cons r rest ih => exact ih _

/-- Ticking `k` times advances the clock by `k`. -/
theorem runList_ticks (duration : ℕ) (s : Owner X W) (k : ℕ) :
    runList duration s (List.replicate k .tick) = { s with clock := s.clock + k } := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ]
      show runList duration (step duration s .tick) _ = _
      rw [ih]
      simp only [step]
      congr 1
      omega

/-- **Catching up is ticking.** -/
theorem catchUp_eq_runList (duration : ℕ) (s : Owner X W) (reading : ℕ) :
    catchUp s reading = runList duration s (List.replicate (reading - s.clock) .tick) := by
  rw [runList_ticks]
  simp only [catchUp]
  congr 1
  omega

/-- **A timed run with a fixed duration is a run of the untimed owner.** -/
theorem timedRun_refines (duration : ℕ) (c : Clock) (s : Owner X W) (arrivals : List (ℕ × Request X W)) :
    ∃ requests, timedRun (fixed duration) c s arrivals = runList duration s requests := by
  induction arrivals generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons a rest ih =>
      obtain ⟨requests, same⟩ := ih (timedStep (fixed duration) c s a)
      refine ⟨List.replicate (c a.1 - s.clock) .tick ++ a.2 :: requests, ?_⟩
      show timedRun (fixed duration) c (timedStep (fixed duration) c s a) rest = _
      rw [same, runList_append, ← catchUp_eq_runList]
      rfl

/-! ## Safety for every clock, schedule and policy -/

omit [DecidableEq X] [DecidableEq W] in
theorem inv_catchUp {s : Owner X W} (inv : Inv s) (reading : ℕ) : Inv (catchUp s reading) :=
  ⟨inv.nodup, inv.done_iff, inv.granted, inv.effect_granted⟩

theorem inv_timedRun (policy : Policy X W) (c : Clock) {s : Owner X W} (inv : Inv s)
    (arrivals : List (ℕ × Request X W)) : Inv (timedRun policy c s arrivals) := by
  induction arrivals generalizing s with
  | nil => exact inv
  | cons a rest ih => exact ih (inv_step _ (inv_catchUp inv _) a.2)

/-- **At most one effect per task, for every clock, every arrival schedule and every duration
policy.** -/
theorem timed_effects_nodup (policy : Policy X W) (c : Clock) (arrivals : List (ℕ × Request X W)) :
    ((timedRun policy c Owner.start arrivals).effects.map Prod.fst).Nodup :=
  (inv_timedRun policy c inv_start arrivals).nodup

/-- **Every accepted effect is from a grant with its epoch**, for every clock, schedule and
policy. -/
theorem timed_effect_from_grant (policy : Policy X W) (c : Clock)
    (arrivals : List (ℕ × Request X W)) :
    ∀ entry ∈ (timedRun policy c Owner.start arrivals).effects,
      entry ∈ (timedRun policy c Owner.start arrivals).grants :=
  (inv_timedRun policy c inv_start arrivals).effect_granted

/-! ## An expired token is dead -/

/-- Epochs never decrease. -/
theorem epoch_step_ge (duration : ℕ) (s : Owner X W) (r : Request X W) (task : X) :
    s.epoch task ≤ (step duration s r).epoch task := by
  cases r with
  | claim who t =>
      simp only [step]; split_ifs
      · by_cases same : task = t
        · subst same; simp
        · simp [Function.update_of_ne same]
      · exact le_rfl
  | tick => exact le_rfl
  | expire t =>
      simp only [step]; split_ifs
      · by_cases same : task = t
        · subst same; simp
        · simp [Function.update_of_ne same]
      · exact le_rfl
  | effect who t e =>
      simp only [step]; split_ifs
      · by_cases same : task = t
        · subst same; simp
        · simp [Function.update_of_ne same]
      · exact le_rfl

/-- What one step adds to the effects: nothing, or the current effect it accepted. -/
theorem effects_step (duration : ℕ) (s : Owner X W) (r : Request X W) :
    (step duration s r).effects = s.effects ∨
      ∃ who task e, Current s who task e ∧ (step duration s r).effects = s.effects ++ [(task, who, e)] := by
  cases r with
  | claim who t => simp only [step]; split_ifs <;> exact Or.inl rfl
  | tick => exact Or.inl rfl
  | expire t => simp only [step]; split_ifs <;> exact Or.inl rfl
  | effect who t e =>
      simp only [step]
      split_ifs with current
      · exact Or.inr ⟨who, t, e, current, rfl⟩
      · exact Or.inl rfl

/-- Once a task's epoch is past `token`, no accepted effect for the task carries `token`, ever. -/
theorem token_dead_of_past (policy : Policy X W) (c : Clock) {task : X} {token : ℕ}
    {s : Owner X W} (past : token < s.epoch task)
    (none : ∀ entry ∈ s.effects, entry.1 = task → entry.2.2 ≠ token)
    (arrivals : List (ℕ × Request X W)) :
    ∀ entry ∈ (timedRun policy c s arrivals).effects, entry.1 = task → entry.2.2 ≠ token := by
  induction arrivals generalizing s with
  | nil => exact none
  | cons a rest ih =>
      apply ih
      · exact lt_of_lt_of_le past (epoch_step_ge _ (catchUp s (c a.1)) a.2 task)
      · intro entry member sameTask
        rcases effects_step (policy (catchUp s (c a.1)) a.2) (catchUp s (c a.1)) a.2 with same | ⟨who, t, e, current, added⟩
        · exact none entry ((show (timedStep policy c s a).effects = s.effects from same) ▸ member) sameTask
        · have member' : entry ∈ (catchUp s (c a.1)).effects ++ [(t, who, e)] := by
            rw [← added]; exact member
          change entry ∈ s.effects ++ [(t, who, e)] at member'
          rcases List.mem_append.mp member' with old | new
          · exact none entry old sameTask
          · rw [List.mem_singleton] at new
            subst new
            simp only at sameTask ⊢
            subst sameTask
            have := current.2
            simp only [catchUp] at this
            omega

/-- **A token expired by the owner's clock is dead, whatever the worker's clock says.** If the
owner, reading its clock at real time `t`, expires a lease held with token `token`, then no effect
carrying that token is accepted in any continuation. -/
theorem expired_token_dead (policy : Policy X W) (c : Clock) {s : Owner X W} (inv : Inv s)
    {task : X} {holder : W} {expiry t : ℕ} (held : s.role task = .claimed holder expiry)
    (dueByOwner : expiry ≤ max s.clock (c t)) (rest : List (ℕ × Request X W)) :
    ∀ entry ∈ (timedRun policy c (timedStep policy c s (t, .expire task)) rest).effects,
      entry.1 = task → entry.2.2 ≠ s.epoch task := by
  have due : (s.role task).expiredAt (max s.clock (c t)) = true :=
    Role.expiredAt_eq_true.mpr ⟨holder, expiry, held, dueByOwner⟩
  apply token_dead_of_past
  · simp [timedStep, step, catchUp, due]
  · intro entry member sameTask
    have notDone : task ∉ s.effects.map Prod.fst := fun inEffects => by
      obtain ⟨w, done⟩ := (inv.done_iff task).mp inEffects
      rw [held] at done; cases done
    have member' : entry ∈ s.effects := by
      simpa [timedStep, step, catchUp, due] using member
    exact absurd (sameTask ▸ List.mem_map_of_mem member') notDone

/-! ## Without fencing: bounded drift and bounded delay -/

/-- **Leases without fencing are safe under bounded drift and bounded delay** (Gray and Cheriton).
A holder sends its claim at real time `sent`; the owner grants at `grant` and grants again at
`next`, once its own clock has advanced by `duration`. The holder writes at real time `u` while its
own clock shows less than `usable` since `sent`, and the write takes `δ ≤ Δ` to land. If the
holder's clock runs at least at `slow / den`, the owner's at most at `fast / den`, and
`fast · (den · usable + slow · Δ) ≤ slow · (den · duration)`, the write lands before `next`. -/
theorem write_lands_before_next_grant {ownerClock holderClock : Clock}
    {den slow fast usable duration Δ sent grant next u δ : ℕ}
    (ownerRate : ∀ t d, den * ownerClock (t + d) ≤ den * ownerClock t + fast * d)
    (holderRate : ∀ t d, den * holderClock t + slow * d ≤ den * holderClock (t + d))
    (slowPos : 0 < slow) (fastPos : 0 < fast)
    (sentFirst : sent ≤ grant) (grantFirst : grant ≤ next)
    (expiredFirst : ownerClock grant + duration ≤ ownerClock next)
    (afterSend : sent ≤ u) (believed : holderClock u < holderClock sent + usable)
    (delayed : δ ≤ Δ) (margin : fast * (den * usable + slow * Δ) ≤ slow * (den * duration)) :
    u + δ < next := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le afterSend
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le grantFirst
  have denPos : 0 < den := by
    rcases Nat.eq_zero_or_pos den with zero | pos
    · have := holderRate 0 1; subst zero; omega
    · exact pos
  have used : slow * x < den * usable := by
    have h1 := holderRate sent x
    have : den * holderClock (sent + x) < den * (holderClock sent + usable) :=
      Nat.mul_lt_mul_of_pos_left believed denPos
    rw [Nat.mul_add] at this
    omega
  have lease : den * duration ≤ fast * y := by
    have h2 := ownerRate grant y
    have : den * (ownerClock grant + duration) ≤ den * ownerClock (grant + y) :=
      Nat.mul_le_mul_left den expiredFirst
    rw [Nat.mul_add] at this
    omega
  have a1 : fast * (slow * x) < fast * (den * usable) := Nat.mul_lt_mul_of_pos_left used fastPos
  have a2 : slow * (den * duration) ≤ slow * (fast * y) := Nat.mul_le_mul_left slow lease
  have key : (fast * slow) * (x + Δ) < (fast * slow) * y := by
    have e1 : (fast * slow) * (x + Δ) = fast * (slow * x) + fast * (slow * Δ) := by ring
    have e2 : fast * (den * usable + slow * Δ) = fast * (den * usable) + fast * (slow * Δ) := by ring
    have e3 : (fast * slow) * y = slow * (fast * y) := by ring
    rw [e1, e3]
    rw [e2] at margin
    omega
  have := Nat.lt_of_mul_lt_mul_left key
  omega

/-- **The holders' writes are ordered**: under the hypotheses of `write_lands_before_next_grant`,
every write the next holder issues after its grant lands after this holder's write. -/
theorem writes_ordered {ownerClock holderClock : Clock}
    {den slow fast usable duration Δ sent grant next u δ u' δ' : ℕ}
    (ownerRate : ∀ t d, den * ownerClock (t + d) ≤ den * ownerClock t + fast * d)
    (holderRate : ∀ t d, den * holderClock t + slow * d ≤ den * holderClock (t + d))
    (slowPos : 0 < slow) (fastPos : 0 < fast)
    (sentFirst : sent ≤ grant) (grantFirst : grant ≤ next)
    (expiredFirst : ownerClock grant + duration ≤ ownerClock next)
    (afterSend : sent ≤ u) (believed : holderClock u < holderClock sent + usable)
    (delayed : δ ≤ Δ) (margin : fast * (den * usable + slow * Δ) ≤ slow * (den * duration))
    (nextAfterGrant : next ≤ u') : u + δ < u' + δ' := by
  have := write_lands_before_next_grant ownerRate holderRate slowPos fastPos sentFirst grantFirst
    expiredFirst afterSend believed delayed margin
  omega

/-! ## Liveness -/

omit [DecidableEq X] [DecidableEq W] in
theorem catchUp_role (s : Owner X W) (reading : ℕ) : (catchUp s reading).role = s.role := rfl

omit [DecidableEq X] [DecidableEq W] in
theorem catchUp_epoch (s : Owner X W) (reading : ℕ) : (catchUp s reading).epoch = s.epoch := rfl

/-- Requests other than ticks leave the owner's clock alone. -/
theorem step_clock (duration : ℕ) (s : Owner X W) {r : Request X W} (notTick : r ≠ .tick) :
    (step duration s r).clock = s.clock := by
  cases r with
  | claim who t => simp only [step]; split_ifs <;> rfl
  | tick => exact absurd rfl notTick
  | expire t => simp only [step]; split_ifs <;> rfl
  | effect who t e => simp only [step]; split_ifs <;> rfl

/-- Without tick requests, the owner's clock is the latest reading of its monotone clock. -/
theorem clock_timedRun_le (policy : Policy X W) {c : Clock} (mono : Monotone c) {s : Owner X W}
    {bound : ℕ} (start : s.clock ≤ c bound) (arrivals : List (ℕ × Request X W))
    (times : ∀ a ∈ arrivals, a.1 ≤ bound) (noTicks : ∀ a ∈ arrivals, a.2 ≠ .tick) :
    (timedRun policy c s arrivals).clock ≤ c bound := by
  induction arrivals generalizing s with
  | nil => exact start
  | cons a rest ih =>
      apply ih _ (fun b member => times b (List.mem_cons_of_mem _ member))
        (fun b member => noTicks b (List.mem_cons_of_mem _ member))
      show (step _ (catchUp s (c a.1)) a.2).clock ≤ c bound
      rw [step_clock _ _ (noTicks a List.mem_cons_self)]
      exact max_le start (mono (times a List.mem_cons_self))

/-- **A timely attempt completes.** A claim of `who` reaches the owner at real time `g` while the
task is live; any requests but ticks arrive until `te`; the holder's effect, with the token it was
granted, arrives at `te`, before the owner's clock reaches the lease's expiry. Then the task is
done by `who`. -/
theorem timely_attempt_completes (policy : Policy X W) {c : Clock} (mono : Monotone c)
    {s : Owner X W} {task : X} {who : W} {g te : ℕ}
    (isLive : s.role task = .live) (clockBelow : s.clock ≤ c g) (order : g ≤ te)
    (mid : List (ℕ × Request X W)) (midTimes : ∀ a ∈ mid, a.1 ≤ te)
    (noTicks : ∀ a ∈ mid, a.2 ≠ .tick)
    (timely : c te < c g + policy (catchUp s (c g)) (.claim who task)) :
    (timedStep policy c (timedRun policy c (timedStep policy c s (g, .claim who task)) mid)
      (te, .effect who task (s.epoch task + 1))).role task = .done who := by
  set expiry := c g + policy (catchUp s (c g)) (.claim who task)
  set token := s.epoch task + 1
  set granted := timedStep policy c s (g, .claim who task)
  have grantedClock : granted.clock = c g := by
    show (step _ (catchUp s (c g)) (.claim who task)).clock = c g
    rw [step_clock _ _ (by simp)]
    exact max_eq_right clockBelow
  have grantedHolds : granted.role task = .claimed who expiry ∧ granted.epoch task = token := by
    show (step _ (catchUp s (c g)) (.claim who task)).role task = _ ∧
      (step _ (catchUp s (c g)) (.claim who task)).epoch task = _
    simp only [step, catchUp_role, isLive, if_true]
    simp [catchUp, expiry, token, max_eq_right clockBelow]
  -- Through `mid`, the lease stays held at the token's epoch, or the task is done by `who`.
  have holds : ∀ (l : List (ℕ × Request X W)), (∀ a ∈ l, a.1 ≤ te) → (∀ a ∈ l, a.2 ≠ .tick) →
      ∀ (σ : Owner X W), σ.clock ≤ c te →
      ((σ.role task = .claimed who expiry ∧ σ.epoch task = token) ∨ σ.role task = .done who) →
      (((timedRun policy c σ l).role task = .claimed who expiry ∧
          (timedRun policy c σ l).epoch task = token) ∨
        (timedRun policy c σ l).role task = .done who) ∧
      (timedRun policy c σ l).clock ≤ c te := by
    intro l
    induction l with
    | nil => exact fun _ _ σ clockLe holdsσ => ⟨holdsσ, clockLe⟩
    | cons a rest ih =>
        intro times notTick σ clockLe holdsσ
        have aTime := times a List.mem_cons_self
        have caught : (catchUp σ (c a.1)).clock < expiry :=
          lt_of_le_of_lt (max_le clockLe (mono aTime)) timely
        apply ih (fun b member => times b (List.mem_cons_of_mem _ member))
          (fun b member => notTick b (List.mem_cons_of_mem _ member))
        · show (step _ (catchUp σ (c a.1)) a.2).clock ≤ c te
          rw [step_clock _ _ (notTick a List.mem_cons_self)]
          exact max_le clockLe (mono aTime)
        · exact lease_step_holds _ (s := catchUp σ (c a.1)) holdsσ caught a.2
  obtain ⟨atEnd, endClock⟩ := holds mid midTimes noTicks granted (grantedClock ▸ mono order)
    (Or.inl grantedHolds)
  set σ := timedRun policy c granted mid
  have caught : (catchUp σ (c te)).clock < expiry := lt_of_le_of_lt (max_le endClock le_rfl) timely
  show (step _ (catchUp σ (c te)) (.effect who task token)).role task = _
  rcases atEnd with ⟨isClaimed, sameEpoch⟩ | isDone
  · have current : Current (catchUp σ (c te)) who task token :=
      ⟨Role.heldBy_eq_true.mpr ⟨expiry, isClaimed⟩, sameEpoch⟩
    simp only [step, if_pos current]
    simp
  · have notCurrent : ¬ Current (catchUp σ (c te)) who task token := fun current => by
      have := current.1
      rw [catchUp_role, isDone] at this
      simp [Role.heldBy] at this
    simp only [step, if_neg notCurrent]
    exact isDone

/-- **Bounded rate and round trip make an attempt timely**: from the arming on, the owner's clock
runs at most at `fast / den`; the effect arrives within `R` of the grant; and `fast · R < den · d`.
Then the owner's clock at the effect's arrival is below the expiry. -/
theorem timely_of_rates {c : Clock} {gst den slow fast g te R d : ℕ}
    (rates : RateBoundsAfter c gst den slow fast) (stable : gst ≤ g) (order : g ≤ te)
    (roundTrip : te ≤ g + R) (margin : fast * R < den * d) : c te < c g + d := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le order
  have rate := rates.upper g x stable
  have : fast * x ≤ fast * R := Nat.mul_le_mul_left fast (by omega)
  have : den * c (g + x) < den * (c g + d) := by rw [Nat.mul_add]; omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Under synchrony an attempt completes**: the owner's clock has nominal rate `n` and drift
`num`, the round trip is at most `R`, and `(n + num) · R` is below the duration. -/
theorem synchronous_attempt_completes (policy : Policy X W) {c : Clock} {nominal num : ℕ}
    (drift : BoundedDrift c nominal num) {s : Owner X W} {task : X} {who : W} {g te R : ℕ}
    (isLive : s.role task = .live) (clockBelow : s.clock ≤ c g) (order : g ≤ te)
    (roundTrip : te ≤ g + R)
    (margin : (nominal + num) * R < policy (catchUp s (c g)) (.claim who task))
    (mid : List (ℕ × Request X W)) (midTimes : ∀ a ∈ mid, a.1 ≤ te)
    (noTicks : ∀ a ∈ mid, a.2 ≠ .tick) :
    (timedStep policy c (timedRun policy c (timedStep policy c s (g, .claim who task)) mid)
      (te, .effect who task (s.epoch task + 1))).role task = .done who :=
  timely_attempt_completes policy (drift.monotone Nat.one_pos) isLive clockBelow order mid midTimes
    noTicks (timely_of_rates (drift.after 0) (Nat.zero_le _) order roundTrip (by simpa using margin))

/-- **After stabilization an attempt completes**: under `eventualBound`, an attempt granted after
the global stabilization time, with a round trip of at most `R` and `(n + num) · R` below the
duration, finishes the task. -/
theorem eventual_attempt_completes (policy : Policy X W) {c : Clock} {gst nominal num : ℕ}
    (rates : RateBoundsAfter c gst 1 (nominal - num) (nominal + num)) (mono : Monotone c)
    {s : Owner X W} {task : X} {who : W} {g te R : ℕ} (stable : gst ≤ g)
    (isLive : s.role task = .live) (clockBelow : s.clock ≤ c g) (order : g ≤ te)
    (roundTrip : te ≤ g + R)
    (margin : (nominal + num) * R < policy (catchUp s (c g)) (.claim who task))
    (mid : List (ℕ × Request X W)) (midTimes : ∀ a ∈ mid, a.1 ≤ te)
    (noTicks : ∀ a ∈ mid, a.2 ≠ .tick) :
    (timedStep policy c (timedRun policy c (timedStep policy c s (g, .claim who task)) mid)
      (te, .effect who task (s.epoch task + 1))).role task = .done who :=
  timely_attempt_completes policy mono isLive clockBelow order mid midTimes noTicks
    (timely_of_rates rates stable order roundTrip (by simpa using margin))

/-! ## Growing durations -/

/-- Durations that grow with the task's epoch. -/
def growing (base : ℕ) : Policy X W := fun s r =>
  match r with
  | .claim _ task => base + s.epoch task
  | _ => base

/-- **Growing durations make an attempt timely once the epoch is large enough**, whatever the
unknown bound on the round trip and the owner's rate. -/
theorem growing_attempt_completes (base : ℕ) {c : Clock} {den slow fast : ℕ}
    (rates : RateBounds c den slow fast) (positive : 0 < den) {s : Owner X W} {task : X} {who : W}
    {g te R : ℕ} (isLive : s.role task = .live) (clockBelow : s.clock ≤ c g) (order : g ≤ te)
    (roundTrip : te ≤ g + R) (late : fast * R < den * (base + s.epoch task))
    (mid : List (ℕ × Request X W)) (midTimes : ∀ a ∈ mid, a.1 ≤ te)
    (noTicks : ∀ a ∈ mid, a.2 ≠ .tick) :
    (timedStep (growing base) c (timedRun (growing base) c
      (timedStep (growing base) c s (g, .claim who task)) mid)
      (te, .effect who task (s.epoch task + 1))).role task = .done who :=
  timely_attempt_completes (growing base) (rates.monotone positive) isLive clockBelow order mid
    midTimes noTicks (timely_of_rates (rates.after 0) (Nat.zero_le _) order roundTrip late)

/-- From some epoch on the growing duration exceeds any bound. -/
theorem growing_eventually_long (base : ℕ) {den : ℕ} (positive : 0 < den) (fast R : ℕ) :
    ∀ e, fast * R + 1 ≤ e → fast * R < den * (base + e) := by
  intro e large
  have : e ≤ den * e := Nat.le_mul_of_pos_left e positive
  nlinarith

/-- Each failed attempt raises the epoch: a claim of a live task raises it by one, and so does
an expiry. -/
theorem epoch_claim (policy : Policy X W) (c : Clock) {s : Owner X W} {task : X} {who : W} {g : ℕ}
    (isLive : s.role task = .live) :
    (timedStep policy c s (g, .claim who task)).epoch task = s.epoch task + 1 := by
  simp [timedStep, step, catchUp, isLive]

/-! ## One attempt, step by step -/

/-- A claim of a live task grants it, until the clock it read plus the policy's duration. -/
theorem claim_live (policy : Policy X W) (c : Clock) {s : Owner X W} {task : X} {who : W} {g : ℕ}
    (isLive : s.role task = .live) :
    (timedStep policy c s (g, .claim who task)).role task =
        .claimed who (max s.clock (c g) + policy (catchUp s (c g)) (.claim who task)) ∧
      (timedStep policy c s (g, .claim who task)).epoch task = s.epoch task + 1 ∧
      (timedStep policy c s (g, .claim who task)).effects = s.effects ∧
      (timedStep policy c s (g, .claim who task)).clock = max s.clock (c g) := by
  simp [timedStep, step, catchUp, isLive]

/-- An expiry that the owner's clock has reached frees the task. -/
theorem expire_due (policy : Policy X W) (c : Clock) {s : Owner X W} {task : X} {holder : W}
    {expiry t : ℕ} (held : s.role task = .claimed holder expiry) (due : expiry ≤ max s.clock (c t)) :
    (timedStep policy c s (t, .expire task)).role task = .live ∧
      (timedStep policy c s (t, .expire task)).epoch task = s.epoch task + 1 ∧
      (timedStep policy c s (t, .expire task)).effects = s.effects ∧
      (timedStep policy c s (t, .expire task)).clock = max s.clock (c t) := by
  have expired : (s.role task).expiredAt (max s.clock (c t)) = true :=
    Role.expiredAt_eq_true.mpr ⟨holder, expiry, held, due⟩
  simp [timedStep, step, catchUp, expired]

/-- An effect on a live task is refused. -/
theorem effect_live (policy : Policy X W) (c : Clock) {s : Owner X W} {task : X} {who : W}
    {t token : ℕ} (isLive : s.role task = .live) :
    (timedStep policy c s (t, .effect who task token)).role = s.role ∧
      (timedStep policy c s (t, .effect who task token)).epoch = s.epoch ∧
      (timedStep policy c s (t, .effect who task token)).effects = s.effects ∧
      (timedStep policy c s (t, .effect who task token)).clock = max s.clock (c t) := by
  have notCurrent : ¬ Current (catchUp s (c t)) who task token := fun current => by
    have := current.1
    rw [catchUp_role, isLive] at this
    simp [Role.heldBy] at this
  simp only [timedStep, step, if_neg notCurrent]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Controls -/

namespace Controls

/-- One attempt of the correct worker `true` on the one task: its claim arrives at `g`; its
effect, with the token of its grant, arrives `d` later, together with the owner's expiry. -/
def lateAttempt (d g token : ℕ) : List (ℕ × Request Unit Bool) :=
  [(g, .claim true ()), (g + d, .expire ()), (g + d, .effect true () token)]

/-- `n` attempts, one every `d + 1` ticks; attempt `k` carries the token `2k + 1` it was granted. -/
def lateAttempts (d : ℕ) : ℕ → List (ℕ × Request Unit Bool)
  | 0 => []
  | n + 1 => lateAttempts d n ++ lateAttempt d (n * (d + 1)) (2 * n + 1)

/-- **A fixed duration fails under an unknown bound.** For every duration `d`, with a perfect
clock and a round trip of `d`, the correct worker answers every grant with its token and every
message arrives, and still the task is never done: each effect arrives as the lease expires. -/
theorem fixed_duration_fails (d n : ℕ) :
    (timedRun (fixed d) (fun t => t) Owner.start (lateAttempts d n)).role () = .live ∧
      (timedRun (fixed d) (fun t => t) Owner.start (lateAttempts d n)).effects = [] ∧
      (timedRun (fixed d) (fun t => t) Owner.start (lateAttempts d n)).epoch () = 2 * n ∧
      (timedRun (fixed d) (fun t => t) Owner.start (lateAttempts d n)).clock ≤ n * (d + 1) := by
  induction n with
  | zero => simp [lateAttempts, timedRun, Owner.start]
  | succ n ih =>
      obtain ⟨live, noEffects, epochIs, clockLe⟩ := ih
      rw [lateAttempts, timedRun_append]
      set s := timedRun (fixed d) (fun t => t) Owner.start (lateAttempts d n)
      set g := n * (d + 1)
      obtain ⟨role₁, epoch₁, effects₁, clock₁⟩ :=
        claim_live (fixed d) (fun t => t) (g := g) (who := true) live
      set s₁ := timedStep (fixed d) (fun t => t) s (g, .claim true ())
      have clockMax : max s.clock g = g := max_eq_right clockLe
      obtain ⟨role₂, epoch₂, effects₂, clock₂⟩ :=
        expire_due (fixed d) (fun t => t) (s := s₁) (t := g + d) role₁ (by
          simp only [clock₁, clockMax, fixed]; omega)
      set s₂ := timedStep (fixed d) (fun t => t) s₁ (g + d, .expire ())
      obtain ⟨role₃, epoch₃, effects₃, clock₃⟩ :=
        effect_live (fixed d) (fun t => t) (s := s₂) (t := g + d) (who := true)
          (token := 2 * n + 1) role₂
      have runIs : timedRun (fixed d) (fun t => t) s (lateAttempt d g (2 * n + 1)) =
          timedStep (fixed d) (fun t => t) s₂ (g + d, .effect true () (2 * n + 1)) := rfl
      rw [runIs]
      refine ⟨by rw [role₃, role₂], by rw [effects₃, effects₂, effects₁, noEffects],
        by rw [epoch₃, epoch₂, epoch₁, epochIs]; ring, ?_⟩
      rw [clock₃, clock₂, clock₁, clockMax]
      simp only [g]
      apply max_le <;> [apply max_le; skip] <;> nlinarith

/-- **Growing durations complete on the same schedule.** With the duration growing with the
epoch from `0` and the same round trip of `3`, the third attempt is timely and the task is done
by the correct worker. -/
theorem growing_completes :
    (timedRun (growing 0) (fun t => t) Owner.start (lateAttempts 3 3)).role () = .done true ∧
      (timedRun (fixed 3) (fun t => t) Owner.start (lateAttempts 3 3)).role () = .live := by
  refine ⟨by decide, (fixed_duration_fails 3 3).1⟩

/-- An owner clock that advances by `dur i` in real tick `i`. -/
def jumpClock (dur : ℕ → ℕ) : Clock := fun t => ∑ i ∈ Finset.range t, dur i

theorem jumpClock_succ (dur : ℕ → ℕ) (t : ℕ) : jumpClock dur (t + 1) = jumpClock dur t + dur t :=
  Finset.sum_range_succ _ _

theorem jumpClock_mono (dur : ℕ → ℕ) : Monotone (jumpClock dur) := by
  intro a b le
  induction le with
  | refl => exact le_rfl
  | step _ ih => rw [jumpClock_succ]; omega

/-- A duration chosen from the task's epoch. -/
def byEpoch (dur : ℕ → ℕ) : Policy Unit Bool := fun s r =>
  match r with
  | .claim _ task => dur (s.epoch task)
  | _ => 0

/-- Attempt `k`: the claim at real time `2k`, the expiry and the effect with its token at `2k + 1`. -/
def quickAttempts : ℕ → List (ℕ × Request Unit Bool)
  | 0 => []
  | n + 1 => quickAttempts n ++
      [(2 * n, .claim true ()), (2 * n + 1, .expire ()), (2 * n + 1, .effect true () (2 * n + 1))]

/-- **No duration policy is live in the asynchronous model.** For every duration chosen from the
epoch, the owner clock `jumpClock` advances by the granted duration during the one real tick in
which the effect travels. The correct worker answers every grant, every message arrives, the
timer fires, and the task is never done. -/
theorem async_never_completes (dur : ℕ → ℕ) (n : ℕ) :
    (timedRun (byEpoch dur) (jumpClock dur) Owner.start (quickAttempts n)).role () = .live ∧
      (timedRun (byEpoch dur) (jumpClock dur) Owner.start (quickAttempts n)).effects = [] ∧
      (timedRun (byEpoch dur) (jumpClock dur) Owner.start (quickAttempts n)).epoch () = 2 * n ∧
      (timedRun (byEpoch dur) (jumpClock dur) Owner.start (quickAttempts n)).clock ≤
        jumpClock dur (2 * n) := by
  induction n with
  | zero => simp [quickAttempts, timedRun, Owner.start, jumpClock]
  | succ n ih =>
      obtain ⟨live, noEffects, epochIs, clockLe⟩ := ih
      rw [quickAttempts, timedRun_append]
      set s := timedRun (byEpoch dur) (jumpClock dur) Owner.start (quickAttempts n)
      obtain ⟨role₁, epoch₁, effects₁, clock₁⟩ :=
        claim_live (byEpoch dur) (jumpClock dur) (g := 2 * n) (who := true) live
      set s₁ := timedStep (byEpoch dur) (jumpClock dur) s (2 * n, .claim true ())
      have clockMax : max s.clock (jumpClock dur (2 * n)) = jumpClock dur (2 * n) :=
        max_eq_right clockLe
      obtain ⟨role₂, epoch₂, effects₂, clock₂⟩ :=
        expire_due (byEpoch dur) (jumpClock dur) (s := s₁) (t := 2 * n + 1) role₁ (by
          simp only [clock₁, clockMax, byEpoch, catchUp, epochIs, jumpClock_succ]
          exact le_max_right _ _)
      set s₂ := timedStep (byEpoch dur) (jumpClock dur) s₁ (2 * n + 1, .expire ())
      obtain ⟨role₃, epoch₃, effects₃, clock₃⟩ :=
        effect_live (byEpoch dur) (jumpClock dur) (s := s₂) (t := 2 * n + 1) (who := true)
          (token := 2 * n + 1) role₂
      have runIs : timedRun (byEpoch dur) (jumpClock dur) s
          [(2 * n, .claim true ()), (2 * n + 1, .expire ()), (2 * n + 1, .effect true () (2 * n + 1))] =
          timedStep (byEpoch dur) (jumpClock dur) s₂ (2 * n + 1, .effect true () (2 * n + 1)) := rfl
      rw [runIs]
      refine ⟨by rw [role₃, role₂], by rw [effects₃, effects₂, effects₁, noEffects],
        by rw [epoch₃, epoch₂, epoch₁, epochIs]; ring, ?_⟩
      rw [clock₃, clock₂, clock₁, clockMax]
      have up := jumpClock_mono dur (show 2 * n ≤ 2 * (n + 1) by omega)
      have up' := jumpClock_mono dur (show 2 * n + 1 ≤ 2 * (n + 1) by omega)
      exact max_le (max_le up up') up'

/-- **A worker fenced out whatever its own clock says.** The owner's clock runs at `3` per tick;
worker `true` is granted the task at `0` until the owner's clock reads `6`; by real time `2` the
owner has expired the lease and granted it to `false`, which completes. The late effect of `true`
at real time `3` is refused, although by `true`'s own clock (rate `1`) its lease of `6` is still
running. -/
theorem slow_worker_fenced :
    let arrivals : List (ℕ × Request Unit Bool) :=
      [(0, .claim true ()), (2, .expire ()), (2, .claim false ()), (2, .effect false () 3),
        (3, .effect true () 1)]
    (fun t : ℕ => t) 3 < (fun t : ℕ => t) 0 + 6 ∧
      (timedRun (fixed 6) (fun t => 3 * t) Owner.start arrivals).effects = [((), false, 3)] := by
  refine ⟨by decide, by decide⟩

/-- Nominal rate `2`: the owner's clock runs at `3`, the worker's at `1`, each within drift `1`. -/
def fastOwner : Clock := fun t => 3 * t

/-- The slow worker's clock. -/
def slowWorker : Clock := fun t => t

theorem fastOwner_drift : BoundedDrift fastOwner 2 1 :=
  ⟨fun t d => by simp only [fastOwner]; ring_nf; omega,
    fun t d => by simp only [fastOwner]; ring_nf; omega⟩

theorem slowWorker_drift : BoundedDrift slowWorker 2 1 :=
  ⟨fun t d => by simp only [slowWorker]; omega, fun t d => by simp only [slowWorker]; omega⟩

/-- **A fast owner and a slow worker without fencing: two writes, the stale one last.** Both clocks
are within drift `1` of the nominal rate `2`; the duration is `6` and the worker uses all of it.
The owner grants at `0` and, its clock at `6` by real time `2`, grants again; the next holder
writes at `2` with epoch `3`. The first worker's clock shows `3 < 6` at real time `3`, so it still
believes in its lease and writes then, with epoch `1`; the write lands after the next grant, and
the margin condition of `write_lands_before_next_grant` fails. An unfenced resource takes both
writes and keeps the stale one last; a fencing resource refuses it. -/
theorem fast_owner_slow_worker :
    BoundedDrift fastOwner 2 1 ∧ BoundedDrift slowWorker 2 1 ∧
      fastOwner 0 + 6 ≤ fastOwner 2 ∧ slowWorker 3 < slowWorker 0 + 6 ∧ 2 ≤ 3 + 0 ∧
      ¬ (3 * (1 * 6 + 1 * 0) ≤ 1 * (1 * 6)) ∧
      ([((), 3, 30), ((), 1, 10)].foldl (fun writes w => writes ++ [w])
        ([] : List (Unit × ℕ × ℕ))).map (fun w => w.2.1) = [3, 1] ∧
      ([((), 3, 30), ((), 1, 10)].foldl (fun r w => FencedResource.write r w.1 w.2.1 w.2.2)
        (⟨fun _ => 0, []⟩ : FencedResource.Resource Unit ℕ)).writes = [((), 3, 30)] :=
  ⟨fastOwner_drift, slowWorker_drift, by decide, by decide, by decide, by decide, by decide,
    FencedResource.unfenced_stale_lands.2⟩

/-- **Positive control: a margin that covers the drift is safe.** With the same clocks and usable
time `2` instead of `6`, the margin condition holds, and a write the worker makes while its clock
shows less than `2` lands before the next grant. -/
theorem margin_suffices : 1 + 0 < 2 :=
  write_lands_before_next_grant (ownerClock := fastOwner) (holderClock := slowWorker)
    (den := 1) (slow := 1) (fast := 3) (usable := 2) (duration := 6) (Δ := 0)
    (sent := 0) (grant := 0) (next := 2) (u := 1) (δ := 0)
    (by simpa using fastOwner_drift.upper) (by simpa using slowWorker_drift.lower)
    Nat.one_pos (by decide) le_rfl (by decide) (by decide) (Nat.zero_le _) (by decide)
    le_rfl (by decide)

/-- **A paused worker has no lower rate**: a clock that stops satisfies no positive lower bound,
and the paused worker believes in its lease at every later time. -/
theorem paused_worker {slow : ℕ} (positive : 0 < slow) :
    ¬ (∀ t d, 1 * (fun _ : ℕ => 0) t + slow * d ≤ 1 * (fun _ : ℕ => 0) (t + d)) ∧
      ∀ u, (fun _ : ℕ => 0) u < (fun _ : ℕ => 0) 0 + 6 := by
  refine ⟨fun bound => ?_, fun _ => Nat.zero_lt_succ 5⟩
  have := bound 0 1
  simp at this
  omega

/-- **Perfect clocks and a delayed write.** Both clocks read real time; the duration is `4` and
the worker uses all of it. It writes at `3`, believing in its lease, and the write takes `2`: it
lands at `5`, after the next grant at `4`. The margin condition fails; usable time `2` satisfies
it. -/
theorem delayed_write_lands_late :
    (fun t : ℕ => t) 0 + 4 ≤ (fun t : ℕ => t) 4 ∧ (fun t : ℕ => t) 3 < (fun t : ℕ => t) 0 + 4 ∧
      4 ≤ 3 + 2 ∧ ¬ (1 * (1 * 4 + 1 * 2) ≤ 1 * (1 * 4)) ∧ 1 * (1 * 2 + 1 * 2) ≤ 1 * (1 * 4) := by
  decide

end Controls

end Mettapedia.GSLT.Timing.TimedLeases
