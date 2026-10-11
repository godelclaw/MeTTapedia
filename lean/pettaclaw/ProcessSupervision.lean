import EventPump
import ClawArchitectures
import HeartModel

/-!
# Supervising a memory-throttled agent loop

The cognition service runs under a memory controller with a soft limit `H`
(above it the kernel throttles every allocation of the service), a hard limit
`M` (an allocation above it kills the process), no swap, and a service
manager that restarts the process whenever it exits. Its memory grows with
work.

In the failure reconstructed here the service crossed `H` in the middle of a
command. Throttled, it made no progress, so it never reached `M`; and since
the service manager restarts only on exit, the process stayed frozen. A
periodic recycle only sets a flag that the loop honours at its next turn
boundary, which a frozen turn never reaches. Meanwhile the separate transport
kept accepting inputs, durably, as queued, and the status responder reported
the last checkpoint: `working`, `turn=completed`. A pressure killer attached to
the whole user session ended one such freeze after about eleven minutes and
did not act on another in eighteen: it watches the session's aggregate
pressure, which other running tasks keep low.

## Model

A synchronous transition system over ticks (`step`, `run`). In each tick the
transport records arrivals in the durable journal (`EventPump.Inbox`), the
process makes one move (`move`), and the watchdog or the environment may end
it; a process that is gone is restarted at the next tick. The environment
(`Tick`) chooses allocations, turn sizes, waits on external calls, arrivals,
recycle-timer firings, external kills, and whether the kernel withholds the
tick. The kernel's rules are built in: it withholds a tick only above `H`,
and an allocation above `M` kills.

## Results

Breaking theorems, for the deployed policy and every policy without a
graceful threshold or an independent backstop:
* `freeze_is_absorbing`: a throttled process that the kernel keeps
  withholding is never restarted, makes no progress and processes nothing.
* `unguarded_freezes_forever`, `incident_reconstruction`: turns that each grow
  memory by only `g` freeze the agent mid-turn, for ever.
* `unguarded_recycle_starves`: the boundary-honoured recycle request is set
  and never honoured.
* `unguarded_inputs_wait_forever`: inputs keep being accepted and are never
  processed.
* `unguarded_status_while_frozen`: the deployed responder reports
  `working`/`completed` throughout.
* `session_killer_silent_forever`, `session_killer_delay_unbounded`: an exact
  session-scoped pressure killer gives no per-agent bound.
* `throttle_sharing_watchdog_freezes`: a watchdog withheld with the service
  does not help, whatever its deadline.

The fixed design has four parts.
* (a) Graceful recycle below the soft limit: `graceful_never_throttles`,
  `graceful_fires_at_boundary` and `turn_growth_of_rate`. It is sharp
  (`graceful_bound_sharp`), and it is not a backstop
  (`runaway_freezes_without_backstop`).
* (b) An independent backstop: `backstop_bounds_silence`,
  `backstop_bounds_throttling` and `backstop_restores_progress` hold in every
  environment. The kill-path model (`unwithholdable_path_completes`,
  `withholdable_path_can_stall`) says exactly when a watchdog thread inside
  the service could serve, and `heartbeat_feed_never_fires` why the watchdog
  must be fed by progress.
* (c) Inputs acknowledged only after the checkpoint: `no_input_lost` holds in
  every environment, and `every_input_processed` gives processing within
  `2 (W + 1)(w + 1) + 3` ticks under `Nominal`. Each assumption is essential
  (`unbounded_wait_never_processes`, `poison_never_processed`,
  `short_deadline_kills_waiting`, `graceful_bound_sharp`,
  `threshold_below_fresh_livelocks`, `external_kills_starve`,
  `hard_limit_below_room_kills`), and acknowledging
  earlier loses inputs (`early_acknowledgement_loses`,
  `presentation_mark_loses_killed_turn`, `upstream_ack_first_loses`).
* (d) Status: `report_working_iff` is exact, `report_flags_freeze` reports the
  freeze, and `no_exact_stale_responder` shows that a freshness signal is
  necessary.

`fixed_resolves_incident` applies the fixed design to the incident's
workload; `freeze_stops_wakes` and `nominal_wakes_recur` relate the result to
the wake-counted guarantees of `ClawArchitectures`, `HeartModel` and
`FuelPolicy`.

## Trusted boundary

The kernel withholds only throttled ticks, and a kill takes effect even on a
throttled process. The service manager restarts a dead process at the next
tick, with no start-rate limit. Journal writes, checkpoints and
acknowledgements are atomic and durable. A tick must be long enough to hold a
watchdog poll and a kill. Nothing here verifies the kernel, the service
manager, the transport or the native runtime.
-/

namespace ProcessSupervision

/-! ## The supervised process -/

/-- Memory-controller limits of the cognition service, in one unit, and the
footprint of a freshly started process. -/
structure Limits where
  /-- Soft limit: above it, every allocation by the service is throttled. -/
  high : Nat
  /-- Hard limit: an allocation that would take the service above it kills it. -/
  max : Nat
  /-- Memory of a freshly started process. -/
  base : Nat
deriving Repr, DecidableEq

/-- Where the loop is. Inside a turn, `busy k` has `k + 1` work units left; the
first unit of a turn is its model call, the rest are its commands. -/
inductive Phase
  | boundary
  | busy (left : Nat)
deriving Repr, DecidableEq

/-- The cognition process. `turnBase` is its memory when the current turn
began, `recycle` a pending boundary-recycle request, and `claimed` the inputs
the current turn holds but has not yet acknowledged. -/
structure Proc where
  mem : Nat
  phase : Phase
  turnBase : Nat
  recycle : Bool
  claimed : List Nat
deriving Repr, DecidableEq

/-- A freshly started process; the boot clears any earlier recycle request. -/
def fresh (L : Limits) : Proc :=
  { mem := L.base, phase := .boundary, turnBase := L.base, recycle := false, claimed := [] }

/-- A process is running, or the service manager is about to restart it. -/
inductive Life
  | up (p : Proc)
  | down
deriving Repr, DecidableEq

/-- Everything outside the policy's control that happens in one tick. -/
structure Tick where
  /-- The kernel withholds the tick. Honoured only above the soft limit. -/
  stall : Bool := false
  /-- The turn waits on an external call (no progress, but legitimate). -/
  wait : Bool := false
  /-- Memory allocated and released by this tick's work unit. -/
  alloc : Nat := 0
  free : Nat := 0
  /-- Size of a turn started this tick (`work + 1` units). -/
  work : Nat := 0
  /-- Inputs the separate transport process accepts this tick. -/
  arrivals : List EventPump.Event := []
  /-- The periodic recycle timer fires. -/
  timer : Bool := false
  /-- The working set the loop checkpoints if a turn completes this tick. -/
  workingSet : HeartModel.S := ⟨HeartModel.maxLoops, HeartModel.defaultSleep⟩
  /-- Something outside the service kills it (a session-wide pressure killer,
  an operator). Constrained only where a theorem says so. -/
  externalKill : Bool := false
  /-- Some other task in the same session ran productively this tick. -/
  othersProductive : Bool := true

/-- A supervision policy. The deployed policy has none of these mechanisms:
its only ways out of a turn are the boundary-honoured recycle flag, the
hard-limit kill and external kills. -/
structure Policy where
  /-- Graceful layer: leave at a turn boundary when memory exceeds `T`. -/
  threshold : Option Nat := none
  /-- Backstop: kill after more than `D` consecutive throttled ticks. -/
  throttleDeadline : Option Nat := none
  /-- Backstop: kill after more than `D` consecutive ticks without progress. -/
  progressDeadline : Option Nat := none
  /-- The watchdog's kill path runs under the supervised service's throttle
  (for example a thread of the supervised process). -/
  sharesThrottle : Bool := false
deriving Repr, DecidableEq

/-- The deployed policy. -/
def deployed : Policy := {}

/-- Everything the supervision layer, the transport and the status responder
can see. `inbox` is the durable input journal shared with the transport;
`processed` lists inputs whose turns reached their checkpoint; `checkpoint`
and `callInFlight` are the status records the loop writes; `quiet` and
`pressure` are the watchdog's counters (ticks without progress, ticks above
the soft limit) for the current process; `lastProgress` is the durable
progress stamp. -/
structure State where
  life : Life
  inbox : EventPump.Inbox
  processed : List Nat
  checkpoint : HeartModel.S
  callInFlight : Bool
  quiet : Nat
  pressure : Nat
  clock : Nat
  lastProgress : Option Nat
  generation : Nat

/-- The process's own move in a tick. -/
inductive Move
  | stalled | waited | worked | passed | exited | oom
deriving Repr, DecidableEq

/-- Completed work units and boundary passes are the loop's progress points. -/
def Move.progress : Move → Bool
  | .worked => true
  | .passed => true
  | _ => false

/-- Moves after which no process remains. -/
def Move.ends : Move → Bool
  | .exited => true
  | .oom => true
  | _ => false

def grown (p : Proc) (e : Tick) : Nat := p.mem + e.alloc - e.free

/-- A boundary-only exit: the recycle flag, or the graceful threshold. -/
def leaves (P : Policy) (p : Proc) : Bool :=
  p.recycle || (match P.threshold with
    | some T => decide (T < p.mem)
    | none => false)

def move (P : Policy) (L : Limits) (p : Proc) (e : Tick) : Move :=
  if e.stall && decide (L.high < p.mem) then .stalled
  else match p.phase with
    | .boundary => if leaves P p then .exited else .passed
    | .busy _ =>
      if e.wait then .waited
      else if decide (L.max < grown p e) then .oom else .worked

/-- The serials of every pending input, claimed together when a turn starts. -/
def pendingIds (inbox : EventPump.Inbox) : List Nat :=
  (EventPump.pending inbox).map (·.serial)

def claimEach (ids : List Nat) (inbox : EventPump.Inbox) : EventPump.Inbox :=
  ids.foldl EventPump.claim inbox

def settleEach (ids : List Nat) (inbox : EventPump.Inbox) : EventPump.Inbox :=
  ids.foldl EventPump.settle inbox

/-- The last unit of a turn commits its checkpoint. -/
def completes (p : Proc) : Move → Bool
  | .worked => p.phase == .busy 0
  | _ => false

/-- The process after a move that keeps it alive. -/
def advance (p : Proc) (e : Tick) (ids : List Nat) : Move → Proc
  | .passed => { p with phase := .busy e.work, turnBase := p.mem, claimed := ids }
  | .worked =>
    match p.phase with
    | .busy (k + 1) => { p with mem := grown p e, phase := .busy k }
    | _ => { p with mem := grown p e, phase := .boundary, turnBase := grown p e, claimed := [] }
  | _ => p

/-- A turn start claims every pending input. A turn's claims are acknowledged
only by the checkpoint that completes it. -/
def inboxAfter (p : Proc) (inbox : EventPump.Inbox) : Move → EventPump.Inbox
  | .passed => claimEach (pendingIds inbox) inbox
  | .worked => if p.phase == .busy 0 then settleEach p.claimed inbox else inbox
  | _ => inbox

def overdue : Option Nat → Nat → Bool
  | some D, count => decide (D < count)
  | none, _ => false

/-- The watchdog's verdict. A watchdog that shares the throttle is withheld
whenever the kernel withholds the service above its soft limit. -/
def watchdogKills (P : Policy) (withheld : Bool) (quiet pressure : Nat) : Bool :=
  (overdue P.progressDeadline quiet || overdue P.throttleDeadline pressure) &&
    !(P.sharesThrottle && withheld)

/-- Whether the process is gone at the end of a tick in which it moved: it
left or was killed at the hard limit, the watchdog fired, or something
outside the service killed it. -/
def killedAt (P : Policy) (L : Limits) (s : State) (e : Tick) (p : Proc) : Bool :=
  let m := move P L p e
  let q := advance p e (pendingIds (e.arrivals.foldl EventPump.record s.inbox)) m
  m.ends ||
    watchdogKills P (e.stall && decide (L.high < q.mem))
      (if m.progress then 0 else s.quiet + 1)
      (if decide (L.high < q.mem) then s.pressure + 1 else 0) ||
    e.externalKill

/-- The next process, after a move that keeps one alive. -/
def survivor (s : State) (e : Tick) (p : Proc) (m : Move) : Proc :=
  let q := advance p e (pendingIds (e.arrivals.foldl EventPump.record s.inbox)) m
  { q with recycle := q.recycle || e.timer }

/-- One tick. The transport records arrivals first. A down service is
restarted. Otherwise the process moves; a death, the watchdog or an external
kill may end it, in which case its unacknowledged claims return to the queue;
a survivor may have its recycle flag set by the timer. -/
def step (P : Policy) (L : Limits) (s : State) (e : Tick) : State :=
  let inbox := e.arrivals.foldl EventPump.record s.inbox
  match s.life with
  | .down =>
    { s with life := .up (fresh L), inbox := inbox, quiet := 0, pressure := 0,
             clock := s.clock + 1, generation := s.generation + 1 }
  | .up p =>
    let m := move P L p e
    let q := advance p e (pendingIds inbox) m
    let killed := killedAt P L s e p
    let inbox₁ := inboxAfter p inbox m
    { life := if killed then .down else .up (survivor s e p m),
      inbox := if killed then EventPump.recover inbox₁ else inbox₁,
      processed := if completes p m then s.processed ++ p.claimed else s.processed,
      checkpoint := if completes p m then e.workingSet else s.checkpoint,
      callInFlight := if m == .passed then true else if m == .worked then false
        else s.callInFlight,
      quiet := if killed then 0 else if m.progress then 0 else s.quiet + 1,
      pressure := if killed then 0 else if decide (L.high < q.mem) then s.pressure + 1 else 0,
      clock := s.clock + 1,
      lastProgress := if m.progress then some (s.clock + 1) else s.lastProgress,
      generation := s.generation }

def run (P : Policy) (L : Limits) (env : Nat → Tick) (s : State) : Nat → State
  | 0 => s
  | n + 1 => step P L (run P L env s n) (env n)

/-- The process's move at tick `n`, if one is running. -/
def moveAt (P : Policy) (L : Limits) (env : Nat → Tick) (s : State) (n : Nat) : Option Move :=
  match (run P L env s n).life with
  | .up p => some (move P L p (env n))
  | .down => none

/-- Tick `n` is a progress point of the running process. -/
def progressAt (P : Policy) (L : Limits) (env : Nat → Tick) (s : State) (n : Nat) : Bool :=
  match moveAt P L env s n with
  | some m => m.progress
  | none => false

/-- The state the service boots into. -/
def boot (L : Limits) (owner : EventPump.Key) : State :=
  { life := .up (fresh L), inbox := { owner := owner }, processed := [],
    checkpoint := ⟨HeartModel.maxLoops, HeartModel.defaultSleep⟩, callInFlight := false,
    quiet := 0, pressure := 0, clock := 0, lastProgress := none, generation := 0 }

/-! ## Basic transition facts -/

section Basic

variable (P : Policy) (L : Limits)

@[simp] theorem step_clock (s : State) (e : Tick) : (step P L s e).clock = s.clock + 1 := by
  unfold step; split <;> rfl

theorem step_of_down (s : State) (e : Tick) (h : s.life = .down) :
    step P L s e =
      { s with life := .up (fresh L), inbox := e.arrivals.foldl EventPump.record s.inbox,
               quiet := 0, pressure := 0, clock := s.clock + 1,
               generation := s.generation + 1 } := by
  simp only [step, h]

theorem step_of_up (s : State) (e : Tick) (p : Proc) (h : s.life = .up p) :
    step P L s e =
      { life := if killedAt P L s e p then .down else .up (survivor s e p (move P L p e)),
        inbox := if killedAt P L s e p then
            EventPump.recover (inboxAfter p (e.arrivals.foldl EventPump.record s.inbox) (move P L p e))
          else inboxAfter p (e.arrivals.foldl EventPump.record s.inbox) (move P L p e),
        processed := if completes p (move P L p e) then s.processed ++ p.claimed else s.processed,
        checkpoint := if completes p (move P L p e) then e.workingSet else s.checkpoint,
        callInFlight := if move P L p e == .passed then true
          else if move P L p e == .worked then false else s.callInFlight,
        quiet := if killedAt P L s e p then 0
          else if (move P L p e).progress then 0 else s.quiet + 1,
        pressure := if killedAt P L s e p then 0
          else if decide (L.high < (advance p e (pendingIds (e.arrivals.foldl EventPump.record s.inbox))
            (move P L p e)).mem) then s.pressure + 1 else 0,
        clock := s.clock + 1,
        lastProgress := if (move P L p e).progress then some (s.clock + 1) else s.lastProgress,
        generation := s.generation } := by
  simp only [step, h]

@[simp] theorem run_zero (env : Nat → Tick) (s : State) : run P L env s 0 = s := rfl

theorem run_succ (env : Nat → Tick) (s : State) (n : Nat) :
    run P L env s (n + 1) = step P L (run P L env s n) (env n) := rfl

theorem run_clock (env : Nat → Tick) (s : State) (n : Nat) :
    (run P L env s n).clock = s.clock + n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, step_clock, ih]; omega

end Basic

/-! ## The freeze -/

/-- No watchdog that can act while the service is withheld: none at all, or one
that shares the service's throttle. -/
def NoIndependentBackstop (P : Policy) : Prop :=
  P.sharesThrottle = true ∨ (P.throttleDeadline = none ∧ P.progressDeadline = none)

theorem deployed_has_no_backstop : NoIndependentBackstop deployed := Or.inr ⟨rfl, rfl⟩

theorem watchdog_withheld (P : Policy) (hP : NoIndependentBackstop P) (q r : Nat) :
    watchdogKills P true q r = false := by
  rcases hP with h | ⟨h1, h2⟩
  · simp [watchdogKills, h]
  · simp [watchdogKills, overdue, h1, h2]

/-- A withheld tick of a throttled process changes nothing but time, the
counters, the journal and the recycle flag. -/
theorem frozen_tick (P : Policy) (L : Limits) (hP : NoIndependentBackstop P) (s : State)
    (e : Tick) (p : Proc) (hs : s.life = .up p) (hthr : L.high < p.mem)
    (hstall : e.stall = true) (hkill : e.externalKill = false) :
    step P L s e =
      { s with life := .up { p with recycle := p.recycle || e.timer },
               inbox := e.arrivals.foldl EventPump.record s.inbox,
               quiet := s.quiet + 1, pressure := s.pressure + 1, clock := s.clock + 1 } := by
  have hm : move P L p e = .stalled := by simp [move, hstall, hthr]
  rw [step_of_up P L s e p hs]
  simp [hm, killedAt, survivor, advance, Move.progress, Move.ends, inboxAfter, completes, hthr,
    hstall, hkill, watchdog_withheld P hP]

/-- Whether the recycle timer fired before tick `n`. -/
def timerBefore (env : Nat → Tick) : Nat → Bool
  | 0 => false
  | n + 1 => timerBefore env n || (env n).timer

/-- The journal after the transport alone has acted for `n` ticks. -/
def transported (env : Nat → Tick) (inbox : EventPump.Inbox) : Nat → EventPump.Inbox
  | 0 => inbox
  | n + 1 => (env n).arrivals.foldl EventPump.record (transported env inbox n)

/-- **The freeze is absorbing.** Without an independent backstop, a throttled
process that the kernel keeps withholding is never restarted, makes no
progress, processes nothing and writes no status. Only the transport (new
arrivals) and the recycle flag change; the flag is honoured only at a
boundary, which never comes. -/
theorem freeze_is_absorbing (P : Policy) (L : Limits) (hP : NoIndependentBackstop P)
    (env : Nat → Tick) (hstall : ∀ n, (env n).stall = true)
    (hkill : ∀ n, (env n).externalKill = false)
    (s : State) (p : Proc) (hs : s.life = .up p) (hthr : L.high < p.mem) (n : Nat) :
    run P L env s n =
      { s with life := .up { p with recycle := p.recycle || timerBefore env n },
               inbox := transported env s.inbox n,
               quiet := s.quiet + n, pressure := s.pressure + n, clock := s.clock + n } := by
  induction n with
  | zero =>
    cases s; simp only at hs; subst hs
    simp [timerBefore, transported]
  | succ n ih =>
    rw [run_succ, ih, frozen_tick P L hP _ _ { p with recycle := p.recycle || timerBefore env n }
      rfl hthr (hstall n) (hkill n)]
    simp only [timerBefore, transported, Bool.or_assoc]
    congr 1 <;> omega

theorem frozen_move (P : Policy) (L : Limits) (hP : NoIndependentBackstop P)
    (env : Nat → Tick) (hstall : ∀ n, (env n).stall = true)
    (hkill : ∀ n, (env n).externalKill = false)
    (s : State) (p : Proc) (hs : s.life = .up p) (hthr : L.high < p.mem) (n : Nat) :
    moveAt P L env s n = some .stalled := by
  simp [moveAt, freeze_is_absorbing P L hP env hstall hkill s p hs hthr n, move, hstall, hthr]

/-! ## The deployed policy freezes

The theorems in this part hold for the deployed policy and, more generally,
for every *unguarded* policy: one with no graceful threshold and no
independent backstop (`NoIndependentBackstop`). A watchdog that shares the
service's throttle is unguarded in this sense. -/

/-- The accumulation workload. Every turn has two units: its model call
allocates `g`, its command allocates nothing, so each turn grows memory by
exactly `g`. The kernel withholds every tick it is allowed to. The recycle
timer fires at every positive multiple of `R`, and from tick `R` on the
transport accepts one input per tick. -/
def accumulation (owner : EventPump.Key) (g R : Nat) (n : Nat) : Tick :=
  { stall := true, work := 1, alloc := if n % 3 = 1 then g else 0,
    timer := decide (0 < n ∧ n % R = 0),
    arrivals := if R ≤ n then [⟨n, owner, 0⟩] else [] }

def defaultWorkingSet : HeartModel.S := ⟨HeartModel.maxLoops, HeartModel.defaultSleep⟩

/-- The state at the boundary after `j` healthy turns of the accumulation workload. -/
def healthyAt (L : Limits) (owner : EventPump.Key) (g j : Nat) : State :=
  { life := .up { mem := L.base + j * g, phase := .boundary, turnBase := L.base + j * g,
                  recycle := false, claimed := [] },
    inbox := { owner := owner }, processed := [], checkpoint := defaultWorkingSet,
    callInFlight := false, quiet := 0, pressure := 0, clock := 3 * j,
    lastProgress := if j = 0 then none else some (3 * j), generation := 0 }

/-- Turn `j` has started: its model call is in flight. -/
def callNext (L : Limits) (owner : EventPump.Key) (g j : Nat) : State :=
  { life := .up { mem := L.base + j * g, phase := .busy 1, turnBase := L.base + j * g,
                  recycle := false, claimed := [] },
    inbox := { owner := owner }, processed := [], checkpoint := defaultWorkingSet,
    callInFlight := true, quiet := 0, pressure := 0,
    clock := 3 * j + 1, lastProgress := some (3 * j + 1), generation := 0 }

/-- Turn `j`'s model call has returned; its command is next. -/
def commandNext (L : Limits) (owner : EventPump.Key) (g j : Nat) : State :=
  { life := .up { mem := L.base + (j + 1) * g, phase := .busy 0, turnBase := L.base + j * g,
                  recycle := false, claimed := [] },
    inbox := { owner := owner }, processed := [], checkpoint := defaultWorkingSet,
    callInFlight := false, quiet := 0,
    pressure := if L.high < L.base + (j + 1) * g then 1 else 0,
    clock := 3 * j + 2, lastProgress := some (3 * j + 2), generation := 0 }

theorem boot_is_healthyAt (L : Limits) (owner : EventPump.Key) (g : Nat) :
    boot L owner = healthyAt L owner g 0 := by
  simp [boot, healthyAt, fresh, defaultWorkingSet]

theorem overdue_zero (d : Option Nat) : overdue d 0 = false := by
  cases d <;> simp [overdue]

section Accumulation

variable (P : Policy) (L : Limits) (owner : EventPump.Key) (g R : Nat)

theorem accumulation_pass (hthr : P.threshold = none) (j : Nat) (hj : L.base + j * g ≤ L.high)
    (hR : 3 * j + 2 < R) :
    step P L (healthyAt L owner g j) (accumulation owner g R (3 * j)) = callNext L owner g j := by
  have h0 : (3 * j) % 3 = 0 := by omega
  have hmod : 3 * j % R = 3 * j := Nat.mod_eq_of_lt (by omega)
  have hR' : ¬ R ≤ 3 * j := by omega
  have hlo : ¬ L.high < L.base + j * g := by omega
  simp [step, killedAt, survivor, healthyAt, callNext, accumulation, move, leaves, hthr,
    advance, inboxAfter, pendingIds, claimEach, EventPump.pending, completes, Move.progress,
    Move.ends, watchdogKills, overdue_zero, h0, hmod, hR', hlo]
  all_goals omega

theorem accumulation_call (hP : NoIndependentBackstop P) (j : Nat)
    (hj : L.base + j * g ≤ L.high) (hM : L.base + (j + 1) * g ≤ L.max) (hR : 3 * j + 2 < R) :
    step P L (callNext L owner g j) (accumulation owner g R (3 * j + 1)) =
      commandNext L owner g j := by
  have h1 : (3 * j + 1) % 3 = 1 := by omega
  have hmod : (3 * j + 1) % R = 3 * j + 1 := Nat.mod_eq_of_lt (by omega)
  have hR' : ¬ R ≤ 3 * j + 1 := by omega
  have hlo : ¬ L.high < L.base + j * g := by omega
  have hgrow : L.base + j * g + g = L.base + (j + 1) * g := by rw [Nat.succ_mul]; omega
  have hmax : ¬ L.max < L.base + (j + 1) * g := by omega
  by_cases hc : L.high < L.base + (j + 1) * g
  · simp [step, killedAt, survivor, callNext, commandNext, accumulation, move, advance,
      inboxAfter, grown, completes, Move.progress, Move.ends, h1, hmod, hR', hlo, hgrow, hmax, hc,
      watchdog_withheld P hP]
  · simp [step, killedAt, survivor, callNext, commandNext, accumulation, move, advance,
      inboxAfter, grown, completes, Move.progress, Move.ends, watchdogKills, overdue_zero, h1,
      hmod, hR', hlo, hgrow, hmax, hc]

theorem accumulation_command (j : Nat)
    (hj : L.base + (j + 1) * g ≤ L.high) (hM : L.base + (j + 1) * g ≤ L.max)
    (hR : 3 * j + 2 < R) :
    step P L (commandNext L owner g j) (accumulation owner g R (3 * j + 2)) =
      healthyAt L owner g (j + 1) := by
  have h2 : (3 * j + 2) % 3 = 2 := by omega
  have hmod : (3 * j + 2) % R = 3 * j + 2 := Nat.mod_eq_of_lt (by omega)
  have hR' : ¬ R ≤ 3 * j + 2 := by omega
  have hlo : ¬ L.high < L.base + (j + 1) * g := by omega
  have hmax : ¬ L.max < L.base + (j + 1) * g := by omega
  simp [step, killedAt, survivor, commandNext, healthyAt, accumulation, move, advance,
    inboxAfter, grown, settleEach, completes, Move.progress, Move.ends, watchdogKills, overdue_zero,
    defaultWorkingSet, h2, hmod, hR', hlo, hmax]
  omega

theorem accumulation_healthy (hthr : P.threshold = none) (hP : NoIndependentBackstop P)
    (k : Nat) (hk : L.base + k * g ≤ L.high) (hM : L.base + (k + 1) * g ≤ L.max)
    (hR : 3 * k + 2 < R) :
    ∀ j ≤ k, run P L (accumulation owner g R) (boot L owner) (3 * j) =
      healthyAt L owner g j := by
  intro j hj
  induction j with
  | zero => simp [boot_is_healthyAt L owner g]
  | succ j ih =>
    have hjk : j ≤ k := by omega
    have hmono : (j + 1) * g ≤ k * g := Nat.mul_le_mul_right g hj
    have hmono' : j * g ≤ (j + 1) * g := Nat.mul_le_mul_right g (by omega)
    have hmono2 : (j + 1) * g ≤ (k + 1) * g := Nat.mul_le_mul_right g (by omega)
    have e3 : 3 * (j + 1) = 3 * j + 2 + 1 := by omega
    rw [e3, run_succ, show 3 * j + 2 = 3 * j + 1 + 1 by omega, run_succ, run_succ, ih hjk,
      accumulation_pass P L owner g R hthr j (by omega) (by omega),
      accumulation_call P L owner g R hP j (by omega) (by omega) (by omega),
      accumulation_command P L owner g R j (by omega) (by omega) (by omega)]

theorem accumulation_reaches_freeze (hthr : P.threshold = none) (hP : NoIndependentBackstop P)
    (k : Nat) (hk : L.base + k * g ≤ L.high) (hM : L.base + (k + 1) * g ≤ L.max)
    (hR : 3 * k + 2 < R) :
    run P L (accumulation owner g R) (boot L owner) (3 * k + 2) = commandNext L owner g k := by
  rw [run_succ, run_succ, accumulation_healthy P L owner g R hthr hP k hk hM hR k (Nat.le_refl k),
    accumulation_pass P L owner g R hthr k hk hR,
    accumulation_call P L owner g R hP k hk hM hR]

end Accumulation

theorem run_add (P : Policy) (L : Limits) (env : Nat → Tick) (s : State) (a b : Nat) :
    run P L env s (a + b) = run P L (fun n => env (a + n)) (run P L env s a) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, run_succ, ih, run_succ]

/-! ### The journal under the transport alone -/

theorem record_owner (s : EventPump.Inbox) (e : EventPump.Event) :
    (EventPump.record s e).owner = s.owner := by
  unfold EventPump.record; split <;> rfl

theorem record_phase (s : EventPump.Inbox) (e : EventPump.Event) (id : Nat) :
    (EventPump.record s e).phase id =
      if e.owner = s.owner ∧ s.phase e.serial = none ∧ id = e.serial then some .queued
      else s.phase id := by
  unfold EventPump.record
  by_cases h : e.owner = s.owner ∧ s.phase e.serial = none
  · by_cases hid : id = e.serial <;> simp [h, hid]
  · simp only [h, if_false]
    by_cases hid : id = e.serial
    · subst hid; simp_all
    · simp [hid]

theorem recordAll_owner (s : EventPump.Inbox) (es : List EventPump.Event) :
    (es.foldl EventPump.record s).owner = s.owner := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => rw [List.foldl_cons, ih, record_owner]

/-- Recording never changes a phase that is already set. -/
theorem recordAll_keeps_phase (s : EventPump.Inbox) (es : List EventPump.Event) (id : Nat)
    (x : EventPump.Delivery) (h : s.phase id = some x) :
    (es.foldl EventPump.record s).phase id = some x := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih =>
    rw [List.foldl_cons]
    apply ih
    rw [record_phase]
    split
    · rename_i hc
      obtain ⟨_, hnone, hid⟩ := hc
      subst hid
      rw [hnone] at h
      exact absurd h (by simp)
    · exact h

/-- Recording events with other serials leaves a phase unchanged. -/
theorem recordAll_other_phase (s : EventPump.Inbox) (es : List EventPump.Event) (id : Nat)
    (h : ∀ e ∈ es, e.serial ≠ id) :
    (es.foldl EventPump.record s).phase id = s.phase id := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    rw [List.foldl_cons, ih _ (fun x hx => h x (List.mem_cons_of_mem e hx)), record_phase]
    have := h e List.mem_cons_self
    simp [Ne.symm this]

theorem transported_owner (env : Nat → Tick) (inbox : EventPump.Inbox) (n : Nat) :
    (transported env inbox n).owner = inbox.owner := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [transported]; rw [recordAll_owner, ih]

theorem transported_keeps_phase (env : Nat → Tick) (inbox : EventPump.Inbox) (id : Nat)
    (x : EventPump.Delivery) (a : Nat) (h : (transported env inbox a).phase id = some x) :
    ∀ b, (transported env inbox (a + b)).phase id = some x := by
  intro b
  induction b with
  | zero => exact h
  | succ b ih => rw [← Nat.add_assoc]; exact recordAll_keeps_phase _ _ id x ih

/-- An input offered with a serial nobody has used, under the journal's owner,
is queued from the tick it arrives on. -/
theorem transported_accepts (env : Nat → Tick) (inbox : EventPump.Inbox) (a : Nat)
    (e : EventPump.Event) (hin : (env a).arrivals = [e]) (howner : e.owner = inbox.owner)
    (hfresh : (transported env inbox a).phase e.serial = none) :
    (transported env inbox (a + 1)).phase e.serial = some .queued := by
  simp only [transported, hin, List.foldl_cons, List.foldl_nil]
  rw [record_phase, transported_owner]
  simp [howner, hfresh]

theorem transported_unrelated (env : Nat → Tick) (inbox : EventPump.Inbox) (id : Nat) :
    ∀ n, (∀ i < n, ∀ e ∈ (env i).arrivals, e.serial ≠ id) →
      (transported env inbox n).phase id = inbox.phase id := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [transported]
    rw [recordAll_other_phase _ _ id (h n (Nat.lt_succ_self n)), ih (fun i hi => h i (by omega))]

theorem timerBefore_of (env : Nat → Tick) (i : Nat) (h : (env i).timer = true) :
    ∀ n, i < n → timerBefore env n = true := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [timerBefore]
    by_cases hin : i < n
    · rw [ih hin]; rfl
    · have : i = n := by omega
      subst this; rw [h]; simp

/-! ### The deployed status responder -/

inductive Activity
  | working | idle
deriving Repr, DecidableEq

inductive TurnMark
  | pending | completed
deriving Repr, DecidableEq

structure DeployedReport where
  activity : Activity
  turn : TurnMark
deriving Repr, DecidableEq

/-- The deployed activity rule: a model call in flight, or loop budget left in
the last checkpoint, reads as working, whatever the checkpoint's age. -/
def deployedReport (s : State) : DeployedReport :=
  { activity := if s.callInFlight || decide (0 < s.checkpoint.loops) then .working else .idle,
    turn := if s.callInFlight then .pending else .completed }

/-! ### The freeze, reconstructed -/

section DeployedFreeze

variable (P : Policy) (L : Limits) (owner : EventPump.Key) (g R k : Nat)

/-- The accumulation workload seen from the freeze onwards. -/
def afterFreeze (i : Nat) : Tick := accumulation owner g R (3 * k + 2 + i)

theorem accumulation_after_freeze (hthr : P.threshold = none) (hP : NoIndependentBackstop P)
    (hk : L.base + k * g ≤ L.high)
    (hk' : L.high < L.base + (k + 1) * g) (hM : L.base + (k + 1) * g ≤ L.max)
    (hR : 3 * k + 2 < R) (n : Nat) :
    run P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n) =
      { commandNext L owner g k with
        life := .up { mem := L.base + (k + 1) * g, phase := .busy 0, turnBase := L.base + k * g,
                      recycle := timerBefore (afterFreeze owner g R k) n, claimed := [] },
        inbox := transported (afterFreeze owner g R k) { owner := owner } n,
        quiet := n, pressure := 1 + n, clock := 3 * k + 2 + n } := by
  rw [run_add, accumulation_reaches_freeze P L owner g R hthr hP k hk hM hR]
  change run P L (afterFreeze owner g R k) _ n = _
  rw [freeze_is_absorbing P L hP (afterFreeze owner g R k)
    (fun _ => rfl) (fun _ => rfl) (commandNext L owner g k) _ rfl hk' n]
  simp [commandNext, hk']

/-- **Breaking theorem (liveness).** Under the deployed policy, and under
every policy with neither a graceful threshold nor an independent backstop,
the accumulation workload freezes the agent mid-turn, and the execution stays
frozen forever: from tick `3k + 2` on, every tick is withheld, the process is
never restarted, and its command never completes. Every turn grew memory by
only `g`, and the kernel withholds only throttled ticks. -/
theorem unguarded_freezes_forever (hthr : P.threshold = none)
    (hP : NoIndependentBackstop P) (hk : L.base + k * g ≤ L.high)
    (hk' : L.high < L.base + (k + 1) * g) (hM : L.base + (k + 1) * g ≤ L.max)
    (hR : 3 * k + 2 < R) (n : Nat) :
    (∃ r, (run P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n)).life =
      .up { mem := L.base + (k + 1) * g, phase := .busy 0, turnBase := L.base + k * g,
            recycle := r, claimed := [] }) ∧
    moveAt P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n) = some .stalled ∧
    progressAt P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n) = false ∧
    (run P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n)).generation = 0 ∧
    (run P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n)).processed = [] := by
  have h := accumulation_after_freeze P L owner g R k hthr hP hk hk' hM hR n
  have hm : moveAt P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n) =
      some .stalled := by
    simp [moveAt, h, move, accumulation, hk']
  refine ⟨⟨_, by rw [h]⟩, hm, ?_, by rw [h]; rfl, by rw [h]; rfl⟩
  simp [progressAt, hm, Move.progress]

/-- **Breaking theorem (recycle starvation).** The periodic recycle request
fires at tick `R`, after the freeze, and is never honoured: from then on the
flag stays set and the frozen process is never replaced. -/
theorem unguarded_recycle_starves (hthr : P.threshold = none)
    (hP : NoIndependentBackstop P) (hk : L.base + k * g ≤ L.high)
    (hk' : L.high < L.base + (k + 1) * g) (hM : L.base + (k + 1) * g ≤ L.max)
    (hR : 3 * k + 2 < R) (n : Nat) (hn : R < 3 * k + 2 + n) :
    (run P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n)).life =
      .up { mem := L.base + (k + 1) * g, phase := .busy 0, turnBase := L.base + k * g,
            recycle := true, claimed := [] } := by
  rw [accumulation_after_freeze P L owner g R k hthr hP hk hk' hM hR n]
  have ht : (afterFreeze owner g R k (R - (3 * k + 2))).timer = true := by
    simp only [afterFreeze, accumulation, show 3 * k + 2 + (R - (3 * k + 2)) = R by omega,
      Nat.mod_self]
    simp; omega
  simp [timerBefore_of _ _ ht n (by omega)]

/-- **Breaking theorem (inputs).** The transport keeps accepting inputs: each
one offered at tick `m ≥ R` is durably queued from then on. None is lost,
and none is ever processed. -/
theorem unguarded_inputs_wait_forever (hthr : P.threshold = none)
    (hP : NoIndependentBackstop P) (hk : L.base + k * g ≤ L.high)
    (hk' : L.high < L.base + (k + 1) * g) (hM : L.base + (k + 1) * g ≤ L.max)
    (hR : 3 * k + 2 < R) (m n : Nat) (hm : R ≤ m) (hmn : m < 3 * k + 2 + n) :
    (run P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n)).inbox.phase m =
      some .queued ∧
    m ∉ (run P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n)).processed := by
  rw [accumulation_after_freeze P L owner g R k hthr hP hk hk' hM hR n]
  refine ⟨?_, by simp [commandNext]⟩
  simp only
  have ha : m = 3 * k + 2 + (m - (3 * k + 2)) := by omega
  have hbefore : (transported (afterFreeze owner g R k) { owner := owner } (m - (3 * k + 2))).phase m
      = none := by
    rw [transported_unrelated]
    intro i hi e he
    simp only [afterFreeze, accumulation] at he
    split at he
    · simp at he; subst he; simp; omega
    · simp at he
  have hacc := transported_accepts (afterFreeze owner g R k) { owner := owner } (m - (3 * k + 2))
    ⟨m, owner, 0⟩ (by simp only [afterFreeze, accumulation, ← ha]; simp [hm]) rfl hbefore
  have hkeep := transported_keeps_phase (afterFreeze owner g R k) { owner := owner } m .queued
    (m - (3 * k + 2) + 1) hacc (n - (m - (3 * k + 2) + 1))
  rwa [show m - (3 * k + 2) + 1 + (n - (m - (3 * k + 2) + 1)) = n by omega] at hkeep

/-- **Breaking theorem (status).** While frozen, the deployed responder
reports `activity: working` and `turn=completed`: the checkpoint still holds
loop budget, and the model call had returned before the command froze. The
loop budget is permission to work (`HeartModel`'s gate `0 < loops`), not
evidence of progress. -/
theorem unguarded_status_while_frozen (hthr : P.threshold = none)
    (hP : NoIndependentBackstop P) (hk : L.base + k * g ≤ L.high)
    (hk' : L.high < L.base + (k + 1) * g) (hM : L.base + (k + 1) * g ≤ L.max)
    (hR : 3 * k + 2 < R) (n : Nat) :
    deployedReport (run P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n)) =
      ⟨.working, .completed⟩ := by
  rw [accumulation_after_freeze P L owner g R k hthr hP hk hk' hM hR n]
  simp [deployedReport, commandNext, defaultWorkingSet, HeartModel.maxLoops]

end DeployedFreeze

/-- The deployed limits, in MiB: soft limit 3 GiB, hard limit 4 GiB. With a
20-second tick, the accumulation workload grows memory by 41 MiB per minute
and the two-hour recycle timer fires at tick 360. The 512 MiB footprint of a
fresh process is illustrative. -/
def deployedLimits : Limits := ⟨3072, 4096, 512⟩

/-- **The incident, reconstructed.** With the deployed limits the agent
freezes at tick 188 (about 63 minutes) and stays frozen. The recycle requested
at two hours is never honoured, and the deployed responder reports
`working`/`completed` throughout. -/
theorem incident_reconstruction (owner : EventPump.Key) (n : Nat) :
    moveAt deployed deployedLimits (accumulation owner 41 360) (boot deployedLimits owner)
        (188 + n) = some .stalled ∧
    (run deployed deployedLimits (accumulation owner 41 360) (boot deployedLimits owner)
        (188 + n)).generation = 0 ∧
    deployedReport (run deployed deployedLimits (accumulation owner 41 360)
        (boot deployedLimits owner) (188 + n)) = ⟨.working, .completed⟩ ∧
    (360 < 188 + n →
      ∃ p, (run deployed deployedLimits (accumulation owner 41 360) (boot deployedLimits owner)
        (188 + n)).life = .up p ∧ p.recycle = true ∧ p.phase = .busy 0) := by
  have h := unguarded_freezes_forever deployed deployedLimits owner 41 360 62 rfl
    deployed_has_no_backstop (by decide) (by decide) (by decide) (by decide) n
  refine ⟨h.2.1, h.2.2.2.1,
    unguarded_status_while_frozen deployed deployedLimits owner 41 360 62 rfl
      deployed_has_no_backstop (by decide) (by decide) (by decide) (by decide) n, fun hn => ?_⟩
  exact ⟨_, unguarded_recycle_starves deployed deployedLimits owner 41 360 62 rfl
    deployed_has_no_backstop (by decide) (by decide) (by decide) (by decide) n hn, rfl, rfl⟩

/-! ## A session-scoped pressure killer gives no per-agent bound

A pressure killer attached to the whole user session watches the session's
full memory pressure: the share of time in which every non-idle task of the
session is delayed. While any other task of the session keeps running, that
pressure stays low, however long the agent has been withheld. -/

/-- Session-wide full pressure during tick `n`: the agent is withheld by its
throttle and no other task of the session runs productively. -/
def SessionFull (P : Policy) (L : Limits) (env : Nat → Tick) (s : State) (n : Nat) : Prop :=
  moveAt P L env s n = some .stalled ∧ (env n).othersProductive = false

/-- A session-scoped killer with sustain window `S` kills exactly when the
session has been fully pressured for the last `S + 1` ticks. The model grants
it the agent as its victim; in operation it picks the most pressured unit of
the session. -/
def SessionKiller (S : Nat) (P : Policy) (L : Limits) (env : Nat → Tick) (s : State) : Prop :=
  ∀ n, (env n).externalKill = true ↔ (S ≤ n ∧ ∀ i ≤ S, SessionFull P L env s (n - i))

theorem move_ignores_session (P : Policy) (L : Limits) (p : Proc) (e : Tick) (b k : Bool) :
    move P L p { e with othersProductive := b, externalKill := k } = move P L p e := rfl

theorem step_ignores_session (P : Policy) (L : Limits) (s : State) (e : Tick) (b : Bool)
    (h : e.externalKill = false) :
    step P L s { e with othersProductive := b, externalKill := false } = step P L s e := by
  cases e; simp only at h; subst h; rfl

/-- **Breaking theorem (session killer, silent).** For every sustain window,
a session-scoped killer is consistent with an agent frozen forever: the
deployed freeze happens while other tasks of the session keep running, the
session is never fully pressured, and the killer never acts. -/
theorem session_killer_silent_forever (L : Limits) (owner : EventPump.Key) (g R k S : Nat)
    (hk : L.base + k * g ≤ L.high) (hk' : L.high < L.base + (k + 1) * g)
    (hM : L.base + (k + 1) * g ≤ L.max) (hR : 3 * k + 2 < R) :
    SessionKiller S deployed L (accumulation owner g R) (boot L owner) ∧
    ∀ n, moveAt deployed L (accumulation owner g R) (boot L owner) (3 * k + 2 + n) =
      some .stalled := by
  refine ⟨fun n => ?_, fun n => (unguarded_freezes_forever deployed L owner g R k rfl deployed_has_no_backstop hk hk' hM hR
    n).2.1⟩
  constructor
  · intro h; simp [accumulation] at h
  · rintro ⟨_, hall⟩
    have := (hall 0 (Nat.zero_le _)).2
    simp [accumulation] at this

/-- The accumulation workload with the rest of the session idle during
`[K - S, K]` only, and the session killer acting at `K`. -/
def lateSession (owner : EventPump.Key) (g R K S : Nat) (n : Nat) : Tick :=
  { accumulation owner g R n with
    othersProductive := !(K - S ≤ n && n ≤ K), externalKill := decide (n = K) }

theorem lateSession_agrees (owner : EventPump.Key) (g R K S : Nat) (L : Limits) (P : Policy)
    (s : State) : ∀ n ≤ K, run P L (lateSession owner g R K S) s n = run P L (accumulation owner g R) s n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, run_succ, ih (by omega)]
    have hne : decide (n = K) = false := by simp; omega
    simp only [lateSession, hne]
    exact step_ignores_session P L _ _ _ rfl

/-- **Breaking theorem (session killer, unbounded delay).** For every bound
`B` there is an execution, consistent with an exact session-scoped killer of
any sustain window `S`, in which the agent is withheld for more than `B`
consecutive ticks before the killer ends the freeze. The delay is set by
when unrelated tasks fall idle, not by the agent. -/
theorem session_killer_delay_unbounded (L : Limits) (owner : EventPump.Key) (g R k S B : Nat)
    (hk : L.base + k * g ≤ L.high) (hk' : L.high < L.base + (k + 1) * g)
    (hM : L.base + (k + 1) * g ≤ L.max) (hR : 3 * k + 2 < R) :
    let K := 3 * k + 2 + B + S
    let env := lateSession owner g R K S
    SessionKiller S deployed L env (boot L owner) ∧
    (∀ i ≤ B + S, moveAt deployed L env (boot L owner) (3 * k + 2 + i) = some .stalled) ∧
    (run deployed L env (boot L owner) (K + 1)).life = .down := by
  intro K env
  have hstalled : ∀ i ≤ B + S, moveAt deployed L env (boot L owner) (3 * k + 2 + i) =
      some .stalled := by
    intro i hi
    have hfr := (unguarded_freezes_forever deployed L owner g R k rfl deployed_has_no_backstop hk hk' hM hR
      i).2.1
    simp only [moveAt] at hfr ⊢
    rw [lateSession_agrees owner g R K S L deployed (boot L owner) _ (by omega)]
    revert hfr
    cases (run deployed L (accumulation owner g R) (boot L owner) (3 * k + 2 + i)).life with
    | down => simp
    | up p => intro hfr; simp only [env, lateSession, move_ignores_session]; exact hfr
  have hkiller : SessionKiller S deployed L env (boot L owner) := by
    intro n
    constructor
    · intro h
      have hn : n = K := by simpa [env, lateSession] using h
      subst hn
      refine ⟨by omega, fun i hi => ⟨?_, ?_⟩⟩
      · have := hstalled (B + S - i) (by omega)
        rwa [show 3 * k + 2 + (B + S - i) = K - i by omega] at this
      · simp [env, lateSession]; omega
    · rintro ⟨hS, hall⟩
      have h0 := (hall 0 (Nat.zero_le _)).2
      have hSf := (hall S (Nat.le_refl _)).2
      simp [env, lateSession] at h0 hSf ⊢
      omega
  refine ⟨hkiller, hstalled, ?_⟩
  have hK : moveAt deployed L env (boot L owner) K = some .stalled := by
    have := hstalled (B + S) (Nat.le_refl _)
    rwa [show 3 * k + 2 + (B + S) = K by omega] at this
  rw [run_succ]
  simp only [moveAt] at hK
  revert hK
  cases hlife : (run deployed L env (boot L owner) K).life with
  | down => simp
  | up p =>
    intro _
    rw [step_of_up deployed L _ _ p hlife]
    simp [killedAt, env, lateSession]

/-! ## Inversion lemmas -/

section Inversion

variable {P : Policy} {L : Limits} {p : Proc} {e : Tick}

theorem move_stalled_iff : move P L p e = .stalled ↔ e.stall = true ∧ L.high < p.mem := by
  unfold move
  by_cases h : e.stall = true ∧ L.high < p.mem
  · simp [h.1, h.2]
  · have : (e.stall && decide (L.high < p.mem)) = false := by
      cases hs : e.stall <;> simp_all
    rw [this]; simp only [Bool.false_eq_true, if_false]
    constructor
    · intro hm
      split at hm
      · split at hm <;> cases hm
      · split at hm
        · cases hm
        · split at hm <;> cases hm
    · intro h'; exact absurd h' h

theorem not_stalled_of_le (hle : p.mem ≤ L.high) : move P L p e ≠ .stalled := by
  rw [Ne, move_stalled_iff]; omega

theorem move_of_not_withheld (h : ¬ (e.stall = true ∧ L.high < p.mem)) :
    move P L p e = match p.phase with
      | .boundary => if leaves P p then .exited else .passed
      | .busy _ => if e.wait then .waited else if decide (L.max < grown p e) then .oom else .worked := by
  have : (e.stall && decide (L.high < p.mem)) = false := by
    cases hs : e.stall <;> simp_all
  simp only [move, this, Bool.false_eq_true, if_false]

theorem move_passed (h : move P L p e = .passed) : p.phase = .boundary ∧ leaves P p = false := by
  unfold move at h
  split at h
  · cases h
  · split at h
    · rename_i hph; split at h
      · cases h
      · rename_i hl; exact ⟨hph, by simpa using hl⟩
    · split at h
      · cases h
      · split at h <;> cases h

theorem move_exited (h : move P L p e = .exited) : p.phase = .boundary ∧ leaves P p = true := by
  unfold move at h
  split at h
  · cases h
  · split at h
    · rename_i hph; split at h
      · rename_i hl; exact ⟨hph, hl⟩
      · cases h
    · split at h
      · cases h
      · split at h <;> cases h

theorem move_worked (h : move P L p e = .worked) :
    (∃ k, p.phase = .busy k) ∧ e.wait = false ∧ grown p e ≤ L.max ∧
      ¬ (e.stall = true ∧ L.high < p.mem) := by
  unfold move at h
  split at h
  · cases h
  · rename_i hns
    split at h
    · split at h <;> cases h
    · rename_i k hph
      split at h
      · cases h
      · rename_i hw
        split at h
        · cases h
        · rename_i hM
          refine ⟨⟨k, hph⟩, by simpa using hw, by simp at hM; omega, ?_⟩
          intro ⟨h1, h2⟩; simp [h1, h2] at hns

theorem move_waited (h : move P L p e = .waited) : (∃ k, p.phase = .busy k) ∧ e.wait = true := by
  unfold move at h
  split at h
  · cases h
  · split at h
    · split at h <;> cases h
    · rename_i k hph
      split at h
      · rename_i hw; exact ⟨⟨k, hph⟩, hw⟩
      · split at h <;> cases h

theorem move_oom (h : move P L p e = .oom) : (∃ k, p.phase = .busy k) ∧ L.max < grown p e := by
  unfold move at h
  split at h
  · cases h
  · split at h
    · split at h <;> cases h
    · rename_i k hph
      split at h
      · cases h
      · split at h
        · rename_i hM; exact ⟨⟨k, hph⟩, by simpa using hM⟩
        · cases h

end Inversion

theorem step_life_cases (P : Policy) (L : Limits) (s : State) (e : Tick) :
    (step P L s e).life = .down ∨
    (s.life = .down ∧ (step P L s e).life = .up (fresh L)) ∨
    (∃ p, s.life = .up p ∧ (step P L s e).life = .up (survivor s e p (move P L p e)) ∧
      killedAt P L s e p = false) := by
  cases hs : s.life with
  | down => right; left; exact ⟨rfl, by rw [step_of_down P L s e hs]⟩
  | up p =>
    rw [step_of_up P L s e p hs]
    cases hk : killedAt P L s e p
    · right; right; exact ⟨p, rfl, by simp, hk⟩
    · left; simp

theorem killedAt_false_not_ends {P : Policy} {L : Limits} {s : State} {e : Tick} {p : Proc}
    (h : killedAt P L s e p = false) : (move P L p e).ends = false := by
  simp only [killedAt, Bool.or_eq_false_iff] at h
  exact h.1.1

/-! ## Layer (a): graceful recycle below the soft limit -/

/-- The workload keeps every turn within `δ` of the memory it started with. -/
def TurnGrowthWithin (δ : Nat) (P : Policy) (L : Limits) (env : Nat → Tick) (s : State) :
    Prop :=
  ∀ n p, (run P L env s n).life = .up p → move P L p (env n) = .worked →
    grown p (env n) ≤ p.turnBase + δ

/-- Memory bounds of a process under the graceful layer. -/
def Graceful (T δ : Nat) (p : Proc) : Prop :=
  (p.phase = .boundary → p.mem ≤ T + δ) ∧
  (∀ k, p.phase = .busy k → p.turnBase ≤ T ∧ p.mem ≤ p.turnBase + δ)

def GracefulInv (T δ : Nat) (s : State) : Prop := ∀ p, s.life = .up p → Graceful T δ p

theorem graceful_survivor (P : Policy) (L : Limits) (T δ : Nat) (hT : P.threshold = some T)
    (s : State) (e : Tick) (p : Proc) (hp : Graceful T δ p)
    (hgrow : move P L p e = .worked → grown p e ≤ p.turnBase + δ) :
    Graceful T δ (survivor s e p (move P L p e)) := by
  generalize hm : move P L p e = m at hgrow
  cases m with
  | passed =>
    obtain ⟨hph, hl⟩ := move_passed hm
    have hmem : p.mem ≤ T := by
      simp only [leaves, hT, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hl; omega
    refine ⟨fun h => by simp [survivor, advance] at h, fun k hk => ?_⟩
    simp [survivor, advance] at hk ⊢
    exact hmem
  | worked =>
    obtain ⟨⟨k, hph⟩, -, -, -⟩ := move_worked hm
    have hg := hgrow rfl
    have hb := (hp.2 k hph).1
    cases k with
    | zero =>
      refine ⟨fun _ => ?_, fun k hk => ?_⟩
      · simp [survivor, advance, hph]; omega
      · simp [survivor, advance, hph] at hk
    | succ k =>
      refine ⟨fun h => by simp [survivor, advance, hph] at h, fun k' hk => ?_⟩
      simp [survivor, advance, hph] at hk ⊢
      exact ⟨hb, hg⟩
  | stalled => simpa [survivor, advance, Graceful] using hp
  | waited => simpa [survivor, advance, Graceful] using hp
  | exited => simpa [survivor, advance, Graceful] using hp
  | oom => simpa [survivor, advance, Graceful] using hp

theorem fresh_graceful (L : Limits) (T δ : Nat) (hbase : L.base ≤ T) :
    Graceful T δ (fresh L) :=
  ⟨fun _ => by simp [fresh]; omega, fun k hk => by simp [fresh] at hk⟩

theorem graceful_invariant (P : Policy) (L : Limits) (env : Nat → Tick) (s : State)
    (T δ : Nat) (hT : P.threshold = some T) (hbase : L.base ≤ T)
    (h0 : GracefulInv T δ s) (hgrow : TurnGrowthWithin δ P L env s) :
    ∀ n, GracefulInv T δ (run P L env s n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    intro q hq
    rw [run_succ] at hq
    rcases step_life_cases P L (run P L env s n) (env n) with hd | ⟨_, hf⟩ | ⟨p, hp, hl, _⟩
    · rw [hd] at hq; cases hq
    · rw [hf] at hq; cases hq; exact fresh_graceful L T δ hbase
    · rw [hl] at hq; cases hq
      exact graceful_survivor P L T δ hT _ _ p (ih p hp) (hgrow n p hp)

theorem boot_graceful (L : Limits) (owner : EventPump.Key) (T δ : Nat) (hbase : L.base ≤ T) :
    GracefulInv T δ (boot L owner) := by
  intro p hp; cases hp; exact fresh_graceful L T δ hbase

/-- **Layer (a), safety.** If every turn grows memory by at most `δ`, the
graceful threshold `T` satisfies `T + δ ≤ H`, and a fresh process starts at
or below `T`, the service never enters the throttled regime, whatever the
watchdog does. -/
theorem graceful_never_throttles (P : Policy) (L : Limits) (env : Nat → Tick)
    (owner : EventPump.Key) (T δ : Nat) (hT : P.threshold = some T) (hbase : L.base ≤ T)
    (hroom : T + δ ≤ L.high) (hgrow : TurnGrowthWithin δ P L env (boot L owner)) :
    ∀ n p, (run P L env (boot L owner) n).life = .up p → p.mem ≤ L.high := by
  intro n p hp
  have hg := graceful_invariant P L env (boot L owner) T δ hT hbase
    (boot_graceful L owner T δ hbase) hgrow n p hp
  cases hph : p.phase with
  | boundary => have := hg.1 hph; omega
  | busy k => have := hg.2 k hph; omega

/-- **Layer (a), the recycle fires.** At a boundary where memory exceeds `T`
the process leaves at that very tick: it is below the soft limit, so the
kernel cannot withhold the exit. The same holds for a pending recycle
request. -/
theorem graceful_fires_at_boundary (P : Policy) (L : Limits) (env : Nat → Tick)
    (owner : EventPump.Key) (T δ : Nat) (hT : P.threshold = some T) (hbase : L.base ≤ T)
    (hroom : T + δ ≤ L.high) (hgrow : TurnGrowthWithin δ P L env (boot L owner))
    (n : Nat) (p : Proc) (hp : (run P L env (boot L owner) n).life = .up p)
    (hb : p.phase = .boundary) (hover : T < p.mem ∨ p.recycle = true) :
    (run P L env (boot L owner) (n + 1)).life = .down := by
  have hle := graceful_never_throttles P L env owner T δ hT hbase hroom hgrow n p hp
  have hm : move P L p (env n) = .exited := by
    rw [move_of_not_withheld (by omega), hb]
    have : leaves P p = true := by
      rcases hover with h | h <;> simp [leaves, hT, h]
    simp [this]
  rw [run_succ, step_of_up P L _ _ p hp]
  simp [killedAt, hm, Move.ends]

/-! ### Where the per-turn bound comes from -/

/-- Every work unit allocates at most `g`, and every turn has at most `W + 1` units. -/
def BoundedWork (g W : Nat) (env : Nat → Tick) : Prop :=
  ∀ n, (env n).alloc ≤ g ∧ (env n).work ≤ W

/-- A turn with `k + 1` units left has room for them within `(W + 1) * g`. -/
def Paced (g W : Nat) (p : Proc) : Prop :=
  ∀ k, p.phase = .busy k → p.mem + (k + 1) * g ≤ p.turnBase + (W + 1) * g

theorem paced_survivor (P : Policy) (L : Limits) (g W : Nat) (s : State) (e : Tick) (p : Proc)
    (hp : Paced g W p) (he : e.alloc ≤ g ∧ e.work ≤ W) :
    Paced g W (survivor s e p (move P L p e)) := by
  generalize hm : move P L p e = m
  cases m with
  | passed =>
    intro k hk
    simp [survivor, advance] at hk ⊢
    subst hk
    exact Nat.mul_le_mul_right g (by omega)
  | worked =>
    obtain ⟨⟨k, hph⟩, -, -, -⟩ := move_worked hm
    have hk := hp k hph
    cases k with
    | zero => intro k' hk'; simp [survivor, advance, hph] at hk'
    | succ k =>
      intro k' hk'
      simp [survivor, advance, hph] at hk' ⊢
      subst hk'
      have : (k + 1 + 1) * g = (k + 1) * g + g := Nat.succ_mul _ _
      simp only [grown]
      omega
  | stalled => simpa [survivor, advance, Paced] using hp
  | waited => simpa [survivor, advance, Paced] using hp
  | exited => simpa [survivor, advance, Paced] using hp
  | oom => simpa [survivor, advance, Paced] using hp

theorem fresh_paced (L : Limits) (g W : Nat) : Paced g W (fresh L) := by
  intro k hk; simp [fresh] at hk

theorem paced_invariant (P : Policy) (L : Limits) (env : Nat → Tick) (owner : EventPump.Key)
    (g W : Nat) (hw : BoundedWork g W env) :
    ∀ n p, (run P L env (boot L owner) n).life = .up p → Paced g W p := by
  intro n
  induction n with
  | zero => intro p hp; cases hp; exact fresh_paced L g W
  | succ n ih =>
    intro q hq
    rw [run_succ] at hq
    rcases step_life_cases P L (run P L env (boot L owner) n) (env n) with
      hd | ⟨_, hf⟩ | ⟨p, hp, hl, _⟩
    · rw [hd] at hq; cases hq
    · rw [hf] at hq; cases hq; exact fresh_paced L g W
    · rw [hl] at hq; cases hq; exact paced_survivor P L g W _ _ p (ih p hp) (hw n)

/-- An allocation rate `g` per work unit and at most `W + 1` units per turn
bound every turn's growth by `g * (W + 1)`. -/
theorem turn_growth_of_rate (P : Policy) (L : Limits) (env : Nat → Tick)
    (owner : EventPump.Key) (g W : Nat) (hw : BoundedWork g W env) :
    TurnGrowthWithin (g * (W + 1)) P L env (boot L owner) := by
  intro n p hp hm
  obtain ⟨⟨k, hph⟩, -, -, -⟩ := move_worked hm
  have hpace := paced_invariant P L env owner g W hw n p hp k hph
  have hk : g ≤ (k + 1) * g := Nat.le_mul_of_pos_left g (by omega)
  have ha := (hw n).1
  simp only [grown]
  rw [Nat.mul_comm g (W + 1)]
  omega

/-! ### Layer (a) is sharp, and is not a backstop -/

/-- **Layer (a) is sharp.** If `T + δ` exceeds the soft limit, a turn that
starts exactly at the threshold and grows by `δ` enters the throttled regime,
although every turn of the workload respects the bound `δ`. -/
theorem graceful_bound_sharp (L : Limits) (owner : EventPump.Key) (T δ : Nat)
    (hbase : L.base = T) (hH : L.high < T + δ) (hM : T + δ ≤ L.max) :
    TurnGrowthWithin δ { threshold := some T } L
        (fun n => if n = 1 then ({ alloc := δ } : Tick) else {}) (boot L owner) ∧
    ∃ p, (run { threshold := some T } L (fun n => if n = 1 then ({ alloc := δ } : Tick) else {})
      (boot L owner) 2).life = .up p ∧ L.high < p.mem := by
  constructor
  · have h := turn_growth_of_rate { threshold := some T } L
      (fun n => if n = 1 then ({ alloc := δ } : Tick) else {}) owner δ 0
      (fun n => by by_cases hn : n = 1 <;> simp [hn])
    simpa using h
  · refine ⟨⟨T + δ, .boundary, T + δ, false, []⟩, ?_, hH⟩
    have hM' : ¬ L.max < T + δ := by omega
    simp [run, step, killedAt, survivor, boot, fresh, move, leaves, advance, grown, hbase,
      pendingIds, EventPump.pending, watchdogKills, overdue, Move.ends, Move.progress, hM']

theorem move_worked_of {P : Policy} {L : Limits} {p : Proc} {e : Tick} {k : Nat}
    (hph : p.phase = .busy k) (hns : ¬ (e.stall = true ∧ L.high < p.mem))
    (hw : e.wait = false) (hM : grown p e ≤ L.max) : move P L p e = .worked := by
  rw [move_of_not_withheld hns, hph]
  simp [hw]; omega

/-- A progress move never trips a watchdog that is withheld with the service:
either the service stays below the soft limit, so both counters are reset, or
the watchdog is withheld. -/
theorem killedAt_progress (P : Policy) (L : Limits) (s : State) (e : Tick) (p : Proc)
    (hP : NoIndependentBackstop P) (hm : (move P L p e).progress = true)
    (hends : (move P L p e).ends = false) (hstall : e.stall = true)
    (hext : e.externalKill = false) : killedAt P L s e p = false := by
  simp only [killedAt, hm, hends, hext, hstall, Bool.true_and, Bool.false_or, Bool.or_false,
    if_true]
  by_cases hc : L.high < (advance p e (pendingIds (e.arrivals.foldl EventPump.record s.inbox))
      (move P L p e)).mem
  · simp only [hc, decide_true]
    exact watchdog_withheld P hP _ _
  · simp [hc, watchdogKills, overdue_zero]

theorem working_ticks (P : Policy) (L : Limits) (env : Nat → Tick) (s : State)
    (hP : NoIndependentBackstop P) (g n : Nat) (p : Proc)
    (hs : (run P L env s n).life = .up p) :
    ∀ j k, p.phase = .busy (k + j) →
      (∀ i < j, (env (n + i)).stall = true ∧ (env (n + i)).wait = false ∧
        (env (n + i)).externalKill = false ∧ (env (n + i)).alloc = g ∧
        (env (n + i)).free = 0) →
      (∀ i < j, p.mem + i * g ≤ L.high) → p.mem + j * g ≤ L.max →
      (∃ r, (run P L env s (n + j)).life =
        .up { p with mem := p.mem + j * g, phase := .busy k, recycle := r }) ∧
      (run P L env s (n + j)).generation = (run P L env s n).generation ∧
      (run P L env s (n + j)).processed = (run P L env s n).processed := by
  intro j
  induction j with
  | zero =>
    intro k hph _ _ _
    refine ⟨⟨p.recycle, ?_⟩, rfl, rfl⟩
    simp only [Nat.add_zero, Nat.zero_mul] at hph ⊢
    rw [hs]; cases p; simp_all
  | succ j ih =>
    intro k hph henv hle hM
    have hjM : p.mem + j * g ≤ L.max := by
      have : j * g ≤ (j + 1) * g := Nat.mul_le_mul_right g (by omega)
      omega
    obtain ⟨⟨r, hr⟩, hgen, hproc⟩ := ih (k + 1) (by rw [hph]; congr 1; omega)
      (fun i hi => henv i (by omega)) (fun i hi => hle i (by omega)) hjM
    obtain ⟨hst, hwt, hext, hal, hfr⟩ := henv j (by omega)
    have hgrown : grown { p with mem := p.mem + j * g, phase := .busy (k + 1), recycle := r }
        (env (n + j)) = p.mem + (j + 1) * g := by
      simp only [grown, hal, hfr, Nat.sub_zero, Nat.succ_mul]; omega
    have hlej := hle j (by omega)
    have hm : move P L { p with mem := p.mem + j * g, phase := .busy (k + 1), recycle := r }
        (env (n + j)) = .worked :=
      move_worked_of (k := k + 1) rfl (by intro ⟨_, h⟩; simp at h; omega) hwt
        (by rw [hgrown]; exact hM)
    have hk := killedAt_progress P L (run P L env s (n + j)) (env (n + j)) _ hP
      (by rw [hm]; rfl) (by rw [hm]; rfl) hst hext
    rw [← Nat.add_assoc, run_succ, step_of_up P L _ _ _ hr]
    refine ⟨⟨r || (env (n + j)).timer, ?_⟩, by simp [hgen], ?_⟩
    · simp [hk, survivor, advance, hm, hgrown]
    · simp [hm, completes, hproc]

/-- One long turn: every unit allocates `g`. -/
def runaway (g N : Nat) (_ : Nat) : Tick := { stall := true, work := N, alloc := g }

/-- **Layer (a) needs the per-turn bound, and is not a backstop.** A single
turn that outgrows the soft limit before its end freezes the service under
any policy without an independent backstop, including a graceful threshold
and a watchdog withheld with the service: the threshold is consulted only at
a boundary, and none comes. -/
theorem runaway_freezes_without_backstop (P : Policy) (L : Limits) (owner : EventPump.Key)
    (g N i : Nat) (hP : NoIndependentBackstop P) (hleave : leaves P (fresh L) = false)
    (hbase : L.base ≤ L.high) (hi : L.base + i * g ≤ L.high)
    (hi' : L.high < L.base + (i + 1) * g) (hM : L.base + (i + 1) * g ≤ L.max)
    (hN : i + 1 ≤ N) (n : Nat) :
    moveAt P L (runaway g N) (boot L owner) (i + 2 + n) = some .stalled ∧
    (run P L (runaway g N) (boot L owner) (i + 2 + n)).generation = 0 := by
  -- the first tick starts the long turn
  have hpass : move P L (fresh L) (runaway g N 0) = .passed := by
    have hns : ¬ ((runaway g N 0).stall = true ∧ L.high < (fresh L).mem) := by
      simp only [fresh, runaway]; omega
    rw [move_of_not_withheld hns]
    show (if leaves P (fresh L) then Move.exited else Move.passed) = .passed
    rw [hleave]; rfl
  have h1 : (run P L (runaway g N) (boot L owner) 1).life =
      .up { fresh L with phase := .busy N, turnBase := L.base, claimed := [] } := by
    have hk := killedAt_progress P L (boot L owner) (runaway g N 0) (fresh L) hP
      (by rw [hpass]; rfl) (by rw [hpass]; rfl) rfl rfl
    rw [run_succ, run_zero, step_of_up P L _ _ (fresh L) rfl]
    simp only [hk, hpass, Bool.false_eq_true, if_false]
    simp [survivor, advance, boot, runaway, pendingIds, EventPump.pending, fresh]
  have hg1 : (run P L (runaway g N) (boot L owner) 1).generation = 0 := by
    rw [run_succ, run_zero, step_of_up P L _ _ (fresh L) rfl]; rfl
  obtain ⟨⟨r, hr⟩, hgen, -⟩ := working_ticks P L (runaway g N) (boot L owner) hP g 1 _ h1 (i + 1)
    (N - (i + 1)) (by simp only; congr 1; omega) (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (fun i' hi'' => by
      have : i' * g ≤ i * g := Nat.mul_le_mul_right g (by omega)
      simp [fresh]; omega)
    (by simpa [fresh] using hM)
  have hfrozen := freeze_is_absorbing P L hP (fun j => runaway g N (1 + (i + 1) + j))
    (fun _ => rfl) (fun _ => rfl) (run P L (runaway g N) (boot L owner) (1 + (i + 1))) _ hr
    (by simpa [fresh] using hi') n
  have hrun : run P L (runaway g N) (boot L owner) (i + 2 + n) =
      run P L (fun j => runaway g N (1 + (i + 1) + j))
        (run P L (runaway g N) (boot L owner) (1 + (i + 1))) n := by
    rw [show i + 2 + n = 1 + (i + 1) + n by omega, run_add]
  rw [hfrozen] at hrun
  constructor
  · simp only [moveAt, hrun]
    simp [move, runaway, fresh, hi']
  · rw [hrun]; simp [hgen, hg1]

/-! ## Layer (b): an independent backstop -/

theorem progressAt_of_up {P : Policy} {L : Limits} {env : Nat → Tick} {s : State} {n : Nat}
    {p : Proc} (h : (run P L env s n).life = .up p) :
    progressAt P L env s n = (move P L p (env n)).progress := by
  simp [progressAt, moveAt, h]

theorem counters_of_survival (P : Policy) (L : Limits) (s : State) (e : Tick) (p : Proc)
    (hI : P.sharesThrottle = false) (hk : killedAt P L s e p = false) :
    (∀ D, P.progressDeadline = some D →
      (if (move P L p e).progress then 0 else s.quiet + 1) ≤ D) ∧
    (∀ D, P.throttleDeadline = some D →
      (if L.high < (advance p e (pendingIds (e.arrivals.foldl EventPump.record s.inbox))
        (move P L p e)).mem then s.pressure + 1 else 0) ≤ D) := by
  simp only [killedAt, watchdogKills, hI, Bool.false_and, Bool.not_false, Bool.and_true,
    Bool.or_eq_false_iff] at hk
  obtain ⟨⟨_, hq, hr⟩, _⟩ := hk
  constructor
  · intro D hD; rw [hD] at hq; simp [overdue] at hq; omega
  · intro D hD; rw [hD] at hr; simp [overdue] at hr; omega

theorem quiet_bounded (P : Policy) (L : Limits) (s : State) (e : Tick)
    (hI : P.sharesThrottle = false) (D : Nat) (hD : P.progressDeadline = some D) :
    (step P L s e).quiet ≤ D := by
  cases hs : s.life with
  | down => rw [step_of_down P L s e hs]; simp
  | up p =>
    rw [step_of_up P L s e p hs]
    cases hk : killedAt P L s e p
    · simpa [hk] using (counters_of_survival P L s e p hI hk).1 D hD
    · simp

theorem pressure_bounded (P : Policy) (L : Limits) (s : State) (e : Tick)
    (hI : P.sharesThrottle = false) (D : Nat) (hD : P.throttleDeadline = some D) :
    (step P L s e).pressure ≤ D := by
  cases hs : s.life with
  | down => rw [step_of_down P L s e hs]; simp
  | up p =>
    rw [step_of_up P L s e p hs]
    cases hk : killedAt P L s e p
    · simpa [hk] using (counters_of_survival P L s e p hI hk).2 D hD
    · simp

theorem quiet_grows (P : Policy) (L : Limits) (s : State) (e : Tick) (p : Proc)
    (hs : s.life = .up p) (hprog : (move P L p e).progress = false)
    (hup : ∃ q, (step P L s e).life = .up q) : (step P L s e).quiet = s.quiet + 1 := by
  rw [step_of_up P L s e p hs] at hup ⊢
  cases hk : killedAt P L s e p
  · simp [hprog]
  · simp [hk] at hup

theorem pressure_grows (P : Policy) (L : Limits) (s : State) (e : Tick) (p q : Proc)
    (hs : s.life = .up p) (hq : (step P L s e).life = .up q) (hthr : L.high < q.mem) :
    (step P L s e).pressure = s.pressure + 1 := by
  rw [step_of_up P L s e p hs] at hq ⊢
  cases hk : killedAt P L s e p
  · simp only [hk, Bool.false_eq_true, if_false, Life.up.injEq] at hq ⊢
    subst hq
    simp [survivor] at hthr
    simp [hthr]
  · simp [hk] at hq

/-- **Layer (b): bounded silence, unconditionally.** With an independent
progress watchdog of deadline `D`, a process that stays up through `k`
consecutive ticks without progress has `k ≤ D`. This holds in every
environment: whatever the kernel withholds, however long calls wait,
whatever else runs in the session or kills the service. The bound asks
nothing of the supervised process. -/
theorem backstop_bounds_silence (P : Policy) (L : Limits) (env : Nat → Tick) (s : State)
    (D : Nat) (hI : P.sharesThrottle = false) (hD : P.progressDeadline = some D) (n k : Nat)
    (hup : ∀ i ≤ k, ∃ p, (run P L env s (n + i)).life = .up p)
    (hquiet : ∀ i < k, progressAt P L env s (n + i) = false) : k ≤ D := by
  have hgrow : ∀ i ≤ k, i ≤ (run P L env s (n + i)).quiet := by
    intro i hi
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      obtain ⟨p, hp⟩ := hup i (by omega)
      have hprog := hquiet i (by omega)
      rw [progressAt_of_up hp] at hprog
      have hnext := hup (i + 1) hi
      rw [← Nat.add_assoc, run_succ] at hnext ⊢
      rw [quiet_grows P L _ _ p hp hprog hnext]
      have := ih (by omega)
      omega
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
    have h1 := hgrow (k + 1) (Nat.le_refl _)
    rw [← Nat.add_assoc, run_succ] at h1
    have h2 := quiet_bounded P L (run P L env s (n + k)) (env (n + k)) hI D hD
    omega

/-- **Layer (b): bounded throttling, unconditionally.** With an independent
throttle watchdog of deadline `D`, no process stays above the soft limit for
more than `D` consecutive ticks. -/
theorem backstop_bounds_throttling (P : Policy) (L : Limits) (env : Nat → Tick) (s : State)
    (D : Nat) (hI : P.sharesThrottle = false) (hD : P.throttleDeadline = some D) (n k : Nat)
    (hup : ∀ i ≤ k, ∃ p, (run P L env s (n + i)).life = .up p ∧ (0 < i → L.high < p.mem)) :
    k ≤ D := by
  have hgrow : ∀ i ≤ k, i ≤ (run P L env s (n + i)).pressure := by
    intro i hi
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      obtain ⟨p, hp, -⟩ := hup i (by omega)
      obtain ⟨q, hq, hthr⟩ := hup (i + 1) hi
      rw [← Nat.add_assoc, run_succ] at hq ⊢
      rw [pressure_grows P L _ _ p q hp hq (hthr (by omega))]
      have := ih (by omega)
      omega
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
    have h1 := hgrow (k + 1) (Nat.le_refl _)
    rw [← Nat.add_assoc, run_succ] at h1
    have h2 := pressure_bounded P L (run P L env s (n + k)) (env (n + k)) hI D hD
    omega

/-- A freshly started process passes its first boundary: it starts below the
soft limit, and neither the recycle flag nor the threshold asks it to leave. -/
theorem fresh_passes (P : Policy) (L : Limits) (e : Tick) (hbase : L.base ≤ L.high)
    (hleave : leaves P (fresh L) = false) : move P L (fresh L) e = .passed := by
  have hns : ¬ (e.stall = true ∧ L.high < (fresh L).mem) := by
    simp only [fresh]; omega
  rw [move_of_not_withheld hns]
  show (if leaves P (fresh L) then Move.exited else Move.passed) = .passed
  rw [hleave]; rfl

theorem leaves_fresh (P : Policy) (L : Limits)
    (hT : ∀ T, P.threshold = some T → L.base ≤ T) : leaves P (fresh L) = false := by
  cases h : P.threshold with
  | none => simp [leaves, fresh, h]
  | some T => have := hT T h; simp [leaves, fresh, h, Nat.not_lt.mpr this]

/-- **Layer (b): bounded unavailability, unconditionally.** With an
independent progress watchdog of deadline `D`, every `D + 3` consecutive
ticks contain a progress point, in every environment. Either the running
process progresses within `D + 1` ticks, or it is gone, and the service
manager's fresh process passes its first boundary. The only assumptions are
on the deployment: a fresh process starts below the soft limit and below the
graceful threshold. -/
theorem backstop_restores_progress (P : Policy) (L : Limits) (env : Nat → Tick) (s : State)
    (D : Nat) (hI : P.sharesThrottle = false) (hD : P.progressDeadline = some D)
    (hbase : L.base ≤ L.high) (hT : ∀ T, P.threshold = some T → L.base ≤ T) (n : Nat) :
    ∃ i ≤ D + 2, progressAt P L env s (n + i) = true := by
  by_cases hprog : ∃ i ≤ D + 1, progressAt P L env s (n + i) = true
  · obtain ⟨i, hi, h⟩ := hprog; exact ⟨i, by omega, h⟩
  · have hquiet : ∀ i < D + 1, progressAt P L env s (n + i) = false := by
      intro i hi
      cases h : progressAt P L env s (n + i)
      · rfl
      · exact absurd ⟨i, by omega, h⟩ hprog
    by_cases hdown : ∃ j ≤ D + 1, (run P L env s (n + j)).life = .down
    · obtain ⟨j, hj, hd⟩ := hdown
      refine ⟨j + 1, by omega, ?_⟩
      have hf : (run P L env s (n + (j + 1))).life = .up (fresh L) := by
        rw [← Nat.add_assoc, run_succ, step_of_down P L _ _ hd]
      rw [progressAt_of_up hf, fresh_passes P L _ hbase (leaves_fresh P L hT)]
      rfl
    · have hup : ∀ i ≤ D + 1, ∃ p, (run P L env s (n + i)).life = .up p := by
        intro i hi
        cases h : (run P L env s (n + i)).life with
        | up p => exact ⟨p, rfl⟩
        | down => exact absurd ⟨i, hi, h⟩ hdown
      have := backstop_bounds_silence P L env s D hI hD n (D + 1) hup hquiet
      omega

/-- **A watchdog withheld with the service is not a backstop.** Without a
graceful threshold, the accumulation freeze happens and lasts forever under
every policy whose watchdog shares the service's throttle, whatever its
deadlines. With a threshold, `runaway_freezes_without_backstop` gives the
same conclusion. -/
theorem throttle_sharing_watchdog_freezes (P : Policy) (L : Limits) (owner : EventPump.Key)
    (g R k : Nat) (hthr : P.threshold = none) (hsh : P.sharesThrottle = true)
    (hk : L.base + k * g ≤ L.high) (hk' : L.high < L.base + (k + 1) * g)
    (hM : L.base + (k + 1) * g ≤ L.max) (hR : 3 * k + 2 < R) (n : Nat) :
    moveAt P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n) = some .stalled ∧
    (run P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n)).generation = 0 :=
  let h := unguarded_freezes_forever P L owner g R k hthr (Or.inl hsh) hk hk' hM hR n
  ⟨h.2.1, h.2.2.2.1⟩

/-! ### When could a watchdog inside the service be the backstop?

A supervisor acts through a kill path: the steps it must complete once it has
decided to kill. While the service is above its soft limit, the kernel delays
the tasks that charge memory to the service's control group, and a thread
waiting for a lock held by such a task waits with it. The other runnable
tasks are still scheduled.

In the transition system above, a watchdog whose kill path has a withholdable
step is the `sharesThrottle` watchdog. One whose kill path has none acts like
the external watchdog, with the path's `length * S` ticks added to its
deadline. -/

/-- What one step of a kill path needs from the supervised service. -/
structure Need where
  /-- The step charges memory to the service's control group: an allocation,
  or a fault on a page the kernel has reclaimed. -/
  charges : Bool
  /-- Locks of the service's process that the step acquires. -/
  locks : List Nat
deriving Repr, DecidableEq

/-- While the service is throttled and its blocked threads hold `held`, a step
can be delayed indefinitely exactly when it charges the service or needs a
held lock. -/
def withholdable (held : List Nat) (n : Need) : Bool :=
  n.charges || n.locks.any (fun l => decide (l ∈ held))

/-- Steps of a kill path completed after `t` ticks, when the current step may
run exactly on the ticks where `runs` holds. -/
def completedSteps (path : List Need) (runs : Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 =>
    if decide (completedSteps path runs t < path.length) && runs t then
      completedSteps path runs t + 1
    else completedSteps path runs t

/-- Kernel scheduling of the kill path: a step that cannot be withheld runs
within `S` ticks of becoming current; a withholdable step may wait forever. -/
def Scheduled (held : List Nat) (S : Nat) (path : List Need) (runs : Nat → Bool) : Prop :=
  ∀ t n, path[completedSteps path runs t]? = some n → withholdable held n = false →
    ∃ i < S, runs (t + i) = true

theorem completedSteps_le (path : List Need) (runs : Nat → Bool) (t : Nat) :
    completedSteps path runs t ≤ path.length := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    simp only [completedSteps]
    split
    · rename_i h; simp at h; omega
    · exact ih

theorem completedSteps_mono (path : List Need) (runs : Nat → Bool) (t d : Nat) :
    completedSteps path runs t ≤ completedSteps path runs (t + d) := by
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    rw [← Nat.add_assoc]
    simp only [completedSteps]
    split <;> omega

theorem completedSteps_run (path : List Need) (runs : Nat → Bool) (t : Nat)
    (hlt : completedSteps path runs t < path.length) (hr : runs t = true) :
    completedSteps path runs (t + 1) = completedSteps path runs t + 1 := by
  simp [completedSteps, hlt, hr]

/-- **Sufficiency.** If no step of the kill path can be withheld, the path
completes within `length * S` ticks under any admissible scheduling. -/
theorem unwithholdable_path_completes (held : List Nat) (S : Nat) (path : List Need)
    (runs : Nat → Bool) (hall : ∀ n ∈ path, withholdable held n = false)
    (hsched : Scheduled held S path runs) :
    completedSteps path runs (path.length * S) = path.length := by
  have key : ∀ k, min k path.length ≤ completedSteps path runs (k * S) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hmono := completedSteps_mono path runs (k * S)
      rw [Nat.succ_mul]
      by_cases hc : path.length ≤ completedSteps path runs (k * S)
      · have := hmono S; omega
      · have hlt : completedSteps path runs (k * S) < path.length := by omega
        obtain ⟨i, hi, hrun⟩ := hsched (k * S) (path[completedSteps path runs (k * S)])
          (by simp [hlt]) (hall _ (List.getElem_mem hlt))
        have hge : completedSteps path runs (k * S) + 1 ≤
            completedSteps path runs (k * S + S) := by
          by_cases hsame : completedSteps path runs (k * S + i) = completedSteps path runs (k * S)
          · have h1 := completedSteps_run path runs (k * S + i) (by omega) hrun
            have h2 := completedSteps_mono path runs (k * S + i + 1) (S - i - 1)
            rw [show k * S + i + 1 + (S - i - 1) = k * S + S by omega] at h2
            omega
          · have h1 := completedSteps_mono path runs (k * S) i
            have h2 := completedSteps_mono path runs (k * S + i) (S - i)
            rw [show k * S + i + (S - i) = k * S + S by omega] at h2
            omega
        omega
  have h1 := key path.length
  have h2 := completedSteps_le path runs (path.length * S)
  simp at h1
  omega

theorem least_below (q : Nat → Bool) :
    ∀ n, (∃ k, k < n ∧ q k = true ∧ ∀ j < k, q j = false) ∨ (∀ j < n, q j = false) := by
  intro n
  induction n with
  | zero => exact Or.inr (fun j hj => absurd hj (Nat.not_lt_zero j))
  | succ n ih =>
    rcases ih with ⟨k, hk, hq, hmin⟩ | hnone
    · exact Or.inl ⟨k, by omega, hq, hmin⟩
    · cases hqn : q n
      · exact Or.inr (fun j hj => if hjn : j < n then hnone j hjn else by
          rw [show j = n by omega]; exact hqn)
      · exact Or.inl ⟨n, by omega, hqn, hnone⟩

theorem exists_least (q : Nat → Bool) :
    ∀ n, (∃ i < n, q i = true) → ∃ k, q k = true ∧ ∀ j < k, q j = false := by
  intro n ⟨i, hi, hq⟩
  rcases least_below q n with ⟨k, -, hk, hmin⟩ | hnone
  · exact ⟨k, hk, hmin⟩
  · rw [hnone i hi] at hq; cases hq

theorem completedSteps_prefix (path : List Need) (i : Nat) (hi : i < path.length) :
    ∀ t, completedSteps path (fun t => decide (t < i)) t = min t i := by
  intro t
  induction t with
  | zero => show 0 = min 0 i; omega
  | succ t ih =>
    simp only [completedSteps, ih]
    by_cases ht : t < i
    · have h1 : min t i = t := by omega
      have h2 : min (t + 1) i = t + 1 := by omega
      have hc : (decide (t < path.length) && decide (t < i)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by omega, ht⟩
      rw [h1, h2, if_pos hc]
    · have h1 : min t i = i := by omega
      have h2 : min (t + 1) i = i := by omega
      have hc : ¬ (decide (i < path.length) && decide (t < i)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]; exact fun h => ht h.2
      rw [h1, h2, if_neg hc]

/-- **Necessity.** If some step of the kill path can be withheld, an admissible
scheduling delays it forever: the path never completes, so the supervised
process is never killed. -/
theorem withholdable_path_can_stall (held : List Nat) (S : Nat) (hS : 0 < S)
    (path : List Need) (hsome : ∃ n ∈ path, withholdable held n = true) :
    ∃ runs, Scheduled held S path runs ∧ ∀ t, completedSteps path runs t < path.length := by
  obtain ⟨n, hn, hw⟩ := hsome
  obtain ⟨i₀, hlt₀, heq₀⟩ := List.getElem_of_mem hn
  obtain ⟨i, hi, hfirst⟩ := exists_least
    (fun i => (path[i]?).any (withholdable held)) (i₀ + 1)
    ⟨i₀, by omega, by simp [List.getElem?_eq_getElem hlt₀, heq₀, hw]⟩
  have hilen : i < path.length := by
    by_cases hlt : i < path.length
    · exact hlt
    · rw [List.getElem?_eq_none (by omega)] at hi; simp at hi
  have hcount := completedSteps_prefix path i hilen
  refine ⟨fun t => decide (t < i), fun t m hm hmw => ⟨0, hS, ?_⟩, fun t => ?_⟩
  · rw [hcount] at hm
    by_cases ht : t < i
    · simp [ht]
    · have : min t i = i := by omega
      rw [this] at hm
      simp [hm, hmw] at hi
  · rw [hcount]; omega

/-- Kill paths. An external watchdog decides and kills from its own control
group, takes no lock of the service, and uses a kill the target cannot catch:
no step of its path runs in the target. -/
def externalPath : List Need := [⟨false, []⟩, ⟨false, []⟩]

/-- A catchable termination signal adds a step of the target: its handler. -/
def catchablePath (handler : Need) : List Need := externalPath ++ [handler]

/-- A watchdog thread of an interpreter whose global lock (lock `0`) the
throttled main thread may hold. -/
def interpreterThreadPath : List Need := [⟨false, [0]⟩, ⟨false, []⟩]

/-- A watchdog thread whose code or stack pages were reclaimed under memory
pressure: waking it faults them back in, charging the service. -/
def faultingThreadPath : List Need := [⟨true, []⟩, ⟨false, []⟩]

/-- A watchdog thread with all of its pages locked in memory, taking no lock a
throttled thread can hold, and exiting with a system call that allocates
nothing. -/
def lockedThreadPath : List Need := [⟨false, []⟩, ⟨false, []⟩]

/-- The external watchdog completes its kill within `2 S` ticks, whatever
the throttled service holds. -/
theorem external_watchdog_kills (held : List Nat) (S : Nat) (runs : Nat → Bool)
    (h : Scheduled held S externalPath runs) :
    completedSteps externalPath runs (2 * S) = 2 :=
  unwithholdable_path_completes held S externalPath runs
    (by intro n hn; simp [externalPath] at hn; rcases hn with rfl | rfl <;> rfl) h

/-- An interpreter thread needing the global lock can be stalled forever. -/
theorem interpreter_thread_can_stall (S : Nat) (hS : 0 < S) :
    ∃ runs, Scheduled [0] S interpreterThreadPath runs ∧
      ∀ t, completedSteps interpreterThreadPath runs t < 2 :=
  withholdable_path_can_stall [0] S hS interpreterThreadPath
    ⟨⟨false, [0]⟩, by simp [interpreterThreadPath], by decide⟩

/-- A thread that must fault its pages back in can be stalled forever. -/
theorem faulting_thread_can_stall (held : List Nat) (S : Nat) (hS : 0 < S) :
    ∃ runs, Scheduled held S faultingThreadPath runs ∧
      ∀ t, completedSteps faultingThreadPath runs t < 2 :=
  withholdable_path_can_stall held S hS faultingThreadPath
    ⟨⟨true, []⟩, by simp [faultingThreadPath], by simp [withholdable]⟩

/-- A catchable signal whose handler allocates can be stalled forever. -/
theorem catchable_kill_can_stall (held : List Nat) (S : Nat) (hS : 0 < S) (handler : Need)
    (hcharges : handler.charges = true) :
    ∃ runs, Scheduled held S (catchablePath handler) runs ∧
      ∀ t, completedSteps (catchablePath handler) runs t < 3 :=
  withholdable_path_can_stall held S hS (catchablePath handler)
    ⟨handler, by simp [catchablePath, externalPath], by simp [withholdable, hcharges]⟩

/-- Under the precise assumptions — pages locked in memory, no lock shared
with code that can block in an allocation, an exit that allocates nothing,
and a kernel that keeps scheduling non-charging tasks — a thread inside the
service does complete its kill within `2 S` ticks. -/
theorem locked_thread_kills (held : List Nat) (S : Nat) (runs : Nat → Bool)
    (h : Scheduled held S lockedThreadPath runs) :
    completedSteps lockedThreadPath runs (2 * S) = 2 :=
  unwithholdable_path_completes held S lockedThreadPath runs
    (by intro n hn; simp [lockedThreadPath] at hn; rcases hn with rfl | rfl <;> rfl) h

/-! ### The watchdog must be fed by progress -/

/-- Ticks since the watchdog was last fed. -/
def unfed (feed : Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => if feed t then 0 else unfed feed t + 1

/-- A watchdog fed by a heartbeat that runs regardless of progress (a timer
thread, a status write) never fires. -/
theorem heartbeat_feed_never_fires (D t : Nat) : ¬ D < unfed (fun _ => true) t := by
  cases t <;> simp [unfed]

/-- Fed only at progress points, it fires once `D + 1` ticks pass without progress. -/
theorem progress_feed_fires (feed progress : Nat → Bool)
    (hfeed : ∀ t, feed t = true → progress t = true) (D n : Nat)
    (hnone : ∀ i ≤ D, progress (n + i) = false) : D < unfed feed (n + D + 1) := by
  have : ∀ i ≤ D + 1, i ≤ unfed feed (n + i) := by
    intro i hi
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hf : feed (n + i) = false := by
        cases h : feed (n + i)
        · rfl
        · have := hfeed _ h; rw [hnone i (by omega)] at this; cases this
      rw [← Nat.add_assoc]; simp only [unfed, hf]; have := ih (by omega); simp; omega
  have := this (D + 1) (Nat.le_refl _)
  rw [← Nat.add_assoc] at this
  omega

/-! ## Layer (c): durable inputs, acknowledged only after the checkpoint -/

section Journal

theorem claim_phase (s : EventPump.Inbox) (a id : Nat) :
    (EventPump.claim s a).phase id =
      if id = a ∧ s.phase a = some .queued then some .claimed else s.phase id := by
  unfold EventPump.claim
  by_cases h : s.phase a = some .queued
  · by_cases hid : id = a <;> simp [h, hid]
  · simp [h]

theorem settle_phase (s : EventPump.Inbox) (a id : Nat) :
    (EventPump.settle s a).phase id =
      if id = a ∧ s.phase a = some .claimed then some .settled else s.phase id := by
  unfold EventPump.settle
  by_cases h : s.phase a = some .claimed
  · by_cases hid : id = a <;> simp [h, hid]
  · simp [h]

theorem recover_phase (s : EventPump.Inbox) (id : Nat) :
    (EventPump.recover s).phase id =
      if s.phase id = some .claimed then some .queued else s.phase id := rfl

theorem claimEach_phase (ids : List Nat) (s : EventPump.Inbox) (id : Nat) :
    (claimEach ids s).phase id =
      if id ∈ ids ∧ s.phase id = some .queued then some .claimed else s.phase id := by
  induction ids generalizing s with
  | nil => simp [claimEach]
  | cons a rest ih =>
    simp only [claimEach, List.foldl_cons] at ih ⊢
    rw [ih, claim_phase]
    by_cases hid : id = a
    · subst hid; by_cases hq : s.phase id = some .queued <;> simp [hq]
    · simp [hid]

theorem settleEach_phase (ids : List Nat) (s : EventPump.Inbox) (id : Nat) :
    (settleEach ids s).phase id =
      if id ∈ ids ∧ s.phase id = some .claimed then some .settled else s.phase id := by
  induction ids generalizing s with
  | nil => simp [settleEach]
  | cons a rest ih =>
    simp only [settleEach, List.foldl_cons] at ih ⊢
    rw [ih, settle_phase]
    by_cases hid : id = a
    · subst hid; by_cases hq : s.phase id = some .claimed <;> simp [hq]
    · simp [hid]

theorem claimEach_journal (ids : List Nat) (s : EventPump.Inbox) :
    (claimEach ids s).journal = s.journal := by
  induction ids generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [claimEach, List.foldl_cons] at ih ⊢
    rw [ih]; unfold EventPump.claim; split <;> rfl

theorem settleEach_journal (ids : List Nat) (s : EventPump.Inbox) :
    (settleEach ids s).journal = s.journal := by
  induction ids generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [settleEach, List.foldl_cons] at ih ⊢
    rw [ih]; unfold EventPump.settle; split <;> rfl

theorem recordAll_journal (es : List EventPump.Event) (s : EventPump.Inbox)
    (ev : EventPump.Event) (h : ev ∈ s.journal) : ev ∈ (es.foldl EventPump.record s).journal := by
  induction es generalizing s with
  | nil => exact h
  | cons e rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (EventPump.journal_never_erased s (.arrival e) ev h)

/-- Recording only ever turns an unset phase into `queued`. -/
theorem recordAll_phase (es : List EventPump.Event) (s : EventPump.Inbox) (id : Nat) :
    (es.foldl EventPump.record s).phase id = s.phase id ∨
      (s.phase id = none ∧ (es.foldl EventPump.record s).phase id = some .queued) := by
  induction es generalizing s with
  | nil => left; rfl
  | cons e rest ih =>
    simp only [List.foldl_cons]
    rcases ih (EventPump.record s e) with h | ⟨hn, hq⟩
    · rw [h, record_phase]
      split
      · rename_i hc; right; exact ⟨hc.2.2 ▸ hc.2.1, rfl⟩
      · left; rfl
    · rw [record_phase] at hn
      split at hn
      · simp at hn
      · right; exact ⟨hn, hq⟩

theorem accounted_recordAll (es : List EventPump.Event) (s : EventPump.Inbox)
    (h : EventPump.accounted s) : EventPump.accounted (es.foldl EventPump.record s) := by
  induction es generalizing s with
  | nil => exact h
  | cons e rest ih =>
    exact ih _ (EventPump.step_preserves_accounting s (.arrival e) h)

theorem accounted_claimEach (ids : List Nat) (s : EventPump.Inbox)
    (h : EventPump.accounted s) : EventPump.accounted (claimEach ids s) := by
  induction ids generalizing s with
  | nil => exact h
  | cons a rest ih =>
    exact ih _ (EventPump.step_preserves_accounting s (.claim a) h)

theorem accounted_settleEach (ids : List Nat) (s : EventPump.Inbox)
    (h : EventPump.accounted s) : EventPump.accounted (settleEach ids s) := by
  induction ids generalizing s with
  | nil => exact h
  | cons a rest ih =>
    exact ih _ (EventPump.step_preserves_accounting s (.settle a) h)

theorem pending_queued (s : EventPump.Inbox) (ev : EventPump.Event)
    (hev : ev ∈ s.journal) (hq : s.phase ev.serial = some .queued) :
    ev.serial ∈ pendingIds s := by
  simp only [pendingIds, List.mem_map]
  exact ⟨ev, List.mem_filter.mpr ⟨hev, by simp [hq]⟩, rfl⟩

theorem pendingIds_queued (s : EventPump.Inbox) (id : Nat) (h : id ∈ pendingIds s) :
    s.phase id = some .queued := by
  simp only [pendingIds, List.mem_map] at h
  obtain ⟨ev, hev, rfl⟩ := h
  exact of_decide_eq_true (List.mem_filter.mp hev).2

end Journal

/-- **The journal invariant.** Every journalled input has a phase. An input is
claimed only by the running turn, so a death can return it to the queue.
An input is acknowledged (settled) only once its turn's checkpoint has
recorded it as processed. A process at a boundary holds no claims. -/
def Accounted (s : State) : Prop :=
  EventPump.accounted s.inbox ∧
  (∀ id, s.inbox.phase id = some .claimed → ∃ p, s.life = .up p ∧ id ∈ p.claimed) ∧
  (∀ id, s.inbox.phase id = some .settled → id ∈ s.processed) ∧
  (∀ p, s.life = .up p → p.phase = .boundary → p.claimed = [])

theorem boot_accounted (L : Limits) (owner : EventPump.Key) : Accounted (boot L owner) := by
  refine ⟨fun e he => by simp [boot] at he, fun id h => by simp [boot] at h,
    fun id h => by simp [boot] at h, fun p hp _ => ?_⟩
  cases hp; rfl

theorem recover_no_claim (J : EventPump.Inbox) (id : Nat) :
    (EventPump.recover J).phase id ≠ some .claimed := by
  rw [recover_phase]; split
  · simp
  · assumption

theorem recover_settled (J : EventPump.Inbox) (id : Nat) :
    (EventPump.recover J).phase id = some .settled ↔ J.phase id = some .settled := by
  rw [recover_phase]; split
  · rename_i h; simp [h]
  · exact Iff.rfl

/-- The journal invariant holds after every step, whatever the policy and the
environment: arrivals, every move, watchdog kills, external kills and
restarts. -/
theorem accounted_step (P : Policy) (L : Limits) (s : State) (e : Tick) (h : Accounted s) :
    Accounted (step P L s e) := by
  obtain ⟨hacc, hcl, hset, hbd⟩ := h
  have hcl₀ : ∀ id, (e.arrivals.foldl EventPump.record s.inbox).phase id = some .claimed →
      s.inbox.phase id = some .claimed := by
    intro id hid
    rcases recordAll_phase e.arrivals s.inbox id with h1 | ⟨_, h2⟩
    · rwa [h1] at hid
    · rw [h2] at hid; cases hid
  have hset₀ : ∀ id, (e.arrivals.foldl EventPump.record s.inbox).phase id = some .settled →
      s.inbox.phase id = some .settled := by
    intro id hid
    rcases recordAll_phase e.arrivals s.inbox id with h1 | ⟨_, h2⟩
    · rwa [h1] at hid
    · rw [h2] at hid; cases hid
  have hacc₀ := accounted_recordAll e.arrivals s.inbox hacc
  cases hs : s.life with
  | down =>
    rw [step_of_down P L s e hs]
    refine ⟨hacc₀, fun id hid => ?_, fun id hid => hset id (hset₀ id hid), fun p hp _ => ?_⟩
    · obtain ⟨p, hp, _⟩ := hcl id (hcl₀ id hid); rw [hs] at hp; cases hp
    · simp only [Life.up.injEq] at hp; subst hp; rfl
  | up p =>
    have hcl₁ : ∀ id, (e.arrivals.foldl EventPump.record s.inbox).phase id = some .claimed →
        id ∈ p.claimed := by
      intro id hid
      obtain ⟨q, hq, hmem⟩ := hcl id (hcl₀ id hid)
      rw [hs] at hq; cases hq; exact hmem
    rw [step_of_up P L s e p hs]
    simp only [survivor]
    generalize e.arrivals.foldl EventPump.record s.inbox = I₀ at hcl₁ hset₀ hacc₀ ⊢
    -- facts about the inbox and the process after the move, for every move
    have hJ : EventPump.accounted (inboxAfter p I₀ (move P L p e)) ∧
        (∀ id, (inboxAfter p I₀ (move P L p e)).phase id = some .claimed →
          id ∈ (advance p e (pendingIds I₀) (move P L p e)).claimed) ∧
        (∀ id, (inboxAfter p I₀ (move P L p e)).phase id = some .settled →
          id ∈ (if completes p (move P L p e) then s.processed ++ p.claimed else s.processed)) ∧
        ((advance p e (pendingIds I₀) (move P L p e)).phase = .boundary →
          (advance p e (pendingIds I₀) (move P L p e)).claimed = []) := by
      generalize hm : move P L p e = m
      cases m with
      | passed =>
        have hb := (move_passed hm).1
        have hpc := hbd p hs hb
        refine ⟨accounted_claimEach _ _ hacc₀, fun id hid => ?_, fun id hid => ?_,
          fun h => by simp [advance] at h⟩
        · simp only [inboxAfter, claimEach_phase] at hid
          split at hid
          · rename_i hc; simpa [advance] using hc.1
          · have := hcl₁ id hid; rw [hpc] at this; cases this
        · simp only [inboxAfter, claimEach_phase] at hid
          split at hid
          · cases hid
          · simpa [completes] using hset id (hset₀ id hid)
      | worked =>
        obtain ⟨⟨k, hph⟩, -, -, -⟩ := move_worked hm
        cases k with
        | zero =>
          refine ⟨by simpa [inboxAfter, hph] using accounted_settleEach p.claimed I₀ hacc₀,
            fun id hid => ?_, fun id hid => ?_, fun _ => by simp [advance, hph]⟩
          · simp only [inboxAfter, hph, beq_self_eq_true, if_true, settleEach_phase] at hid
            split at hid
            · cases hid
            · rename_i hc; exact absurd ⟨hcl₁ id hid, hid⟩ hc
          · simp only [inboxAfter, hph, beq_self_eq_true, if_true, settleEach_phase] at hid
            simp only [completes, hph, beq_self_eq_true, if_true, List.mem_append]
            split at hid
            · rename_i hc; exact Or.inr hc.1
            · exact Or.inl (hset id (hset₀ id hid))
        | succ k =>
          have hne : (Phase.busy (k + 1) == Phase.busy 0) = false := by simp
          refine ⟨by simpa [inboxAfter, hph, hne] using hacc₀, fun id hid => ?_,
            fun id hid => ?_, fun h => by simp [advance, hph] at h⟩
          · simp only [inboxAfter, hph, hne] at hid
            simpa [advance, hph] using hcl₁ id hid
          · simp only [inboxAfter, hph, hne] at hid
            simpa [completes, hph, hne] using hset id (hset₀ id hid)
      | stalled =>
        exact ⟨hacc₀, fun id hid => hcl₁ id hid,
          fun id hid => by simpa [completes] using hset id (hset₀ id hid), hbd p hs⟩
      | waited =>
        exact ⟨hacc₀, fun id hid => hcl₁ id hid,
          fun id hid => by simpa [completes] using hset id (hset₀ id hid), hbd p hs⟩
      | exited =>
        exact ⟨hacc₀, fun id hid => hcl₁ id hid,
          fun id hid => by simpa [completes] using hset id (hset₀ id hid), hbd p hs⟩
      | oom =>
        exact ⟨hacc₀, fun id hid => hcl₁ id hid,
          fun id hid => by simpa [completes] using hset id (hset₀ id hid), hbd p hs⟩
    obtain ⟨hJacc, hJcl, hJset, hJbd⟩ := hJ
    cases killedAt P L s e p
    · refine ⟨hJacc, fun id hid => ⟨_, rfl, hJcl id hid⟩, hJset, fun q hq hb => ?_⟩
      simp only [Bool.false_eq_true, if_false, Life.up.injEq] at hq
      subst hq
      exact hJbd hb
    · refine ⟨EventPump.step_preserves_accounting _ .recover hJacc,
        fun id hid => absurd hid (recover_no_claim _ id),
        fun id hid => hJset id ((recover_settled _ id).mp hid), fun q hq _ => ?_⟩
      simp at hq

theorem accounted_invariant (P : Policy) (L : Limits) (env : Nat → Tick) (s : State)
    (h : Accounted s) : ∀ n, Accounted (run P L env s n) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact accounted_step P L _ _ ih

theorem journal_step (P : Policy) (L : Limits) (s : State) (e : Tick) (ev : EventPump.Event)
    (h : ev ∈ s.inbox.journal) : ev ∈ (step P L s e).inbox.journal := by
  have h₀ := recordAll_journal e.arrivals s.inbox ev h
  cases hs : s.life with
  | down => rw [step_of_down P L s e hs]; exact h₀
  | up p =>
    rw [step_of_up P L s e p hs]
    have hJ : ev ∈ (inboxAfter p (e.arrivals.foldl EventPump.record s.inbox)
        (move P L p e)).journal := by
      cases move P L p e with
      | passed => simp only [inboxAfter]; rw [claimEach_journal]; exact h₀
      | worked =>
        simp only [inboxAfter]
        split
        · rw [settleEach_journal]; exact h₀
        · exact h₀
      | stalled => exact h₀
      | waited => exact h₀
      | exited => exact h₀
      | oom => exact h₀
    cases killedAt P L s e p
    · simpa using hJ
    · simpa [EventPump.recover] using hJ

theorem journal_mono (P : Policy) (L : Limits) (env : Nat → Tick) (s : State) (n : Nat)
    (ev : EventPump.Event) (h : ev ∈ (run P L env s n).inbox.journal) :
    ∀ d, ev ∈ (run P L env s (n + d)).inbox.journal := by
  intro d
  induction d with
  | zero => exact h
  | succ d ih => rw [← Nat.add_assoc, run_succ]; exact journal_step P L _ _ ev ih

/-- **Layer (c), safety: no input is lost.** Under every policy and in every
environment (throttling, watchdog kills, kernel kills, external kills,
restarts), an accepted input stays in the journal. At every later tick it is
queued, held by the running turn, or acknowledged after its turn's checkpoint
recorded it as processed. -/
theorem no_input_lost (P : Policy) (L : Limits) (env : Nat → Tick) (owner : EventPump.Key)
    (n : Nat) (ev : EventPump.Event)
    (hev : ev ∈ (run P L env (boot L owner) n).inbox.journal) (d : Nat) :
    ev ∈ (run P L env (boot L owner) (n + d)).inbox.journal ∧
    ((run P L env (boot L owner) (n + d)).inbox.phase ev.serial = some .queued ∨
     ((run P L env (boot L owner) (n + d)).inbox.phase ev.serial = some .claimed ∧
       ∃ p, (run P L env (boot L owner) (n + d)).life = .up p ∧ ev.serial ∈ p.claimed) ∨
     ((run P L env (boot L owner) (n + d)).inbox.phase ev.serial = some .settled ∧
       ev.serial ∈ (run P L env (boot L owner) (n + d)).processed)) := by
  have hj := journal_mono P L env (boot L owner) n ev hev d
  obtain ⟨hacc, hcl, hset, _⟩ :=
    accounted_invariant P L env (boot L owner) (boot_accounted L owner) (n + d)
  refine ⟨hj, ?_⟩
  have hne := hacc ev hj
  cases hph : (run P L env (boot L owner) (n + d)).inbox.phase ev.serial with
  | none => exact absurd hph hne
  | some x =>
    cases x with
    | queued => exact Or.inl rfl
    | claimed => exact Or.inr (Or.inl ⟨rfl, hcl _ hph⟩)
    | settled => exact Or.inr (Or.inr ⟨rfl, hset _ hph⟩)

/-! ### Acknowledging before the checkpoint loses inputs -/

/-- **Acknowledged at presentation, lost at a kill.** A turn that settles an
input when it claims it, and is killed before its checkpoint, leaves the input
settled although no turn processed it. Recovery cannot return it, and no
later action reopens a settlement (`EventPump.settlement_never_reopened`). -/
theorem early_acknowledgement_loses (s : EventPump.Inbox) (ev : EventPump.Event)
    (h : ev.owner = s.owner ∧ s.phase ev.serial = none) :
    (EventPump.recover (EventPump.settle (EventPump.claim (EventPump.record s ev) ev.serial)
      ev.serial)).phase ev.serial = some .settled ∧
    ev ∉ EventPump.pending (EventPump.recover (EventPump.settle
      (EventPump.claim (EventPump.record s ev) ev.serial) ev.serial)) := by
  have hq := (EventPump.accepted_event_is_queued s ev h).2
  have hset : (EventPump.recover (EventPump.settle (EventPump.claim (EventPump.record s ev)
      ev.serial) ev.serial)).phase ev.serial = some .settled := by
    rw [recover_phase, settle_phase, claim_phase]; simp [hq]
  refine ⟨hset, fun hp => ?_⟩
  have := of_decide_eq_true (List.mem_filter.mp hp).2
  rw [hset] at this; cases this

/-- Acknowledged only at the checkpoint, the same kill returns it to the queue. -/
theorem late_acknowledgement_requeues (s : EventPump.Inbox) (ev : EventPump.Event)
    (h : ev.owner = s.owner ∧ s.phase ev.serial = none) :
    (EventPump.recover (EventPump.claim (EventPump.record s ev) ev.serial)).phase ev.serial =
      some .queued ∧
    ev ∈ EventPump.pending (EventPump.recover (EventPump.claim (EventPump.record s ev)
      ev.serial)) := by
  have hq := (EventPump.accepted_event_is_queued s ev h)
  have hph : (EventPump.recover (EventPump.claim (EventPump.record s ev) ev.serial)).phase
      ev.serial = some .queued := by
    rw [recover_phase, claim_phase]; simp [hq.2]
  refine ⟨hph, List.mem_filter.mpr ⟨?_, by simp [hph]⟩⟩
  have hj : (EventPump.recover (EventPump.claim (EventPump.record s ev) ev.serial)).journal =
      (EventPump.record s ev).journal := by
    simp only [EventPump.recover]; unfold EventPump.claim; split <;> rfl
  rw [hj]; exact hq.1

/-- **At-most-once presentation needs the checkpoint too.** `Claws.drainFiltered`
marks an input as presented when it drains it. If the turn is killed before its
checkpoint and the transport redelivers the input, the filter suppresses it,
so an input that no turn processed is never presented again. -/
theorem presentation_mark_loses_killed_turn (s : Claws.S) (m : Claws.Msg)
    (hq : m ∈ s.queue) (hnew : m.id ∉ s.seen) :
    m ∈ (Claws.drainFiltered s).1 ∧
    m ∉ (Claws.drainFiltered { (Claws.drainFiltered s).2 with queue := [m] }).1 := by
  refine ⟨Claws.filtered_presents_fresh s m hq hnew, Claws.filtered_never_represents _ m ?_⟩
  have := Claws.filtered_presents_fresh s m hq hnew
  simp only [Claws.drainFiltered] at this ⊢
  exact List.mem_append_left _ (List.mem_map_of_mem this)

/-- Marked only at the checkpoint, a killed turn's input is unmarked, and the
redelivered input is presented again. -/
theorem checkpoint_mark_represents (s : Claws.S) (m : Claws.Msg) (hnew : m.id ∉ s.seen) :
    m ∈ (Claws.drainFiltered { s with queue := [m] }).1 :=
  Claws.filtered_presents_fresh _ m (by simp) hnew

/-- The transport's hand-over of one update: the journal, and the updates the
upstream would still redeliver (those not yet acknowledged upstream). -/
structure Handover where
  upstream : List EventPump.Event
  inbox : EventPump.Inbox

/-- After a transport crash the upstream redelivers what it still holds. -/
def redeliver (h : Handover) : EventPump.Inbox := h.upstream.foldl EventPump.record h.inbox

/-- **Acknowledged upstream before it is journalled, lost at a crash.** The
upstream has forgotten the update and the journal never held it. -/
theorem upstream_ack_first_loses (s : EventPump.Inbox) (ev : EventPump.Event)
    (hfresh : ev ∉ s.journal) :
    ev ∉ (redeliver ⟨[], s⟩).journal := by
  simpa [redeliver] using hfresh

/-- Journalled before it is acknowledged upstream, the update survives a crash:
redelivery records it again, and recording is idempotent. -/
theorem journal_first_survives (s : EventPump.Inbox) (ev : EventPump.Event)
    (h : ev.owner = s.owner ∧ s.phase ev.serial = none) :
    redeliver ⟨[ev], EventPump.record s ev⟩ = EventPump.record s ev ∧
    ev ∈ (redeliver ⟨[ev], EventPump.record s ev⟩).journal := by
  have hidem := EventPump.duplicate_arrival_is_idempotent s ev
  refine ⟨by simp [redeliver, hidem], ?_⟩
  simp only [redeliver, List.foldl_cons, List.foldl_nil, hidem]
  exact (EventPump.accepted_event_is_queued s ev h).1

/-! ### Layer (c), liveness: every input is processed -/

/-- Assumptions under which the fixed design is live. The graceful threshold
`T` leaves room for a turn's growth under the workload's allocation per unit
`g` and turn size `W`. A fresh process starts at or below `T`. A legitimate
wait lasts at most `w` consecutive ticks, and the progress deadline does not
cut it off. Nothing outside the service kills it. -/
structure Nominal (P : Policy) (L : Limits) (env : Nat → Tick) (T g W w : Nat) : Prop where
  threshold : P.threshold = some T
  freshBelow : L.base ≤ T
  room : T + g * (W + 1) ≤ L.high
  hardAbove : L.high ≤ L.max
  work : BoundedWork g W env
  waits : ∀ n, ∃ i ≤ w, (env (n + i)).wait = false
  deadline : ∀ D, P.progressDeadline = some D → w ≤ D
  noExternal : ∀ n, (env n).externalKill = false

def ShortTurn (W : Nat) (p : Proc) : Prop := ∀ k, p.phase = .busy k → k ≤ W

theorem shortTurn_survivor (P : Policy) (L : Limits) (W : Nat) (s : State) (e : Tick) (p : Proc)
    (hp : ShortTurn W p) (he : e.work ≤ W) : ShortTurn W (survivor s e p (move P L p e)) := by
  generalize hm : move P L p e = m
  cases m with
  | passed => intro k hk; simp [survivor, advance] at hk; omega
  | worked =>
    obtain ⟨⟨k, hph⟩, -, -, -⟩ := move_worked hm
    have := hp k hph
    cases k with
    | zero => intro k' hk'; simp [survivor, advance, hph] at hk'
    | succ k => intro k' hk'; simp [survivor, advance, hph] at hk'; omega
  | stalled => simpa [survivor, advance, ShortTurn] using hp
  | waited => simpa [survivor, advance, ShortTurn] using hp
  | exited => simpa [survivor, advance, ShortTurn] using hp
  | oom => simpa [survivor, advance, ShortTurn] using hp

theorem shortTurn_invariant (P : Policy) (L : Limits) (env : Nat → Tick) (owner : EventPump.Key)
    (W : Nat) (hw : ∀ n, (env n).work ≤ W) :
    ∀ n p, (run P L env (boot L owner) n).life = .up p → ShortTurn W p := by
  intro n
  induction n with
  | zero => intro p hp k hk; cases hp; simp [fresh] at hk
  | succ n ih =>
    intro q hq
    rw [run_succ] at hq
    rcases step_life_cases P L (run P L env (boot L owner) n) (env n) with
      hd | ⟨_, hf⟩ | ⟨p, hp, hl, _⟩
    · rw [hd] at hq; cases hq
    · rw [hf] at hq; cases hq; intro k hk; simp [fresh] at hk
    · rw [hl] at hq; cases hq; exact shortTurn_survivor P L W _ _ p (ih p hp) (hw n)

/-- The watchdog's silence counter only counts legitimate waits. -/
def WaitTrace (env : Nat → Tick) (n : Nat) (s : State) : Prop :=
  s.quiet ≤ n ∧ ∀ i < s.quiet, (env (n - 1 - i)).wait = true

section Nominal

variable {P : Policy} {L : Limits} {env : Nat → Tick} {owner : EventPump.Key} {T g W w : Nat}

theorem nominal_mem (h : Nominal P L env T g W w) (n : Nat) (p : Proc)
    (hp : (run P L env (boot L owner) n).life = .up p) : p.mem ≤ L.high :=
  graceful_never_throttles P L env owner T (g * (W + 1)) h.threshold h.freshBelow h.room
    (turn_growth_of_rate P L env owner g W h.work) n p hp

theorem nominal_grown (h : Nominal P L env T g W w) (n : Nat) (p : Proc) (k : Nat)
    (hp : (run P L env (boot L owner) n).life = .up p) (hph : p.phase = .busy k) :
    grown p (env n) ≤ L.high := by
  have hg := graceful_invariant P L env (boot L owner) T (g * (W + 1)) h.threshold h.freshBelow
    (boot_graceful L owner T _ h.freshBelow) (turn_growth_of_rate P L env owner g W h.work) n p hp
  have hb := (hg.2 k hph).1
  have hpace := paced_invariant P L env owner g W h.work n p hp k hph
  have hk : g ≤ (k + 1) * g := Nat.le_mul_of_pos_left g (by omega)
  have ha := (h.work n).1
  have hroom := h.room
  rw [Nat.mul_comm g (W + 1)] at hroom
  simp only [grown]
  omega

theorem nominal_not_stalled (h : Nominal P L env T g W w) (n : Nat) (p : Proc)
    (hp : (run P L env (boot L owner) n).life = .up p) : move P L p (env n) ≠ .stalled :=
  not_stalled_of_le (nominal_mem h n p hp)

theorem nominal_not_oom (h : Nominal P L env T g W w) (n : Nat) (p : Proc)
    (hp : (run P L env (boot L owner) n).life = .up p) : move P L p (env n) ≠ .oom := by
  intro hm
  obtain ⟨⟨k, hph⟩, hM⟩ := move_oom hm
  have := nominal_grown h n p k hp hph
  have := h.hardAbove
  omega

theorem nominal_next_mem (h : Nominal P L env T g W w) (n : Nat) (p : Proc)
    (hp : (run P L env (boot L owner) n).life = .up p) :
    (advance p (env n) (pendingIds ((env n).arrivals.foldl EventPump.record
      (run P L env (boot L owner) n).inbox)) (move P L p (env n))).mem ≤ L.high := by
  have hmem := nominal_mem h n p hp
  generalize hm : move P L p (env n) = m
  cases m with
  | worked =>
    obtain ⟨⟨k, hph⟩, -, -, -⟩ := move_worked hm
    have := nominal_grown h n p k hp hph
    cases k with
    | zero => simpa [advance, hph] using this
    | succ k => simpa [advance, hph] using this
  | passed => simpa [advance] using hmem
  | stalled => simpa [advance] using hmem
  | waited => simpa [advance] using hmem
  | exited => simpa [advance] using hmem
  | oom => simpa [advance] using hmem

theorem nominal_waittrace (h : Nominal P L env T g W w) :
    ∀ n, WaitTrace env n (run P L env (boot L owner) n) := by
  intro n
  induction n with
  | zero => exact ⟨Nat.le_refl _, fun i hi => by simp [boot] at hi⟩
  | succ n ih =>
    rw [run_succ]
    cases hs : (run P L env (boot L owner) n).life with
    | down => rw [step_of_down P L _ _ hs]; exact ⟨Nat.zero_le _, fun i hi => by simp at hi⟩
    | up p =>
      rw [step_of_up P L _ _ p hs]
      cases hk : killedAt P L (run P L env (boot L owner) n) (env n) p
      · simp only [Bool.false_eq_true, if_false]
        cases hpr : (move P L p (env n)).progress
        · simp only [Bool.false_eq_true, if_false]
          have hwait : (env n).wait = true := by
            generalize hm : move P L p (env n) = m at hpr
            cases m with
            | waited => exact (move_waited hm).2
            | stalled => exact absurd hm (nominal_not_stalled h n p hs)
            | exited =>
              have := killedAt_false_not_ends hk; rw [hm] at this; cases this
            | oom => exact absurd hm (nominal_not_oom h n p hs)
            | worked => cases hpr
            | passed => cases hpr
          refine ⟨?_, fun i hi => ?_⟩
          · show (run P L env (boot L owner) n).quiet + 1 ≤ n + 1
            have := ih.1; omega
          · have hi' : i < (run P L env (boot L owner) n).quiet + 1 := hi
            show (env (n + 1 - 1 - i)).wait = true
            cases i with
            | zero => simpa using hwait
            | succ i =>
              have := ih.2 i (by omega)
              rwa [show n + 1 - 1 - (i + 1) = n - 1 - i by omega]
        · simp only [if_true]; exact ⟨Nat.zero_le _, fun i hi => by simp at hi⟩
      · simp only [if_true]; exact ⟨Nat.zero_le _, fun i hi => by simp at hi⟩

theorem nominal_quiet_room (h : Nominal P L env T g W w) (n : Nat)
    (hwait : (env n).wait = true) : (run P L env (boot L owner) n).quiet + 1 ≤ w := by
  obtain ⟨hle, hall⟩ := nominal_waittrace (owner := owner) h n
  generalize (run P L env (boot L owner) n).quiet = q at hle hall
  by_cases hq : q + 1 ≤ w
  · exact hq
  · obtain ⟨i, hi, hfree⟩ := h.waits (n - q)
    exfalso
    by_cases hin : n - q + i = n
    · rw [hin, hwait] at hfree; cases hfree
    · have := hall (n - 1 - (n - q + i)) (by omega)
      rw [show n - 1 - (n - 1 - (n - q + i)) = n - q + i by omega, hfree] at this
      cases this

/-- Under the nominal assumptions the only way a process ends is its own
boundary exit: no watchdog fires, the kernel never kills, nothing else does. -/
theorem nominal_alive (h : Nominal P L env T g W w) (n : Nat) (p : Proc)
    (hp : (run P L env (boot L owner) n).life = .up p) (hne : move P L p (env n) ≠ .exited) :
    killedAt P L (run P L env (boot L owner) n) (env n) p = false := by
  have hq := nominal_next_mem h n p hp
  have hns := nominal_not_stalled h n p hp
  have hno := nominal_not_oom h n p hp
  have hends : (move P L p (env n)).ends = false := by
    generalize move P L p (env n) = m at hne hns hno
    cases m <;> simp_all [Move.ends]
  have hquiet : ∀ D, P.progressDeadline = some D →
      (if (move P L p (env n)).progress then 0 else (run P L env (boot L owner) n).quiet + 1) ≤ D := by
    intro D hD
    have hwD := h.deadline D hD
    cases hpr : (move P L p (env n)).progress
    · simp only [Bool.false_eq_true, if_false]
      have hwait : (env n).wait = true := by
        generalize hm : move P L p (env n) = m at hpr hns hno hends
        cases m with
        | waited => exact (move_waited hm).2
        | stalled => exact absurd rfl hns
        | oom => exact absurd rfl hno
        | exited => cases hends
        | worked => cases hpr
        | passed => cases hpr
      have := nominal_quiet_room (owner := owner) h n hwait
      omega
    · simp
  simp only [killedAt, hends, h.noExternal n, Bool.false_or, Bool.or_false]
  have hz : (if decide (L.high < (advance p (env n) (pendingIds ((env n).arrivals.foldl
      EventPump.record (run P L env (boot L owner) n).inbox)) (move P L p (env n))).mem) = true
      then (run P L env (boot L owner) n).pressure + 1 else 0) = 0 := by
    simp; omega
  rw [hz]
  simp only [watchdogKills, overdue_zero, Bool.or_false]
  cases hD : P.progressDeadline with
  | none => simp [overdue]
  | some D => have := hquiet D hD; simp [overdue]; omega

theorem nominal_step_up (h : Nominal P L env T g W w) (n : Nat) (p : Proc)
    (hp : (run P L env (boot L owner) n).life = .up p) (hne : move P L p (env n) ≠ .exited) :
    (run P L env (boot L owner) (n + 1)).life =
      .up (survivor (run P L env (boot L owner) n) (env n) p (move P L p (env n))) ∧
    (run P L env (boot L owner) (n + 1)).inbox =
      inboxAfter p ((env n).arrivals.foldl EventPump.record (run P L env (boot L owner) n).inbox)
        (move P L p (env n)) ∧
    (run P L env (boot L owner) (n + 1)).processed =
      if completes p (move P L p (env n)) then (run P L env (boot L owner) n).processed ++ p.claimed
      else (run P L env (boot L owner) n).processed := by
  have hk := nominal_alive h n p hp hne
  rw [run_succ, step_of_up P L _ _ p hp]
  simp [hk]

theorem not_withheld_of (h : Nominal P L env T g W w) (n : Nat) (p : Proc)
    (hp : (run P L env (boot L owner) n).life = .up p) :
    ¬ ((env n).stall = true ∧ L.high < p.mem) := by
  have := nominal_mem h n p hp; omega

theorem nominal_wait_run (h : Nominal P L env T g W w) (n : Nat) (p : Proc) (k : Nat)
    (hp : (run P L env (boot L owner) n).life = .up p) (hph : p.phase = .busy k) :
    ∀ i, (∀ j < i, (env (n + j)).wait = true) →
      ∃ r, (run P L env (boot L owner) (n + i)).life = .up { p with recycle := r } ∧
        (run P L env (boot L owner) (n + i)).processed = (run P L env (boot L owner) n).processed ∧
        (∀ id x, (run P L env (boot L owner) n).inbox.phase id = some x →
          (run P L env (boot L owner) (n + i)).inbox.phase id = some x) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨p.recycle, by rw [Nat.add_zero, hp], rfl, fun _ _ hx => hx⟩
  | succ i ih =>
    intro hw
    obtain ⟨r, hr, hproc, hph'⟩ := ih (fun j hj => hw j (by omega))
    have hwait := hw i (by omega)
    have hm : move P L { p with recycle := r } (env (n + i)) = .waited := by
      rw [move_of_not_withheld (not_withheld_of h _ _ hr)]
      simp [hph, hwait]
    obtain ⟨hl, hi, hpr⟩ := nominal_step_up h (n + i) _ hr (by rw [hm]; simp)
    rw [← Nat.add_assoc]
    refine ⟨r || (env (n + i)).timer, ?_, ?_, fun id x hx => ?_⟩
    · rw [hl, hm]; rfl
    · rw [hpr, hm, hproc]; rfl
    · rw [hi, hm]
      exact recordAll_keeps_phase _ _ id x (hph' id x hx)

theorem nominal_unit (h : Nominal P L env T g W w) (n : Nat) (p : Proc) (k : Nat)
    (hp : (run P L env (boot L owner) n).life = .up p) (hph : p.phase = .busy k) :
    ∃ i ≤ w, ∃ r, (run P L env (boot L owner) (n + i)).life = .up { p with recycle := r } ∧
      (env (n + i)).wait = false ∧
      (run P L env (boot L owner) (n + i)).processed = (run P L env (boot L owner) n).processed ∧
      (∀ id x, (run P L env (boot L owner) n).inbox.phase id = some x →
        (run P L env (boot L owner) (n + i)).inbox.phase id = some x) := by
  obtain ⟨i₀, hi₀, hfree₀⟩ := h.waits n
  obtain ⟨i, hi, hfirst⟩ := exists_least (fun j => !(env (n + j)).wait) (i₀ + 1)
    ⟨i₀, by omega, by simp [hfree₀]⟩
  have hile : i ≤ i₀ := by
    by_cases hc : i ≤ i₀
    · exact hc
    · have := hfirst i₀ (by omega); simp [hfree₀] at this
  obtain ⟨r, hr, hproc, hph'⟩ := nominal_wait_run h n p k hp hph i
    (fun j hj => by simpa using hfirst j hj)
  exact ⟨i, by omega, r, hr, by simpa using hi, hproc, hph'⟩

theorem nominal_work (h : Nominal P L env T g W w) (n : Nat) (p : Proc) (k : Nat)
    (hp : (run P L env (boot L owner) n).life = .up p) (hph : p.phase = .busy k)
    (hwait : (env n).wait = false) : move P L p (env n) = .worked :=
  move_worked_of hph (not_withheld_of h n p hp) hwait
    (by have := nominal_grown h n p k hp hph; have := h.hardAbove; omega)

/-- **Turns complete.** Under the nominal assumptions a turn with `k + 1`
units left reaches its boundary within `(k + 1) * (w + 1)` ticks, having
recorded everything it claimed as processed and left queued inputs queued. -/
theorem nominal_turn_completes (h : Nominal P L env T g W w) :
    ∀ k n p, (run P L env (boot L owner) n).life = .up p → p.phase = .busy k →
      ∃ m, n < m ∧ m ≤ n + (k + 1) * (w + 1) ∧
        ∃ p', (run P L env (boot L owner) m).life = .up p' ∧ p'.phase = .boundary ∧
          (∀ id ∈ p.claimed, id ∈ (run P L env (boot L owner) m).processed) ∧
          (∀ id, (run P L env (boot L owner) n).inbox.phase id = some .queued →
            (run P L env (boot L owner) m).inbox.phase id = some .queued) := by
  intro k
  induction k with
  | zero =>
    intro n p hp hph
    obtain ⟨i, hi, r, hr, hwait, hproc, hkeep⟩ := nominal_unit h n p 0 hp hph
    have hm := nominal_work h (n + i) _ 0 hr hph hwait
    obtain ⟨hl, hin, hpr⟩ := nominal_step_up h (n + i) _ hr (by rw [hm]; simp)
    refine ⟨n + i + 1, by omega, by omega, _, hl, ?_, fun id hid => ?_, fun id hq => ?_⟩
    · simp only [survivor]; rw [hm]; simp [advance, hph]
    · rw [hpr, hm]; simp [completes, hph, hid]
    · rw [hin, hm]
      simp only [inboxAfter, hph, beq_self_eq_true, if_true, settleEach_phase]
      have := recordAll_keeps_phase _ ((env (n + i)).arrivals) id _ (hkeep id _ hq)
      rw [this]; simp
  | succ k ih =>
    intro n p hp hph
    obtain ⟨i, hi, r, hr, hwait, hproc, hkeep⟩ := nominal_unit h n p (k + 1) hp hph
    have hm := nominal_work h (n + i) _ (k + 1) hr hph hwait
    obtain ⟨hl, hin, hpr⟩ := nominal_step_up h (n + i) _ hr (by rw [hm]; simp)
    have hne : (Phase.busy (k + 1) == Phase.busy 0) = false := by simp
    obtain ⟨m, hm1, hm2, p', hp', hb', hcl', hq'⟩ := ih (n + i + 1) _ hl
      (by simp only [survivor]; rw [hm]; simp [advance, hph])
    refine ⟨m, by omega, ?_, p', hp', hb', fun id hid => hcl' id ?_, fun id hq => hq' id ?_⟩
    · have : (k + 1 + 1) * (w + 1) = (k + 1) * (w + 1) + (w + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    · simp only [survivor]; rw [hm]; simp [advance, hph, hid]
    · rw [hin, hm]
      simp only [inboxAfter, hph, hne]
      exact recordAll_keeps_phase _ _ id _ (hkeep id _ hq)

theorem restart_tick (P : Policy) (L : Limits) (env : Nat → Tick) (s : State) (n : Nat)
    (hd : (run P L env s n).life = .down) :
    (run P L env s (n + 1)).life = .up (fresh L) ∧
    ∀ id x, (run P L env s n).inbox.phase id = some x →
      (run P L env s (n + 1)).inbox.phase id = some x := by
  rw [run_succ, step_of_down P L _ _ hd]
  exact ⟨rfl, fun id x hx => recordAll_keeps_phase _ _ id x hx⟩

theorem nominal_pass (h : Nominal P L env T g W w) (n : Nat) (p : Proc)
    (hp : (run P L env (boot L owner) n).life = .up p) (hb : p.phase = .boundary)
    (hl : leaves P p = false) (ev : EventPump.Event)
    (hev : ev ∈ (run P L env (boot L owner) n).inbox.journal)
    (hq : (run P L env (boot L owner) n).inbox.phase ev.serial = some .queued) :
    ∃ p', (run P L env (boot L owner) (n + 1)).life = .up p' ∧ (∃ k, p'.phase = .busy k) ∧
      ev.serial ∈ p'.claimed := by
  have hm : move P L p (env n) = .passed := by
    rw [move_of_not_withheld (not_withheld_of h n p hp), hb]; simp [hl]
  obtain ⟨hlife, -, -⟩ := nominal_step_up h n p hp (by rw [hm]; simp)
  refine ⟨_, hlife, ⟨(env n).work, by simp [survivor, advance, hm]⟩, ?_⟩
  simp only [survivor, advance, hm]
  exact pending_queued _ ev (recordAll_journal _ _ ev hev)
    (recordAll_keeps_phase _ _ _ _ hq)

theorem nominal_exit (h : Nominal P L env T g W w) (n : Nat) (p : Proc)
    (hp : (run P L env (boot L owner) n).life = .up p) (hb : p.phase = .boundary)
    (hl : leaves P p = true) :
    (run P L env (boot L owner) (n + 1)).life = .down ∧
    ∀ id, (run P L env (boot L owner) n).inbox.phase id = some .queued →
      (run P L env (boot L owner) (n + 1)).inbox.phase id = some .queued := by
  have hm : move P L p (env n) = .exited := by
    rw [move_of_not_withheld (not_withheld_of h n p hp), hb]; simp [hl]
  have hk : killedAt P L (run P L env (boot L owner) n) (env n) p = true := by
    simp [killedAt, hm, Move.ends]
  rw [run_succ, step_of_up P L _ _ p hp]
  refine ⟨by simp [hk], fun id hq => ?_⟩
  simp only [hk, if_true, hm, inboxAfter, recover_phase]
  rw [recordAll_keeps_phase _ _ id _ hq]
  simp

/-- **Queued inputs get claimed.** From a boundary, or from a restart, the next
turn starts within three ticks and claims every queued input. -/
theorem nominal_claims (h : Nominal P L env T g W w) (n : Nat) (ev : EventPump.Event)
    (hev : ev ∈ (run P L env (boot L owner) n).inbox.journal)
    (hq : (run P L env (boot L owner) n).inbox.phase ev.serial = some .queued)
    (hb : (run P L env (boot L owner) n).life = .down ∨
      ∃ p, (run P L env (boot L owner) n).life = .up p ∧ p.phase = .boundary) :
    ∃ m, n < m ∧ m ≤ n + 3 ∧ ∃ p', (run P L env (boot L owner) m).life = .up p' ∧
      (∃ k, p'.phase = .busy k) ∧ ev.serial ∈ p'.claimed := by
  have hfresh : leaves P (fresh L) = false :=
    leaves_fresh P L (fun T' hT' => by rw [h.threshold] at hT'; cases hT'; exact h.freshBelow)
  have from_down : ∀ n', n' ≤ n + 1 → (run P L env (boot L owner) n').life = .down →
      (run P L env (boot L owner) n').inbox.phase ev.serial = some .queued → n ≤ n' →
      ∃ m, n < m ∧ m ≤ n + 3 ∧ ∃ p', (run P L env (boot L owner) m).life = .up p' ∧
        (∃ k, p'.phase = .busy k) ∧ ev.serial ∈ p'.claimed := by
    intro n' hn' hd hq' hle
    obtain ⟨hf, hkeep⟩ := restart_tick P L env (boot L owner) n' hd
    have hev' := journal_mono P L env (boot L owner) n ev hev (n' + 1 - n)
    rw [show n + (n' + 1 - n) = n' + 1 by omega] at hev'
    obtain ⟨p', hp', hk', hc'⟩ := nominal_pass h (n' + 1) (fresh L) hf rfl hfresh ev hev'
      (hkeep _ _ hq')
    exact ⟨n' + 1 + 1, by omega, by omega, p', hp', hk', hc'⟩
  rcases hb with hd | ⟨p, hp, hbd⟩
  · exact from_down n (by omega) hd hq (Nat.le_refl _)
  · cases hl : leaves P p
    · obtain ⟨p', hp', hk', hc'⟩ := nominal_pass h n p hp hbd hl ev hev hq
      exact ⟨n + 1, by omega, by omega, p', hp', hk', hc'⟩
    · obtain ⟨hd, hkeep⟩ := nominal_exit h n p hp hbd hl
      exact from_down (n + 1) (Nat.le_refl _) hd (hkeep _ hq) (by omega)

/-- **Layer (c), liveness: every input is processed, within a bound.** Under the
nominal assumptions, an input in the journal at tick `n` has been processed,
by a turn that reached its checkpoint, by tick `n + 2 (W + 1)(w + 1) + 3`. -/
theorem every_input_processed (h : Nominal P L env T g W w) (n : Nat) (ev : EventPump.Event)
    (hev : ev ∈ (run P L env (boot L owner) n).inbox.journal) :
    ∃ m, n ≤ m ∧ m ≤ n + 2 * ((W + 1) * (w + 1)) + 3 ∧
      ev.serial ∈ (run P L env (boot L owner) m).processed := by
  have hshort := shortTurn_invariant P L env owner W (fun n => (h.work n).2)
  have hbound : ∀ k, k ≤ W → (k + 1) * (w + 1) ≤ (W + 1) * (w + 1) :=
    fun k hk => Nat.mul_le_mul_right _ (by omega)
  have finish : ∀ n₁, n ≤ n₁ → n₁ ≤ n + (W + 1) * (w + 1) + 3 →
      ∀ p, (run P L env (boot L owner) n₁).life = .up p → (∃ k, p.phase = .busy k) →
      ev.serial ∈ p.claimed →
      ∃ m, n ≤ m ∧ m ≤ n + 2 * ((W + 1) * (w + 1)) + 3 ∧
        ev.serial ∈ (run P L env (boot L owner) m).processed := by
    intro n₁ hn₁ hn₁' p hp ⟨k, hk⟩ hc
    obtain ⟨m, hm1, hm2, -, -, -, hcl, -⟩ := nominal_turn_completes h k n₁ p hp hk
    have := hbound k (hshort n₁ p hp k hk)
    exact ⟨m, by omega, by omega, hcl _ hc⟩
  obtain ⟨-, hcase⟩ := no_input_lost P L env owner n ev hev 0
  simp only [Nat.add_zero] at hcase
  rcases hcase with hq | ⟨_, p, hp, hc⟩ | ⟨_, hpr⟩
  · cases hlife : (run P L env (boot L owner) n).life with
    | down =>
      obtain ⟨m₁, h1, h2, p', hp', hk', hc'⟩ := nominal_claims h n ev hev hq (Or.inl hlife)
      exact finish m₁ (by omega) (by omega) p' hp' hk' hc'
    | up p =>
      cases hph : p.phase with
      | boundary =>
        obtain ⟨m₁, h1, h2, p', hp', hk', hc'⟩ :=
          nominal_claims h n ev hev hq (Or.inr ⟨p, hlife, hph⟩)
        exact finish m₁ (by omega) (by omega) p' hp' hk' hc'
      | busy k =>
        obtain ⟨m₁, h1, h2, p₁, hp₁, hb₁, -, hq₁⟩ := nominal_turn_completes h k n p hlife hph
        have hev₁ := journal_mono P L env (boot L owner) n ev hev (m₁ - n)
        rw [show n + (m₁ - n) = m₁ by omega] at hev₁
        obtain ⟨m₂, h3, h4, p₂, hp₂, hk₂, hc₂⟩ :=
          nominal_claims h m₁ ev hev₁ (hq₁ _ hq) (Or.inr ⟨p₁, hp₁, hb₁⟩)
        have := hbound k (hshort n p hlife k hph)
        obtain ⟨k₂, hk₂'⟩ := hk₂
        obtain ⟨m, hm1, hm2, -, -, -, hcl, -⟩ := nominal_turn_completes h k₂ m₂ p₂ hp₂ hk₂'
        have := hbound k₂ (hshort m₂ p₂ hp₂ k₂ hk₂')
        exact ⟨m, by omega, by omega, hcl _ hc₂⟩
  · cases hph : p.phase with
    | boundary =>
      have := (accounted_invariant P L env (boot L owner) (boot_accounted L owner) n).2.2.2 p hp hph
      rw [this] at hc; cases hc
    | busy k => exact finish n (Nat.le_refl _) (by omega) p hp ⟨k, hph⟩ hc
  · exact ⟨n, Nat.le_refl _, by omega, hpr⟩

end Nominal

/-- **No false kills.** Under the nominal assumptions the only deaths are
boundary exits: the graceful threshold or a recycle request, honoured below
the soft limit. The watchdog never fires and the kernel never kills. -/
theorem nominal_deaths_are_exits {P : Policy} {L : Limits} {env : Nat → Tick}
    {owner : EventPump.Key} {T g W w : Nat} (h : Nominal P L env T g W w) (n : Nat) (p : Proc)
    (hp : (run P L env (boot L owner) n).life = .up p)
    (hd : (run P L env (boot L owner) (n + 1)).life = .down) :
    move P L p (env n) = .exited ∧ p.phase = .boundary := by
  by_cases hm : move P L p (env n) = .exited
  · exact ⟨hm, (move_exited hm).1⟩
  · have := (nominal_step_up h n p hp hm).1
    rw [hd] at this; cases this

/-- Under the graceful layer the agent is never withheld, so a session-scoped
pressure killer never acts on it: the nominal assumption of no external kills
then holds for such a killer. -/
theorem session_killer_silent_under_graceful (S : Nat) (P : Policy) (L : Limits)
    (env : Nat → Tick) (owner : EventPump.Key) (T δ : Nat) (hT : P.threshold = some T)
    (hbase : L.base ≤ T) (hroom : T + δ ≤ L.high)
    (hgrow : TurnGrowthWithin δ P L env (boot L owner))
    (hK : SessionKiller S P L env (boot L owner)) : ∀ n, (env n).externalKill = false := by
  intro n
  cases hk : (env n).externalKill
  · rfl
  · obtain ⟨_, hall⟩ := (hK n).mp hk
    have hfull := (hall 0 (Nat.zero_le _)).1
    simp only [Nat.sub_zero, moveAt] at hfull
    cases hl : (run P L env (boot L owner) n).life with
    | down => rw [hl] at hfull; cases hfull
    | up p =>
      rw [hl] at hfull
      have hle := graceful_never_throttles P L env owner T δ hT hbase hroom hgrow n p hl
      have := (move_stalled_iff.mp (Option.some.inj hfull)).2
      omega

/-! ### What the liveness assumptions buy -/

/-- **Bounded waits are essential.** If the turn's external call never returns,
no supervision policy completes it. Nothing is ever processed, although every
input stays in the journal. -/
theorem unbounded_wait_never_processes (P : Policy) (L : Limits) (owner : EventPump.Key)
    (env : Nat → Tick) (hwait : ∀ n, (env n).wait = true) :
    ∀ n, (run P L env (boot L owner) n).processed = [] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ]
    cases hs : (run P L env (boot L owner) n).life with
    | down => rw [step_of_down P L _ _ hs]; exact ih
    | up p =>
      rw [step_of_up P L _ _ p hs]
      have : completes p (move P L p (env n)) = false := by
        generalize hm : move P L p (env n) = m
        cases m with
        | worked => have := (move_worked hm).2.1; rw [hwait n] at this; cases this
        | _ => rfl
      simp [this, ih]

/-- A poison input: its turn has `N + 1` units, each allocating `g`. -/
def poison (owner : EventPump.Key) (g N : Nat) (n : Nat) : Tick :=
  { stall := true, work := N, alloc := g,
    arrivals := if n = 0 then [⟨0, owner, 0⟩] else [] }

theorem poison_shape (P : Policy) (L : Limits) (owner : EventPump.Key) (g N : Nat)
    (hover : L.high < L.base + N * g) :
    ∀ n p, (run P L (poison owner g N) (boot L owner) n).life = .up p →
      (p.phase = .boundary → p.mem = L.base) ∧
      (∀ k, p.phase = .busy k → k ≤ N ∧ p.mem = L.base + (N - k) * g) := by
  intro n
  induction n with
  | zero => intro p hp; cases hp; exact ⟨fun _ => rfl, fun k hk => by simp [fresh] at hk⟩
  | succ n ih =>
    intro q hq
    rw [run_succ] at hq
    rcases step_life_cases P L (run P L (poison owner g N) (boot L owner) n)
      (poison owner g N n) with hd | ⟨_, hf⟩ | ⟨p, hp, hl, _⟩
    · rw [hd] at hq; cases hq
    · rw [hf] at hq; cases hq; exact ⟨fun _ => rfl, fun k hk => by simp [fresh] at hk⟩
    · rw [hl] at hq; cases hq
      obtain ⟨hb, hbusy⟩ := ih p hp
      generalize hm : move P L p (poison owner g N n) = m
      cases m with
      | passed =>
        have hmem := hb (move_passed hm).1
        refine ⟨fun h => by simp [survivor, advance] at h, fun k hk => ?_⟩
        simp [survivor, advance, poison] at hk ⊢
        subst hk; simp [hmem]
      | worked =>
        obtain ⟨⟨k, hph⟩, -, -, hns⟩ := move_worked hm
        obtain ⟨hkN, hmem⟩ := hbusy k hph
        cases k with
        | zero =>
          exfalso; apply hns
          refine ⟨rfl, ?_⟩
          rw [hmem]; simpa using hover
        | succ k =>
          refine ⟨fun h => by simp [survivor, advance, hph] at h, fun k' hk' => ?_⟩
          simp [survivor, advance, hph] at hk' ⊢
          subst hk'
          refine ⟨by omega, ?_⟩
          simp only [grown, poison, hmem, Nat.sub_zero]
          have : N - k = N - (k + 1) + 1 := by omega
          rw [this, Nat.succ_mul]
          omega
      | stalled => exact ⟨by simpa [survivor, advance] using hb, by simpa [survivor, advance] using hbusy⟩
      | waited => exact ⟨by simpa [survivor, advance] using hb, by simpa [survivor, advance] using hbusy⟩
      | exited => exact ⟨by simpa [survivor, advance] using hb, by simpa [survivor, advance] using hbusy⟩
      | oom => exact ⟨by simpa [survivor, advance] using hb, by simpa [survivor, advance] using hbusy⟩

/-- **The per-turn bound is essential, even with both layers.** A turn that
outgrows the soft limit before its end is never completed, under any policy:
the graceful layer finds no boundary, and the backstop's kill only restarts
the same turn. The poison input stays in the journal and is never processed;
bounding a turn's growth, or the attempts an input gets, is the remedy. -/
theorem poison_never_processed (P : Policy) (L : Limits) (owner : EventPump.Key) (g N : Nat)
    (hover : L.high < L.base + N * g) :
    ∀ n, (run P L (poison owner g N) (boot L owner) n).processed = [] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ]
    cases hs : (run P L (poison owner g N) (boot L owner) n).life with
    | down => rw [step_of_down P L _ _ hs]; exact ih
    | up p =>
      rw [step_of_up P L _ _ p hs]
      have : completes p (move P L p (poison owner g N n)) = false := by
        generalize hm : move P L p (poison owner g N n) = m
        cases m with
        | worked =>
          obtain ⟨⟨k, hph⟩, -, -, hns⟩ := move_worked hm
          cases k with
          | zero =>
            obtain ⟨-, hmem⟩ := (poison_shape P L owner g N hover n p hs).2 0 hph
            exfalso; apply hns; refine ⟨rfl, ?_⟩; rw [hmem]; simpa using hover
          | succ k => simp [completes, hph]
        | _ => rfl
      simp [this, ih]

theorem poison_is_journalled (P : Policy) (L : Limits) (owner : EventPump.Key) (g N : Nat) :
    (⟨0, owner, 0⟩ : EventPump.Event) ∈
      (run P L (poison owner g N) (boot L owner) 1).inbox.journal := by
  rw [run_succ, run_zero]
  have hrec : (⟨0, owner, 0⟩ : EventPump.Event) ∈
      ((poison owner g N 0).arrivals.foldl EventPump.record (boot L owner).inbox).journal := by
    simp [poison, boot, EventPump.record]
  rw [step_of_up P L _ _ (fresh L) rfl]
  have hJ : (⟨0, owner, 0⟩ : EventPump.Event) ∈ (inboxAfter (fresh L)
      ((poison owner g N 0).arrivals.foldl EventPump.record (boot L owner).inbox)
      (move P L (fresh L) (poison owner g N 0))).journal := by
    cases move P L (fresh L) (poison owner g N 0) with
    | passed => simp only [inboxAfter]; rw [claimEach_journal]; exact hrec
    | worked =>
      simp only [inboxAfter]; split
      · rw [settleEach_journal]; exact hrec
      · exact hrec
    | stalled => exact hrec
    | waited => exact hrec
    | exited => exact hrec
    | oom => exact hrec
  cases killedAt P L (boot L owner) (poison owner g N 0) (fresh L)
  · simpa using hJ
  · simpa [EventPump.recover] using hJ

/-- **A fresh process must start at or below the threshold.** Otherwise every
process leaves at its first boundary: no turn ever starts and nothing is
processed, while the service restarts for ever. -/
theorem threshold_below_fresh_livelocks (P : Policy) (L : Limits) (owner : EventPump.Key)
    (env : Nat → Tick) (T : Nat) (hT : P.threshold = some T) (hfresh : T < L.base)
    (hbH : L.base ≤ L.high) :
    ∀ n, (∀ p, (run P L env (boot L owner) n).life = .up p → p = fresh L) ∧
      (run P L env (boot L owner) n).processed = [] := by
  intro n
  induction n with
  | zero => exact ⟨fun p hp => by cases hp; rfl, rfl⟩
  | succ n ih =>
    obtain ⟨hfr, hpr⟩ := ih
    have hexit : ∀ e, move P L (fresh L) e = .exited := by
      intro e
      rw [move_of_not_withheld (by simp only [fresh]; omega)]
      simp [fresh, leaves, hT, hfresh]
    rw [run_succ]
    cases hs : (run P L env (boot L owner) n).life with
    | down =>
      rw [step_of_down P L _ _ hs]
      exact ⟨fun p hp => by simp only [Life.up.injEq] at hp; exact hp.symm, hpr⟩
    | up p =>
      have hp := hfr p hs
      subst hp
      rw [step_of_up P L _ _ _ hs]
      have hk : killedAt P L (run P L env (boot L owner) n) (env n) (fresh L) = true := by
        simp [killedAt, hexit, Move.ends]
      refine ⟨fun q hq => by simp [hk] at hq, ?_⟩
      simp [hexit, completes, hpr]

/-- **External kills must be bounded.** A killer that ends every turn as it
starts leaves every input unprocessed, under any policy. -/
theorem external_kills_starve (P : Policy) (L : Limits) (owner : EventPump.Key)
    (env : Nat → Tick) (hkill : ∀ n, (env n).externalKill = true) :
    ∀ n, (∀ p, (run P L env (boot L owner) n).life = .up p → p.phase = .boundary) ∧
      (run P L env (boot L owner) n).processed = [] := by
  intro n
  induction n with
  | zero => exact ⟨fun p hp => by cases hp; rfl, rfl⟩
  | succ n ih =>
    obtain ⟨hb, hpr⟩ := ih
    rw [run_succ]
    cases hs : (run P L env (boot L owner) n).life with
    | down =>
      rw [step_of_down P L _ _ hs]
      exact ⟨fun p hp => by simp only [Life.up.injEq] at hp; subst hp; rfl, hpr⟩
    | up p =>
      rw [step_of_up P L _ _ p hs]
      have hk : killedAt P L (run P L env (boot L owner) n) (env n) p = true := by
        simp [killedAt, hkill n]
      have hc : completes p (move P L p (env n)) = false := by
        generalize hm : move P L p (env n) = m
        cases m with
        | worked =>
          obtain ⟨⟨k, hph⟩, -⟩ := move_worked hm
          rw [hb p hs] at hph; cases hph
        | _ => rfl
      exact ⟨fun q hq => by simp [hk] at hq, by simp [hc, hpr]⟩

/-- **The hard limit must clear the graceful room.** If the hard limit lies
below `T + δ`, a turn that respects the growth bound `δ` is killed at the
hard limit instead of reaching its boundary. -/
theorem hard_limit_below_room_kills (L : Limits) (owner : EventPump.Key) (T δ : Nat)
    (hbase : L.base = T) (hbH : L.base ≤ L.high) (hM : L.max < T + δ) :
    TurnGrowthWithin δ { threshold := some T } L
        (fun n => if n = 1 then ({ alloc := δ } : Tick) else {}) (boot L owner) ∧
    (run { threshold := some T } L (fun n => if n = 1 then ({ alloc := δ } : Tick) else {})
      (boot L owner) 2).life = .down := by
  constructor
  · have h := turn_growth_of_rate { threshold := some T } L
      (fun n => if n = 1 then ({ alloc := δ } : Tick) else {}) owner δ 0
      (fun n => by by_cases hn : n = 1 <;> simp [hn])
    simpa using h
  · have hH : ¬ L.high < T := by omega
    simp [run, step, killedAt, survivor, boot, fresh, move, leaves, advance, grown, hbase,
      pendingIds, EventPump.pending, watchdogKills, overdue, Move.ends, Move.progress, hM, hH]

/-- A legitimate wait of `D + 1` ticks inside the first turn. -/
def longWait (D : Nat) (n : Nat) : Tick :=
  { stall := true, wait := decide (1 ≤ n ∧ n ≤ D + 1) }

/-- **The progress deadline must cover legitimate waits.** A deadline `D`
shorter than a legitimate wait of `D + 1` ticks kills a process that is below
every limit and only waiting. This is why `Nominal` asks for `w ≤ D`. -/
theorem short_deadline_kills_waiting (L : Limits) (owner : EventPump.Key) (T D : Nat)
    (hbase : L.base ≤ T) (hbH : L.base ≤ L.high) :
    (∀ n, ∃ i ≤ D + 1, (longWait D (n + i)).wait = false) ∧
    (∀ i ≤ D, (run { threshold := some T, progressDeadline := some D } L (longWait D)
      (boot L owner) (1 + i)).life =
        .up { fresh L with phase := .busy 0, claimed := [] }) ∧
    (run { threshold := some T, progressDeadline := some D } L (longWait D) (boot L owner)
      (D + 2)).life = .down := by
  refine ⟨fun n => ?_, ?_⟩
  · by_cases h0 : n = 0
    · exact ⟨0, by omega, by simp [longWait, h0]⟩
    · by_cases hbig : D + 2 ≤ n
      · exact ⟨0, by omega, by simp [longWait]; omega⟩
      · exact ⟨D + 2 - n, by omega, by simp [longWait]; omega⟩
  · have hpass : move { threshold := some T, progressDeadline := some D } L (fresh L)
        (longWait D 0) = .passed :=
      fresh_passes _ L _ hbH (leaves_fresh _ L (fun T' hT' => by simp at hT'; omega))
    have h1 : run { threshold := some T, progressDeadline := some D } L (longWait D)
        (boot L owner) 1 =
        { boot L owner with
          life := .up { fresh L with phase := .busy 0, claimed := [] }, callInFlight := true,
          clock := 1, lastProgress := some 1 } := by
      rw [run_succ, run_zero, step_of_up _ L _ _ (fresh L) rfl]
      have hk : killedAt { threshold := some T, progressDeadline := some D } L (boot L owner)
          (longWait D 0) (fresh L) = false := by
        simp only [killedAt, hpass]
        simp [Move.ends, Move.progress, watchdogKills, overdue, advance, fresh, longWait,
          Nat.not_lt.mpr hbH]
      simp only [hk, hpass]
      simp [survivor, advance, inboxAfter, completes, boot, longWait, pendingIds, claimEach,
        EventPump.pending, Move.progress, fresh, hbH]
    have hwaits : ∀ i ≤ D, run { threshold := some T, progressDeadline := some D } L (longWait D)
        (boot L owner) (1 + i) =
        { boot L owner with
          life := .up { fresh L with phase := .busy 0, claimed := [] }, callInFlight := true,
          quiet := i, clock := 1 + i, lastProgress := some 1 } := by
      intro i hi
      induction i with
      | zero => exact h1
      | succ i ih =>
        rw [← Nat.add_assoc, run_succ, ih (by omega)]
        have hm : move { threshold := some T, progressDeadline := some D } L
            { fresh L with phase := .busy 0, claimed := [] } (longWait D (1 + i)) = .waited := by
          rw [move_of_not_withheld (by simp [fresh]; omega)]
          simp [longWait]; omega
        rw [step_of_up _ L _ _ _ rfl]
        have hk : killedAt { threshold := some T, progressDeadline := some D } L
            { boot L owner with
              life := .up { fresh L with phase := .busy 0, claimed := [] }, callInFlight := true,
              quiet := i, clock := 1 + i, lastProgress := some 1 }
            (longWait D (1 + i)) { fresh L with phase := .busy 0, claimed := [] } = false := by
          simp only [killedAt, hm]
          simp [Move.ends, Move.progress, watchdogKills, overdue, advance, fresh, longWait,
            Nat.not_lt.mpr hbH]
          omega
        simp only [hk, hm]
        simp [survivor, advance, inboxAfter, completes, boot, longWait, Move.progress, fresh]
        exact decide_eq_false (Nat.not_lt.mpr hbH)
    refine ⟨fun i hi => by rw [hwaits i hi], ?_⟩
    rw [show D + 2 = 1 + D + 1 by omega, run_succ, hwaits D (Nat.le_refl _)]
    have hm : move { threshold := some T, progressDeadline := some D } L
        { fresh L with phase := .busy 0, claimed := [] } (longWait D (1 + D)) = .waited := by
      have h1D : 1 + D ≤ D + 1 := by omega
      rw [move_of_not_withheld (by simp [fresh]; omega)]
      simp [longWait, h1D]
    rw [step_of_up _ L _ _ _ rfl]
    have hk : killedAt { threshold := some T, progressDeadline := some D } L
        { boot L owner with
          life := .up { fresh L with phase := .busy 0, claimed := [] }, callInFlight := true,
          quiet := D, clock := 1 + D, lastProgress := some 1 }
        (longWait D (1 + D)) { fresh L with phase := .busy 0, claimed := [] } = true := by
      simp only [killedAt, hm]
      simp [Move.progress, watchdogKills, overdue]
    simp [hk]

/-! ## Layer (d): a status report that reflects progress -/

inductive Report
  | restarting
  | stalled (silentTicks : Nat)
  | working
deriving Repr, DecidableEq

/-- The fixed responder runs outside the supervised service and reads only
what a frozen process cannot keep looking fresh: whether the service manager
has a process running, the control group's memory, and the age of the durable
progress stamp on the responder's own clock. -/
def report (F : Nat) (L : Limits) (s : State) : Report :=
  match s.life with
  | .down => .restarting
  | .up p =>
    match s.lastProgress with
    | none => .stalled s.clock
    | some t =>
      if decide (L.high < p.mem) || decide (F ≤ s.clock - t) then .stalled (s.clock - t)
      else .working

theorem run_lastProgress (P : Policy) (L : Limits) (env : Nat → Tick) (s : State) (n : Nat) :
    (run P L env s (n + 1)).lastProgress =
      if progressAt P L env s n then some ((run P L env s n).clock + 1)
      else (run P L env s n).lastProgress := by
  rw [run_succ]
  cases hs : (run P L env s n).life with
  | down => rw [step_of_down P L _ _ hs]; simp [progressAt, moveAt, hs]
  | up p => rw [step_of_up P L _ _ p hs]; simp [progressAt, moveAt, hs]

/-- The durable stamp is the tick after the last progress point. -/
theorem lastProgress_spec (P : Policy) (L : Limits) (env : Nat → Tick) (owner : EventPump.Key) :
    ∀ n,
      (∀ t, (run P L env (boot L owner) n).lastProgress = some t →
        1 ≤ t ∧ t ≤ n ∧ progressAt P L env (boot L owner) (t - 1) = true ∧
        ∀ i, t ≤ i → i < n → progressAt P L env (boot L owner) i = false) ∧
      ((run P L env (boot L owner) n).lastProgress = none →
        ∀ i < n, progressAt P L env (boot L owner) i = false) := by
  intro n
  induction n with
  | zero => exact ⟨fun t h => by simp [boot] at h, fun _ i hi => by omega⟩
  | succ n ih =>
    have hc : (run P L env (boot L owner) n).clock = n := by rw [run_clock]; simp [boot]
    rw [run_lastProgress, hc]
    cases hpr : progressAt P L env (boot L owner) n
    · simp only [Bool.false_eq_true, if_false]
      refine ⟨fun t ht => ?_, fun hn i hi => ?_⟩
      · obtain ⟨h1, h2, h3, h4⟩ := ih.1 t ht
        refine ⟨h1, by omega, h3, fun i hi1 hi2 => ?_⟩
        by_cases hin : i = n
        · rw [hin]; exact hpr
        · exact h4 i hi1 (by omega)
      · by_cases hin : i = n
        · rw [hin]; exact hpr
        · exact ih.2 hn i (by omega)
    · simp only [if_true, Option.some.injEq]
      refine ⟨fun t ht => ?_, fun h => by cases h⟩
      subst ht
      exact ⟨by omega, by omega, by simpa using hpr, fun i hi1 hi2 => by omega⟩

/-- **Layer (d): the report is exact.** The fixed responder says `working`
exactly when a process is running below the soft limit and the loop made
progress within the last `F` ticks. -/
theorem report_working_iff (P : Policy) (L : Limits) (env : Nat → Tick) (owner : EventPump.Key)
    (F n : Nat) :
    report F L (run P L env (boot L owner) n) = .working ↔
      (∃ p, (run P L env (boot L owner) n).life = .up p ∧ p.mem ≤ L.high) ∧
      ∃ t, t < n ∧ n ≤ t + F ∧ progressAt P L env (boot L owner) t = true := by
  have hclock : (run P L env (boot L owner) n).clock = n := by
    rw [run_clock]; simp [boot]
  have hspec := lastProgress_spec P L env owner n
  constructor
  · intro hrep
    unfold report at hrep
    cases hl : (run P L env (boot L owner) n).life with
    | down => rw [hl] at hrep; cases hrep
    | up p =>
      rw [hl] at hrep
      cases hlp : (run P L env (boot L owner) n).lastProgress with
      | none => rw [hlp] at hrep; cases hrep
      | some t₀ =>
        rw [hlp, hclock] at hrep
        simp only at hrep
        split at hrep
        · cases hrep
        · rename_i hc
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hc
          obtain ⟨h1, h2, h3, -⟩ := hspec.1 t₀ hlp
          exact ⟨⟨p, rfl, by omega⟩, t₀ - 1, by omega, by omega, h3⟩
  · rintro ⟨⟨p, hp, hmem⟩, t, ht, htF, hprog⟩
    unfold report
    rw [hp]
    cases hlp : (run P L env (boot L owner) n).lastProgress with
    | none => have := hspec.2 hlp t ht; rw [hprog] at this; cases this
    | some t₀ =>
      obtain ⟨-, -, -, h4⟩ := hspec.1 t₀ hlp
      have hlt : t < t₀ := by
        by_cases hc : t₀ ≤ t
        · have := h4 t hc ht; rw [hprog] at this; cases this
        · omega
      simp only [hclock]
      have : ¬ (L.high < p.mem ∨ F ≤ n - t₀) := by omega
      simp only [Bool.or_eq_true, decide_eq_true_eq] at *
      simp [this]

/-- **The frozen state is reported as such.** If the loop made no progress in
the last `F` ticks, or the service is above its soft limit, the fixed
responder does not say `working`. -/
theorem report_flags_freeze (P : Policy) (L : Limits) (env : Nat → Tick) (owner : EventPump.Key)
    (F n : Nat)
    (h : (∀ t, t < n → n ≤ t + F → progressAt P L env (boot L owner) t = false) ∨
      ∃ p, (run P L env (boot L owner) n).life = .up p ∧ L.high < p.mem) :
    report F L (run P L env (boot L owner) n) ≠ .working := by
  intro hw
  obtain ⟨⟨p, hp, hmem⟩, t, ht, htF, hprog⟩ := (report_working_iff P L env owner F n).mp hw
  rcases h with hnone | ⟨q, hq, hthr⟩
  · rw [hnone t ht htF] at hprog; cases hprog
  · rw [hp] at hq; cases hq; omega

/-- **The incident under both responders.** On the reconstructed freeze, the
deployed responder says `working`/`completed` while the fixed responder,
whatever its window, does not say `working`. -/
theorem incident_reports (owner : EventPump.Key) (F n : Nat) :
    deployedReport (run deployed deployedLimits (accumulation owner 41 360)
      (boot deployedLimits owner) (188 + n)) = ⟨.working, .completed⟩ ∧
    report F deployedLimits (run deployed deployedLimits (accumulation owner 41 360)
      (boot deployedLimits owner) (188 + n)) ≠ .working := by
  refine ⟨(incident_reconstruction owner n).2.2.1, report_flags_freeze _ _ _ owner F _ (Or.inr ?_)⟩
  obtain ⟨⟨r, hr⟩, -⟩ := unguarded_freezes_forever deployed deployedLimits owner 41 360 62 rfl
    deployed_has_no_backstop (by decide) (by decide) (by decide) (by decide) n
  exact ⟨_, hr, by show (3072 : Nat) < 512 + (62 + 1) * 41; decide⟩

/-! ### Without a freshness signal no responder is exact -/

/-- What a responder sees without a freshness signal: whether a process is
running, the records the loop last wrote, and the control group's memory. -/
structure StaleView where
  running : Bool
  checkpoint : HeartModel.S
  callInFlight : Bool
  mem : Nat
deriving DecidableEq

def staleView (s : State) : StaleView :=
  { running := match s.life with
      | .up _ => true
      | .down => false,
    checkpoint := s.checkpoint, callInFlight := s.callInFlight,
    mem := match s.life with
      | .up p => p.mem
      | .down => 0 }

/-- A turn of `F + 2` units whose model call returns at tick 1; from tick 2 on
its command either keeps completing units or waits. -/
def probe (F : Nat) (waiting : Bool) (n : Nat) : Tick :=
  { stall := true, work := F + 1, wait := waiting && decide (2 ≤ n) }

def probeAt (L : Limits) (owner : EventPump.Key) (left quiet clock stamp : Nat) : State :=
  { life := .up { mem := L.base, phase := .busy left, turnBase := L.base, recycle := false,
                  claimed := [] },
    inbox := { owner := owner }, processed := [], checkpoint := defaultWorkingSet,
    callInFlight := false, quiet := quiet, pressure := 0, clock := clock,
    lastProgress := some stamp, generation := 0 }

section Probe

variable (L : Limits) (owner : EventPump.Key) (F : Nat)

theorem probe_start (b : Bool) (hbH : L.base ≤ L.high) (hbM : L.base ≤ L.max) :
    run deployed L (probe F b) (boot L owner) 2 = probeAt L owner F 0 2 2 := by
  have h1 : ¬ L.high < L.base := by omega
  have h2 : ¬ L.max < L.base := by omega
  simp [run, step, killedAt, survivor, move, leaves, deployed, advance, inboxAfter, pendingIds,
    claimEach, EventPump.pending, completes, Move.progress, Move.ends, watchdogKills, overdue,
    probe, probeAt, boot, fresh, grown, defaultWorkingSet, h1, h2]

theorem probe_wait (i : Nat) (hbH : L.base ≤ L.high) :
    step deployed L (probeAt L owner F i (2 + i) 2) (probe F true (2 + i)) =
      probeAt L owner F (i + 1) (2 + i + 1) 2 := by
  have h1 : ¬ L.high < L.base := by omega
  simp [step, killedAt, survivor, move, deployed, advance, inboxAfter, completes, Move.progress,
    Move.ends, watchdogKills, overdue, probe, probeAt, h1]

theorem probe_work (k c : Nat) (hbH : L.base ≤ L.high) (hbM : L.base ≤ L.max) :
    step deployed L (probeAt L owner (k + 1) 0 c c) (probe F false c) =
      probeAt L owner k 0 (c + 1) (c + 1) := by
  have h1 : ¬ L.high < L.base := by omega
  have h2 : ¬ L.max < L.base := by omega
  simp [step, killedAt, survivor, move, deployed, advance, inboxAfter, completes, Move.progress,
    Move.ends, watchdogKills, overdue, probe, probeAt, grown, h1, h2]

theorem probe_waiting_run (hbH : L.base ≤ L.high) (hbM : L.base ≤ L.max) :
    ∀ i, run deployed L (probe F true) (boot L owner) (2 + i) = probeAt L owner F i (2 + i) 2 := by
  intro i
  induction i with
  | zero => exact probe_start L owner F true hbH hbM
  | succ i ih => rw [← Nat.add_assoc, run_succ, ih, probe_wait L owner F i hbH]

theorem probe_busy_run (hbH : L.base ≤ L.high) (hbM : L.base ≤ L.max) :
    ∀ i ≤ F, run deployed L (probe F false) (boot L owner) (2 + i) =
      probeAt L owner (F - i) 0 (2 + i) (2 + i) := by
  intro i hi
  induction i with
  | zero => exact probe_start L owner F false hbH hbM
  | succ i ih =>
    rw [← Nat.add_assoc, run_succ, ih (by omega), show F - i = F - (i + 1) + 1 by omega,
      probe_work L owner F _ _ hbH hbM]

end Probe

/-- **No responder without a freshness signal is exact.** Two reachable
executions look the same to a responder that sees only whether a process is
running, the records the loop wrote and the control group's memory: in one
the command has been waiting for `F` ticks, in the other it completed a unit
in the last tick. Any such responder misreports one of them. The deployed
responder reads only the loop's records. -/
theorem no_exact_stale_responder (F : Nat) (hF : 1 ≤ F) (L : Limits) (owner : EventPump.Key)
    (hbH : L.base ≤ L.high) (hbM : L.base ≤ L.max) (r : StaleView → Report) :
    ¬ ∀ env n, (r (staleView (run deployed L env (boot L owner) n)) = .working ↔
      (∃ p, (run deployed L env (boot L owner) n).life = .up p ∧ p.mem ≤ L.high) ∧
      ∃ t, t < n ∧ n ≤ t + F ∧ progressAt deployed L env (boot L owner) t = true) := by
  intro hexact
  have hA := probe_waiting_run L owner F hbH hbM F
  have hB := probe_busy_run L owner F hbH hbM F (Nat.le_refl _)
  have hview : staleView (run deployed L (probe F true) (boot L owner) (2 + F)) =
      staleView (run deployed L (probe F false) (boot L owner) (2 + F)) := by
    rw [hA, hB]; rfl
  have hprogB : progressAt deployed L (probe F false) (boot L owner) (2 + (F - 1)) = true := by
    have := probe_busy_run L owner F hbH hbM (F - 1) (by omega)
    rw [progressAt_of_up (by rw [this]; rfl)]
    rw [show F - (F - 1) = 0 + 1 by omega]
    have h1 : ¬ L.high < L.base := by omega
    have h2 : ¬ L.max < L.base := by omega
    simp [move, probe, grown, Move.progress, h1, h2]
  have hworkB := (hexact (probe F false) (2 + F)).mpr
    ⟨⟨_, by rw [hB]; rfl, hbH⟩, 2 + (F - 1), by omega, by omega, hprogB⟩
  obtain ⟨-, t, ht, htF, hprog⟩ := (hexact (probe F true) (2 + F)).mp (by rw [hview]; exact hworkB)
  have hwait : progressAt deployed L (probe F true) (boot L owner) (2 + (t - 2)) = false := by
    have := probe_waiting_run L owner F hbH hbM (t - 2)
    rw [progressAt_of_up (by rw [this]; rfl)]
    have h1 : ¬ L.high < L.base := by omega
    simp [move, probe, Move.progress, h1]
  rw [show 2 + (t - 2) = t by omega, hprog] at hwait
  cases hwait

/-! ## Relation to the loop models

`ClawArchitectures`, `HeartModel` and `FuelPolicy` count their guarantees in
wakes. The heartbeat renews a full burst within `H` wakes
(`Claws.starvation_bounded`), a breath spends at most the budget it holds
(`HeartModel.bounded_spend`), and no renewal discipline starves
(`FuelPolicy.refuel_never_starves`). A wake is a boundary pass here, so these
guarantees hold in wall time only while passes keep coming. -/

/-- **A freeze stops every wake-counted clock.** After the accumulation freeze
no boundary pass ever happens again, so no wake-counted guarantee
(heartbeat renewal, recycle, fuel renewal) is ever discharged. -/
theorem freeze_stops_wakes (P : Policy) (L : Limits) (owner : EventPump.Key) (g R k : Nat)
    (hthr : P.threshold = none) (hP : NoIndependentBackstop P)
    (hk : L.base + k * g ≤ L.high) (hk' : L.high < L.base + (k + 1) * g)
    (hM : L.base + (k + 1) * g ≤ L.max) (hR : 3 * k + 2 < R) (n : Nat) :
    moveAt P L (accumulation owner g R) (boot L owner) (3 * k + 2 + n) ≠ some .passed := by
  rw [(unguarded_freezes_forever P L owner g R k hthr hP hk hk' hM hR n).2.1]
  simp

theorem nominal_pass_from_boundary {P : Policy} {L : Limits} {env : Nat → Tick}
    {owner : EventPump.Key} {T g W w : Nat} (h : Nominal P L env T g W w) (n : Nat)
    (hb : (run P L env (boot L owner) n).life = .down ∨
      ∃ p, (run P L env (boot L owner) n).life = .up p ∧ p.phase = .boundary) :
    ∃ m, n ≤ m ∧ m ≤ n + 2 ∧ moveAt P L env (boot L owner) m = some .passed := by
  have hfresh : leaves P (fresh L) = false :=
    leaves_fresh P L (fun T' hT' => by rw [h.threshold] at hT'; cases hT'; exact h.freshBelow)
  have hbH : L.base ≤ L.high := by have := h.room; have := h.freshBelow; omega
  have from_down : ∀ n', (run P L env (boot L owner) n').life = .down →
      moveAt P L env (boot L owner) (n' + 1) = some .passed := by
    intro n' hd
    simp only [moveAt, (restart_tick P L env (boot L owner) n' hd).1]
    rw [fresh_passes P L _ hbH hfresh]
  rcases hb with hd | ⟨p, hp, hbd⟩
  · exact ⟨n + 1, by omega, by omega, from_down n hd⟩
  · cases hl : leaves P p
    · refine ⟨n, Nat.le_refl _, by omega, ?_⟩
      simp only [moveAt, hp]
      rw [move_of_not_withheld (not_withheld_of h n p hp), hbd]
      simp [hl]
    · exact ⟨n + 2, by omega, by omega, from_down (n + 1) (nominal_exit h n p hp hbd hl).1⟩

/-- **Under the fix, wakes recur in wall time.** Under the nominal
assumptions a boundary pass happens at least every `(W + 1)(w + 1) + 2` ticks.
Every wake-counted guarantee of the loop models becomes a wall-clock one. -/
theorem nominal_wakes_recur {P : Policy} {L : Limits} {env : Nat → Tick}
    {owner : EventPump.Key} {T g W w : Nat} (h : Nominal P L env T g W w) (n : Nat) :
    ∃ m, n ≤ m ∧ m ≤ n + (W + 1) * (w + 1) + 2 ∧
      moveAt P L env (boot L owner) m = some .passed := by
  cases hl : (run P L env (boot L owner) n).life with
  | down =>
    obtain ⟨m, h1, h2, h3⟩ := nominal_pass_from_boundary h n (Or.inl hl)
    exact ⟨m, h1, by omega, h3⟩
  | up p =>
    cases hph : p.phase with
    | boundary =>
      obtain ⟨m, h1, h2, h3⟩ := nominal_pass_from_boundary h n (Or.inr ⟨p, hl, hph⟩)
      exact ⟨m, h1, by omega, h3⟩
    | busy k =>
      obtain ⟨m₁, h1, h2, p₁, hp₁, hb₁, -, -⟩ := nominal_turn_completes h k n p hl hph
      obtain ⟨m, h3, h4, h5⟩ := nominal_pass_from_boundary h m₁ (Or.inr ⟨p₁, hp₁, hb₁⟩)
      have hk := shortTurn_invariant P L env owner W (fun n => (h.work n).2) n p hl k hph
      have : (k + 1) * (w + 1) ≤ (W + 1) * (w + 1) := Nat.mul_le_mul_right _ (by omega)
      exact ⟨m, by omega, by omega, h5⟩

/-- A kill in the middle of a provider call is a recovery in `AsyncWait`'s
sense: the call becomes `interruptedUnknown`, the restarted process cannot
adopt it, and the slot it owns is not free for a blind resubmission. -/
theorem kill_mid_call_is_recovery (call : AsyncWait.Call) (revision : Nat)
    (hsent : call.sent = true) (hpend : call.terminal = none) :
    (AsyncWait.recover call).terminal = some .interruptedUnknown ∧
    AsyncWait.adopt (AsyncWait.recover call) revision = AsyncWait.recover call ∧
    AsyncWait.canSubmit (some (AsyncWait.recover call)) = false :=
  ⟨AsyncWait.recovery_records_uncertainty call hsent hpend,
   AsyncWait.recovered_call_cannot_act call revision hsent hpend, rfl⟩

/-! ## The fix on the incident's workload -/

/-- The fixed policy for the deployed limits: leave at a boundary above
2990 MiB, and kill after more than `D` throttled ticks or `D` ticks without
progress. -/
def fixedPolicy (D : Nat) : Policy :=
  { threshold := some 2990, throttleDeadline := some D, progressDeadline := some D }

theorem fixed_nominal_on_incident (owner : EventPump.Key) (D : Nat) :
    Nominal (fixedPolicy D) deployedLimits (accumulation owner 41 360) 2990 41 1 0 where
  threshold := rfl
  freshBelow := by decide
  room := by decide
  hardAbove := by decide
  work := fun n => ⟨by simp only [accumulation]; split <;> omega, by simp [accumulation]⟩
  waits := fun n => ⟨0, Nat.le_refl _, rfl⟩
  deadline := fun D' hD' => Nat.zero_le _
  noExternal := fun _ => rfl

/-- **The fix resolves the incident.** On the workload that froze the deployed
policy, the fixed policy never enters the throttled regime, its only deaths
are boundary recycles, and every input is processed within seven ticks of
reaching the journal. -/
theorem fixed_resolves_incident (owner : EventPump.Key) (D n : Nat) :
    (∀ p, (run (fixedPolicy D) deployedLimits (accumulation owner 41 360)
      (boot deployedLimits owner) n).life = .up p → p.mem ≤ 3072) ∧
    (∀ ev ∈ (run (fixedPolicy D) deployedLimits (accumulation owner 41 360)
      (boot deployedLimits owner) n).inbox.journal,
      ∃ m, n ≤ m ∧ m ≤ n + 7 ∧ ev.serial ∈ (run (fixedPolicy D) deployedLimits
        (accumulation owner 41 360) (boot deployedLimits owner) m).processed) ∧
    (∀ p, (run (fixedPolicy D) deployedLimits (accumulation owner 41 360)
      (boot deployedLimits owner) n).life = .up p →
      (run (fixedPolicy D) deployedLimits (accumulation owner 41 360)
        (boot deployedLimits owner) (n + 1)).life = .down →
      p.phase = .boundary) := by
  have h := fixed_nominal_on_incident owner D
  refine ⟨fun p hp => nominal_mem h n p hp, fun ev hev => ?_, fun p hp hd =>
    (nominal_deaths_are_exits h n p hp hd).2⟩
  obtain ⟨m, h1, h2, h3⟩ := every_input_processed h n ev hev
  exact ⟨m, h1, by omega, h3⟩

end ProcessSupervision

/-! ## Axiom audit (kernel-level trust check) -/
#print axioms ProcessSupervision.freeze_is_absorbing
#print axioms ProcessSupervision.unguarded_freezes_forever
#print axioms ProcessSupervision.unguarded_recycle_starves
#print axioms ProcessSupervision.unguarded_inputs_wait_forever
#print axioms ProcessSupervision.unguarded_status_while_frozen
#print axioms ProcessSupervision.incident_reconstruction
#print axioms ProcessSupervision.session_killer_silent_forever
#print axioms ProcessSupervision.session_killer_delay_unbounded
#print axioms ProcessSupervision.graceful_never_throttles
#print axioms ProcessSupervision.graceful_fires_at_boundary
#print axioms ProcessSupervision.turn_growth_of_rate
#print axioms ProcessSupervision.graceful_bound_sharp
#print axioms ProcessSupervision.runaway_freezes_without_backstop
#print axioms ProcessSupervision.backstop_bounds_silence
#print axioms ProcessSupervision.backstop_bounds_throttling
#print axioms ProcessSupervision.backstop_restores_progress
#print axioms ProcessSupervision.throttle_sharing_watchdog_freezes
#print axioms ProcessSupervision.unwithholdable_path_completes
#print axioms ProcessSupervision.completedSteps_prefix
#print axioms ProcessSupervision.withholdable_path_can_stall
#print axioms ProcessSupervision.external_watchdog_kills
#print axioms ProcessSupervision.interpreter_thread_can_stall
#print axioms ProcessSupervision.faulting_thread_can_stall
#print axioms ProcessSupervision.catchable_kill_can_stall
#print axioms ProcessSupervision.locked_thread_kills
#print axioms ProcessSupervision.heartbeat_feed_never_fires
#print axioms ProcessSupervision.progress_feed_fires
#print axioms ProcessSupervision.accounted_invariant
#print axioms ProcessSupervision.no_input_lost
#print axioms ProcessSupervision.early_acknowledgement_loses
#print axioms ProcessSupervision.late_acknowledgement_requeues
#print axioms ProcessSupervision.presentation_mark_loses_killed_turn
#print axioms ProcessSupervision.checkpoint_mark_represents
#print axioms ProcessSupervision.upstream_ack_first_loses
#print axioms ProcessSupervision.journal_first_survives
#print axioms ProcessSupervision.nominal_alive
#print axioms ProcessSupervision.nominal_turn_completes
#print axioms ProcessSupervision.nominal_claims
#print axioms ProcessSupervision.every_input_processed
#print axioms ProcessSupervision.nominal_deaths_are_exits
#print axioms ProcessSupervision.session_killer_silent_under_graceful
#print axioms ProcessSupervision.unbounded_wait_never_processes
#print axioms ProcessSupervision.poison_never_processed
#print axioms ProcessSupervision.poison_is_journalled
#print axioms ProcessSupervision.short_deadline_kills_waiting
#print axioms ProcessSupervision.threshold_below_fresh_livelocks
#print axioms ProcessSupervision.external_kills_starve
#print axioms ProcessSupervision.hard_limit_below_room_kills
#print axioms ProcessSupervision.report_working_iff
#print axioms ProcessSupervision.report_flags_freeze
#print axioms ProcessSupervision.incident_reports
#print axioms ProcessSupervision.no_exact_stale_responder
#print axioms ProcessSupervision.freeze_stops_wakes
#print axioms ProcessSupervision.nominal_wakes_recur
#print axioms ProcessSupervision.kill_mid_call_is_recovery
#print axioms ProcessSupervision.fixed_resolves_incident
