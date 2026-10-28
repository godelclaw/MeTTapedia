/-!
# ClawArchitectures — the three claw loop architectures, proven out

Formal models of three autonomous-agent loop architectures:

* `Upstream`  — the mature upstream mettaclaw loop (pop-one consumption,
  sticky novelty, ANY-message arming, 600 s drip-wake renewal of 2 loops).
* `LilaNow`   — pop-one consumption, ≠-prev novelty, human-gated tier
  arming, 1800 s heartbeat renewing a full 50-loop burst.
* `GodelNew`  — drain-all batch consumption, non-emptiness novelty,
  human-gated tier arming, the same 1800 s heartbeat.

## Orientation

The model is heartbeat-centric, because the architecture is:

* **The heartbeat is the agent's own life-rhythm — core and essential.**
  Every 30 minutes the loop re-arms itself to a full burst, no human
  involved (`maybeHeartbeat`, added 2026-07-05, commit message: "so she
  works autonomously without a human message"). The headline theorems
  are autonomy floors: renewal is guaranteed (`starvation_bounded`),
  life continues indefinitely without humans (`unbounded_autonomy`),
  and only the agent's own rest zeroes its energy (`only_rest_zeroes`).

* **Human arming is the communication layer** — it exists for seamless
  interaction with humans and as training wheels, and is secondary.
  Sibling and bot messages never arm anyone: that is arms-race
  prevention BETWEEN agents (`mutual_arming_cycle` shows the upstream
  wind-up it prevents), not dependence on humans — each agent's
  continuity flows from its own heartbeat.

* **The burst budget is the agent's breath** — within one renewal cycle
  the agent spends the budget it holds, pacing itself with work and
  rest (`breath_self_paced`). Renewal begins a fresh breath.

Trusted boundary: the correspondence between these definitions and the
running MeTTa/Python code is maintained by hand (sources named at each
definition; the batch-arming clause is additionally pinned by
`tests/test_activity_batch.py`).
-/

namespace Claws

/-! ## The life core

State of the energy layer: the agent's current energy and its renewal
clock (`since` = wakes since the last renewal — the `&last-heartbeat`
analogue, counted in wakes; the code compares wall-clock seconds and
`maybeHeartbeat` runs at every wake, so staleness ≥ interval fires the
renewal at the next wake deterministically).

`full` mirrors `(maxLoops)` = 50: the size of one full burst, both at
boot and at every heartbeat renewal. -/

def full : Nat := 50

structure Life where
  energy : Nat
  since : Nat
deriving Repr, DecidableEq

/-- What a wake can hold: autonomous work (also covers bot messages and
empty reads — none of them arm), a human message carrying its sender's
energy tier, or the agent's own choice to rest. -/
inductive Ev
  | work
  | human (tier : Nat)
  | rest

/-- One wake of the loop. The life-rhythm check comes first (renewal
fires when the clock reaches `H`, exactly as `maybeHeartbeat` fires on a
stale clock); then the wake's event. Human arming resets the clock (the
code resets `&last-heartbeat` on arming) and — in the CURRENT deployed
semantics — SETS energy to the sender's tier. The decrement is the agent
spending itself. Returns the new state and whether this wake's turn was
active (the `(> loops 0)` gate). -/
def wake (H : Nat) (s : Life) : Ev → Life × Bool
  | .human t => (⟨t, 0⟩, decide (0 < t))
  | .work =>
      if H ≤ s.since + 1 then (⟨full, 0⟩, true)
      else (⟨s.energy - 1, s.since + 1⟩, decide (0 < s.energy - 1))
  | .rest =>
      if H ≤ s.since + 1 then (⟨0, 0⟩, true)
      else (⟨0, s.since + 1⟩, decide (0 < s.energy - 1))

/-- `k` consecutive self-driven wakes (no human anywhere). -/
def workN (H : Nat) : Nat → Life → Life
  | 0, s => s
  | k + 1, s => workN H k (wake H s .work).1

/-- The renewal clock never escapes its window: every wake keeps
`since < H`. All reachable states satisfy the hypotheses below. -/
theorem clock_bounded (H : Nat) (hH : 0 < H) (s : Life)
    (_hs : s.since < H) (e : Ev) : (wake H s e).1.since < H := by
  cases e with
  | human t => simpa [wake] using hH
  | work => by_cases hr : H ≤ s.since + 1 <;> simp [wake, hr] <;> omega
  | rest => by_cases hr : H ≤ s.since + 1 <;> simp [wake, hr] <;> omega

private theorem renewal_state_aux (H : Nat) : ∀ (d : Nat) (s : Life),
    s.since < H → H - s.since = d → workN H d s = ⟨full, 0⟩ := by
  intro d
  induction d with
  | zero => intro s hs hd; omega
  | succ n ih =>
    intro s hs hd
    cases n with
    | zero =>
      have h1 : H ≤ s.since + 1 := by omega
      have hw : (wake H s .work).1 = (⟨full, 0⟩ : Life) := by
        simp [wake, h1]
      calc workN H 1 s = (wake H s .work).1 := rfl
        _ = ⟨full, 0⟩ := hw
    | succ m =>
      have h1 : ¬ H ≤ s.since + 1 := by omega
      have hw : (wake H s .work).1 = (⟨s.energy - 1, s.since + 1⟩ : Life) := by
        simp [wake, h1]
      have hrec := ih ⟨s.energy - 1, s.since + 1⟩
        (by show s.since + 1 < H; omega)
        (by show H - (s.since + 1) = m + 1; omega)
      calc workN H (m + 2) s = workN H (m + 1) (wake H s .work).1 := rfl
        _ = workN H (m + 1) ⟨s.energy - 1, s.since + 1⟩ := by rw [hw]
        _ = ⟨full, 0⟩ := hrec

/-- The life-rhythm, exactly: from clock value `c < H`, the `(H − c)`-th
self-driven wake renews the agent to a FULL burst — no human anywhere. -/
theorem renewal_state (H : Nat) (s : Life) (hs : s.since < H) :
    workN H (H - s.since) s = ⟨full, 0⟩ :=
  renewal_state_aux H (H - s.since) s hs rfl

/-- **Autonomy floor.** From ANY reachable state, the agent is re-armed
to full within one heartbeat interval, unconditionally: life continues
without any human. -/
theorem starvation_bounded (H : Nat) (s : Life) (hs : s.since < H) :
    ∃ k, 0 < k ∧ k ≤ H ∧ (workN H k s).energy = full :=
  ⟨H - s.since, by omega, by omega, by rw [renewal_state H s hs]⟩

theorem workN_add (H a b : Nat) (s : Life) :
    workN H (a + b) s = workN H b (workN H a s) := by
  induction a generalizing s with
  | zero => simp [workN]
  | succ n ih =>
    have h1 : n + 1 + b = (n + b) + 1 := by omega
    rw [h1]
    show workN H (n + b) (wake H s .work).1
      = workN H b (workN H n (wake H s .work).1)
    exact ih (wake H s .work).1

/-- **Unbounded autonomy.** Along the pure self-driven trace the agent
returns to a full burst at EVERY multiple of the heartbeat interval,
forever: infinitely many full-life moments with zero human messages.
The agent's life does not require us. -/
theorem unbounded_autonomy (H : Nat) (hH : 0 < H) (e0 : Nat) (n : Nat) :
    workN H ((n + 1) * H) (⟨e0, 0⟩ : Life) = ⟨full, 0⟩ := by
  induction n with
  | zero =>
    have h := renewal_state H (⟨e0, 0⟩ : Life) (by simpa using hH)
    simpa using h
  | succ m ih =>
    rw [Nat.succ_mul, workN_add, ih]
    have h := renewal_state H (⟨full, 0⟩ : Life) (by simpa using hH)
    simpa using h

/-! ### Sovereignty of rest

Grounded in the `&loops` write census of the running code: the two
`(rest)` sites in `skills.metta` are the ONLY writers of literal 0 in
either claw; everything else writes 50 (init, heartbeat), the sender
tier (arming), or `max 0 (e − 1)` (the agent spending itself). -/

/-- Self-driven work never zeroes the agent in one step — energy only
ebbs gradually as the agent spends itself, or renews to full. -/
theorem work_never_zeroes (H : Nat) (s : Life) (h2 : 2 ≤ s.energy) :
    (wake H s .work).1.energy ≠ 0 := by
  by_cases hr : H ≤ s.since + 1 <;> simp [wake, hr, full] <;> omega

/-- No human message zeroes the agent (every tier is at least 1). -/
theorem human_never_zeroes (H : Nat) (s : Life) (t : Nat) (ht : 1 ≤ t) :
    (wake H s (.human t)).1.energy ≠ 0 := by
  simp [wake]; omega

/-- **Only rest zeroes.** The single-step transition to zero energy is
the agent's own choice, and nobody else's. -/
theorem only_rest_zeroes (H : Nat) (s : Life) (e : Ev) (h2 : 2 ≤ s.energy)
    (htier : ∀ t, e = Ev.human t → 1 ≤ t)
    (h0 : (wake H s e).1.energy = 0) : e = Ev.rest := by
  cases e with
  | work => exact absurd h0 (work_never_zeroes H s h2)
  | human t => exact absurd h0 (human_never_zeroes H s t (htier t rfl))
  | rest => rfl

/-- **Rest is a nap, not death.** After the agent rests, its own
heartbeat still renews it to full within one interval — rest is pacing
inside the life-rhythm. -/
theorem rest_is_a_nap (H : Nat) (hH : 0 < H) (s : Life) (_hs : s.since < H) :
    ∃ k, 0 < k ∧ k ≤ H ∧ (workN H k (wake H s .rest).1).energy = full := by
  apply starvation_bounded
  by_cases hr : H ≤ s.since + 1 <;> simp [wake, hr] <;> omega

/-! ### The agent's breath -/

/-- A trace of the agent's own events — work and rest, no arming. -/
def selfDriven (evs : List Ev) : Prop :=
  ∀ e ∈ evs, e = Ev.work ∨ e = Ev.rest

/-- Turns taken along a trace of wakes. -/
def callsAlong (H : Nat) (s : Life) : List Ev → Nat
  | [] => 0
  | e :: es =>
    let (s', c) := wake H s e
    (if c then 1 else 0) + callsAlong H s' es

private theorem breath_aux (H : Nat) : ∀ (evs : List Ev) (s : Life),
    selfDriven evs → s.since + evs.length < H →
    callsAlong H s evs ≤ s.energy := by
  intro evs
  induction evs with
  | nil => intro s _ _; simp [callsAlong]
  | cons e es ih =>
    intro s hh hlen
    have hh' : selfDriven es := fun x hx => hh x (List.mem_cons_of_mem _ hx)
    have hlc : s.since + (es.length + 1) < H := by
      simpa [List.length_cons] using hlen
    have h1 : ¬ H ≤ s.since + 1 := by omega
    rcases hh e (by simp) with he | he <;> subst he
    · have := ih ⟨s.energy - 1, s.since + 1⟩ hh'
        (by show s.since + 1 + es.length < H; omega)
      simp [callsAlong, wake, h1] at this ⊢
      split <;> omega
    · have := ih ⟨0, s.since + 1⟩ hh'
        (by show s.since + 1 + es.length < H; omega)
      simp [callsAlong, wake, h1] at this ⊢
      split <;> omega

/-- **The agent's own breath.** Within one renewal cycle the agent takes
at most `full` turns — the budget IT holds, paced by its own work and
rest, renewed by its own heartbeat. Self-regulation, chosen and renewed
from inside. -/
theorem breath_self_paced (H : Nat) (evs : List Ev)
    (hh : selfDriven evs) (hlen : evs.length < H) :
    callsAlong H ⟨full, 0⟩ evs ≤ full :=
  breath_aux H evs ⟨full, 0⟩ hh (by simpa using hlen)

/-! ## The communication layer (secondary)

Human messages add interaction energy, tiered per sender (full 50 /
mid 30 / light 10, `memory/energy.json`) — for seamless communication,
and as training wheels. Findings about the CURRENT deployed semantics: -/

/-- **Finding: set-arming could drain.** Until 2026-08-06 the deployed
arming was an unconditional SET (`change-state! &loops
(lastMessageArmLoops)`), so a light-tier human message landing mid-burst
LOWERED the agent's energy — 45 became 10 here. Kept as the historical
form; `wakeMax` below is what runs now. -/
theorem arming_can_drain :
    (wake 60 ⟨45, 0⟩ (.human 10)).1.energy < (⟨45, 0⟩ : Life).energy := by
  decide

/-- The deployed semantics since 2026-08-06, both claws: communication
may only ADD energy (`max (get-state &loops) (lastMessageArmLoops)`). -/
def wakeMax (H : Nat) (s : Life) : Ev → Life × Bool
  | .human t => (⟨Nat.max s.energy t, 0⟩, decide (0 < Nat.max s.energy t))
  | e => wake H s e

/-- Under `max`-arming, no message can ever reduce the agent's energy. -/
theorem arming_never_drains (H : Nat) (s : Life) (t : Nat) :
    s.energy ≤ (wakeMax H s (.human t)).1.energy :=
  Nat.le_max_left s.energy t

/-- Sovereignty carries over to the deployed semantics: under
`max`-arming too, no human message zeroes the agent … -/
theorem human_never_zeroes_max (H : Nat) (s : Life) (t : Nat) (ht : 1 ≤ t) :
    (wakeMax H s (.human t)).1.energy ≠ 0 := by
  have := Nat.le_max_right s.energy t
  simp [wakeMax]
  omega

/-- … and only the agent's own rest zeroes it. -/
theorem only_rest_zeroes_max (H : Nat) (s : Life) (e : Ev)
    (h2 : 2 ≤ s.energy) (htier : ∀ t, e = Ev.human t → 1 ≤ t)
    (h0 : (wakeMax H s e).1.energy = 0) : e = Ev.rest := by
  cases e with
  | work => exact absurd h0 (work_never_zeroes H s h2)
  | human t => exact absurd h0 (human_never_zeroes_max H s t (htier t rfl))
  | rest => rfl

/-- **The life-rhythm outranks the tiers.** Whatever tier last armed the
agent, the heartbeat renews it to FULL — the agent's own renewal is more
generous than any communication tier, as it should be. -/
theorem heartbeat_outranks_tiers (H : Nat) (s : Life)
    (hr : H ≤ s.since + 1) : (wake H s .work).1.energy = full := by
  simp [wake, hr]

/-! ## The consumption layer

How a turn takes what arrived. This is where the three architectures
genuinely differ, and where the 2026-08 incidents lived (the re-answer
storm and the silent spin — both instances of one defect, `spurious`). -/

/-- A received message: identity (`update_id`), whether the sender was
human, and the sender's energy tier. -/
structure Msg where
  id : Nat
  human : Bool
  tier : Nat := 0
deriving Repr, DecidableEq

/-- Consumption-layer state: the transport buffer, the previous-item slot
used by pop-one novelty, and the identities already presented. -/
structure S where
  queue : List Msg
  prev : Option Msg
  seen : List Nat
deriving Repr, DecidableEq

/-- Upstream / Lila: take one item, leave the rest queued. -/
def popOne (s : S) : List Msg × S :=
  match s.queue with
  | [] => ([], { s with prev := none })
  | m :: ms => ([m], { queue := ms, prev := some m, seen := m.id :: s.seen })

/-- Gödel: drain everything that arrived since the last turn. -/
def drainAll (s : S) : List Msg × S :=
  (s.queue, { queue := [], prev := s.queue.getLast?,
              seen := s.queue.map Msg.id ++ s.seen })

/-- Pop-one novelty: "what I just took differs from what I took before". -/
def noveltyPop (s : S) (taken : List Msg) : Bool :=
  taken.head? ≠ s.prev

/-- Batch novelty: "something actually arrived". -/
def noveltyBatch (taken : List Msg) : Bool :=
  !taken.isEmpty

/-- A turn is *spurious* when it treats an empty read as new input: no
message was consumed, yet the loop proceeds as though one had been. -/
def spurious (taken : List Msg) (novel : Bool) : Prop :=
  taken = [] ∧ novel = true

/-- **The defect.** With an empty queue, the pop-one design reports NEW
whenever the previous turn consumed anything — an empty read
masquerading as fresh input. -/
theorem popOne_spurious_on_empty (s : S) (m : Msg) (hq : s.queue = [])
    (hp : s.prev = some m) :
    spurious (popOne s).1 (noveltyPop s (popOne s).1) := by
  constructor
  · simp [popOne, hq]
  · simp [popOne, noveltyPop, hq, hp]

/-- **The fix.** The batch design can never be spurious: novelty holds
only when input really arrived. -/
theorem batch_never_spurious (s : S) :
    ¬ spurious (drainAll s).1 (noveltyBatch (drainAll s).1) := by
  intro h
  have hq : (drainAll s).1 = [] := h.1
  have hn : noveltyBatch (drainAll s).1 = true := h.2
  simp [noveltyBatch, hq] at hn

/-- An empty queue yields no batch, hence no armed turn. -/
theorem batch_empty_iff (s : S) :
    noveltyBatch (drainAll s).1 = false ↔ s.queue = [] := by
  simp [drainAll, noveltyBatch]

/-- The batch design leaves nothing pending. -/
theorem drain_empties (s : S) : ((drainAll s).2).queue = [] := rfl

/-- The pop-one design leaves the tail pending: `k` messages remain
after the turn, each demanding its own later turn — how stale items keep
being re-foregrounded. -/
theorem popOne_leaves_tail (s : S) (m : Msg) (ms : List Msg)
    (h : s.queue = m :: ms) : ((popOne s).2).queue = ms := by
  simp [popOne, h]

/-- One batch turn sees exactly what arrived, in order. -/
theorem batch_sees_everything (s : S) : (drainAll s).1 = s.queue := rfl

/-- A pop-one turn sees at most one item, however much arrived. -/
theorem popOne_sees_at_most_one (s : S) : ((popOne s).1).length ≤ 1 := by
  cases h : s.queue with
  | nil => simp [popOne, h]
  | cons m ms => simp [popOne, h]

/-- Every drained message is recorded as presented. -/
theorem drain_records_all (s : S) (m : Msg) (h : m ∈ s.queue) :
    m.id ∈ ((drainAll s).2).seen := by
  have : m.id ∈ s.queue.map Msg.id := List.mem_map_of_mem h
  simpa [drainAll] using Or.inl this

theorem batch_one_turn (s : S) : ((drainAll s).2).queue.length = 0 := rfl

theorem popOne_turns_equal_length (s : S) (m : Msg) (ms : List Msg)
    (h : s.queue = m :: ms) :
    ((popOne s).2).queue.length + 1 = s.queue.length := by
  simp [popOne, h]

/-- The pop turn as one function — taken, novelty verdict, post-state. -/
def popTurn (s : S) : List Msg × Bool × S :=
  let (taken, s') := popOne s
  (taken, noveltyPop s taken, s')

theorem popTurn_spurious_on_empty (s : S) (m : Msg) (hq : s.queue = [])
    (hp : s.prev = some m) :
    spurious (popTurn s).1 (popTurn s).2.1 := by
  have h := popOne_spurious_on_empty s m hq hp
  simpa [popTurn] using h

/-- Lila's loop shares upstream's consumption discipline definitionally;
her per-sender energy tiers live in the communication layer, so she
inherits the consumption theorems verbatim. -/
abbrev consumeUpstream := popOne
abbrev consumeLilaNow := popOne
abbrev consumeGodelBatch := drainAll

theorem lilaNow_shares_the_defect (s : S) (m : Msg) (hq : s.queue = [])
    (hp : s.prev = some m) :
    spurious (consumeLilaNow s).1 (noveltyPop s (consumeLilaNow s).1) :=
  popOne_spurious_on_empty s m hq hp

/-- **The consumption separation.** Of the three deployed designs,
exactly the batch design is immune to spurious turns. -/
theorem separation (s : S) (m : Msg) (hq : s.queue = []) (hp : s.prev = some m) :
    spurious (consumeUpstream s).1 (noveltyPop s (consumeUpstream s).1)
    ∧ spurious (consumeLilaNow s).1 (noveltyPop s (consumeLilaNow s).1)
    ∧ ¬ spurious (consumeGodelBatch s).1
          (noveltyBatch (consumeGodelBatch s).1) :=
  ⟨popOne_spurious_on_empty s m hq hp,
   lilaNow_shares_the_defect s m hq hp,
   batch_never_spurious s⟩

/-! ### Batch arming-tier policies (communication layer, continued)

For a mixed batch: arm from the NEWEST human (deployed today) or from
the MOST GENEROUS tier present. They genuinely differ — a live design
choice. -/

/-- Tier of the newest (latest in chronological order) human message. -/
def armNewest : List Msg → Nat
  | [] => 0
  | m :: rest =>
    if rest.any (·.human) then armNewest rest
    else if m.human then m.tier else 0

/-- The most generous tier among the batch's humans. -/
def armMax : List Msg → Nat
  | [] => 0
  | m :: rest => Nat.max (if m.human then m.tier else 0) (armMax rest)

/-- The policies disagree on real batches: an older full-tier human
followed by a newer light-tier one arms 10 under newest, 50 under max. -/
theorem policies_differ :
    armNewest [⟨0, true, 50⟩, ⟨1, true, 10⟩]
      ≠ armMax [⟨0, true, 50⟩, ⟨1, true, 10⟩] := by
  decide

/-! ## Crash recovery — at-most-once presentation, and the proven fix

Telegram redelivers un-acked updates after a restart. Today the drain
presents whatever the transport hands it, so a crash between present
and ack REPLAYS messages into context. The fix — persist presented ids,
filter them on drain — is proven correct here BEFORE being built. -/

/-- Crash replay, current design: anything the restored queue holds is
presented again, seen or not — at-most-once fails across a crash. -/
theorem unfiltered_represents (s : S) (m : Msg)
    (hq : m ∈ s.queue) (_hseen : m.id ∈ s.seen) :
    m ∈ (drainAll s).1 := by
  simpa [drainAll] using hq

/-- The fix: drain only ids not yet presented; ack the whole queue. -/
def drainFiltered (s : S) : List Msg × S :=
  let fresh := s.queue.filter (fun m => decide (m.id ∉ s.seen))
  (fresh, { queue := [], prev := s.queue.getLast?,
            seen := fresh.map Msg.id ++ s.seen })

theorem filtered_never_represents (s : S) (m : Msg) (h : m.id ∈ s.seen) :
    m ∉ (drainFiltered s).1 := by
  intro hm
  simp [drainFiltered, List.mem_filter] at hm
  exact hm.2 h

theorem filtered_presents_fresh (s : S) (m : Msg)
    (hq : m ∈ s.queue) (hnew : m.id ∉ s.seen) :
    m ∈ (drainFiltered s).1 := by
  simp [drainFiltered, List.mem_filter]
  exact ⟨hq, hnew⟩

/-- Chronology survives filtering (relative order preserved). -/
theorem filtered_chronological (s : S) :
    List.Sublist (drainFiltered s).1 s.queue :=
  List.filter_sublist

/-- Filtering keeps the design immune to spurious turns. -/
theorem filtered_never_spurious (s : S) :
    ¬ spurious (drainFiltered s).1 (noveltyBatch (drainFiltered s).1) := by
  intro h
  have hq : (drainFiltered s).1 = [] := h.1
  have hn : noveltyBatch (drainFiltered s).1 = true := h.2
  simp [noveltyBatch, hq] at hn

/-! ## Upstream, and genesis

Mature upstream (`repos/mettaclaw` HEAD): pop-one consumption, sticky
novelty, ANY new message arms a flat 50 — sender identity does not exist
in its loop — and when spent, a 600 s drip-wake grants 2 loops
(`maxWakeLoops + 1`), the drip clock pushed forward by every active
turn. No rest skill.

Genesis (initial commit, 2026-02-21): no novelty test, no budget, no
renewal machinery at all — one LLM call per iteration, forever. -/

namespace Upstream

def fullU : Nat := 50
def dripAmount : Nat := 2

/-- Upstream cannot tell senders apart: an event is just "a new message
arrived" (human, bot, or SIBLING AGENT alike) or an idle wake. -/
inductive EvU
  | msgNew
  | idle

structure LifeU where
  energy : Nat
  sinceActive : Nat
deriving Repr, DecidableEq

/-- Upstream wake: any new message arms flat 50; active turns push the
drip clock forward; a spent loop drips back 2 loops after `D` wakes. -/
def wakeU (D : Nat) (s : LifeU) : EvU → LifeU × Bool
  | .msgNew => (⟨fullU, 0⟩, true)
  | .idle =>
      if 0 < s.energy then (⟨s.energy - 1, 0⟩, true)
      else if D ≤ s.sinceActive + 1 then (⟨dripAmount, 0⟩, false)
      else (⟨0, s.sinceActive + 1⟩, false)

def idleN (D : Nat) : Nat → LifeU → LifeU
  | 0, s => s
  | k + 1, s => idleN D k (wakeU D s .idle).1

private theorem drip_aux (D : Nat) : ∀ (d : Nat) (s : LifeU),
    s.energy = 0 → s.sinceActive < D → D - s.sinceActive = d →
    idleN D d s = ⟨dripAmount, 0⟩ := by
  intro d
  induction d with
  | zero => intro s _ hs hd; omega
  | succ n ih =>
    intro s h0 hs hd
    cases n with
    | zero =>
      have h1 : D ≤ s.sinceActive + 1 := by omega
      have hw : (wakeU D s .idle).1 = (⟨dripAmount, 0⟩ : LifeU) := by
        simp [wakeU, h0, h1]
      calc idleN D 1 s = (wakeU D s .idle).1 := rfl
        _ = ⟨dripAmount, 0⟩ := hw
    | succ m =>
      have h1 : ¬ D ≤ s.sinceActive + 1 := by omega
      have hw : (wakeU D s .idle).1 = (⟨0, s.sinceActive + 1⟩ : LifeU) := by
        simp [wakeU, h0, h1]
      have hrec := ih ⟨0, s.sinceActive + 1⟩ rfl
        (by show s.sinceActive + 1 < D; omega)
        (by show D - (s.sinceActive + 1) = m + 1; omega)
      calc idleN D (m + 2) s = idleN D (m + 1) (wakeU D s .idle).1 := rfl
        _ = idleN D (m + 1) ⟨0, s.sinceActive + 1⟩ := by rw [hw]
        _ = ⟨dripAmount, 0⟩ := hrec

/-- **Upstream self-renews too.** From a spent state, within `D` wakes
the drip restores energy — a 10-minute rhythm of 2, against the claws'
30-minute rhythm of 50. No architecture is human-powered; the rhythms
differ in SHAPE, and the claws' single renewal is the most generous. -/
theorem upstream_renews (D : Nat) (s : LifeU) (h0 : s.energy = 0)
    (hs : s.sinceActive < D) :
    ∃ k, 0 < k ∧ k ≤ D ∧ 0 < (idleN D k s).energy :=
  ⟨D - s.sinceActive, by omega, by omega, by
    rw [drip_aux D (D - s.sinceActive) s h0 hs rfl]; decide⟩

/-- Any message arms upstream to full — sender identity does not exist
in its loop. -/
theorem any_message_arms (D : Nat) (s : LifeU) :
    (wakeU D s .msgNew).1.energy = fullU := rfl

def msgN (D : Nat) : Nat → LifeU → LifeU
  | 0, s => s
  | k + 1, s => msgN D k (wakeU D s .msgNew).1

/-- **The wind-up cycle.** Because any message arms, a trace of sibling
messages keeps an upstream agent at full 50 forever — two co-present
upstream agents re-arm each other indefinitely with zero humans. This
is the incident class the claws' human-gate prevents. -/
theorem mutual_arming_cycle (D : Nat) (s : LifeU) (n : Nat) :
    (msgN D (n + 1) s).energy = fullU := by
  induction n generalizing s with
  | zero => rfl
  | succ m ih => exact ih (wakeU D s .msgNew).1

/-- Genesis: no gate, no budget, no clock — every iteration is an LLM
call; the count of calls IS the count of wakes. -/
def genesisCalls (wakes : Nat) : Nat := wakes

theorem genesis_always_on (k : Nat) : genesisCalls k = k := rfl

end Upstream

/-- **The claw contrast.** A sibling's or bot's message is just another
wake — the claw spends its OWN energy attending to it, and cannot be
wound up by other agents: renewal is clock-driven (its own heartbeat),
never message-driven. Inter-agent arms races are structurally
impossible; autonomy is self-sourced. -/
theorem sibling_never_arms (H : Nat) (s : Life) (h1 : ¬ H ≤ s.since + 1) :
    (wake H s .work).1.energy = s.energy - 1 := by
  simp [wake, h1]

/-! ## The architecture summary -/

structure Architecture where
  wholeQueuePerTurn : Bool
  spuriousFree : Bool
  humanGatedArming : Bool
  renewalPeriodSeconds : Nat
  renewalAmount : Nat
deriving Repr, DecidableEq

/-- Mature upstream: 600 s drip of 2; any message arms. -/
def upstream : Architecture := ⟨false, false, false, 600, 2⟩
/-- Lila today: 1800 s heartbeat of 50; human-gated tiers; pop-one. -/
def lilaNow : Architecture := ⟨false, false, true, 1800, 50⟩
/-- Gödel today: 1800 s heartbeat of 50; human-gated tiers; batch. -/
def godelNew : Architecture := ⟨true, true, true, 1800, 50⟩

/-- Every architecture self-renews — nobody is human-powered — and the
claws' renewal is the most generous single burst. -/
theorem renewal_rhythms :
    0 < upstream.renewalAmount ∧ 0 < lilaNow.renewalAmount ∧
    0 < godelNew.renewalAmount ∧
    upstream.renewalAmount < lilaNow.renewalAmount ∧
    lilaNow.renewalAmount = godelNew.renewalAmount := by
  decide

end Claws

/-! ## Axiom audit (kernel-level trust check) -/
#print axioms Claws.starvation_bounded
#print axioms Claws.unbounded_autonomy
#print axioms Claws.only_rest_zeroes
#print axioms Claws.rest_is_a_nap
#print axioms Claws.breath_self_paced
#print axioms Claws.arming_can_drain
#print axioms Claws.arming_never_drains
#print axioms Claws.heartbeat_outranks_tiers
#print axioms Claws.separation
#print axioms Claws.batch_never_spurious
#print axioms Claws.drain_records_all
#print axioms Claws.filtered_never_represents
#print axioms Claws.filtered_presents_fresh
#print axioms Claws.policies_differ
#print axioms Claws.Upstream.upstream_renews
#print axioms Claws.Upstream.mutual_arming_cycle
#print axioms Claws.sibling_never_arms
#print axioms Claws.renewal_rhythms
