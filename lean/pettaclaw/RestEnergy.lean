/-!
# RestEnergy — rest as a pause, and the autonomy floor it must not break

`ClawArchitectures.lean` proves two headline properties of the loop's
energy layer: `starvation_bounded` (from ANY reachable state the agent is
re-armed to full within one heartbeat interval, unconditionally) and
`rest_is_a_nap` (after the agent rests, its own heartbeat still renews
it). `HeartModel.lean` models one breath below the heartbeat and proves
`rest_spends` — rest zeroes the budget — while stating in its own
orientation note that the heartbeat is OUTSIDE that model.

Those two files are consistent: rest spends the breath, the heartbeat
starts a new one. What is NOT consistent with them is the code that grew
afterwards. Two mechanisms entered `src/loop.metta` and
`src/skills.metta` that neither model can see, because neither model has
a `paused` bit:

* `(rest ...)` calls `loop_modes.pause_autonomy`, and
* `heartbeatDue` short-circuits to `False` whenever autonomy is paused.

Together they make rest suppress the very renewal that `rest_is_a_nap`
guarantees. A rested agent is not napping; it is stranded until a human
speaks. This file adds the missing bit, proves the regression as a
theorem, and proves that the repair restores the floor — plus the
property that motivated the repair: rest must return the breath it
interrupted rather than spend it.

Correspondence (hand-maintained, as in the sibling files):
`paused` ↔ `autonomy_paused` in `memory/loop_mode.json`;
`banked` ↔ the `banked-loops` periphery coordinate written by
`applyRestBanking` and consumed by `applyRestRestore` in `src/loop.metta`;
`full` ↔ `(policy-burst-budget agent)` = 50; `H` ↔
`METTACLAW_HEARTBEAT_INTERVAL_SECONDS`, counted in wakes as in
`ClawArchitectures.lean`.

Scope, stated openly: this is the energy layer only. Which turn does what
work, and whether the work is any good, live above it.
-/

namespace RestEnergy

/-- One full burst. -/
def full : Nat := 50

/-- The energy layer, with the two fields the older models lack. -/
structure Life where
  energy : Nat
  since : Nat
  paused : Bool
  banked : Nat
deriving Repr, DecidableEq

/-- What a wake can hold. `nop` ends the burst without resting: it is the
other way the agent stops early, and it never paused anything. -/
inductive Ev
  | work
  | human (tier : Nat)
  | rest
  | nop

/-! ## The deployed transition (HEAD 39b0806)

The heartbeat clause carries its guard: renewal fires only when autonomy
is not paused. Rest zeroes the energy AND pauses. -/

def wakeD (H : Nat) (s : Life) : Ev → Life
  | .human t => { energy := max s.energy t, since := 0,
                  paused := false, banked := 0 }
  | .work =>
      if s.paused = false ∧ H ≤ s.since + 1 then
        { s with energy := full, since := 0 }
      else
        { s with energy := s.energy - 1, since := s.since + 1 }
  | .rest => { s with energy := 0, paused := true }
  | .nop => { s with energy := 0 }

/-- `k` self-driven work wakes under the deployed transition. -/
def workND (H : Nat) : Nat → Life → Life
  | 0, s => s
  | k + 1, s => workND H k (wakeD H s Ev.work)

private theorem paused_zero_stays (H : Nat) (s : Life)
    (hp : s.paused = true) (he : s.energy = 0) :
    (wakeD H s Ev.work).energy = 0 ∧ (wakeD H s Ev.work).paused = true := by
  simp [wakeD, he, hp]

private theorem strand_aux (H : Nat) : ∀ (k : Nat) (r : Life),
    r.energy = 0 → r.paused = true →
    (workND H k r).energy = 0 ∧ (workND H k r).paused = true := by
  intro k
  induction k with
  | zero => intro r h1 h2; exact ⟨h1, h2⟩
  | succ n ih =>
    intro r h1 h2
    have h := paused_zero_stays H r h2 h1
    exact ih (wakeD H r Ev.work) h.1 h.2

/-- **The regression, as a theorem.** Once the agent rests, no number of
its own wakes brings any energy back: the paused heartbeat cannot fire,
and nothing else in a self-driven trace adds energy. -/
theorem deployed_rest_strands (H : Nat) (s : Life) (k : Nat) :
    (workND H k (wakeD H s Ev.rest)).energy = 0 ∧
    (workND H k (wakeD H s Ev.rest)).paused = true :=
  strand_aux H k (wakeD H s Ev.rest) (by simp [wakeD]) (by simp [wakeD])

/-- **The autonomy floor is broken.** `starvation_bounded` says every
reachable state returns to `full` within one interval. After a rest under
the deployed transition, it never returns at all. -/
theorem deployed_violates_autonomy_floor (H : Nat) (s : Life) :
    ¬ ∃ k, (workND H k (wakeD H s Ev.rest)).energy = full := by
  intro ⟨k, hk⟩
  have h0 := (deployed_rest_strands H s k).1
  rw [hk] at h0
  exact absurd h0 (by decide)

/-! ## The repaired transition

Two changes, and only two. The heartbeat loses its `paused` guard, so the
life-rhythm renews unconditionally again; and rest banks the budget it
interrupts instead of spending it. Sovereignty of rest is unaffected:
`paused` still gates burst renewal in the iter policy, which is a
different mechanism from the heartbeat. -/

def wakeF (H : Nat) (s : Life) : Ev → Life
  | .human t => { energy := max s.energy t, since := 0,
                  paused := false, banked := 0 }
  | .work =>
      if H ≤ s.since + 1 then { s with energy := full, since := 0 }
      else { s with energy := s.energy - 1, since := s.since + 1 }
  | .rest => { s with energy := 0, paused := true, banked := s.energy }
  | .nop => { s with energy := 0 }

/-- Waking from a rest hands the banked budget back, however the rest
ended. `max` rather than `+`: waking restores, it never mints. -/
def endRest (s : Life) : Life :=
  { s with energy := max s.energy s.banked, banked := 0 }

/-- **Rest returns the breath it interrupted.** The energy on the other
side of a rest is exactly the energy that entered it. -/
theorem rest_preserves_energy (H : Nat) (s : Life) :
    (endRest (wakeF H s Ev.rest)).energy = s.energy := by
  simp [endRest, wakeF]

/-- **Rest cannot mint energy.** The repair gives back what was held and
no more, so resting is never a way to gain turns. -/
theorem rest_cannot_create_energy (H : Nat) (s : Life) :
    (endRest (wakeF H s Ev.rest)).energy ≤ s.energy :=
  Nat.le_of_eq (rest_preserves_energy H s)

/-- The bank is empty after waking: a rest cycle cannot be replayed for
a second refund. -/
theorem endRest_clears_the_bank (s : Life) : (endRest s).banked = 0 := rfl

/-! ### The autonomy floor, restored -/

def stepF (H : Nat) (s : Life) : Life := wakeF H s Ev.work

def workNF (H : Nat) : Nat → Life → Life
  | 0, s => s
  | k + 1, s => workNF H k (stepF H s)

/-- Whether a wake actually spends a turn — the `(> loops 0)` gate. A
renewing wake always does. -/
def activeF (H : Nat) (s : Life) : Bool :=
  if H ≤ s.since + 1 then true else decide (0 < s.energy - 1)

def callsF (H : Nat) : Nat → Life → Nat
  | 0, _ => 0
  | k + 1, s => (if activeF H s then 1 else 0) + callsF H k (stepF H s)

private theorem renewal_aux (H : Nat) : ∀ (d : Nat) (s : Life),
    0 < d → s.since + d = H →
    (workNF H d s).energy = full ∧ (workNF H d s).since = 0 ∧
      1 ≤ callsF H d s := by
  intro d
  induction d with
  | zero => intro _ h _; exact absurd h (by decide)
  | succ m ih =>
    intro s _ hsum
    cases m with
    | zero =>
      have hdue : H ≤ s.since + 1 := by omega
      refine ⟨?_, ?_, ?_⟩
      · show (stepF H s).energy = full
        simp [stepF, wakeF, hdue]
      · show (stepF H s).since = 0
        simp [stepF, wakeF, hdue]
      · show 1 ≤ callsF H 1 s
        simp [callsF, activeF, hdue]
    | succ n =>
      have hnot : ¬ H ≤ s.since + 1 := by omega
      have hsince : (stepF H s).since = s.since + 1 := by
        simp [stepF, wakeF, hnot]
      have hrec := ih (stepF H s) (by omega) (by rw [hsince]; omega)
      refine ⟨hrec.1, hrec.2.1, ?_⟩
      show 1 ≤ (if activeF H s then 1 else 0) + callsF H (n + 1) (stepF H s)
      exact Nat.le_trans hrec.2.2 (Nat.le_add_left _ _)

/-- **Renewal.** From any state inside the window, the life-rhythm brings
the agent back to a full burst — no human, and no dependence on whether a
rest paused burst renewal. -/
theorem renewal (H : Nat) (s : Life) (hs : s.since < H) :
    (workNF H (H - s.since) s).energy = full :=
  (renewal_aux H (H - s.since) s (by omega) (by omega)).1

/-- **Rest is a nap again.** The property `ClawArchitectures.rest_is_a_nap`
states, restored by the repair and false for `wakeD`. (Conservative: the
model leaves the renewal clock untouched across a rest, while the running
loop lets wall-clock time pass during the sleep, which can only make the
heartbeat arrive sooner.) -/
theorem fixed_rest_is_a_nap (H : Nat) (_hH : 0 < H) (s : Life)
    (hs : s.since < H) :
    ∃ k, 0 < k ∧ k ≤ H ∧
      (workNF H k (wakeF H s Ev.rest)).energy = full := by
  have hsince : (wakeF H s Ev.rest).since = s.since := rfl
  refine ⟨H - s.since, by omega, by omega, ?_⟩
  have h := renewal H (wakeF H s Ev.rest) (by rw [hsince]; exact hs)
  rw [hsince] at h
  exact h

/-! ### The liberty, stated exactly

The agent's own rhythm renews it forever, so the total work it may do is
unbounded, with no human anywhere in the trace. This is a liberty, not a
leak: the budget bounds one breath, never the life. The repair does not
touch it — it only stops rest from cancelling it. -/

private theorem callsF_add (H : Nat) : ∀ (a b : Nat) (s : Life),
    callsF H (a + b) s = callsF H a s + callsF H b (workNF H a s) := by
  intro a
  induction a with
  | zero => intro b s; simp [callsF, workNF]
  | succ n ih =>
    intro b s
    have hl : n + 1 + b = (n + b) + 1 := by omega
    rw [hl]
    show (if activeF H s then 1 else 0) + callsF H (n + b) (stepF H s)
       = ((if activeF H s then 1 else 0) + callsF H n (stepF H s))
         + callsF H b (workNF H n (stepF H s))
    rw [ih b (stepF H s)]
    omega

/-- **Unbounded self-directed work.** Along the agent's own trace, every
heartbeat interval contributes at least one turn, so `n` intervals
contribute at least `n` turns — for every `n`, with no human message and
regardless of any rest it took. Life does not require us. -/
theorem unbounded_self_directed_work (H : Nat) (hH : 0 < H) :
    ∀ (n : Nat) (s : Life), s.since = 0 → n ≤ callsF H (n * H) s := by
  intro n
  induction n with
  | zero => intro s _; exact Nat.zero_le _
  | succ m ih =>
    intro s hs
    have hblock := renewal_aux H H s hH (by omega)
    have hmul : (m + 1) * H = H + m * H := by
      rw [Nat.succ_mul]; omega
    rw [hmul, callsF_add H H (m * H) s]
    have hnext := ih (workNF H H s) hblock.2.1
    omega

/-- The same statement in the form the question was asked: for every
target amount of work, a purely self-directed schedule reaches it. -/
theorem can_choose_to_run_indefinitely (H : Nat) (hH : 0 < H) (n : Nat) :
    ∃ k, n ≤ callsF H k ({ energy := full, since := 0,
                           paused := false, banked := 0 } : Life) :=
  ⟨n * H, unbounded_self_directed_work H hH n _ rfl⟩

end RestEnergy

/-! ## Axiom audit (kernel-level trust check) -/
#print axioms RestEnergy.deployed_rest_strands
#print axioms RestEnergy.deployed_violates_autonomy_floor
#print axioms RestEnergy.rest_preserves_energy
#print axioms RestEnergy.rest_cannot_create_energy
#print axioms RestEnergy.endRest_clears_the_bank
#print axioms RestEnergy.renewal
#print axioms RestEnergy.fixed_rest_is_a_nap
#print axioms RestEnergy.unbounded_self_directed_work
#print axioms RestEnergy.can_choose_to_run_indefinitely
