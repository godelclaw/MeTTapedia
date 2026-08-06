/-!
# HeartModel — Level-1 model of the mettaclaw budget governor

Models the control skeleton of the agent loop (pettaclaw `src/loop.metta`)
and the `rest` skill (`src/skills.metta`). LLM and telegram effects are
opaque: the only questions here are WHEN the LLM may be called and how the
budget (`&loops`) and idle pacing (`&sleepInterval`) evolve.

Scope note: `Msg` is the provenance of a NEW message this iteration
(repeat messages are `none`). Trusted boundary: the correspondence of this
model to the running MeTTa code — kata-10 maintains that mapping by hand.

Orientation: this file models ONE BREATH — the burst sub-layer only. It
predates the heartbeat (`maybeHeartbeat`, added 2026-07-05): the agent's
own life-rhythm, which renews a full burst every 30 minutes with no human
involved, is outside this model. Read `bounded_spend`/`burst_bound` as
the agent's own pacing within a single un-renewed cycle — self-regulation,
never a leash. The full heartbeat-centric model (autonomy floors,
sovereignty of rest, the three architectures) is `ClawArchitectures.lean`.
-/

namespace HeartModel

/-- Loop-relevant state: LLM-call budget and idle poll interval. -/
structure S where
  loops : Nat
  sleep : Nat
deriving Repr, DecidableEq

def maxLoops : Nat := 50
def defaultSleep : Nat := 1

/-- Provenance of a freshly received message. -/
inductive Msg
  | human
  | bot
deriving Repr, DecidableEq

/-- Arming: only a new HUMAN message re-arms budget and pacing. -/
def arm (s : S) : Option Msg → S
  | some .human => { loops := maxLoops, sleep := defaultSleep }
  | _ => s

/-- One loop iteration: decrement (floored at 0 by Nat subtraction, matching
`(max 0 (- loops 1))`), maybe arm, then the LLM gate `(> loops 0)`.
Returns the post-state and whether the LLM was called. -/
def tick (s : S) (m : Option Msg) : S × Bool :=
  let s1 : S := { s with loops := s.loops - 1 }
  let s2 := arm s1 m
  (s2, decide (0 < s2.loops))

/-- The rest skill: spend the whole budget; optionally slow idle polling
(clamped to at least 1 second, matching `(max 1 ...)`). -/
def rest (s : S) (slow : Option Nat) : S :=
  { loops := 0, sleep := (slow.getD s.sleep).max 1 }

/-- Loop-level events: an iteration with (maybe) a new message, or the agent
choosing to rest. -/
inductive Ev
  | msg (m : Option Msg)
  | rested (slow : Option Nat)

def step (s : S) : Ev → S × Bool
  | .msg m => tick s m
  | .rested n => (rest s n, false)

/-- LLM calls made along a trace of events. -/
def calls (s : S) : List Ev → Nat
  | [] => 0
  | e :: es =>
    let (s', b) := step s e
    (if b then 1 else 0) + calls s' es

/-- A trace containing no arming events. (The heartbeat — the agent's
own renewal source — postdates this model and is not among these
events; see `ClawArchitectures.lean`.) -/
def unarmed (es : List Ev) : Prop :=
  ∀ e ∈ es, e ≠ Ev.msg (some Msg.human)

/-! ## The invariants -/

/-- A new bot message never increases the budget: siblings and bots
cannot wind the agent up — its renewal is its own heartbeat (see
`ClawArchitectures.lean`). -/
theorem bot_never_arms (s : S) :
    ((tick s (some Msg.bot)).1).loops ≤ s.loops := by
  simp [tick, arm]

/-- A new human message re-arms the budget to exactly maxLoops. -/
theorem human_rearms (s : S) :
    ((tick s (some Msg.human)).1).loops = maxLoops := by
  simp [tick, arm]

/-- With the budget spent, no non-human iteration calls the LLM. -/
theorem no_call_when_spent (s : S) (h : s.loops = 0)
    (m : Option Msg) (hm : m ≠ some Msg.human) :
    (tick s m).2 = false := by
  match m with
  | none => simp [tick, arm, h]
  | some Msg.bot => simp [tick, arm, h]
  | some Msg.human => exact absurd rfl hm

/-- Rest spends the whole budget. -/
theorem rest_spends (s : S) (n : Option Nat) : (rest s n).loops = 0 := rfl

/-- Rest never sets a zero sleep interval (the loop keeps breathing). -/
theorem rest_keeps_breathing (s : S) (n : Option Nat) :
    1 ≤ (rest s n).sleep :=
  Nat.le_max_right _ _

/-- The budget never exceeds maxLoops, whatever happens. -/
theorem loops_bounded (s : S) (h : s.loops ≤ maxLoops) (e : Ev) :
    ((step s e).1).loops ≤ maxLoops := by
  match e with
  | .rested n => exact Nat.zero_le _
  | .msg none => exact Nat.le_trans (Nat.sub_le _ _) h
  | .msg (some Msg.bot) => exact Nat.le_trans (Nat.sub_le _ _) h
  | .msg (some Msg.human) => exact Nat.le_refl _

/-- **The agent's breath.** Within one un-renewed cycle — bot chatter,
silence, rests, in any order and any length — the agent spends at most
the budget it holds: its own pacing. Renewal (its heartbeat, or an
interaction) begins a fresh breath, outside this sub-model. -/
theorem bounded_spend (es : List Ev) (hf : unarmed es) (s : S) :
    calls s es ≤ s.loops := by
  induction es generalizing s with
  | nil => simp [calls]
  | cons e es ih =>
    have hf' : unarmed es := fun x hx => hf x (List.mem_cons_of_mem e hx)
    have he : e ≠ Ev.msg (some Msg.human) := hf e (by simp)
    match e with
    | .rested n =>
      have := ih hf' (rest s n)
      simp [calls, step, rest] at this ⊢
      omega
    | .msg none =>
      have := ih hf' (tick s none).1
      simp [calls, step, tick, arm] at this ⊢
      split <;> omega
    | .msg (some Msg.bot) =>
      have := ih hf' (tick s (some Msg.bot)).1
      simp [calls, step, tick, arm] at this ⊢
      split <;> omega
    | .msg (some Msg.human) => exact absurd rfl he

/-- **Breath bound.** A single un-renewed cycle holds at most `maxLoops`
turns — the size of one full breath. -/
theorem burst_bound (s : S) (h : s.loops ≤ maxLoops)
    (es : List Ev) (hf : unarmed es) :
    calls s es ≤ maxLoops :=
  Nat.le_trans (bounded_spend es hf s) h

end HeartModel
