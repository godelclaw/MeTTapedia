/-!
# The Telegram command plane

Operator commands are answered by the channel service, a process separate
from the agent they control. Every command is keyed by its Telegram update,
and each decision reads and writes only that command's record, so the
service is one small automaton per command plus the lifecycle latch.

A command about the service itself (help, a menu, deleting a message, stop,
start) is answered when it is received. A command about the agent is passed
to the agent and raced against a deadline the service owns: an answer from
the agent before the deadline is the reply; otherwise, at the deadline, the
service replies with its own facts and later edits that reply with the
agent's answer. Exactly one of the two replies is ever sent.

The agent is arbitrary. It may answer at once, late, never or repeatedly,
answer commands it was never asked, and submit any sends at any time. Every
theorem below holds for every such behaviour, interleaved in any order with
Telegram input and the service's clock. The model has no chat lanes: nothing
in a command's automaton waits on the agent's messages.

No Mathlib; the audit at the end lists the axioms.
-/

namespace PettaClaw.TelegramCommandPlane

/-- What a received command asks for. -/
inductive Kind where
  | service
  | delegated
  | stop
  | start
deriving DecidableEq, Repr

/-- What a reply carries: the service's own answer, the agent's answer, or
the service's facts at the deadline. -/
inductive Body (A : Type) where
  | service
  | agent (answer : A)
  | fallback
deriving DecidableEq, Repr

/-- The actions the service takes for one command. -/
inductive Action (A : Type) where
  | ask
  | reply (body : Body A)
  | edit (answer : A)
deriving DecidableEq, Repr

def Action.isReply {A : Type} : Action A → Bool
  | .reply _ => true
  | _ => false

def Action.isEdit {A : Type} : Action A → Bool
  | .edit _ => true
  | _ => false

/-- Telegram input, the agent's behaviour and the clock, in any interleaving. -/
inductive Event (A : Type) where
  | command (id : Nat) (kind : Kind)
  | answer (id : Nat) (answer : A)
  | submit (submission : Nat)
  | tick

/-- One command's record. -/
inductive Phase (A : Type) where
  | unseen
  | served (receivedAt : Nat)
  | waiting (receivedAt : Nat)
  | answered (receivedAt repliedAt : Nat) (answer : A)
  | fellBack (receivedAt : Nat)
  | edited (receivedAt editedAt : Nat) (answer : A)

def Phase.receivedAt {A : Type} : Phase A → Option Nat
  | .unseen => none
  | .served t => some t
  | .waiting t => some t
  | .answered t _ _ => some t
  | .fellBack t => some t
  | .edited t _ _ => some t

inductive Latch where
  | running
  | stopped
deriving DecidableEq, Repr

structure State (A : Type) where
  now : Nat
  latch : Latch
  phase : Nat → Phase A
  log : Nat → List (Nat × Action A)
  /-- Every answer the agent submitted, as the journal records it. -/
  heard : List (Nat × A)
  dispatched : List (Nat × Nat)
  held : List Nat

def State.init (A : Type) : State A :=
  { now := 0, latch := .running, phase := fun _ => .unseen, log := fun _ => [],
    heard := [], dispatched := [], held := [] }

def update {β : Type} (f : Nat → β) (k : Nat) (v : β) : Nat → β :=
  fun j => if j = k then v else f j

section Service

variable {A : Type} (D : Nat)

/-- Answer a command about the service at once. -/
def serve (s : State A) (id : Nat) : State A :=
  { s with phase := update s.phase id (.served s.now),
           log := update s.log id (s.log id ++ [(s.now, .reply .service)]) }

/-- A command arrives. Only its first arrival counts. -/
def receive (s : State A) (id : Nat) (kind : Kind) : State A :=
  match s.phase id with
  | .unseen =>
    match kind with
    | .service => serve s id
    | .stop => { serve s id with latch := .stopped }
    | .start => { serve s id with latch := .running }
    | .delegated =>
      { s with phase := update s.phase id (.waiting s.now),
               log := update s.log id (s.log id ++ [(s.now, .ask)]) }
  | _ => s

/-- The agent answers. The answer is recorded; it is the reply if the command
is still waiting, an edit of the fallback if the deadline has passed, and
otherwise changes nothing. -/
def hear (s : State A) (id : Nat) (a : A) : State A :=
  match s.phase id with
  | .waiting t0 =>
    { s with heard := s.heard ++ [(id, a)],
             phase := update s.phase id (.answered t0 s.now a),
             log := update s.log id (s.log id ++ [(s.now, .reply (.agent a))]) }
  | .fellBack t0 =>
    { s with heard := s.heard ++ [(id, a)],
             phase := update s.phase id (.edited t0 s.now a),
             log := update s.log id (s.log id ++ [(s.now, .edit a)]) }
  | _ => { s with heard := s.heard ++ [(id, a)] }

/-- The agent submits a send. It is dispatched only while running. -/
def submit (s : State A) (x : Nat) : State A :=
  match s.latch with
  | .running => { s with dispatched := s.dispatched ++ [(s.now, x)] }
  | .stopped => { s with held := s.held ++ [x] }

def fire (now : Nat) : Phase A → Phase A
  | .waiting t0 => if t0 + D ≤ now then .fellBack t0 else .waiting t0
  | p => p

def fireLog (now : Nat) : Phase A → List (Nat × Action A) → List (Nat × Action A)
  | .waiting t0, l => if t0 + D ≤ now then l ++ [(now, .reply .fallback)] else l
  | _, l => l

/-- The clock advances; every command whose deadline has come gets the
fallback reply. -/
def tick (s : State A) : State A :=
  { s with now := s.now + 1,
           phase := fun j => fire D (s.now + 1) (s.phase j),
           log := fun j => fireLog D (s.now + 1) (s.phase j) (s.log j) }

def step (s : State A) : Event A → State A
  | .command id kind => receive s id kind
  | .answer id a => hear s id a
  | .submit x => submit s x
  | .tick => tick D s

def run (s : State A) (es : List (Event A)) : State A := es.foldl (step D) s

/-- The log each phase stands for. -/
def expected : Phase A → List (Nat × Action A)
  | .unseen => []
  | .served t0 => [(t0, .reply .service)]
  | .waiting t0 => [(t0, .ask)]
  | .answered t0 t1 a => [(t0, .ask), (t1, .reply (.agent a))]
  | .fellBack t0 => [(t0, .ask), (t0 + D, .reply .fallback)]
  | .edited t0 t2 a => [(t0, .ask), (t0 + D, .reply .fallback), (t2, .edit a)]

def PhaseOk (now : Nat) (heard : List (Nat × A)) (j : Nat) : Phase A → Prop
  | .unseen => True
  | .served t0 => t0 ≤ now
  | .waiting t0 => t0 ≤ now ∧ now < t0 + D
  | .answered t0 t1 a => t0 ≤ t1 ∧ t1 < t0 + D ∧ t1 ≤ now ∧ (j, a) ∈ heard
  | .fellBack t0 => t0 + D ≤ now
  | .edited t0 t2 a => t0 + D ≤ t2 ∧ t2 ≤ now ∧ (j, a) ∈ heard

structure Inv (s : State A) : Prop where
  log_eq : ∀ j, s.log j = expected D (s.phase j)
  phase_ok : ∀ j, PhaseOk D s.now s.heard j (s.phase j)

theorem inv_init : Inv D (State.init A) :=
  ⟨fun _ => rfl, fun _ => trivial⟩

theorem phaseOk_mono {now now' : Nat} {heard heard' : List (Nat × A)} {j : Nat}
    {p : Phase A} (hn : now ≤ now') (hh : ∀ x, x ∈ heard → x ∈ heard')
    (h : PhaseOk D now heard j p) (hw : ∀ t0, p = .waiting t0 → now' < t0 + D) :
    PhaseOk D now' heard' j p := by
  cases p with
  | unseen => trivial
  | served t0 => exact Nat.le_trans h hn
  | waiting t0 => exact ⟨Nat.le_trans h.1 hn, hw t0 rfl⟩
  | answered t0 t1 a => exact ⟨h.1, h.2.1, Nat.le_trans h.2.2.1 hn, hh _ h.2.2.2⟩
  | fellBack t0 => exact Nat.le_trans h hn
  | edited t0 t2 a => exact ⟨h.1, Nat.le_trans h.2.1 hn, hh _ h.2.2⟩

theorem inv_receive (s : State A) (id : Nat) (kind : Kind) (hD : 0 < D)
    (h : Inv D s) : Inv D (receive s id kind) := by
  unfold receive
  cases hp : s.phase id with
  | unseen =>
    have hl := h.log_eq id
    rw [hp] at hl
    cases kind <;>
    · constructor
      · intro j
        by_cases hj : j = id
        · subst hj; simp [serve, update, hl, expected]
        · simp [serve, update, hj, h.log_eq j]
      · intro j
        by_cases hj : j = id
        · subst hj; simp [serve, update, PhaseOk] <;> omega
        · simp [serve, update, hj]; exact h.phase_ok j
  | _ => simpa [hp] using h

theorem inv_hear (s : State A) (id : Nat) (a : A) (h : Inv D s) :
    Inv D (hear s id a) := by
  have hh : ∀ x, x ∈ s.heard → x ∈ s.heard ++ [(id, a)] :=
    fun x hx => List.mem_append_left _ hx
  have keep : ∀ j, PhaseOk D s.now (s.heard ++ [(id, a)]) j (s.phase j) := fun j =>
    phaseOk_mono D (Nat.le_refl _) hh (h.phase_ok j) (fun t0 hw => by
      have := h.phase_ok j; rw [hw] at this; exact this.2)
  unfold hear
  cases hp : s.phase id with
  | waiting t0 =>
    have hl := h.log_eq id
    have ho := h.phase_ok id
    rw [hp] at hl ho
    constructor
    · intro j
      by_cases hj : j = id
      · subst hj; simp [update, hl, expected]
      · simp [update, hj, h.log_eq j]
    · intro j
      by_cases hj : j = id
      · subst hj; simp only [PhaseOk] at ho; simp [update, PhaseOk, ho.1, ho.2]
      · simp [update, hj]; exact keep j
  | fellBack t0 =>
    have hl := h.log_eq id
    have ho := h.phase_ok id
    rw [hp] at hl ho
    constructor
    · intro j
      by_cases hj : j = id
      · subst hj; simp [update, hl, expected]
      · simp [update, hj, h.log_eq j]
    · intro j
      by_cases hj : j = id
      · subst hj; simp [update, PhaseOk]; exact ho
      · simp [update, hj]; exact keep j
  | _ => exact ⟨h.log_eq, keep⟩

theorem inv_submit (s : State A) (x : Nat) (h : Inv D s) : Inv D (submit s x) := by
  unfold submit
  cases s.latch <;> exact ⟨h.log_eq, h.phase_ok⟩

theorem inv_tick (s : State A) (h : Inv D s) : Inv D (tick D s) := by
  constructor
  · intro j
    have hl := h.log_eq j
    have ho := h.phase_ok j
    simp only [tick]
    cases hp : s.phase j with
    | waiting t0 =>
      rw [hp] at hl ho
      simp only [PhaseOk] at ho
      simp only [fire, fireLog]
      by_cases hd : t0 + D ≤ s.now + 1
      · have hnow : s.now + 1 = t0 + D := by omega
        rw [if_pos hd, if_pos hd, hl, hnow]; rfl
      · rw [if_neg hd, if_neg hd, hl]
    | _ => rw [hp] at hl; simp only [fire, fireLog]; exact hl
  · intro j
    have ho := h.phase_ok j
    simp only [tick]
    cases hp : s.phase j with
    | waiting t0 =>
      rw [hp] at ho
      simp only [PhaseOk] at ho
      simp only [fire]
      by_cases hd : t0 + D ≤ s.now + 1
      · rw [if_pos hd]; exact hd
      · rw [if_neg hd]; exact ⟨by omega, by omega⟩
    | _ =>
      rw [hp] at ho
      simp only [fire]
      exact phaseOk_mono D (Nat.le_succ _) (fun _ hx => hx) ho (fun _ hw => by cases hw)

theorem inv_step (s : State A) (e : Event A) (hD : 0 < D) (h : Inv D s) :
    Inv D (step D s e) := by
  cases e with
  | command id kind => exact inv_receive D s id kind hD h
  | answer id a => exact inv_hear D s id a h
  | submit x => exact inv_submit D s x h
  | tick => exact inv_tick D s h

theorem inv_run (s : State A) (es : List (Event A)) (hD : 0 < D) (h : Inv D s) :
    Inv D (run D s es) := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (inv_step D s e hD h)

/-- The service records exactly the answers the agent submitted, in order. -/
def answersOf : List (Event A) → List (Nat × A)
  | [] => []
  | .answer id a :: es => (id, a) :: answersOf es
  | _ :: es => answersOf es

theorem heard_run (s : State A) (es : List (Event A)) :
    (run D s es).heard = s.heard ++ answersOf es := by
  induction es generalizing s with
  | nil => simp [run, answersOf]
  | cons e es ih =>
    show (run D (step D s e) es).heard = _
    rw [ih]
    cases e with
    | command id kind =>
      simp only [step, answersOf]; unfold receive
      cases s.phase id <;> (try cases kind) <;> simp [serve]
    | answer id a =>
      simp only [step, answersOf]; unfold hear
      cases s.phase id <;> simp
    | submit x => simp only [step, answersOf]; unfold submit; cases s.latch <;> simp
    | tick => simp [step, tick, answersOf]

/-! ## The guarantees -/

/-- A command is never replied to twice. -/
theorem at_most_one_reply (es : List (Event A)) (hD : 0 < D) (c : Nat) :
    ((run D (State.init A) es).log c).countP (fun e => e.2.isReply) ≤ 1 := by
  rw [(inv_run D _ es hD (inv_init D)).log_eq c]
  cases (run D (State.init A) es).phase c <;> simp [expected, Action.isReply]

/-- Bounded response. Whatever the agent does, a command received at time
`t0` has exactly one reply once the clock reaches `t0 + D`, sent no later. -/
theorem reply_by_deadline (es : List (Event A)) (hD : 0 < D) (c t0 : Nat)
    (hr : ((run D (State.init A) es).phase c).receivedAt = some t0)
    (hn : t0 + D ≤ (run D (State.init A) es).now) :
    ((run D (State.init A) es).log c).countP (fun e => e.2.isReply) = 1 ∧
    ∀ e ∈ (run D (State.init A) es).log c, e.2.isReply = true → e.1 ≤ t0 + D := by
  have inv := inv_run D _ es hD (inv_init D)
  rw [inv.log_eq c]
  have ho := inv.phase_ok c
  cases hp : (run D (State.init A) es).phase c with
  | unseen => rw [hp] at hr; cases hr
  | served t =>
    rw [hp] at hr; cases hr
    simp [expected, Action.isReply] <;> omega
  | waiting t =>
    rw [hp] at hr ho; cases hr; simp [PhaseOk] at ho; omega
  | answered t t1 a =>
    rw [hp] at hr ho; cases hr
    simp [expected, Action.isReply, PhaseOk] at ho ⊢; omega
  | fellBack t =>
    rw [hp] at hr; cases hr
    simp [expected, Action.isReply]
  | edited t t2 a =>
    rw [hp] at hr; cases hr
    simp [expected, Action.isReply]

/-- A command about the service is answered by the service at the moment it
is received. -/
theorem service_reply_is_immediate (es : List (Event A)) (hD : 0 < D) (c t0 : Nat)
    (hp : (run D (State.init A) es).phase c = .served t0) :
    (run D (State.init A) es).log c = [(t0, .reply .service)] := by
  rw [(inv_run D _ es hD (inv_init D)).log_eq c, hp]; rfl

/-- Every reply is the service's own answer, the fallback, or an answer the
agent actually gave to this very command. -/
theorem reply_provenance (es : List (Event A)) (hD : 0 < D) (c t : Nat) (b : Body A)
    (hm : (t, Action.reply b) ∈ (run D (State.init A) es).log c) :
    b = .service ∨ b = .fallback ∨ ∃ a, b = .agent a ∧ (c, a) ∈ answersOf es := by
  have inv := inv_run D _ es hD (inv_init D)
  rw [inv.log_eq c] at hm
  have ho := inv.phase_ok c
  rw [heard_run] at ho
  cases hp : (run D (State.init A) es).phase c with
  | unseen => rw [hp] at hm; cases hm
  | served t0 => rw [hp] at hm; simp [expected] at hm; exact Or.inl hm.2
  | waiting t0 => rw [hp] at hm; simp [expected] at hm
  | answered t0 t1 a =>
    rw [hp] at hm ho
    simp [expected] at hm
    simp only [PhaseOk, State.init, List.nil_append] at ho
    exact Or.inr (Or.inr ⟨a, hm.2, ho.2.2.2⟩)
  | fellBack t0 => rw [hp] at hm; simp [expected] at hm; exact Or.inr (Or.inl hm.2)
  | edited t0 t2 a => rw [hp] at hm; simp [expected] at hm; exact Or.inr (Or.inl hm.2)

/-- An edit only ever follows the fallback reply, at or after the deadline,
and carries an answer the agent gave to this very command. -/
theorem edit_provenance (es : List (Event A)) (hD : 0 < D) (c t : Nat) (a : A)
    (hm : (t, Action.edit a) ∈ (run D (State.init A) es).log c) :
    ∃ t0, ((run D (State.init A) es).phase c).receivedAt = some t0 ∧
      (t0 + D, Action.reply .fallback) ∈ (run D (State.init A) es).log c ∧
      t0 + D ≤ t ∧ (c, a) ∈ answersOf es := by
  have inv := inv_run D _ es hD (inv_init D)
  have hl := inv.log_eq c
  have ho := inv.phase_ok c
  rw [heard_run] at ho
  rw [hl] at hm ⊢
  cases hp : (run D (State.init A) es).phase c with
  | edited t0 t2 a' =>
    rw [hp] at hm ho
    simp [expected] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp only [PhaseOk, State.init, List.nil_append] at ho
    exact ⟨t0, rfl, List.mem_cons_of_mem _ List.mem_cons_self, ho.1, ho.2.2⟩
  | _ => rw [hp] at hm; simp [expected] at hm

/-- If the agent never answers a command, its reply is the fallback, sent
exactly at the deadline. -/
theorem silent_agent_gets_fallback (es : List (Event A)) (hD : 0 < D) (c t0 : Nat)
    (hsilent : ∀ a, (c, a) ∉ answersOf es)
    (hw : ((run D (State.init A) es).phase c).receivedAt = some t0)
    (hdel : ∀ t, (run D (State.init A) es).phase c ≠ .served t)
    (hn : t0 + D ≤ (run D (State.init A) es).now) :
    (run D (State.init A) es).log c = [(t0, .ask), (t0 + D, .reply .fallback)] := by
  have inv := inv_run D _ es hD (inv_init D)
  have ho := inv.phase_ok c
  rw [heard_run] at ho
  rw [inv.log_eq c]
  cases hp : (run D (State.init A) es).phase c with
  | unseen => rw [hp] at hw; cases hw
  | served t => exact absurd hp (hdel t)
  | waiting t => rw [hp] at hw ho; cases hw; simp only [PhaseOk] at ho; exfalso; omega
  | answered t t1 a =>
    rw [hp] at ho; simp only [PhaseOk, State.init, List.nil_append] at ho; exact absurd ho.2.2.2 (hsilent a)
  | fellBack t => rw [hp] at hw; cases hw; rfl
  | edited t t2 a =>
    rw [hp] at ho; simp only [PhaseOk, State.init, List.nil_append] at ho; exact absurd ho.2.2 (hsilent a)

/-! ## Why the deadline must be the service's

In the design where a command about the agent is answered only by the agent,
the clock produces nothing: while the agent is silent, the command is never
answered, however long the operator waits. -/

def tickGated (s : State A) : State A := { s with now := s.now + 1 }

def stepGated (s : State A) : Event A → State A
  | .command id kind => receive s id kind
  | .answer id a => hear s id a
  | .submit x => submit s x
  | .tick => tickGated s

theorem gated_ticks_keep_log (s : State A) (n : Nat) :
    (List.foldl stepGated s (List.replicate n .tick)).log = s.log := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (tickGated s)

theorem gated_silent_agent_never_answered (n : Nat) :
    ((List.foldl stepGated (State.init A)
        (Event.command 0 .delegated :: List.replicate n .tick)).log 0).countP
      (fun e => e.2.isReply) = 0 := by
  show ((List.foldl stepGated (stepGated (State.init A) (.command 0 .delegated))
        (List.replicate n .tick)).log 0).countP _ = 0
  rw [gated_ticks_keep_log]
  simp [stepGated, receive, State.init, update, Action.isReply]

/-! ## Stop is enforced where sends are dispatched -/

def NoStart (es : List (Event A)) : Prop := ∀ id, Event.command id .start ∉ es

/-- Once stopped, no send the agent submits is dispatched until a start
command arrives, whatever the agent does. -/
theorem stopped_dispatches_nothing (s : State A) (es : List (Event A))
    (hs : s.latch = .stopped) (hns : NoStart es) :
    (run D s es).dispatched = s.dispatched ∧ (run D s es).latch = .stopped := by
  induction es generalizing s with
  | nil => exact ⟨rfl, hs⟩
  | cons e es ih =>
    have hrest : NoStart es := fun id hm => hns id (List.mem_cons_of_mem _ hm)
    have hstep : (step D s e).dispatched = s.dispatched ∧ (step D s e).latch = .stopped := by
      cases e with
      | command id kind =>
        have hk : kind ≠ .start := fun hk => hns id (by rw [hk]; exact List.mem_cons_self)
        simp only [step]; unfold receive
        cases s.phase id <;> (try cases kind) <;> simp_all [serve]
      | answer id a => simp only [step]; unfold hear; cases s.phase id <;> simp [hs]
      | submit x => simp only [step]; unfold submit; simp [hs]
      | tick => simp [step, tick, hs]
    have := ih (step D s e) hstep.2 hrest
    exact ⟨this.1.trans hstep.1, this.2⟩

/-- A stop command's first arrival stops dispatch at once and is answered at
once. -/
theorem stop_takes_effect (s : State A) (id : Nat) (hu : ∀ p, s.phase id = p → p = .unseen) :
    (receive s id .stop).latch = .stopped ∧
    (receive s id .stop).log id = s.log id ++ [(s.now, .reply .service)] := by
  have := hu _ rfl
  unfold receive; rw [this]; simp [serve, update]

end Service

#print axioms at_most_one_reply
#print axioms reply_by_deadline
#print axioms service_reply_is_immediate
#print axioms reply_provenance
#print axioms edit_provenance
#print axioms silent_agent_gets_fallback
#print axioms gated_silent_agent_never_answered
#print axioms stopped_dispatches_nothing
#print axioms stop_takes_effect

end PettaClaw.TelegramCommandPlane
