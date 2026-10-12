/-!
# Operator control through the channel service

Operator commands now reach an agent through the CeTTa Telegram channel
service. Three switches can stop the agent:

* the service's own latch, which holds outgoing sends (`svc`);
* the cognition latch (`lifecycle.json`), which the agent's command responder
  sets when the service forwards `/stop` or `/start` to it (`cog`);
* the supervisor's pause marker, which the sibling tool and the watchdog use
  to keep the process down (`paused`).

The service answers `/stop` and `/start` at once from its own latch. The
cognition latch changes later, when the responder handles the forwarded
command. `LifecycleAuthority` and `ControlFastPath` model the cognition latch
alone; this file models the composition.

Deployed composition, counterexamples:
* `stopped_reply_while_thinking`: the operator is told "Stopped" while the
  forwarded command is pending, and the agent keeps making provider calls.
  With the responder down this continues for any number of calls
  (`stopped_reply_while_thinking_unbounded`).
* `started_reply_while_paused`: after the sibling tool pauses the agent, a
  `/start` is answered "Started" although no operator command can make the
  agent think again (`operator_commands_keep_pause`).

Commands among several agents:
* `bare_command_reaches_every_agent`: every agent of ours in a group accepts a
  bare `/stop`. `group_bare_command_reaches_none` and
  `addressed_command_reaches_only_its_agent` hold when groups require
  `/command@bot`; a private chat keeps bare commands
  (`private_bare_command_reaches_its_agent`).
* `shared_name_misnames`: with one command file shared by two agents with
  different names, one of them replies under the other's name. Taking the name
  from each agent's own configuration names the replying agent
  (`own_name_names_self`).

Proposed composition, results:
* One latch, held by the channel service, is the only stop authority.
  Cognition and the supervisor read it; the sibling tool writes it instead of
  a separate marker. Replies are computed from the committed latch.
* `reply_matches_authority`: after an operator command the reply equals the
  committed latch, whatever happened before.
* `stopped_means_no_new_calls`: once the latch is stopped, no provider call is
  admitted until a start.

The implemented repair keeps both latches and changes what the operator is
told: the reply is the responder's answer after it set the cognition latch, and
`/start` clears the agent's own pause. `implemented_replies_follow_effect`,
`implemented_no_false_stop` and `implemented_start_resumes` check it.

A provider call already in flight when the stop is committed completes; the
model admits each call atomically. Time, credentials and Telegram delivery are
abstracted.
-/

namespace ChannelOperatorControl

inductive Latch where
  | running | stopped
  deriving DecidableEq, Repr

/-! ## The deployed composition -/

structure Deployed where
  /-- The channel service's latch; it holds outgoing sends. -/
  svc : Latch
  /-- The cognition latch the responder writes. -/
  cog : Latch
  /-- The supervisor's pause marker. -/
  paused : Bool
  responderUp : Bool
  /-- Forwarded `/stop` and `/start` commands the responder has not applied. -/
  pending : List Latch
  /-- The last reply the operator received. -/
  told : Option Latch
  /-- Ghost: provider calls made. -/
  calls : Nat
  deriving DecidableEq, Repr

inductive Ev where
  | opStop | opStart
  /-- The responder applies the oldest forwarded command. -/
  | deliver
  | responderDown | responderUp
  | siblingPause | siblingResume
  /-- A model turn: one provider call if cognition may run. -/
  | think
  deriving DecidableEq, Repr

def Deployed.thinks (s : Deployed) : Bool := decide (s.cog = .running) && !s.paused

def stepD (s : Deployed) : Ev → Deployed
  | .opStop => { s with svc := .stopped, told := some .stopped, pending := s.pending ++ [.stopped] }
  | .opStart => { s with svc := .running, told := some .running, pending := s.pending ++ [.running] }
  | .deliver =>
      match s.pending with
      | [] => s
      | l :: rest => if s.responderUp then { s with cog := l, pending := rest } else s
  | .responderDown => { s with responderUp := false }
  | .responderUp => { s with responderUp := true }
  | .siblingPause => { s with paused := true }
  | .siblingResume => { s with paused := false }
  | .think => if s.thinks then { s with calls := s.calls + 1 } else s

def runD (s : Deployed) : List Ev → Deployed
  | [] => s
  | e :: es => runD (stepD s e) es

/-- A running agent with a live responder and nothing pending. -/
def d0 : Deployed :=
  { svc := .running, cog := .running, paused := false, responderUp := true,
    pending := [], told := none, calls := 0 }

/-- **Told "Stopped", still thinking.** Before the responder applies the
forwarded command, the agent keeps calling the provider. -/
theorem stopped_reply_while_thinking :
    (runD d0 [.opStop, .think, .think]).told = some .stopped ∧
    (runD d0 [.opStop, .think, .think]).calls = 2 := by decide

theorem think_while_responder_down (s : Deployed) (h : s.thinks = true) :
    stepD s .think = { s with calls := s.calls + 1 } := by
  simp [stepD, h]

theorem run_thinks (s : Deployed) (h : s.thinks = true) (n : Nat) :
    (runD s (List.replicate n .think)).calls = s.calls + n ∧
    (runD s (List.replicate n .think)).told = s.told := by
  induction n generalizing s with
  | zero => simp [runD]
  | succ n ih =>
    have h' : ({ s with calls := s.calls + 1 } : Deployed).thinks = true := by
      simpa [Deployed.thinks] using h
    rw [List.replicate_succ, runD, think_while_responder_down s h]
    obtain ⟨hc, ht⟩ := ih _ h'
    dsimp only at hc ht
    exact ⟨by rw [hc]; omega, ht⟩

/-- With the responder down, the agent keeps calling the provider for as long
as it runs, although the operator was told "Stopped". -/
theorem stopped_reply_while_thinking_unbounded (n : Nat) :
    (runD d0 ([.responderDown, .opStop] ++ List.replicate n .think)).told = some .stopped ∧
    (runD d0 ([.responderDown, .opStop] ++ List.replicate n .think)).calls = n := by
  have h : (runD d0 [.responderDown, .opStop]).thinks = true := by decide
  have hrun : ∀ es, runD d0 ([.responderDown, .opStop] ++ es) =
      runD (runD d0 [.responderDown, .opStop]) es := by
    intro es; rfl
  have h0 : (runD d0 [.responderDown, .opStop]).calls = 0 := by decide
  have ht0 : (runD d0 [.responderDown, .opStop]).told = some .stopped := by decide
  obtain ⟨hc, ht⟩ := run_thinks _ h n
  rw [hrun]
  exact ⟨ht.trans ht0, by rw [hc, h0]; omega⟩

/-- Operator commands and their delivery never clear the pause marker. -/
theorem operator_steps_keep_pause (s : Deployed) (e : Ev)
    (he : e = .opStop ∨ e = .opStart ∨ e = .deliver ∨ e = .think)
    (hp : s.paused = true) : (stepD s e).paused = true := by
  rcases he with rfl | rfl | rfl | rfl
  · simpa [stepD] using hp
  · simpa [stepD] using hp
  · simp only [stepD]
    split
    · exact hp
    · split <;> simpa using hp
  · simp only [stepD]; split <;> simpa using hp

theorem operator_commands_keep_pause (s : Deployed) (es : List Ev)
    (hes : ∀ e ∈ es, e = .opStop ∨ e = .opStart ∨ e = .deliver ∨ e = .think)
    (hp : s.paused = true) : (runD s es).paused = true ∧ (runD s es).thinks = false := by
  induction es generalizing s with
  | nil => exact ⟨hp, by simp [runD, Deployed.thinks, hp]⟩
  | cons e es ih =>
    exact ih _ (fun x hx => hes x (List.mem_cons_of_mem e hx))
      (operator_steps_keep_pause s e (hes e (List.mem_cons_self ..)) hp)

/-- **Told "Started", still paused.** After the sibling tool pauses the agent,
`/start` is answered "Started" and delivered, yet no turn can run, and no
further operator command changes that. -/
theorem started_reply_while_paused :
    (runD d0 [.siblingPause, .opStart, .deliver]).told = some .running ∧
    (runD d0 [.siblingPause, .opStart, .deliver]).cog = .running ∧
    (runD d0 [.siblingPause, .opStart, .deliver]).thinks = false := by decide

/-! ## Commands among several agents -/

structure Agent where
  name : String
  bot : String
  deriving DecidableEq, Repr

/-- An operator command: in a group or a private chat, bare or addressed as
`/command@bot`. -/
structure Command where
  inGroup : Bool
  addressee : Option String
  deriving DecidableEq, Repr

/-- Deployed: a bare command, or one addressed to this bot. -/
def acceptsD (a : Agent) (c : Command) : Bool :=
  match c.addressee with
  | none => true
  | some b => decide (b = a.bot)

/-- Proposed: in a group, only a command addressed to this bot. -/
def acceptsF (a : Agent) (c : Command) : Bool :=
  match c.addressee with
  | none => !c.inGroup
  | some b => decide (b = a.bot)

/-- Every agent in a group accepts a bare command there. -/
theorem bare_command_reaches_every_agent (agents : List Agent) :
    ∀ a ∈ agents, acceptsD a ⟨true, none⟩ = true := by
  intro a _; rfl

theorem group_bare_command_reaches_none (a : Agent) :
    acceptsF a ⟨true, none⟩ = false := rfl

theorem private_bare_command_reaches_its_agent (a : Agent) :
    acceptsF a ⟨false, none⟩ = true := rfl

theorem addressed_command_reaches_only_its_agent (a b : Agent) (inGroup : Bool) :
    acceptsF a ⟨inGroup, some b.bot⟩ = true ↔ a.bot = b.bot := by
  simp [acceptsF, eq_comm]

/-- Deployed: replies name the agent written in the shared command file. -/
def replyNameD (shared : String) (_ : Agent) : String := shared

/-- Proposed: replies name the agent from its own configuration. -/
def replyNameF (a : Agent) : String := a.name

/-- With one shared command file, one of two differently named agents replies
under the wrong name. -/
theorem shared_name_misnames (shared : String) (a b : Agent) (h : a.name ≠ b.name) :
    replyNameD shared a ≠ a.name ∨ replyNameD shared b ≠ b.name := by
  by_cases ha : shared = a.name
  · right; intro hb; exact h (ha ▸ hb)
  · left; exact ha

theorem own_name_names_self (a : Agent) : replyNameF a = a.name := rfl

/-- The deployed case: both agents ship the file that names Lila. -/
theorem godel_replies_as_lila :
    replyNameD "Lila" ⟨"Gödel", "godel_bot"⟩ = "Lila" ∧ ("Gödel" : String) ≠ "Lila" := by
  decide

/-! ## The proposed composition: one authority -/

structure Fixed where
  /-- The only stop authority, held by the channel service. Cognition and the
  supervisor read it; the sibling tool writes it. -/
  latch : Latch
  told : Option Latch
  calls : Nat
  deriving DecidableEq, Repr

inductive FEv where
  | opStop | opStart | siblingStop | siblingStart | think
  deriving DecidableEq, Repr

def stepF (s : Fixed) : FEv → Fixed
  | .opStop => { s with latch := .stopped, told := some .stopped }
  | .opStart => { s with latch := .running, told := some .running }
  | .siblingStop => { s with latch := .stopped }
  | .siblingStart => { s with latch := .running }
  | .think => if s.latch = .running then { s with calls := s.calls + 1 } else s

def runF (s : Fixed) : List FEv → Fixed
  | [] => s
  | e :: es => runF (stepF s e) es

/-- **The reply is the authority.** After any history, the reply to an operator
command equals the latch that cognition and the supervisor read. -/
theorem reply_matches_authority (s : Fixed) (es : List FEv) (c : FEv)
    (hc : c = .opStop ∨ c = .opStart) :
    (runF s (es ++ [c])).told = some (runF s (es ++ [c])).latch := by
  have : ∀ t : Fixed, runF t [c] = stepF t c := fun _ => rfl
  have hsplit : runF s (es ++ [c]) = runF (runF s es) [c] := by
    induction es generalizing s with
    | nil => rfl
    | cons e es ih => exact ih (stepF s e)
  rw [hsplit, this]
  rcases hc with rfl | rfl <;> rfl

/-- **Stopped means no new calls.** From a stopped latch, no sequence of turns
and stops admits a provider call. -/
theorem stopped_means_no_new_calls (s : Fixed) (es : List FEv)
    (hs : s.latch = .stopped)
    (hes : ∀ e ∈ es, e = .think ∨ e = .opStop ∨ e = .siblingStop) :
    (runF s es).calls = s.calls ∧ (runF s es).latch = .stopped := by
  induction es generalizing s with
  | nil => exact ⟨rfl, hs⟩
  | cons e es ih =>
    have he := hes e (List.mem_cons_self ..)
    have hrest := fun x hx => hes x (List.mem_cons_of_mem e hx)
    have hstep : (stepF s e).calls = s.calls ∧ (stepF s e).latch = .stopped := by
      rcases he with rfl | rfl | rfl
      · simp [stepF, hs]
      · simp [stepF]
      · simp [stepF]
    obtain ⟨hc, hl⟩ := ih (stepF s e) hstep.2 hrest
    exact ⟨hc.trans hstep.1, hl⟩


/-! ## The implemented repair

The deployment keeps both latches but changes what the operator is told. The
service still sets its send latch at once and forwards the command, but the
reply is the responder's answer, computed after it set the cognition latch;
`/start` also clears the agent's own pause marker. If the responder does not
answer before the deadline, the reply is a notice that claims nothing. -/

inductive Reply where
  | stopped | started | noAnswerYet
  deriving DecidableEq, Repr

structure Impl where
  svc : Latch
  cog : Latch
  paused : Bool
  responderUp : Bool
  pending : List Latch
  /-- The last reply sent to the operator. -/
  reply : Option Reply
  calls : Nat
  deriving DecidableEq, Repr

inductive IEv where
  | opStop | opStart | deliver | deadline
  | responderDown | responderUp | siblingPause | think
  deriving DecidableEq, Repr

def Impl.thinks (s : Impl) : Bool := decide (s.cog = .running) && !s.paused

def stepI (s : Impl) : IEv → Impl
  | .opStop => { s with svc := .stopped, pending := s.pending ++ [.stopped], reply := none }
  | .opStart => { s with svc := .running, pending := s.pending ++ [.running], reply := none }
  | .deliver =>
      match s.pending with
      | [] => s
      | l :: rest =>
          if s.responderUp then
            match l with
            | .stopped => { s with cog := .stopped, pending := rest, reply := some .stopped }
            | .running => { s with cog := .running, paused := false, pending := rest, reply := some .started }
          else s
  | .deadline => if s.reply = none then { s with reply := some .noAnswerYet } else s
  | .responderDown => { s with responderUp := false }
  | .responderUp => { s with responderUp := true }
  | .siblingPause => { s with paused := true }
  | .think => if s.thinks then { s with calls := s.calls + 1 } else s

def runI (s : Impl) : List IEv → Impl
  | [] => s
  | e :: es => runI (stepI s e) es

/-- A "Stopped" reply is sent only together with the stopped cognition latch,
and a "Started" reply only when the agent can think. -/
theorem implemented_replies_follow_effect (s : Impl) :
    ((stepI s .deliver).reply = some .stopped → (stepI s .deliver).reply ≠ s.reply →
      (stepI s .deliver).cog = .stopped) ∧
    ((stepI s .deliver).reply = some .started → (stepI s .deliver).reply ≠ s.reply →
      (stepI s .deliver).thinks = true) := by
  simp only [stepI]
  split
  · exact ⟨fun _ h => absurd rfl h, fun _ h => absurd rfl h⟩
  · split
    · split <;> simp [Impl.thinks]
    · exact ⟨fun _ h => absurd rfl h, fun _ h => absurd rfl h⟩

def i0 : Impl :=
  { svc := .running, cog := .running, paused := false, responderUp := true,
    pending := [], reply := none, calls := 0 }

/-- The deployed counterexample, replayed: with the responder down the agent
still thinks, but the operator is told only that there is no answer yet. -/
theorem implemented_no_false_stop :
    (runI i0 [.responderDown, .opStop, .think, .deadline]).reply = some .noAnswerYet ∧
    (runI i0 [.responderDown, .opStop, .think, .deadline]).calls = 1 := by decide

/-- After a sibling's pause, `/start` is answered "Started" only once the
agent can think again. -/
theorem implemented_start_resumes :
    (runI i0 [.siblingPause, .opStart, .deliver]).reply = some .started ∧
    (runI i0 [.siblingPause, .opStart, .deliver]).thinks = true := by decide

end ChannelOperatorControl

#print axioms ChannelOperatorControl.stopped_reply_while_thinking
#print axioms ChannelOperatorControl.stopped_reply_while_thinking_unbounded
#print axioms ChannelOperatorControl.started_reply_while_paused
#print axioms ChannelOperatorControl.operator_commands_keep_pause
#print axioms ChannelOperatorControl.bare_command_reaches_every_agent
#print axioms ChannelOperatorControl.addressed_command_reaches_only_its_agent
#print axioms ChannelOperatorControl.shared_name_misnames
#print axioms ChannelOperatorControl.godel_replies_as_lila
#print axioms ChannelOperatorControl.reply_matches_authority
#print axioms ChannelOperatorControl.stopped_means_no_new_calls
#print axioms ChannelOperatorControl.implemented_replies_follow_effect
#print axioms ChannelOperatorControl.implemented_no_false_stop
#print axioms ChannelOperatorControl.implemented_start_resumes
