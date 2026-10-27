import Mettapedia.GSLT.Timing.ClockModels
import Mettapedia.GSLT.Coordination.Deduplication
import Mettapedia.Logic.EvidenceKinds.Verdicts

/-!
# A timeout yields "unknown": never failure, never a blind rerun

A caller sends a request, the callee performs the effect when the request arrives, and a
completion comes back. A deadline that fires before the completion has arrived is a **timeout**.

## What a timeout tells the caller

A call is described by when it was sent, when the effect happened (if ever) and when the
completion reached the caller (if ever) (`Call`). The caller sees only its own send and the
completion if it has arrived (`view`). A **verdict rule** maps what the caller sees to `done`,
`notDone` or `unknown`; it is **sound** when `done` means the effect happened and `notDone` means
it never will (`Sound`). These are the verdicts of `Logic.EvidenceKinds` on the claim that the
effect happens (`Sound.reads`), with `done` dated.

* **A timeout is unknown, even in the synchronous model** (`timeout_unknown`): a callee that
  performs the effect and stops before replying, and one that stops before performing it, look
  the same to the caller at every time. Both are admissible with every delay bound
  (`SyncCall`), so every sound rule answers `unknown` on a timeout.
* **In the asynchronous model the effect can still come** (`Controls.async_late_effect`): the
  request may still be in flight, so the effect may happen after the deadline. "Not yet" is not
  "not".
* **In the synchronous model the unknown is stable** (`sync_no_late_effect`,
  `deadline_after_bound`): once a bound on the request's delay has passed, no effect happens
  later. A deadline of `D` units on a clock running at most at `fast / den` with `fast · Δ <
  den · D` fires after that bound. Synchrony does not resolve the unknown; it only ensures that
  nothing changes after the deadline.

## The durable runner with timeouts

The runner of `Coordination.Deduplication` (begin, call, finish, crash) gains a deadline per
activity (`TimedEvent.timeout`) and the completion notice, which may arrive at any time, also
after the deadline (`TimedEvent.complete`).

* **Unknown never reruns** (`unknown_at_most_once`): if a timeout makes the activity unknown, every
  activity's external effect happens at most once, for every order of begins, calls, timeouts,
  completions and crashes: for every timing.
* **A late completion is matched, not repeated** (`complete_unknown_finishes`,
  `Controls.late_completion_deduplicated`): the completion of a timed-out activity finishes it by
  its identifier, and a further call is refused.
* **Timeout as failure calls twice** (`Controls.timeout_as_failure_twice`), with no late
  completion at all: the run is admissible in the synchronous model.
* **A deliberate retry is safe only through the key** (`keyed_retry_once`,
  `Controls.keyed_retry_applies_once`): a sink that deduplicates by the activity's identifier
  applies each called activity exactly once, however often a retry calls it.

This connects the deadline arm of a timed `await` (`TimedAwait`) to the durable-continuation
rule: the timed-out continuation resumes with "unknown", and only the key at the effect's
boundary makes a retry safe.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Timing.TimeoutUnknown

open Mettapedia.GSLT.Timing
open Mettapedia.GSLT.Coordination.Deduplication

universe u

/-! ## What a timeout tells the caller -/

/-- One call: when it was sent, when the callee performed the effect (if ever), and when the
completion reached the caller (if ever). -/
structure Call where
  sentAt : ℕ
  effectAt : Option ℕ
  replyAt : Option ℕ

/-- What the caller sees at real time `t`: its own send, and the completion if it has arrived. -/
def view (c : Call) (t : ℕ) : ℕ × Option ℕ := (c.sentAt, c.replyAt.filter (· ≤ t))

/-- The three verdicts. -/
inductive Verdict where
  | done
  | notDone
  | unknown
  deriving DecidableEq, Repr

/-- A verdict at real time `t` is sound for a call: `done` only if the effect has happened by
`t`, `notDone` only if it never happens. `unknown` claims nothing. -/
def Sound (v : Verdict) (c : Call) (t : ℕ) : Prop :=
  (v = .done → ∃ e, c.effectAt = some e ∧ e ≤ t) ∧ (v = .notDone → c.effectAt = none)

/-- A call admissible in the asynchronous model: the effect follows the send, and a completion
follows the effect. -/
def AsyncCall (c : Call) : Prop :=
  (∀ e, c.effectAt = some e → c.sentAt ≤ e) ∧
    ∀ r, c.replyAt = some r → ∃ e, c.effectAt = some e ∧ e ≤ r

/-- A call admissible in the synchronous model with delay bound `Δ`: the request, if it arrives,
arrives within `Δ`, and so does the completion. The callee may stop at any point. -/
def SyncCall (Δ : ℕ) (c : Call) : Prop :=
  (∀ e, c.effectAt = some e → c.sentAt ≤ e ∧ e ≤ c.sentAt + Δ) ∧
    ∀ r, c.replyAt = some r → ∃ e, c.effectAt = some e ∧ e ≤ r ∧ r ≤ e + Δ

/-- A call admissible with a delay bound is admissible asynchronously. -/
theorem SyncCall.async {Δ : ℕ} {c : Call} (admissible : SyncCall Δ c) : AsyncCall c :=
  ⟨fun e h => (admissible.1 e h).1, fun r h => by
    obtain ⟨e, happened, before, -⟩ := admissible.2 r h
    exact ⟨e, happened, before⟩⟩

/-- The callee performed the effect at once and stopped before replying. -/
def effectNoReply (s : ℕ) : Call := ⟨s, some s, none⟩

/-- The callee stopped before performing the effect. -/
def noEffect (s : ℕ) : Call := ⟨s, none, none⟩

theorem effectNoReply_sync (Δ s : ℕ) : SyncCall Δ (effectNoReply s) :=
  ⟨fun e h => by simp only [effectNoReply, Option.some.injEq] at h ⊢; omega,
    fun r h => by simp [effectNoReply] at h⟩

theorem noEffect_sync (Δ s : ℕ) : SyncCall Δ (noEffect s) :=
  ⟨fun e h => by simp [noEffect] at h, fun r h => by simp [noEffect] at h⟩

/-- A timeout verdict read as a verdict of `Logic.EvidenceKinds` on the claim that the effect
happens: `done` establishes it, `notDone` refutes it, `unknown` claims nothing. -/
def Verdict.toEvidence : Verdict → Mettapedia.Logic.EvidenceKinds.Verdict
  | .done => .established
  | .notDone => .refuted
  | .unknown => .unknown

/-- **A sound timeout verdict is a sound evidence verdict** on the claim that the effect happens.
It says more: `done` also dates the effect (`Controls.done_dates_effect`). -/
theorem Sound.reads {v : Verdict} {c : Call} {t : ℕ} (sound : Sound v c t) :
    v.toEvidence.Reads (c.effectAt ≠ none) := by
  cases v with
  | done =>
      obtain ⟨e, happened, -⟩ := sound.1 rfl
      simp [Verdict.toEvidence, Mettapedia.Logic.EvidenceKinds.Verdict.Reads, happened]
  | notDone =>
      simp [Verdict.toEvidence, Mettapedia.Logic.EvidenceKinds.Verdict.Reads, sound.2 rfl]
  | unknown => trivial

/-- **A timeout is unknown, even in the synchronous model.** Every verdict rule that is sound on
every call admissible with delay bound `Δ`, at every time, answers `unknown` to a caller that sent
at `s` and has no completion. -/
theorem timeout_unknown (Δ : ℕ) (rule : ℕ × Option ℕ → Verdict)
    (sound : ∀ c t, SyncCall Δ c → Sound (rule (view c t)) c t) (s : ℕ) :
    rule (s, none) = .unknown := by
  have viewOne : view (effectNoReply s) s = (s, none) := rfl
  have viewTwo : view (noEffect s) s = (s, none) := rfl
  have one := sound (effectNoReply s) s (effectNoReply_sync Δ s)
  have two := sound (noEffect s) s (noEffect_sync Δ s)
  rw [viewOne] at one
  rw [viewTwo] at two
  cases verdict : rule (s, none) with
  | done =>
      obtain ⟨e, isSome, -⟩ := two.1 verdict
      simp [noEffect] at isSome
  | notDone =>
      have := one.2 verdict
      simp [effectNoReply] at this
  | unknown => rfl

/-- **In the synchronous model nothing happens after the bound**: once `Δ` has passed since the
send, the effect, if any, has happened. -/
theorem sync_no_late_effect {Δ : ℕ} {c : Call} (admissible : SyncCall Δ c) {t : ℕ}
    (past : c.sentAt + Δ ≤ t) : ∀ e, c.effectAt = some e → e ≤ t :=
  fun e happened => le_trans (admissible.1 e happened).2 past

/-- **A deadline past the bound**: a deadline of `D` units armed at the send, on a clock that runs
at most at `fast / den`, with `fast · Δ < den · D`, passes only after the bound `Δ`, so once it
fires no effect of the call is still to come. -/
theorem deadline_after_bound {c : Clock} {den slow fast D Δ t : ℕ} (rates : RateBounds c den slow fast)
    {call : Call} (admissible : SyncCall Δ call) (margin : fast * Δ < den * D)
    (passed : Passed c call.sentAt D t) : ∀ e, call.effectAt = some e → e ≤ t := by
  apply sync_no_late_effect admissible
  have := reply_before_passed rates (r := call.sentAt + Δ) le_rfl margin passed
  omega

/-! ## The durable runner with timeouts -/

variable {A : Type u} [DecidableEq A]

/-- What the runner does when an activity's deadline fires while it is begun. -/
inductive OnTimeout where
  /-- The activity becomes unknown; the runner never calls it again. -/
  | unknown
  /-- The call counts as failed; the runner may call again. -/
  | retry
  deriving DecidableEq

/-- Runner events with time: the events of `Deduplication`, a deadline per activity, and the
completion notice of a call, which may arrive at any time, also after the deadline. -/
inductive TimedEvent (A : Type u) where
  | base (e : RunnerEvent A)
  | timeout (a : A)
  | complete (a : A)

/-- One event. Crashes recover by the unknown rule of `Deduplication`. A completion finishes a
begun activity that was called in this life, or an unknown activity whose effect happened: it is
matched by the activity's identifier. -/
def timedStep (policy : OnTimeout) (r : Runner A) : TimedEvent A → Runner A
  | .base e => runnerStep .markUnknown r e
  | .timeout a =>
      if r.status a = .begun then
        match policy with
        | .unknown => { r with status := Function.update r.status a .unknown }
        | .retry => { r with called := r.called.erase a }
      else r
  | .complete a =>
      if (r.status a = .begun ∧ a ∈ r.called) ∨ (r.status a = .unknown ∧ a ∈ r.external) then
        { r with status := Function.update r.status a .finished }
      else r

/-- A run. -/
def timedRun (policy : OnTimeout) (r : Runner A) : List (TimedEvent A) → Runner A
  | [] => r
  | e :: es => timedRun policy (timedStep policy r e) es

theorem unknownInv_timeout {r : Runner A} (inv : UnknownInv r) (a : A) :
    UnknownInv (timedStep .unknown r (.timeout a)) := by
  simp only [timedStep]
  split_ifs with isBegun
  · refine ⟨inv.nodup, fun x h => ?_, fun x member => ?_, fun x h => ?_⟩
    · by_cases same : x = a
      · subst same; simp at h
      · simp only [Function.update_of_ne same] at h; exact inv.absentNone x h
    · by_cases same : x = a
      · subst same; simp
      · simp only [Function.update_of_ne same]; exact inv.calledPresent x member
    · by_cases same : x = a
      · subst same; simp at h
      · simp only [Function.update_of_ne same] at h; exact inv.begunCalled x h
  · exact inv

theorem unknownInv_complete {r : Runner A} (inv : UnknownInv r) (policy : OnTimeout) (a : A) :
    UnknownInv (timedStep policy r (.complete a)) := by
  simp only [timedStep]
  split_ifs with ok
  · refine ⟨inv.nodup, fun x h => ?_, fun x member => ?_, fun x h => ?_⟩
    · by_cases same : x = a
      · subst same; simp at h
      · simp only [Function.update_of_ne same] at h; exact inv.absentNone x h
    · by_cases same : x = a
      · subst same; simp
      · simp only [Function.update_of_ne same]; exact inv.calledPresent x member
    · by_cases same : x = a
      · subst same; simp at h
      · simp only [Function.update_of_ne same] at h; exact inv.begunCalled x h
  · exact inv

/-- **Unknown never reruns**: when a timeout makes the activity unknown, every activity's
external effect happens at most once, for every order of begins, calls, timeouts, completions,
finishes and crashes. -/
theorem unknown_at_most_once (events : List (TimedEvent A)) :
    (timedRun .unknown Runner.fresh events).external.Nodup := by
  suffices ∀ r : Runner A, UnknownInv r → UnknownInv (timedRun .unknown r events) from
    (this _ unknownInv_fresh).nodup
  induction events with
  | nil => exact fun _ inv => inv
  | cons e rest ih =>
      intro r inv
      apply ih
      cases e with
      | base e => exact unknownInv_step inv e
      | timeout a => exact unknownInv_timeout inv a
      | complete a => exact unknownInv_complete inv .unknown a

/-- **A late completion is matched, not repeated**: the completion notice of an unknown activity
whose effect happened finishes it, and adds no effect. -/
theorem complete_unknown_finishes (policy : OnTimeout) {r : Runner A} {a : A}
    (isUnknown : r.status a = .unknown) (happened : a ∈ r.external) :
    (timedStep policy r (.complete a)).status a = .finished ∧
      (timedStep policy r (.complete a)).external = r.external := by
  simp [timedStep, isUnknown, happened]

/-- An unknown activity is never called again. -/
theorem call_refused_of_unknown (policy : OnTimeout) {r : Runner A} {a : A}
    (isUnknown : r.status a = .unknown) :
    (timedStep policy r (.base (.call a))).external = r.external := by
  simp [timedStep, runnerStep, isUnknown]

/-- **A deliberate retry is safe through the key**: a sink that deduplicates by the activity's
identifier applies every activity the runner called, each exactly once, whatever the policy and
however often a retry called it. -/
theorem keyed_retry_once (policy : OnTimeout) (events : List (TimedEvent A)) :
    (receiveAll Receiver.empty (timedRun policy Runner.fresh events).external).applied.Perm
      (timedRun policy Runner.fresh events).external.dedup :=
  exactly_once (List.nodup_dedup _) (fun _ member => List.mem_dedup.mp member)
    (fun _ member => List.mem_dedup.mpr member)

/-! ## Controls -/

namespace Controls

/-- **In the asynchronous model the effect can still come after the deadline**: sent at `s`, no
completion by `t ≥ s`, the effect at `t + 1` and the completion at `t + 2`. The call is
admissible asynchronously and not under any bound smaller than `t + 1 - s`. -/
theorem async_late_effect {s t : ℕ} (sentFirst : s ≤ t) :
    let c : Call := ⟨s, some (t + 1), some (t + 2)⟩
    AsyncCall c ∧ view c t = (s, none) ∧ (∀ Δ, Δ + s ≤ t → ¬ SyncCall Δ c) := by
  refine ⟨⟨fun e h => ?_, fun r h => ?_⟩, ?_, fun Δ small sync => ?_⟩
  · simp only [Option.some.injEq] at h ⊢; omega
  · simp only [Option.some.injEq] at h
    exact ⟨t + 1, rfl, by omega⟩
  · simp [view]
  · have := (sync.1 (t + 1) rfl).2
    dsimp only at this
    omega

/-- Positive control: the rule "done once the completion is in, unknown otherwise" is sound for
every asynchronous call, so `timeout_unknown` constrains real rules, and a completion does give a
definite verdict. -/
theorem reply_rule_sound (c : Call) (admissible : AsyncCall c) (t : ℕ) :
    Sound (if (view c t).2.isSome then .done else .unknown) c t := by
  refine ⟨fun isDone => ?_, fun isNot => ?_⟩
  · cases reply : c.replyAt with
    | none => simp [view, reply] at isDone
    | some r =>
        have arrived : r ≤ t := by
          by_contra late
          simp [view, reply, late] at isDone
        obtain ⟨e, happened, before⟩ := admissible.2 r reply
        exact ⟨e, happened, le_trans before arrived⟩
  · split at isNot <;> cases isNot

/-- The hypotheses of `timeout_unknown` are met by a rule that is not constant: the reply rule is
sound on every synchronous call, and on a timeout it answers `unknown`. -/
theorem reply_rule_meets_timeout_unknown (Δ s : ℕ) :
    (∀ c t, SyncCall Δ c → Sound (if (view c t).2.isSome then .done else .unknown) c t) ∧
      (fun v : ℕ × Option ℕ => if v.2.isSome then Verdict.done else .unknown) (s, none) = .unknown :=
  ⟨fun c t admissible => reply_rule_sound c admissible.async t, rfl⟩

/-- **A late completion is matched, not repeated.** Activity `0` is begun and called; its
deadline fires; the runner tries to call it again and is refused; the completion arrives and
finishes it. One effect. -/
theorem late_completion_deduplicated :
    (timedRun .unknown Runner.fresh
        [.base (.begin 0), .base (.call 0), .timeout 0, .base (.call 0), .complete 0]).external = [0] ∧
      (timedRun .unknown Runner.fresh
        [.base (.begin 0), .base (.call 0), .timeout 0, .base (.call 0), .complete 0]).status 0 =
        .finished := by
  decide

/-- **Timeout as failure calls twice**, with no completion at all: the callee performed the
effect and stopped before replying, which the synchronous model admits. -/
theorem timeout_as_failure_twice :
    (timedRun .retry Runner.fresh [.base (.begin 0), .base (.call 0), .timeout 0, .base (.call 0)]).external =
      [0, 0] := by
  decide

/-- **The keyed sink applies the twice-called activity once.** -/
theorem keyed_retry_applies_once :
    (receiveAll Receiver.empty
      (timedRun .retry Runner.fresh
        [.base (.begin 0), .base (.call 0), .timeout 0, .base (.call 0)]).external).applied = [0] := by
  decide

/-- Positive control: without a timeout, the call completes and the activity is finished with
one effect under either policy. -/
theorem on_time_completion (policy : OnTimeout) :
    (timedRun policy Runner.fresh [.base (.begin 0), .base (.call 0), .complete 0]).external = [0] ∧
      (timedRun policy Runner.fresh [.base (.begin 0), .base (.call 0), .complete 0]).status 0 =
        .finished := by
  cases policy <;> decide

/-- **`done` dates the effect**: an effect at time `5` establishes the evidence claim at time `3`,
while `done` is unsound there; it becomes sound at `5`. -/
theorem done_dates_effect :
    Verdict.done.toEvidence.Reads ((⟨0, some 5, none⟩ : Call).effectAt ≠ none) ∧
      ¬ Sound .done ⟨0, some 5, none⟩ 3 ∧ Sound .done ⟨0, some 5, none⟩ 5 := by
  refine ⟨by simp [Verdict.toEvidence, Mettapedia.Logic.EvidenceKinds.Verdict.Reads], ?_, ?_⟩
  · rintro ⟨dated, -⟩
    obtain ⟨e, same, le⟩ := dated rfl
    simp only [Option.some.injEq] at same
    omega
  · exact ⟨fun _ => ⟨5, rfl, le_rfl⟩, fun h => by cases h⟩

/-- **Synchronous call, positive**: sent at `0`, effect at `2`, reply at `3`: both within the
delay bound `5`. -/
theorem timely_call_sync : SyncCall 5 ⟨0, some 2, some 3⟩ := by
  refine ⟨fun e effect => ?_, fun r reply => ⟨2, rfl, ?_⟩⟩
  · cases effect; decide
  · cases reply; decide

/-- **Asynchronous call, negative**: a reply with no effect behind it is not admissible, even
asynchronously. -/
theorem reply_without_effect_not_async : ¬ AsyncCall ⟨0, none, some 3⟩ := fun async => by
  obtain ⟨e, effect, -⟩ := async.2 3 rfl
  cases effect

end Controls

end Mettapedia.GSLT.Timing.TimeoutUnknown
