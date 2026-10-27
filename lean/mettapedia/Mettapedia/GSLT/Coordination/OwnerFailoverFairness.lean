import Mettapedia.GSLT.Coordination.OwnerFailoverLiveness
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.FairRuns

/-!
# Failover liveness from weak fairness

`OwnerFailoverLiveness` assumes that the members of a quorum handle the stable candidate's
messages and that the candidate elects itself. Here those assumptions are derived from **weak
fairness** in the sense of `OccurrenceCommits.Liveness.FairRuns`: a task that is enabled at every
moment from some time on fires infinitely often.

## The system

The failover protocol is a labelled transition system (`protocolLTS`): an event is allowed when it
changes the state, that is, when its guard holds; the effect is `apply`. An idle step is added
(`LTS.withIdle`) so that every state allows a step. A run of this system is a sequence of events
(`eventsOf`, idle steps read as a refused start), and its states are those of
`OwnerFailover.trace` (`state_eq_trace`).

## The theorems

The tasks: acceptor `a` handles the candidate's request for promises (`promiseTask`); the
candidate elects itself with quorum `Q` (`electTask`); acceptor `a` handles a log `L` of the
candidate (`acceptTask`).

* **With weak fairness of these tasks, the stable candidate becomes the owner and stays the owner**
  (`fair_stable_owns`): no event has to occur at any given time; each member of the quorum either
  handles the request or has already reached the epoch through the candidate.
* **And every log it sends is chosen** (`fair_stable_log_chosen`): each member either accepts the
  log or already holds a longer log of the epoch.

Weak fairness suffices, strong fairness is not needed: each of these tasks stays enabled until it
fires or until what it would bring about holds already (`promise_or_owner`, `elect_fires`,
`accepted_extending`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.OwnerFailover

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

universe u v w

variable {V : Type u} [DecidableEq V] {P : Type v} [DecidableEq P] {C : Type w} [DecidableEq C]
variable {quorum : Finset V → Prop} [DecidablePred quorum] {fenced : Bool}
variable {valid : List C → C → Prop} [∀ log c, Decidable (valid log c)]

variable (quorum fenced valid) in
/-- The failover protocol as a labelled transition system: an event is allowed when it changes the
state. -/
def protocolLTS : LTS (State V P C) (Event V P C) where
  Allowed s ev := apply quorum fenced valid s ev ≠ s
  next := apply quorum fenced valid

variable (quorum fenced valid) in
/-- The protocol with an idle step. -/
abbrev FailoverSystem : LTS (State V P C) (Option (Event V P C)) := (protocolLTS quorum fenced valid).withIdle

/-- The events of a run, an idle step read as a start of epoch `0` by `idle` (always refused). -/
def eventsOf (idle : P) (r : Run (FailoverSystem (P := P) quorum fenced valid)) (n : ℕ) : Event V P C :=
  (r.label n).getD (.start idle 0)

theorem start_zero_refused (s : State V P C) (idle : P) :
    apply quorum fenced valid s (.start idle 0) = s := by
  simp [apply]

/-- **The states of a run from the initial state are those of `trace`.** -/
theorem state_eq_trace (idle : P) (r : Run (FailoverSystem (P := P) quorum fenced valid))
    (init : r.state 0 = State.init) : ∀ n, r.state n = trace quorum fenced valid (eventsOf idle r) n := by
  intro n
  induction n with
  | zero => exact init
  | succ n ih =>
      rw [r.step n]
      show (FailoverSystem quorum fenced valid).next (r.state n) (r.label n) =
        apply quorum fenced valid (trace quorum fenced valid (eventsOf idle r) n) (eventsOf idle r n)
      rw [← ih]
      cases h : r.label n with
      | none =>
          simp only [FailoverSystem, LTS.withIdle, eventsOf, h, Option.getD_none]
          exact (start_zero_refused _ _).symm
      | some ev => simp [FailoverSystem, LTS.withIdle, eventsOf, h, protocolLTS]

omit [DecidableEq V] [DecidableEq P] [DecidableEq C] in
/-- An event whose guard adds a message changes the state. -/
theorem ne_of_sent_cons {s s' : State V P C} {m : Msg V P C} (sent : s'.sent = m :: s.sent) : s' ≠ s := by
  intro same
  have := congrArg (fun t : State V P C => t.sent.length) same
  simp [sent] at this

/-! ## The tasks -/

/-- Acceptor `a` handles the candidate's request for promises. -/
def promiseTask (a : V) (c : P) (e : ℕ) : Option (Event V P C) → Prop :=
  LTS.liftTask fun ev => ev = .promise a c e

/-- The candidate elects itself with quorum `Q`, with some report. -/
def electTask (c : P) (Q : Finset V) : Option (Event V P C) → Prop :=
  LTS.liftTask fun ev => ∃ ae al, ev = .elect c Q ae al

/-- Acceptor `a` handles the candidate's log `L` of epoch `e`. -/
def acceptTask (a : V) (c : P) (e : ℕ) (L : List C) : Option (Event V P C) → Prop :=
  LTS.liftTask fun ev => ev = .accept a c e L

omit [DecidableEq V] [DecidableEq P] [DecidableEq C] [DecidablePred quorum] [(log : List C) → (c : C) → Decidable (valid log c)] in
/-- A best report exists among the promises of a quorum's members. -/
theorem best_report_exists {s : State V P C} (inv : Inv (quorum := quorum) (valid := valid) s)
    {Q : Finset V} (nonempty : Q.Nonempty) {who : P} {e : ℕ}
    (promised : ∀ a ∈ Q, ∃ ae al, Msg.promise a who e ae al ∈ s.sent) :
    ∃ ae al, (∃ a ∈ Q, Msg.promise a who e ae al ∈ s.sent) ∧
      ∀ a ∈ Q, ∀ m ∈ s.sent, m.BelowReport a who e ae al := by
  classical
  choose! aeOf alOf h using promised
  obtain ⟨best, inQ, isMax⟩ := Q.exists_max_image (fun a => toLex (aeOf a, (alOf a).length)) nonempty
  refine ⟨aeOf best, alOf best, ⟨best, inQ, h best inQ⟩, fun a member m inSent => ?_⟩
  cases m with
  | promise a' w e' ae' al' =>
      intro sameA sameW sameE
      subst sameA sameW sameE
      obtain ⟨_, rfl, rfl⟩ := inv.promise_unique a' w w e' ae' (aeOf a') al' (alOf a') inSent (h a' member)
      have le := isMax a' member
      rcases (Prod.Lex.le_iff).mp le with lt | ⟨eq, le'⟩
      · exact Or.inl lt
      · exact Or.inr ⟨eq, le'⟩
  | prepare => trivial
  | accept => trivial
  | accepted => trivial

section Fair

variable {c : P} {e T : ℕ} (r : Run (FailoverSystem (P := P) quorum fenced valid)) (init : r.state 0 = State.init)
include init

/-- **A member handles the request for promises, or the candidate already owns the epoch.** -/
theorem promise_or_owner (fencedOn : fenced = true)
    (stable : Stable (quorum := quorum) (fenced := fenced) (valid := valid) (eventsOf c r) c e T)
    (a : V) (fair : r.WeaklyFair (promiseTask a c e)) :
    ∃ t, T < t ∧ ((∃ ae al, Msg.promise a c e ae al ∈ (trace quorum fenced valid (eventsOf c r) t).sent) ∨
      ∃ log, ((trace quorum fenced valid (eventsOf c r) t).cand c).phase = .owner log) := by
  by_contra never
  push Not at never
  have prepared : ∀ n, T < n → Msg.prepare c e ∈ (trace quorum fenced valid (eventsOf c r) n).sent := by
    intro n after
    have first : Msg.prepare c e ∈ (trace quorum fenced valid (eventsOf c r) (T + 1)).sent := by
      show Msg.prepare c e ∈ (apply quorum fenced valid (trace quorum fenced valid (eventsOf c r) T) (eventsOf c r T)).sent
      rw [stable.starts]
      simp only [apply, if_pos (stable.above_cand c)]
      exact List.mem_cons_self ..
    exact trace_sent_mono (quorum := quorum) (fenced := fenced) (valid := valid) _ (by omega) _ first
  have below : ∀ n, T < n → ((trace quorum fenced valid (eventsOf c r) n).acc a).promised < e := by
    intro n after
    have holds := afterStart_all fencedOn stable n after
    rcases Nat.lt_or_ge ((trace quorum fenced valid (eventsOf c r) n).acc a).promised e with lt | ge
    · exact lt
    · exfalso
      have atE := le_antisymm (holds.acc_le a) ge
      rcases holds.reached a atE with ⟨ae, al, h⟩ | ⟨L, h⟩
      · exact (never n after).1 ae al h
      · obtain ⟨log, isOwner⟩ := (accepted_at_e_owner fencedOn stable after h).2
        exact (never n after).2 log isOwner
  obtain ⟨n, le, fires⟩ := fair.fires (T + 1) fun n le _ => by
    refine ⟨some (.promise a c e), rfl, ?_⟩
    show apply quorum fenced valid (r.state n) (.promise a c e) ≠ r.state n
    rw [state_eq_trace c r init n]
    apply ne_of_sent_cons (m := .promise a c e ((trace quorum fenced valid (eventsOf c r) n).acc a).acceptedEpoch ((trace quorum fenced valid (eventsOf c r) n).acc a).log)
    simp only [apply, if_pos (And.intro (prepared n (by omega)) (below n (by omega)))]
  have isPromise : eventsOf c r n = .promise a c e := by
    simp only [promiseTask, LTS.liftTask] at fires
    cases h : r.label n with
    | none => rw [h] at fires; exact absurd fires (by simp)
    | some ev =>
        rw [h] at fires
        simp only at fires
        simp [eventsOf, h, fires]
  apply (never (n + 1) (by omega)).1 ((trace quorum fenced valid (eventsOf c r) n).acc a).acceptedEpoch ((trace quorum fenced valid (eventsOf c r) n).acc a).log
  show Msg.promise a c e _ _ ∈ (apply quorum fenced valid (trace quorum fenced valid (eventsOf c r) n) (eventsOf c r n)).sent
  rw [isPromise]
  simp only [apply, if_pos (And.intro (prepared n (by omega)) (below n (by omega)))]
  exact List.mem_cons_self ..

/-- **With weak fairness, the stable candidate becomes the owner and stays the owner.** -/
theorem fair_stable_owns (fencedOn : fenced = true) (system : QuorumSystem quorum)
    (stable : Stable (quorum := quorum) (fenced := fenced) (valid := valid) (eventsOf c r) c e T)
    {Q : Finset V} (isQ : quorum Q) (fairPromise : ∀ a ∈ Q, r.WeaklyFair (promiseTask a c e))
    (fairElect : r.WeaklyFair (electTask c Q)) :
    ∃ t, T < t ∧ ∀ t', t ≤ t' → ∃ log, ((trace quorum fenced valid (eventsOf c r) t').cand c).phase = .owner log := by
  -- it suffices to reach ownership once
  suffices ∃ t, T < t ∧ ∃ log, ((trace quorum fenced valid (eventsOf c r) t).cand c).phase = .owner log by
    obtain ⟨t, after, owner⟩ := this
    exact ⟨t, after, owner_stays stable after owner⟩
  by_contra never
  push Not at never
  have each := fun a inQ => promise_or_owner r init fencedOn stable a (fairPromise a inQ)
  choose! when after which using each
  have nonempty : Q.Nonempty := by
    obtain ⟨a, inQ, -⟩ := system Q Q isQ isQ
    exact ⟨a, inQ⟩
  -- from the latest of these times, every member's promise is present and the candidate electing
  set t₀ := Q.sup when + T + 1
  have present : ∀ n, t₀ ≤ n → ∀ a ∈ Q, ∃ ae al, Msg.promise a c e ae al ∈ (trace quorum fenced valid (eventsOf c r) n).sent := by
    intro n le a inQ
    rcases which a inQ with ⟨ae, al, h⟩ | ⟨log, isOwner⟩
    · have : when a ≤ n := (Finset.le_sup inQ).trans (by omega)
      exact ⟨ae, al, trace_sent_mono (quorum := quorum) (fenced := fenced) (valid := valid) _ this _ h⟩
    · exact absurd isOwner (never (when a) (after a inQ) log)
  have electing : ∀ n, T < n → ((trace quorum fenced valid (eventsOf c r) n).cand c).phase = .electing := by
    intro n afterN
    rcases (afterStart_all fencedOn stable n afterN).cand_phase with h | ⟨log, h⟩
    · exact h
    · exact absurd h (never n afterN log)
  obtain ⟨n, le, fires⟩ := fairElect.fires t₀ fun n le _ => by
    have inv := inv_reachable fencedOn (trace_reachable (quorum := quorum) (fenced := fenced)
      (valid := valid) (eventsOf c r) n)
    have holds := afterStart_all fencedOn stable n (by omega)
    obtain ⟨ae, al, best, below⟩ := best_report_exists inv nonempty (who := c) (e := e) (present n le)
    have guard : ElectOK quorum (trace quorum fenced valid (eventsOf c r) n) c Q ae al := by
      refine ⟨electing n (by omega), isQ, fun a inQ => ?_, by rw [holds.cand_epoch]; exact best,
        by rw [holds.cand_epoch]; exact below⟩
      obtain ⟨ae', al', h⟩ := present n le a inQ
      rw [holds.cand_epoch]
      exact ⟨_, h, Msg.isPromiseFor_iff.mpr ⟨ae', al', rfl⟩⟩
    refine ⟨some (.elect c Q ae al), ⟨ae, al, rfl⟩, ?_⟩
    show apply quorum fenced valid (r.state n) (.elect c Q ae al) ≠ r.state n
    rw [state_eq_trace c r init n]
    apply ne_of_sent_cons (m := .accept c ((trace quorum fenced valid (eventsOf c r) n).cand c).epoch al)
    simp only [apply, if_pos guard]
  -- the elect step fired and changed the state: its guard held, so the candidate owns its epoch
  cases h : r.label n with
  | none => rw [h] at fires; simp [electTask, LTS.liftTask] at fires
  | some ev =>
      rw [h] at fires
      simp only [electTask, LTS.liftTask] at fires
      obtain ⟨ae, al, rfl⟩ := fires
      have allowed := r.allowed n
      rw [h] at allowed
      change apply quorum fenced valid (r.state n) (.elect c Q ae al) ≠ r.state n at allowed
      rw [state_eq_trace c r init n] at allowed
      have guard : ElectOK quorum (trace quorum fenced valid (eventsOf c r) n) c Q ae al := by
        by_contra notGuard
        apply allowed
        simp only [apply, if_neg notGuard]
      apply never (n + 1) (by omega) al
      show ((apply quorum fenced valid (trace quorum fenced valid (eventsOf c r) n) (eventsOf c r n)).cand c).phase = .owner al
      rw [show eventsOf c r n = .elect c Q ae al by simp [eventsOf, h]]
      simp only [apply, if_pos guard]
      simp

/-- **A member accepts the log, or already holds a longer log of the epoch.** -/
theorem accepted_extending (fencedOn : fenced = true) (system : QuorumSystem quorum)
    (stable : Stable (quorum := quorum) (fenced := fenced) (valid := valid) (eventsOf c r) c e T)
    {t₁ : ℕ} (afterT : T < t₁) {L : List C}
    (sentL : Msg.accept c e L ∈ (trace quorum fenced valid (eventsOf c r) t₁).sent)
    (a : V) (fair : r.WeaklyFair (acceptTask a c e L)) :
    ∃ t L', L <+: L' ∧ Msg.accepted a e L' ∈ (trace quorum fenced valid (eventsOf c r) t).sent := by
  by_contra never
  push Not at never
  have guardAt : ∀ n, t₁ ≤ n → AcceptOK fenced (trace quorum fenced valid (eventsOf c r) n) a c e L := by
    intro n le
    have inv := inv_reachable fencedOn (trace_reachable (quorum := quorum) (fenced := fenced)
      (valid := valid) (eventsOf c r) n)
    have holds := afterStart_all fencedOn stable n (by omega)
    have present : Msg.accept c e L ∈ (trace quorum fenced valid (eventsOf c r) n).sent :=
      trace_sent_mono (quorum := quorum) (fenced := fenced) (valid := valid) _ le _ sentL
    refine ⟨present, fun _ => holds.acc_le a, ?_⟩
    have notAbove : ((trace quorum fenced valid (eventsOf c r) n).acc a).acceptedEpoch ≤ e := (inv.acc_le a).trans (holds.acc_le a)
    rcases Nat.lt_or_ge ((trace quorum fenced valid (eventsOf c r) n).acc a).acceptedEpoch e with lt | ge
    · exact Or.inl lt
    · have eq := le_antisymm notAbove ge
      refine Or.inr ⟨eq, ?_⟩
      have pos : 1 ≤ e := (inv.accept_le c e L present).1
      rcases inv.acc_cur a with ⟨zero, _⟩ | current
      · omega
      · rw [eq] at current
        obtain ⟨w', src⟩ := inv.accepted_src a e _ current
        rcases accepts_comparable system inv present src with pre | pre
        · exact absurd current (never n _ pre)
        · exact pre
  obtain ⟨n, le, fires⟩ := fair.fires t₁ fun n le _ => by
    refine ⟨some (.accept a c e L), rfl, ?_⟩
    show apply quorum fenced valid (r.state n) (.accept a c e L) ≠ r.state n
    rw [state_eq_trace c r init n]
    apply ne_of_sent_cons (m := .accepted a e L)
    simp only [apply, if_pos (guardAt n le)]
  have isAccept : eventsOf c r n = .accept a c e L := by
    cases h : r.label n with
    | none => rw [h] at fires; exact absurd fires (by simp [acceptTask, LTS.liftTask])
    | some ev =>
        rw [h] at fires
        simp only [acceptTask, LTS.liftTask] at fires
        simp [eventsOf, h, fires]
  apply never (n + 1) L (List.prefix_refl _)
  show Msg.accepted a e L ∈ (apply quorum fenced valid (trace quorum fenced valid (eventsOf c r) n) (eventsOf c r n)).sent
  rw [isAccept]
  simp only [apply, if_pos (guardAt n le)]
  exact List.mem_cons_self ..

/-- **With weak fairness, every log the stable owner sends is chosen.** -/
theorem fair_stable_log_chosen (fencedOn : fenced = true) (system : QuorumSystem quorum)
    (stable : Stable (quorum := quorum) (fenced := fenced) (valid := valid) (eventsOf c r) c e T)
    {Q : Finset V} (isQ : quorum Q) {t₁ : ℕ} (afterT : T < t₁) {L : List C}
    (sentL : Msg.accept c e L ∈ (trace quorum fenced valid (eventsOf c r) t₁).sent)
    (fairAccept : ∀ a ∈ Q, r.WeaklyFair (acceptTask a c e L)) :
    ∃ t₂, Chosen quorum (trace quorum fenced valid (eventsOf c r) t₂) e L := by
  have each := fun a inQ => accepted_extending r init fencedOn system stable afterT sentL a (fairAccept a inQ)
  choose! when longer pre accepted using each
  refine ⟨Q.sup when, Q, isQ, fun a inQ => ⟨longer a, ?_, pre a inQ⟩⟩
  exact trace_sent_mono (quorum := quorum) (fenced := fenced) (valid := valid) _ (Finset.le_sup inQ) _
    (accepted a inQ)

end Fair

namespace Controls

/-- **Tasks, positive and negative**: each task holds of its own event, not of another, and not of
an idle step. -/
theorem task_controls :
    promiseTask (V := Fin 3) (P := Bool) (C := Bool) 0 true 1 (some (.promise 0 true 1)) ∧
      ¬ promiseTask (V := Fin 3) (P := Bool) (C := Bool) 0 true 1 (some (.promise 1 true 1)) ∧
      electTask (V := Fin 3) (P := Bool) (C := Bool) true {0, 1} (some (.elect true {0, 1} 0 [])) ∧
      ¬ electTask (V := Fin 3) (P := Bool) (C := Bool) true {0, 1} (some (.elect true {0} 0 [])) ∧
      acceptTask (V := Fin 3) (P := Bool) (C := Bool) 0 true 1 [true] (some (.accept 0 true 1 [true])) ∧
      ¬ acceptTask (V := Fin 3) (P := Bool) (C := Bool) 0 true 1 [true] none := by
  refine ⟨rfl, ?_, ⟨0, [], rfl⟩, ?_, rfl, fun h => h⟩
  · simp only [promiseTask, LTS.liftTask, Event.promise.injEq]
    decide
  · rintro ⟨ae, al, h⟩
    simp only [Event.elect.injEq] at h
    exact absurd h.2.1 (by decide)

end Controls

end Mettapedia.GSLT.Coordination.OwnerFailover
