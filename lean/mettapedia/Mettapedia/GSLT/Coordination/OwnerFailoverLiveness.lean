import Mettapedia.GSLT.Coordination.OwnerFailover
import Mettapedia.GSLT.Timing.ClockModels

/-!
# Owner failover is live with a stable candidate, a correct quorum and eventual delivery

By the theorem of Fischer, Lynch and Paterson (`CrashConsensusImpossibility`) the failover
protocol of `OwnerFailover` cannot terminate in every asynchronous run. This module proves what it
does do under the standard extra assumption, and shows the assumption is needed.

## Liveness over infinite runs

An infinite run is a sequence of events from the initial state (`trace`). From some point `T` on:

* **one candidate is stable**: at `T` it starts an epoch above every epoch in use, and after `T`
  nobody starts an epoch (`Stable`);
* **a quorum of acceptors is correct and reachable**: each of them eventually handles the
  candidate's request for promises, and each eventually handles each log the candidate sends;
* the candidate is correct: it elects itself with the best report of the promises it collected.

Interleaved with these, any other event may happen: stale owners' messages, other acceptors'
steps, repeated deliveries.

* **The stable candidate becomes the owner and stays the owner** (`stable_candidate_owns`).
* **Every log it sends is chosen** (`stable_owner_log_chosen`): the state it took over, and every
  command it appends.

## Where the stability comes from: timeouts under partial synchrony

A candidate starts an epoch only when its election timer passes without news from an owner. Under
the second form of partial synchrony (`Timing.eventualBound`), an owner that sends news every `h`
real ticks reaches every candidate within `h + Δ` after stabilization; a timer of `D` local units
re-armed by every piece of news never passes when `fast · (h + Δ) < den · D`
(`timer_never_passes`, from `Timing.ClockModels.passed_not_early_after`). So after stabilization
no other candidate starts an epoch, which is the stability assumption.

## Controls

* `Controls.dueling_nothing_chosen`: two candidates that keep starting higher epochs before the
  other's logs are accepted: in every state of the infinite run, nothing is chosen. This is the
  livelock that stability rules out.
* `Controls.unreachable_quorum_nothing_chosen`: with a stable candidate but only a minority of
  acceptors handling its messages, its log is never chosen.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.OwnerFailover

open Mettapedia.GSLT.Coordination.MajorityEpochs

universe u v w

variable {V : Type u} [DecidableEq V] {P : Type v} [DecidableEq P] {C : Type w} [DecidableEq C]
variable {quorum : Finset V → Prop} [DecidablePred quorum] {fenced : Bool}
variable {valid : List C → C → Prop} [∀ log c, Decidable (valid log c)]

variable (quorum fenced valid) in
/-- An infinite run from the initial state: the state after the first `n` events. -/
def trace (events : ℕ → Event V P C) : ℕ → State V P C
  | 0 => State.init
  | n + 1 => apply quorum fenced valid (trace events n) (events n)

theorem trace_reachable (events : ℕ → Event V P C) (n : ℕ) :
    Reachable quorum fenced valid (trace quorum fenced valid events n) := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
      obtain ⟨before, eq⟩ := ih
      refine ⟨before ++ [events n], ?_⟩
      rw [run_append, ← eq]
      rfl

theorem trace_sent_mono (events : ℕ → Event V P C) {n m : ℕ} (le : n ≤ m) :
    ∀ msg ∈ (trace quorum fenced valid events n).sent, msg ∈ (trace quorum fenced valid events m).sent := by
  induction le with
  | refl => exact fun _ h => h
  | step _ ih => exact fun msg h => sent_apply _ _ msg (ih msg h)

/-! ## Stability -/

/-- **A stable candidate from `T` on**: at `T` the candidate `c` starts epoch `e`, above every
candidate's epoch and every acceptor's promise, and after `T` nobody starts an epoch: every start
event after `T` is refused (changes nothing). -/
structure Stable (events : ℕ → Event V P C) (c : P) (e T : ℕ) : Prop where
  starts : events T = .start c e
  above_cand : ∀ w, ((trace quorum fenced valid events T).cand w).epoch < e
  above_acc : ∀ a, ((trace quorum fenced valid events T).acc a).promised < e
  quiet : ∀ t, T < t → ∀ w e', events t = .start w e' →
    apply quorum fenced valid (trace quorum fenced valid events t) (events t) =
      trace quorum fenced valid events t

/-- What holds of every state after a stable start: the candidate is at epoch `e`, every other
candidate is below it, and no acceptor has promised above it. An acceptor that has reached `e`
promised it to the candidate or accepted one of its logs. -/
structure AfterStart (s : State V P C) (c : P) (e : ℕ) : Prop where
  cand_epoch : (s.cand c).epoch = e
  cand_phase : (s.cand c).phase = .electing ∨ ∃ log, (s.cand c).phase = .owner log
  others : ∀ w, w ≠ c → (s.cand w).epoch < e
  acc_le : ∀ a, (s.acc a).promised ≤ e
  reached : ∀ a, (s.acc a).promised = e →
    (∃ ae al, Msg.promise a c e ae al ∈ s.sent) ∨ ∃ L, Msg.accepted a e L ∈ s.sent

section Stable

variable {events : ℕ → Event V P C} {c : P} {e T : ℕ}

theorem afterStart_first
    (stable : Stable (quorum := quorum) (fenced := fenced) (valid := valid) events c e T) :
    AfterStart (trace quorum fenced valid events (T + 1)) c e := by
  have higher := stable.above_cand c
  show AfterStart (apply quorum fenced valid (trace quorum fenced valid events T) (events T)) c e
  rw [stable.starts]
  simp only [apply, if_pos higher]
  refine ⟨by simp, by simp, fun w apart => ?_, fun a => (stable.above_acc a).le, fun a reached => ?_⟩
  · simp only [Function.update_of_ne apart]; exact stable.above_cand w
  · dsimp only at reached
    have := stable.above_acc a
    omega

theorem afterStart_step (fencedOn : fenced = true)
    (stable : Stable (quorum := quorum) (fenced := fenced) (valid := valid) events c e T) {t : ℕ}
    (after : T < t) (holds : AfterStart (trace quorum fenced valid events t) c e) :
    AfterStart (trace quorum fenced valid events (t + 1)) c e := by
  set s := trace quorum fenced valid events t
  have inv := inv_reachable fencedOn (trace_reachable (quorum := quorum) (fenced := fenced)
    (valid := valid) events t)
  have candLe : ∀ w, (s.cand w).epoch ≤ e := fun w => by
    by_cases same : w = c
    · subst same; exact holds.cand_epoch.le
    · exact (holds.others w same).le
  show AfterStart (apply quorum fenced valid s (events t)) c e
  have refused := stable.quiet t after
  cases hev : events t with
  | start w e' =>
      have same := refused w e' hev
      rw [hev] at same
      rw [same]
      exact holds
  | promise a w e' =>
      simp only [apply]
      split_ifs with guard
      · obtain ⟨prepared, below⟩ := guard
        have epochLe : e' ≤ e := (inv.prepare_le w e' prepared).trans (candLe w)
        refine ⟨holds.cand_epoch, holds.cand_phase, holds.others, fun b => ?_, fun b reached => ?_⟩
        · by_cases same : b = a
          · subst same; simp only [Function.update_self]; exact epochLe
          · simp only [Function.update_of_ne same]; exact holds.acc_le b
        · by_cases same : b = a
          · subst same
            simp only [Function.update_self] at reached
            subst reached
            have isC : w = c := by
              by_contra apart
              have := (inv.prepare_le w _ prepared).trans_lt (holds.others w apart)
              omega
            subst isC
            exact Or.inl ⟨_, _, List.mem_cons_self ..⟩
          · simp only [Function.update_of_ne same] at reached
            rcases holds.reached b reached with ⟨ae, al, h⟩ | ⟨L, h⟩
            · exact Or.inl ⟨ae, al, List.mem_cons_of_mem _ h⟩
            · exact Or.inr ⟨L, List.mem_cons_of_mem _ h⟩
      · exact holds
  | elect w Q ae al =>
      simp only [apply]
      split_ifs with guard
      · refine ⟨?_, ?_, fun v apart => ?_, holds.acc_le, fun b reached => ?_⟩
        · by_cases same : c = w
          · subst same; simp [holds.cand_epoch]
          · simp only [Function.update_of_ne same]; exact holds.cand_epoch
        · by_cases same : c = w
          · subst same; simp
          · simp only [Function.update_of_ne same]; exact holds.cand_phase
        · by_cases same : v = w
          · subst same; simp only [Function.update_self]; exact holds.others v apart
          · simp only [Function.update_of_ne same]; exact holds.others v apart
        · rcases holds.reached b reached with ⟨ae', al', h⟩ | ⟨L, h⟩
          · exact Or.inl ⟨ae', al', List.mem_cons_of_mem _ h⟩
          · exact Or.inr ⟨L, List.mem_cons_of_mem _ h⟩
      · exact holds
  | propose w cmd =>
      simp only [apply]
      rcases phaseIs : (s.cand w).phase with _ | _ | log
      · exact holds
      · exact holds
      · simp only
        split_ifs with ok
        · refine ⟨?_, ?_, fun v apart => ?_, holds.acc_le, fun b reached => ?_⟩
          · by_cases same : c = w
            · subst same; simp [holds.cand_epoch]
            · simp only [Function.update_of_ne same]; exact holds.cand_epoch
          · by_cases same : c = w
            · subst same; simp
            · simp only [Function.update_of_ne same]; exact holds.cand_phase
          · by_cases same : v = w
            · subst same; simp only [Function.update_self]; exact holds.others v apart
            · simp only [Function.update_of_ne same]; exact holds.others v apart
          · rcases holds.reached b reached with ⟨ae', al', h⟩ | ⟨L, h⟩
            · exact Or.inl ⟨ae', al', List.mem_cons_of_mem _ h⟩
            · exact Or.inr ⟨L, List.mem_cons_of_mem _ h⟩
        · exact holds
  | accept a w e' L =>
      simp only [apply]
      split_ifs with guard
      · obtain ⟨sentAccept, _, _⟩ := guard
        have epochLe : e' ≤ e := (inv.accept_le w e' L sentAccept).2.trans (candLe w)
        refine ⟨holds.cand_epoch, holds.cand_phase, holds.others, fun b => ?_, fun b reached => ?_⟩
        · by_cases same : b = a
          · subst same; simp only [Function.update_self]; exact max_le (holds.acc_le b) epochLe
          · simp only [Function.update_of_ne same]; exact holds.acc_le b
        · by_cases same : b = a
          · subst same
            simp only [Function.update_self] at reached
            rcases Nat.lt_or_ge (s.acc b).promised e with lt | ge
            · have : e' = e := by
                rcases le_total (s.acc b).promised e' with h | h
                · rw [max_eq_right h] at reached; exact reached
                · rw [max_eq_left h] at reached; omega
              subst this
              exact Or.inr ⟨L, List.mem_cons_self ..⟩
            · have atE : (s.acc b).promised = e := le_antisymm (holds.acc_le b) ge
              rcases holds.reached b atE with ⟨ae, al, h⟩ | ⟨L', h⟩
              · exact Or.inl ⟨ae, al, List.mem_cons_of_mem _ h⟩
              · exact Or.inr ⟨L', List.mem_cons_of_mem _ h⟩
          · simp only [Function.update_of_ne same] at reached
            rcases holds.reached b reached with ⟨ae, al, h⟩ | ⟨L', h⟩
            · exact Or.inl ⟨ae, al, List.mem_cons_of_mem _ h⟩
            · exact Or.inr ⟨L', List.mem_cons_of_mem _ h⟩
      · exact holds

theorem afterStart_all (fencedOn : fenced = true)
    (stable : Stable (quorum := quorum) (fenced := fenced) (valid := valid) events c e T) :
    ∀ t, T < t → AfterStart (trace quorum fenced valid events t) c e := by
  intro t after
  induction t, after using Nat.le_induction with
  | base => exact afterStart_first stable
  | succ t le ih => exact afterStart_step fencedOn stable (by omega) ih

/-- Once the stable candidate owns its epoch, it stays the owner. -/
theorem owner_stays
    (stable : Stable (quorum := quorum) (fenced := fenced) (valid := valid) events c e T) {t : ℕ}
    (after : T < t) (owner : ∃ log, ((trace quorum fenced valid events t).cand c).phase = .owner log) :
    ∀ t', t ≤ t' → ∃ log, ((trace quorum fenced valid events t').cand c).phase = .owner log := by
  intro t' le
  induction t', le using Nat.le_induction with
  | base => exact owner
  | succ t' le ih =>
      obtain ⟨log, isOwner⟩ := ih
      set s := trace quorum fenced valid events t'
      show ∃ log, ((apply quorum fenced valid s (events t')).cand c).phase = .owner log
      cases hev : events t' with
      | start w e' =>
          have same := stable.quiet t' (by omega) w e' hev
          rw [hev] at same
          rw [same]
          exact ⟨log, isOwner⟩
      | promise a w e' =>
          refine ⟨log, ?_⟩
          simp only [apply]; split_ifs <;> exact isOwner
      | elect w Q ae al =>
          simp only [apply]
          split_ifs with guard
          · by_cases same : c = w
            · subst same
              have := guard.1
              rw [isOwner] at this; cases this
            · exact ⟨log, by simp only [Function.update_of_ne same]; exact isOwner⟩
          · exact ⟨log, isOwner⟩
      | propose w cmd =>
          simp only [apply]
          rcases phaseIs : (s.cand w).phase with _ | _ | log'
          · exact ⟨log, isOwner⟩
          · exact ⟨log, isOwner⟩
          · simp only
            split_ifs
            · by_cases same : c = w
              · subst same; exact ⟨log' ++ [cmd], by simp⟩
              · exact ⟨log, by simp only [Function.update_of_ne same]; exact isOwner⟩
            · exact ⟨log, isOwner⟩
      | accept a w e' L =>
          refine ⟨log, ?_⟩
          simp only [apply]; split_ifs <;> exact isOwner

/-- An acceptor's message for epoch `e` concerns the stable candidate's logs. -/
theorem accepted_at_e_owner (fencedOn : fenced = true)
    (stable : Stable (quorum := quorum) (fenced := fenced) (valid := valid) events c e T) {t : ℕ}
    (after : T < t) {a : V} {L : List C}
    (accepted : Msg.accepted a e L ∈ (trace quorum fenced valid events t).sent) :
    Msg.accept c e L ∈ (trace quorum fenced valid events t).sent ∧
      ∃ log, ((trace quorum fenced valid events t).cand c).phase = .owner log := by
  have inv := inv_reachable fencedOn (trace_reachable (quorum := quorum) (fenced := fenced)
    (valid := valid) events t)
  have holds := afterStart_all fencedOn stable t after
  obtain ⟨w, src⟩ := inv.accepted_src a e L accepted
  have isC : w = c := by
    by_contra apart
    have := (inv.accept_le w e L src).2
    have := holds.others w apart
    omega
  subst isC
  refine ⟨src, ?_⟩
  rcases holds.cand_phase with electing | owner
  · have := inv.electing_silent w electing L
    rw [holds.cand_epoch] at this
    exact absurd src this
  · exact owner

/-- **The stable candidate becomes the owner of its epoch and stays the owner**: once every member
of a quorum has handled its request for promises, and it then elects itself with the best report
it holds. -/
theorem stable_candidate_owns (fencedOn : fenced = true)
    (stable : Stable (quorum := quorum) (fenced := fenced) (valid := valid) events c e T)
    {Q : Finset V} (isQ : quorum Q) {tE : ℕ} {ae : ℕ} {al : List C}
    (promised : ∀ a ∈ Q, ∃ t, T < t ∧ t < tE ∧ events t = .promise a c e)
    (elects : events tE = .elect c Q ae al)
    (best : ∃ a ∈ Q, Msg.promise a c e ae al ∈ (trace quorum fenced valid events tE).sent)
    (bestBelow : ∀ a ∈ Q, ∀ m ∈ (trace quorum fenced valid events tE).sent, m.BelowReport a c e ae al)
    (afterT : T < tE) :
    ∀ t', tE < t' → ∃ log, ((trace quorum fenced valid events t').cand c).phase = .owner log := by
  apply owner_stays stable (t := tE + 1) (by omega)
  · set s := trace quorum fenced valid events tE
    have holds := afterStart_all fencedOn stable tE afterT
    rcases holds.cand_phase with electing | owner
    · -- every member of the quorum has promised
      have present : ∀ a ∈ Q, ∃ m ∈ s.sent, m.IsPromiseFor a c (s.cand c).epoch := by
        intro a inQ
        obtain ⟨t, after, before, isPromise⟩ := promised a inQ
        have prepared : Msg.prepare c e ∈ (trace quorum fenced valid events t).sent := by
          have := trace_sent_mono (quorum := quorum) (fenced := fenced) (valid := valid) events
            (show T + 1 ≤ t by omega)
          apply this
          show Msg.prepare c e ∈ (apply quorum fenced valid (trace quorum fenced valid events T) (events T)).sent
          rw [stable.starts]
          simp only [apply, if_pos (stable.above_cand c)]
          exact List.mem_cons_self ..
        have holdsT := afterStart_all fencedOn stable t after
        have result : (∃ ae al, Msg.promise a c e ae al ∈ (trace quorum fenced valid events (t + 1)).sent) ∨
            ∃ L, Msg.accepted a e L ∈ (trace quorum fenced valid events (t + 1)).sent := by
          show (∃ ae al, Msg.promise a c e ae al ∈
              (apply quorum fenced valid (trace quorum fenced valid events t) (events t)).sent) ∨
            ∃ L, Msg.accepted a e L ∈
              (apply quorum fenced valid (trace quorum fenced valid events t) (events t)).sent
          rw [isPromise]
          simp only [apply]
          split_ifs with guard
          · exact Or.inl ⟨_, _, List.mem_cons_self ..⟩
          · have atE : ((trace quorum fenced valid events t).acc a).promised = e := by
              have := holdsT.acc_le a
              by_contra ne
              exact guard ⟨prepared, by omega⟩
            exact holdsT.reached a atE
        rcases result with ⟨ae', al', h⟩ | ⟨L, h⟩
        · refine ⟨_, trace_sent_mono (quorum := quorum) (fenced := fenced) (valid := valid) events
            (show t + 1 ≤ tE by omega) _ h, ?_⟩
          rw [holds.cand_epoch]
          exact ⟨rfl, rfl, rfl⟩
        · have owned := (accepted_at_e_owner fencedOn stable (t := tE) afterT
            (trace_sent_mono (quorum := quorum) (fenced := fenced) (valid := valid) events
              (show t + 1 ≤ tE by omega) _ h)).2
          obtain ⟨log, isOwner⟩ := owned
          rw [electing] at isOwner; cases isOwner
      have guard : ElectOK quorum s c Q ae al := by
        rw [holds.cand_epoch] at present
        refine ⟨electing, isQ, ?_, ?_, ?_⟩
        · rw [holds.cand_epoch]; exact present
        · rw [holds.cand_epoch]; exact best
        · rw [holds.cand_epoch]; exact bestBelow
      refine ⟨al, ?_⟩
      show ((apply quorum fenced valid s (events tE)).cand c).phase = .owner al
      rw [elects]
      simp only [apply, if_pos guard]
      simp
    · obtain ⟨log, isOwner⟩ := owner
      have := owner_stays stable afterT ⟨log, isOwner⟩ (tE + 1) (by omega)
      exact this

/-- **Every log the stable owner sends is chosen**, once each member of a correct quorum has handled
it. -/
theorem stable_owner_log_chosen (fencedOn : fenced = true) (system : QuorumSystem quorum)
    (stable : Stable (quorum := quorum) (fenced := fenced) (valid := valid) events c e T)
    {Q : Finset V} (isQ : quorum Q) {t₁ : ℕ} (afterT : T < t₁) {L : List C}
    (sentL : Msg.accept c e L ∈ (trace quorum fenced valid events t₁).sent)
    (delivered : ∀ a ∈ Q, ∃ t, t₁ ≤ t ∧ events t = .accept a c e L) :
    ∃ t₂, Chosen quorum (trace quorum fenced valid events t₂) e L := by
  -- after its delivery, each member holds a log of epoch `e` that extends `L`
  have each : ∀ a ∈ Q, ∃ t, ∃ L', L <+: L' ∧ Msg.accepted a e L' ∈ (trace quorum fenced valid events t).sent := by
    intro a inQ
    obtain ⟨t, later, isAccept⟩ := delivered a inQ
    have inv := inv_reachable fencedOn (trace_reachable (quorum := quorum) (fenced := fenced)
      (valid := valid) events t)
    have holds := afterStart_all fencedOn stable t (by omega)
    set s := trace quorum fenced valid events t
    have present : Msg.accept c e L ∈ s.sent :=
      trace_sent_mono (quorum := quorum) (fenced := fenced) (valid := valid) events later _ sentL
    by_cases guard : AcceptOK fenced s a c e L
    · refine ⟨t + 1, L, List.prefix_refl _, ?_⟩
      show Msg.accepted a e L ∈ (apply quorum fenced valid s (events t)).sent
      rw [isAccept]
      simp only [apply, if_pos guard]
      exact List.mem_cons_self ..
    · -- the guard fails only because the acceptor already holds a longer log of epoch `e`
      have notAbove : (s.acc a).acceptedEpoch ≤ e := (inv.acc_le a).trans (holds.acc_le a)
      have atE : (s.acc a).acceptedEpoch = e ∧ ¬ (s.acc a).log <+: L := by
        by_contra no
        apply guard
        refine ⟨present, fun _ => holds.acc_le a, ?_⟩
        rcases Nat.lt_or_ge (s.acc a).acceptedEpoch e with lt | ge
        · exact Or.inl lt
        · refine Or.inr ⟨le_antisymm notAbove ge, ?_⟩
          by_contra notPrefix
          exact no ⟨le_antisymm notAbove ge, notPrefix⟩
      obtain ⟨eq, notPrefix⟩ := atE
      have pos : 1 ≤ e := (inv.accept_le c e L present).1
      rcases inv.acc_cur a with ⟨zero, _⟩ | current
      · omega
      · rw [eq] at current
        obtain ⟨w, src⟩ := inv.accepted_src a e _ current
        rcases accepts_comparable system inv present src with pre | pre
        · exact ⟨t, _, pre, current⟩
        · exact absurd pre notPrefix
  choose! when longer pre accepted using each
  -- the latest of these times
  obtain ⟨tMax, bound⟩ : ∃ tMax, ∀ a ∈ Q, when a ≤ tMax :=
    ⟨Q.sup when, fun a inQ => Finset.le_sup inQ⟩
  refine ⟨tMax, Q, isQ, fun a inQ => ⟨longer a, ?_, pre a inQ⟩⟩
  exact trace_sent_mono (quorum := quorum) (fenced := fenced) (valid := valid) events (bound a inQ) _
    (accepted a inQ)

end Stable

/-! ## Stability from timeouts under partial synchrony -/

section Timers

open Mettapedia.GSLT.Timing

/-- **A timer re-armed often enough never passes.** A timer of `D` units of clock `c` is re-armed
at real times `arm 0 < arm 1 < …`, all after stabilization, each at most `R` real ticks after the
one before. If the clock's rate is at most `fast / den` after stabilization and
`fast · R < den · D`, the deadline armed at `arm k` has not passed when the next arming comes, at
any `k`. -/
theorem timer_never_passes {c : Clock} {gst den slow fast D R : ℕ}
    (bounds : RateBoundsAfter c gst den slow fast) (margin : fast * R < den * D) (arm : ℕ → ℕ)
    (afterGst : ∀ k, gst ≤ arm k) (spacing : ∀ k, arm (k + 1) ≤ arm k + R) :
    ∀ k t, arm k ≤ t → t ≤ arm (k + 1) → ¬ Passed c (arm k) D t := by
  intro k t _ before passed
  have early := passed_not_early_after bounds (afterGst k) passed
  have : t - arm k ≤ R := by have := spacing k; omega
  have : fast * (t - arm k) ≤ fast * R := Nat.mul_le_mul_left fast this
  omega

/-- The same, read in a timing of the second form of partial synchrony: news sent every `h` real
ticks and delayed at most `Δ` reaches the candidate within `h + Δ`, so a candidate whose timer is
re-armed by each piece of news never starts an epoch after stabilization when
`(nominal + num) · (h + Δ) < D`. -/
theorem news_keeps_timer {Pr : Type u} {T : Environment Pr} {Δ nominal num : ℕ}
    {gst : ℕ} (delays : DelaysWithinAfter T.delay gst Δ)
    (rates : ∀ p, RateBoundsAfter (T.clock p) gst 1 (nominal - num) (nominal + num))
    {owner candidate : Pr} {h D : ℕ} (margin : (nominal + num) * (h + Δ) < 1 * D)
    (send : ℕ → ℕ) (sendAfter : ∀ k, gst ≤ send k) (period : ∀ k, send (k + 1) ≤ send k + h)
    (arrive : ℕ → ℕ) (arrival : ∀ k, arrive k = send k + T.delay owner candidate (send k)) :
    ∀ k t, arrive k ≤ t → t ≤ arrive (k + 1) → ¬ Passed (T.clock candidate) (arrive k) D t := by
  refine timer_never_passes (rates candidate) margin arrive (fun k => ?_) (fun k => ?_)
  · rw [arrival]; exact (sendAfter k).trans (Nat.le_add_right _ _)
  · rw [arrival, arrival]
    have := delays owner candidate (send (k + 1)) (sendAfter _)
    have := period k
    omega

end Timers

/-! ## Controls -/

namespace Controls

/-- Any log is admitted: the controls are about the protocol, not the commands. -/
abbrev any : List Bool → Bool → Prop := fun _ _ => True

/-! ### Dueling candidates -/

/-- Round `k` of two dueling candidates, with one acceptor: `true` starts epoch `2k + 1` and is
promised it; the stale log of `false` from epoch `2k` arrives; `true` elects itself; `false`
starts `2k + 2` and is promised it; `true`'s log of epoch `2k + 1` arrives; `false` elects
itself. -/
def duel (n : ℕ) : Event (Fin 1) Bool Bool :=
  match n % 8 with
  | 0 => .start true (2 * (n / 8) + 1)
  | 1 => .promise 0 true (2 * (n / 8) + 1)
  | 2 => .accept 0 false (2 * (n / 8)) []
  | 3 => .elect true {0} 0 []
  | 4 => .start false (2 * (n / 8) + 2)
  | 5 => .promise 0 false (2 * (n / 8) + 2)
  | 6 => .accept 0 true (2 * (n / 8) + 1) []
  | _ => .elect false {0} 0 []

/-- No acceptor has accepted anything. -/
def NoAccepted (s : State (Fin 1) Bool Bool) : Prop := ∀ a e L, Msg.accepted a e L ∉ s.sent

/-- The promised epoch of the acceptor at each point of a round. -/
def promisedAt (n : ℕ) : ℕ := if n % 8 < 2 then 2 * (n / 8) else if n % 8 < 6 then 2 * (n / 8) + 1
  else 2 * (n / 8) + 2

/-- What holds at each point of the dueling run. -/
structure DuelInv (n : ℕ) (s : State (Fin 1) Bool Bool) : Prop where
  none : NoAccepted s
  promised : (s.acc 0).promised = promisedAt n
  epochTrue : n % 8 = 0 → (s.cand true).epoch ≤ 2 * (n / 8)
  epochTrueLe : (s.cand true).epoch ≤ 2 * (n / 8) + 1
  epochFalse : n % 8 ≤ 4 → (s.cand false).epoch ≤ 2 * (n / 8)
  epochFalseLe : (s.cand false).epoch ≤ 2 * (n / 8) + 2
  prepTrue : 1 ≤ n % 8 → Msg.prepare true (2 * (n / 8) + 1) ∈ s.sent
  prepFalse : 5 ≤ n % 8 → Msg.prepare false (2 * (n / 8) + 2) ∈ s.sent

theorem apply_elect_facts (s : State (Fin 1) Bool Bool) (who : Bool) (Q : Finset (Fin 1)) (ae : ℕ)
    (al : List Bool) :
    (apply (IsMajority (V := Fin 1)) true any s (.elect who Q ae al)).acc = s.acc ∧
      (∀ w, ((apply (IsMajority (V := Fin 1)) true any s (.elect who Q ae al)).cand w).epoch =
        (s.cand w).epoch) ∧
      (∀ m ∈ (apply (IsMajority (V := Fin 1)) true any s (.elect who Q ae al)).sent,
        m ∈ s.sent ∨ ∃ e L, m = .accept who e L) := by
  simp only [apply]
  split_ifs
  · refine ⟨rfl, fun w => ?_, fun m member => ?_⟩
    · by_cases same : w = who
      · subst same; simp
      · simp [Function.update_of_ne same]
    · rcases List.mem_cons.mp member with rfl | old
      · exact Or.inr ⟨_, _, rfl⟩
      · exact Or.inl old
  · exact ⟨rfl, fun _ => rfl, fun m member => Or.inl member⟩

theorem duelInv_zero : DuelInv 0 (State.init : State (Fin 1) Bool Bool) where
  none _ _ _ h := by simp [State.init] at h
  promised := by simp [State.init, promisedAt]
  epochTrue _ := by simp [State.init]
  epochTrueLe := by simp [State.init]
  epochFalse _ := by simp [State.init]
  epochFalseLe := by simp [State.init]
  prepTrue h := by simp at h
  prepFalse h := by simp at h

theorem duelInv_step {n : ℕ} {s : State (Fin 1) Bool Bool} (inv : DuelInv n s) :
    DuelInv (n + 1) (apply (IsMajority (V := Fin 1)) true any s (duel n)) := by
  obtain ⟨none, promised, epochTrue, epochTrueLe, epochFalse, epochFalseLe, prepTrue, prepFalse⟩ := inv
  have phase : n % 8 < 8 := Nat.mod_lt _ (by decide)
  set k := n / 8 with hk
  have split : n = 8 * k + n % 8 := (Nat.div_add_mod n 8).symm
  rcases (by omega : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨
      n % 8 = 6 ∨ n % 8 = 7) with j | j | j | j | j | j | j | j
  · -- start true (2k + 1)
    have next : (n + 1) % 8 = 1 ∧ (n + 1) / 8 = k := by omega
    have ev : duel n = .start true (2 * k + 1) := by simp [duel, j, hk]
    have higher : (s.cand true).epoch < 2 * k + 1 := by have := epochTrue j; omega
    rw [ev]
    simp only [apply, if_pos higher]
    refine ⟨fun a e L h => ?_, ?_, fun h => by (try dsimp only); omega, ?_, fun _ => ?_, ?_, fun _ => ?_, fun h => by (try dsimp only); omega⟩
    all_goals try dsimp only
    · rcases List.mem_cons.mp h with h | h
      · cases h
      · exact none a e L h
    · rw [promised]; simp [promisedAt, j, next.1, next.2, ← hk]
    · simp [next]
    · simp only [Function.update_of_ne (show false ≠ true by decide), next]; exact epochFalse (by omega)
    · simp only [Function.update_of_ne (show false ≠ true by decide), next]; omega
    · simp [next]
  · -- promise 0 true (2k + 1)
    have next : (n + 1) % 8 = 2 ∧ (n + 1) / 8 = k := by omega
    have ev : duel n = .promise 0 true (2 * k + 1) := by simp [duel, j, hk]
    have prepared := prepTrue (by omega)
    have below : (s.acc 0).promised < 2 * k + 1 := by rw [promised]; simp [promisedAt, j, ← hk]
    rw [ev]
    simp only [apply, if_pos (And.intro prepared below)]
    refine ⟨fun a e L h => ?_, ?_, fun h => by (try dsimp only); omega, ?_, fun h => by (try dsimp only); omega, ?_, fun _ => ?_,
      fun h => by (try dsimp only); omega⟩
    all_goals try dsimp only
    · rcases List.mem_cons.mp h with h | h
      · cases h
      · exact none a e L h
    · simp [promisedAt, next.1, next.2]
    · simp only [next]; exact epochTrueLe
    · simp only [next]; exact epochFalseLe
    · simp only [next]; exact List.mem_cons_of_mem _ prepared
  · -- the stale log of epoch 2k is refused
    have next : (n + 1) % 8 = 3 ∧ (n + 1) / 8 = k := by omega
    have ev : duel n = .accept 0 false (2 * k) [] := by simp [duel, j, hk]
    have stale : 2 * k < (s.acc 0).promised := by rw [promised]; simp [promisedAt, j, ← hk]
    rw [ev, stale_accept_refused rfl s stale]
    refine ⟨none, ?_, fun h => by omega, ?_, fun h => ?_, ?_, fun _ => ?_, fun h => by omega⟩
    · rw [promised]; simp [promisedAt, j, next.1, next.2, ← hk]
    · simp only [next]; exact epochTrueLe
    · simp only [next]; exact epochFalse (by omega)
    · simp only [next]; exact epochFalseLe
    · simp only [next]; exact prepTrue (by omega)
  · -- true elects itself (or not)
    have next : (n + 1) % 8 = 4 ∧ (n + 1) / 8 = k := by omega
    have ev : duel n = .elect true {0} 0 [] := by simp [duel, j]
    rw [ev]
    obtain ⟨accSame, epochSame, sentFrom⟩ := apply_elect_facts s true {0} 0 []
    refine ⟨fun a e L h => ?_, ?_, fun h => by omega, ?_, fun h => ?_, ?_, fun _ => ?_, fun h => by omega⟩
    · rcases sentFrom _ h with h | ⟨_, _, h⟩
      · exact none a e L h
      · cases h
    · rw [accSame, promised]; simp [promisedAt, j, next.1, next.2, ← hk]
    · rw [epochSame]; simp only [next]; exact epochTrueLe
    · rw [epochSame]; simp only [next]; exact epochFalse (by omega)
    · rw [epochSame]; simp only [next]; exact epochFalseLe
    · simp only [next]; exact sent_apply s _ _ (prepTrue (by omega))
  · -- start false (2k + 2)
    have next : (n + 1) % 8 = 5 ∧ (n + 1) / 8 = k := by omega
    have ev : duel n = .start false (2 * k + 2) := by simp [duel, j, hk]
    have higher : (s.cand false).epoch < 2 * k + 2 := by have := epochFalse (by omega); omega
    rw [ev]
    simp only [apply, if_pos higher]
    refine ⟨fun a e L h => ?_, ?_, fun h => by (try dsimp only); omega, ?_, fun h => by (try dsimp only); omega, ?_, fun _ => ?_, fun _ => ?_⟩
    all_goals try dsimp only
    · rcases List.mem_cons.mp h with h | h
      · cases h
      · exact none a e L h
    · rw [promised]; simp [promisedAt, j, next.1, next.2, ← hk]
    · simp only [Function.update_of_ne (show true ≠ false by decide), next]; exact epochTrueLe
    · simp [next]
    · simp only [next]; exact List.mem_cons_of_mem _ (prepTrue (by omega))
    · simp [next]
  · -- promise 0 false (2k + 2)
    have next : (n + 1) % 8 = 6 ∧ (n + 1) / 8 = k := by omega
    have ev : duel n = .promise 0 false (2 * k + 2) := by simp [duel, j, hk]
    have prepared := prepFalse (by omega)
    have below : (s.acc 0).promised < 2 * k + 2 := by rw [promised]; simp [promisedAt, j, ← hk]
    rw [ev]
    simp only [apply, if_pos (And.intro prepared below)]
    refine ⟨fun a e L h => ?_, ?_, fun h => by (try dsimp only); omega, ?_, fun h => by (try dsimp only); omega, ?_, fun _ => ?_, fun _ => ?_⟩
    all_goals try dsimp only
    · rcases List.mem_cons.mp h with h | h
      · cases h
      · exact none a e L h
    · simp [promisedAt, next.1, next.2]
    · simp only [next]; exact epochTrueLe
    · simp only [next]; exact epochFalseLe
    · simp only [next]; exact List.mem_cons_of_mem _ (prepTrue (by omega))
    · simp only [next]; exact List.mem_cons_of_mem _ prepared
  · -- the log of epoch 2k + 1 is refused
    have next : (n + 1) % 8 = 7 ∧ (n + 1) / 8 = k := by omega
    have ev : duel n = .accept 0 true (2 * k + 1) [] := by simp [duel, j, hk]
    have stale : 2 * k + 1 < (s.acc 0).promised := by rw [promised]; simp [promisedAt, j, ← hk]
    rw [ev, stale_accept_refused rfl s stale]
    refine ⟨none, ?_, fun h => by omega, ?_, fun h => by omega, ?_, fun _ => ?_, fun _ => ?_⟩
    · rw [promised]; simp [promisedAt, j, next.1, next.2, ← hk]
    · simp only [next]; exact epochTrueLe
    · simp only [next]; exact epochFalseLe
    · simp only [next]; exact prepTrue (by omega)
    · simp only [next]; exact prepFalse (by omega)
  · -- false elects itself (or not); the next round begins
    have next : (n + 1) % 8 = 0 ∧ (n + 1) / 8 = k + 1 := by omega
    have ev : duel n = .elect false {0} 0 [] := by simp [duel, j]
    rw [ev]
    obtain ⟨accSame, epochSame, sentFrom⟩ := apply_elect_facts s false {0} 0 []
    refine ⟨fun a e L h => ?_, ?_, fun _ => ?_, ?_, fun _ => ?_, ?_, fun h => by omega,
      fun h => by omega⟩
    · rcases sentFrom _ h with h | ⟨_, _, h⟩
      · exact none a e L h
      · cases h
    · rw [accSame, promised]; simp [promisedAt, j, next.1, next.2, ← hk]; omega
    · rw [epochSame]; simp only [next]; omega
    · rw [epochSame]; simp only [next]; omega
    · rw [epochSame]; simp only [next]; omega
    · rw [epochSame]; simp only [next]; omega

theorem duelInv_all : ∀ n, DuelInv n (trace (IsMajority (V := Fin 1)) true any duel n)
  | 0 => duelInv_zero
  | n + 1 => duelInv_step (duelInv_all n)

/-- **Dueling candidates choose nothing**: in every state of the infinite run of two candidates
that keep starting higher epochs, no log is chosen at any epoch, although every message is
delivered and the acceptor never fails. -/
theorem dueling_nothing_chosen (n e : ℕ) (L : List Bool) :
    ¬ Chosen IsMajority (trace (IsMajority (V := Fin 1)) true any duel n) e L := by
  rintro ⟨Q, isQ, accepts⟩
  obtain ⟨a, inQ, -⟩ := majority_quorumSystem Q Q isQ isQ
  obtain ⟨L', h, -⟩ := accepts a inQ
  exact (duelInv_all n).none a e L' h

/-! ### An unreachable quorum -/

/-- A stable candidate whose messages only acceptor `0` of three handles: it starts epoch `1`,
then acceptor `0` keeps promising and the candidate keeps trying to elect itself with `{0}`. -/
def lonely (n : ℕ) : Event (Fin 3) Bool Bool :=
  if n = 0 then .start true 1 else if n % 2 = 1 then .promise 0 true 1 else .elect true {0} 0 []

/-- No log is ever sent. -/
def NoAccept (s : State (Fin 3) Bool Bool) : Prop := ∀ w e L, Msg.accept w e L ∉ s.sent

theorem lonely_noAccept : ∀ n, NoAccept (trace (IsMajority (V := Fin 3)) true any lonely n) := by
  intro n
  induction n with
  | zero => intro w e L h; simp [trace, State.init] at h
  | succ n ih =>
      intro w e L h
      change Msg.accept w e L ∈
        (apply (IsMajority (V := Fin 3)) true any (trace (IsMajority (V := Fin 3)) true any lonely n)
          (lonely n)).sent at h
      by_cases zero : n = 0
      · subst zero
        rw [show lonely 0 = .start true 1 from rfl] at h
        simp only [apply] at h
        split_ifs at h
        · rcases List.mem_cons.mp h with h | h
          · cases h
          · exact ih w e L h
        · exact ih w e L h
      · by_cases odd : n % 2 = 1
        · rw [show lonely n = .promise 0 true 1 by simp [lonely, zero, odd]] at h
          simp only [apply] at h
          split_ifs at h
          · rcases List.mem_cons.mp h with h | h
            · cases h
            · exact ih w e L h
          · exact ih w e L h
        · rw [show lonely n = .elect true {0} 0 [] by simp [lonely, zero, odd]] at h
          simp only [apply] at h
          rw [if_neg fun guard => absurd guard.2.1 (by decide)] at h
          exact ih w e L h

/-- **Without a reachable quorum nothing is chosen**: the candidate is stable and correct, the one
acceptor it reaches handles every message, and no log is ever chosen. -/
theorem unreachable_quorum_nothing_chosen (n e : ℕ) (L : List Bool) :
    ¬ Chosen IsMajority (trace (IsMajority (V := Fin 3)) true any lonely n) e L := by
  rintro ⟨Q, isQ, accepts⟩
  obtain ⟨a, inQ, -⟩ := majority_quorumSystem Q Q isQ isQ
  obtain ⟨L', h, -⟩ := accepts a inQ
  have inv := inv_reachable (quorum := IsMajority (V := Fin 3)) (fenced := true) (valid := any) rfl
    (trace_reachable lonely n)
  obtain ⟨w, src⟩ := inv.accepted_src a e L' h
  exact lonely_noAccept n w e L' src

/-! ### The liveness hypotheses can all hold -/

/-- A stable candidate with three correct acceptors: it starts epoch `1`, collects three promises,
elects itself, proposes one command, and its log reaches the three acceptors; afterwards only
repeated deliveries happen. -/
def calm (n : ℕ) : Event (Fin 3) Bool Bool :=
  match n with
  | 0 => .start true 1
  | 1 => .promise 0 true 1
  | 2 => .promise 1 true 1
  | 3 => .promise 2 true 1
  | 4 => .elect true Finset.univ 0 []
  | 5 => .propose true true
  | 6 => .accept 0 true 1 [true]
  | 7 => .accept 1 true 1 [true]
  | 8 => .accept 2 true 1 [true]
  | _ => .promise 0 true 1

theorem calm_stable : Stable (quorum := IsMajority (V := Fin 3)) (fenced := true) (valid := any) calm true 1 0 where
  starts := rfl
  above_cand w := by cases w <;> decide
  above_acc a := by fin_cases a <;> decide
  quiet t after w e' isStart := by
    exfalso
    match t, after with
    | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => simp [calm] at isStart
    | n + 9, _ => simp [calm] at isStart

theorem calm_majority : IsMajority (Finset.univ : Finset (Fin 3)) := by decide

/-- **Positive control**: the hypotheses of `stable_candidate_owns` and `stable_owner_log_chosen`
hold together in this run, and the candidate's log `[true]` is chosen. -/
theorem calm_owns_and_chooses :
    (∀ t', 4 < t' → ∃ log, ((trace (IsMajority (V := Fin 3)) true any calm t').cand true).phase = .owner log) ∧
      ∃ t, Chosen IsMajority (trace (IsMajority (V := Fin 3)) true any calm t) 1 [true] := by
  refine ⟨stable_candidate_owns rfl calm_stable calm_majority (tE := 4) (ae := 0) (al := [])
    (fun a _ => ?_) rfl ⟨0, Finset.mem_univ _, by decide⟩ (by decide) (by decide), ?_⟩
  · fin_cases a
    · exact ⟨1, by decide, by decide, rfl⟩
    · exact ⟨2, by decide, by decide, rfl⟩
    · exact ⟨3, by decide, by decide, rfl⟩
  · refine stable_owner_log_chosen rfl majority_quorumSystem calm_stable calm_majority (t₁ := 6)
      (by decide) (by decide) (fun a _ => ?_)
    fin_cases a
    · exact ⟨6, le_rfl, rfl⟩
    · exact ⟨7, by decide, rfl⟩
    · exact ⟨8, by decide, rfl⟩

/-- **Stability, negative**: in the dueling run the other candidate starts epoch `2` at step `4`,
which changes the state, so the start of epoch `1` is not stable. -/
theorem duel_not_stable :
    ¬ Stable (quorum := IsMajority (V := Fin 1)) (fenced := true) (valid := any) duel true 1 0 := by
  intro stable
  have quiet := stable.quiet 4 (by decide) false 2 rfl
  have below : ((trace (IsMajority (V := Fin 1)) true any duel 4).cand false).epoch < 2 := by decide
  have grows : (apply (IsMajority (V := Fin 1)) true any (trace (IsMajority (V := Fin 1)) true any duel 4)
      (duel 4)).sent.length = (trace (IsMajority (V := Fin 1)) true any duel 4).sent.length + 1 := by
    show (apply (IsMajority (V := Fin 1)) true any _ (.start false 2)).sent.length = _
    simp only [apply, if_pos below, List.length_cons]
  rw [quiet] at grows
  omega

/-- **After a stable start, positive and negative**: one step into the calm run the candidate is at
epoch `1` and electing; at the initial state it is not. -/
theorem afterStart_controls :
    AfterStart (trace (IsMajority (V := Fin 3)) true any calm 1) true 1 ∧
      ¬ AfterStart (State.init : State (Fin 3) Bool Bool) true 1 :=
  ⟨afterStart_first calm_stable, fun h => by have := h.cand_epoch; simp [State.init] at this⟩

end Controls

end Mettapedia.GSLT.Coordination.OwnerFailover
