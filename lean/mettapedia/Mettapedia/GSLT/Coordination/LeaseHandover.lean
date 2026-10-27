import Mettapedia.GSLT.Coordination.OwnerFailover
import Mettapedia.GSLT.Coordination.FencedLeases
import Mettapedia.GSLT.Timing.TimedLeases

/-!
# Lease handover: what a new owner does with the leases it inherits

When a lease owner fails over (`OwnerFailover`), the new owner inherits the lease table: which
tasks are claimed, by whom, at which epoch. It does not inherit the old owner's clock. The expiry
of an inherited lease was read on the old clock and means nothing on the new one.

**The handover rule** (`Cmd.takeover`): on taking over at its own clock reading `now`, the new
owner sets its clock to `now` and extends every inherited lease to `now + duration`. The rule is a
command of the replicated log like any other, so every replica applies it at the same point.

## Safety needs no clock

* **The handover keeps the owner's invariant and is invisible in the atomic view**
  (`inv_cmdStep`, `takeover_abstraction`): no task becomes done or undone, no effect appears or
  disappears, no grant is forgotten.
* **So for every sequence of requests and takeovers**, at most one effect per task is accepted
  (`cmd_effects_nodup`), every accepted effect is from a grant with its epoch
  (`cmd_effect_from_grant`), and every step is invisible or one atomic take (`cmd_step_refines`).
* **Across failover** (`failover_effects_once`): in every reachable state of the failover
  protocol whose commands are these, the effects of any two chosen logs are one list, the shorter
  a prefix of the longer, and no task appears twice in it. No acknowledged effect is lost and none
  is accepted twice, however many owners the history spans.

## What the clock is for

* **An inherited lease is honoured for a full duration of the new clock**
  (`inherited_lease_holds`): until the new owner's clock reaches `now + duration`, the inherited
  holder keeps its lease at the same epoch, or completes the task.
* **Together with bounded drift and delay, an unfenced holder's write lands before the task is
  granted again** (`handover_write_lands_before_regrant`): the holder sent its claim before the old
  owner granted it, hence before the takeover, so the margin of
  `Timing.TimedLeases.write_lands_before_next_grant` covers the handover too.

## Controls

* `Controls.trusted_expiry_regrants_early`: a new owner that trusts the inherited expiry while its
  own clock reads far ahead expires the lease at once and grants the task to another worker; with
  the takeover the same request is refused.
* `Controls.inherited_lease_eventually_expires`: after the takeover, once the new clock has passed
  the extended expiry, the timer frees a crashed holder's task.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.LeaseHandover

open Mettapedia.GSLT.Coordination.FencedLeases

universe u v

variable {X : Type u} [DecidableEq X] {W : Type v} [DecidableEq W]

/-- A command of the replicated lease log: a request, or a takeover at the new owner's clock
reading. -/
inductive Cmd (X : Type u) (W : Type v) where
  | req (r : Request X W)
  | takeover (now : ℕ)
  deriving DecidableEq

/-- Extend an inherited lease to `now + duration`. -/
def extend (duration now : ℕ) : Role W → Role W
  | .claimed holder _ => .claimed holder (now + duration)
  | role => role

/-- The takeover: the new owner's clock, and every inherited lease extended. -/
def takeover (duration now : ℕ) (s : Owner X W) : Owner X W :=
  { s with clock := now, role := fun task => extend duration now (s.role task) }

variable (duration : ℕ)

/-- One command. -/
def cmdStep (s : Owner X W) : Cmd X W → Owner X W
  | .req r => step duration s r
  | .takeover now => takeover duration now s

/-- A run of commands. -/
def cmdRun (s : Owner X W) : List (Cmd X W) → Owner X W
  | [] => s
  | c :: cs => cmdRun (cmdStep duration s c) cs

omit [DecidableEq X] [DecidableEq W] in
theorem extend_done {now : ℕ} {role : Role W} {who : W} :
    extend duration now role = .done who ↔ role = .done who := by
  cases role <;> simp [extend]

omit [DecidableEq X] [DecidableEq W] in
theorem extend_claimed {now : ℕ} {role : Role W} {who : W} {expiry : ℕ} :
    extend duration now role = .claimed who expiry ↔
      expiry = now + duration ∧ ∃ old, role = .claimed who old := by
  cases role with
  | live => simp [extend]
  | claimed holder old =>
      simp only [extend, Role.claimed.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, old, rfl, rfl⟩
      · rintro ⟨rfl, _, rfl, _⟩; exact ⟨rfl, rfl⟩
  | done => simp [extend]

omit [DecidableEq X] [DecidableEq W] in
/-- **The takeover keeps the owner's invariant.** -/
theorem inv_takeover {s : Owner X W} (inv : Inv s) (now : ℕ) : Inv (takeover duration now s) where
  nodup := inv.nodup
  done_iff task := by
    simp only [takeover, extend_done]
    exact inv.done_iff task
  granted task who expiry h := by
    simp only [takeover] at h ⊢
    obtain ⟨_, old, isClaimed⟩ := (extend_claimed duration).mp h
    exact inv.granted task who old isClaimed
  effect_granted := inv.effect_granted

omit [DecidableEq X] [DecidableEq W] in
/-- **The takeover is invisible in the atomic view.** -/
theorem takeover_abstraction (s : Owner X W) (now : ℕ) :
    abstraction (takeover duration now s) = abstraction s := by
  simp only [abstraction, takeover, extend_done]

theorem inv_cmdStep {s : Owner X W} (inv : Inv s) (c : Cmd X W) : Inv (cmdStep duration s c) := by
  cases c with
  | req r => exact inv_step duration inv r
  | takeover now => exact inv_takeover duration inv now

theorem inv_cmdRun {s : Owner X W} (inv : Inv s) (cs : List (Cmd X W)) : Inv (cmdRun duration s cs) := by
  induction cs generalizing s with
  | nil => exact inv
  | cons c rest ih => exact ih (inv_cmdStep duration inv c)

/-- **At most one effect per task, for every sequence of requests and takeovers.** -/
theorem cmd_effects_nodup (cs : List (Cmd X W)) :
    ((cmdRun duration Owner.start cs).effects.map Prod.fst).Nodup :=
  (inv_cmdRun duration inv_start cs).nodup

/-- **Every accepted effect is from a grant with its epoch**, across takeovers. -/
theorem cmd_effect_from_grant (cs : List (Cmd X W)) :
    ∀ entry ∈ (cmdRun duration Owner.start cs).effects, entry ∈ (cmdRun duration Owner.start cs).grants :=
  (inv_cmdRun duration inv_start cs).effect_granted

/-- **Every command is invisible or one atomic take.** -/
theorem cmd_step_refines (s : Owner X W) (c : Cmd X W) :
    abstraction (cmdStep duration s c) = abstraction s ∨
      ∃ who task, task ∉ (abstraction s).taken ∧
        abstraction (cmdStep duration s c) = (abstraction s).take who task := by
  cases c with
  | req r => exact step_refines duration s r
  | takeover now => exact Or.inl (takeover_abstraction duration s now)

/-! ## Effects grow along a log -/

omit [DecidableEq X] [DecidableEq W] in
theorem effects_takeover (s : Owner X W) (now : ℕ) :
    (takeover duration now s).effects = s.effects := rfl

theorem effects_step_prefix (s : Owner X W) (r : Request X W) : s.effects <+: (step duration s r).effects := by
  cases r with
  | claim who task => simp only [step]; split_ifs <;> exact List.prefix_refl _
  | tick => exact List.prefix_refl _
  | expire task => simp only [step]; split_ifs <;> exact List.prefix_refl _
  | effect who task epoch =>
      simp only [step]
      split_ifs
      · exact List.prefix_append _ _
      · exact List.prefix_refl _

theorem effects_cmdRun_prefix (s : Owner X W) (cs : List (Cmd X W)) :
    s.effects <+: (cmdRun duration s cs).effects := by
  induction cs generalizing s with
  | nil => exact List.prefix_refl _
  | cons c rest ih =>
      refine List.IsPrefix.trans ?_ (ih _)
      cases c with
      | req r => exact effects_step_prefix duration s r
      | takeover now => exact List.prefix_refl _

theorem cmdRun_append (s : Owner X W) (first second : List (Cmd X W)) :
    cmdRun duration s (first ++ second) = cmdRun duration (cmdRun duration s first) second := by
  induction first generalizing s with
  | nil => rfl
  | cons c rest ih => exact ih _

/-- A longer log has the effects of the shorter one as a prefix. -/
theorem effects_prefix_of_prefix {cs ds : List (Cmd X W)} (pre : cs <+: ds) :
    (cmdRun duration Owner.start cs).effects <+: (cmdRun duration Owner.start ds).effects := by
  obtain ⟨rest, rfl⟩ := pre
  rw [cmdRun_append]
  exact effects_cmdRun_prefix duration _ rest

/-! ## Across failover -/

section Failover

open Mettapedia.GSLT.Coordination.OwnerFailover

variable {V : Type*} [DecidableEq V] {P : Type*} [DecidableEq P]
variable {quorum : Finset V → Prop} [DecidablePred quorum]

/-- **No effect is accepted twice or lost across failover**: in every reachable state of the
failover protocol over lease commands, the effects of any two chosen logs are one list, the
shorter a prefix of the longer, and no task appears twice in it. -/
theorem failover_effects_once (system : QuorumSystem quorum) {s : State V P (Cmd X W)}
    (reach : Reachable quorum true (fun _ _ => True) s) {e₁ e₂ : ℕ} {L₁ L₂ : List (Cmd X W)}
    (chosen₁ : Chosen quorum s e₁ L₁) (chosen₂ : Chosen quorum s e₂ L₂) :
    ((cmdRun duration Owner.start L₁).effects <+: (cmdRun duration Owner.start L₂).effects ∨
      (cmdRun duration Owner.start L₂).effects <+: (cmdRun duration Owner.start L₁).effects) ∧
      ((cmdRun duration Owner.start L₁).effects.map Prod.fst).Nodup ∧
      ((cmdRun duration Owner.start L₂).effects.map Prod.fst).Nodup := by
  have inv := inv_reachable rfl reach
  refine ⟨?_, cmd_effects_nodup duration L₁, cmd_effects_nodup duration L₂⟩
  rcases chosen_comparable system inv chosen₁ chosen₂ with pre | pre
  · exact Or.inl (effects_prefix_of_prefix duration pre)
  · exact Or.inr (effects_prefix_of_prefix duration pre)

end Failover

/-! ## What the clock is for -/

theorem clock_runList_ge (s : Owner X W) (rs : List (Request X W)) : s.clock ≤ (runList duration s rs).clock := by
  induction rs generalizing s with
  | nil => exact le_rfl
  | cons r rest ih => exact (clock_step_ge duration s r).trans (ih _)

/-- **An inherited lease is honoured for a full duration of the new clock**: after the takeover at
reading `now`, while the new owner's clock stays below `now + duration`, the inherited holder keeps
its lease at the same epoch, or completes the task. -/
theorem inherited_lease_holds {s : Owner X W} {task : X} {who : W} {old now : ℕ}
    (held : s.role task = .claimed who old) :
    ∀ (rs : List (Request X W)), (runList duration (takeover duration now s) rs).clock < now + duration →
      ((runList duration (takeover duration now s) rs).role task = .claimed who (now + duration) ∧
        (runList duration (takeover duration now s) rs).epoch task = s.epoch task) ∨
      (runList duration (takeover duration now s) rs).role task = .done who := by
  suffices ∀ (rs : List (Request X W)) (σ : Owner X W),
      ((σ.role task = .claimed who (now + duration) ∧ σ.epoch task = s.epoch task) ∨
        σ.role task = .done who) →
      (runList duration σ rs).clock < now + duration →
      ((runList duration σ rs).role task = .claimed who (now + duration) ∧
        (runList duration σ rs).epoch task = s.epoch task) ∨
      (runList duration σ rs).role task = .done who by
    intro rs below
    exact this rs _ (Or.inl ⟨by simp [takeover, held, extend], rfl⟩) below
  intro rs
  induction rs with
  | nil => exact fun σ holds _ => holds
  | cons r rest ih =>
      intro σ holds below
      apply ih _ _ below
      have clockBelow : σ.clock < now + duration :=
        lt_of_le_of_lt ((clock_step_ge duration σ r).trans (clock_runList_ge duration _ rest)) below
      exact lease_step_holds duration holds clockBelow r

open Mettapedia.GSLT.Timing in
/-- **An unfenced holder's write lands before the task is granted again**, across a handover. The
holder sent its claim at real time `sent`, before the takeover at real time `handover`; the new
owner grants the task again at `next`, once its clock has passed the extended expiry; the holder
writes at `u` while its own clock shows less than `usable` since `sent`, and the write takes
`δ ≤ Δ` to land. With the rates and margin of `TimedLeases.write_lands_before_next_grant`, the
write lands before `next`. -/
theorem handover_write_lands_before_regrant {newClock holderClock : Clock}
    {den slow fast usable Δ sent handover next u δ : ℕ}
    (ownerRate : ∀ t d, den * newClock (t + d) ≤ den * newClock t + fast * d)
    (holderRate : ∀ t d, den * holderClock t + slow * d ≤ den * holderClock (t + d))
    (slowPos : 0 < slow) (fastPos : 0 < fast)
    (sentFirst : sent ≤ handover) (regrantAfter : handover ≤ next)
    (extended : newClock handover + duration ≤ newClock next)
    (afterSend : sent ≤ u) (believed : holderClock u < holderClock sent + usable)
    (delayed : δ ≤ Δ) (margin : fast * (den * usable + slow * Δ) ≤ slow * (den * duration)) :
    u + δ < next :=
  TimedLeases.write_lands_before_next_grant ownerRate holderRate slowPos fastPos sentFirst
    regrantAfter extended afterSend believed delayed margin

/-! ## Controls -/

namespace Controls

/-- The old owner granted the task to worker `true` until its clock read `10`; the new owner's
clock reads `105` when it takes over. -/
def inherited : Owner Unit Bool :=
  ⟨fun _ => .claimed true 10, fun _ => 1, 105, [((), true, 1)], []⟩

/-- **Trusting the inherited expiry regrants early**: without the takeover, the expiry request is
accepted at once and worker `false` is granted the task, while worker `true` may still believe its
lease runs; with the takeover, the same requests leave the lease with `true`. -/
theorem trusted_expiry_regrants_early :
    (runList 20 inherited [.expire (), .claim false ()]).role () = .claimed false 125 ∧
      (runList 20 (takeover 20 105 inherited) [.expire (), .claim false ()]).role () = .claimed true 125 := by
  decide

/-- **After the takeover a crashed holder's task is freed** once the new clock has passed the
extended expiry: twenty ticks, then the timer. -/
theorem inherited_lease_eventually_expires :
    (runList 20 (takeover 20 105 inherited) (List.replicate 20 .tick ++ [.expire ()])).role () = .live := by
  decide

end Controls

end Mettapedia.GSLT.Coordination.LeaseHandover
