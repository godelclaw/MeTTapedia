import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Clock models: asynchronous, partially synchronous, synchronous with bounded drift

**Real time** is a global count of ticks that no process observes. A process observes only its
own **clock**, a reading at each real time (`Clock`), and messages, each of which takes some real
time to arrive (`Delays`). A **timing** fixes every clock and every delay (`Environment`). A timing
model is a set of timings; a result proved for a model holds for every timing in it.

## Rates and drift

A clock's rate lies between `slow / den` and `fast / den` local units per real tick
(`RateBounds`); integer factors over a common denominator keep everything in `ℕ`. Local units are
finer than real ticks: a clock of **nominal rate** `n` advances `n` local units per real tick, and
**bounded drift** `num` means it advances between `n - num` and `n + num` (`BoundedDrift`), so a
slow clock and a fast clock are both expressible. A clock of rate `n` reads `n · t`
(`RateBounds.nominal`); a perfect clock reads real time (`RateBounds.perfect`). A positive lower
rate makes a clock monotone (`RateBounds.monotone`).

## The models, weakest assumption first

* `asynchronous`: every timing. Delays are finite but unbounded; clocks are arbitrary functions.
* `unknownBound` (partial synchrony in the first form of Dwork, Lynch and Stockmeyer): some bound
  on every delay and some bounds on every clock's rate hold from the start, but nobody knows
  them, so a protocol must work for all of them.
* `eventualBound Δ n num` (the second form): a known delay bound `Δ` and the drift bound `num`
  around the nominal rate `n` hold from an unknown **global stabilization time** `gst` on.
* `synchronous Δ n num`: the known bounds hold always.

The relations (`synchronous_subset_eventualBound`, `synchronous_subset_unknownBound`) and the
separations, each by a timing (`Separations`):

* a delay of `Δ + 1` everywhere is in `unknownBound` and not in `eventualBound Δ`;
* a clock stalled before `gst` is in `eventualBound` and in neither `unknownBound` nor
  `synchronous`; so the two forms of partial synchrony are incomparable as sets of timings, and
  both lie strictly between `synchronous` and `asynchronous`;
* a delay that grows with the send time is in `asynchronous` and in neither form of partial
  synchrony.

## What "a deadline fires" means in each model

A deadline armed at real time `t₀` for `D` units of clock `c` has **passed** at real time `t` when
`c` has advanced by `D` since `t₀` (`Passed`). The clock region makes the deadline's occurrence at
some real time at which the deadline has passed, never before. What that says about real time
depends on the model:

* **asynchronous**: nothing. A deadline may pass one tick after it is armed
  (`Controls.async_deadline_early`), or never (`Controls.stopped_clock_never`). A deadline is a
  nondeterministic event, ordered only by the commits around it.
* **synchronous**: it passes no earlier than `den · D / fast` real ticks after arming
  (`passed_not_early`), and by `den · D / slow` real ticks at the latest (`passed_by`); with
  nominal rate `n` and drift `num`, between `D / (n + num)` and `D / (n - num)`.
* **partial synchrony**: the same window, but only for deadlines armed after `gst`
  (`passed_not_early_after`), and with unknown constants in the first form.

**A timeout is accurate only under a known bound** (`reply_before_passed`): if a reply always
arrives within `R` real ticks and `fast · R < den · D`, the reply arrives before the deadline
passes. Without a known bound, for every deadline some admissible reply arrives after it
(`Controls.reply_after_deadline`, a timing in `unknownBound`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Timing

universe u

/-- A local clock: its reading at each real time. -/
abbrev Clock := ℕ → ℕ

/-- Message delays: `delay p q t` is the real time the message from `p` to `q` sent at real time
`t` takes to arrive. -/
abbrev Delays (P : Type u) := P → P → ℕ → ℕ

/-- A timing environment: every process's clock and every message's delay. -/
structure Environment (P : Type u) where
  clock : P → Clock
  delay : Delays P

variable {P : Type u}

/-! ## Rates, drift, delays, skew -/

/-- A clock's rate lies between `slow / den` and `fast / den` local units per real tick. -/
structure RateBounds (c : Clock) (den slow fast : ℕ) : Prop where
  lower : ∀ t d, den * c t + slow * d ≤ den * c (t + d)
  upper : ∀ t d, den * c (t + d) ≤ den * c t + fast * d

/-- The same bounds, from real time `gst` on. -/
structure RateBoundsAfter (c : Clock) (gst den slow fast : ℕ) : Prop where
  lower : ∀ t d, gst ≤ t → den * c t + slow * d ≤ den * c (t + d)
  upper : ∀ t d, gst ≤ t → den * c (t + d) ≤ den * c t + fast * d

/-- **Bounded drift**: the clock advances between `nominal - num` and `nominal + num` local units
per real tick. -/
def BoundedDrift (c : Clock) (nominal num : ℕ) : Prop := RateBounds c 1 (nominal - num) (nominal + num)

/-- Every delay is at most `Δ`. -/
def DelaysWithin (delay : Delays P) (Δ : ℕ) : Prop := ∀ p q t, delay p q t ≤ Δ

/-- Every message sent from real time `gst` on takes at most `Δ`. -/
def DelaysWithinAfter (delay : Delays P) (gst Δ : ℕ) : Prop := ∀ p q t, gst ≤ t → delay p q t ≤ Δ

/-- Clocks never differ by more than `ε`. -/
def SkewWithin (clock : P → Clock) (ε : ℕ) : Prop := ∀ p q t, clock p t ≤ clock q t + ε

namespace RateBounds

/-- **A perfect clock reads real time.** -/
theorem perfect (den : ℕ) : RateBounds (fun t => t) den den den :=
  ⟨fun t d => by ring_nf; omega, fun t d => by ring_nf; omega⟩

/-- A clock of rate `n` reads `n · t`. -/
theorem nominal (n : ℕ) : RateBounds (fun t => n * t) 1 n n :=
  ⟨fun t d => by ring_nf; omega, fun t d => by ring_nf; omega⟩

/-- A clock of rate `n` has drift `num` around `n`. -/
theorem nominal_drift (n num : ℕ) : BoundedDrift (fun t => n * t) n num :=
  ⟨fun t d => by
      have := Nat.mul_le_mul_right d (Nat.sub_le n num)
      simp only [one_mul]; rw [Nat.mul_add]; omega,
    fun t d => by simp only [one_mul]; rw [Nat.mul_add, Nat.add_mul]; omega⟩

/-- A clock with rate bounds has them from every later time on. -/
theorem after {c : Clock} {den slow fast : ℕ} (bounds : RateBounds c den slow fast) (gst : ℕ) :
    RateBoundsAfter c gst den slow fast :=
  ⟨fun t d _ => bounds.lower t d, fun t d _ => bounds.upper t d⟩

/-- **A clock with rate bounds is monotone.** -/
theorem monotone {c : Clock} {den slow fast : ℕ} (bounds : RateBounds c den slow fast)
    (positive : 0 < den) : Monotone c := by
  intro t t' le
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le le
  have := bounds.lower t d
  have : den * c t ≤ den * c (t + d) := le_trans (Nat.le_add_right _ _) this
  exact Nat.le_of_mul_le_mul_left this positive

end RateBounds

/-! ## The models -/

/-- **Asynchronous**: every timing. -/
def asynchronous : Set (Environment P) := Set.univ

/-- **Partial synchrony, first form**: bounds on delays and on clock rates hold always, but they
are not known. -/
def unknownBound : Set (Environment P) :=
  {T | (∃ Δ, DelaysWithin T.delay Δ) ∧
    ∃ den slow fast, 0 < den ∧ 0 < slow ∧ ∀ p, RateBounds (T.clock p) den slow fast}

/-- **Partial synchrony, second form**: the known delay bound `Δ` and the drift bound `num` around
the nominal rate hold from an unknown global stabilization time on. -/
def eventualBound (Δ nominal num : ℕ) : Set (Environment P) :=
  {T | ∃ gst, DelaysWithinAfter T.delay gst Δ ∧
    ∀ p, RateBoundsAfter (T.clock p) gst 1 (nominal - num) (nominal + num)}

/-- **Synchronous**: the known delay bound and drift bound hold always. -/
def synchronous (Δ nominal num : ℕ) : Set (Environment P) :=
  {T | DelaysWithin T.delay Δ ∧ ∀ p, BoundedDrift (T.clock p) nominal num}

theorem synchronous_subset_eventualBound (Δ nominal num : ℕ) :
    (synchronous Δ nominal num : Set (Environment P)) ⊆ eventualBound Δ nominal num :=
  fun _ ⟨delays, drift⟩ => ⟨0, fun p q t _ => delays p q t, fun p => (drift p).after 0⟩

theorem synchronous_subset_unknownBound {Δ nominal num : ℕ} (small : num < nominal) :
    (synchronous Δ nominal num : Set (Environment P)) ⊆ unknownBound :=
  fun _ ⟨delays, drift⟩ =>
    ⟨⟨Δ, delays⟩, 1, nominal - num, nominal + num, Nat.one_pos, by omega, drift⟩

theorem unknownBound_subset_asynchronous : (unknownBound : Set (Environment P)) ⊆ asynchronous :=
  Set.subset_univ _

/-! ## Deadlines -/

/-- A deadline armed at real time `t₀` for `D` units of clock `c` has **passed** at real time
`t`. -/
def Passed (c : Clock) (t₀ D t : ℕ) : Prop := t₀ ≤ t ∧ c t₀ + D ≤ c t

instance (c : Clock) (t₀ D t : ℕ) : Decidable (Passed c t₀ D t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **A deadline never passes early** on a clock whose rate is at most `fast / den` from the
arming on: at least `den · D / fast` real ticks go by. -/
theorem passed_not_early_after {c : Clock} {gst den slow fast t₀ D t : ℕ}
    (bounds : RateBoundsAfter c gst den slow fast) (armedAfter : gst ≤ t₀) (passed : Passed c t₀ D t) :
    den * D ≤ fast * (t - t₀) := by
  obtain ⟨le, advanced⟩ := passed
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le le
  have := bounds.upper t₀ d armedAfter
  have : den * (c t₀ + D) ≤ den * c (t₀ + d) := Nat.mul_le_mul_left den advanced
  rw [Nat.add_sub_cancel_left]
  nlinarith

theorem passed_not_early {c : Clock} {den slow fast t₀ D t : ℕ}
    (bounds : RateBounds c den slow fast) (passed : Passed c t₀ D t) :
    den * D ≤ fast * (t - t₀) :=
  passed_not_early_after (bounds.after 0) (Nat.zero_le _) passed

/-- **A deadline has passed** `d` real ticks after arming once `slow · d ≥ den · D`. -/
theorem passed_by_after {c : Clock} {gst den slow fast t₀ D d : ℕ}
    (bounds : RateBoundsAfter c gst den slow fast) (positive : 0 < den) (armedAfter : gst ≤ t₀)
    (long : den * D ≤ slow * d) : Passed c t₀ D (t₀ + d) := by
  refine ⟨Nat.le_add_right _ _, ?_⟩
  have := bounds.lower t₀ d armedAfter
  have : den * (c t₀ + D) ≤ den * c (t₀ + d) := by nlinarith
  exact Nat.le_of_mul_le_mul_left this positive

theorem passed_by {c : Clock} {den slow fast t₀ D d : ℕ} (bounds : RateBounds c den slow fast)
    (positive : 0 < den) (long : den * D ≤ slow * d) : Passed c t₀ D (t₀ + d) :=
  passed_by_after (bounds.after 0) positive (Nat.zero_le _) long

/-- **A timeout is accurate under a known bound.** If a reply arrives within `R` real ticks of the
arming, and the caller's clock runs at most at `fast / den` with `fast · R < den · D`, then the
reply arrives strictly before the deadline passes. -/
theorem reply_before_passed {c : Clock} {den slow fast t₀ D t r R : ℕ}
    (bounds : RateBounds c den slow fast) (replyBy : r ≤ t₀ + R) (margin : fast * R < den * D)
    (passed : Passed c t₀ D t) : r < t := by
  have early := passed_not_early bounds passed
  by_contra notBefore
  push Not at notBefore
  have : t - t₀ ≤ R := by have := passed.1; omega
  have : fast * (t - t₀) ≤ fast * R := Nat.mul_le_mul_left fast this
  omega

/-! ## Separations -/

namespace Separations

/-- Perfect clocks and a constant delay. -/
def constantDelay (Δ : ℕ) : Environment P := ⟨fun _ t => t, fun _ _ _ => Δ⟩

/-- **A delay of `Δ + 1` everywhere is a partially synchronous timing of the first form that the
second form with bound `Δ` excludes.** -/
theorem unknownBound_not_eventualBound [Nonempty P] (Δ nominal num : ℕ) :
    constantDelay (Δ + 1) ∈ (unknownBound : Set (Environment P)) ∧
      constantDelay (Δ + 1) ∉ (eventualBound Δ nominal num : Set (Environment P)) := by
  refine ⟨⟨⟨Δ + 1, fun _ _ _ => le_rfl⟩, 1, 1, 1, Nat.one_pos, Nat.one_pos,
    fun _ => RateBounds.perfect 1⟩, ?_⟩
  rintro ⟨gst, delays, -⟩
  obtain ⟨p⟩ := ‹Nonempty P›
  have := delays p p gst le_rfl
  simp [constantDelay] at this

/-- A clock that stalls for one tick and then reads real time minus one. -/
def stalled : Clock := fun t => t - 1

theorem stalled_after : RateBoundsAfter stalled 1 1 1 1 :=
  ⟨fun t d h => by simp only [stalled]; omega, fun t d h => by simp only [stalled]; omega⟩

/-- Instant delivery, and every clock stalled for one tick. -/
def stalledTiming : Environment P := ⟨fun _ => stalled, fun _ _ _ => 0⟩

/-- **A clock stalled before stabilization is in the second form only**: the stalled timing is in
`eventualBound 0 1 0`, and in neither `unknownBound` nor `synchronous 0 1 0`. -/
theorem eventualBound_not_unknownBound [Nonempty P] :
    stalledTiming ∈ (eventualBound 0 1 0 : Set (Environment P)) ∧
      stalledTiming ∉ (unknownBound : Set (Environment P)) ∧
        stalledTiming ∉ (synchronous 0 1 0 : Set (Environment P)) := by
  obtain ⟨p⟩ := ‹Nonempty P›
  refine ⟨⟨1, fun _ _ _ _ => le_rfl, fun _ => stalled_after⟩, ?_, ?_⟩
  · rintro ⟨-, den, slow, fast, -, slowPos, rates⟩
    have := (rates p).lower 0 1
    simp only [stalledTiming, stalled] at this
    omega
  · rintro ⟨-, drift⟩
    have := (drift p).lower 0 1
    simp only [stalledTiming, stalled] at this
    omega

/-- Perfect clocks and a delay that grows with the send time. -/
def growingDelay : Environment P := ⟨fun _ t => t, fun _ _ t => t⟩

/-- **A delay growing with the send time is asynchronous and partially synchronous in neither
form.** -/
theorem asynchronous_not_partial [Nonempty P] (Δ nominal num : ℕ) :
    growingDelay ∈ (asynchronous : Set (Environment P)) ∧
      growingDelay ∉ (unknownBound : Set (Environment P)) ∧
        growingDelay ∉ (eventualBound Δ nominal num : Set (Environment P)) := by
  obtain ⟨p⟩ := ‹Nonempty P›
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · rintro ⟨⟨bound, delays⟩, -⟩
    have := delays p p (bound + 1)
    simp [growingDelay] at this
  · rintro ⟨gst, delays, -⟩
    have := delays p p (gst + Δ + 1) (by omega)
    simp only [growingDelay] at this
    omega

end Separations

/-! ## Controls -/

namespace Controls

/-- **In the asynchronous model a deadline may pass one tick after it is armed**: a clock that
jumps by `D`. -/
theorem async_deadline_early (t₀ D : ℕ) :
    Passed (fun t => if t ≤ t₀ then 0 else D) t₀ D (t₀ + 1) := by
  refine ⟨Nat.le_add_right _ _, ?_⟩
  simp

/-- **In the asynchronous model a deadline may never pass**: a stopped clock. -/
theorem stopped_clock_never {t₀ D : ℕ} (positive : 0 < D) (t : ℕ) : ¬ Passed (fun _ => 0) t₀ D t :=
  fun passed => by have := passed.2; dsimp only at this; omega

/-- Positive control: on a perfect clock the deadline passes exactly `D` ticks after arming, and
not one tick earlier. -/
theorem perfect_deadline {t₀ D : ℕ} (positive : 0 < D) :
    Passed (fun t => t) t₀ D (t₀ + D) ∧ ¬ Passed (fun t => t) t₀ D (t₀ + D - 1) :=
  ⟨⟨Nat.le_add_right _ _, le_rfl⟩, fun passed => by have := passed.2; dsimp only at this; omega⟩

/-- **Without a known bound a reply can follow the deadline**: with perfect clocks and every
delay `D + 1`, which is a timing of `unknownBound`, a reply sent at the arming arrives after the
deadline of `D` has passed. -/
theorem reply_after_deadline [Nonempty P] (t₀ D : ℕ) :
    Separations.constantDelay (D + 1) ∈ (unknownBound : Set (Environment P)) ∧
      Passed (fun t => t) t₀ D (t₀ + D) ∧ t₀ + D < t₀ + (D + 1) := by
  refine ⟨(Separations.unknownBound_not_eventualBound D 1 0).1, ⟨Nat.le_add_right _ _, le_rfl⟩, by omega⟩

/-! ### Negative controls of the timing assumptions -/

/-- **Rate bounds, negative**: a stopped clock has no positive lower rate: in one real tick it
gains nothing. (`RateBounds.perfect` is the positive control.) -/
theorem stopped_clock_not_rateBounded : ¬ RateBounds (fun _ => 0) 1 1 1 := fun bounds => by
  have := bounds.lower 0 1
  omega

/-- **Bounded drift, negative**: a clock running at three local units per real tick drifts more
than one unit per tick from the nominal rate one. -/
theorem fast_clock_drifts : ¬ BoundedDrift (fun t => 3 * t) 1 1 := fun drift => by
  have := drift.upper 0 1
  omega

/-- **Delays within, negative**: every message taking five ticks exceeds the bound three. -/
theorem slow_delays_exceed : ¬ DelaysWithin (fun (_ _ : Unit) _ => 5) 3 := fun within => by
  have := within () () 0
  dsimp only at this
  omega

/-- **Skew within, negative**: one clock five ahead of the other exceeds the skew bound three. -/
theorem far_clocks_skewed : ¬ SkewWithin (fun p : Bool => fun t => if p then t + 5 else t) 3 :=
  fun skew => by
    have := skew true false 0
    simp at this

end Controls

end Mettapedia.GSLT.Timing
