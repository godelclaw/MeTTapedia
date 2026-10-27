import Mettapedia.GSLT.Timing.ClockModels
import Mettapedia.GSLT.Coordination.MajorityEpochs

/-!
# The winner rule with local clocks

Each claimant broadcasts a claim stamped with its own clock, waits `wait` units **of its own
clock**, and then proceeds unless it has received a claim that comes before its own: an earlier
stamp, or the same stamp and a smaller rank (`ProceedsAt`). `Coordination.MajorityEpochs` states
the rule with perfect clocks; here every claimant reads its own clock, and delays depend on the
send time.

## Safety needs a known bound

* **Safe in the synchronous model** (`winner_unique`): if every delay is at most `Δ`, clocks
  differ by at most `ε`, the waiting claimant's clock runs at most at `fast / den`, and
  `ε < wait` and `fast · Δ + den · ε ≤ den · wait`, at most one claimant proceeds. With perfect
  clocks this is `Δ ≤ wait` (and `0 < wait`); a fast clock and a skew each lengthen the wait.
  `synchronous_safe` states it for `synchronous`: `(n + num) · Δ + ε ≤ wait` in local units.
* **The perfect-clock rule is the one of `MajorityEpochs`** (`proceedsAt_iff_proceeds`): with
  clocks that read real time and a decision exactly `wait` after the claim, `ProceedsAt` is
  `MajorityEpochs.Proceeds`.
* **Unsafe under partial synchrony, in both forms, for every wait**
  (`partial_synchrony_unsafe`): for every `wait`, `Δ` and drift bound there is a timing that is in
  `unknownBound` and in `eventualBound Δ` in which two claimants proceed: the claims are made
  before stabilization, with a delay of `wait + 1`. Safety must hold before stabilization too, so
  no wait makes the rule safe without a bound known in advance; a fortiori not in the
  asynchronous model.
* Controls, each breaking one hypothesis of `winner_unique` with all others kept:
  a skew larger than the wait with instant delivery (`Controls.skew_two_winners`); a fast clock
  with every delay within the wait, the condition that perfect clocks need
  (`Controls.drift_two_winners`). Positive control: a synchronous instance with exactly one
  winner, the earliest (`Controls.synchronous_one_winner`).

## Liveness needs nothing

* **The earliest claim always proceeds** (`earliest_proceeds`), in every timing.

So the winner rule is the reverse of a fenced lease: it is live in every model and safe only in
the synchronous one, while a fenced lease is safe in every model and live only under eventual
synchrony (`TimedLeases`). Where safety matters, the winner rule's effect must be fenced at an
owner, which makes the owner the arbiter.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Timing.WinnerRule

open Mettapedia.GSLT.Timing
open Mettapedia.GSLT.Coordination.MajorityEpochs (Before before_asymm)

universe u

variable {W : Type u}

/-- When each claimant claims, and when it decides, in real time. -/
structure Claims (W : Type u) where
  claimAt : W → ℕ
  decideAt : W → ℕ

variable (E : Environment W) (cl : Claims W)

/-- The stamp of a claim: the claimant's clock when it claims. -/
def stamp (w : W) : ℕ := E.clock w (cl.claimAt w)

/-- Every claimant decides after waiting `wait` units of its own clock. -/
def Waited (wait : ℕ) : Prop :=
  ∀ w, cl.claimAt w ≤ cl.decideAt w ∧ stamp E cl w + wait ≤ E.clock w (cl.decideAt w)

/-- `w` has received `v`'s claim when it decides. -/
def Received (v w : W) : Prop := cl.claimAt v + E.delay v w (cl.claimAt v) ≤ cl.decideAt w

instance (v w : W) : Decidable (Received E cl v w) := inferInstanceAs (Decidable (_ ≤ _))

/-- `w` proceeds when no claim it has received comes before its own. -/
def ProceedsAt (rank : W → ℕ) (w : W) : Prop :=
  ∀ v, v ≠ w → Received E cl v w → ¬ Before (stamp E cl) rank v w

variable {E cl}

/-! ## Safety under a known bound -/

/-- **An earlier claim is received in time.** Under the bounds of `winner_unique`, a claimant
receives every claim that comes before its own before it decides. -/
theorem received_of_before {rank : W → ℕ} {wait Δ ε den fast : ℕ} (waited : Waited E cl wait)
    (delays : DelaysWithin E.delay Δ) (skew : SkewWithin E.clock ε)
    (rates : ∀ w t d, den * E.clock w (t + d) ≤ den * E.clock w t + fast * d)
    (monotone : ∀ w, Monotone (E.clock w)) (positive : 0 < den) (skewBelow : ε < wait)
    (margin : fast * Δ + den * ε ≤ den * wait) {v w : W} (before : Before (stamp E cl) rank v w) :
    Received E cl v w := by
  have stampLe : stamp E cl v ≤ stamp E cl w := by
    unfold Before at before; omega
  by_contra late
  unfold Received at late
  push Not at late
  have delayed := delays v w (cl.claimAt v)
  have waitedW := (waited w).2
  have skewed := skew w v (cl.claimAt v)
  unfold stamp at stampLe waitedW
  -- `w`'s clock advanced by at least `wait - ε` between `v`'s claim and `w`'s decision.
  have advanced : E.clock w (cl.claimAt v) + wait ≤ E.clock w (cl.decideAt w) + ε := by omega
  rcases le_or_gt (cl.decideAt w) (cl.claimAt v) with early | after
  · have := monotone w early
    omega
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt after
    have rate := rates w (cl.claimAt v) (d + 1)
    rw [show cl.claimAt v + (d + 1) = cl.decideAt w by omega] at rate
    have scaled : den * (E.clock w (cl.claimAt v) + wait) ≤ den * (E.clock w (cl.decideAt w) + ε) :=
      Nat.mul_le_mul_left den advanced
    rw [Nat.mul_add, Nat.mul_add] at scaled
    have short : d + 1 < Δ := by omega
    have combined : den * wait ≤ fast * (d + 1) + den * ε := by linarith
    have slowEnough : fast * Δ ≤ fast * (d + 1) := by linarith
    rcases Nat.eq_zero_or_pos fast with zero | fastPos
    · subst zero
      have : den * wait ≤ den * ε := by simpa using combined
      have := Nat.le_of_mul_le_mul_left this positive
      omega
    · have := Nat.le_of_mul_le_mul_left slowEnough fastPos
      omega

/-- **The winner rule is safe under a known bound**: at most one claimant proceeds. -/
theorem winner_unique {rank : W → ℕ} (distinct : Function.Injective rank) {wait Δ ε den fast : ℕ}
    (waited : Waited E cl wait) (delays : DelaysWithin E.delay Δ) (skew : SkewWithin E.clock ε)
    (rates : ∀ w t d, den * E.clock w (t + d) ≤ den * E.clock w t + fast * d)
    (monotone : ∀ w, Monotone (E.clock w)) (positive : 0 < den) (skewBelow : ε < wait)
    (margin : fast * Δ + den * ε ≤ den * wait) {first second : W}
    (proceedsFirst : ProceedsAt E cl rank first) (proceedsSecond : ProceedsAt E cl rank second) :
    first = second := by
  by_contra apart
  have ordered : Before (stamp E cl) rank first second ∨ Before (stamp E cl) rank second first := by
    unfold Before
    rcases lt_trichotomy (stamp E cl first) (stamp E cl second) with lt | eq | gt
    · exact Or.inl (Or.inl lt)
    · rcases lt_trichotomy (rank first) (rank second) with lt' | eq' | gt'
      · exact Or.inl (Or.inr ⟨eq, lt'⟩)
      · exact absurd (distinct eq') apart
      · exact Or.inr (Or.inr ⟨eq.symm, gt'⟩)
    · exact Or.inr (Or.inl gt)
  have received := fun {v w : W} (before : Before (stamp E cl) rank v w) =>
    received_of_before waited delays skew rates monotone positive skewBelow margin before
  rcases ordered with before | before
  · exact proceedsSecond first apart (received before) before
  · exact proceedsFirst second (Ne.symm apart) (received before) before

/-- **The winner rule in the synchronous model**: with delays at most `Δ`, clocks of nominal rate
`n` with drift `num` (local units per real tick), skew at most `ε`, `ε < wait` and
`(n + num) · Δ + ε ≤ wait`, at most one claimant proceeds. -/
theorem synchronous_safe {rank : W → ℕ} (distinct : Function.Injective rank)
    {wait Δ ε nominal num : ℕ} (sync : E ∈ synchronous Δ nominal num) (skew : SkewWithin E.clock ε)
    (waited : Waited E cl wait) (skewBelow : ε < wait) (margin : (nominal + num) * Δ + ε ≤ wait)
    {first second : W} (proceedsFirst : ProceedsAt E cl rank first)
    (proceedsSecond : ProceedsAt E cl rank second) : first = second :=
  winner_unique distinct waited sync.1 skew (fun w => (sync.2 w).upper)
    (fun w => (sync.2 w).monotone Nat.one_pos) Nat.one_pos skewBelow (by simpa using margin)
    proceedsFirst proceedsSecond

/-- **With perfect clocks the rule is the one of `MajorityEpochs`**: when clocks read real time
and each claimant decides exactly `wait` after its claim, proceeding here is proceeding there,
with the delay of each claim. -/
theorem proceedsAt_iff_proceeds {rank : W → ℕ} {wait : ℕ} (perfect : ∀ w t, E.clock w t = t)
    (exact : ∀ w, cl.decideAt w = cl.claimAt w + wait) (w : W) :
    ProceedsAt E cl rank w ↔
      Mettapedia.GSLT.Coordination.MajorityEpochs.Proceeds cl.claimAt rank
        (fun v w => E.delay v w (cl.claimAt v)) wait w := by
  have stampIs : stamp E cl = cl.claimAt := funext fun w => perfect w _
  unfold ProceedsAt Mettapedia.GSLT.Coordination.MajorityEpochs.Proceeds Received
    Mettapedia.GSLT.Coordination.MajorityEpochs.Sees
  simp only [stampIs, exact]

/-! ## Liveness needs nothing -/

/-- **The earliest claim proceeds**, in every timing. -/
theorem earliest_proceeds {rank : W → ℕ} {earliest : W}
    (isEarliest : ∀ v, v ≠ earliest → Before (stamp E cl) rank earliest v) :
    ProceedsAt E cl rank earliest :=
  fun v apart _ before => before_asymm earliest v (isEarliest v apart) before

/-! ## Unsafe under partial synchrony -/

/-- Two claimants, `false` ranked first. -/
def twoRank : Bool → ℕ := fun w => if w then 1 else 0

theorem twoRank_injective : Function.Injective twoRank := by
  intro a b same
  cases a <;> cases b <;> simp_all [twoRank]

/-- Clocks of nominal rate `n` without drift; a claim sent at real time `0` takes `wait + 1`, every
later message is instant. -/
def lateBeforeStable (nominal wait : ℕ) : Environment Bool :=
  ⟨fun _ t => nominal * t, fun _ _ t => if t = 0 then wait + 1 else 0⟩

/-- Both claim at `0` and decide at real time `wait`. -/
def sameTime (wait : ℕ) : Claims Bool := ⟨fun _ => 0, fun _ => wait⟩

/-- **The winner rule is unsafe under partial synchrony, in both forms, for every wait**: the
timing `lateBeforeStable n wait` is in `unknownBound` and in `eventualBound Δ n num` for every `Δ`
and drift `num`, every claimant waits `wait` on its clock, and both proceed. -/
theorem partial_synchrony_unsafe (wait Δ nominal num : ℕ) (positive : 0 < nominal) :
    lateBeforeStable nominal wait ∈ (unknownBound : Set (Environment Bool)) ∧
      lateBeforeStable nominal wait ∈ (eventualBound Δ nominal num : Set (Environment Bool)) ∧
      Waited (lateBeforeStable nominal wait) (sameTime wait) wait ∧
      ProceedsAt (lateBeforeStable nominal wait) (sameTime wait) twoRank false ∧
      ProceedsAt (lateBeforeStable nominal wait) (sameTime wait) twoRank true := by
  refine ⟨⟨⟨wait + 1, fun _ _ t => by simp only [lateBeforeStable]; split <;> omega⟩,
      1, nominal, nominal, Nat.one_pos, positive, fun _ => RateBounds.nominal nominal⟩,
    ⟨1, fun _ _ t after => by simp only [lateBeforeStable]; split <;> omega,
      fun _ => (RateBounds.nominal_drift nominal num).after 1⟩,
    fun w => ⟨by simp [sameTime], by
      simp only [stamp, lateBeforeStable, sameTime, Nat.mul_zero, Nat.zero_add]
      exact Nat.le_mul_of_pos_left wait positive⟩, ?_, ?_⟩
  · intro v apart _ before
    cases v
    · exact apart rfl
    · simp [Before, stamp, twoRank, lateBeforeStable, sameTime] at before
  · intro v apart received _
    cases v
    · simp [Received, lateBeforeStable, sameTime] at received
    · exact apart rfl

/-! ## Controls -/

namespace Controls

/-- **A skew larger than the wait gives two winners, with instant delivery.** Clock `true` reads
three ahead; `true` claims at `0` (stamp `3`) and decides at `1`; `false` claims at `2`
(stamp `2`, earlier) and decides at `3`. Each clock runs at the perfect rate. -/
def skewed : Environment Bool := ⟨fun w t => if w then t + 3 else t, fun _ _ _ => 0⟩

def skewedClaims : Claims Bool := ⟨fun w => if w then 0 else 2, fun w => if w then 1 else 3⟩

theorem skew_two_winners :
    Waited skewed skewedClaims 1 ∧ DelaysWithin skewed.delay 0 ∧ SkewWithin skewed.clock 3 ∧
      (∀ w, RateBounds (skewed.clock w) 1 1 1) ∧
      ProceedsAt skewed skewedClaims twoRank false ∧ ProceedsAt skewed skewedClaims twoRank true := by
  refine ⟨fun w => ?_, fun _ _ _ => le_rfl, fun p q t => ?_, fun w => ?_, ?_, ?_⟩
  · cases w <;> simp [stamp, skewed, skewedClaims]
  · cases p <;> cases q <;> simp [skewed]
    all_goals omega
  · cases w
    · simpa [skewed] using RateBounds.perfect 1
    · exact ⟨fun t d => by simp [skewed]; omega, fun t d => by simp [skewed]; omega⟩
  · intro v apart _ before
    cases v
    · exact apart rfl
    · simp [Before, stamp, skewed, skewedClaims] at before
  · intro v apart received _
    cases v
    · simp [Received, skewed, skewedClaims] at received
    · exact apart rfl

/-- **A fast clock gives two winners although every delay is within the wait**, the condition
perfect clocks need. Both claim at `0` with stamp `0`; `false` ranks first. The clock of `true`
runs at twice the real rate for one tick, so `true` has waited `2` by real time `1`, while
`false`'s claim takes `2` to reach it. -/
def drifting : Environment Bool :=
  ⟨fun w t => if w then min (2 * t) (t + 1) else t, fun v _ _ => if v then 0 else 2⟩

def driftingClaims : Claims Bool := ⟨fun _ => 0, fun w => if w then 1 else 2⟩

theorem drift_two_winners :
    Waited drifting driftingClaims 2 ∧ DelaysWithin drifting.delay 2 ∧
      SkewWithin drifting.clock 1 ∧ RateBounds (drifting.clock true) 1 0 2 ∧
      ProceedsAt drifting driftingClaims twoRank false ∧
      ProceedsAt drifting driftingClaims twoRank true := by
  refine ⟨fun w => ?_, fun v _ _ => ?_, fun p q t => ?_, ⟨fun t d => ?_, fun t d => ?_⟩, ?_, ?_⟩
  · cases w <;> simp [stamp, drifting, driftingClaims]
  · cases v <;> simp [drifting]
  · cases p <;> cases q <;> simp [drifting]
    all_goals omega
  · simp only [drifting, if_true]; omega
  · simp only [drifting, if_true]; omega
  · intro v apart _ before
    cases v
    · exact apart rfl
    · simp [Before, stamp, drifting, driftingClaims, twoRank] at before
  · intro v apart received _
    cases v
    · simp [Received, drifting, driftingClaims] at received
    · exact apart rfl

/-- **Positive control**: a synchronous instance of `winner_unique`'s hypotheses (perfect clocks,
delay `1`, wait `2`, no skew) in which exactly one claimant proceeds, the earliest. -/
def synchronized : Environment Bool := ⟨fun _ t => t, fun _ _ _ => 1⟩

theorem synchronous_one_winner :
    Waited synchronized (sameTime 2) 2 ∧ DelaysWithin synchronized.delay 1 ∧
      SkewWithin synchronized.clock 0 ∧
      ProceedsAt synchronized (sameTime 2) twoRank false ∧
      ¬ ProceedsAt synchronized (sameTime 2) twoRank true := by
  refine ⟨fun w => ⟨by simp [sameTime], by simp [stamp, synchronized, sameTime]⟩,
    fun _ _ _ => le_rfl, fun _ _ _ => by simp [synchronized], ?_, ?_⟩
  · intro v apart _ before
    cases v
    · exact apart rfl
    · simp [Before, stamp, twoRank, synchronized, sameTime] at before
  · intro proceeds
    exact proceeds false (by decide) (by simp [Received, synchronized, sameTime])
      (Or.inr ⟨rfl, by simp [twoRank]⟩)

end Controls

end Mettapedia.GSLT.Timing.WinnerRule
