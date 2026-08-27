/-!
# FuelPolicy — what a renewal does to the budget it finds

`HeartModel.loops_bounded` says "the budget never exceeds `maxLoops`,
whatever happens", and `ClawArchitectures.breath_self_paced` says a single
renewal cycle holds at most `full` turns. Both are true of the loop as it
was written, and both are consequences of one unexamined decision: every
grant site *overwrote* the budget it found. An unspent burst was simply
lost at the next renewal.

That is a choice, not a law. It encodes the claim that each interval is a
fresh, equal breath and that restraint earns nothing. This file makes the
choice explicit as a `Fuel` discipline, proves the ceiling each one
guarantees, and says exactly which of the older theorems each preserves.

The headline: `saturate` is the only discipline under which
`loops_bounded` holds. That theorem was never about the agent — it was
about the grant site. `carry` and `decay` replace it with wider but still
finite ceilings; `accumulate` removes it, deliberately, and that removal
IS the mode's content — restraint becomes convertible into a longer breath
later.

Nothing here touches the autonomy floor. `starvation_bounded`,
`rest_is_a_nap` and `RestEnergy.unbounded_self_directed_work` depend only
on a renewal happening and granting at least one turn, which
`refuel_never_starves` guarantees for every discipline.

Correspondence (hand-maintained, as in the sibling files): `Fuel` ↔ the
persisted selection in `memory/fuel_mode.json`; `refuel` ↔
`fuel_modes.refuel`, called by `applyHeartbeat` and `applyAutonomousBurst`
in `src/loop.metta`; `carryMultiple` ↔ `fuel_modes.CARRY`; `full` ↔
`(policy-burst-budget agent)` = 50. The arithmetic is integer on both
sides on purpose — the ceilings below are exact statements about the code
that runs, not about a real-valued idealisation of it.

Human arming is out of scope here, and stays a saturating `max` in the
code: a message means work has arrived, and the communication layer grants
one breath to answer it rather than minting fuel.
-/

namespace FuelPolicy

/-- One full burst. -/
def full : Nat := 50

/-- The `carry` ceiling, in full bursts. -/
def carryMultiple : Nat := 4

inductive Fuel
  | saturate
  | accumulate
  | carry
  | decay
deriving Repr, DecidableEq

/-- A renewal, as a function of what is held and what is offered. -/
def refuel : Fuel → Nat → Nat → Nat
  | .saturate,   held, grant => max held grant
  | .accumulate, held, grant => held + grant
  | .carry,      held, grant => min (carryMultiple * grant) (held + grant)
  | .decay,      held, grant => held * 3 / 4 + grant

/-- `k` successive renewals. -/
def refuelN (f : Fuel) (grant : Nat) : Nat → Nat → Nat
  | 0,     held => held
  | k + 1, held => refuelN f grant k (refuel f held grant)

/-! ## The floor every discipline keeps

This is the property the autonomy theorems rest on. None of the ceilings
below may be bought at the price of a renewal that grants nothing. -/

/-- **No discipline starves a renewal.** Whatever is held and whichever
discipline is active, a renewal leaves at least the offered burst — so
`starvation_bounded` and `rest_is_a_nap` survive every choice here. -/
theorem refuel_never_starves (f : Fuel) (held grant : Nat) :
    grant ≤ refuel f held grant := by
  cases f
  · exact Nat.le_max_right _ _
  · exact Nat.le_add_left _ _
  · exact Nat.le_min.mpr ⟨by
      show grant ≤ carryMultiple * grant
      calc grant = 1 * grant := (Nat.one_mul grant).symm
        _ ≤ carryMultiple * grant :=
            Nat.mul_le_mul_right grant (by decide), Nat.le_add_left _ _⟩
  · exact Nat.le_add_left _ _

/-! ## The ceilings -/

/-- `saturate` holds the budget at one full burst: today's behaviour, and
the reason `HeartModel.loops_bounded` was provable. -/
theorem saturate_step (held grant : Nat) (h : held ≤ grant) :
    refuel .saturate held grant ≤ grant :=
  Nat.max_le.mpr ⟨h, Nat.le_refl _⟩

theorem saturate_bounded (grant : Nat) :
    ∀ (k held : Nat), held ≤ grant → refuelN .saturate grant k held ≤ grant := by
  intro k
  induction k with
  | zero => intro held h; exact h
  | succ n ih => intro held h; exact ih _ (saturate_step held grant h)

/-- `carry` needs no invariant: the ceiling is enforced at every step. -/
theorem carry_bounded (grant : Nat) :
    ∀ (k held : Nat), 0 < k → refuelN .carry grant k held ≤ carryMultiple * grant := by
  intro k
  induction k with
  | zero => intro _ h; exact absurd h (by decide)
  | succ n ih =>
    intro held _
    cases n with
    | zero => exact Nat.min_le_left _ _
    | succ m => exact ih _ (Nat.succ_pos m)

/-- `decay` shares `carry`'s ceiling and differs only in how it gets there:
three quarters of what is held carries over, and the rate is 3/4 precisely
so that the fixed point of `x ↦ 3x/4 + grant` is `carryMultiple * grant`.
carry accumulates at full rate and stops dead at the ceiling; decay forgets
a quarter each renewal and converges to it. -/
theorem decay_step (held grant : Nat) (h : held ≤ carryMultiple * grant) :
    refuel .decay held grant ≤ carryMultiple * grant := by
  have hheld : held ≤ 4 * grant := h
  show held * 3 / 4 + grant ≤ 4 * grant
  omega

theorem decay_bounded (grant : Nat) :
    ∀ (k held : Nat), held ≤ carryMultiple * grant →
      refuelN .decay grant k held ≤ carryMultiple * grant := by
  intro k
  induction k with
  | zero => intro held h; exact h
  | succ n ih => intro held h; exact ih _ (decay_step held grant h)

/-- **The two bounded disciplines agree on the limit.** Stated once, so the
shared ceiling is a theorem rather than a coincidence of two constants. -/
theorem carry_and_decay_share_a_ceiling (grant : Nat) :
    ∀ (k held : Nat), 0 < k → held ≤ carryMultiple * grant →
      refuelN .carry grant k held ≤ carryMultiple * grant ∧
      refuelN .decay grant k held ≤ carryMultiple * grant :=
  fun k held hk h => ⟨carry_bounded grant k held hk, decay_bounded grant k held h⟩

/-! ## The one that has none -/

theorem accumulate_iter (grant : Nat) :
    ∀ (k held : Nat), refuelN .accumulate grant k held = held + k * grant := by
  intro k
  induction k with
  | zero => intro held; simp [refuelN]
  | succ n ih =>
    intro held
    show refuelN .accumulate grant n (held + grant) = _
    rw [ih (held + grant)]
    have : (n + 1) * grant = n * grant + grant := by
      rw [Nat.succ_mul]
    omega

/-- **`accumulate` has no ceiling.** For every bound, some number of
renewals passes it — with no human anywhere, purely by not spending. This
is the mode's content, not a defect: unspent breath becomes convertible
into a longer one later. -/
theorem accumulate_has_no_ceiling (grant : Nat) (hg : 0 < grant) (bound : Nat) :
    ∃ k, bound < refuelN .accumulate grant k 0 := by
  refine ⟨bound + 1, ?_⟩
  rw [accumulate_iter grant (bound + 1) 0]
  have : bound + 1 ≤ (bound + 1) * grant :=
    Nat.le_mul_of_pos_right (bound + 1) hg
  omega

/-! ## Which older theorems survive

`HeartModel.loops_bounded` is stated there as an invariant of the whole
step relation. Restated as a property of the grant site, it holds for
`saturate` and fails for `accumulate` — so the theorem was never about the
agent's restraint, it was about which discipline the code happened to
implement. -/

/-- `saturate` is exactly the discipline `loops_bounded` describes. -/
theorem saturate_preserves_loops_bounded (held : Nat) (h : held ≤ full) :
    refuel .saturate held full ≤ full :=
  saturate_step held full h

/-- Under `accumulate` the budget leaves `full` behind, so the breath is no
longer bounded by one burst. -/
theorem accumulate_breaks_loops_bounded :
    ∃ held, held ≤ full ∧ ¬ (refuel .accumulate held full ≤ full) := by
  refine ⟨1, by decide, ?_⟩
  decide

/-- The wider disciplines are still finite: both hold at most
`carryMultiple` full bursts, so a bounded-breath theorem survives in a
weaker form rather than disappearing. -/
theorem carry_and_decay_stay_finite (held : Nat) :
    refuel .carry held full ≤ carryMultiple * full ∧
    (held ≤ carryMultiple * full →
      refuel .decay held full ≤ carryMultiple * full) :=
  ⟨Nat.min_le_left _ _, decay_step held full⟩

end FuelPolicy

/-! ## Axiom audit (kernel-level trust check) -/
#print axioms FuelPolicy.refuel_never_starves
#print axioms FuelPolicy.saturate_bounded
#print axioms FuelPolicy.carry_bounded
#print axioms FuelPolicy.decay_bounded
#print axioms FuelPolicy.carry_and_decay_share_a_ceiling
#print axioms FuelPolicy.accumulate_iter
#print axioms FuelPolicy.accumulate_has_no_ceiling
#print axioms FuelPolicy.saturate_preserves_loops_bounded
#print axioms FuelPolicy.accumulate_breaks_loops_bounded
#print axioms FuelPolicy.carry_and_decay_stay_finite
