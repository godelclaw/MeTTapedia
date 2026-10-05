import Mettapedia.Cybernetics.DistinctionCalculus.Basic
import Mettapedia.GSLT.Core.NonFactorization
import MettapediaNS.WholeSpaceHistoryBridge

/-!
# Real distinction observers for actual fluid histories

The distinction calculus supplies observer-relative bounded distances. This
module instantiates its real-valued tolerance with a clipped energy readout.
A uniform margin below saturation recovers an unbounded physical energy
estimate; at derivative order one the existing whole-space continuation theorem
then applies. The bound must precede all same-datum solution prefixes.

The coupled-parent control at the end uses the explicit polynomial readout
identified by the complete degree-twelve calculation. Its factorization
obstruction is kernel-checked algebra. Identification with an actual PDE time
jet is analytic and independently checked in `distinction_coupled_history.py`.

The signed reserve contract is the existing `BoundaryBellman.Bounds` on actual
`WholeSpaceHistoryBridge.WindowStep` witnesses. Its finite initial payment gives
a concrete nonsaturating observer bound. Existence of an order-one reserve is
still an open physical estimate, not a consequence of bounded distances.

The upstream tolerance is from Goertzel's distinction calculus, as formalized
in MeTTapedia revision `3b432626d`. No identification of a scalar energy view
with a complete predictive state is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.DistinctionHistory

open Mettapedia.Cybernetics.DistinctionCalculus
open Mettapedia.GSLT.Dynamics.BoundaryBellman
open WholeSpaceOrderEnergy WholeSpaceViscousFlow WholeSpaceHistoryBridge
open EulerSmoothLimit EulerLpTranslation EulerMeanSolenoidal Set

/-- A scalar energy observer with an explicit physical scale. -/
def energyTolerance (M : ℝ) (hM : 0 < M) : Tolerance ℝ ℝ where
  similarity x y := 1 - min 1 (|x - y| / M)
  nonnegative x y := sub_nonneg.mpr (min_le_left _ _)
  bounded x y := sub_le_self _ (le_min (by norm_num)
    (div_nonneg (abs_nonneg _) hM.le))
  reflexive x := by simp
  symmetric x y := by rw [abs_sub_comm]

theorem energyTolerance_distance (M : ℝ) (hM : 0 < M) (x y : ℝ) :
    (energyTolerance M hM).distance x y = min 1 (|x - y| / M) := by
  simp [Tolerance.distance, energyTolerance]

/-- Clipping a scaled scalar distance still obeys the triangle law. -/
theorem energyTolerance_metric (M : ℝ) (hM : 0 < M) :
    (energyTolerance M hM).Metric := by
  intro x y z
  simp only [energyTolerance_distance]
  have left : 0 ≤ |x - y| / M := div_nonneg (abs_nonneg _) hM.le
  have right : 0 ≤ |y - z| / M := div_nonneg (abs_nonneg _) hM.le
  by_cases first : 1 ≤ |x - y| / M
  · rw [min_eq_left first]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (le_min (by norm_num) right))
  · by_cases second : 1 ≤ |y - z| / M
    · rw [min_eq_left second]
      exact (min_le_left _ _).trans (le_add_of_nonneg_left (le_min (by norm_num) left))
    · rw [min_eq_right (le_of_not_ge first), min_eq_right (le_of_not_ge second)]
      calc min 1 (|x - z| / M) ≤ |x - z| / M := min_le_right _ _
        _ ≤ (|x - y| + |y - z|) / M :=
          div_le_div_of_nonneg_right (abs_sub_le x y z) hM.le
        _ = |x - y| / M + |y - z| / M := add_div _ _ _

/-- The actual order-energy report, expressed as a distinction from zero. -/
def energyScore (M : ℝ) (hM : 0 < M) (n : ℕ) (A : SmoothL2Field Space) : ℝ :=
  (energyTolerance M hM).distance (orderEnergy n A) 0

/-- An observer bound below saturation is precisely a physical energy bound. -/
theorem energyScore_le_iff (M : ℝ) (hM : 0 < M) (q : ℝ) (hq : q < 1)
    (n : ℕ) (A : SmoothL2Field Space) :
    energyScore M hM n A ≤ q ↔ orderEnergy n A ≤ q * M := by
  rw [energyScore, energyTolerance_distance, sub_zero,
    abs_of_nonneg (orderEnergy_nonneg n A)]
  constructor
  · intro bound
    have raw : orderEnergy n A / M ≤ q := by
      by_contra exceeds
      have : q < min 1 (orderEnergy n A / M) := lt_min hq (lt_of_not_ge exceeds)
      exact (not_lt_of_ge bound) this
    exact (div_le_iff₀ hM).mp raw
  · intro bound
    exact (min_le_right _ _).trans ((div_le_iff₀ hM).mpr bound)

/-- Above the chosen scale the observer cannot distinguish larger energies. -/
theorem energyScore_saturated (M : ℝ) (hM : 0 < M) (n : ℕ)
    (A : SmoothL2Field Space) (large : M ≤ orderEnergy n A) :
    energyScore M hM n A = 1 := by
  rw [energyScore, energyTolerance_distance, sub_zero,
    abs_of_nonneg (orderEnergy_nonneg n A)]
  apply min_eq_left
  exact (le_div_iff₀ hM).mpr (by simpa using large)

/-- Actual signed history payment supplies a uniform margin from saturation.
The same original reserve fixes both the physical scale and the margin. -/
theorem energyScore_le_of_reserve {ν T H : ℝ} {hT : 0 ≤ T} {n : ℕ}
    (U : NSEvolution ν T hT) (hTH : T ≤ H) (reserve : TimedState → ℝ)
    (nonnegative : ∀ state, 0 ≤ reserve state)
    (bound : (window ν H n).Bounds reserve reserve) :
    let Z := orderEnergy n (U.velocity ⟨0, le_rfl, hT⟩) +
      reserve (0, U.velocity ⟨0, le_rfl, hT⟩)
    ∃ hM : 0 < Z + 1, Z / (Z + 1) < 1 ∧
      ∀ t : Icc (0 : ℝ) T,
        energyScore (Z + 1) hM n (U.velocity t) ≤ Z / (Z + 1) := by
  let Z := orderEnergy n (U.velocity ⟨0, le_rfl, hT⟩) +
    reserve (0, U.velocity ⟨0, le_rfl, hT⟩)
  have hZ : 0 ≤ Z := add_nonneg (orderEnergy_nonneg n _) (nonnegative _)
  have hM : 0 < Z + 1 := by linarith
  have hq : Z / (Z + 1) < 1 := (div_lt_one hM).mpr (by linarith)
  refine ⟨hM, hq, ?_⟩
  intro t
  apply (energyScore_le_iff _ hM _ hq _ _).mpr
  rw [div_mul_cancel₀ _ (ne_of_gt hM)]
  exact orderEnergy_le_of_reserve U hTH reserve nonnegative bound t

/-- A datum-fixed nonsaturation estimate on every physical prefix closes the
whole-space continuation criterion. Obtaining this estimate remains open. -/
theorem hasNSEvolution_of_distinction_bound {ν : ℝ} (hν : 0 < ν)
    (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace)
    (hbound : ∀ H : ℝ, ∃ (M q : ℝ) (hM : 0 < M), q < 1 ∧
      ∀ S (hS : 0 < S), S ≤ H → ∀ U : NSEvolution ν S hS.le,
        U.velocity ⟨0, le_rfl, hS.le⟩ = A → ∀ t,
          energyScore M hM 1 (U.velocity t) ≤ q) :
    ∀ T, 0 < T → HasNSEvolution ν A T := by
  apply hasNSEvolution_of_orderOne_bound hν A hA
  intro H
  obtain ⟨M, q, hM, hq, bound⟩ := hbound H
  refine ⟨q * M, ?_⟩
  intro S hS hSH U hU t
  exact (energyScore_le_iff M hM q hq 1 _).mp (bound S hS hSH U hU t)

namespace CoupledParents

/-- The ordered amplitudes of the periodic three-parent datum. -/
structure Seed where
  A : ℚ
  B : ℚ
  C : ℚ

/-- Original scalar energy, complete source amplitude and leading work factor.
All initial modes have radius one in the physical instance. -/
def shadow (seed : Seed) : ℚ × ℚ × ℚ :=
  ((seed.A ^ 2 + seed.B ^ 2 + seed.C ^ 2) / 2,
    seed.A * seed.C, seed.A ^ 4 * seed.B ^ 2 * seed.C ^ 4)

/-- Ninth time derivative of the degree-twelve generated self-work coefficient.
The separate PDE identification remains analytic. -/
def ninthJet (seed : Seed) : ℚ :=
  seed.A ^ 4 * seed.B ^ 2 * seed.C ^ 4 *
    (-150354011 / 950400 * seed.A ^ 2 - 18702523 / 129600 * seed.B ^ 2 -
      35270591 / 2376000 * seed.C ^ 2)

/-- A concrete nontrivial fibre: equal energy/source/leading work, different
next nonlinear work. Both endpoints are identified with unforced data in
the analytic coupled-parent calculation. -/
def costFiber : Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber shadow ninthJet where
  left := ⟨2, 1, 1⟩
  right := ⟨1, 1, 2⟩
  sameShadow := by norm_num [shadow]
  differentValue := by norm_num [ninthJet]

theorem ninthJet_not_factors :
    ¬ Mettapedia.GSLT.Core.NonFactorization.Factors shadow ninthJet :=
  costFiber.not_factors

/-- The hidden difference is an explicitly signed physical-jet coefficient. -/
theorem cost_difference : ninthJet ⟨2, 1, 1⟩ - ninthJet ⟨1, 1, 2⟩ = -75692097 / 11000 := by
  norm_num [ninthJet]

end CoupledParents

end Mettapedia.FluidDynamics.NavierStokes.DistinctionHistory
