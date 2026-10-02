import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Finite energy and time do not bound an abstract stretching ledger

At length `2^(-n)`, the velocity scale `nu / length` has energy scale
`nu^2 * length`, viscous time `length^2 / nu`, and vorticity scale
`nu / length^2`. The exact sequence below has finite total energy
expenditure and finite total time, but every stage contributes one to
the integrated vorticity scale. Its decreasing reserve pays every stage.

This is arithmetic of an abstract scaling model. There is no NS solution,
pressure, nonlinear transfer, or geometric realization in its hypotheses
or conclusions. It rules out an inference from these ledger quantities
alone, not a regularity estimate using the actual equation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GeometricCascadeLedger

def length (n : ℕ) : ℝ := (1 / 2 : ℝ)^n
def energyCost (ν : ℝ) (n : ℕ) : ℝ := ν^2 * (1 / 2 : ℝ)^n
def duration (ν : ℝ) (n : ℕ) : ℝ := (1 / ν) * (1 / 4 : ℝ)^n
def vorticityScale (ν : ℝ) (n : ℕ) : ℝ := ν * (4 : ℝ)^n
def reserve (ν : ℝ) (n : ℕ) : ℝ := 2 * ν^2 * (1 / 2 : ℝ)^n

theorem positive_stage (ν : ℝ) (hν : 0 < ν) (n : ℕ) :
    0 < length n ∧ 0 < energyCost ν n ∧ 0 < duration ν n ∧
      0 < vorticityScale ν n ∧ 0 < reserve ν n := by
  unfold length energyCost duration vorticityScale reserve
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem reserve_payment (ν : ℝ) (n : ℕ) :
    reserve ν n - reserve ν (n+1) = energyCost ν n := by
  unfold reserve energyCost
  rw [pow_succ]
  ring

theorem duration_eq_viscous_time (ν : ℝ) (n : ℕ) :
    duration ν n = length n ^ 2 / ν := by
  unfold duration length
  rw [← pow_mul, mul_comm n 2, pow_mul]
  norm_num
  ring

theorem stage_stretching (ν : ℝ) (hν : ν ≠ 0) (n : ℕ) :
    duration ν n * vorticityScale ν n = 1 := by
  unfold duration vorticityScale
  calc
    (1 / ν * (1 / 4 : ℝ)^n) * (ν * (4 : ℝ)^n) =
        (1 / 4 : ℝ)^n * (4 : ℝ)^n := by field_simp
    _ = 1 := by rw [← mul_pow]; norm_num

theorem energy_summable (ν : ℝ) : Summable (energyCost ν) := by
  exact (summable_geometric_of_norm_lt_one (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)).mul_left _

theorem duration_summable (ν : ℝ) : Summable (duration ν) := by
  exact (summable_geometric_of_norm_lt_one (show ‖(1 / 4 : ℝ)‖ < 1 by norm_num)).mul_left _

theorem total_energy (ν : ℝ) : (∑' n : ℕ, energyCost ν n) = 2 * ν^2 := by
  unfold energyCost
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)]
  norm_num
  ring

theorem total_duration (ν : ℝ) : (∑' n : ℕ, duration ν n) = 4 / (3*ν) := by
  unfold duration
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (show ‖(1 / 4 : ℝ)‖ < 1 by norm_num)]
  norm_num
  ring

theorem prefix_stretching (ν : ℝ) (hν : ν ≠ 0) (N : ℕ) :
    (∑ n ∈ Finset.range N, duration ν n * vorticityScale ν n) = (N : ℝ) := by
  simp only [stage_stretching ν hν, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- The positive costs have unbounded partial sums; no use is made of
Lean's totalized real `tsum` for a divergent series. -/
theorem stretching_unbounded (ν : ℝ) (hν : ν ≠ 0) (C : ℝ) :
    ∃ N : ℕ, C < ∑ n ∈ Finset.range N, duration ν n * vorticityScale ν n := by
  obtain ⟨N, hN⟩ := exists_nat_gt C
  exact ⟨N, by simpa only [prefix_stretching ν hν N] using hN⟩

end Mettapedia.FluidDynamics.NavierStokes.GeometricCascadeLedger
