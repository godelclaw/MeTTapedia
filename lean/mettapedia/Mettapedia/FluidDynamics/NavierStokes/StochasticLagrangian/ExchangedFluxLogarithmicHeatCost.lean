import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorShellBudget

/-!
# A logarithmically weighted half-derivative heat-test cost

The shell bound is summed using the exact allocation
`1 / ((n+1)*(n+2))`. The remaining positive-order square cost has weight
`2^n*(n+1)*(n+2)`, not the previous full-derivative weight of order `4^n`.
The test is the actual nonlinear adjoint. Its new cost may still be
infinite; neither this estimate nor its finiteness is a global closure.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxLogarithmicHeatCost

open scoped ENNReal RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLocalInfiniteVelocity InfiniteConvectionEnergy
open FourierHeatCommutatorShellBudget ExchangedFluxHeatDualBudget ExchangedFluxHeatAdjoint
open FourierHeatFlow PancakeCoefficientLimitEquation PancakeFilteredStrainDynamics

theorem nonlinearCommutator_zero (ν σ : ℝ) (u : FourierVelocity) :
    nonlinearCommutator ν σ u 0 = 0 := by
  simp [nonlinearCommutator, coefficients, filteredVelocity, infiniteVelocityRHS_zero]

def coefficientPairingCost (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) (q : Wavevector) : ℝ≥0∞ :=
  ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
    ENNReal.ofReal (2 * |⟪coefficientVec (nonlinearCommutator ν σ (u τ) q),
      heatCoefficientTest ν σ (u τ) q⟫|)

def shellPairingCost (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∑ q ∈ IntegerDyadicShell.shell n, coefficientPairingCost ν u t q

def logarithmicTestCost (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ n * ((n : ℝ) + 1) * (n + 2)) * shellTestCost ν u t n

theorem coefficientPairingCost_zero (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) :
    coefficientPairingCost ν u t 0 = 0 := by
  simp [coefficientPairingCost, nonlinearCommutator_zero, coefficientVec]

theorem absolutePairingCost_eq_tsum_shells (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) :
    absolutePairingCost ν u t = ∑' n, shellPairingCost ν u t n :=
  (IntegerDyadicShell.tsum_shells (coefficientPairingCost ν u t)
    (coefficientPairingCost_zero ν u t)).symm

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)

include hg hsg hu

theorem shellPairingCost_le_initial_add_test (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    shellPairingCost ν s.coefficients t n ≤
      ENNReal.ofReal (a * initialShellBudget ν u₀) +
        ENNReal.ofReal ((2 : ℝ) ^ n / a) * shellTestCost ν s.coefficients t n := by
  have h := Finset.sum_le_sum (s := IntegerDyadicShell.shell n) (fun q _ ↦
    ExchangedFluxHeatDualBudget.coefficientPairingCost_le s g hg hsg hu hν t ht q
      (by positivity : 0 < a / (2 : ℝ) ^ n))
  have he : (a / (2 : ℝ) ^ n)⁻¹ = (2 : ℝ) ^ n / a := inv_div _ _
  simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  change shellPairingCost ν s.coefficients t n ≤
    ENNReal.ofReal (a / (2 : ℝ) ^ n) * shellCommutatorCost ν s.coefficients t n + _ at h
  apply h.trans
  apply add_le_add _ le_rfl
  apply (mul_le_mul_right (shellCommutatorCost_le_initial s g hg hsg hu hν t ht n) _).trans_eq
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- Arbitrary positive allocations retain the exact unpaid shell-test cost. -/
theorem absolutePairingCost_le_of_allocation (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) :
    absolutePairingCost ν s.coefficients t ≤
      ENNReal.ofReal (initialShellBudget ν u₀) * (∑' n, ENNReal.ofReal (a n)) +
        ∑' n, ENNReal.ofReal ((2 : ℝ) ^ n / a n) * shellTestCost ν s.coefficients t n := by
  rw [absolutePairingCost_eq_tsum_shells]
  have h := ENNReal.tsum_le_tsum (fun n ↦
    shellPairingCost_le_initial_add_test s g hg hsg hu hν t ht n (ha n))
  simpa only [ENNReal.tsum_add, ENNReal.ofReal_mul (ha _).le,
    ENNReal.tsum_mul_right, mul_comm] using h

/-- The full all-scale pairing costs initial energy plus a half-derivative
test norm with an explicit logarithmic correction. -/
theorem absolutePairingCost_le_initial_add_logarithmic (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε) :
    absolutePairingCost ν s.coefficients t ≤
      ENNReal.ofReal ε * ENNReal.ofReal (initialShellBudget ν u₀) +
        ENNReal.ofReal ε⁻¹ * logarithmicTestCost ν s.coefficients t := by
  have h := absolutePairingCost_le_of_allocation s g hg hsg hu hν t ht
    (fun n ↦ ε * IntegerDyadicShell.summationWeight n)
    (fun n ↦ mul_pos hε (IntegerDyadicShell.summationWeight_pos n))
  have he (n : ℕ) : (2 : ℝ) ^ n / (ε * IntegerDyadicShell.summationWeight n) =
      ε⁻¹ * ((2 : ℝ) ^ n * ((n : ℝ) + 1) * (n + 2)) := by
    unfold IntegerDyadicShell.summationWeight
    field_simp
  simp only [he, ENNReal.ofReal_mul hε.le, ENNReal.tsum_mul_left,
    IntegerDyadicShell.tsum_ofReal_summationWeight, mul_one,
    ENNReal.ofReal_mul (inv_nonneg.mpr hε.le), mul_assoc] at h
  simpa only [← ENNReal.tsum_mul_left, logarithmicTestCost, mul_comm, mul_left_comm, mul_assoc] using h

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxLogarithmicHeatCost
