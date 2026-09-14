import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorPowerBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxLogarithmicHeatCost

/-!
# A nonquadratic all-scale cost for the actual heat adjoint

Young's conjugate exponents `8/3` and `8/5` leave a Fourier `8/5` test
cost with weight `2^n * ((n+1)*(n+2))^(3/5)`. Initial kinetic energy
pays the commutator term. Neither this cost nor its physical-space
derivative requirements are identified with vorticity dissipation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxPowerHeatCost

open scoped ENNReal RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLocalInfiniteVelocity InfiniteConvectionEnergy
open FourierHeatFlow FourierHeatCommutatorTime FourierHeatCommutatorParameter
open FourierHeatCommutatorScaleBudget FourierHeatCommutatorShellBudget
open FourierHeatCommutatorPowerBudget ExchangedFluxHeatDualBudget ExchangedFluxHeatAdjoint
open ExchangedFluxLogarithmicHeatCost

def testPowerIntegral (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) (q : Wavevector) : ℝ≥0∞ :=
  ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
    ENNReal.ofReal (‖heatCoefficientTest ν σ (u τ) q‖ ^ (8 / 5 : ℝ))

def shellTestPowerCost (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∑ q ∈ IntegerDyadicShell.shell n, testPowerIntegral ν u t q

/-- A Fourier-coefficient cost, not a physical-space `L^(8/5)` norm. -/
def logarithmicTestPowerCost (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ n * (((n : ℝ) + 1) * (n + 2)) ^ (3 / 5 : ℝ)) *
    shellTestPowerCost ν u t n

theorem normalized_allocation_rpow (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (a / ((2 : ℝ) ^ n) ^ (5 / 3 : ℝ)) ^ (-3 / 5 : ℝ) =
      (2 : ℝ) ^ n * a ^ (-3 / 5 : ℝ) := by
  rw [Real.div_rpow ha.le (by positivity), ← Real.rpow_mul (by positivity)]
  norm_num only [show (5 / 3 : ℝ) * (-3 / 5) = -1 by norm_num]
  rw [Real.rpow_neg_one, div_inv_eq_mul, mul_comm]

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)

include hg hsg hu

theorem coefficientPairingCost_le_square_add_power (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) {n : ℕ} {q : Wavevector}
    (hq : q ∈ IntegerDyadicShell.shell n) {a : ℝ} (ha : 0 < a) :
    coefficientPairingCost ν s.coefficients t q ≤
      ENNReal.ofReal (2 * a * (initialAmplitude u₀ * (2 : ℝ) ^ n) ^ (2 / 3 : ℝ)) *
        commutatorSquareIntegral ν s.coefficients t q +
      ENNReal.ofReal (2 * a ^ (-3 / 5 : ℝ)) * testPowerIntegral ν s.coefficients t q := by
  let c := fun σ ↦ ∫⁻ τ : ℝ in Set.Ioc 0 t,
    ENNReal.ofReal (‖coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q)‖ ^ 2)
  have hc : AEMeasurable c (volume.restrict (Set.Ioi 0)) := by
    have hm : AEMeasurable (fun σ ↦ ENNReal.ofReal
        (accumulatedCoefficient ν s.coefficients σ t q)) (volume.restrict (Set.Ioi 0)) :=
      (((continuousOn_integral_norm_commutator_sq s g hg hsg hu hν.le q t ht).mono
        Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi).aemeasurable.ennreal_ofReal
    apply hm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
    exact (lintegral_commutator_sq_eq s g hg hsg hu hν hσ.le t ht q).symm
  calc
    _ ≤ ∫⁻ σ : ℝ in Set.Ioi 0,
        ENNReal.ofReal (2 * a * (initialAmplitude u₀ * (2 : ℝ) ^ n) ^ (2 / 3 : ℝ)) * c σ +
        ENNReal.ofReal (2 * a ^ (-3 / 5 : ℝ)) *
          (∫⁻ τ : ℝ in Set.Ioc 0 t, ENNReal.ofReal
            (‖heatCoefficientTest ν σ (s.coefficients τ) q‖ ^ (8 / 5 : ℝ))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
      apply WeightedYoung.lintegral_two_mul_abs_inner_le_bounded_eight_fifths _ _ ha
        (mul_nonneg (initialAmplitude_nonneg _) (by positivity))
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
        exact norm_commutator_le_initial_shell s g hg hsg hu hν.le hσ.le τ
          ⟨hτ.1.le, hτ.2.trans ht.2⟩ hq
      · exact (((continuousOn_norm_commutator_sq s g hg hsg hu hν.le hσ.le q).mono
          (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2))).aestronglyMeasurable
            measurableSet_Ioc).aemeasurable.ennreal_ofReal
    _ = _ := by
      rw [lintegral_add_left' (hc.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl

theorem shellPairingCost_le_initial_add_power (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    shellPairingCost ν s.coefficients t n ≤
      ENNReal.ofReal (2 * a * initialPowerShellBudget ν u₀) +
        ENNReal.ofReal (2 * (2 : ℝ) ^ n * a ^ (-3 / 5 : ℝ)) *
          shellTestPowerCost ν s.coefficients t n := by
  have hA := initialAmplitude_nonneg u₀
  have h := Finset.sum_le_sum (s := IntegerDyadicShell.shell n) (fun q hq ↦
    coefficientPairingCost_le_square_add_power s g hg hsg hu hν t ht hq
      (by positivity : 0 < a / ((2 : ℝ) ^ n) ^ (5 / 3 : ℝ)))
  simp only [normalized_allocation_rpow n ha, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← mul_assoc] at h
  change shellPairingCost ν s.coefficients t n ≤
    ENNReal.ofReal _ * shellCommutatorCost ν s.coefficients t n + _ at h
  apply h.trans
  apply add_le_add _ le_rfl
  apply (mul_le_mul_right (shellCommutatorCost_le_initial s g hg hsg hu hν t ht n) _).trans_eq
  rw [← ENNReal.ofReal_mul (by positivity), Real.mul_rpow hA (by positivity)]
  congr 1
  rw [initialPowerShellBudget,
    show (5 / 3 : ℝ) = 2 / 3 + 1 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
  field_simp

theorem absolutePairingCost_le_of_allocation (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) :
    absolutePairingCost ν s.coefficients t ≤
      ENNReal.ofReal (2 * initialPowerShellBudget ν u₀) * (∑' n, ENNReal.ofReal (a n)) +
        ∑' n, ENNReal.ofReal (2 * (2 : ℝ) ^ n * (a n) ^ (-3 / 5 : ℝ)) *
          shellTestPowerCost ν s.coefficients t n := by
  rw [absolutePairingCost_eq_tsum_shells]
  have h := ENNReal.tsum_le_tsum (fun n ↦
    shellPairingCost_le_initial_add_power s g hg hsg hu hν t ht n (ha n))
  have he (n : ℕ) : 2 * a n * initialPowerShellBudget ν u₀ =
      (2 * initialPowerShellBudget ν u₀) * a n := by ring
  simpa only [he, ENNReal.tsum_add,
    ENNReal.ofReal_mul (show 0 ≤ 2 * initialPowerShellBudget ν u₀ from
      mul_nonneg (by norm_num) (initialPowerShellBudget_nonneg _ _)),
    ENNReal.tsum_mul_left] using h

theorem absolutePairingCost_le_initial_add_logarithmic_power (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε) :
    absolutePairingCost ν s.coefficients t ≤
      ENNReal.ofReal (2 * ε * initialPowerShellBudget ν u₀) +
        ENNReal.ofReal (2 * ε ^ (-3 / 5 : ℝ)) * logarithmicTestPowerCost ν s.coefficients t := by
  have h := absolutePairingCost_le_of_allocation s g hg hsg hu hν t ht
    (fun n ↦ ε * IntegerDyadicShell.summationWeight n)
    (fun n ↦ mul_pos hε (IntegerDyadicShell.summationWeight_pos n))
  have he (n : ℕ) : 2 * (2 : ℝ) ^ n *
      (ε * IntegerDyadicShell.summationWeight n) ^ (-3 / 5 : ℝ) =
      (2 * ε ^ (-3 / 5 : ℝ)) *
        ((2 : ℝ) ^ n * (((n : ℝ) + 1) * (n + 2)) ^ (3 / 5 : ℝ)) := by
    rw [Real.mul_rpow hε.le (IntegerDyadicShell.summationWeight_pos n).le]
    unfold IntegerDyadicShell.summationWeight
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    norm_num only [neg_div, neg_neg]
    ring
  simp only [he, ENNReal.ofReal_mul (show 0 ≤ 2 * ε ^ (-3 / 5 : ℝ) by positivity)] at h
  simp only [ENNReal.ofReal_mul hε.le, ENNReal.tsum_mul_left,
    IntegerDyadicShell.tsum_ofReal_summationWeight, mul_one,
    mul_assoc] at h
  rw [← ENNReal.ofReal_mul (show 0 ≤ 2 * initialPowerShellBudget ν u₀ from
    mul_nonneg (by norm_num) (initialPowerShellBudget_nonneg _ _))] at h
  have he0 : (2 * initialPowerShellBudget ν u₀) * ε =
      2 * ε * initialPowerShellBudget ν u₀ := by ring
  simpa only [he0, ← ENNReal.tsum_mul_left, logarithmicTestPowerCost] using h

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxPowerHeatCost
