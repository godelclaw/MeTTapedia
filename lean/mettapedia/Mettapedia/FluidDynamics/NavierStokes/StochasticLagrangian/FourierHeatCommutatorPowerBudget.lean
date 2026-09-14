import Mettapedia.Analysis.WeightedYoung
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorShellBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalSixthDecay

/-!
# Initial-energy payment for the `8/3` commutator moment

The uniform coefficient bound and the integrated square bound both concern
the actual unforced solution. Interpolation pays the higher moment with
initial energy alone, at the explicit shell weight `2^(5n/3)`.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorPowerBudget

open scoped ENNReal
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLocalInfiniteVelocity InfiniteConvectionEnergy
open FourierHeatCommutatorShellBudget ExchangedFluxHeatDualBudget
open FourierHeatFlow FourierHeatCommutatorEnergy LocalKineticEnergy
open PancakePeriodicVorticityEquation PancakePeriodicComplexStretch

theorem norm_frequency_le_six_mul_radius {n : ℕ} {q : Wavevector}
    (hq : q ∈ IntegerDyadicShell.shell n) : ‖frequencyVec q‖ ≤ 6 * (2 : ℝ) ^ n := by
  have hh := (IntegerDyadicShell.mem_shell n q).mp hq
  have hc (i : Fin 3) : (q i).natAbs ≤ 2 * 2 ^ n := by
    have hi := (IntegerDyadicShell.coordinate_le_height q i).trans_lt hh.2
    rw [pow_succ] at hi
    omega
  have hb (i : Fin 3) : ‖wavevectorCoefficient q i‖ ≤ 2 * (2 : ℝ) ^ n := by
    have hz : |q i| ≤ 2 * (2 : ℤ) ^ n := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hc i
    rw [wavevectorCoefficient, Complex.norm_intCast]
    exact_mod_cast hz
  exact (PancakePhysicalSixthDecay.norm_coefficientVec_le_three
    (wavevectorCoefficient q) _ (by positivity) hb).trans_eq (by ring)

def initialAmplitude (u₀ : FourierVelocity) : ℝ := 6 * (2 * Real.pi) * kineticEnergy u₀

theorem initialAmplitude_nonneg (u₀ : FourierVelocity) : 0 ≤ initialAmplitude u₀ := by
  unfold initialAmplitude
  exact mul_nonneg (by positivity) (kineticEnergy_nonneg _)

def initialPowerShellBudget (ν : ℝ) (u₀ : FourierVelocity) : ℝ :=
  initialShellBudget ν u₀ * initialAmplitude u₀ ^ (2 / 3 : ℝ)

theorem initialPowerShellBudget_nonneg (ν : ℝ) (u₀ : FourierVelocity) :
    0 ≤ initialPowerShellBudget ν u₀ :=
  mul_nonneg (initialShellBudget_nonneg _ _)
    (Real.rpow_nonneg (initialAmplitude_nonneg _) _)

def commutatorPowerIntegral (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ)
    (q : Wavevector) : ℝ≥0∞ :=
  ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
    ENNReal.ofReal (‖coefficientVec (nonlinearCommutator ν σ (u τ) q)‖ ^ (8 / 3 : ℝ))

def shellCommutatorPowerCost (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ)
    (n : ℕ) : ℝ≥0∞ := ∑ q ∈ IntegerDyadicShell.shell n, commutatorPowerIntegral ν u t q

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)

include hg hsg hu

theorem norm_commutator_le_initial {σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
    ‖coefficientVec (nonlinearCommutator ν σ (s.coefficients t) q)‖ ≤
      (2 * Real.pi) * ‖frequencyVec q‖ * kineticEnergy u₀ := by
  have hm := hsg.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)
  have he : Summable (fun k ↦ ‖coefficientVec (s.coefficients t k)‖ ^ 2) := by
    simpa only [norm_coefficientVec_sq] using InfiniteKineticCancellation.summable_coefficientEnergy _
      (InfiniteKineticCancellation.summable_amplitude _ (summable_firstMoment_of_second _ hm))
  rw [nonlinearCommutator_eq_subgridForce hν hσ _ hm]
  exact (norm_heat_subgridForce_le_energy hν hσ _ he q).trans
    (mul_le_mul_of_nonneg_left (energy_le_initial s hν g hg hsg hu t ht) (by positivity))

theorem norm_commutator_le_initial_shell {σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) {n : ℕ} {q : Wavevector}
    (hq : q ∈ IntegerDyadicShell.shell n) :
    ‖coefficientVec (nonlinearCommutator ν σ (s.coefficients t) q)‖ ≤
      initialAmplitude u₀ * (2 : ℝ) ^ n := by
  apply (norm_commutator_le_initial s g hg hsg hu hν hσ t ht q).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_frequency_le_six_mul_radius hq)
      (by positivity : 0 ≤ 2 * Real.pi)) (kineticEnergy_nonneg u₀)
  exact h.trans_eq (by unfold initialAmplitude; ring)

theorem commutatorPowerIntegral_le_square (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) {n : ℕ} {q : Wavevector}
    (hq : q ∈ IntegerDyadicShell.shell n) :
    commutatorPowerIntegral ν s.coefficients t q ≤
      ENNReal.ofReal ((initialAmplitude u₀ * (2 : ℝ) ^ n) ^ (2 / 3 : ℝ)) *
        commutatorSquareIntegral ν s.coefficients t q := by
  have hA := initialAmplitude_nonneg u₀
  unfold commutatorPowerIntegral commutatorSquareIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
  have hb := WeightedYoung.rpow_eight_thirds_le_sq_mul (norm_nonneg _)
    (norm_commutator_le_initial_shell s g hg hsg hu hν.le hσ.le τ
      ⟨hτ.1.le, hτ.2.trans ht.2⟩ hq)
  rw [mul_comm] at hb
  simpa only [ENNReal.ofReal_mul (show 0 ≤ (initialAmplitude u₀ * (2 : ℝ) ^ n) ^
    (2 / 3 : ℝ) by positivity)] using ENNReal.ofReal_le_ofReal hb

theorem shellCommutatorPowerCost_le_initial (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (n : ℕ) :
    shellCommutatorPowerCost ν s.coefficients t n ≤
      ENNReal.ofReal (initialPowerShellBudget ν u₀ * ((2 : ℝ) ^ n) ^ (5 / 3 : ℝ)) := by
  have hA := initialAmplitude_nonneg u₀
  have h := Finset.sum_le_sum (s := IntegerDyadicShell.shell n) (fun q hq ↦
    commutatorPowerIntegral_le_square s g hg hsg hu hν t ht hq)
  rw [← Finset.mul_sum] at h
  change shellCommutatorPowerCost ν s.coefficients t n ≤
    ENNReal.ofReal _ * shellCommutatorCost ν s.coefficients t n at h
  apply h.trans
  apply (mul_le_mul_right (shellCommutatorCost_le_initial s g hg hsg hu hν t ht n) _).trans_eq
  rw [← ENNReal.ofReal_mul (by positivity), Real.mul_rpow hA (by positivity)]
  congr 1
  rw [initialPowerShellBudget,
    show (5 / 3 : ℝ) = 2 / 3 + 1 by norm_num,
    Real.rpow_add (by positivity), Real.rpow_one]
  ring

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorPowerBudget
