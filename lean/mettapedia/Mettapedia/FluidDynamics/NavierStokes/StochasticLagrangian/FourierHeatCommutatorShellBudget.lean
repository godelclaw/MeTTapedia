import Mettapedia.Analysis.IntegerDyadicShell
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxHeatDualBudget

/-!
# Critical shell payment for the actual heat commutator

The complete physical-time and auxiliary-heat square cost on a shell
of radius `2^n` is bounded by initial kinetic energy squared times `2^n`.
Thus the negative half-derivative shell cost is uniform in the scale.
This does not assert summability of those uniform costs over all shells.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorShellBudget

open scoped ENNReal
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLocalInfiniteVelocity InfiniteConvectionEnergy
open FourierHeatCommutatorScaleBudget ExchangedFluxHeatDualBudget PancakeIndexedFourierMoments

theorem height_le_norm_frequency (q : Wavevector) :
    (IntegerDyadicShell.height q : ℝ) ≤ ‖frequencyVec q‖ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i : Fin 3 ↦ (q i).natAbs)
  rw [IntegerDyadicShell.height, hi]
  simpa using norm_frequency_coordinate_le q i

theorem radius_le_norm_frequency {n : ℕ} {q : Wavevector}
    (hq : q ∈ IntegerDyadicShell.shell n) : (2 : ℝ) ^ n ≤ ‖frequencyVec q‖ := by
  have h := (IntegerDyadicShell.mem_shell n q).mp hq
  have hc : (2 : ℝ) ^ n ≤ (IntegerDyadicShell.height q : ℝ) := by exact_mod_cast h.1
  exact hc.trans (height_le_norm_frequency q)

def initialShellBudget (ν : ℝ) (u₀ : FourierVelocity) : ℝ :=
  125 * kineticEnergy u₀ ^ 2 / (2 * ν ^ 2 * (2 * Real.pi) ^ 2)

theorem initialShellBudget_nonneg (ν : ℝ) (u₀ : FourierVelocity) :
    0 ≤ initialShellBudget ν u₀ := by unfold initialShellBudget; positivity

def shellCommutatorCost (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∑ q ∈ IntegerDyadicShell.shell n, commutatorSquareIntegral ν u t q

def shellTestCost (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∑ q ∈ IntegerDyadicShell.shell n, testSquareIntegral ν u t q

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)

include hg hsg hu

theorem coefficientCost_le_shell_radius (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) {n : ℕ} {q : Wavevector}
    (hq : q ∈ IntegerDyadicShell.shell n) :
    commutatorSquareIntegral ν s.coefficients t q ≤
      ENNReal.ofReal (kineticEnergy u₀ ^ 2 /
        (2 * ν ^ 2 * (2 * Real.pi) ^ 2 * ((2 : ℝ) ^ n) ^ 2)) := by
  rw [commutatorSquareIntegral_eq s g hg hsg hu hν t ht q]
  apply ENNReal.ofReal_le_ofReal
  apply (integral_accumulatedCoefficient_le_initial s g hg hsg hu hν q
    (IntegerDyadicShell.ne_zero_of_mem_shell hq) t ht).trans
  gcongr
  exact radius_le_norm_frequency hq

theorem shellCommutatorCost_le_initial (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (n : ℕ) :
    shellCommutatorCost ν s.coefficients t n ≤
      ENNReal.ofReal (initialShellBudget ν u₀ * (2 : ℝ) ^ n) := by
  have h := Finset.sum_le_sum (s := IntegerDyadicShell.shell n) (fun q hq ↦
    coefficientCost_le_shell_radius s g hg hsg hu hν t ht hq)
  change shellCommutatorCost ν s.coefficients t n ≤ _ at h
  apply h.trans
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hc : ((IntegerDyadicShell.shell n).card : ℝ) ≤ 125 * ((2 : ℝ) ^ n) ^ 3 := by
    exact_mod_cast IntegerDyadicShell.card_shell_le n
  calc
    _ ≤ (125 * ((2 : ℝ) ^ n) ^ 3) *
        (kineticEnergy u₀ ^ 2 / (2 * ν ^ 2 * (2 * Real.pi) ^ 2 * ((2 : ℝ) ^ n) ^ 2)) := by
      gcongr
    _ = _ := by unfold initialShellBudget; field_simp

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorShellBudget
