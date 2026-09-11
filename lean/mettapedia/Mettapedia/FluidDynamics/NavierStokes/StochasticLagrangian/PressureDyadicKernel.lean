import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicSymbol
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputKernel

/-!
# Uniform moments for the exact-partition pressure kernels

The normalized dyadic cutoffs define new inverse Fourier kernels. Their
moment bounds follow from joint smoothness and common compact support,
not from a pointwise comparison with the unnormalized multiplier.
The quadratic output/input factor is retained explicitly.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicKernel

open MeasureTheory Mettapedia.Analysis.CompactSchwartzFamily
open PressureLowOutputCutoff (ratio receiver)
open PressureLowOutputSymbol (pairEquiv commonSupport isCompact_commonSupport)
open PressureLowOutputKernel (parameterSet isCompact_parameterSet mem_parameterSet)
open PressureDyadicSymbol
open scoped ContDiff FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "A" => ℝ × R3

def kernel (a : A) (w v : R3) (i : Fin 3) : 𝓢(E6, ℂ) := 𝓕⁻ (symbol a w v i)

@[simp] theorem fourier_kernel (a : A) (w v : R3) (i : Fin 3) :
    𝓕 (kernel a w v i) = symbol a w v i := FourierTransform.fourier_fourierInv_eq _

theorem exists_uniform_moment (w v : R3) (i : Fin 3) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      (∫ x : E6, ‖x‖ ^ m * ‖kernel (t, e) w v i x‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_fourierInv_moment
    (fun a ↦ symbol a w v i) (contDiff_symbol w v i)
    parameterSet isCompact_parameterSet commonSupport isCompact_commonSupport
    (fun a ↦ tsupport_symbol_subset a w v i) m
  exact ⟨C, hC, fun t ht e he ↦ hb (t, e) (mem_parameterSet t ht e he)⟩

def retainedKernel (a : A) (w v : R3) (i : Fin 3) : 𝓢(E6, ℂ) :=
  (ratio a.1) ^ 2 • kernel a w v i

theorem fourier_retainedKernel (a : A) (w v : R3) (i : Fin 3) (x : E6) :
    (𝓕 (retainedKernel a w v i)) x =
      ((retained a.1 (pairEquiv x) * CoherentPressurePair.tiltPair a.2
        (pairEquiv x).1 (receiver a.1 (pairEquiv x)) w v i : ℝ) : ℂ) := by
  rw [retainedKernel, FourierTransform.fourier_smul, fourier_kernel, entry_eq_pressure]
  simp

theorem moment_retainedKernel (a : A) (w v : R3) (i : Fin 3) (m : ℕ) :
    (∫ x : E6, ‖x‖ ^ m * ‖retainedKernel a w v i x‖) =
      (ratio a.1) ^ 2 * ∫ x : E6, ‖x‖ ^ m * ‖kernel a w v i x‖ := by
  simp only [retainedKernel, smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (ratio a.1))]
  simp_rw [mul_left_comm (‖_‖ ^ m) ((ratio a.1) ^ 2)]
  exact integral_const_mul _ _

theorem exists_uniform_retained_moment (w v : R3) (i : Fin 3) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      (∫ x : E6, ‖x‖ ^ m * ‖retainedKernel (t, e) w v i x‖) ≤ (ratio t) ^ 2 * C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_moment w v i m
  refine ⟨C, hC, fun t ht e he ↦ ?_⟩
  rw [moment_retainedKernel]
  exact mul_le_mul_of_nonneg_left (hb t ht e he) (sq_nonneg _)

@[simp] theorem retainedKernel_zero (e w v : R3) (i : Fin 3) :
    retainedKernel (0, e) w v i = 0 := by simp [retainedKernel, ratio]

theorem exists_uniform_basis_moment (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      ∀ i j l : Fin 3,
      (∫ x : E6, ‖x‖ ^ m * ‖retainedKernel (t, e)
        (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) i x‖) ≤ (ratio t) ^ 2 * C := by
  classical
  choose C hC hb using fun a : Fin 3 × Fin 3 × Fin 3 ↦
    exists_uniform_retained_moment (EuclideanSpace.single a.2.1 1)
      (EuclideanSpace.single a.2.2 1) a.1 m
  refine ⟨∑ a, C a, Finset.sum_nonneg (fun a _ ↦ hC a), ?_⟩
  intro t ht e he i j l
  exact (hb (i, j, l) t ht e he).trans (mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun a _ ↦ hC a) (Finset.mem_univ (i, j, l))) (sq_nonneg _))

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicKernel
