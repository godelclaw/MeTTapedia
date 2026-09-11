import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergenceSymbol
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputKernel

/-!
# Uniform kernels for the coherent longitudinal factorization

The inverse Fourier kernel of the factored symbol has uniformly bounded
moments on the compact ratio/direction parameter set. The retained kernel
includes one output/input ratio. Its Fourier symbol, multiplied by the
sum of the longitudinal input frequencies, is exactly coherent pressure.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceKernel

open MeasureTheory Mettapedia.Analysis.CompactSchwartzFamily
open PressureLowOutputCutoff (ratio receiver)
open PressureLowOutputSymbol (pairEquiv commonSupport isCompact_commonSupport)
open PressureLowOutputKernel (parameterSet isCompact_parameterSet mem_parameterSet)
open PressureCoherentDivergenceSymbol
open scoped ContDiff FourierTransform SchwartzMap RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "A" => ℝ × R3

def kernel (a : A) (i : Fin 3) : 𝓢(E6, ℂ) := 𝓕⁻ (symbol a i)

@[simp] theorem fourier_kernel (a : A) (i : Fin 3) :
    𝓕 (kernel a i) = symbol a i := FourierTransform.fourier_fourierInv_eq _

theorem exists_uniform_moment (i : Fin 3) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      (∫ x : E6, ‖x‖ ^ m * ‖kernel (t, e) i x‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_fourierInv_moment
    (fun a ↦ symbol a i) (contDiff_symbol i)
    parameterSet isCompact_parameterSet commonSupport isCompact_commonSupport
    (fun a ↦ tsupport_symbol_subset a i) m
  exact ⟨C, hC, fun t ht e he ↦ hb (t, e) (mem_parameterSet t ht e he)⟩

def retainedKernel (a : A) (i : Fin 3) : 𝓢(E6, ℂ) :=
  ratio a.1 • kernel a i

theorem fourier_retainedKernel (a : A) (i : Fin 3) (x : E6) :
    (𝓕 (retainedKernel a i)) x = ((ratio a.1 * entry a.1 a.2 i (pairEquiv x) : ℝ) : ℂ) := by
  rw [retainedKernel, FourierTransform.fourier_smul, fourier_kernel]
  simp

theorem retained_pressure_eq_fourier_mul (a : A) (i : Fin 3) (x : E6) :
    ((PressureDyadicSymbol.retained a.1 (pairEquiv x) *
        CoherentPressurePair.tiltPair a.2 (pairEquiv x).1
          (receiver a.1 (pairEquiv x)) a.2 a.2 i : ℝ) : ℂ) =
      (𝓕 (retainedKernel a i)) x *
        ((⟪(pairEquiv x).1, a.2⟫ + ⟪receiver a.1 (pairEquiv x), a.2⟫ : ℝ) : ℂ) := by
  rw [fourier_retainedKernel, ← Complex.ofReal_mul, retained_pressure_eq]

theorem moment_retainedKernel (a : A) (i : Fin 3) (m : ℕ) :
    (∫ x : E6, ‖x‖ ^ m * ‖retainedKernel a i x‖) =
      |ratio a.1| * ∫ x : E6, ‖x‖ ^ m * ‖kernel a i x‖ := by
  simp only [retainedKernel, smul_apply, norm_smul, Real.norm_eq_abs]
  simp_rw [mul_left_comm (‖_‖ ^ m) |ratio a.1|]
  exact integral_const_mul _ _

theorem exists_uniform_retained_moment (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      ∀ i : Fin 3, (∫ x : E6, ‖x‖ ^ m * ‖retainedKernel (t, e) i x‖) ≤ ratio t * C := by
  classical
  choose C hC hb using fun i : Fin 3 ↦ exists_uniform_moment i m
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ ↦ hC i), ?_⟩
  intro t ht e he i
  have hr : 0 ≤ ratio t := div_nonneg ht.1 (by norm_num)
  rw [moment_retainedKernel, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left ((hb i t ht e he).trans
    (Finset.single_le_sum (fun i _ ↦ hC i) (Finset.mem_univ i))) hr

@[simp] theorem retainedKernel_zero (e : R3) (i : Fin 3) :
    retainedKernel (0, e) i = 0 := by simp [retainedKernel, ratio]

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceKernel
