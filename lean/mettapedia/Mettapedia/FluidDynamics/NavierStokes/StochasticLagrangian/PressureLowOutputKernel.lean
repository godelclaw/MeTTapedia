import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputSymbol

/-!
# Uniform moments of normalized low-output pressure kernels

These kernels are inverse transforms in input/normalized-output coordinates,
not the original two-input coordinates. The ratio-squared factor is kept
explicit. All spatial moments are uniform down to zero ratio, for every
unit frozen direction. Physical-coordinate dilation and periodization are
separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputKernel

open MeasureTheory Mettapedia.Analysis.CompactSchwartzFamily
open PressureLowOutputCutoff PressureLowOutputSymbol
open scoped ContDiff FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "A" => ℝ × R3

def parameterSet : Set A := Set.Icc (0 : ℝ) (1 / 2) ×ˢ Metric.sphere (0 : R3) 1

theorem isCompact_parameterSet : IsCompact parameterSet :=
  isCompact_Icc.prod (isCompact_sphere (0 : R3) 1)

theorem mem_parameterSet (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2))
    (e : R3) (he : ‖e‖ = 1) : (t, e) ∈ parameterSet := by
  exact ⟨ht, by simpa [Metric.mem_sphere, dist_zero_right] using he⟩

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

theorem exists_uniform_mass_and_firstMoment (w v : R3) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      (∫ x : E6, ‖kernel (t, e) w v i x‖) ≤ C ∧
      (∫ x : E6, ‖x‖ * ‖kernel (t, e) w v i x‖) ≤ C := by
  obtain ⟨C0, hC0, h0⟩ := exists_uniform_moment w v i 0
  obtain ⟨C1, hC1, h1⟩ := exists_uniform_moment w v i 1
  refine ⟨max C0 C1, hC0.trans (le_max_left _ _), ?_⟩
  intro t ht e he
  constructor
  · simpa using (h0 t ht e he).trans (le_max_left C0 C1)
  · simpa using (h1 t ht e he).trans (le_max_right C0 C1)

/-- The retained pressure kernel, still in normalized coordinates. -/
def retainedKernel (a : A) (w v : R3) (i : Fin 3) : 𝓢(E6, ℂ) :=
  (ratio a.1) ^ 2 • kernel a w v i

theorem fourier_retainedKernel (a : A) (w v : R3) (i : Fin 3) (x : E6) :
    (𝓕 (retainedKernel a w v i)) x =
      ((retained a.1 (pairEquiv x) * CoherentPressurePair.tiltPair a.2
        (pairEquiv x).1 (receiver a.1 (pairEquiv x)) w v i : ℝ) : ℂ) := by
  rw [retainedKernel, FourierTransform.fourier_smul, fourier_kernel]
  rw [entry_eq_pressure]
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

/-- A single constant controls all 27 entries, independently of the small ratio. -/
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

end Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputKernel
