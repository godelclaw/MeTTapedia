import MettapediaNS.GaussianHeatEnergy
import MettapediaNS.WholeSpaceUnforcedEnergy
import Euler.OrdinaryMollifier

/-!
# A derivative-energy bound for the actual Gaussian stress

The translation-increment estimate and Gaussian quadratic majorant are
imported from OpenAI. Mathlib supplies the variance bound after subtraction
of a constant. These give a small-heat-scale gain for the integrated stress
trace without a supremum norm of the velocity gradient.

The translation theorem is independent of the compact mollifier elsewhere
in its upstream module: the averaging here remains the literal Gaussian.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance

open MeasureTheory ProbabilityTheory EulerWholeSpaceGaussian EulerLpTranslation
open EulerSmoothLimit (Space)
open scoped ENNReal

theorem stress_trace_le_increment {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) :
    (∑ i : Fin 3, stress τ u x i i) ≤
      ∫ y, ‖u (x + y) - u x‖ ^ 2 ∂displacementMeasure τ := by
  let := displacementMeasure_isProbability hτ
  have hx := memLp_displacement hτ hu x
  have hi (i : Fin 3) : stress τ u x i i ≤
      ∫ y, (u (x + y) i - u x i) ^ 2 ∂displacementMeasure τ := by
    rw [stress_eq_covariance hτ hu, covariance_self (hx.eval_piLp i).aemeasurable,
      ← variance_sub_const (hx.eval_piLp i).aestronglyMeasurable (u x i)]
    exact variance_le_expectation_sq
      ((hx.eval_piLp i).aestronglyMeasurable.sub aestronglyMeasurable_const)
  calc
    _ ≤ ∑ i : Fin 3, ∫ y, (u (x + y) i - u x i) ^ 2 ∂displacementMeasure τ :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by
      have hiInt (i : Fin 3) : Integrable (fun y => (u (x + y) i - u x i) ^ 2)
          (displacementMeasure τ) := by
        have hs : MemLp (fun y => u (x + y) i - u x i) 2 (displacementMeasure τ) :=
          (hx.eval_piLp i).sub (memLp_const (u x i))
        exact (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).1 hs
      rw [← integral_finsetSum Finset.univ (fun i _ => hiInt i)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        simpa only [PiLp.sub_apply] using
          (EuclideanSpace.real_norm_sq_eq (u (x + y) - u x)).symm)

/-- The imported widened-Gaussian bound supplies both integrability and
the second-moment estimate; no Gaussian moment is recomputed. -/
theorem displacement_secondMoment {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun y : Space => ‖y‖ ^ 2) (displacementMeasure τ) ∧
      (∫ y : Space, ‖y‖ ^ 2 ∂displacementMeasure τ) ≤
        (2 * τ) * (2 : ℝ) ^ (3 / 2 : ℝ) := by
  have hw := (wideKernel_integrable hτ).const_mul (2 * τ)
  have hk : Integrable (fun y : Space => kernel τ y * ‖y‖ ^ 2) volume := by
    apply hw.mono' ((kernel_smooth τ).continuous.mul (continuous_norm.pow 2)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => by
      change ‖kernel τ y * ‖y‖ ^ 2‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (kernel_nonneg hτ y) (sq_nonneg _)), mul_comm]
      exact norm_sq_kernel_le hτ y)
  have hμ : Integrable (fun y : Space => ‖y‖ ^ 2) (displacementMeasure τ) := by
    rw [displacementMeasure, integrable_withDensity_iff_integrable_smul'
      (kernel_smooth τ).continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (kernel_nonneg hτ _), smul_eq_mul] using hk
  refine ⟨hμ, ?_⟩
  rw [displacementMeasure, integral_withDensity_eq_integral_toReal_smul
    (kernel_smooth τ).continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (kernel_nonneg hτ _), smul_eq_mul]
  calc
    _ ≤ ∫ y : Space, (2 * τ) * wideKernel τ y := integral_mono hk hw
      (fun y => by simpa only [mul_comm] using norm_sq_kernel_le hτ y)
    _ = _ := by rw [integral_const_mul, integral_wideKernel hτ]

/-- Convert the actual upstream translation in L² to its spatial representative. -/
theorem translation_increment_ae (A : SmoothL2Field Space) (y : Space) :
    (translation y A.toLp - A.toLp : L2Space Space) =ᵐ[volume]
      fun x => A.field (x + y) - A.field x := by
  filter_upwards [Lp.coeFn_sub (translation y A.toLp) A.toLp, translation_ae y A.toLp,
    A.toLp_ae, (measurePreserving_add_right (volume : Measure Space) y).quasiMeasurePreserving.ae
      A.toLp_ae] with x hs ht hx hxy
  simpa only [Pi.sub_apply, ht, hx, hxy] using hs

theorem integral_translation_increment_sq_le (A : SmoothL2Field Space) (y : Space) :
    (∫ x, ‖A.field (x + y) - A.field x‖ ^ 2) ≤ ‖A.derivative.toLp‖ ^ 2 * ‖y‖ ^ 2 := by
  have he : (∫ x, ‖A.field (x + y) - A.field x‖ ^ 2) =
      ‖translation y A.toLp - A.toLp‖ ^ 2 := by
    rw [EulerLpBochnerRealization.norm_sq_eq_integral]
    exact integral_congr_ae ((translation_increment_ae A y).fun_comp (fun v => ‖v‖ ^ 2)).symm
  rw [he, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (EulerOrdinaryMollifier.translation_increment A y) 2

/-- Joint integrability is obtained from the upstream Bochner realization
theorem, not from a pointwise bound on the spatial gradient. -/
theorem gaussian_increment_integrable {τ : ℝ} (hτ : 0 < τ) (A : SmoothL2Field Space) :
    Integrable (fun p : Space × Space => ‖A.field (p.2 + p.1) - A.field p.2‖ ^ 2)
      ((displacementMeasure τ).prod volume) := by
  let := displacementMeasure_isProbability hτ
  let w : Space → L2Space Space := fun y => translation y A.toLp - A.toLp
  have hw : MemLp w 2 (displacementMeasure τ) := by
    apply MemLp.of_bound ((translation_continuous A.toLp).sub continuous_const).aestronglyMeasurable
      (2 * ‖A.toLp‖)
    exact Filter.Eventually.of_forall (fun y => by
      dsimp [w]
      calc
        _ ≤ ‖translation y A.toLp‖ + ‖A.toLp‖ := norm_sub_le _ _
        _ = _ := by rw [(translation y).norm_map]; ring)
  have hm : AEStronglyMeasurable (fun p : Space × Space => A.field (p.2 + p.1) - A.field p.2)
      ((displacementMeasure τ).prod volume) :=
    ((A.smooth.continuous.comp (continuous_snd.add continuous_fst)).sub
      (A.smooth.continuous.comp continuous_snd)).aestronglyMeasurable
  have hp := EulerLpBochnerRealization.field_memLp (hw.toLp w)
    (fun p : Space × Space => A.field (p.2 + p.1) - A.field p.2) hm (by
      filter_upwards [hw.coeFn_toLp] with y hy
      rw [hy]
      exact translation_increment_ae A y)
  exact (memLp_two_iff_integrable_sq_norm hm).1 hp

/-- A small-heat-scale stress bound, paid by the ordinary L² spatial derivative.
The constant is the imported Gaussian majorant, not an optimized second moment. -/
theorem integral_stress_trace_le_derivative_energy {τ : ℝ} (hτ : 0 < τ)
    (A : SmoothL2Field Space) :
    (∫ x, ∑ i : Fin 3, stress τ A.field x i i) ≤
      ((2 * τ) * (2 : ℝ) ^ (3 / 2 : ℝ)) * ‖A.derivative.toLp‖ ^ 2 := by
  let := displacementMeasure_isProbability hτ
  have hp := gaussian_increment_integrable hτ A
  have hm := displacement_secondMoment hτ
  calc
    _ ≤ ∫ x, ∫ y, ‖A.field (x + y) - A.field x‖ ^ 2 ∂displacementMeasure τ :=
      integral_mono (stress_trace_integrable hτ A.memLp) hp.integral_prod_right
        (stress_trace_le_increment hτ A.memLp)
    _ = ∫ y, (∫ x, ‖A.field (x + y) - A.field x‖ ^ 2) ∂displacementMeasure τ :=
      (integral_integral_swap hp).symm
    _ ≤ ∫ y, ‖A.derivative.toLp‖ ^ 2 * ‖y‖ ^ 2 ∂displacementMeasure τ :=
      integral_mono hp.integral_prod_left (hm.1.const_mul _) (integral_translation_increment_sq_le A)
    _ = ‖A.derivative.toLp‖ ^ 2 * (∫ y : Space, ‖y‖ ^ 2 ∂displacementMeasure τ) := integral_const_mul _ _
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hm.2 (sq_nonneg _)

/-- The independent energy bound applies to actual unforced H³ solutions
on their given lifespan; it is uniform in the auxiliary heat parameter. -/
theorem integral_stress_trace_le_initial
    {ν T : ℝ} {u : NavierStokesR3.ProblemStatement.VelocityField}
    {p : NavierStokesR3.ProblemStatement.PressureField} {u₀ : Space → Space}
    (s : NavierStokesR3.H3Comparison.ClassicalH3Solution ν (fun _ => 0) u₀ T u p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) {τ : ℝ} (hτ : 0 < τ) :
    (∫ x, ∑ i : Fin 3, stress τ (fun y => u (t, y)) x i i) ≤
      NavierStokesR3.Comparison.l2Sq u₀ := by
  obtain ⟨hu, he⟩ := WholeSpaceUnforcedEnergy.classical_memLp_and_l2Sq_le_initial s hν ht
  exact (integral_stress_trace_le_energy hτ hu).trans he

end Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance
