import MettapediaNS.GaussianHeatCovariance
import Euler.LpParameterIntegral
import Mathlib.Analysis.Convolution

/-!
# Energy of the actual Gaussian heat stress

OpenAI's parameter-integral theorem gives the L² contraction. Mathlib's
convolution theorem gives conservation of the integral of the scalar energy
density. Their combination identifies the integrated stress trace with the
kinetic energy lost by Gaussian averaging.

This controls the undifferentiated stress, not its divergence or its work
against a differentiated receiver.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance

open MeasureTheory EulerWholeSpaceGaussian
open EulerSmoothLimit (Space)
open scoped ENNReal Convolution

/-- Direct application of the upstream parameter-integral theorem to
Gaussian-distributed translations. -/
theorem average_memLp_and_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {τ : ℝ} (hτ : 0 < τ) {f : Space → V} (hf : MemLp f 2 volume) :
    MemLp (average τ f) 2 volume ∧
      (eLpNorm (average τ f) 2 volume).toReal ≤ (eLpNorm f 2 volume).toReal := by
  let := displacementMeasure_isProbability hτ
  have hm : AEStronglyMeasurable (fun p : Space × Space => f (p.2 + p.1))
      ((displacementMeasure τ).prod volume) := by
    have hm' := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_add (displacementMeasure τ) (volume : Measure Space))
    change AEStronglyMeasurable (fun p : Space × Space => f (p.1 + p.2)) _ at hm'
    simpa only [add_comm] using hm'
  have h := EulerLpParameterIntegral.integral_memLp_and_bound
    (displacementMeasure τ) volume (fun p : Space × Space => f (p.2 + p.1)) hm
    (eLpNorm f 2 volume).toReal ENNReal.toReal_nonneg
    (Filter.Eventually.of_forall (fun y => by
      have ht := measurePreserving_add_right (volume : Measure Space) y
      refine ⟨hf.comp_measurePreserving ht, ?_⟩
      exact le_of_eq (congrArg ENNReal.toReal
        (eLpNorm_comp_measurePreserving hf.aestronglyMeasurable ht))))
  simpa only [integral_displacement_eq_average hτ, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_mul] using h

/-- The upstream plus-displacement convention equals mathlib convolution
because the literal Gaussian kernel is even. -/
theorem average_eq_convolution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (τ : ℝ) (f : Space → V) :
    average τ f = kernel τ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  funext x
  rw [convolution_lsmul, ← integral_neg_eq_self]
  simp only [kernel, norm_neg, sub_neg_eq_add, EulerWholeSpaceGaussian.average]

theorem average_integrable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {τ : ℝ} (hτ : 0 < τ) {f : Space → V} (hf : Integrable f volume) :
    Integrable (average τ f) volume := by
  rw [average_eq_convolution]
  exact (kernel_integrable hτ).integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf

theorem integral_average {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {τ : ℝ} (hτ : 0 < τ) {f : Space → V} (hf : Integrable f volume) :
    (∫ x, average τ f x) = ∫ x, f x := by
  rw [average_eq_convolution, integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
    (kernel_integrable hτ) hf, integral_kernel hτ]
  simp

theorem stress_trace {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) :
    (∑ i : Fin 3, stress τ u x i i) =
      average τ (fun y => ‖u y‖ ^ 2) x - ‖average τ u x‖ ^ 2 := by
  have hx := memLp_displacement hτ hu x
  simp only [stress, Finset.sum_sub_distrib, ← sq, EuclideanSpace.real_norm_sq_eq]
  congr 1
  simp_rw [← integral_displacement_eq_average hτ]
  simpa only [Pi.mul_apply, ← sq] using
    (integral_finsetSum Finset.univ (fun i _ => (hx.eval_piLp i).integrable_mul
      (hx.eval_piLp i))).symm

theorem stress_trace_integrable {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) : Integrable (fun x => ∑ i : Fin 3, stress τ u x i i) volume := by
  have hsq := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have ha := (average_memLp_and_bound hτ hu).1
  have hi := (average_integrable hτ hsq).sub
    ((memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).1 ha)
  change Integrable (fun x => average τ (fun y => ‖u y‖ ^ 2) x - ‖average τ u x‖ ^ 2) volume at hi
  simpa only [stress_trace hτ hu] using hi

/-- Exact integrated covariance trace: no multiplicative dimension loss. -/
theorem integral_stress_trace {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) :
    (∫ x, ∑ i : Fin 3, stress τ u x i i) =
      (∫ x, ‖u x‖ ^ 2) - ∫ x, ‖average τ u x‖ ^ 2 := by
  have hsq := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have ha := (average_memLp_and_bound hτ hu).1
  simp_rw [stress_trace hτ hu]
  rw [integral_sub (average_integrable hτ hsq)
    ((memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).1 ha), integral_average hτ hsq]

theorem integral_stress_trace_le_energy {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) :
    (∫ x, ∑ i : Fin 3, stress τ u x i i) ≤ ∫ x, ‖u x‖ ^ 2 := by
  rw [integral_stress_trace hτ hu]
  exact sub_le_self _ (integral_nonneg (fun x => sq_nonneg ‖average τ u x‖))

end Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance
