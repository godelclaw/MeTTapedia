import Euler.WholeSpaceGaussianFields
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# The actual Gaussian heat stress as a covariance

The density and averaging operator are OpenAI's normalized whole-space
Gaussian. Mathlib supplies covariance, its bilinear form, and positivity.
The covariance is identified with the literal velocity-product defect for
ordinary L² velocities; no pointwise velocity bound is assumed.

The upstream Gaussian parameter has generator `Δ/4`. Thus physical heat
time `νσ` corresponds to Gaussian parameter `4νσ`.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance

open MeasureTheory ProbabilityTheory EulerWholeSpaceGaussian
open EulerSmoothLimit (Space)
open scoped ENNReal

/-- The upstream normalized Gaussian viewed as a measure on displacements. -/
def displacementMeasure (τ : ℝ) : Measure Space :=
  volume.withDensity (fun y => ENNReal.ofReal (kernel τ y))

theorem displacementMeasure_isProbability {τ : ℝ} (hτ : 0 < τ) :
    IsProbabilityMeasure (displacementMeasure τ) := by
  constructor
  rw [displacementMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (kernel_integrable hτ)
      (Filter.Eventually.of_forall (kernel_nonneg hτ)), integral_kernel hτ, ENNReal.ofReal_one]

/-- The existing Gaussian upper bound transports every ordinary L² field
into L² for the displacement probability measure. -/
theorem displacementMeasure_le {τ : ℝ} (hτ : 0 < τ) :
    displacementMeasure τ ≤ ENNReal.ofReal (normalization τ) • volume := by
  rw [← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall
    (fun y => ENNReal.ofReal_le_ofReal (kernel_le_normalization hτ y)))

theorem memLp_displacement {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {τ : ℝ} (hτ : 0 < τ) {f : Space → V} (hf : MemLp f 2 volume) (x : Space) :
    MemLp (fun y => f (x + y)) 2 (displacementMeasure τ) := by
  have ht := hf.comp_measurePreserving (measurePreserving_add_left (volume : Measure Space) x)
  exact (ht.smul_measure ENNReal.ofReal_ne_top).mono_measure (displacementMeasure_le hτ)

/-- This is the literal upstream heat average, not a new averaging operator. -/
theorem integral_displacement_eq_average {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {τ : ℝ} (hτ : 0 < τ) (f : Space → V) (x : Space) :
    (∫ y, f (x + y) ∂displacementMeasure τ) = average τ f x := by
  rw [displacementMeasure, integral_withDensity_eq_integral_toReal_smul
    (kernel_smooth τ).continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (kernel_nonneg hτ _), EulerWholeSpaceGaussian.average]

theorem average_component {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) (i : Fin 3) :
    average τ (fun y => u y i) x = (average τ u x) i := by
  let := displacementMeasure_isProbability hτ
  rw [← integral_displacement_eq_average hτ, ← integral_displacement_eq_average hτ]
  exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm
    ((memLp_displacement hτ hu x).integrable (by norm_num))

/-- The Reynolds stress is defined by the actual averaged product defect. -/
def stress (τ : ℝ) (u : Space → Space) (x : Space) (i j : Fin 3) : ℝ :=
  average τ (fun y => u y i * u y j) x - (average τ u x) i * (average τ u x) j

theorem stress_eq_covariance {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) (i j : Fin 3) :
    stress τ u x i j = covariance (fun y => u (x + y) i) (fun y => u (x + y) j)
      (displacementMeasure τ) := by
  let := displacementMeasure_isProbability hτ
  have hx := memLp_displacement hτ hu x
  rw [covariance_eq_sub (hx.eval_piLp i) (hx.eval_piLp j)]
  change stress τ u x i j = (∫ y, u (x+y) i * u (x+y) j ∂displacementMeasure τ) - _
  rw [integral_displacement_eq_average hτ (fun y => u y i * u y j),
    integral_displacement_eq_average hτ (fun y => u y i),
    integral_displacement_eq_average hτ (fun y => u y j),
    average_component hτ hu, average_component hτ hu]
  rfl

/-- Mathlib's actual covariance bilinear form of the velocity-value law. -/
def stressBilin (τ : ℝ) (u : Space → Space) (x : Space) : Space →L[ℝ] Space →L[ℝ] ℝ :=
  covarianceBilin ((displacementMeasure τ).map (fun y => u (x + y)))

theorem stressBilin_apply {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x v w : Space) :
    stressBilin τ u x v w = ∑ i : Fin 3, ∑ j : Fin 3, v i * w j * stress τ u x i j := by
  let := displacementMeasure_isProbability hτ
  have hx := memLp_displacement hτ hu x
  have he : (fun y => WithLp.toLp 2 (fun i : Fin 3 => u (x+y) i)) = (fun y => u (x+y)) := rfl
  have h := covarianceBilin_apply_pi (fun i => hx.eval_piLp i) v w
  rw [he] at h
  simpa only [stressBilin, stress_eq_covariance hτ hu x] using h

/-- Positivity is inherited from mathlib's covariance theorem, after the
actual velocity-product identification has been proved. -/
theorem stress_quadratic_nonneg {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x v : Space) :
    0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, v i * v j * stress τ u x i j := by
  rw [← stressBilin_apply hτ hu]
  exact covarianceBilin_self_nonneg v

theorem stress_symmetric {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) (i j : Fin 3) :
    stress τ u x i j = stress τ u x j i := by
  rw [stress_eq_covariance hτ hu, stress_eq_covariance hτ hu, covariance_comm]

theorem stress_diagonal_nonneg {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) (i : Fin 3) : 0 ≤ stress τ u x i i := by
  rw [stress_eq_covariance hτ hu,
    covariance_self ((memLp_displacement hτ hu x).eval_piLp i).aemeasurable]
  exact variance_nonneg _ _

end Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance
