import MettapediaNS.GaussianHeatIncrement

/-!
# Signed tensor pairing of the actual Gaussian heat stress

The full tensor contraction is the Gaussian expectation of a quadratic
form on centered velocity. Mathlib's inner-product and operator-norm
inequalities then bound this contraction without a dimension factor.
The one-sided version retains the sign of the receiver's quadratic form.

This is a spatial weak-stress estimate. Identification with the existing
Fourier stretching adjoint and payment of its evolving derivative remain
separate obligations; those existing adjoint/heat identities are not
reimplemented here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance

open MeasureTheory ProbabilityTheory EulerWholeSpaceGaussian EulerLpTranslation
open EulerSmoothLimit (Space)
open scoped ENNReal InnerProductSpace

/-- Centered velocity under the literal Gaussian displacement law. -/
def fluctuation (τ : ℝ) (u : Space → Space) (x y : Space) : Space :=
  u (x + y) - average τ u x

theorem fluctuation_memLp {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) :
    MemLp (fluctuation τ u x) 2 (displacementMeasure τ) := by
  let := displacementMeasure_isProbability hτ
  exact (memLp_displacement hτ hu x).sub (memLp_const _)

theorem stress_eq_integral_fluctuation {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) (i j : Fin 3) :
    stress τ u x i j = ∫ y, fluctuation τ u x y i * fluctuation τ u x y j
      ∂displacementMeasure τ := by
  rw [stress_eq_covariance hτ hu, covariance]
  change (∫ y, (u (x + y) i - ∫ z, u (x + z) i ∂displacementMeasure τ) *
    (u (x + y) j - ∫ z, u (x + z) j ∂displacementMeasure τ) ∂displacementMeasure τ) = _
  rw [integral_displacement_eq_average hτ (fun z => u z i),
    integral_displacement_eq_average hτ (fun z => u z j),
    average_component hτ hu, average_component hτ hu]
  rfl

theorem stress_trace_eq_integral_fluctuation {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) :
    (∑ i : Fin 3, stress τ u x i i) =
      ∫ y, ‖fluctuation τ u x y‖ ^ 2 ∂displacementMeasure τ := by
  have hz := fluctuation_memLp hτ hu x
  simp_rw [stress_eq_integral_fluctuation hτ hu, ← sq]
  have hi (i : Fin 3) := (memLp_two_iff_integrable_sq (hz.eval_piLp i).aestronglyMeasurable).1
    (hz.eval_piLp i)
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun y =>
    (EuclideanSpace.real_norm_sq_eq (fluctuation τ u x y)).symm))

/-- All entries are paired before taking an absolute value. -/
def contraction (τ : ℝ) (u : Space → Space) (x : Space) (M : Space →L[ℝ] Space) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, stress τ u x i j * (M (EuclideanSpace.single j 1)) i

private theorem quadratic_eq_sum (M : Space →L[ℝ] Space) (z : Space) :
    ⟪z, M z⟫_ℝ = ∑ i : Fin 3, ∑ j : Fin 3,
      z i * z j * (M (EuclideanSpace.single j 1)) i := by
  have hz : z = ∑ j : Fin 3, z j • EuclideanSpace.single j 1 := by
    ext i
    simp [Pi.single_apply]
  have hMz := congrArg M hz
  rw [map_sum] at hMz
  rw [hMz]
  simp only [inner_sum, map_smul, inner_smul_right, PiLp.inner_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change z i * ((M (EuclideanSpace.single i 1)) j * z j) = _
  ring

/-- Exact quadratic expectation, retaining the receiver's directional sign. -/
theorem contraction_eq_integral_quadratic {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) (M : Space →L[ℝ] Space) :
    contraction τ u x M = ∫ y, ⟪fluctuation τ u x y, M (fluctuation τ u x y)⟫_ℝ
      ∂displacementMeasure τ := by
  have hz := fluctuation_memLp hτ hu x
  have hi (i j : Fin 3) : Integrable (fun y =>
      fluctuation τ u x y i * fluctuation τ u x y j * (M (EuclideanSpace.single j 1)) i)
      (displacementMeasure τ) :=
    ((hz.eval_piLp i).integrable_mul (hz.eval_piLp j)).mul_const _
  simp only [contraction, stress_eq_integral_fluctuation hτ hu, ← integral_mul_const]
  simp_rw [← integral_finsetSum Finset.univ (fun j _ => hi _ j)]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun y => (quadratic_eq_sum M _).symm))

theorem norm_contraction_le_trace {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) (M : Space →L[ℝ] Space) :
    ‖contraction τ u x M‖ ≤ ‖M‖ * ∑ i : Fin 3, stress τ u x i i := by
  have hz := fluctuation_memLp hτ hu x
  have hi := (memLp_two_iff_integrable_sq_norm hz.aestronglyMeasurable).1 hz
  rw [contraction_eq_integral_quadratic hτ hu, stress_trace_eq_integral_fluctuation hτ hu,
    ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hi.const_mul _)
  exact Filter.Eventually.of_forall (fun y => by
    calc
      _ ≤ ‖fluctuation τ u x y‖ * ‖M (fluctuation τ u x y)‖ := norm_inner_le_norm _ _
      _ ≤ ‖fluctuation τ u x y‖ * (‖M‖ * ‖fluctuation τ u x y‖) :=
        mul_le_mul_of_nonneg_left (M.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring)

/-- A signed quadratic upper bound is preserved under the actual covariance.
The scalar `K` is not required to be nonnegative in this pointwise theorem. -/
theorem contraction_le_trace_of_quadratic_le {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) (M : Space →L[ℝ] Space) (K : ℝ)
    (hM : ∀ z : Space, ⟪z, M z⟫_ℝ ≤ K * ‖z‖ ^ 2) :
    contraction τ u x M ≤ K * ∑ i : Fin 3, stress τ u x i i := by
  have hz := fluctuation_memLp hτ hu x
  have hi := (memLp_two_iff_integrable_sq_norm hz.aestronglyMeasurable).1 hz
  have hq : Integrable (fun y => ⟪fluctuation τ u x y, M (fluctuation τ u x y)⟫_ℝ)
      (displacementMeasure τ) := by
    exact memLp_one_iff_integrable.1 ((innerSL ℝ).memLp_of_bilin 1 hz (M.comp_memLp' hz))
  rw [contraction_eq_integral_quadratic hτ hu, stress_trace_eq_integral_fluctuation hτ hu,
    ← integral_const_mul]
  exact integral_mono hq (hi.const_mul _) (fun y => hM _)

/-- The antisymmetric part of the receiving operator makes no contribution.
This is an exact identity before any norm bound. -/
theorem contraction_selfAdjointPart {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) (M : Space →L[ℝ] Space) :
    contraction τ u x (selfAdjointPart ℝ M : Space →L[ℝ] Space) = contraction τ u x M := by
  rw [contraction_eq_integral_quadratic hτ hu, contraction_eq_integral_quadratic hτ hu]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    simp only [selfAdjointPart_apply_coe, ContinuousLinearMap.star_eq_adjoint,
      smul_apply, add_apply, inner_smul_right, inner_add_right,
      ContinuousLinearMap.adjoint_inner_right, real_inner_comm (M _)]
    norm_num
    ring)

theorem norm_contraction_le_selfAdjointPart_trace {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (x : Space) (M : Space →L[ℝ] Space) :
    ‖contraction τ u x M‖ ≤ ‖(selfAdjointPart ℝ M : Space →L[ℝ] Space)‖ *
      ∑ i : Fin 3, stress τ u x i i := by
  rw [← contraction_selfAdjointPart hτ hu x M]
  exact norm_contraction_le_trace hτ hu x _

theorem stress_integrable {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) (i j : Fin 3) : Integrable (fun x => stress τ u x i j) volume := by
  have ha := (average_memLp_and_bound hτ hu).1
  exact (average_integrable hτ ((hu.eval_piLp i).integrable_mul (hu.eval_piLp j))).sub
    ((ha.eval_piLp i).integrable_mul (ha.eval_piLp j))

theorem contraction_aestronglyMeasurable {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) {M : Space → Space →L[ℝ] Space} (hM : Continuous M) :
    AEStronglyMeasurable (fun x => contraction τ u x (M x)) volume := by
  simp only [contraction]
  apply Finset.aestronglyMeasurable_fun_sum
  intro i _
  apply Finset.aestronglyMeasurable_fun_sum
  intro j _
  exact (stress_integrable hτ hu i j).aestronglyMeasurable.mul
    ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp
      (hM.clm_apply continuous_const)).aestronglyMeasurable

theorem contraction_integrable {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) {M : Space → Space →L[ℝ] Space} (hM : Continuous M)
    (K : ℝ) (hK : ∀ x, ‖M x‖ ≤ K) :
    Integrable (fun x => contraction τ u x (M x)) volume := by
  apply ((stress_trace_integrable hτ hu).const_mul K).mono'
    (contraction_aestronglyMeasurable hτ hu hM)
  exact Filter.Eventually.of_forall (fun x => (norm_contraction_le_trace hτ hu x (M x)).trans
    (mul_le_mul_of_nonneg_right (hK x)
      (Finset.sum_nonneg (fun i _ => stress_diagonal_nonneg hτ hu x i))))

/-- A bound for the complete integrated tensor pairing, not a componentwise
absolute sum. The receiver norm is explicit and still has to be paid. -/
theorem norm_integral_contraction_le {τ : ℝ} (hτ : 0 < τ) {u : Space → Space}
    (hu : MemLp u 2 volume) {M : Space → Space →L[ℝ] Space}
    (K : ℝ) (hK : ∀ x, ‖M x‖ ≤ K) :
    ‖∫ x, contraction τ u x (M x)‖ ≤ K * (∫ x, ∑ i : Fin 3, stress τ u x i i) := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le ((stress_trace_integrable hτ hu).const_mul K)
  exact Filter.Eventually.of_forall (fun x => (norm_contraction_le_trace hτ hu x (M x)).trans
    (mul_le_mul_of_nonneg_right (hK x)
      (Finset.sum_nonneg (fun i _ => stress_diagonal_nonneg hτ hu x i))))

end Mettapedia.FluidDynamics.NavierStokes.GaussianHeatCovariance
