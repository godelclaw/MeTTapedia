import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeQuadraticProjectionLocalization

/-!
# Fourier approximation of general nonnegative weights

Unlike partition weights, the input weights need not be bounded by one.
Square-root approximation preserves positivity. The common absolute error
budget for a finite family has no factor equal to its cardinality; the
accuracy and bandwidth of the chosen polynomials may depend on that family.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.QuadraticFourierWeightApproximation

open scoped BigOperators
open PancakeAdaptiveFourierPartition PancakeQuadraticFourierSupport

theorem abs_normSq_sub_sq_le (z : ℂ) (r M epsilon : ℝ) (hr : 0 ≤ r) (hrM : r ≤ M)
    (he : 0 ≤ epsilon) (hclose : ‖z - (r : ℂ)‖ ≤ epsilon) :
    |Complex.normSq z - r ^ 2| ≤ epsilon * (epsilon + 2 * M) := by
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_nonneg hr]
  have hdiff : |‖z‖ - r| ≤ epsilon := by
    rw [← hrnorm]
    exact (abs_norm_sub_norm_le z (r : ℂ)).trans hclose
  have hz : ‖z‖ ≤ epsilon + r := by
    have h := norm_le_norm_sub_add z (r : ℂ)
    rw [hrnorm] at h
    linarith only [h, hclose]
  rw [Complex.normSq_eq_norm_sq]
  calc
    |‖z‖ ^ 2 - r ^ 2| = |‖z‖ - r| * (‖z‖ + r) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg z) hr)]
      ring
    _ ≤ epsilon * (‖z‖ + r) :=
      mul_le_mul_of_nonneg_right hdiff (add_nonneg (norm_nonneg z) hr)
    _ ≤ epsilon * (epsilon + 2 * M) :=
      mul_le_mul_of_nonneg_left (by linarith only [hz, hrM]) he

/-- A nonnegative continuous weight can be approximated by the squared
modulus of one finite Fourier polynomial at any absolute tolerance. -/
theorem exists_quadraticWeight_approximation {d : Type*} [Fintype d]
    (a : C(UnitAddTorus d, ℝ)) (ha : ∀ x, 0 ≤ a x) (delta : ℝ) (hd : 0 < delta) :
    ∃ c : FourierCoeff d, ∀ x, |Complex.normSq (fourierPolynomial c x) - a x| ≤ delta := by
  let root := sqrtContinuousMap a
  let M := ‖root‖
  let epsilon := min 1 (delta / (1 + 2 * M))
  have hM : 0 ≤ M := norm_nonneg _
  have hden : 0 < 1 + 2 * M := by positivity
  have he : 0 < epsilon := lt_min zero_lt_one (div_pos hd hden)
  have heone : epsilon ≤ 1 := min_le_left _ _
  have hepay : epsilon * (1 + 2 * M) ≤ delta :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨c, hc⟩ := exists_finsupp_mFourier_realWeight_approximation root he
  refine ⟨c, fun x ↦ ?_⟩
  have hrM : Real.sqrt (a x) ≤ M := by
    have h := root.norm_coe_le_norm x
    simpa only [root, sqrtContinuousMap_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using h
  have hclose : ‖fourierPolynomial c x - (Real.sqrt (a x) : ℂ)‖ ≤ epsilon := by
    simpa only [fourierPolynomial, root, sqrtContinuousMap_apply, norm_sub_rev] using (hc x).le
  have h := abs_normSq_sub_sq_le _ _ M epsilon (Real.sqrt_nonneg _) hrM he.le hclose
  rw [Real.sq_sqrt (ha x)] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (by linarith only [heone]) he.le).trans hepay)

/-- Total approximation error is prescribed before the finite family is
approximated. No bound on the magnitude of the original weights is assumed. -/
theorem exists_finite_quadraticWeight_approximation {d ι : Type*} [Fintype d] [Fintype ι]
    (a : ι → C(UnitAddTorus d, ℝ)) (ha : ∀ i x, 0 ≤ a i x) (delta : ℝ) (hd : 0 < delta) :
    ∃ c : ι → FourierCoeff d, ∀ x,
      (∑ i, |Complex.normSq (fourierPolynomial (c i) x) - a i x|) ≤ delta := by
  let epsilon := delta / ((Fintype.card ι : ℝ) + 1)
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have he : 0 < epsilon := div_pos hd (by positivity)
  choose c hc using fun i ↦ exists_quadraticWeight_approximation (a i) (ha i) epsilon he
  refine ⟨c, fun x ↦ ?_⟩
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hc i x)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hp : epsilon * ((Fintype.card ι : ℝ) + 1) = delta := div_mul_cancel₀ _ (by positivity)
  linarith only [h, hp, he]

end Mettapedia.FluidDynamics.NavierStokes.QuadraticFourierWeightApproximation
