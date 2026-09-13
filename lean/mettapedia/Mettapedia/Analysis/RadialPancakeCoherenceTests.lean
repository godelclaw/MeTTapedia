import Mettapedia.Analysis.RadialPancakeCoherence

/-!
# Plane coherence and normal-defect checks

These finite-dimensional checks are not Navier–Stokes solutions. A plane
alone does not cancel coherent growth when strain tilts its normal.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialPancakeCoherenceTests

open RadialPancakeCoherence SignedRadialStretch RadialPower EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def e (i : Fin 3) : R3 := EuclideanSpace.single i 1

theorem norm_e (i : Fin 3) : ‖e i‖ = 1 := by simp [e]

theorem inner_e (i j : Fin 3) : ⟪e i, e j⟫ = if i = j then 1 else 0 := by
  simp [e, EuclideanSpace.inner_single_left, PiLp.single_apply]

def tilt : R3 →L[ℝ] R3 :=
  (innerSL ℝ (e 2)).smulRight (e 0) + (innerSL ℝ (e 0)).smulRight (e 2)

theorem tilt_normal_action (v : R3) :
    ⟪tilt (e 2), v⟫ + ⟪e 2, tilt v⟫ = 2 * ⟪e 0, v⟫ := by
  simp [tilt, ContinuousLinearMap.smulRight_apply, inner_add_right,
    real_inner_smul_right, inner_e, norm_e]
  ring

theorem zero_normalMoment (p : ℕ) : normalMoment p (e 0) (e 1) (e 2) = 0 := by
  simp [normalMoment, inner_e]

theorem nonzero_tripleProduct : tripleProduct (e 0) (e 1) (e 2) = 1 := by
  norm_num [tripleProduct, cross, cross_apply, e, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_succ, Pi.single_apply, Matrix.cons_val_two]

/-- A nonzero eigen-normal defect can produce growth despite exact coplanarity. -/
theorem tilted_normal_produces_coherent_growth (n : ℕ) : coherentRate n tilt 1 0 (e 0) (e 1) (e 2) = 2 := by
  have hc := commonAmplitudeRate_eq_normal_defects n tilt (e 0) (e 1) (e 2) (e 0) 0
    (by simpa only [zero_smul, zero_add] using tilt_normal_action)
  simp only [coherentRate, zero_mul, zero_add, one_mul, nonzero_tripleProduct, hc]
  simp [radialPower, norm_e, inner_sub_right, inner_e]

theorem zero_normal (n : ℕ) (A : R3 →L[ℝ] R3) (k dk : ℝ) (a b : R3) :
    coherentRate n A k dk a b 0 = 0 := by
  simp [coherentRate, tripleProduct]

def pancakeMatrix : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 1, -2]
def pancake : R3 →L[ℝ] R3 := pancakeMatrix.toEuclideanLin.toContinuousLinearMap
def nearPlane : R3 := WithLp.toLp 2 ![4, 0, 1]
def normal : R3 := WithLp.toLp 2 ![0, 0, 1]

theorem pancake_symmetric : pancakeMatrix.transpose = pancakeMatrix := by simp [pancakeMatrix]
theorem pancake_trace : pancakeMatrix.trace = 0 := by
  norm_num [pancakeMatrix, Matrix.trace, Fin.sum_univ_succ]

theorem pancake_normal : pancake normal = (-2 : ℝ) • normal := by
  ext i
  fin_cases i <;> norm_num [pancake, pancakeMatrix, normal, Matrix.toLpLin_apply,
    Matrix.mulVec, Matrix.diagonal, dotProduct, Fin.sum_univ_succ,
    Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk] <;> decide

theorem nearPlane_norm_sq : ‖nearPlane‖ ^ 2 = 17 := by
  norm_num [nearPlane, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]

theorem height_rate_negative :
    ⟪pancake normal, nearPlane⟫ + ⟪normal, pancake nearPlane⟫ = -4 := by
  norm_num [pancake, pancakeMatrix, normal, nearPlane, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, Matrix.mulVec, Matrix.diagonal, dotProduct, Fin.sum_univ_succ,
    Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk]
  norm_num [Matrix.cons_val_two]

theorem weightedHeightRate_positive :
    weightedHeightRate 2 nearPlane normal (pancake nearPlane) (pancake normal) = 4624 := by
  have hp (n : ℕ) : ‖nearPlane‖ ^ (2 * n) = 17 ^ n := by rw [pow_mul, nearPlane_norm_sq]
  rw [weightedHeightRate_eq, height_rate_negative]
  simp only [hp]
  norm_num [pancake, pancakeMatrix, normal, nearPlane, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, Matrix.mulVec, Matrix.diagonal, dotProduct, Fin.sum_univ_succ,
    Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk]
  norm_num [show (0 : Fin 3) ≠ 2 by decide]

theorem initial_heights : ⟪normal, nearPlane⟫ = 1 ∧ weightedHeight 2 nearPlane normal = 4913 := by
  have hp : ‖nearPlane‖ ^ (2 * (2 + 1)) = (17 : ℝ) ^ 3 := by rw [pow_mul, nearPlane_norm_sq]
  simp only [weightedHeight, radialPower, hp, real_inner_smul_right]
  norm_num [normal, nearPlane, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]

theorem not_weighted_damping_of_normal_damping :
    ¬ ∀ a : R3, ⟪pancake normal, a⟫ + ⟪normal, pancake a⟫ ≤ 0 →
      weightedHeightRate 2 a normal (pancake a) (pancake normal) ≤ 0 := by
  intro h
  have hf := h nearPlane (by rw [height_rate_negative]; norm_num)
  rw [weightedHeightRate_positive] at hf
  norm_num at hf

/-- Compression of the unweighted height does not imply weighted-height damping. -/
theorem weighted_growth_firstVariation :
    HasDerivAt (fun t : ℝ ↦ weightedHeight 2
      (nearPlane + t • pancake nearPlane) (normal + t • pancake normal)) 4624 0 := by
  have ha := ((hasDerivAt_id (0 : ℝ)).smul_const (pancake nearPlane)).const_add nearPlane
  have hh := ((hasDerivAt_id (0 : ℝ)).smul_const (pancake normal)).const_add normal
  simpa only [id_eq, zero_smul, one_smul, add_zero, weightedHeightRate_positive] using
    hasDerivAt_weightedHeight 2 ha hh

theorem unweighted_decay_firstVariation :
    HasDerivAt (fun t : ℝ ↦ ⟪normal + t • pancake normal, nearPlane + t • pancake nearPlane⟫)
      (-4) 0 := by
  have ha := ((hasDerivAt_id (0 : ℝ)).smul_const (pancake nearPlane)).const_add nearPlane
  have hh := ((hasDerivAt_id (0 : ℝ)).smul_const (pancake normal)).const_add normal
  have h := hh.inner ℝ ha
  simp only [id_eq, zero_smul, one_smul, add_zero] at h
  exact h.congr_deriv ((add_comm _ _).trans height_rate_negative)

end Mettapedia.Analysis.RadialPancakeCoherenceTests
