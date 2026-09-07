import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeTwoShearFiniteTime
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicMean

/-!
# Exact spatial averaging of the two-shear spectral defect

Half-period translation performs the sign pairing inside the actual
Lebesgue integral. Full-period frequency repetition removes the integer
frequency from the spatial average, but not from the heat decay rate.
The finite-time comparison is then integrated using exact cosine moments.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeTwoShearSpatialMean

open Real PancakeTwoShearDiffusion PancakeTwoShearFiniteTime PancakePeriodicMean

def pairedField (p q x y : ℝ) : ℝ := pairedDefect (p * |cos y|) (q * |cos x|)

def pairedMean (p q : ℝ) : ℝ := spatialMean (pairedField p q)

theorem continuous_pairedField (p q : ℝ) : Continuous (pairedField p q).uncurry := by
  unfold pairedField pairedDefect shearDefect Function.uncurry
  fun_prop

theorem circleMean_shear_pair (p g : ℝ) (hp : 0 ≤ p) :
    circleMean (fun y ↦ shearDefect (p * cos y) g) =
      circleMean (fun y ↦ pairedDefect (p * |cos y|) |g|) := by
  have hper : Function.Periodic (fun y ↦ shearDefect (p * cos y) g) (2 * π) := by
    intro y
    simp only [cos_add_two_pi]
  have hs := circleMean_shift (fun y ↦ shearDefect (p * cos y) g) hper π
  have hn : circleMean (fun y ↦ shearDefect (-(p * cos y)) g) =
      circleMean (fun y ↦ shearDefect (p * cos y) g) := by
    simpa only [cos_add_pi, mul_neg] using hs
  calc
    _ = circleMean (fun y ↦ pairedDefect (p * cos y) g) := by
      unfold pairedDefect
      rw [circleMean_div, circleMean_add _ _ (by unfold shearDefect; fun_prop)
        (by unfold shearDefect; fun_prop), hn]
      ring
    _ = _ := by
      apply circleMean_congr
      intro y
      have h := pairedDefect_abs (p * cos y) g
      simpa only [abs_mul, abs_of_nonneg hp] using h.symm

def rawMean (N : ℕ) (p q : ℝ) : ℝ :=
  spatialMean (fun x y ↦ shearDefect (p * cos ((N : ℝ) * y)) (q * cos x))

theorem rawMean_eq_pairedMean (N : ℕ) (p q : ℝ) (hN : N ≠ 0)
    (hp : 0 ≤ p) (hq : 0 ≤ q) : rawMean N p q = pairedMean p q := by
  unfold rawMean pairedMean spatialMean
  apply circleMean_congr
  intro x
  have hc : Continuous (fun y ↦ shearDefect (p * cos y) (q * cos x)) := by
    unfold shearDefect
    fun_prop
  have hper : Function.Periodic (fun y ↦ shearDefect (p * cos y) (q * cos x)) (2 * π) := by
    intro y
    simp only [cos_add_two_pi]
  rw [circleMean_nat_frequency _ hc hper N hN, circleMean_shear_pair p (q * cos x) hp]
  apply circleMean_congr
  intro y
  simp only [pairedField, abs_mul, abs_of_nonneg hq]

theorem pairedMean_scale (c p q : ℝ) (hc : 0 ≤ c) :
    pairedMean (c * p) (c * q) = c ^ 3 * pairedMean p q := by
  unfold pairedMean
  rw [← spatialMean_const_mul]
  apply spatialMean_congr
  intro x y
  simp only [pairedField, mul_assoc]
  exact pairedDefect_scale c _ _ hc

theorem pairedMean_nonneg (p q : ℝ) : 0 ≤ pairedMean p q := by
  rw [← spatialMean_const (0 : ℝ)]
  exact spatialMean_mono _ _ (by fun_prop) (continuous_pairedField p q)
    (fun x y ↦ pairedDefect_nonneg _ _)

theorem pairedMean_le_four (eps : ℝ) (he : 0 ≤ eps) (he1 : eps ≤ 1) :
    pairedMean eps 1 ≤ 4 := by
  rw [← spatialMean_const (4 : ℝ)]
  apply spatialMean_mono _ _ (continuous_pairedField eps 1) (by fun_prop)
  intro x y
  apply pairedDefect_le_four _ _ (by positivity) (by positivity)
  · exact (mul_le_mul_of_nonneg_left (abs_cos_le_one y) he).trans (by simpa using he1)
  · simpa only [one_mul] using abs_cos_le_one x

/-- An actual spatial finite-time comparison, including all crossings. -/
theorem pairedMean_damping_lower (alpha eps : ℝ)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (he : 0 ≤ eps) :
    (1 - alpha ^ 2) * (2 - 8 * eps) * eps ^ 2 / 2 ≤
      pairedMean (alpha * eps) 1 - pairedMean eps 1 := by
  let L : ℝ → ℝ → ℝ := fun x y ↦
    (1 - alpha ^ 2) * (4 * |cos x| - 8 * eps) * (eps * |cos y|) ^ 2
  have h := spatialMean_mono L
    (fun x y ↦ pairedField (alpha * eps) 1 x y - pairedField eps 1 x y)
    (by dsimp [L]; fun_prop)
    ((continuous_pairedField (alpha * eps) 1).sub (continuous_pairedField eps 1)) (by
      intro x y
      dsimp only [L, pairedField]
      simp only [one_mul, mul_assoc]
      simpa only [mul_assoc] using pairedDefect_damping_lower_bounded alpha (eps * |cos y|) |cos x| eps
        ha ha1 (mul_nonneg he (abs_nonneg _)) (abs_nonneg _)
        (by nlinarith [abs_cos_le_one y]))
  rw [spatialMean_sub _ _ (continuous_pairedField (alpha * eps) 1)
    (continuous_pairedField eps 1)] at h
  have hL : spatialMean L =
      (1 - alpha ^ 2) * (4 * circleMean (fun x ↦ |cos x|) - 8 * eps) * eps ^ 2 / 2 := by
    dsimp only [L]
    rw [spatialMean_product, circleMean_const_mul,
      circleMean_sub _ _ (by fun_prop) (by fun_prop), circleMean_const_mul,
      circleMean_const, circleMean_scaled_abs_cos_sq]
    ring
  rw [hL] at h
  apply le_trans ?_ h
  have ha2 : 0 ≤ 1 - alpha ^ 2 := by nlinarith
  have hm := circleMean_abs_cos_lower
  nlinarith [mul_nonneg (mul_nonneg ha2 (sq_nonneg eps)) (sub_nonneg.mpr hm)]

/-- A concrete positive margin using coarse exact bounds. No numerical
quadrature, derivative under the integral, or null crossing-set premise. -/
theorem pairedMean_concrete_growth (alpha beta : ℝ)
    (ha : 0 ≤ alpha) (ha2 : alpha ^ 2 ≤ 1 / 2)
    (hb : 0 ≤ beta) (hb3 : (16381 : ℝ) / 16384 ≤ beta ^ 3) :
    pairedMean ((beta * alpha) * (1 / 16)) beta - pairedMean (1 / 16) 1 ≥
      (24567 : ℝ) / 33554432 := by
  have ha1 : alpha ≤ 1 := by nlinarith
  have h := pairedMean_damping_lower alpha (1 / 16) ha ha1 (by norm_num)
  have h0 := pairedMean_nonneg (1 / 16) 1
  have h4 := pairedMean_le_four (1 / 16) (by norm_num) (by norm_num)
  have hgain : (3 : ℝ) / 2048 ≤ pairedMean (alpha * (1 / 16)) 1 - pairedMean (1 / 16) 1 := by
    nlinarith
  have heq : pairedMean ((beta * alpha) * (1 / 16)) beta =
      beta ^ 3 * pairedMean (alpha * (1 / 16)) 1 := by
    simpa only [mul_one, mul_assoc] using pairedMean_scale beta (alpha * (1 / 16)) 1 hb
  rw [heq]
  have hc1 := mul_nonneg (pow_nonneg hb 3) (sub_nonneg.mpr hgain)
  have hc2 := mul_nonneg (sub_nonneg.mpr hb3)
    (show 0 ≤ pairedMean (1 / 16) 1 + 3 / 2048 by linarith)
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeTwoShearSpatialMean
