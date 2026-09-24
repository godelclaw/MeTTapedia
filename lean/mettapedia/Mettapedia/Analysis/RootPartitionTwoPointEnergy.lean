import Mettapedia.Analysis.RootPartitionEnergy
import Mettapedia.Analysis.GaussianAmplitudeOverlap

/-!
# Two-point derivative energy for Gaussian root partitions

The root weight is evaluated at a different point from the derivative.
Gaussian overlap controls the sum, while the common scalar derivative,
temperature, and two-point distance moment remain explicit. No inverse
power of the vorticity norm is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RootPartitionEnergy

open scoped BigOperators
open GaussianPartitionEnergy FiniteExponentialWeights RadialSquareRoot

variable {ι E F : Type*} [Fintype ι] [Nonempty ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem deriv_rootAmplitude_eq (center : ι → F) (tau : ℝ)
    {b : ℝ → ℝ} {bd : ℝ} {x : ℝ → F} {v : F} {t : ℝ}
    (hb : HasDerivAt b bd t) (hx : HasDerivAt x v t) (i : ι) :
    deriv (fun s ↦ rootAmplitude center tau (b s) (x s) i) t =
      Real.sqrt (gaussianAmplitude center tau (x t) i) *
        (bd + b t / 4 * (scoreRate center tau (x t) v i -
          mean (score center tau (x t)) (scoreRate center tau (x t) v))) := by
  have hA := hasDerivAt_gaussianAmplitude center tau hx i
  have hpos : 0 < gaussianAmplitude center tau (x t) i := amplitude_pos _ _
  have hroot := Real.sq_sqrt hpos.le
  have hn := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hd : deriv (fun s ↦ rootAmplitude center tau (b s) (x s) i) t =
      bd * Real.sqrt (gaussianAmplitude center tau (x t) i) + b t *
        (amplitudeRate (score center tau (x t)) (scoreRate center tau (x t) v) i /
          (2 * Real.sqrt (gaussianAmplitude center tau (x t) i))) :=
    (hb.mul (hA.sqrt (ne_of_gt hpos))).deriv
  have hdiv : gaussianAmplitude center tau (x t) i /
      (4 * Real.sqrt (gaussianAmplitude center tau (x t) i)) =
      Real.sqrt (gaussianAmplitude center tau (x t) i) / 4 := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hn)).mpr
    nlinarith only [hroot]
  rw [hd]
  calc
    _ = bd * Real.sqrt (gaussianAmplitude center tau (x t) i) +
        b t * (scoreRate center tau (x t) v i -
          mean (score center tau (x t)) (scoreRate center tau (x t) v)) *
        (gaussianAmplitude center tau (x t) i / (4 * Real.sqrt (gaussianAmplitude center tau (x t) i))) := by
      unfold amplitudeRate gaussianAmplitude
      ring
    _ = _ := by rw [hdiv]; ring

omit [InnerProductSpace ℝ F] in
theorem sum_rootAmplitude_sq_mul_sq_le (center : ι → F) (tau bx bz : ℝ) (x z : F) :
    (∑ i, rootAmplitude center tau bz z i ^ 2 * rootAmplitude center tau bx x i ^ 2) ≤
      bz ^ 2 * bx ^ 2 := by
  simp only [rootAmplitude_sq]
  have h := mul_le_mul_of_nonneg_left (sum_gaussianAmplitude_mul_le_one center tau z x)
    (show 0 ≤ bz ^ 2 * bx ^ 2 by positivity)
  rw [mul_one, Finset.mul_sum] at h
  calc
    _ = ∑ i, bz ^ 2 * bx ^ 2 * (gaussianAmplitude center tau z i * gaussianAmplitude center tau x i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := h

theorem sum_rootAmplitude_sq_mul_deriv_sq_le (center : ι → F) (tau : ℝ)
    {b : ℝ → ℝ} {bd : ℝ} {x : ℝ → F} {v : F} {t : ℝ}
    (hb : HasDerivAt b bd t) (hx : HasDerivAt x v t) (bz : ℝ) (z : F) :
    (∑ i, rootAmplitude center tau bz z i ^ 2 *
      deriv (fun s ↦ rootAmplitude center tau (b s) (x s) i) t ^ 2) ≤
      bz ^ 2 * (2 * bd ^ 2 + b t ^ 2 / tau ^ 2 * ‖v‖ ^ 2 * twoPointDistanceMoment center tau (x t) z) := by
  have he : (∑ i, rootAmplitude center tau bz z i ^ 2 *
      deriv (fun s ↦ rootAmplitude center tau (b s) (x s) i) t ^ 2) =
      bz ^ 2 * ∑ i, amplitude (score center tau (x t)) i * amplitude (score center tau z) i *
        (bd + b t / 4 * (scoreRate center tau (x t) v i -
          mean (score center tau (x t)) (scoreRate center tau (x t) v))) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [rootAmplitude_sq, deriv_rootAmplitude_eq center tau hb hx i, mul_pow,
      Real.sq_sqrt (show 0 ≤ gaussianAmplitude center tau (x t) i from (amplitude_pos _ _).le)]
    unfold gaussianAmplitude
    ring
  rw [he]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg bz)
  have h0 := sum_amplitude_mul_affine_centered_sq_le
    (score center tau (x t)) (score center tau z) (scoreRate center tau (x t) v) bd (b t / 4)
  have h1 := mul_le_mul_of_nonneg_left (mean_scoreRate_sq_average_add_le center tau (x t) z v)
    (show 0 ≤ 4 * (b t / 4) ^ 2 by positivity)
  calc
    _ ≤ 2 * bd ^ 2 + 4 * (b t / 4) ^ 2 *
        (mean (fun j ↦ (score center tau (x t) j + score center tau z j) / 2)
          (fun i ↦ scoreRate center tau (x t) v i ^ 2) +
          mean (score center tau (x t)) (fun i ↦ scoreRate center tau (x t) v i ^ 2)) := h0
    _ ≤ 2 * bd ^ 2 + 4 * (b t / 4) ^ 2 *
        (4 / tau ^ 2 * ‖v‖ ^ 2 * twoPointDistanceMoment center tau (x t) z) :=
      add_le_add le_rfl h1
    _ = 2 * bd ^ 2 + b t ^ 2 / tau ^ 2 * ‖v‖ ^ 2 * twoPointDistanceMoment center tau (x t) z := by ring

/-- The partner root is evaluated at `z`; the derivative is evaluated at `x t`.
Both vorticity norms may vanish. -/
theorem sum_twoPoint_rootVorticity_deriv_sq_le (center : ι → F) (tau : ℝ)
    {b : ℝ → ℝ} {bd : ℝ} {x : ℝ → F} {v : F} {w : ℝ → E} {wd : E} {t : ℝ}
    (hb : HasDerivAt b bd t) (hx : HasDerivAt x v t) (hw : HasDerivAt w wd t)
    (bz : ℝ) (z : F) (wz : E) :
    ‖wz‖ ^ 2 * (∑ i, (rootAmplitude center tau bz z i * Real.sqrt ‖wz‖) ^ 2 *
      ‖deriv (fun s ↦ rootAmplitude center tau (b s) (x s) i • radialSqrt (w s)) t‖ ^ 2) ≤
      2 * bz ^ 2 * ‖wz‖ ^ 3 * ‖w t‖ ^ 3 *
        (2 * bd ^ 2 + b t ^ 2 / tau ^ 2 * ‖v‖ ^ 2 * twoPointDistanceMoment center tau (x t) z) +
      8 * bz ^ 2 * b t ^ 2 * ‖wz‖ ^ 3 * ‖w t‖ * ‖wd‖ ^ 2 := by
  have hp (i : ι) := mul_le_mul_of_nonneg_left
    (norm_deriv_smul_radialSqrt_sq_le
      (differentiableAt_rootAmplitude center tau hb hx i).hasDerivAt hw)
    (sq_nonneg (rootAmplitude center tau bz z i * Real.sqrt ‖wz‖))
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hp i)) (sq_nonneg ‖wz‖)
  have he : ‖wz‖ ^ 2 * (∑ i, (rootAmplitude center tau bz z i * Real.sqrt ‖wz‖) ^ 2 *
      (2 * deriv (fun s ↦ rootAmplitude center tau (b s) (x s) i) t ^ 2 * ‖w t‖ ^ 3 +
        8 * rootAmplitude center tau (b t) (x t) i ^ 2 * ‖w t‖ * ‖wd‖ ^ 2)) =
      2 * ‖wz‖ ^ 3 * ‖w t‖ ^ 3 * (∑ i, rootAmplitude center tau bz z i ^ 2 *
        deriv (fun s ↦ rootAmplitude center tau (b s) (x s) i) t ^ 2) +
      8 * ‖wz‖ ^ 3 * ‖w t‖ * ‖wd‖ ^ 2 *
        (∑ i, rootAmplitude center tau bz z i ^ 2 * rootAmplitude center tau (b t) (x t) i ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_pow, Real.sq_sqrt (norm_nonneg wz)]
    ring
  rw [he] at hs
  have h0 := mul_le_mul_of_nonneg_left (sum_rootAmplitude_sq_mul_deriv_sq_le center tau hb hx bz z)
    (show 0 ≤ 2 * ‖wz‖ ^ 3 * ‖w t‖ ^ 3 by positivity)
  have h1 := mul_le_mul_of_nonneg_left (sum_rootAmplitude_sq_mul_sq_le center tau (b t) bz (x t) z)
    (show 0 ≤ 8 * ‖wz‖ ^ 3 * ‖w t‖ * ‖wd‖ ^ 2 by positivity)
  exact hs.trans ((add_le_add h0 h1).trans_eq (by ring))

end Mettapedia.Analysis.RootPartitionEnergy
