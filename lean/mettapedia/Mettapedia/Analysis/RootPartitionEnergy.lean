import Mettapedia.Analysis.RadialSquareRoot
import Mettapedia.Analysis.GaussianPartitionEnergy

/-!
# Weighted derivative energy for fourth-power root partitions

The derivative energy is weighted by a second copy of the scalar root
patch. This retains fourth-power normalization and avoids a direct count
of patches. It is not the unweighted derivative energy of scalar cutoffs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RootPartitionEnergy

open scoped BigOperators
open RadialSquareRoot GaussianPartitionEnergy FiniteExponentialWeights

variable {ι E F : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem sum_weighted_deriv_sq_le {a : ι → ℝ → ℝ} {ad : ι → ℝ}
    {w : ℝ → E} {v : E} {t : ℝ}
    (ha : ∀ i, HasDerivAt (a i) (ad i) t) (hw : HasDerivAt w v t) :
    (∑ i, (a i t * Real.sqrt ‖w t‖) ^ 2 *
      ‖deriv (fun s ↦ a i s • radialSqrt (w s)) t‖ ^ 2) ≤
      (∑ i, deriv (fun s ↦ a i s ^ 2) t ^ 2) * ‖w t‖ ^ 4 / 2 +
      8 * (∑ i, a i t ^ 4) * ‖w t‖ ^ 2 * ‖v‖ ^ 2 := by
  have h (i : ι) : (a i t * Real.sqrt ‖w t‖) ^ 2 *
      ‖deriv (fun s ↦ a i s • radialSqrt (w s)) t‖ ^ 2 ≤
      deriv (fun s ↦ a i s ^ 2) t ^ 2 * ‖w t‖ ^ 4 / 2 +
        8 * a i t ^ 4 * ‖w t‖ ^ 2 * ‖v‖ ^ 2 := by
    have hd : deriv (fun s ↦ a i s ^ 2) t = 2 * a i t * ad i := by
      simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using ((ha i).fun_pow 2).deriv
    have hb := mul_le_mul_of_nonneg_left (norm_deriv_smul_radialSqrt_sq_le (ha i) hw)
      (sq_nonneg (a i t * Real.sqrt ‖w t‖))
    exact hb.trans_eq (by
      simp only [hd, mul_pow, Real.sq_sqrt (norm_nonneg (w t))]
      ring)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ h i)
  simpa only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    ← Finset.mul_sum] using hs

variable [Nonempty ι]

def rootAmplitude (center : ι → F) (tau b : ℝ) (x : F) (i : ι) : ℝ :=
  b * Real.sqrt (gaussianAmplitude center tau x i)

omit [InnerProductSpace ℝ F] in
theorem rootAmplitude_sq (center : ι → F) (tau b : ℝ) (x : F) (i : ι) :
    rootAmplitude center tau b x i ^ 2 = b ^ 2 * gaussianAmplitude center tau x i := by
  have hp : 0 ≤ gaussianAmplitude center tau x i := (amplitude_pos _ i).le
  simp only [rootAmplitude, mul_pow, Real.sq_sqrt hp]

omit [InnerProductSpace ℝ F] in
theorem sum_rootAmplitude_fourth (center : ι → F) (tau b : ℝ) (x : F) :
    (∑ i, rootAmplitude center tau b x i ^ 4) = b ^ 4 := by
  simp_rw [show ∀ i, rootAmplitude center tau b x i ^ 4 =
    (rootAmplitude center tau b x i ^ 2) ^ 2 from fun _ ↦ by ring,
    rootAmplitude_sq, mul_pow]
  rw [← Finset.mul_sum, sum_gaussianAmplitude_sq]
  ring

theorem differentiableAt_rootAmplitude (center : ι → F) (tau : ℝ)
    {b : ℝ → ℝ} {bd : ℝ} {x : ℝ → F} {v : F} {t : ℝ}
    (hb : HasDerivAt b bd t) (hx : HasDerivAt x v t) (i : ι) :
    DifferentiableAt ℝ (fun s ↦ rootAmplitude center tau (b s) (x s) i) t :=
  hb.differentiableAt.mul ((hasDerivAt_gaussianAmplitude center tau hx i).differentiableAt.sqrt
    (ne_of_gt (amplitude_pos _ i)))

theorem sum_deriv_rootAmplitude_sq_sq_le (center : ι → F) (tau : ℝ) (ht : 0 < tau)
    {b : ℝ → ℝ} {bd : ℝ} {x : ℝ → F} {v : F} {t : ℝ}
    (hb : HasDerivAt b bd t) (hx : HasDerivAt x v t) (j : ι) :
    (∑ i, deriv (fun s ↦ rootAmplitude center tau (b s) (x s) i ^ 2) t ^ 2) ≤
      4 * b t ^ 2 * bd ^ 2 + b t ^ 4 *
        (‖x t - center j‖ ^ 2 + tau * Real.log (Fintype.card ι)) * ‖v‖ ^ 2 / tau ^ 2 := by
  simp_rw [rootAmplitude_sq]
  have h := sum_scaled_deriv_sq_le center tau ht hx (hb.pow 2) j
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  convert h using 1
  ring

theorem sum_weighted_rootVorticity_deriv_sq_le (center : ι → F) (tau : ℝ) (ht : 0 < tau)
    {b : ℝ → ℝ} {bd : ℝ} {x : ℝ → F} {v : F} {w : ℝ → E} {wd : E} {t : ℝ}
    (hb : HasDerivAt b bd t) (hx : HasDerivAt x v t) (hw : HasDerivAt w wd t) (j : ι) :
    (∑ i, (rootAmplitude center tau (b t) (x t) i * Real.sqrt ‖w t‖) ^ 2 *
      ‖deriv (fun s ↦ rootAmplitude center tau (b s) (x s) i • radialSqrt (w s)) t‖ ^ 2) ≤
      2 * b t ^ 2 * bd ^ 2 * ‖w t‖ ^ 4 +
      b t ^ 4 * (‖x t - center j‖ ^ 2 + tau * Real.log (Fintype.card ι)) *
        ‖v‖ ^ 2 * ‖w t‖ ^ 4 / (2 * tau ^ 2) +
      8 * b t ^ 4 * ‖w t‖ ^ 2 * ‖wd‖ ^ 2 := by
  have ha (i : ι) := (differentiableAt_rootAmplitude center tau hb hx i).hasDerivAt
  have h := sum_weighted_deriv_sq_le ha hw
  rw [sum_rootAmplitude_fourth] at h
  have hm := mul_le_mul_of_nonneg_right (sum_deriv_rootAmplitude_sq_sq_le center tau ht hb hx j)
    (show 0 ≤ ‖w t‖ ^ 4 / 2 by positivity)
  have hfinal := add_le_add_right hm (8 * b t ^ 4 * ‖w t‖ ^ 2 * ‖wd‖ ^ 2)
  exact h.trans (by
    convert hfinal using 1 <;> ring)

end Mettapedia.Analysis.RootPartitionEnergy
