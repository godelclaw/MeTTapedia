import Mettapedia.Analysis.SchwartzDilation

/-!
# Dimension-sharp decay of finite dyadic Schwartz sums

A rational telescoping majorant controls a dyadic family without a
cutoff-dependent constant or a logarithmic loss. Three adjacent Schwartz
seminorms supply the majorant. The starting dilation can be any positive
number; its value does not enter the final bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SchwartzDyadicDecay

open SchwartzDilation
open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def transitionBound (f : 𝓢(E, ℂ)) (m : ℕ) : ℝ :=
  SchwartzMap.seminorm ℝ m 0 f + 3 * SchwartzMap.seminorm ℝ (m + 1) 0 f +
    2 * SchwartzMap.seminorm ℝ (m + 2) 0 f

theorem transitionBound_nonneg (f : 𝓢(E, ℂ)) (m : ℕ) : 0 ≤ transitionBound f m := by
  unfold transitionBound
  positivity

/-- A single rational transition pays for both small and large spatial arguments. -/
theorem pow_mul_norm_le_transition (f : 𝓢(E, ℂ)) (m : ℕ) (x : E) :
    ‖x‖ ^ (m + 1) * ‖f x‖ ≤ transitionBound f m *
      ((1 + ‖x‖)⁻¹ - (1 + 2 * ‖x‖)⁻¹) := by
  have h₀ := SchwartzMap.norm_pow_mul_le_seminorm ℝ f m x
  have h₁ := SchwartzMap.norm_pow_mul_le_seminorm ℝ f (m + 1) x
  have h₂ := SchwartzMap.norm_pow_mul_le_seminorm ℝ f (m + 2) x
  have he : (1 + ‖x‖)⁻¹ - (1 + 2 * ‖x‖)⁻¹ =
      ‖x‖ / ((1 + ‖x‖) * (1 + 2 * ‖x‖)) := by
    field_simp
    ring
  rw [he, ← mul_div_assoc, le_div_iff₀ (by positivity)]
  calc
    _ = ‖x‖ * (‖x‖ ^ m * ‖f x‖ + 3 * (‖x‖ ^ (m + 1) * ‖f x‖) +
        2 * (‖x‖ ^ (m + 2) * ‖f x‖)) := by simp only [pow_succ]; ring
    _ ≤ ‖x‖ * transitionBound f m := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      unfold transitionBound
      linarith only [h₀, h₁, h₂]
    _ = _ := mul_comm _ _

def dimensionBound (f : 𝓢(E, ℂ)) : ℝ := transitionBound f (Module.finrank ℝ E - 1)

theorem dimensionBound_nonneg (f : 𝓢(E, ℂ)) : 0 ≤ dimensionBound f :=
  transitionBound_nonneg f _

private theorem telescoping_sum (a : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (a n - a (n + 1))) = a 0 - a N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

/-- The true dimension power is uniform in both the top cutoff and the
positive starting scale. The estimate also holds at the origin. -/
theorem pow_mul_norm_sum_dilate_le (f : 𝓢(E, ℂ))
    (hd : 0 < Module.finrank ℝ E) (r : ℝ) (hr : 0 < r) (N : ℕ) (x : E) :
    ‖x‖ ^ Module.finrank ℝ E *
      ‖∑ n ∈ Finset.range N,
        dilate ((2 : ℝ) ^ n * r) (by positivity : (2 : ℝ) ^ n * r ≠ 0) f x‖ ≤
      dimensionBound f := by
  let a : ℕ → ℝ := fun n => (1 + (2 : ℝ) ^ n * r * ‖x‖)⁻¹
  have hdim : Module.finrank ℝ E - 1 + 1 = Module.finrank ℝ E := by omega
  have hterm (n : ℕ) :
      ‖x‖ ^ Module.finrank ℝ E *
        ‖dilate ((2 : ℝ) ^ n * r) (by positivity) f x‖ ≤
          dimensionBound f * (a n - a (n + 1)) := by
    have hs : 0 < (2 : ℝ) ^ n * r := by positivity
    have he : ‖x‖ ^ Module.finrank ℝ E *
        ‖dilate ((2 : ℝ) ^ n * r) (by positivity) f x‖ =
          ‖((2 : ℝ) ^ n * r) • x‖ ^ Module.finrank ℝ E *
            ‖f (((2 : ℝ) ^ n * r) • x)‖ := by
      rw [dilate_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow]
      ring
    rw [he]
    have hb := pow_mul_norm_le_transition f (Module.finrank ℝ E - 1)
      (((2 : ℝ) ^ n * r) • x)
    rw [hdim] at hb
    convert hb using 1
    simp only [a, dimensionBound, norm_smul, Real.norm_eq_abs, abs_of_pos hs, pow_succ]
    congr 2
    ring
  have ha₀ : a 0 ≤ 1 := by
    apply inv_le_one_of_one_le₀
    change (1 : ℝ) ≤ 1 + (2 : ℝ) ^ 0 * r * ‖x‖
    simp only [pow_zero, one_mul]
    linarith [mul_nonneg hr.le (norm_nonneg x)]
  have haN : 0 ≤ a N := by dsimp [a]; positivity
  calc
    _ ≤ ‖x‖ ^ Module.finrank ℝ E * ∑ n ∈ Finset.range N,
        ‖dilate ((2 : ℝ) ^ n * r) (by positivity) f x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ n ∈ Finset.range N, ‖x‖ ^ Module.finrank ℝ E *
        ‖dilate ((2 : ℝ) ^ n * r) (by positivity) f x‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ n ∈ Finset.range N, dimensionBound f * (a n - a (n + 1)) :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ = dimensionBound f * (a 0 - a N) := by rw [← Finset.mul_sum, telescoping_sum]
    _ ≤ dimensionBound f * 1 :=
      mul_le_mul_of_nonneg_left (by linarith only [ha₀, haN]) (dimensionBound_nonneg f)
    _ = _ := mul_one _

end Mettapedia.Analysis.SchwartzDyadicDecay
