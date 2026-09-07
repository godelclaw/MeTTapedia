import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSobolevAbsorption

/-!
# A zero-safe local bound for quadratic energy growth

The reciprocal of one plus the energy avoids division by a possibly zero
initial energy. The resulting time window is explicit and depends only on
the scalar growth constant and an initial bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeQuadraticGrowthWindow

def timeWindow (C B : ℝ) : ℝ := 1 / (2 * (C + 1) * (B + 1))

theorem timeWindow_pos (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) : 0 < timeWindow C B := by
  unfold timeWindow
  positivity

theorem reciprocal_growth_monotone (E dE : ℝ → ℝ) (C T : ℝ)
    (hC : 0 ≤ C) (hE : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ E t)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt E (dE t) t)
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) T, dE t ≤ C * (E t)^2) :
    MonotoneOn (fun t ↦ 1 / (E t + 1) + C * t) (Set.Icc (0 : ℝ) T) := by
  have hD (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      HasDerivAt (fun t ↦ 1 / (E t + 1) + C * t)
        (-dE t / (E t + 1)^2 + C) t := by
    have hp : E t + 1 ≠ 0 := by linarith [hE t ht]
    have h := ((hd t ht).add_const 1).inv hp |>.add ((hasDerivAt_id t).const_mul C)
    change HasDerivAt (fun tau ↦ (E tau + 1)⁻¹ + C * tau)
      (-dE t / (E t + 1)^2 + C * 1) t at h
    simpa only [one_div, mul_one] using h
  have hN (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : 0 ≤ -dE t / (E t + 1)^2 + C := by
    have hp : 0 < (E t + 1)^2 := by nlinarith [hE t ht]
    have hb : dE t ≤ C * (E t + 1)^2 := by
      nlinarith [hg t ht, mul_nonneg hC (hE t ht)]
    have hdiv := (div_le_iff₀ hp).mpr hb
    simpa only [neg_div, sub_eq_add_neg, add_comm] using sub_nonneg.mpr hdiv
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
  · exact fun t ht ↦ (hD t ht).continuousAt.continuousWithinAt
  · exact fun t ht ↦ (hD t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hD t (interior_subset ht)).deriv]
    exact hN t (interior_subset ht)

theorem quadratic_growth_bound (E dE : ℝ → ℝ) (C B T t : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hE : ∀ tau ∈ Set.Icc (0 : ℝ) T, 0 ≤ E tau)
    (hd : ∀ tau ∈ Set.Icc (0 : ℝ) T, HasDerivAt E (dE tau) tau)
    (hg : ∀ tau ∈ Set.Icc (0 : ℝ) T, dE tau ≤ C * (E tau)^2)
    (h0 : E 0 ≤ B) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hw : t ≤ timeWindow C B) : E t ≤ 2 * (B + 1) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hm := reciprocal_growth_monotone E dE C T hC hE hd hg
    (show (0 : ℝ) ∈ Set.Icc 0 T from ⟨le_rfl, hT⟩) ht ht.1
  have hp0 : 0 < E 0 + 1 := by linarith [hE 0 ⟨le_rfl, hT⟩]
  have hpB : 0 < B + 1 := by linarith
  have hpE : 0 < E t + 1 := by linarith [hE t ht]
  have hi : 1 / (B + 1) ≤ 1 / (E 0 + 1) :=
    one_div_le_one_div_of_le hp0 (by linarith)
  have hprod : t * (2 * (C+1) * (B+1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hw
  have hct : C * t ≤ 1 / (2 * (B+1)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg ht.1 hpB.le]
  have hhalf : 1 / (B+1) - 1 / (2 * (B+1)) = 1 / (2 * (B+1)) := by field_simp; ring
  have hinv : 1 / (2 * (B+1)) ≤ 1 / (E t+1) := by
    simp only [mul_zero, add_zero] at hm
    linarith
  have hcross := (div_le_div_iff₀ (show 0 < 2 * (B+1) by positivity) hpE).mp hinv
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeQuadraticGrowthWindow
