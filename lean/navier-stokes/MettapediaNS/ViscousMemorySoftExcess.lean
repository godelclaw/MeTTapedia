import MettapediaNS.WholeSpaceMemoryExcess

/-!
# A differentiable excess and its pressure-receiver weight

The perspective excess `(X-bh)₊²/X` controls the linear excess after doubling
the fixed threshold. Its first derivative has no jump at the level boundary.
The positive Hessian supplies a diffusion payment for the derivative of the
pressure-receiver weight. The last theorem connects this observable to the
actual whole-space memory-capacity criterion.

These are scalar, differential-algebraic and spatial-integral statements.
The physical memory construction, weak PDE chain rule and mixing histories
are analytic in the companion lab. No arbitrary-flow excess bound is proved.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes
namespace ViscousMemorySoftExcess

def excess (X h b : ℝ) : ℝ := if b * h < X then (X - b * h) ^ 2 / X else 0

theorem excess_nonneg (X h b : ℝ) (hX : 0 < X) : 0 ≤ excess X h b := by
  unfold excess
  split_ifs <;> positivity

/-- The new observable is below the linear positive part. -/
theorem excess_le_linear (X h b : ℝ) (hX : 0 < X) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    excess X h b ≤ max (X - b * h) 0 := by
  unfold excess
  split_ifs with ha
  · rw [max_eq_left (by linarith : 0 ≤ X - b * h)]
    apply (div_le_iff₀ hX).2
    nlinarith [mul_nonneg (mul_nonneg hb hh) (show 0 ≤ X - b * h by linarith)]
  · exact le_max_right _ _

/-- Doubling a datum-fixed threshold recovers the previous continuation
majorant; no future threshold or extra pointwise bound is used. -/
theorem threshold_coercivity (X h b : ℝ) (hX : 0 < X) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    X ≤ 2 * b * h + excess X h b := by
  unfold excess
  split_ifs with ha
  · have hq : (X - 2 * b * h) * X ≤ (X - b * h) ^ 2 := by
      nlinarith [sq_nonneg (b * h)]
    have hp := (le_div_iff₀ hX).2 hq
    linarith
  · have hm := mul_nonneg hb hh
    push Not at ha
    linarith

def curvature (b z : ℝ) : ℝ := 2 * b ^ 2 / z ^ 3

/-- Derivative on the active branch `z>b`. Its value tends to zero at b. -/
theorem active_hasDerivAt (b z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ (x - b) ^ 2 / x) (1 - b ^ 2 / z ^ 2) z := by
  convert! (((hasDerivAt_id z).sub_const b).pow 2).div (hasDerivAt_id z) hz using 1
  simp only [Pi.pow_apply, id_eq]
  field_simp
  ring

/-- The same curvature differentiates the pressure-receiver weight. -/
theorem weight_hasDerivAt (b z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ 1 - b ^ 2 / x ^ 2) (curvature b z) z := by
  convert! ((hasDerivAt_const z (b ^ 2)).div
    ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz)).const_sub 1 using 1
  simp only [Pi.pow_apply, id_eq, curvature]
  field_simp
  ring

/-- The active two-variable perspective Hessian is a square. In the PDE
its contribution has the dissipative sign `-ν Hessian`. -/
theorem perspective_hessian (X h b dX dh : ℝ) (hX : X ≠ 0) :
    2 * b ^ 2 * h ^ 2 / X ^ 3 * dX ^ 2 -
      4 * b ^ 2 * h / X ^ 2 * dX * dh + 2 * b ^ 2 / X * dh ^ 2 =
        2 * b ^ 2 / X ^ 3 * (h * dX - X * dh) ^ 2 := by
  field_simp
  ring

theorem curvature_nonneg (b z : ℝ) (hz : 0 < z) : 0 ≤ curvature b z := by
  unfold curvature
  positivity

theorem curvature_scale (b z : ℝ) (hb : 0 < b) (hbz : b ≤ z) :
    z ^ 2 * curvature b z ≤ 2 * b := by
  have hz : 0 < z := hb.trans_le hbz
  rw [show z ^ 2 * curvature b z = 2 * b ^ 2 / z by
    unfold curvature
    field_simp]
  apply (div_le_iff₀ hz).2
  nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hbz)]

theorem curvature_le (b z : ℝ) (hb : 0 < b) (hbz : b ≤ z) :
    curvature b z ≤ 2 / b := by
  have hp : b ^ 3 ≤ z ^ 3 := by gcongr
  calc
    curvature b z ≤ 2 * b ^ 2 / b ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    _ = 2 / b := by field_simp

/-- This pays the derivative of the cutoff weight, not the complete
pressure-test tensor or its nonlocal weighted norm. -/
theorem weight_gradient_paid (ν h b z g : ℝ)
    (hν : 0 ≤ ν) (hh : 0 ≤ h) (hb : 0 < b) (hbz : b ≤ z) :
    (ν * b * h / 2) * (curvature b z * g) ^ 2 ≤
      ν * h * curvature b z * g ^ 2 := by
  have hc := curvature_nonneg b z (hb.trans_le hbz)
  calc
    _ = curvature b z * ((ν * b * h / 2) * curvature b z * g ^ 2) := by ring
    _ ≤ (2 / b) * ((ν * b * h / 2) * curvature b z * g ^ 2) :=
      mul_le_mul_of_nonneg_right (curvature_le b z hb hbz) (by positivity)
    _ = _ := by field_simp

/-- If the actual strain sensitivity is bounded by `K X=K h z`, its
threshold-weight derivative has this explicit weighted diffusion payment.
Derivatives of that sensitivity itself remain a separate physical term. -/
theorem receiver_weight_paid (A K h b z g : ℝ) (hb : 0 < b) (hbz : b ≤ z)
    (hA : A ^ 2 ≤ K ^ 2 * h ^ 2 * z ^ 2) :
    A ^ 2 * (curvature b z * g) ^ 2 ≤
      2 * K ^ 2 * b * h ^ 2 * curvature b z * g ^ 2 := by
  have hc := curvature_nonneg b z (hb.trans_le hbz)
  calc
    _ ≤ (K ^ 2 * h ^ 2 * z ^ 2) * (curvature b z * g) ^ 2 :=
      mul_le_mul_of_nonneg_right hA (sq_nonneg _)
    _ = (z ^ 2 * curvature b z) * (K ^ 2 * h ^ 2 * curvature b z * g ^ 2) := by ring
    _ ≤ (2 * b) * (K ^ 2 * h ^ 2 * curvature b z * g ^ 2) :=
      mul_le_mul_of_nonneg_right (curvature_scale b z hb hbz) (by positivity)
    _ = _ := by ring

open MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field WholeSpaceBetchov MiddleEigenvalueAlgebra
  WholeSpaceMemoryEnvelope

/-- The physical observable's integrated excess supplies the exact spatial
hypothesis consumed by actual whole-space continuation. -/
theorem massEnvelope_of_soft_excess (u : SmoothL2Field Space) (X h c : Space → ℝ)
    {b k B E : ℝ} (hb : 0 < b) (hk : 0 < k)
    (hX : ∀ x, 0 < X x) (hh : ∀ x, 0 ≤ h x) (hhc : ∀ x, h x ≤ 1 + c x)
    (hc : Integrable c) (hc0 : ∀ x, 0 ≤ c x) (hcB : (∫ x, c x) ≤ B)
    (he : Integrable (fun x ↦ excess (X x) (h x) b))
    (heE : (∫ x, excess (X x) (h x) b) ≤ E)
    (hcoerce : ∀ x, k * vortSq (gradMatrix u x) ^ 2 ≤ X x) :
    MassEnvelope u (2 * b / k) (B + E / (2 * b)) := by
  have heE' : (∫ x, excess (X x) (h x) b / k) ≤ E / k := by
    rw [integral_div]
    exact div_le_div_of_nonneg_right heE hk.le
  have hp (x : Space) : vortSq (gradMatrix u x) ^ 2 ≤
      (2 * b / k) * (1 + c x) + excess (X x) (h x) b / k := by
    have ht := threshold_coercivity (X x) (h x) b (hX x) (hh x) hb.le
    have hm := mul_le_mul_of_nonneg_left (hhc x) (show 0 ≤ 2 * b by positivity)
    have hs : vortSq (gradMatrix u x) ^ 2 ≤
        (2 * b * (1 + c x) + excess (X x) (h x) b) / k :=
      (le_div_iff₀ hk).2 (by nlinarith only [hcoerce x, ht, hm])
    calc
      _ ≤ _ := hs
      _ = _ := by ring
  have hm := massEnvelope_of_excess u c (fun x ↦ excess (X x) (h x) b / k)
    (show 0 < 2 * b / k by positivity) hc (he.div_const k) hc0
    (fun x ↦ div_nonneg (excess_nonneg _ _ _ (hX x)) hk.le) hcB heE' hp
  convert! hm using 1
  field_simp

end ViscousMemorySoftExcess
end Mettapedia.FluidDynamics.NavierStokes
