import MettapediaNS.PlanarParentReserve

/-!
# A reserve for the first generated-parent interval

The physical calibration has a parent observation `U(t) = C t^2 + O(t^3)`,
an initially positive source observation `V(t) = M + O(t)`, and stretching
`G(t) = γ t + O(t^2)`. On a fixed original interval of length `H`, normalize
`s = t/H`, `p = U/(C H^2)`, `q = V/M`, and `g = G/(γ H)`.

The reserve below has physical scale `2 γ H^2`. Its complete derivative
pays `2 G` when the five normalized errors are small. The scalar calculus,
error absorption and payment are certified here. Identification with the
actual nonlocal fluid observations and their uniform local Taylor bounds
are analytic obligations. Nothing here bounds repeated regeneration or
permits restarting the reserve with a new initial allowance.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.RotationalForecastReserve

def reserve (s p q : ℝ) : ℝ :=
  2 * (1 - s) * p + (7 / 3 : ℝ) * (1 - s) ^ 3 * q

def rate (s p dp q dq : ℝ) : ℝ :=
  2 * ((1 - s) * dp - p) + (7 / 3 : ℝ) * (1 - s) ^ 3 * dq -
    7 * (1 - s) ^ 2 * q

theorem reserve_nonneg (s p q : ℝ) (hs : s ≤ 1) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 ≤ reserve s p q := by
  unfold reserve
  have ht : 0 ≤ 1 - s := sub_nonneg.mpr hs
  positivity

theorem reserve_initial : reserve 0 0 1 = 7 / 3 := by
  norm_num [reserve]

theorem reserve_terminal (p q : ℝ) : reserve 1 p q = 0 := by
  simp [reserve]

theorem reserve_derivative (p q : ℝ → ℝ) (s dp dq : ℝ)
    (hp : HasDerivAt p dp s) (hq : HasDerivAt q dq s) :
    HasDerivAt (fun x ↦ reserve x (p x) (q x)) (rate s (p s) dp (q s) dq) s := by
  have ht := (hasDerivAt_id s).const_sub 1
  have h := ((ht.const_mul 2).mul hp).add
    (((ht.pow 3).const_mul (7 / 3 : ℝ)).mul hq)
  apply h.congr_deriv
  dsimp [rate]
  ring

theorem physical_reserve_derivative (p q : ℝ → ℝ) (γ H t dp dq : ℝ)
    (hH : H ≠ 0) (hp : HasDerivAt p dp (t / H)) (hq : HasDerivAt q dq (t / H)) :
    HasDerivAt (fun x ↦ 2 * γ * H ^ 2 * reserve (x / H) (p (x / H)) (q (x / H)))
      (2 * γ * H * rate (t / H) (p (t / H)) dp (q (t / H)) dq) t := by
  have h := ((reserve_derivative p q (t / H) dp dq hp hq).comp t
    ((hasDerivAt_id t).div_const H)).const_mul (2 * γ * H ^ 2)
  apply h.congr_deriv
  field_simp

theorem physical_initial (γ H : ℝ) :
    2 * γ * H ^ 2 * reserve 0 0 1 = 14 * γ * H ^ 2 / 3 := by
  rw [reserve_initial]
  ring

theorem ideal_rate (s : ℝ) : rate s (s ^ 2) (2 * s) 1 0 + s =
    -13 * s ^ 2 + 19 * s - 7 := by
  unfold rate
  ring

theorem ideal_margin (s : ℝ) : -13 * s ^ 2 + 19 * s - 7 ≤ -(3 / 52 : ℝ) := by
  nlinarith [sq_nonneg (26 * s - 19)]

theorem rate_defect (s p dp q dq g : ℝ) :
    rate s p dp q dq + g = -13 * s ^ 2 + 19 * s - 7 +
      (2 * (1 - s) * (dp - 2 * s) - 2 * (p - s ^ 2) +
        (7 / 3 : ℝ) * (1 - s) ^ 3 * dq - 7 * (1 - s) ^ 2 * (q - 1) + (g - s)) := by
  unfold rate
  ring

theorem rate_error_bound (s p dp q dq g ε : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hp : |p - s ^ 2| ≤ ε) (hdp : |dp - 2 * s| ≤ ε)
    (hq : |q - 1| ≤ ε) (hdq : |dq| ≤ ε) (hg : |g - s| ≤ ε) :
    rate s p dp q dq + g ≤ -(3 / 52 : ℝ) + (43 / 3 : ℝ) * ε := by
  have ht0 : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have ht1 : 1 - s ≤ 1 := by linarith
  have ht2 : (1 - s) ^ 2 ≤ 1 := by nlinarith
  have ht3 : (1 - s) ^ 3 ≤ 1 := by
    have hm := mul_le_mul ht2 ht1 ht0 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [hm]
  have ep := (abs_le.mp hp).1
  have edp := (abs_le.mp hdp).2
  have eq := (abs_le.mp hq).1
  have edq := (abs_le.mp hdq).2
  have eg := (abs_le.mp hg).2
  have hdp' : (1 - s) * (dp - 2 * s) ≤ ε :=
    (mul_le_mul_of_nonneg_left edp ht0).trans
      (by nlinarith [mul_nonneg hε hs0])
  have hdq' : (1 - s) ^ 3 * dq ≤ ε :=
    (mul_le_mul_of_nonneg_left edq (by positivity)).trans
      (by nlinarith [mul_nonneg hε (sub_nonneg.mpr ht3)])
  have hq' : -(1 - s) ^ 2 * (q - 1) ≤ ε := by
    have hm := mul_le_mul_of_nonneg_left eq (sq_nonneg (1 - s))
    nlinarith [mul_nonneg hε (sub_nonneg.mpr ht2)]
  rw [rate_defect]
  have hi := ideal_margin s
  nlinarith only [hdp', hdq', hq', ep, eg, hi]

theorem strict_payment (s p dp q dq g ε : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (hsmall : ε ≤ 9 / 4472)
    (hp : |p - s ^ 2| ≤ ε) (hdp : |dp - 2 * s| ≤ ε)
    (hq : |q - 1| ≤ ε) (hdq : |dq| ≤ ε) (hg : |g - s| ≤ ε) :
    rate s p dp q dq + g ≤ -(3 / 104 : ℝ) := by
  have h := rate_error_bound s p dp q dq g ε hs0 hs1 hε hp hdp hq hdq hg
  linarith

theorem physical_payment (γ H ρ G ν D s p dp q dq g ε : ℝ)
    (hγ : 0 < γ) (hH : 0 < H) (hν : 0 ≤ ν) (hD : 0 ≤ D)
    (hρ : ρ = 2 * γ * H * rate s p dp q dq) (hG : G = γ * H * g)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (hsmall : ε ≤ 9 / 4472)
    (hp : |p - s ^ 2| ≤ ε) (hdp : |dp - 2 * s| ≤ ε)
    (hq : |q - 1| ≤ ε) (hdq : |dq| ≤ ε) (hg : |g - s| ≤ ε) :
    ρ + 2 * G - ν * D ≤ -(3 * γ * H / 52) := by
  have h := strict_payment s p dp q dq g ε hs0 hs1 hε hsmall hp hdp hq hdq hg
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * γ * H)
  rw [hρ, hG]
  nlinarith [mul_nonneg hν hD]

end Mettapedia.FluidDynamics.NavierStokes.RotationalForecastReserve
