import MettapediaNS.ViscousMemorySoftExcess

/-!
# Scalar certificates for a joint pressure/geometry diffusion completion

The companion lab derives uniform matrix estimates for the actual gradient
and retained-pressure variables. These declarations certify their scalar
sum-of-squares, branch-combination and receiver-payment steps. They do not
identify a matrix derivative with the NS PDE or bound nonlinear histories.

The completed observable retains both pressure and core branches. Its local
diffusion controls the full strain-receiver derivative with weight `1/Q`.
The anisotropic, nonlocal memory-pressure comparison remains a separate
obligation, as does the signed production allowance for continuation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes
namespace PressureDiffusionCompletion

/-- In the matrix interpretation, `r = ‖B‖²`, `q = sqrt(σ²+‖P‖²)`,
`e = ‖E‖²`, `d = B:E`, `l = (P:L)/q`, and `g = ‖L‖²`. -/
def completionCurvature (r q e d l g : ℝ) : ℝ :=
  8 * d ^ 2 + 4 * (r + q) * e + 8 * d * l + 2 * g +
    2 * r / q * (g - l ^ 2)

theorem completion_curvature_decomposition (r q e d l g : ℝ) (hq : q ≠ 0) :
    completionCurvature r q e d l g =
      2 * (r + q) * e + (2 / 5 : ℝ) * g +
        ((2 / 5 : ℝ) * (5 * d + 2 * l) ^ 2 + 2 * (r * e - d ^ 2) +
          2 * q * e + (8 / 5 : ℝ) * (g - l ^ 2) +
            2 * r / q * (g - l ^ 2)) := by
  unfold completionCurvature
  field_simp
  ring

/-- The matrix Cauchy--Schwarz inequalities are explicit hypotheses. -/
theorem completion_curvature_lower (r q e d l g : ℝ)
    (hr : 0 ≤ r) (hq : 0 < q) (he : 0 ≤ e)
    (hd : d ^ 2 ≤ r * e) (hl : l ^ 2 ≤ g) :
    2 * (r + q) * e + (2 / 5 : ℝ) * g ≤ completionCurvature r q e d l g := by
  rw [completion_curvature_decomposition r q e d l g hq.ne']
  have hd' : 0 ≤ r * e - d ^ 2 := sub_nonneg.mpr hd
  have hl' : 0 ≤ g - l ^ 2 := sub_nonneg.mpr hl
  exact le_add_of_nonneg_right (by positivity)

/-- The analytic core estimate is completed uniformly in both variables. -/
theorem completed_core_lower (r q e g c k : ℝ)
    (hr : 0 ≤ r) (hq : 0 ≤ q) (he : 0 ≤ e) (hg : 0 ≤ g)
    (hc : -(1744 / 21 : ℝ) * r * e ≤ c)
    (hk : 2 * (r + q) * e + (2 / 5 : ℝ) * g ≤ k) :
    8 * (r + q) * e + (56 / 5 : ℝ) * g ≤ c + 48 * k := by
  nlinarith [mul_nonneg hr he, mul_nonneg hq he]

/-- The mixed pressure derivative is retained in the analytic input bound. -/
theorem completed_pressure_lower (r q e g p k : ℝ)
    (hq : 0 ≤ q) (he : 0 ≤ e)
    (hp : -(88 * r + 8 * q) * e - 8 * g ≤ p)
    (hk : 2 * (r + q) * e + (2 / 5 : ℝ) * g ≤ k) :
    8 * (r + q) * e + (56 / 5 : ℝ) * g ≤ p + 48 * k := by
  nlinarith [mul_nonneg hq he]

/-- With `ρ²=A²+B²`, this is the positive square in the Hessian of the
Euclidean norm of the two positive completed branches. -/
theorem radial_curvature_square (A B ρ a b : ℝ) :
    ρ ^ 2 * (a ^ 2 + b ^ 2) - (A * a + B * b) ^ 2 - (B * a - A * b) ^ 2 =
      (ρ ^ 2 - A ^ 2 - B ^ 2) * (a ^ 2 + b ^ 2) := by
  ring

theorem radial_curvature_lower (A B ρ a b c d k : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ) (hs : ρ ≤ A + B)
    (hk : 0 ≤ k) (hc : k ≤ c) (hd : k ≤ d) :
    k ≤ (A * c + B * d) / ρ + (B * a - A * b) ^ 2 / ρ ^ 3 := by
  have hf : k ≤ (A * c + B * d) / ρ := by
    apply (le_div_iff₀ hρ).2
    have h1 := mul_le_mul_of_nonneg_left hc hA
    have h2 := mul_le_mul_of_nonneg_left hd hB
    have h3 := mul_le_mul_of_nonneg_right hs hk
    nlinarith
  exact hf.trans (le_add_of_nonneg_right (by positivity))

/-- Upper certificate for the pure strain slot of the radial completion.
The physical matrix estimates supplying its hypotheses are analytic. -/
theorem radial_strain_upper (A B ρ Q a b c d v : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ) (hQ : 0 ≤ Q)
    (hAρ : A ≤ ρ) (hBρ : B ≤ ρ) (hscale : 48 * Q ^ 2 ≤ ρ)
    (hc : c ≤ 596 * Q) (hd : d ≤ 601 * Q)
    (ha : a ^ 2 ≤ 212 ^ 2 * Q ^ 3) (hb : b ^ 2 ≤ 217 ^ 2 * Q ^ 3)
    (hv : v ≤ (A * c + B * d) / ρ + (a ^ 2 + b ^ 2) / ρ) :
    v ≤ 3200 * Q := by
  have h1 := mul_le_mul_of_nonneg_left hc hA
  have h2 := mul_le_mul_of_nonneg_left hd hB
  have h3 := mul_le_mul_of_nonneg_right hAρ (show 0 ≤ 596 * Q by positivity)
  have h4 := mul_le_mul_of_nonneg_right hBρ (show 0 ≤ 601 * Q by positivity)
  have hf : (A * c + B * d) / ρ ≤ 1197 * Q := by
    apply (div_le_iff₀ hρ).2
    nlinarith
  have h5 := mul_le_mul_of_nonneg_right hscale hQ
  have hg : (a ^ 2 + b ^ 2) / ρ ≤ (92033 / 48 : ℝ) * Q := by
    apply (div_le_iff₀ hρ).2
    nlinarith only [ha, hb, h5]
  nlinarith only [hv, hf, hg, hQ]

theorem receiver_weight_scale (b z : ℝ) (hb : 0 < b) (hbz : b ≤ z) :
    z * ViscousMemorySoftExcess.curvature b z ≤ 2 := by
  have hz : 0 < z := hb.trans_le hbz
  rw [show z * ViscousMemorySoftExcess.curvature b z = 2 * b ^ 2 / z ^ 2 by
    unfold ViscousMemorySoftExcess.curvature
    field_simp]
  apply (div_le_iff₀ (sq_pos_of_pos hz)).2
  nlinarith

/-- For `M=a T`, the squared product-rule bound and the two physical
estimates give a payment for the entire derivative. The norm here has
weight `1/Q`, not the nonlocal memory matrix weights. -/
theorem full_receiver_gradient_paid (ν Q a m₂ T₂ da₂ dT₂ J D : ℝ)
    (hν : 0 ≤ ν) (hQ : 0 < Q) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hJ : 0 ≤ J) (hD : 0 ≤ D)
    (hm : m₂ ≤ 2 * T₂ * da₂ + 2 * a ^ 2 * dT₂)
    (hweight : ν / Q * T₂ * da₂ ≤ 3875 * J)
    (htensor : ν / Q * dT₂ ≤ 3200 * D) :
    ν / (8000 * Q) * m₂ ≤ J + a * D := by
  have hp := mul_le_mul_of_nonneg_left hm (div_nonneg hν hQ.le)
  have ht := mul_le_mul_of_nonneg_left htensor (sq_nonneg a)
  have haa : a ^ 2 ≤ a := by nlinarith
  have hDa := mul_le_mul_of_nonneg_right haa hD
  have hpay : ν / Q * m₂ ≤ 8000 * (J + a * D) := by
    nlinarith [mul_nonneg ha hD]
  have heq : ν / (8000 * Q) * m₂ = (ν / Q * m₂) / 8000 := by
    field_simp
  rw [heq]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 8000)).2 (by nlinarith)

end PressureDiffusionCompletion
end Mettapedia.FluidDynamics.NavierStokes
