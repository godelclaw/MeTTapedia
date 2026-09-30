import MettapediaNS.SelectedPressureCotangent
import MettapediaNS.PressureDiffusionCompletion

/-!
# Complete local receiver payments and signed velocity work

The companion lab derives the complete gradient and pressure-slot bounds
for the joint geometric observable. These declarations certify their
radial and product-rule coefficients. Matrix derivative identification
and the weak construction of the joint receivers remain analytic inputs.

The complete pressure receiver has weight `q / Q`, unlike the unweighted
canonical pressure component. No weighted Helmholtz contraction is used.
The signed work theorem retains both divergence receivers on the actual
NS time tangent. Neither a finite-history allowance nor a payment of the
complete projected velocity norm is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.JointReceiverDiffusion

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal EulerMeanClassical
  WholeSpaceBetchov
  WholeSpaceOrderEnergy WholeSpaceViscousEnergy WholeSpacePressureProduction
  SelectedPressureCotangent MiddleEigenvalueAlgebra

open scoped Topology NNReal

/-- The complete `B` slot varies vorticity as well as symmetric strain.
The companion matrix bounds supplying these hypotheses are analytic. -/
theorem radial_full_B_upper (A B ρ Q a b c d v : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ) (hQ : 0 ≤ Q)
    (hAρ : A ≤ ρ) (hBρ : B ≤ ρ) (hscale : 48 * Q ^ 2 ≤ ρ)
    (hc : c ≤ 1400 * Q) (hd : d ≤ 1400 * Q)
    (ha : a ^ 2 ≤ 90000 * Q ^ 3) (hb : b ^ 2 ≤ 90000 * Q ^ 3)
    (hv : v ≤ (A * c + B * d) / ρ + (a ^ 2 + b ^ 2) / ρ) :
    v ≤ 6600 * Q := by
  have h1 := mul_le_mul_of_nonneg_left hc hA
  have h2 := mul_le_mul_of_nonneg_left hd hB
  have h3 := mul_le_mul_of_nonneg_right hAρ (show 0 ≤ 1400 * Q by positivity)
  have h4 := mul_le_mul_of_nonneg_right hBρ (show 0 ≤ 1400 * Q by positivity)
  have hf : (A * c + B * d) / ρ ≤ 2800 * Q := by
    apply (div_le_iff₀ hρ).2
    nlinarith only [h1, h2, h3, h4]
  have h5 := mul_le_mul_of_nonneg_right hscale hQ
  have hg : (a ^ 2 + b ^ 2) / ρ ≤ 3750 * Q := by
    apply (div_le_iff₀ hρ).2
    nlinarith only [ha, hb, h5]
  nlinarith only [hv, hf, hg, hQ]

/-- The full pressure-slot upper block grows with `Q/q`. This factor is
retained; it cannot be discarded before the projection or time work. -/
theorem radial_full_pressure_upper (A B ρ Q q a b c d v : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ) (hq : 0 < q) (hqQ : q ≤ Q)
    (hAρ : A ≤ ρ) (hBρ : B ≤ ρ) (hscale : 48 * Q ^ 2 ≤ ρ)
    (hc : c ≤ 96 * Q / q) (hd : d ≤ 96 * Q / q)
    (ha : a ^ 2 ≤ 10000 * Q ^ 2) (hb : b ^ 2 ≤ 9216 * Q ^ 2)
    (hv : v ≤ (A * c + B * d) / ρ + (a ^ 2 + b ^ 2) / ρ) :
    v ≤ 600 * Q / q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have h1 := mul_le_mul_of_nonneg_left hc hA
  have h2 := mul_le_mul_of_nonneg_left hd hB
  have h3 := mul_le_mul_of_nonneg_right hAρ
    (show 0 ≤ 96 * Q / q by positivity)
  have h4 := mul_le_mul_of_nonneg_right hBρ
    (show 0 ≤ 96 * Q / q by positivity)
  have hf : (A * c + B * d) / ρ ≤ 192 * Q / q := by
    apply (div_le_iff₀ hρ).2
    have he : 192 * Q / q * ρ = ρ * (96 * Q / q) + ρ * (96 * Q / q) := by ring
    rw [he]
    exact add_le_add (h1.trans h3) (h2.trans h4)
  have hg : (a ^ 2 + b ^ 2) / ρ ≤ (1201 / 3 : ℝ) := by
    apply (div_le_iff₀ hρ).2
    nlinarith only [ha, hb, hscale]
  have hratio : 1 ≤ Q / q := (one_le_div hq).2 hqQ
  have he : 192 * Q / q = 192 * (Q / q) := by ring
  have he' : 600 * Q / q = 600 * (Q / q) := by ring
  rw [he] at hf
  rw [he']
  nlinarith only [hv, hf, hg, hratio]

/-- Selection payment from the complete gradient sensitivity. The base
perspective curvature supplies `ν Φ |∇a|² ≤ 2J`. -/
theorem full_B_selector_paid (ν Q Φ T₂ da₂ J : ℝ)
    (hν : 0 ≤ ν) (hQ : 0 < Q) (hda : 0 ≤ da₂)
    (hT : T₂ ≤ 180000 * Q ^ 3) (hΦ : 48 * Q ^ 2 ≤ Φ)
    (hweight : ν * Φ * da₂ ≤ 2 * J) :
    ν / Q * T₂ * da₂ ≤ 7500 * J := by
  have h1 := mul_le_mul_of_nonneg_left hΦ (show 0 ≤ 3750 * Q by positivity)
  have h2 : T₂ ≤ 3750 * Q * Φ := by nlinarith only [hT, h1]
  have h3 := mul_le_mul_of_nonneg_left h2 (div_nonneg hν hQ.le)
  have h4 := mul_le_mul_of_nonneg_right h3 hda
  have he : ν / Q * (3750 * Q * Φ) * da₂ = 3750 * (ν * Φ * da₂) := by
    field_simp
  rw [he] at h4
  nlinarith only [h4, hweight]

/-- The pressure selector is paid in its actual `q/Q` norm. -/
theorem pressure_selector_paid (ν Q q Φ T₂ da₂ J : ℝ)
    (hν : 0 ≤ ν) (hQ : 0 < Q) (_hq : 0 ≤ q) (hqQ : q ≤ Q) (hda : 0 ≤ da₂)
    (hT : 0 ≤ T₂) (hTbound : T₂ ≤ 20000 * Q ^ 2)
    (hΦ : 48 * Q ^ 2 ≤ Φ) (hweight : ν * Φ * da₂ ≤ 2 * J) :
    ν * (q / Q) * T₂ * da₂ ≤ (2500 / 3 : ℝ) * J := by
  have h1 : T₂ ≤ (1250 / 3 : ℝ) * Φ := by nlinarith only [hTbound, hΦ]
  have hratio : q / Q ≤ 1 := (div_le_one hQ).2 hqQ
  have h2 := mul_le_mul_of_nonneg_right hratio hT
  have h3 : q / Q * T₂ ≤ (1250 / 3 : ℝ) * Φ := h2.trans (by simpa using h1)
  have h4 := mul_le_mul_of_nonneg_left h3 hν
  have h5 := mul_le_mul_of_nonneg_right h4 hda
  nlinarith only [h5, hweight]

/-- Full gradient-slot product rule, including vorticity variations. -/
theorem full_B_receiver_gradient_paid (ν Q a m₂ T₂ da₂ dT₂ J D : ℝ)
    (hν : 0 ≤ ν) (hQ : 0 < Q) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (_hJ : 0 ≤ J) (hD : 0 ≤ D)
    (hm : m₂ ≤ 2 * T₂ * da₂ + 2 * a ^ 2 * dT₂)
    (hweight : ν / Q * T₂ * da₂ ≤ 7500 * J)
    (htensor : ν / Q * dT₂ ≤ 6600 * D) :
    ν / Q * m₂ ≤ 15000 * (J + a * D) := by
  have hp := mul_le_mul_of_nonneg_left hm (div_nonneg hν hQ.le)
  have ht := mul_le_mul_of_nonneg_left htensor (sq_nonneg a)
  have haa : a ^ 2 ≤ a := by nlinarith only [ha, ha1]
  have hDa := mul_le_mul_of_nonneg_right haa hD
  nlinarith only [hp, ht, hweight, hDa, mul_nonneg ha hD]

/-- Full observer-pressure product rule; its normalized cost keeps `q/Q`. -/
theorem pressure_receiver_gradient_paid (ν Q q a n₂ T₂ da₂ dT₂ J D : ℝ)
    (hν : 0 ≤ ν) (hQ : 0 < Q) (hq : 0 ≤ q) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hJ : 0 ≤ J) (hD : 0 ≤ D)
    (hn : n₂ ≤ 2 * T₂ * da₂ + 2 * a ^ 2 * dT₂)
    (hweight : ν * (q / Q) * T₂ * da₂ ≤ (2500 / 3 : ℝ) * J)
    (htensor : ν * (q / Q) * dT₂ ≤ 600 * D) :
    ν * (q / Q) * n₂ ≤ 1700 * (J + a * D) := by
  have hp := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ ν * (q / Q))
  have ht := mul_le_mul_of_nonneg_left htensor (sq_nonneg a)
  have haa : a ^ 2 ≤ a := by nlinarith only [ha, ha1]
  have hDa := mul_le_mul_of_nonneg_right haa hD
  nlinarith only [hp, ht, hweight, hDa, hJ, mul_nonneg ha hD]

/-- The canonical `2aP` component is added without replacing the full
observer-pressure receiver by it. Its unweighted payment is explicit. -/
theorem joint_pressure_gradient_paid (ν Q q n₂ p₂ total₂ R : ℝ)
    (hν : 0 ≤ ν) (hQ : 0 < Q) (hq : 0 ≤ q) (hqQ : q ≤ Q)
    (hp : 0 ≤ p₂) (hR : 0 ≤ R)
    (htotal : total₂ ≤ 2 * n₂ + 2 * p₂)
    (hnative : ν * (q / Q) * n₂ ≤ 1700 * R)
    (hcanonical : ν * p₂ ≤ 16 * R) :
    ν * (q / Q) * total₂ ≤ 3500 * R := by
  have hw0 : 0 ≤ ν * (q / Q) := by positivity
  have hw1 : q / Q ≤ 1 := (div_le_one hQ).2 hqQ
  have hp1 := mul_le_mul_of_nonneg_right hw1 hp
  have hp2 := mul_le_mul_of_nonneg_left hp1 hν
  have ht := mul_le_mul_of_nonneg_left htotal hw0
  nlinarith only [ht, hnative, hcanonical, hp2, hR]

/-- Local representative of the complete divergence-form velocity work. -/
def jointVelocityCotangent (B : GradMatrix) (D V : Space) : Space :=
  -D + localCotangent B V

/-- This comparison retains an UNWEIGHTED projection norm. The pressure
receiver's `q/Q` gradient payment does not supply that norm. -/
theorem joint_velocity_norm_le (B : GradMatrix) (D V : Space) (Q : ℝ)
    (hQ : 0 < Q) (hr : normSq B ≤ Q) :
    ‖jointVelocityCotangent B D V‖ ^ 2 / Q ≤
      2 * ‖D‖ ^ 2 / Q + 8 * ‖V‖ ^ 2 := by
  have hs := localCotangent_square_le B V
  have ht := norm_add_le (-D) (localCotangent B V)
  rw [norm_neg] at ht
  have h0 := norm_nonneg (-D + localCotangent B V)
  have h1 := norm_nonneg D
  have h2 := norm_nonneg (localCotangent B V)
  have hsq := sq_nonneg (‖D‖ - ‖localCotangent B V‖)
  have h3 := mul_le_mul_of_nonneg_right hr (sq_nonneg ‖V‖)
  unfold jointVelocityCotangent
  apply (div_le_iff₀ hQ).2
  have he : (2 * ‖D‖ ^ 2 / Q + 8 * ‖V‖ ^ 2) * Q =
      2 * ‖D‖ ^ 2 + 8 * Q * ‖V‖ ^ 2 := by field_simp
  rw [he]
  nlinarith only [hs, ht, h0, h1, h2, hsq, h3]

/-- Both receiver divergences are ordinary `L²` fields. Their weak
identification with the completed matrix observable remains explicit. -/
theorem joint_velocity_work_integrable (u v : SmoothL2Field Space) (D V : L2) :
    Integrable (fun x ↦ ⟪jointVelocityCotangent (gradMatrix u x) (D x) (V x),
      v.field x⟫_ℝ) := by
  have hd : Integrable (fun x ↦ -⟪D x, v.field x⟫_ℝ) := by
    apply (MeasureTheory.L2.integrable_inner D v.toLp).neg.congr
    filter_upwards [v.toLp_ae] with x hx
    simp only [Pi.neg_apply, hx]
  apply (hd.add (localCotangent_work_integrable u v V)).congr
  exact Filter.Eventually.of_forall fun x ↦ by
    simp only [Pi.add_apply, jointVelocityCotangent, inner_add_left, inner_neg_left]

/-- The complete signed velocity work retains the two receivers and the
actual canonical pressure variation. No absolute-value split is made. -/
theorem integral_joint_velocity_work (u v : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) (hv : v.toLp ∈ solenoidalSpace) (D N : L2) :
    (∫ x, ⟪jointVelocityCotangent (gradMatrix u x) (D x)
      ((-gradientSpace.starProjection N : L2) x), v.field x⟫_ℝ) =
      -⟪D, v.toLp⟫_ℝ - ⟪N, (pressureVariation u v).toLp⟫_ℝ := by
  have hd : Integrable (fun x ↦ -⟪D x, v.field x⟫_ℝ) := by
    apply (MeasureTheory.L2.integrable_inner D v.toLp).neg.congr
    filter_upwards [v.toLp_ae] with x hx
    simp only [Pi.neg_apply, hx]
  have he : (fun x ↦ ⟪jointVelocityCotangent (gradMatrix u x) (D x)
      ((-gradientSpace.starProjection N : L2) x), v.field x⟫_ℝ) =
      fun x ↦ -⟪D x, v.field x⟫_ℝ +
        ⟪localCotangent (gradMatrix u x) ((-gradientSpace.starProjection N : L2) x), v.field x⟫_ℝ := by
    funext x
    simp only [jointVelocityCotangent, inner_add_left, inner_neg_left]
  rw [he, integral_add hd (localCotangent_work_integrable u v _)]
  have hDi : (∫ x, -⟪D x, v.field x⟫_ℝ) = -⟪D, v.toLp⟫_ℝ := by
    rw [integral_neg, MeasureTheory.L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards [v.toLp_ae] with x hx
    simp only [hx]
  rw [hDi, integral_localCotangent_work]
  have hp := pressure_variation_work u v hu hv N
  linarith only [hp]

namespace NSEvolution

open Set WholeSpaceViscousFlow WholeSpaceTimeSmooth

/-- Signed joint divergence work on the actual complete physical-time
velocity and pressure derivatives. It supplies no nonlinear allowance. -/
theorem joint_velocity_work {ν T : ℝ} {hT : 0 ≤ T}
    (U : NSEvolution ν T hT) (hpos : 0 < T) (t : ℝ) (ht : t ∈ Ioo 0 T) (D N : L2) :
    let u := U.velocity ⟨t, ht.1.le, ht.2.le⟩;
    (∫ x, ⟪jointVelocityCotangent (gradMatrix u x) (D x)
      ((-gradientSpace.starProjection N : L2) x),
      (projectedNavierStokesRhs ν u).field x⟫_ℝ) =
      -⟪D, (projectedNavierStokesRhs ν u).toLp⟫_ℝ -
        ⟪N, deriv (fun r ↦ (pressureField (U.velocity (projIcc 0 T hT r))).toLp) t⟫_ℝ := by
  dsimp only
  rw [(SelectedPressureCotangent.NSEvolution.pressureGradient_hasDerivAt U hpos t ht).deriv]
  exact integral_joint_velocity_work _ _ (U.solenoidal _)
    (projectedNavierStokesRhs_mem_solenoidal ν _ (U.solenoidal _)) D N

end NSEvolution

end Mettapedia.FluidDynamics.NavierStokes.JointReceiverDiffusion
