import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Separated pressure response and a joint stretching budget

The fourth directional derivative of the three-dimensional Newtonian
kernel has an angular numerator `angularKernel`. For a unit radial vector,
its interval is `[-12,24] * ‖e‖² * ‖v‖²`. The proof keeps the orientation
and uses two sum-of-squares identities on the radial orthogonal complement.
Integrating away from a fixed radius gives a bound paid by kinetic energy.

The derivative identification with `1/(4π|x|)`, its realization as the
far part of the physical pressure Hessian, and the radial-swirl examples
are analytic in the companion lab documentation. The integral theorem
here is about the explicit kernel, with its measurability hypothesis.

For `ζ=(∇u)ω`, the unforced parabolic law is
`Dζ=-(Hess p)ω-2ν Σ_j (∂j∇u)(∂jω)`.
The joint energy `|ω|²+τ²|ζ|²` can absorb a bounded far-pressure part
with coefficient `1/τ+τK`. Its near-pressure and viscous cross terms
remain signed. The finite production estimate below does not assert a
bound on these remaining terms or arbitrary-data regularity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureBoundaryResponse

open scoped RealInnerProductSpace
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def orthogonalPart (n v : E) : E := v - ⟪v, n⟫ • n

theorem norm_orthogonalPart_sq (n v : E) (hn : ‖n‖ = 1) :
    ‖orthogonalPart n v‖ ^ 2 = ‖v‖ ^ 2 - ⟪v, n⟫ ^ 2 := by
  simp only [orthogonalPart, norm_sub_sq_real, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, sq_abs, hn, mul_one]
  ring

theorem inner_orthogonalPart (n e v : E) (hn : ‖n‖ = 1) :
    ⟪orthogonalPart n e, orthogonalPart n v⟫ = ⟪e, v⟫ - ⟪e, n⟫ * ⟪v, n⟫ := by
  simp only [orthogonalPart, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow]
  rw [real_inner_comm n v]
  ring

theorem gram_nonneg (e v : E) : 0 ≤ ‖e‖ ^ 2 * ‖v‖ ^ 2 - ⟪e, v⟫ ^ 2 := by
  have h := real_inner_mul_inner_self_le e v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith only [h]

/-- Angular numerator of `4π |x|⁵ ∂ee∂vv (1/(4π|x|))` when `n=x/|x|`. -/
def angularKernel (n e v : E) : ℝ :=
  105 * ⟪e, n⟫ ^ 2 * ⟪v, n⟫ ^ 2 -
    15 * (‖e‖ ^ 2 * ⟪v, n⟫ ^ 2 + ⟪e, n⟫ ^ 2 * ‖v‖ ^ 2 +
      4 * ⟪e, n⟫ * ⟪e, v⟫ * ⟪v, n⟫) +
    3 * (‖e‖ ^ 2 * ‖v‖ ^ 2 + 2 * ⟪e, v⟫ ^ 2)

theorem angularKernel_lower_certificate (n e v : E) (hn : ‖n‖ = 1) :
    angularKernel n e v + 12 * ‖e‖ ^ 2 * ‖v‖ ^ 2 =
      4 * (3 * ⟪e, n⟫ * ⟪v, n⟫ -
        2 * ⟪orthogonalPart n e, orthogonalPart n v⟫) ^ 2 +
      5 * ⟪orthogonalPart n e, orthogonalPart n v⟫ ^ 2 +
      15 * (‖orthogonalPart n e‖ ^ 2 * ‖orthogonalPart n v‖ ^ 2 -
        ⟪orthogonalPart n e, orthogonalPart n v⟫ ^ 2) := by
  simp only [angularKernel, norm_orthogonalPart_sq n _ hn,
    inner_orthogonalPart n e v hn]
  ring

theorem angularKernel_upper_certificate (n e v : E) (hn : ‖n‖ = 1) :
    24 * ‖e‖ ^ 2 * ‖v‖ ^ 2 - angularKernel n e v =
      4 * ‖(3 * ⟪v, n⟫) • orthogonalPart n e +
        (2 * ⟪e, n⟫) • orthogonalPart n v‖ ^ 2 +
      (15 * ‖orthogonalPart n e‖ ^ 2 + 20 * ⟪e, n⟫ ^ 2) *
        ‖orthogonalPart n v‖ ^ 2 +
      6 * (‖orthogonalPart n e‖ ^ 2 * ‖orthogonalPart n v‖ ^ 2 -
        ⟪orthogonalPart n e, orthogonalPart n v⟫ ^ 2) := by
  simp only [angularKernel, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right,
    norm_orthogonalPart_sq n _ hn, inner_orthogonalPart n e v hn]
  ring

theorem angularKernel_bounds (n e v : E) (hn : ‖n‖ = 1) :
    -12 * ‖e‖ ^ 2 * ‖v‖ ^ 2 ≤ angularKernel n e v ∧
      angularKernel n e v ≤ 24 * ‖e‖ ^ 2 * ‖v‖ ^ 2 := by
  have hg := gram_nonneg (orthogonalPart n e) (orthogonalPart n v)
  have hl : 0 ≤ angularKernel n e v + 12 * ‖e‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [angularKernel_lower_certificate n e v hn]
    positivity
  have hu : 0 ≤ 24 * ‖e‖ ^ 2 * ‖v‖ ^ 2 - angularKernel n e v := by
    rw [angularKernel_upper_certificate n e v hn]
    positivity
  constructor <;> linarith

theorem abs_angularKernel_le (n e v : E) (hn : ‖n‖ = 1) :
    |angularKernel n e v| ≤ 24 * ‖e‖ ^ 2 * ‖v‖ ^ 2 := by
  obtain ⟨hl, hu⟩ := angularKernel_bounds n e v hn
  refine abs_le.mpr ⟨?_, hu⟩
  have h : 0 ≤ ‖e‖ ^ 2 * ‖v‖ ^ 2 := by positivity
  nlinarith only [hl, h]

/-- The explicit fourth-derivative kernel, including the Newtonian constant. -/
def pressureKernel (e separation velocity : E) : ℝ :=
  angularKernel (‖separation‖⁻¹ • separation) e velocity /
    (4 * Real.pi * ‖separation‖ ^ 5)

theorem abs_pressureKernel_le (e separation velocity : E) (R : ℝ)
    (hR : 0 < R) (hsep : R ≤ ‖separation‖) :
    |pressureKernel e separation velocity| ≤
      (6 / (Real.pi * R ^ 5)) * ‖e‖ ^ 2 * ‖velocity‖ ^ 2 := by
  have hs : 0 < ‖separation‖ := hR.trans_le hsep
  have hn : ‖‖separation‖⁻¹ • separation‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hs.ne']
  have hnum := abs_angularKernel_le (‖separation‖⁻¹ • separation) e velocity hn
  have hden : 0 < 4 * Real.pi * ‖separation‖ ^ 5 := by positivity
  have hpow : R ^ 5 ≤ ‖separation‖ ^ 5 := pow_le_pow_left₀ hR.le hsep 5
  calc
    |pressureKernel e separation velocity| =
        |angularKernel (‖separation‖⁻¹ • separation) e velocity| /
          (4 * Real.pi * ‖separation‖ ^ 5) := by
      rw [pressureKernel, abs_div, abs_of_pos hden]
    _ ≤ (24 * ‖e‖ ^ 2 * ‖velocity‖ ^ 2) /
          (4 * Real.pi * ‖separation‖ ^ 5) := div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (24 * ‖e‖ ^ 2 * ‖velocity‖ ^ 2) / (4 * Real.pi * R ^ 5) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

/-- A separated stress distribution has an energy-paid directional response.
The measure may already be restricted to an exterior region. -/
theorem abs_integral_pressureKernel_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (e : E) (separation velocity : X → E) (R : ℝ)
    (hR : 0 < R) (hsep : ∀ᵐ y ∂μ, R ≤ ‖separation y‖)
    (henergy : Integrable (fun y ↦ ‖velocity y‖ ^ 2) μ)
    (hkernel : AEStronglyMeasurable (fun y ↦ pressureKernel e (separation y) (velocity y)) μ) :
    |∫ y, pressureKernel e (separation y) (velocity y) ∂μ| ≤
      (6 / (Real.pi * R ^ 5)) * ‖e‖ ^ 2 * ∫ y, ‖velocity y‖ ^ 2 ∂μ := by
  let C := (6 / (Real.pi * R ^ 5)) * ‖e‖ ^ 2
  have hb : ∀ᵐ y ∂μ, |pressureKernel e (separation y) (velocity y)| ≤
      C * ‖velocity y‖ ^ 2 := hsep.mono fun y hy ↦
    abs_pressureKernel_le e (separation y) (velocity y) R hR hy
  have hc := henergy.const_mul C
  have hi : Integrable (fun y ↦ pressureKernel e (separation y) (velocity y)) μ :=
    hc.mono' hkernel (by simpa only [Real.norm_eq_abs] using hb)
  calc
    |∫ y, pressureKernel e (separation y) (velocity y) ∂μ| ≤
        ∫ y, |pressureKernel e (separation y) (velocity y)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y, C * ‖velocity y‖ ^ 2 ∂μ := integral_mono_ae hi.abs hc hb
    _ = _ := by rw [integral_const_mul]

/-- The same fixed-radius allowance pays the entire sampled history. The
direction, separation and integration region may vary with time; no fixed
packet shape or orientation is assumed. The physical energy inequality
supplies `hbudget`. -/
theorem interval_pressure_history_le {X : Type*} [MeasurableSpace X]
    (μ : ℝ → Measure X) (e : ℝ → E) (separation velocity : ℝ → X → E)
    (R H E₀ : ℝ) (hR : 0 < R) (hH : 0 ≤ H)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) H, ‖e t‖ = 1)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) H, ∀ᵐ y ∂μ t, R ≤ ‖separation t y‖)
    (henergy : ∀ t ∈ Set.Icc (0 : ℝ) H, Integrable (fun y ↦ ‖velocity t y‖ ^ 2) (μ t))
    (hkernel : ∀ t ∈ Set.Icc (0 : ℝ) H,
      AEStronglyMeasurable (fun y ↦ pressureKernel (e t) (separation t y) (velocity t y)) (μ t))
    (hbudget : ∀ t ∈ Set.Icc (0 : ℝ) H, (∫ y, ‖velocity t y‖ ^ 2 ∂μ t) ≤ E₀)
    (htime : IntervalIntegrable
      (fun t ↦ |∫ y, pressureKernel (e t) (separation t y) (velocity t y) ∂μ t|) volume 0 H) :
    (∫ t in (0 : ℝ)..H,
      |∫ y, pressureKernel (e t) (separation t y) (velocity t y) ∂μ t|) ≤
        (6 * H / (Real.pi * R ^ 5)) * E₀ := by
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) H) :
      |∫ y, pressureKernel (e t) (separation t y) (velocity t y) ∂μ t| ≤
        (6 / (Real.pi * R ^ 5)) * E₀ := by
    have h := abs_integral_pressureKernel_le (μ t) (e t) (separation t) (velocity t) R
      hR (hsep t ht) (henergy t ht) (hkernel t ht)
    rw [he t ht, one_pow, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hbudget t ht) (by positivity))
  calc
    _ ≤ ∫ _ in (0 : ℝ)..H, (6 / (Real.pi * R ^ 5)) * E₀ :=
      intervalIntegral.integral_mono_on hH htime intervalIntegrable_const hb
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [sub_zero, smul_eq_mul]; ring

/-- Scalar joint energy for vorticity and its stretching vector. -/
def jointEnergy (τ : ℝ) (ω ζ : E) : ℝ := ‖ω‖ ^ 2 + τ ^ 2 * ‖ζ‖ ^ 2

omit [InnerProductSpace ℝ E] in
theorem jointEnergy_mixed (τ : ℝ) (ω ζ : E) :
    2 * τ * ‖ω‖ * ‖ζ‖ ≤ jointEnergy τ ω ζ := by
  have h := sq_nonneg (‖ω‖ - τ * ‖ζ‖)
  dsimp [jointEnergy]
  nlinarith only [h]

/-- The far operator is paid by `K`; no sign is imposed on near pressure
or on the viscous commutator. This is the algebra after the PDE product rule. -/
theorem joint_production_le (τ ν K nearWork viscousWork gradOmega gradZeta : ℝ)
    (ω ζ far : E) (hτ : 0 < τ) (hK : 0 ≤ K) (hfar : ‖far‖ ≤ K * ‖ω‖) :
    (2 * ⟪ω, ζ⟫ - 2 * τ ^ 2 * (⟪ζ, far⟫ + nearWork) -
        4 * ν * τ ^ 2 * viscousWork - 2 * ν * (gradOmega + τ ^ 2 * gradZeta)) +
      2 * ν * (gradOmega + τ ^ 2 * gradZeta) ≤
        (τ⁻¹ + τ * K) * jointEnergy τ ω ζ -
          2 * τ ^ 2 * nearWork - 4 * ν * τ ^ 2 * viscousWork := by
  have hm := jointEnergy_mixed τ ω ζ
  have hωζ : ⟪ω, ζ⟫ ≤ ‖ω‖ * ‖ζ‖ := real_inner_le_norm ω ζ
  have hz : -⟪ζ, far⟫ ≤ ‖ζ‖ * ‖far‖ := by
    exact (neg_le_abs _).trans (abs_real_inner_le_norm ζ far)
  have hf : ‖ζ‖ * ‖far‖ ≤ ‖ζ‖ * (K * ‖ω‖) :=
    mul_le_mul_of_nonneg_left hfar (norm_nonneg _)
  have hcross : 2 * ⟪ω, ζ⟫ ≤ τ⁻¹ * jointEnergy τ ω ζ := by
    calc
      2 * ⟪ω, ζ⟫ ≤ jointEnergy τ ω ζ / τ := by
        apply (le_div_iff₀ hτ).mpr
        nlinarith only [hm, mul_le_mul_of_nonneg_left hωζ hτ.le]
      _ = _ := by ring
  have hpressure : -2 * τ ^ 2 * ⟪ζ, far⟫ ≤ τ * K * jointEnergy τ ω ζ := by
    have h1 := mul_le_mul_of_nonneg_left (hz.trans hf) (by positivity : 0 ≤ 2 * τ ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hm (mul_nonneg hτ.le hK)
    nlinarith only [h1, h2]
  nlinarith only [hcross, hpressure]

end Mettapedia.FluidDynamics.NavierStokes.PressureBoundaryResponse
