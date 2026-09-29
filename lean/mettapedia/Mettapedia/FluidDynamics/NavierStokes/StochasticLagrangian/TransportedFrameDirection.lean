import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TransportedFrameMetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Directional conversion for a transported-frame metric

Let `D = ∂t + u·∇ - νΔ`, `s = |ω|²`, and `q = ωᵀ M⁻¹ ω`.
The frame identity gives `Dq = -2ν F`, whereas the ordinary vorticity
identity gives `Ds = 2 stretch - 2ν G`, with `G = |∇ω|²`.
Where the denominator is positive, the quotient `κ = s/q` satisfies

`(D - 2ν ∇log q · ∇) κ = (2 stretch - 2ν G)/q + 2ν s F/q²`.

Thus loss of metric norm enters the conversion factor with a positive
sign. At the identity-initialized frame, `q=s`, `F=G`, and their spatial
gradients agree. The initial quotient rate is exactly `2 stretch/s`.
Replacing both `s` and `q` by `s+η` and `q+η`, with fixed `η>0`, gives
a smooth positive quotient even at vorticity zeros. It still starts at
one; its initial rate is `2 stretch/(s+η)`. A bound for any one fixed
positive regularizer already controls the physical norm.

There is also an exact scalar HJB change of variables. For `ℓ=log q`,
`Lq=D-2ν∇ℓ·∇`, and `R=Ψ-ℓ`,

`Lq R - ν|∇R|² = DΨ - ν|∇Ψ|² + 2ν F/q`.

Consequently this scalar renormalization cancels the geometric `F` term
from both sides of the proposed barrier inequality. It supplies no new
bound for its remaining physical stretching term.

This file proves the scalar algebra on supplied rates and gradient
pairings. The chain rules, construction of the fields and PDE comparison
are separate obligations. The companion exact lab checks independent
rational jets and a smooth periodic unforced initial-data example. Neither
that example nor this algebra refutes a full-state history reserve.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TransportedFrameDirection

open scoped RealInnerProductSpace

/-- Parabolic quotient rule for `s/q`. The last inputs are
`∇s·∇q` and `|∇q|²`, respectively. -/
def quotientRate (ν s q sRate qRate gradPair gradSq : ℝ) : ℝ :=
  sRate / q - s * qRate / q ^ 2 - 2 * ν * s * gradSq / q ^ 3 +
    2 * ν * gradPair / q ^ 2

/-- The drift correction `2ν ∇log q · ∇(s/q)`. -/
def quotientDrift (ν s q gradPair gradSq : ℝ) : ℝ :=
  2 * ν * gradPair / q ^ 2 - 2 * ν * s * gradSq / q ^ 3

theorem quotientRate_sub_drift (ν s q sRate qRate gradPair gradSq : ℝ) :
    quotientRate ν s q sRate qRate gradPair gradSq -
      quotientDrift ν s q gradPair gradSq = sRate / q - s * qRate / q ^ 2 := by
  unfold quotientRate quotientDrift
  ring

/-- The metric loss has a positive sign in the physical-to-metric ratio. -/
theorem unforced_quotientRate_sub_drift (ν s q stretch G F gradPair gradSq : ℝ) :
    quotientRate ν s q (2 * stretch - 2 * ν * G) (-2 * ν * F) gradPair gradSq -
      quotientDrift ν s q gradPair gradSq =
        (2 * stretch - 2 * ν * G) / q + 2 * ν * s * F / q ^ 2 := by
  rw [quotientRate_sub_drift]
  ring

theorem unforced_quotientRate_sub_drift_eq_reaction
    (ν s q stretch G F gradPair gradSq : ℝ) (hs : s ≠ 0) (hq : q ≠ 0) :
    quotientRate ν s q (2 * stretch - 2 * ν * G) (-2 * ν * F) gradPair gradSq -
      quotientDrift ν s q gradPair gradSq =
        2 * (s / q) * (stretch / s - ν * G / s + ν * F / q) := by
  rw [unforced_quotientRate_sub_drift]
  field_simp

/-- At `M=I` with zero spatial frame derivatives, the initial ratio is
constant and its rate is the ordinary directional stretching rate. -/
theorem initial_frame_quotientRate (ν s stretch G gradSq : ℝ) (hs : s ≠ 0) :
    quotientRate ν s s (2 * stretch - 2 * ν * G) (-2 * ν * G) gradSq gradSq =
      2 * stretch / s := by
  unfold quotientRate
  field_simp
  ring

/-- A fixed positive regularization is enough for physical comparison;
no limit as the regularizer tends to zero is required. -/
theorem physical_sq_le_of_regularized_ratio_le (s q η K C : ℝ)
    (hqpos : 0 < q + η) (hη : 0 ≤ η) (hK : 0 ≤ K) (hq : q ≤ C)
    (hr : (s + η) / (q + η) ≤ K) : s ≤ K * (C + η) := by
  have h := (div_le_iff₀ hqpos).mp hr
  have hc := mul_le_mul_of_nonneg_left (add_le_add_right hq η) hK
  linarith

/-- The rate-minus-quadratic-gradient expression after the change
`R=Ψ-log q`. Inputs encode `DΨ`, `|∇log q|²`, `|∇Ψ|²` and their pairing. -/
def gaugeHJB (ν q F psiRate logGradSq psiGradSq gradPair : ℝ) : ℝ :=
  (psiRate - (-2 * ν * F / q + ν * logGradSq) -
    2 * ν * (gradPair - logGradSq)) -
      ν * (psiGradSq - 2 * gradPair + logGradSq)

theorem gaugeHJB_eq (ν q F psiRate logGradSq psiGradSq gradPair : ℝ) :
    gaugeHJB ν q F psiRate logGradSq psiGradSq gradPair =
      psiRate - ν * psiGradSq + 2 * ν * F / q := by
  unfold gaugeHJB
  ring

/-- This particular scalar correction leaves exactly the ordinary
log-vorticity supersolution obligation. It does not control that term. -/
theorem gauge_barrier_iff
    (ν s q stretch G F psiRate logGradSq psiGradSq gradPair : ℝ) :
    (2 * stretch - 2 * ν * G) / s + 2 * ν * F / q ≤
        gaugeHJB ν q F psiRate logGradSq psiGradSq gradPair ↔
      (2 * stretch - 2 * ν * G) / s ≤ psiRate - ν * psiGradSq := by
  rw [gaugeHJB_eq]
  exact add_le_add_iff_right _

/-- The quadratic Hamiltonian for a diffusion with covariance `2ν I`. -/
def controlHamiltonian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ν : ℝ) (gradient control : E) : ℝ :=
  ⟪control, gradient⟫ - ‖control‖ ^ 2 / (4 * ν)

theorem controlHamiltonian_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ν : ℝ) (hν : ν ≠ 0) (gradient control : E) :
    controlHamiltonian ν gradient control =
      ν * ‖gradient‖ ^ 2 - ‖control - (2 * ν) • gradient‖ ^ 2 / (4 * ν) := by
  unfold controlHamiltonian
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  field_simp
  ring

theorem controlHamiltonian_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ν : ℝ) (hν : 0 < ν) (gradient control : E) :
    controlHamiltonian ν gradient control ≤ ν * ‖gradient‖ ^ 2 := by
  rw [controlHamiltonian_eq ν hν.ne']
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))

theorem controlHamiltonian_attained {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ν : ℝ) (hν : ν ≠ 0) (gradient : E) :
    controlHamiltonian ν gradient ((2 * ν) • gradient) = ν * ‖gradient‖ ^ 2 := by
  rw [controlHamiltonian_eq ν hν]
  simp

/-- Combining the logarithmic-reference drift with the maximizing
control eliminates the scalar frame normalization. This concerns the
auxiliary sampling drift, not an admissible change of the fluid velocity. -/
theorem optimal_sampling_drift {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ν : ℝ) (u logPhysicalGradient logMetricGradient : E) :
    (-u + (2 * ν) • logMetricGradient) +
        (2 * ν) • (logPhysicalGradient - logMetricGradient) =
      -u + (2 * ν) • logPhysicalGradient := by
  rw [smul_sub]
  abel

/-- The scalar initial jet of the companion periodic example: at its
symmetry point `s=4b²`, `stretch=4ab²`, and both gradient costs vanish.
Realization by the actual local NS evolution is analytic, not asserted here. -/
theorem symmetry_initial_rate (ν a b : ℝ) (hb : b ≠ 0) :
    quotientRate ν (4 * b ^ 2) (4 * b ^ 2) (2 * (4 * a * b ^ 2)) 0 0 0 =
      2 * a := by
  unfold quotientRate
  field_simp
  ring

theorem symmetry_regularized_initial_rate_pos (ν a b η : ℝ)
    (ha : 0 < a) (hb : b ≠ 0) (hη : 0 < η) :
    0 < quotientRate ν (4 * b ^ 2 + η) (4 * b ^ 2 + η)
      (2 * (4 * a * b ^ 2)) 0 0 0 := by
  have hb2 := sq_pos_of_ne_zero hb
  simp only [quotientRate, mul_zero, zero_div, sub_zero, add_zero]
  positivity

end Mettapedia.FluidDynamics.NavierStokes.TransportedFrameDirection
