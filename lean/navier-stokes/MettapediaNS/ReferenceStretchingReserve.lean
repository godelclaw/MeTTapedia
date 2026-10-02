import MettapediaNS.PlanarParentReserve

/-!
# Coupled mean and relative-energy payment for reference stretching

The companion analytic argument identifies `n` with a negative-Sobolev
observation of the actual perturbation (or its generated vertical mean),
`E` with its relative kinetic energy, and `D` with its gradient dissipation.
Its estimates have the form `n' ≤ κ n + c E` and
`E' ≤ a E - 2ν D`. Backward adjoint weights pay `j n + 6 L D`, which
dominates the mixed cubic stretching involving the known reference.

This module certifies the coupled reserve calculus, including explicit
source defects and interval composition. The negative-Sobolev estimates,
physical identification and actual absolutely-continuous norm paths remain
analytic. Pure perturbation self-stretching is not paid by this reserve.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ReferenceStretchingReserve

open Set MeasureTheory

def reserve (p r n E : ℝ) : ℝ := p * n + r * E

def rate (p r p' r' n E n' E' : ℝ) : ℝ :=
  p' * n + p * n' + r' * E + r * E'

theorem reserve_nonneg (p r n E : ℝ) (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hn : 0 ≤ n) (hE : 0 ≤ E) : 0 ≤ reserve p r n E := by
  exact add_nonneg (mul_nonneg hp hn) (mul_nonneg hr hE)

theorem reserve_derivative (p r n E : ℝ → ℝ) (p' r' n' E' t : ℝ)
    (hp : HasDerivAt p p' t) (hr : HasDerivAt r r' t)
    (hn : HasDerivAt n n' t) (hE : HasDerivAt E E' t) :
    HasDerivAt (fun s ↦ reserve (p s) (r s) (n s) (E s))
      (rate (p t) (r t) p' r' (n t) (E t) n' E') t := by
  have hd := (hp.mul hn).add (hr.mul hE)
  change HasDerivAt (fun s ↦ reserve (p s) (r s) (n s) (E s)) _ t at hd
  apply hd.congr_deriv
  unfold rate
  ring

/-- Source and energy defects remain visible. They are zero for the
unforced physical comparison; they may not be dropped for another model. -/
theorem payment_with_defects (p r p' r' n E n' E' κ c a j ν L D f w : ℝ)
    (hp : 0 ≤ p) (hr : 0 ≤ r) (hD : 0 ≤ D)
    (hp' : p' = -j - κ * p) (hr' : r' = -a * r - c * p)
    (hn' : n' ≤ κ * n + c * E + f)
    (hE' : E' ≤ a * E - 2 * ν * D + w)
    (hvisc : 6 * L ≤ 2 * ν * r) :
    rate p r p' r' n E n' E' + j * n + 6 * L * D ≤ p * f + r * w := by
  have hm := mul_le_mul_of_nonneg_left hn' hp
  have he := mul_le_mul_of_nonneg_left hE' hr
  have hd := mul_le_mul_of_nonneg_right hvisc hD
  rw [hp', hr']
  unfold rate
  nlinarith only [hm, he, hd]

theorem unforced_payment (p r p' r' n E n' E' κ c a j ν L D : ℝ)
    (hp : 0 ≤ p) (hr : 0 ≤ r) (hD : 0 ≤ D)
    (hp' : p' = -j - κ * p) (hr' : r' = -a * r - c * p)
    (hn' : n' ≤ κ * n + c * E) (hE' : E' ≤ a * E - 2 * ν * D)
    (hvisc : 6 * L ≤ 2 * ν * r) :
    rate p r p' r' n E n' E' + j * n + 6 * L * D ≤ 0 := by
  simpa using payment_with_defects p r p' r' n E n' E' κ c a j ν L D 0 0
    hp hr hD hp' hr' (by simpa using hn') (by simpa using hE') hvisc

/-- Any physically identified cost below the paid observation is paid too. -/
theorem observation_paid (p r p' r' n E n' E' j L D cost : ℝ)
    (hpaid : rate p r p' r' n E n' E' + j * n + 6 * L * D ≤ 0)
    (hcost : cost ≤ j * n + 6 * L * D) :
    rate p r p' r' n E n' E' + cost ≤ 0 := by
  linarith

/-- The generated-mean specialization has no original mean charge. -/
theorem initial_zero_mean (p r E : ℝ) : reserve p r 0 E = r * E := by
  simp [reserve]

theorem terminal_zero_mean_weight (r n E : ℝ) : reserve 0 r n E = r * E := by
  simp [reserve]

/-- The interval calculus is reused rather than recreated. Its classical
derivative hypotheses must be supplied; the PDE norm's a.e. passage remains
part of the separate analytic identification. -/
theorem interval_payment (R ρ cost : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hR : ContinuousOn R (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt R (ρ t) t)
    (hρ : IntervalIntegrable ρ volume a b)
    (hc : IntervalIntegrable cost volume a b)
    (hp : ∀ t ∈ Icc a b, ρ t + cost t ≤ 0) :
    (∫ t in a..b, cost t) ≤ R a - R b := by
  have h := PlanarParentReserve.interval_payment R ρ cost (fun _ ↦ 0) a b
    hab hR hd hρ hc intervalIntegrable_const hp
  simpa using h

/-- The same intermediate reserve is retained on both sides of a seam. -/
theorem seam_payment (R₀ R₁ R₂ c₁ c₂ : ℝ)
    (h₁ : c₁ ≤ R₀ - R₁) (h₂ : c₂ ≤ R₁ - R₂) :
    c₁ + c₂ ≤ R₀ - R₂ := by
  linarith

end Mettapedia.FluidDynamics.NavierStokes.ReferenceStretchingReserve
