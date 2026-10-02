import MettapediaNS.ReferenceStretchingReserve

/-!
# Energy compensation for the evolving planar mean

The companion analytic estimate bounds all mean-containing cubic stretching
by a fraction of second-gradient dissipation plus `β * M * Z`, where `M`
is the mean's gradient energy and `M ≤ Z` is exact projection orthogonality.
Here `E`, `Z`, `D` denote total kinetic, gradient and second-gradient energy.
The actual kinetic law is `E' = -2ν Z`. With `2νγ = β`, multiplying by
`exp (γ E)` pays the mean coefficient from the same decreasing kinetic stock.

The remaining fluctuation self-stretching is the explicit input `g`.
Its reserve `R` is a hypothesis, not constructed here. The scalar calculus
does not certify the periodic anisotropic estimate, the projection identities
or arbitrary-data global regularity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GeneratedMeanEnstrophy

def reserve (γ E Z R : ℝ) : ℝ := Real.exp (γ * E) * (Z + R)

def rate (γ E Z R E' Z' R' : ℝ) : ℝ :=
  Real.exp (γ * E) * (Z' + R' + γ * E' * (Z + R))

theorem reserve_nonneg (γ E Z R : ℝ) (hZ : 0 ≤ Z) (hR : 0 ≤ R) :
    0 ≤ reserve γ E Z R := by
  exact mul_nonneg (Real.exp_pos _).le (add_nonneg hZ hR)

theorem reserve_derivative (γ t : ℝ) (E Z R : ℝ → ℝ) (E' Z' R' : ℝ)
    (hE : HasDerivAt E E' t) (hZ : HasDerivAt Z Z' t)
    (hR : HasDerivAt R R' t) :
    HasDerivAt (fun s ↦ reserve γ (E s) (Z s) (R s))
      (rate γ (E t) (Z t) (R t) E' Z' R') t := by
  have hd := ((hE.const_mul γ).exp).mul (hZ.add hR)
  change HasDerivAt (fun s ↦ reserve γ (E s) (Z s) (R s)) _ t at hd
  apply hd.congr_deriv
  unfold rate
  simp only [Pi.add_apply]
  ring

/-- The self-stretching reserve is still an open physical obligation. Its signed
input is the actual fluctuation stretching, with a fixed viscous share. -/
theorem compensated_payment (ν β γ E Z R M D g E' Z' R' : ℝ)
    (hβ : 0 ≤ β) (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hM : M ≤ Z)
    (hprice : 2 * ν * γ = β)
    (hE' : E' = -2 * ν * Z)
    (hZ' : Z' ≤ 2 * g - (3 / 2 : ℝ) * ν * D + β * M * Z)
    (hR' : R' = -2 * g + ν / 2 * D) :
    rate γ E Z R E' Z' R' + ν * Real.exp (γ * E) * D ≤ 0 := by
  have hm := mul_nonneg (mul_nonneg hβ (sub_nonneg.mpr hM)) hZ
  have hr := mul_nonneg (mul_nonneg hβ hZ) hR
  have heq : γ * E' * (Z + R) = -β * Z * (Z + R) := by
    rw [hE', ← hprice]
    ring
  have hi : Z' + R' + γ * E' * (Z + R) + ν * D ≤ 0 := by
    rw [heq, hR']
    nlinarith only [hZ', hm, hr]
  have hp := mul_le_mul_of_nonneg_left hi (Real.exp_pos (γ * E)).le
  unfold rate
  nlinarith only [hp]

theorem pricing_identity (ν C : ℝ) (hν : ν ≠ 0) :
    2 * ν * (C ^ 2 / (4 * ν ^ 2)) = C ^ 2 / (2 * ν) := by
  field_simp
  ring

/-- A nonnegative current kinetic stock makes the compensated quantity
dominate the actual gradient energy. -/
theorem enstrophy_le_reserve (γ E Z R : ℝ)
    (hγ : 0 ≤ γ) (hE : 0 ≤ E) (hZ : 0 ≤ Z) (hR : 0 ≤ R) :
    Z ≤ reserve γ E Z R := by
  have he := Real.one_le_exp (mul_nonneg hγ hE)
  unfold reserve
  nlinarith [mul_nonneg (sub_nonneg.mpr he) (add_nonneg hZ hR)]

/-- Once interval integration supplies nonincrease of this same reserve,
the original energy and the original self-stretching allowance give the
bound. Neither allowance is restarted at an intermediate endpoint. -/
theorem initial_allowance (γ E Z R E₀ Z₀ K : ℝ)
    (hγ : 0 ≤ γ) (hE : 0 ≤ E) (hZ : 0 ≤ Z) (hR : 0 ≤ R)
    (hpaid : reserve γ E Z R ≤ reserve γ E₀ Z₀ K) :
    Z ≤ Real.exp (γ * E₀) * (Z₀ + K) :=
  (enstrophy_le_reserve γ E Z R hγ hE hZ hR).trans hpaid

end Mettapedia.FluidDynamics.NavierStokes.GeneratedMeanEnstrophy
