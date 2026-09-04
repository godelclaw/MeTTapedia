import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ConstantinIyerRepresentation

/-!
# A nonzero exact solution of the transported-momentum system

The decaying shear at unit viscosity and unit frequency,

`u(t, x) = e^{−t} sin(x₁) e₀`,

together with the gauge potential

`W(t, x) = B(t) cos(2 x₁)`, `B(t) = (e^{−2t} − e^{−4t})/8`,

satisfies the averaged frame-transport equation for the momentum one-form
`μ = u♭ + dW`: the gauge absorbs the non-exact production `f f′` of the
self-transport term through the Riccati-type balance
`B′ = −4B + e^{−2t}/4`.  This exhibits a genuinely nonzero inhabitant of
`TransportedMomentumData` — with nonzero velocity, nonzero gauge, and
nonzero representation pressure — so the pushdown theorem
(`TransportedMomentumData.navierStokes_of_transportedMomentum`) is
instantiated on data where every hypothesis field carries content.

The instance is a single Fourier mode; it is an exact Navier–Stokes solution
(the classical decaying shear), and its momentum gauge is the classical
Weber-transform gauge of that flow.  No claim beyond this explicit family is
made.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped RealInnerProductSpace BigOperators

/-- Three-dimensional coordinate space. -/
local notation "R3" => EuclideanSpace ℝ (Fin 3)

namespace DecayingShear

/-- Streamwise direction of the shear. -/
def e0 : R3 := EuclideanSpace.single 0 1

/-- Wave vector of the shear (unit frequency along the second axis). -/
def K1 : R3 := EuclideanSpace.single 1 1

/-- Wave vector of the gauge mode (twice the shear frequency). -/
def K2 : R3 := (2 : ℝ) • (EuclideanSpace.single 1 1 : R3)

/-- Decaying amplitude `e^{−t}`. -/
def amp (t : ℝ) : ℝ := Real.exp (-t)

/-- Gauge amplitude `B(t) = (e^{−2t} − e^{−4t})/8`. -/
def gaugeAmp (t : ℝ) : ℝ := (Real.exp ((-2) * t) - Real.exp ((-4) * t)) / 8

/-- Time derivative of the gauge amplitude. -/
def gaugeAmpDot (t : ℝ) : ℝ :=
  (Real.exp ((-2) * t) * -2 - Real.exp ((-4) * t) * -4) / 8

/-- The amplitude solves `amp′ = −amp`. -/
theorem hasDerivAt_amp (t : ℝ) : HasDerivAt amp (-amp t) t := by
  have h := ((hasDerivAt_id t).neg).exp
  have hval : Real.exp (-t) * -1 = -amp t := by
    unfold amp
    ring
  exact hval ▸ h

/-- The gauge amplitude has derivative `gaugeAmpDot`. -/
theorem hasDerivAt_gaugeAmp (t : ℝ) :
    HasDerivAt gaugeAmp (gaugeAmpDot t) t := by
  have h2 : HasDerivAt (fun s : ℝ => Real.exp ((-2) * s))
      (Real.exp ((-2) * t) * -2) t := by
    have hlin : HasDerivAt (fun s : ℝ => (-2 : ℝ) * s) (-2) t := by
      simpa using (hasDerivAt_id t).const_mul (-2 : ℝ)
    exact hlin.exp
  have h4 : HasDerivAt (fun s : ℝ => Real.exp ((-4) * s))
      (Real.exp ((-4) * t) * -4) t := by
    have hlin : HasDerivAt (fun s : ℝ => (-4 : ℝ) * s) (-4) t := by
      simpa using (hasDerivAt_id t).const_mul (-4 : ℝ)
    exact hlin.exp
  exact (h2.sub h4).div_const 8

/-- The Riccati-type gauge balance: `B′ = −4B + amp²/4`, where
`amp² = e^{−2t}`. -/
theorem gaugeAmp_balance (t : ℝ) :
    gaugeAmpDot t = -4 * gaugeAmp t + amp t * amp t / 4 := by
  unfold gaugeAmpDot gaugeAmp amp
  have hexp : Real.exp (-t) * Real.exp (-t) = Real.exp ((-2) * t) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hexp]
  ring

/-- Basic wave-vector pairings. -/
theorem inner_K1_e0 : ⟪K1, e0⟫ = 0 := by
  unfold K1 e0
  simp [EuclideanSpace.inner_single_left]

theorem inner_K2_e0 : ⟪K2, e0⟫ = 0 := by
  unfold K2 e0
  rw [real_inner_smul_left]
  simp [EuclideanSpace.inner_single_left]

theorem inner_e0_K2 : ⟪e0, K2⟫ = 0 := by
  rw [real_inner_comm]
  exact inner_K2_e0

theorem inner_e0_e0 : ⟪e0, e0⟫ = 1 := by
  unfold e0
  simp

theorem inner_K1_K1 : ⟪K1, K1⟫ = 1 := by
  unfold K1
  simp

theorem inner_K2_K2 : ⟪K2, K2⟫ = 4 := by
  unfold K2
  rw [real_inner_smul_left, real_inner_smul_right]
  simp
  norm_num

/-- The gauge phase is twice the shear phase. -/
theorem inner_K2_eq_two_K1 (x : R3) : ⟪K2, x⟫ = 2 * ⟪K1, x⟫ := by
  unfold K2 K1
  rw [real_inner_smul_left]

/-- The velocity: decaying unit-frequency shear. -/
def velocity : ℝ → R3 → R3 := fun t =>
  profileMode (fun s => amp t * Real.sin s) K1 e0

/-- Its time derivative. -/
def velocityDot : ℝ → R3 → R3 := fun t =>
  profileMode (fun s => -amp t * Real.sin s) K1 e0

/-- The gauge potential `W(t, y) = B(t) cos(⟪K₂, y⟫)`. -/
def gauge : ℝ → R3 → ℝ := fun t y => gaugeAmp t * Real.cos ⟪K2, y⟫

/-- Its time derivative. -/
def gaugeDot : ℝ → R3 → ℝ := fun t y => gaugeAmpDot t * Real.cos ⟪K2, y⟫

/-- Its Laplacian. -/
def gaugeLap : ℝ → R3 → ℝ := fun t y => -4 * gaugeAmp t * Real.cos ⟪K2, y⟫

/-- The gauge gradient in closed form. -/
theorem gradField_gauge (t : ℝ) (x : R3) :
    gradField (gauge t) x = (gaugeAmp t * -Real.sin ⟪K2, x⟫) • K2 :=
  gradField_scalarProfile (hasDerivAt_amp_cos (gaugeAmp t)) K2 x

/-- The gauge gradient as a profile mode. -/
theorem gradField_gauge_eq_mode (t : ℝ) :
    gradField (gauge t) = profileMode (fun s => gaugeAmp t * -Real.sin s) K2 K2 := by
  funext x
  rw [gradField_gauge]
  rfl

/-- Smoothness of scalar trigonometric profiles. -/
theorem contDiff_scalarCosMode (n : ℕ) (c : ℝ) (K : R3) :
    ContDiff ℝ n (fun y : R3 => c * Real.cos ⟪K, y⟫) := by
  have hphase : ContDiff ℝ n (fun y : R3 => ⟪K, y⟫) := (innerSL ℝ K).contDiff
  exact contDiff_const.mul (Real.contDiff_cos.comp hphase)

theorem contDiff_scalarSinMode (n : ℕ) (c : ℝ) (K : R3) :
    ContDiff ℝ n (fun y : R3 => c * Real.sin ⟪K, y⟫) := by
  have hphase : ContDiff ℝ n (fun y : R3 => ⟪K, y⟫) := (innerSL ℝ K).contDiff
  exact contDiff_const.mul (Real.contDiff_sin.comp hphase)

theorem contDiff_scalarNegSinMode (n : ℕ) (c : ℝ) (K : R3) :
    ContDiff ℝ n (fun y : R3 => c * -Real.sin ⟪K, y⟫) := by
  have hphase : ContDiff ℝ n (fun y : R3 => ⟪K, y⟫) := (innerSL ℝ K).contDiff
  exact contDiff_const.mul ((Real.contDiff_sin.comp hphase).neg)

/-- Smoothness of the velocity. -/
theorem contDiff_velocity (t : ℝ) : ContDiff ℝ 2 (velocity t) := by
  unfold velocity profileMode
  exact (contDiff_scalarSinMode 2 (amp t) K1).smul contDiff_const

/-- The decaying shear with its Weber gauge is transported-momentum data:
a genuinely nonzero exact inhabitant. -/
def data : TransportedMomentumData where
  ν := 1
  u := velocity
  udot := velocityDot
  W := gauge
  Wdot := gaugeDot
  WLap := gaugeLap
  u_contDiff := contDiff_velocity
  W_contDiff := fun t => contDiff_scalarCosMode 3 (gaugeAmp t) K2
  Wdot_diff := fun t =>
    (contDiff_scalarCosMode 1 (gaugeAmpDot t) K2).differentiable (by norm_num)
  WLap_diff := fun t =>
    (contDiff_scalarCosMode 1 (-4 * gaugeAmp t) K2).differentiable (by norm_num)
  u_hasTimeDeriv := fun t x => by
    show HasDerivAt (fun s => (amp s * Real.sin ⟪K1, x⟫) • e0)
      ((-amp t * Real.sin ⟪K1, x⟫) • e0) t
    exact ((hasDerivAt_amp t).mul_const (Real.sin ⟪K1, x⟫)).smul_const e0
  gradW_hasTimeDeriv := fun t x => by
    have hfun : (fun s => gradField (gauge s) x) =
        fun s => (gaugeAmp s * -Real.sin ⟪K2, x⟫) • K2 := by
      funext s
      exact gradField_gauge s x
    rw [hfun]
    have htarget : gradField (gaugeDot t) x =
        (gaugeAmpDot t * -Real.sin ⟪K2, x⟫) • K2 :=
      gradField_scalarProfile (hasDerivAt_amp_cos (gaugeAmpDot t)) K2 x
    rw [htarget]
    exact ((hasDerivAt_gaugeAmp t).mul_const (-Real.sin ⟪K2, x⟫)).smul_const K2
  gradW_laplacian_exchange := fun t x => by
    rw [gradField_gauge_eq_mode t]
    rw [coordLaplacian_profileMode (hasDerivAt_amp_neg_sin (gaugeAmp t))
      (hasDerivAt_amp_neg_cos (gaugeAmp t)) x]
    have htarget : gradField (gaugeLap t) x =
        ((-4 * gaugeAmp t) * -Real.sin ⟪K2, x⟫) • K2 :=
      gradField_scalarProfile (hasDerivAt_amp_cos (-4 * gaugeAmp t)) K2 x
    rw [htarget, inner_K2_K2]
    match_scalars
    ring
  transport := fun t x => by
    -- Smoothness of the gauge gradient and of the momentum.
    have hgwC2 : ContDiff ℝ 2 (gradField (gauge t)) := by
      rw [gradField_gauge_eq_mode t]
      unfold profileMode
      exact (contDiff_scalarNegSinMode 2 (gaugeAmp t) K2).smul contDiff_const
    have hμC2 : ContDiff ℝ 2 (fun y => velocity t y + gradField (gauge t) y) :=
      (contDiff_velocity t).add hgwC2
    -- Pass from the frame sum to the Laplacian and split it.
    rw [normalizedFrameSecondSum_eq_coordLaplacian hμC2 x, one_smul,
      coordLaplacian_add (contDiff_velocity t) hgwC2]
    -- Laplacian of the velocity mode.
    have hlapu : coordLaplacian (velocity t) x =
        ((amp t * -Real.sin ⟪K1, x⟫) * ⟪K1, K1⟫) • e0 := by
      unfold velocity
      exact coordLaplacian_profileMode (hasDerivAt_amp_sin (amp t))
        (hasDerivAt_amp_cos (amp t)) x
    -- Laplacian of the gauge gradient.
    have hlapgw : coordLaplacian (gradField (gauge t)) x =
        ((gaugeAmp t * Real.sin ⟪K2, x⟫) * ⟪K2, K2⟫) • K2 := by
      rw [gradField_gauge_eq_mode t]
      exact coordLaplacian_profileMode (hasDerivAt_amp_neg_sin (gaugeAmp t))
        (hasDerivAt_amp_neg_cos (gaugeAmp t)) x
    rw [hlapu, hlapgw, inner_K1_K1, inner_K2_K2]
    -- Split the Lie derivative of the momentum.
    have hu_diff : DifferentiableAt ℝ (velocity t) x :=
      ((contDiff_velocity t).differentiable (by norm_num)).differentiableAt
    have hgw_diff : DifferentiableAt ℝ (gradField (gauge t)) x :=
      (hgwC2.differentiable (by norm_num)).differentiableAt
    rw [lieOneForm_add_right hu_diff hgw_diff]
    -- Directional derivatives along the streamwise direction vanish.
    have hfd_u_e0 : fderiv ℝ (velocity t) x e0 = 0 := by
      have h : (fun y => fderiv ℝ (velocity t) y e0) =
          profileMode (fun r => ⟪K1, e0⟫ * (amp t * Real.cos r)) K1 e0 :=
        fderiv_profileMode_eval (hasDerivAt_amp_sin (amp t)) e0
      have h' := congrFun h x
      rw [h']
      unfold profileMode
      rw [inner_K1_e0]
      simp
    have hfd_gw_e0 : fderiv ℝ (gradField (gauge t)) x e0 = 0 := by
      rw [gradField_gauge_eq_mode t]
      have h : (fun y => fderiv ℝ
          (profileMode (fun s => gaugeAmp t * -Real.sin s) K2 K2) y e0) =
          profileMode (fun r => ⟪K2, e0⟫ * (gaugeAmp t * -Real.cos r)) K2 K2 :=
        fderiv_profileMode_eval (hasDerivAt_amp_neg_sin (gaugeAmp t)) e0
      have h' := congrFun h x
      rw [h']
      unfold profileMode
      rw [inner_K2_e0]
      simp
    -- Streamwise pairings of the momenta.
    have hinner_u : ⟪e0, velocity t x⟫ = amp t * Real.sin ⟪K1, x⟫ := by
      unfold velocity profileMode
      rw [real_inner_smul_right, inner_e0_e0, mul_one]
    have hinner_gw : ⟪e0, gradField (gauge t) x⟫ = 0 := by
      rw [gradField_gauge]
      rw [real_inner_smul_right, inner_e0_K2, mul_zero]
    -- Transport of the velocity's own one-form.
    have hlie_u : lieOneForm (velocity t) (velocity t) x =
        ((amp t * Real.cos ⟪K1, x⟫) * (amp t * Real.sin ⟪K1, x⟫)) • K1 := by
      have happly : lieOneForm (velocity t) (velocity t) x =
          (amp t * Real.sin ⟪K1, x⟫) • fderiv ℝ (velocity t) x e0 +
            ((amp t * Real.cos ⟪K1, x⟫) * ⟪e0, velocity t x⟫) • K1 :=
        lieOneForm_profileMode_apply (hasDerivAt_amp_sin (amp t))
      rw [happly, hfd_u_e0, hinner_u, smul_zero, zero_add]
    -- Transport of the gauge gradient along the velocity.
    have hlie_gw : lieOneForm (velocity t) (gradField (gauge t)) x = 0 := by
      have happly : lieOneForm (velocity t) (gradField (gauge t)) x =
          (amp t * Real.sin ⟪K1, x⟫) • fderiv ℝ (gradField (gauge t)) x e0 +
            ((amp t * Real.cos ⟪K1, x⟫) * ⟪e0, gradField (gauge t) x⟫) • K1 :=
        lieOneForm_profileMode_apply (hasDerivAt_amp_sin (amp t))
      rw [happly, hfd_gw_e0, hinner_gw, smul_zero, zero_add, mul_zero,
        zero_smul]
    rw [hlie_u, hlie_gw, add_zero]
    -- The gauge-drift term.
    have hgdot : gradField (gaugeDot t) x =
        (gaugeAmpDot t * -Real.sin ⟪K2, x⟫) • K2 :=
      gradField_scalarProfile (hasDerivAt_amp_cos (gaugeAmpDot t)) K2 x
    rw [hgdot]
    -- The velocity drift, pointwise.
    have hvdot : velocityDot t x = (-amp t * Real.sin ⟪K1, x⟫) • e0 := rfl
    rw [hvdot]
    -- Reduce the double phase and close with the gauge balance.
    rw [inner_K2_eq_two_K1 x, Real.sin_two_mul, gaugeAmp_balance t]
    unfold K2 K1 e0
    match_scalars <;> ring

/-- The instance is genuinely nonzero: at time `0` and phase `π/2` the
velocity is the unit streamwise vector. -/
theorem velocity_ne_zero :
    velocity 0 ((Real.pi / 2) • (EuclideanSpace.single 1 1 : R3)) ≠ 0 := by
  have hval : velocity 0 ((Real.pi / 2) • (EuclideanSpace.single 1 1 : R3)) =
      e0 := by
    unfold velocity profileMode amp K1
    have hphase : ⟪(EuclideanSpace.single 1 1 : R3),
        (Real.pi / 2) • (EuclideanSpace.single 1 1 : R3)⟫ = Real.pi / 2 := by
      rw [real_inner_smul_right]
      simp
    rw [hphase]
    simp [Real.sin_pi_div_two]
  rw [hval]
  unfold e0
  intro hcontra
  have h0 := congrFun (congrArg WithLp.ofLp hcontra) 0
  simp at h0

/-- The pushdown theorem instantiated on the decaying shear: it satisfies
the Navier–Stokes equations with the explicit representation pressure. -/
theorem decayingShear_navierStokes (t : ℝ) (x : R3) :
    deriv (fun s => data.u s x) t + fderiv ℝ (data.u t) x (data.u t x) +
      gradField (data.pressure t) x =
    data.ν • coordLaplacian (data.u t) x :=
  data.navierStokes_of_transportedMomentum t x

end DecayingShear

end NavierStokes
end FluidDynamics
end Mettapedia
