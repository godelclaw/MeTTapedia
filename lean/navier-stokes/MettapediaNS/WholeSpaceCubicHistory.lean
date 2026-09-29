import MettapediaNS.WholeSpacePressureHistory

/-!
# A physical-time allowance for cubic transport flux

The cubic velocity moment is paid by actual kinetic loss plus a constant
depending on the initial energy and positive viscosity. The terminal
energy remains in the estimate, so successive time segments share one
allowance. This controls the separated cubic transport contribution to
the pressure-Hessian history through its explicit fifth-derivative kernel.

The stress-transport identity and kernel identification are analytic in
`labs/pressure_stress_transport.py`. Pressure--strain redistribution and
the material receiver terms are not bounded by this theorem. Interval
integrability is a technical hypothesis on a smooth solution prefix,
not a bound on its magnitude or an arbitrary-horizon continuation premise.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceCubicHistory

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerContinuousTimeIntegral EulerVolterraConvolution WholeSpaceViscousFlow WholeSpaceOrderEnergy
  WholeSpacePressureHistory

/-- The full spatial cubic velocity moment. -/
def cubicMass (A : SmoothL2Field Space) : ℝ := ∫ x, ‖A.field x‖ ^ 3

/-- A common envelope for cubic velocity flux and the canonical
pressure--velocity boundary flux. The latter identification uses the
analytic `L²` pressure multiplier bound, not proved in this module. -/
def transportSize (A : SmoothL2Field Space) : ℝ :=
  quarticEnergy 0 A * Real.sqrt (orderEnergy 0 A)

theorem cubicMass_integrable (A : SmoothL2Field Space) :
    Integrable (fun x ↦ ‖A.field x‖ ^ 3) := by
  have h6 := memLp_six A.field A.smooth A.memLp A.derivative.memLp
  have h := A.memLp.norm.integrable_mul (square_memLp A.memLp h6)
  convert h using 1
  funext x
  simp only [Pi.mul_apply]
  ring

theorem cubicMass_nonneg (A : SmoothL2Field Space) : 0 ≤ cubicMass A :=
  integral_nonneg (fun _ ↦ by positivity)

theorem cubicMass_le_quartic (A : SmoothL2Field Space) :
    cubicMass A ≤ quarticEnergy 0 A * Real.sqrt (orderEnergy 0 A) := by
  have h6 := memLp_six A.field A.smooth A.memLp A.derivative.memLp
  have hcs := NavierStokes.R3EnergyNorms.integral_mul_le A.memLp.norm
    (square_memLp A.memLp h6) (fun _ ↦ norm_nonneg _) (fun _ ↦ sq_nonneg _)
  rw [lpNorm_norm A.memLp.1, ← norm_four_sq A.memLp h6, field_lpNorm] at hcs
  have hleft : (∫ x, ‖A.field x‖ * ‖A.field x‖ ^ 2) = cubicMass A := by
    unfold cubicMass
    congr 1
    funext x
    ring
  rw [hleft] at hcs
  have hn := norm_le_sqrt_orderEnergy A (n := 0) Fin.elim0
  have hq := sq_lpNorm_four_le A (n := 0) Fin.elim0
  rw [wordField_zero] at hn hq
  calc
    _ ≤ ‖A.toLp‖ * lpNorm A.field 4 volume ^ 2 := hcs
    _ ≤ Real.sqrt (orderEnergy 0 A) * quarticEnergy 0 A :=
      mul_le_mul hn hq (sq_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem transportSize_pow_four_le (A : SmoothL2Field Space) :
    transportSize A ^ 4 ≤ 27 * sobolevReal ^ 6 *
      orderEnergy 0 A ^ 3 * orderEnergy 1 A ^ 3 := by
  have hq := quarticEnergy_pow_four_le 0 A
  norm_num only [pow_zero, one_mul, zero_add] at hq
  have h0 := orderEnergy_nonneg 0 A
  calc
    _ = quarticEnergy 0 A ^ 4 * orderEnergy 0 A ^ 2 := by
      unfold transportSize
      rw [mul_pow, sqrt_pow_four h0]
    _ ≤ (27 * sobolevReal ^ 6 * orderEnergy 0 A * orderEnergy 1 A ^ 3) *
        orderEnergy 0 A ^ 2 := mul_le_mul_of_nonneg_right hq (sq_nonneg _)
    _ = _ := by ring

theorem cubicMass_pow_four_le (A : SmoothL2Field Space) :
    cubicMass A ^ 4 ≤ 27 * sobolevReal ^ 6 *
      orderEnergy 0 A ^ 3 * orderEnergy 1 A ^ 3 := by
  exact (pow_le_pow_left₀ (cubicMass_nonneg A) (cubicMass_le_quartic A) 4).trans
    (transportSize_pow_four_le A)

/-- A finite rate allowance; no future norm enters its definition. -/
def allowance (ν E : ℝ) : ℝ := 27 * sobolevReal ^ 6 * E ^ 3 / (32 * ν ^ 3)

theorem transportSize_le_loss_add (A : SmoothL2Field Space) (ν E : ℝ)
    (hν : 0 < ν) (hE : orderEnergy 0 A ≤ E) :
    transportSize A ≤ 2 * ν * orderEnergy 1 A + allowance ν E := by
  have hEn : 0 ≤ E := (orderEnergy_nonneg 0 A).trans hE
  have he3 := pow_le_pow_left₀ (orderEnergy_nonneg 0 A) hE 3
  have hn : 0 ≤ transportSize A :=
    mul_nonneg (quarticEnergy_nonneg 0 A) (Real.sqrt_nonneg _)
  have h := absorb hn
    (show 0 ≤ 27 * sobolevReal ^ 6 by positivity) (pow_nonneg hEn 3)
    (orderEnergy_nonneg 1 A) (show 0 < 2 * ν by positivity) ?_
  · convert h using 1
    dsimp [allowance]
    ring
  · calc
      _ ≤ 27 * sobolevReal ^ 6 * orderEnergy 0 A ^ 3 * orderEnergy 1 A ^ 3 :=
        transportSize_pow_four_le A
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he3 (by positivity)) (pow_nonneg (orderEnergy_nonneg 1 A) 3)

theorem cubicMass_le_loss_add (A : SmoothL2Field Space) (ν E : ℝ)
    (hν : 0 < ν) (hE : orderEnergy 0 A ≤ E) :
    cubicMass A ≤ 2 * ν * orderEnergy 1 A + allowance ν E :=
  (cubicMass_le_quartic A).trans (transportSize_le_loss_add A ν E hν hE)

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- The cubic transport allowance is shared by the complete actual
unforced history, with terminal kinetic energy retained. -/
theorem cubic_history_with_remaining (U : NSEvolution ν T hT) (hν : 0 < ν)
    (t : Icc (0 : ℝ) T)
    (hi : IntervalIntegrable
      (fun r ↦ cubicMass (U.velocity (projIcc 0 T hT r))) volume 0 t) :
    (∫ r in (0 : ℝ)..t, cubicMass (U.velocity (projIcc 0 T hT r))) +
      orderEnergy 0 (U.velocity t) ≤
      orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩) +
        allowance ν (orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩)) * t := by
  let a := allowance ν (orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩))
  have hc := (extendPath_continuous T hT (kineticLossPath U)).intervalIntegrable
    (μ := volume) 0 (t : ℝ)
  have hb : (∫ r in (0 : ℝ)..t, cubicMass (U.velocity (projIcc 0 T hT r))) ≤
      realIntegral T hT (kineticLossPath U) t + a * t := by
    calc
      _ ≤ ∫ r in (0 : ℝ)..t, extendPath T hT (kineticLossPath U) r + a := by
        apply intervalIntegral.integral_mono_on t.property.1 hi (hc.add (intervalIntegrable_const))
        intro r _
        exact cubicMass_le_loss_add _ ν _ hν (U.orderEnergy_zero_le hν.le _)
      _ = _ := by
        rw [intervalIntegral.integral_add hc intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        change realIntegral T hT (kineticLossPath U) t + (t : ℝ) * a = _
        ring
  have he := kinetic_balance U t
  dsimp [a] at hb
  linarith

/-- An explicit cubic kernel response can move with the receiver and
orientation. Its uniform spatial bound is the only kernel hypothesis.
The fifth Newtonian-kernel calculation supplies it analytically for the
separated transport source. This does not cover pressure redistribution. -/
theorem cubic_response_le (A : SmoothL2Field Space) (K : ℝ)
    (f : Space → ℝ) (hm : AEStronglyMeasurable f volume)
    (hb : ∀ᵐ x ∂volume, |f x| ≤ K * ‖A.field x‖ ^ 3) :
    |∫ x, f x| ≤ K * cubicMass A := by
  have hc := (cubicMass_integrable A).const_mul K
  have hf := hc.mono' hm (by simpa only [Real.norm_eq_abs] using hb)
  calc
    _ ≤ ∫ x, |f x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, K * ‖A.field x‖ ^ 3 := integral_mono_ae hf.abs hc hb
    _ = _ := by rw [integral_const_mul]; rfl

/-- The same bound applies to a signed sampled cubic response over the
full history. Receiver motion changes the kernel, not this common budget. -/
theorem response_history_with_remaining (U : NSEvolution ν T hT) (hν : 0 < ν)
    (t : Icc (0 : ℝ) T) (K : ℝ) (hK : 0 ≤ K) (F : ℝ → ℝ)
    (hF : IntervalIntegrable (fun r ↦ |F r|) volume 0 t)
    (hb : ∀ r ∈ Icc (0 : ℝ) t,
      |F r| ≤ K * transportSize (U.velocity (projIcc 0 T hT r))) :
    (∫ r in (0 : ℝ)..t, |F r|) + K * orderEnergy 0 (U.velocity t) ≤
      K * (orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩) +
        allowance ν (orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩)) * t) := by
  let a := allowance ν (orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩))
  have hc := (extendPath_continuous T hT (kineticLossPath U)).intervalIntegrable
    (μ := volume) 0 (t : ℝ)
  have hm : (∫ r in (0 : ℝ)..t, |F r|) ≤
      K * (realIntegral T hT (kineticLossPath U) t + a * t) := by
    calc
      _ ≤ ∫ r in (0 : ℝ)..t, K * (extendPath T hT (kineticLossPath U) r + a) := by
        apply intervalIntegral.integral_mono_on t.property.1 hF
          ((hc.add intervalIntegrable_const).const_mul K)
        intro r hr
        exact (hb r hr).trans (mul_le_mul_of_nonneg_left
          (transportSize_le_loss_add _ ν _ hν (U.orderEnergy_zero_le hν.le _)) hK)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hc intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        change K * (realIntegral T hT (kineticLossPath U) t + (t : ℝ) * a) = _
        ring
  have he := kinetic_balance U t
  dsimp [a] at hm
  nlinarith [he]

/-- Endpoint certificate for the signed pressure transfer observed by
a positive tensor bounded by the identity. Here `a` is its kinetic
component, `d` its accumulated dissipation, and `C` the complete observer
transport/pressure-flux cost. The physical weighted-stress identification
is analytic in the companion lab, not an assumption that `C` is bounded. -/
theorem signed_redistribution_bounds (E₀ E a₀ a d D W C : ℝ)
    (ha : 0 ≤ a) (haE : a ≤ E) (hd : 0 ≤ d) (hdD : d ≤ D)
    (henergy : E + D = E₀) (hwork : W + C = a - a₀ + d) :
    -a₀ ≤ W + C ∧ W + C ≤ E₀ - a₀ := by
  constructor <;> linarith

/-- A constant global unit direction has zero observer cost. The signed
time-integrated transfer, with cancellations retained, is energy-bounded.
This says nothing about the integral of its absolute instantaneous work. -/
theorem fixed_direction_signed_abs (E₀ E a₀ a d D W : ℝ)
    (ha₀ : 0 ≤ a₀) (ha₀E : a₀ ≤ E₀) (ha : 0 ≤ a) (haE : a ≤ E)
    (hd : 0 ≤ d) (hdD : d ≤ D) (henergy : E + D = E₀)
    (hwork : W = a - a₀ + d) : |W| ≤ E₀ := by
  have hb := signed_redistribution_bounds E₀ E a₀ a d D W 0 ha haE hd hdD henergy
    (by simpa using hwork)
  apply abs_le.mpr
  constructor <;> linarith [hb.1, hb.2]

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceCubicHistory
