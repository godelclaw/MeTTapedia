import MettapediaNS.FullEnergyParentReserve
import MettapediaNS.ShearFluctuationReserve
import Euler.OrdinaryRegularizedEquation
import Euler.OrdinaryEulerL2Stability

/-!
# Paying a fixed smooth parent's nonlinear feedback

Transport skew symmetry bounds the actual nonlinear source observed against
a fixed smooth test field by its gradient bound times full kinetic energy.
The square of that energy pays the source multiplied by enstrophy, including
the bounded exponential cotangent in the parent reserve.

The native history theorem uses an actual whole-space NSEvolution. It retains
pressure in the observed equation and eliminates it only for a solenoidal
test field. It does not control unresolved receiver stretching, growing
observation constants, or arbitrary-data regularity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceParentFeedback

open Set MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceViscousFlow
  WholeSpaceViscousEnergy WholeSpaceOrderEnergy

def source (u ψ : SmoothL2Field Space) : ℝ :=
  -⟪(advectionField u u).toLp, ψ.toLp⟫_ℝ

theorem advection_skew_pair (u ψ : SmoothL2Field Space)
    (hdiv : ∀ x, divergence u.field x = 0) :
    ⟪(advectionField u u).toLp, ψ.toLp⟫_ℝ =
      -⟪(advectionField u ψ).toLp, u.toLp⟫_ℝ := by
  have h := advection_inner_zero u (addField u ψ) hdiv
  rw [advection_add_right, toLp_addField, toLp_addField,
    inner_add_left, inner_add_right, inner_add_right,
    advection_inner_zero u u hdiv, advection_inner_zero u ψ hdiv] at h
  linarith

theorem source_le_energy (u ψ : SmoothL2Field Space) (K : ℝ)
    (hdiv : ∀ x, divergence u.field x = 0)
    (hK : ∀ x, ‖fderiv ℝ ψ.field x‖ ≤ K) :
    |source u ψ| ≤ K * ‖u.toLp‖^2 := by
  rw [source, advection_skew_pair u ψ hdiv, neg_neg]
  calc
    _ ≤ ‖(advectionField u ψ).toLp‖ * ‖u.toLp‖ := abs_real_inner_le_norm _ _
    _ ≤ (K * ‖u.toLp‖) * ‖u.toLp‖ :=
      mul_le_mul_of_nonneg_right (advection_norm_gradient u ψ K hK) (norm_nonneg _)
    _ = _ := by ring

theorem orderEnergy_zero (u : SmoothL2Field Space) :
    orderEnergy 0 u = ‖u.toLp‖^2 := by
  simp [orderEnergy, wordField_zero]

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- The observed source is part of the actual unforced equation, not an
independent input; solenoidal tests cancel the actual pressure force. -/
theorem actual_observed_rhs (U : NSEvolution ν T hT) (ψ : SmoothL2Field Space)
    (hψ : ψ.toLp ∈ solenoidalSpace) (t : Icc (0 : ℝ) T) :
    ⟪(U.derivative t).toLp, ψ.toLp⟫_ℝ =
      ν * ⟪(laplacianField (U.velocity t)).toLp, ψ.toLp⟫_ℝ +
        source (U.velocity t) ψ := by
  rw [U.derivative_toLp_expand, inner_add_left, inner_neg_left, inner_add_left,
    real_inner_smul_left, pressure_pairing_zero (U.gradient t) hψ]
  unfold source
  ring

def amplitudeCap (U : NSEvolution ν T hT) (ψ : SmoothL2Field Space) : ℝ :=
  ‖(U.velocity ⟨0, le_rfl, hT⟩).toLp‖ * ‖ψ.toLp‖

theorem actual_amplitude_le (U : NSEvolution ν T hT) (ψ : SmoothL2Field Space)
    (hν : 0 ≤ ν) (t : Icc (0 : ℝ) T) :
    |⟪(U.velocity t).toLp, ψ.toLp⟫_ℝ| ≤ amplitudeCap U ψ := by
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (U.l2_norm_le hν t) (norm_nonneg _))

def feedbackCost (U : NSEvolution ν T hT) (ψ : SmoothL2Field Space)
    (c : ℝ) (t : ℝ) : ℝ :=
  let u := U.velocity (projIcc 0 T hT t)
  c * Real.exp (c * |⟪u.toLp, ψ.toLp⟫_ℝ|) * |source u ψ| * orderEnergy 1 u

def coefficient (U : NSEvolution ν T hT) (ψ : SmoothL2Field Space)
    (c K : ℝ) : ℝ := c * K * Real.exp (c * amplitudeCap U ψ)

theorem actual_feedback_le (U : NSEvolution ν T hT) (ψ : SmoothL2Field Space)
    (c K : ℝ) (hν : 0 ≤ ν) (hc : 0 ≤ c)
    (hK : ∀ x, ‖fderiv ℝ ψ.field x‖ ≤ K) (t : ℝ) :
    feedbackCost U ψ c t ≤ coefficient U ψ c K *
      extendPath T hT (U.orderEnergyPath 0) t *
      extendPath T hT (U.orderEnergyPath 1) t := by
  let ti := projIcc 0 T hT t
  have hs := source_le_energy (U.velocity ti) ψ K (U.velocity_divergence ti) hK
  rw [← orderEnergy_zero] at hs
  have ha := actual_amplitude_le U ψ hν ti
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha hc)
  have hz := orderEnergy_nonneg 1 (U.velocity ti)
  have hE := orderEnergy_nonneg 0 (U.velocity ti)
  change c * Real.exp (c * |⟪(U.velocity ti).toLp, ψ.toLp⟫_ℝ|) *
      |source (U.velocity ti) ψ| * orderEnergy 1 (U.velocity ti) ≤
    coefficient U ψ c K * orderEnergy 0 (U.velocity ti) * orderEnergy 1 (U.velocity ti)
  calc
    _ ≤ c * Real.exp (c * amplitudeCap U ψ) *
        (K * orderEnergy 0 (U.velocity ti)) * orderEnergy 1 (U.velocity ti) := by gcongr
    _ = _ := by unfold coefficient; ring

def kineticReserve (C ν E : ℝ) : ℝ := C / (4 * ν) * E^2

theorem kineticReserve_nonneg (C ν E : ℝ) (hC : 0 ≤ C) (hν : 0 < ν) :
    0 ≤ kineticReserve C ν E := by unfold kineticReserve; positivity

theorem kineticReserve_derivative (C ν Z t : ℝ) (E : ℝ → ℝ) (hν : ν ≠ 0)
    (hE : HasDerivAt E (-2 * ν * Z) t) :
    HasDerivAt (fun s ↦ kineticReserve C ν (E s)) (-C * E t * Z) t := by
  have hd := (hE.pow 2).const_mul (C / (4 * ν))
  apply hd.congr_deriv
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

def energyReserve (U : NSEvolution ν T hT) (C : ℝ) (t : ℝ) : ℝ :=
  kineticReserve C ν (extendPath T hT (U.orderEnergyPath 0) t)

theorem actual_reserve_derivative (U : NSEvolution ν T hT) (C t : ℝ)
    (hν : 0 < ν) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (energyReserve U C)
      (-C * extendPath T hT (U.orderEnergyPath 0) t *
        extendPath T hT (U.orderEnergyPath 1) t) t := by
  let ti : Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
  have hd := (U.orderEnergy_hasDerivWithinAt 0 ti).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  rw [FullEnergyParentReserve.actual_kinetic_rate] at hd
  have heq : extendPath T hT (U.orderEnergyPath 1) t = orderEnergy 1 (U.velocity ti) := by
    simp [extendPath, NSEvolution.orderEnergyPath, projIcc_of_mem hT ti.property, ti]
  unfold energyReserve
  rw [heq]
  exact kineticReserve_derivative C ν (orderEnergy 1 (U.velocity ti)) t _ hν.ne' hd

/-- The entire weighted nonlinear feedback is paid from the original full
kinetic energy. Integrability is technical; no future size bound is assumed. -/
theorem actual_feedback_interval (U : NSEvolution ν T hT) (ψ : SmoothL2Field Space)
    (c K a b : ℝ) (hν : 0 < ν) (hc : 0 ≤ c)
    (hK : ∀ x, ‖fderiv ℝ ψ.field x‖ ≤ K)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hi : IntervalIntegrable (feedbackCost U ψ c) volume a b) :
    (∫ t in a..b, feedbackCost U ψ c t) +
        energyReserve U (coefficient U ψ c K) b ≤
      energyReserve U (coefficient U ψ c K) a := by
  let C := coefficient U ψ c K
  let e := extendPath T hT (U.orderEnergyPath 0)
  let z := extendPath T hT (U.orderEnergyPath 1)
  let ρ : ℝ → ℝ := fun t ↦ -C * e t * z t
  have he : Continuous e := extendPath_continuous T hT (U.orderEnergyPath 0)
  have hz : Continuous z := extendPath_continuous T hT (U.orderEnergyPath 1)
  have hρ : Continuous ρ := by dsimp [ρ]; fun_prop
  have hR : ContinuousOn (energyReserve U C) (Icc a b) := by
    change ContinuousOn (fun t ↦ kineticReserve C ν (e t)) _
    unfold kineticReserve
    fun_prop
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (energyReserve U C) (ρ t) t :=
    actual_reserve_derivative U C t hν ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩
  have hp (t : ℝ) (_ht : t ∈ Icc a b) : ρ t + feedbackCost U ψ c t ≤ 0 := by
    have h := actual_feedback_le U ψ c K hν.le hc hK t
    dsimp [ρ, C, e, z]
    linarith
  have hi' := PlanarParentReserve.interval_payment (energyReserve U C) ρ
    (feedbackCost U ψ c) (fun _ ↦ 0) a b hab hR hd
    (hρ.intervalIntegrable a b) hi intervalIntegrable_const hp
  simp only [intervalIntegral.integral_zero, add_zero] at hi'
  linarith

theorem actual_initial_allowance (U : NSEvolution ν T hT) (ψ : SmoothL2Field Space)
    (c K : ℝ) (hν : 0 < ν) (hc : 0 ≤ c) (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖fderiv ℝ ψ.field x‖ ≤ K)
    (hi : IntervalIntegrable (feedbackCost U ψ c) volume 0 T) :
    (∫ t in (0 : ℝ)..T, feedbackCost U ψ c t) ≤
      kineticReserve (coefficient U ψ c K) ν
        (orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩)) := by
  have hp := actual_feedback_interval U ψ c K 0 T hν hc hK le_rfl hT le_rfl hi
  have hC : 0 ≤ coefficient U ψ c K := by unfold coefficient; positivity
  have hn := kineticReserve_nonneg (coefficient U ψ c K) ν
    (extendPath T hT (U.orderEnergyPath 0) T) hC hν
  have heq : energyReserve U (coefficient U ψ c K) 0 =
      kineticReserve (coefficient U ψ c K) ν
        (orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩)) := by
    simp [energyReserve, extendPath, NSEvolution.orderEnergyPath]
  rw [heq] at hp
  change 0 ≤ energyReserve U (coefficient U ψ c K) T at hn
  linarith

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceParentFeedback
