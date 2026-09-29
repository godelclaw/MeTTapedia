import MettapediaNS.WholeSpaceHistoryBridge
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureBoundaryResponse
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.AlignedPressureReserve
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoreEnvelope

/-!
# An energy-paid part of the pressure history

For the actual unforced whole-space evolution, the kinetic-energy loss
is exactly `2ν ∫ ‖∇u‖₂²`. The separated fourth Newtonian kernel applied
to `-2ν Σᵢ ∂ᵢu ⊗ ∂ᵢu` consequently has total directional response at most
`6 E₀ / (π R⁵)`, uniformly over moving receivers and unit directions.
The allowance is shared by the entire history, not renewed at a time seam.

This is the viscous product-rule source in the pressure-Hessian evolution.
Its identification there is analytic in the companion lab; the source here
uses the actual spatial derivative fields of `NSEvolution`. The nonlinear
transport commutator, pressure-velocity reaction, receiver-direction terms,
and near part are not bounded here. The unweighted bound uses a fixed
positive radius. The scale-weighted bound permits a changing positive
radius, retaining moving-cutoff derivatives as separate costs. Time
integrability of the sampled response is a technical hypothesis, not
a supplied bound on its size.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureHistory

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerVolterraConvolution
  EulerContinuousTimeIntegral WholeSpaceViscousFlow WholeSpaceOrderEnergy
  WholeSpaceHistoryBridge PressureBoundaryResponse

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- The actual kinetic loss rate, including its viscosity coefficient. -/
def kineticLossPath (U : NSEvolution ν T hT) : C(Icc (0 : ℝ) T, ℝ) :=
  (2 * ν) • U.orderEnergyPath 1

theorem kinetic_balance (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    orderEnergy 0 (U.velocity t) + realIntegral T hT (kineticLossPath U) t =
      orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩) := by
  have hp : productionPath U 0 = -(kineticLossPath U) := by
    ext r
    change orderProduction 0 (U.velocity r) (U.derivative r) =
      -(2 * ν * orderEnergy 1 (U.velocity r))
    rw [U.derivative_eq_navierStokesRhs, orderProduction_navierStokesRhs 0 ν _ _
      (U.velocity_divergence r) (U.solenoidal r) (U.gradient r)]
    simp only [transportCommutator_zero, inner_zero_left, Finset.sum_const_zero,
      mul_zero, zero_sub, zero_add]
  have hi := production_integral U 0 t
  rw [hp] at hi
  have hn : realIntegral T hT (-kineticLossPath U) t =
      -realIntegral T hT (kineticLossPath U) t := by
    simp only [realIntegral, extendPath, ContinuousMap.neg_apply,
      intervalIntegral.integral_neg]
  rw [hn] at hi
  linarith

theorem kinetic_loss_le_initial (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    realIntegral T hT (kineticLossPath U) t ≤
      orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩) := by
  have hb := kinetic_balance U t
  have hn := orderEnergy_nonneg 0 (U.velocity t)
  linarith

theorem orderEnergy_one_eq (A : SmoothL2Field Space) :
    orderEnergy 1 A = ∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, orderEnergy_succ]
  simp [wordField_zero]

/-- One separated directional response of an actual smooth field. -/
def separatedResponse (A : SmoothL2Field Space) (e x : Space) (R : ℝ) : ℝ :=
  ∫ y in {y : Space | R ≤ ‖x - y‖}, pressureKernel e (x - y) (A.field y)

theorem abs_separatedResponse_le (A : SmoothL2Field Space) (e x : Space)
    (R : ℝ) (hR : 0 < R) :
    |separatedResponse A e x R| ≤ (6 / (Real.pi * R ^ 5)) * ‖e‖ ^ 2 * ‖A.toLp‖ ^ 2 := by
  have hi : Integrable (fun y ↦ ‖A.field y‖ ^ 2) :=
    A.memLp.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hs : MeasurableSet {y : Space | R ≤ ‖x - y‖} :=
    isClosed_le continuous_const (continuous_const.sub continuous_id).norm |>.measurableSet
  have hm : Measurable (fun y ↦ pressureKernel e (x - y) (A.field y)) := by
    have hA : Measurable A.field := A.smooth.continuous.measurable
    unfold pressureKernel angularKernel
    fun_prop
  have hb := abs_integral_pressureKernel_le
    (volume.restrict {y : Space | R ≤ ‖x - y‖}) e (fun y ↦ x - y) A.field R hR
    (ae_restrict_mem hs) hi.restrict hm.aestronglyMeasurable
  have he : (∫ y in {y : Space | R ≤ ‖x - y‖}, ‖A.field y‖ ^ 2) ≤ ‖A.toLp‖ ^ 2 := by
    rw [← WholeSpaceOfficial.integral_norm_sq]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _)) hi
  exact hb.trans (mul_le_mul_of_nonneg_left he (by positivity))

/-- The actual derivative tensor is retained in every source component. -/
def viscousSource (ν : ℝ) (A : SmoothL2Field Space) (e x : Space) (R : ℝ) : ℝ :=
  -(2 * ν) * ∑ i : Fin 3, separatedResponse (A.directionalField (axis i)) e x R

theorem abs_viscousSource_le (hν : 0 ≤ ν) (A : SmoothL2Field Space) (e x : Space)
    (R : ℝ) (hR : 0 < R) (he : ‖e‖ = 1) :
    |viscousSource ν A e x R| ≤
      (6 / (Real.pi * R ^ 5)) * (2 * ν * orderEnergy 1 A) := by
  have hb (i : Fin 3) := abs_separatedResponse_le (A.directionalField (axis i)) e x R hR
  simp only [he, one_pow, mul_one] at hb
  rw [viscousSource, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * ν)]
  calc
    _ ≤ 2 * ν * ∑ i : Fin 3, |separatedResponse (A.directionalField (axis i)) e x R| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ 2 * ν * ∑ i : Fin 3,
        (6 / (Real.pi * R ^ 5)) * ‖(A.directionalField (axis i)).toLp‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hb i)) (by positivity)
    _ = _ := by rw [← Finset.mul_sum, orderEnergy_one_eq]; ring

/-- One initial-energy allowance pays all separated viscous pressure
renewal. The receiver and direction may depend on the complete history. -/
theorem viscous_history_le_initial (U : NSEvolution ν T hT) (hν : 0 ≤ ν)
    (e x : ℝ → Space) (R : ℝ) (hR : 0 < R) (t : Icc (0 : ℝ) T)
    (he : ∀ r ∈ Icc (0 : ℝ) t, ‖e r‖ = 1)
    (hi : IntervalIntegrable (fun r ↦
      |viscousSource ν (U.velocity (projIcc 0 T hT r)) (e r) (x r) R|) volume 0 t) :
    (∫ r in (0 : ℝ)..t,
      |viscousSource ν (U.velocity (projIcc 0 T hT r)) (e r) (x r) R|) ≤
        (6 / (Real.pi * R ^ 5)) * orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩) := by
  have hc := (extendPath_continuous T hT (kineticLossPath U)).intervalIntegrable
    (μ := volume) 0 (t : ℝ)
  calc
    _ ≤ ∫ r in (0 : ℝ)..t,
        (6 / (Real.pi * R ^ 5)) * extendPath T hT (kineticLossPath U) r := by
      apply intervalIntegral.integral_mono_on t.property.1 hi (hc.const_mul _)
      intro r hr
      exact abs_viscousSource_le hν _ (e r) (x r) R hR (he r hr)
    _ = (6 / (Real.pi * R ^ 5)) * realIntegral T hT (kineticLossPath U) t := by
      rw [intervalIntegral.integral_const_mul]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (kinetic_loss_le_initial U t) (by positivity)

/-- The fifth radius power removes the separation factor. This allows
the sampled radius to follow the actual evolving amplitude. It does not
discard derivatives of a moving cutoff in the full pressure equation. -/
theorem scaled_viscousSource_le (hν : 0 ≤ ν) (A : SmoothL2Field Space) (e x : Space)
    (R : ℝ) (hR : 0 < R) (he : ‖e‖ = 1) :
    R ^ 5 * |viscousSource ν A e x R| ≤ (6 / Real.pi) * (2 * ν * orderEnergy 1 A) := by
  have hb := mul_le_mul_of_nonneg_left (abs_viscousSource_le hν A e x R hR he)
    (by positivity : 0 ≤ R ^ 5)
  calc
    _ ≤ R ^ 5 * ((6 / (Real.pi * R ^ 5)) * (2 * ν * orderEnergy 1 A)) := hb
    _ = _ := by field_simp [hR.ne']

/-- One finite initial resource pays the scale-weighted source even
when the positive separation radius shrinks along the history. -/
theorem scaled_viscous_history_le_loss (U : NSEvolution ν T hT) (hν : 0 ≤ ν)
    (e x : ℝ → Space) (R : ℝ → ℝ) (t : Icc (0 : ℝ) T)
    (hR : ∀ r ∈ Icc (0 : ℝ) t, 0 < R r)
    (he : ∀ r ∈ Icc (0 : ℝ) t, ‖e r‖ = 1)
    (hi : IntervalIntegrable (fun r ↦ R r ^ 5 *
      |viscousSource ν (U.velocity (projIcc 0 T hT r)) (e r) (x r) (R r)|) volume 0 t) :
    (∫ r in (0 : ℝ)..t, R r ^ 5 *
      |viscousSource ν (U.velocity (projIcc 0 T hT r)) (e r) (x r) (R r)|) ≤
        (6 / Real.pi) * realIntegral T hT (kineticLossPath U) t := by
  have hc := (extendPath_continuous T hT (kineticLossPath U)).intervalIntegrable
    (μ := volume) 0 (t : ℝ)
  calc
    _ ≤ ∫ r in (0 : ℝ)..t,
        (6 / Real.pi) * extendPath T hT (kineticLossPath U) r := by
      apply intervalIntegral.integral_mono_on t.property.1 hi (hc.const_mul _)
      intro r hr
      exact scaled_viscousSource_le hν _ (e r) (x r) (R r) (hR r hr) (he r hr)
    _ = (6 / Real.pi) * realIntegral T hT (kineticLossPath U) t := by
      rw [intervalIntegral.integral_const_mul]; rfl

/-- The terminal kinetic energy remains available. Concatenating physical
segments spends this resource once and preserves the remaining reserve. -/
theorem scaled_history_with_remaining (U : NSEvolution ν T hT) (hν : 0 ≤ ν)
    (e x : ℝ → Space) (R : ℝ → ℝ) (t : Icc (0 : ℝ) T)
    (hR : ∀ r ∈ Icc (0 : ℝ) t, 0 < R r)
    (he : ∀ r ∈ Icc (0 : ℝ) t, ‖e r‖ = 1)
    (hi : IntervalIntegrable (fun r ↦ R r ^ 5 *
      |viscousSource ν (U.velocity (projIcc 0 T hT r)) (e r) (x r) (R r)|) volume 0 t) :
    (∫ r in (0 : ℝ)..t, R r ^ 5 *
      |viscousSource ν (U.velocity (projIcc 0 T hT r)) (e r) (x r) (R r)|) +
        (6 / Real.pi) * orderEnergy 0 (U.velocity t) ≤
        (6 / Real.pi) * orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩) := by
  have hs := scaled_viscous_history_le_loss U hν e x R t hR he hi
  have hb := kinetic_balance U t
  have hc := congrArg (fun z : ℝ ↦ (6 / Real.pi) * z) hb
  nlinarith only [hs, hc]

theorem scaled_viscous_history_le_initial (U : NSEvolution ν T hT) (hν : 0 ≤ ν)
    (e x : ℝ → Space) (R : ℝ → ℝ) (t : Icc (0 : ℝ) T)
    (hR : ∀ r ∈ Icc (0 : ℝ) t, 0 < R r)
    (he : ∀ r ∈ Icc (0 : ℝ) t, ‖e r‖ = 1)
    (hi : IntervalIntegrable (fun r ↦ R r ^ 5 *
      |viscousSource ν (U.velocity (projIcc 0 T hT r)) (e r) (x r) (R r)|) volume 0 t) :
    (∫ r in (0 : ℝ)..t, R r ^ 5 *
      |viscousSource ν (U.velocity (projIcc 0 T hT r)) (e r) (x r) (R r)|) ≤
        (6 / Real.pi) * orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩) := by
  exact (scaled_viscous_history_le_loss U hν e x R t hR he hi).trans
    (mul_le_mul_of_nonneg_left (kinetic_loss_le_initial U t) (by positivity))

/-- In a nonnegative regime of the joint reserve, choosing the radius
with `R⁵ |ω|² ≥ Λ` turns this pressure-slot work into an integrable
multiplicative coefficient. Other defects and positivity of a physical
pressure summary remain separate obligations. -/
theorem reserve_source_work_le (w σ h R Λ F : ℝ)
    (hw : 0 ≤ w) (hh : 0 ≤ h) (hR : 0 < R) (hΛ : 0 < Λ)
    (hscale : Λ ≤ R ^ 5 * w ^ 14) :
    |665 * w ^ 5 * F| ≤
      ((665 / (154 * Λ)) * (R ^ 5 * |F|)) * AlignedPressureReserve.reserve w σ h := by
  have hc := AlignedPressureReserve.coercive w σ h hw hh
  have hs := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 154 * w ^ 5)
  have hcR := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ R ^ 5)
  have hmain : 154 * Λ * w ^ 5 ≤ R ^ 5 * AlignedPressureReserve.reserve w σ h := by
    nlinarith only [hs, hcR]
  have hm := mul_le_mul_of_nonneg_left hmain (mul_nonneg (by norm_num : (0 : ℝ) ≤ 665)
    (abs_nonneg F))
  have hd : 665 * w ^ 5 * |F| ≤
      (665 * R ^ 5 * |F| * AlignedPressureReserve.reserve w σ h) / (154 * Λ) := by
    apply (le_div_iff₀ (by positivity : 0 < 154 * Λ)).mpr
    convert hm using 1 <;> ring
  calc
    _ = 665 * w ^ 5 * |F| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 665 * w ^ 5)]
    _ ≤ _ := hd
    _ = _ := by ring

/-- A concrete growth coefficient paid by the actual kinetic loss rate.
It supplies the energy correction `reserve * exp(c * kineticEnergy)`
for this channel alone, where `c = 1995 / (77πΛ)`. -/
theorem viscous_reserve_source_le (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (e x : Space) (w σ h R Λ : ℝ) (he : ‖e‖ = 1)
    (hw : 0 ≤ w) (hh : 0 ≤ h) (hR : 0 < R) (hΛ : 0 < Λ)
    (hscale : Λ ≤ R ^ 5 * w ^ 14) :
    |665 * w ^ 5 * viscousSource ν A e x R| ≤
      ((1995 / (77 * Real.pi * Λ)) * (2 * ν * orderEnergy 1 A)) *
        AlignedPressureReserve.reserve w σ h := by
  have hb := scaled_viscousSource_le hν A e x R hR he
  have hr := AlignedPressureReserve.reserve_nonneg w σ h hw hh
  calc
    _ ≤ ((665 / (154 * Λ)) * (R ^ 5 * |viscousSource ν A e x R|)) *
        AlignedPressureReserve.reserve w σ h :=
      reserve_source_work_le w σ h R Λ _ hw hh hR hΛ hscale
    _ ≤ ((665 / (154 * Λ)) * ((6 / Real.pi) * (2 * ν * orderEnergy 1 A))) *
        AlignedPressureReserve.reserve w σ h :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) hr
    _ = _ := by ring

/-- A quartic pressure-vorticity reserve with the displayed coercivity
pays the same separated source after the scale choice `Λ ≤ R⁵W`.
For the physical candidate `W=|ω|²`, its directional pressure work is
`2W F`. Coercivity must come from the actual pressure/history estimate. -/
theorem quartic_source_work_le (W J R Λ F : ℝ)
    (hW : 0 ≤ W) (hJ : (44/95) * W ^ 2 ≤ J)
    (hR : 0 < R) (hΛ : 0 < Λ) (hscale : Λ ≤ R ^ 5 * W) :
    |2 * W * F| ≤ ((95 / (22 * Λ)) * (R ^ 5 * |F|)) * J := by
  have hs := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 44 * W by positivity)
  have hc := mul_le_mul_of_nonneg_left hJ (show 0 ≤ R ^ 5 by positivity)
  have hmain : 44 * Λ * W ≤ 95 * R ^ 5 * J := by nlinarith only [hs, hc]
  have hm := mul_le_mul_of_nonneg_right hmain (abs_nonneg F)
  have hd : 2 * W * |F| ≤ (95 * R ^ 5 * |F| * J) / (22 * Λ) := by
    apply (le_div_iff₀ (show 0 < 22 * Λ by positivity)).mpr
    convert hm using 1 <;> ring
  calc
    _ = 2 * W * |F| := by
      rw [abs_mul, abs_of_nonneg (show 0 ≤ 2 * W by positivity)]
    _ ≤ _ := hd
    _ = _ := by ring

/-- The actual kinetic-loss coefficient is unchanged by the quartic
reweighting. This pays only the separated viscous pressure source. -/
theorem quartic_viscous_source_le (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (e x : Space) (W J R Λ : ℝ) (he : ‖e‖ = 1)
    (hW : 0 ≤ W) (hJ : (44/95) * W ^ 2 ≤ J)
    (hR : 0 < R) (hΛ : 0 < Λ) (hscale : Λ ≤ R ^ 5 * W) :
    |2 * W * viscousSource ν A e x R| ≤
      ((1995 / (77 * Real.pi * Λ)) * (2 * ν * orderEnergy 1 A)) * J := by
  have hb := scaled_viscousSource_le hν A e x R hR he
  have hJn : 0 ≤ J := le_trans (by positivity) hJ
  calc
    _ ≤ ((95 / (22 * Λ)) * (R ^ 5 * |viscousSource ν A e x R|)) * J :=
      quartic_source_work_le W J R Λ _ hW hJ hR hΛ hscale
    _ ≤ ((95 / (22 * Λ)) * ((6 / Real.pi) * (2 * ν * orderEnergy 1 A))) * J :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) hJn
    _ = _ := by ring

/-- A positive offset and quartic coercivity pay the weighted source at
a fixed radius, including at zero vorticity. No scale condition involving
`W` is needed. This is only the separated viscous pressure channel. -/
theorem coercive_viscous_source_le (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (e x : Space) (θ W Y R : ℝ) (he : ‖e‖ = 1)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hW : 0 ≤ W)
    (hY : 1 + (44/95) * W ^ 2 ≤ Y) (hR : 0 < R) :
    |θ * (2 * W * viscousSource ν A e x R)| ≤
      ((9 / (Real.pi * R ^ 5)) * (2 * ν * orderEnergy 1 A)) * Y := by
  have hb := abs_viscousSource_le hν A e x R hR he
  have hYn : 0 ≤ Y := by nlinarith [sq_nonneg W]
  calc
    _ ≤ (3/2) * |viscousSource ν A e x R| * Y :=
      PressureCoreEnvelope.weighted_source_le θ W Y _ hθ hθ1 hW hY
    _ ≤ (3/2) * ((6 / (Real.pi * R ^ 5)) * (2 * ν * orderEnergy 1 A)) * Y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) hYn
    _ = _ := by ring

/-- Instantiation for the smooth pressure/core reserve and its actual
pressure-branch weight. The moment identification with a smooth fluid
and the remaining production equation are stated in the analytic lab. -/
theorem reserve_viscous_source_le (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (e x : Space) (η δ Q W V Z N R : ℝ) (he : ‖e‖ = 1)
    (hη : 0 < η) (hδ : 0 < δ) (hQ : 0 ≤ Q) (hW : 0 ≤ W) (hZ : 0 ≤ Z)
    (hR : 0 < R) :
    |PressureCoreEnvelope.weight δ
        (PressureCoreEnvelope.pressure η W V N - PressureCoreEnvelope.core η Q W V Z) *
      (2 * W * viscousSource ν A e x R)| ≤
      ((9 / (Real.pi * R ^ 5)) * (2 * ν * orderEnergy 1 A)) *
        PressureCoreEnvelope.reserve η δ Q W V Z N := by
  have hw := PressureCoreEnvelope.weight_mem δ
    (PressureCoreEnvelope.pressure η W V N - PressureCoreEnvelope.core η Q W V Z) hδ
  exact coercive_viscous_source_le hν A e x _ W _ R he hw.1 hw.2 hW
    (PressureCoreEnvelope.reserve_coercive η δ Q W V Z N hη hQ hW hZ) hR

end Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureHistory
