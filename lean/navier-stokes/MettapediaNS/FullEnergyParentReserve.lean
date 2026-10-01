import MettapediaNS.PlanarParentReserve
import MettapediaNS.WholeSpacePressureHistory

/-!
# Full-energy payment of bounded parent-strain observations

The finite-horizon reserve `C sqrt((H-t) E / (2 nu))` pays an observation
bounded by `C sqrt(d)` when the complete kinetic energy satisfies
`E' = -2 nu d`. Internal transfers between observed and hidden fluid
cancel in that energy equation. The whole-space adapter uses the actual
unforced NS derivative, not an assumed energy ledger. A fixed positive
energy cushion handles the zero-energy state without a singular derivative.

The finite-band or smoothed-strain observer bound remains an analytic
identification in the companion lab. Its scale-dependent constant cannot
be omitted. The final scalar comparison removes paid low-strain work
from a full enstrophy balance while retaining the signed high-strain
production. No arbitrary-data continuation bound is supplied here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FullEnergyParentReserve

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceOrderEnergy
  WholeSpaceViscousFlow

def reserve (C ν h E : ℝ) : ℝ :=
  C / Real.sqrt (2 * ν) * Real.sqrt h * Real.sqrt E

def loss (C ν h E d : ℝ) : ℝ :=
  C * (E + 2 * ν * h * d) /
    (2 * Real.sqrt (2 * ν) * Real.sqrt h * Real.sqrt E)

theorem reserve_nonneg (C ν h E : ℝ) (hC : 0 ≤ C) : 0 ≤ reserve C ν h E := by
  unfold reserve
  positivity

theorem reserve_sq (C ν h E : ℝ) (hν : 0 < ν) (hh : 0 ≤ h) (hE : 0 ≤ E) :
    reserve C ν h E ^ 2 = C ^ 2 * h * E / (2 * ν) := by
  simp only [reserve, mul_pow, div_pow, Real.sq_sqrt hh, Real.sq_sqrt hE,
    Real.sq_sqrt (show 0 ≤ 2 * ν by positivity)]
  ring

/-- Bellman square completion. The dissipation control is a relaxation
of the energy equation, not a force applied to the fluid. -/
theorem bellman_gap (C ν h E d : ℝ) (hν : 0 < ν) (hh : 0 < h)
    (hE : 0 < E) (hd : 0 ≤ d) :
    loss C ν h E d - C * Real.sqrt d =
      C * (Real.sqrt E - Real.sqrt (2 * ν) * Real.sqrt h * Real.sqrt d) ^ 2 /
        (2 * Real.sqrt (2 * ν) * Real.sqrt h * Real.sqrt E) := by
  have hn : Real.sqrt (2 * ν) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have ht : Real.sqrt h ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hh)
  have he : Real.sqrt E ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hE)
  unfold loss
  field_simp
  ring_nf
  simp only [Real.sq_sqrt hh.le, Real.sq_sqrt hE.le, Real.sq_sqrt hd,
    Real.sq_sqrt (show 0 ≤ ν * 2 by positivity)]
  ring

theorem observation_paid (C ν h E d : ℝ) (hC : 0 ≤ C) (hν : 0 < ν)
    (hh : 0 < h) (hE : 0 < E) (hd : 0 ≤ d) :
    C * Real.sqrt d ≤ loss C ν h E d := by
  have hg := bellman_gap C ν h E d hν hh hE hd
  have hp : 0 ≤ C * (Real.sqrt E - Real.sqrt (2 * ν) * Real.sqrt h * Real.sqrt d) ^ 2 /
      (2 * Real.sqrt (2 * ν) * Real.sqrt h * Real.sqrt E) := by positivity
  linarith

theorem reserve_derivative (C ν H t d : ℝ) (E : ℝ → ℝ)
    (hν : 0 < ν) (ht : t < H) (hE : 0 < E t)
    (hE' : HasDerivAt E (-2 * ν * d) t) :
    HasDerivAt (fun s ↦ reserve C ν (H - s) (E s))
      (-loss C ν (H - t) (E t) d) t := by
  have hh : 0 < H - t := sub_pos.mpr ht
  have hd := (((((hasDerivAt_const t H).sub (hasDerivAt_id t)).sqrt
    (ne_of_gt hh)).const_mul (C / Real.sqrt (2 * ν))).mul
      (hE'.sqrt (ne_of_gt hE)))
  apply hd.congr_deriv
  dsimp [loss]
  have hn : Real.sqrt (2 * ν) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hs : Real.sqrt (H - t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hh)
  have he : Real.sqrt (E t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hE)
  field_simp
  ring_nf
  simp only [Real.sq_sqrt hh.le, Real.sq_sqrt hE.le]
  ring

/-- Increasing observational resolution spends an additional resource.
It cannot be hidden by resetting the finite-horizon reserve. -/
theorem moving_observation_derivative (ν H t d C' : ℝ) (C E : ℝ → ℝ)
    (hν : 0 < ν) (ht : t < H) (hE : 0 < E t)
    (hC' : HasDerivAt C C' t) (hE' : HasDerivAt E (-2 * ν * d) t) :
    HasDerivAt (fun s ↦ reserve (C s) ν (H - s) (E s))
      (-loss (C t) ν (H - t) (E t) d + C' * reserve 1 ν (H - t) (E t)) t := by
  have hd := hC'.mul (reserve_derivative 1 ν H t d E hν ht hE hE')
  have hf : (fun s ↦ C s * reserve 1 ν (H - s) (E s)) =
      (fun s ↦ reserve (C s) ν (H - s) (E s)) := by
    funext s
    unfold reserve
    ring
  change HasDerivAt (fun s ↦ C s * reserve 1 ν (H - s) (E s)) _ t at hd
  rw [hf] at hd
  apply hd.congr_deriv
  unfold loss
  ring

theorem moving_observation_payment (C C' ν h E d : ℝ) (hC : 0 ≤ C)
    (hν : 0 < ν) (hh : 0 < h) (hE : 0 < E) (hd : 0 ≤ d) :
    -loss C ν h E d + C' * reserve 1 ν h E + C * Real.sqrt d ≤
      C' * reserve 1 ν h E := by
  have hp := observation_paid C ν h E d hC hν hh hE hd
  linarith

/-- The exact complete kinetic-energy derivative of an actual evolution. -/
theorem actual_kinetic_rate {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT)
    (t : Icc (0 : ℝ) T) :
    orderProduction 0 (U.velocity t) (U.derivative t) =
      -2 * ν * orderEnergy 1 (U.velocity t) := by
  rw [U.derivative_eq_navierStokesRhs, orderProduction_navierStokesRhs 0 ν _ _
    (U.velocity_divergence t) (U.solenoidal t) (U.gradient t)]
  simp only [transportCommutator_zero, inner_zero_left, Finset.sum_const_zero,
    mul_zero, zero_sub, zero_add]
  ring

def energyReserve {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT)
    (C H ε : ℝ) (t : ℝ) : ℝ :=
  reserve C ν (H - t) (extendPath T hT (U.orderEnergyPath 0) t + ε)

theorem actual_reserve_derivative {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT)
    (C H ε t : ℝ) (hν : 0 < ν) (hε : 0 < ε) (ht : t ∈ Ioo (0 : ℝ) T)
    (hH : t < H) :
    HasDerivAt (energyReserve U C H ε)
      (-loss C ν (H - t) (orderEnergy 0 (U.velocity ⟨t, ht.1.le, ht.2.le⟩) + ε)
        (orderEnergy 1 (U.velocity ⟨t, ht.1.le, ht.2.le⟩))) t := by
  let ti : Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
  have hd := ((U.orderEnergy_hasDerivWithinAt 0 ti).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)).add_const ε
  rw [actual_kinetic_rate] at hd
  have heq : extendPath T hT (U.orderEnergyPath 0) t = orderEnergy 0 (U.velocity ti) := by
    simp [extendPath, NSEvolution.orderEnergyPath, projIcc_of_mem hT ti.property, ti]
  have hp : 0 < extendPath T hT (U.orderEnergyPath 0) t + ε := by
    rw [heq]
    exact add_pos_of_nonneg_of_pos (orderEnergy_nonneg _ _) hε
  have h := reserve_derivative C ν H t (orderEnergy 1 (U.velocity ti)) _ hν hH hp hd
  unfold energyReserve
  simpa only [heq, ti] using h

/-- Native whole-space payment of the dissipation-root observation.
The observer's spatial smoothing constant remains explicit. -/
theorem actual_observation_paid {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT)
    (C H ε t : ℝ) (hC : 0 ≤ C) (hν : 0 < ν) (hε : 0 < ε)
    (ht : t ∈ Ioo (0 : ℝ) T) (hH : t < H) :
    deriv (energyReserve U C H ε) t +
      C * Real.sqrt (orderEnergy 1 (U.velocity ⟨t, ht.1.le, ht.2.le⟩)) ≤ 0 := by
  rw [(actual_reserve_derivative U C H ε t hν hε ht hH).deriv]
  have h := observation_paid C ν (H - t)
    (orderEnergy 0 (U.velocity ⟨t, ht.1.le, ht.2.le⟩) + ε)
    (orderEnergy 1 (U.velocity ⟨t, ht.1.le, ht.2.le⟩)) hC hν (sub_pos.mpr hH)
    (add_pos_of_nonneg_of_pos (orderEnergy_nonneg _ _) hε) (orderEnergy_nonneg _ _)
  linarith

/-- Every compatible subinterval spends the same full-energy reserve.
Only its fixed observation constant, viscosity, horizon and positive
energy cushion occur; no future norm bound is assumed. -/
theorem actual_interval_payment {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT)
    (C H ε a b : ℝ) (hC : 0 ≤ C) (hν : 0 < ν) (hε : 0 < ε)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (hH : b < H) :
    (∫ s in a..b, C * Real.sqrt (extendPath T hT (U.orderEnergyPath 1) s)) ≤
      energyReserve U C H ε a - energyReserve U C H ε b := by
  let e : ℝ → ℝ := fun s ↦ extendPath T hT (U.orderEnergyPath 0) s + ε
  let d : ℝ → ℝ := extendPath T hT (U.orderEnergyPath 1)
  let ρ : ℝ → ℝ := fun s ↦ -loss C ν (H - s) (e s) (d s)
  have he : Continuous e := (extendPath_continuous T hT (U.orderEnergyPath 0)).add_const ε
  have hd : Continuous d := extendPath_continuous T hT (U.orderEnergyPath 1)
  have hep (s : ℝ) : 0 < e s :=
    add_pos_of_nonneg_of_pos (orderEnergy_nonneg 0 (U.velocity (projIcc 0 T hT s))) hε
  have hdp (s : ℝ) : 0 ≤ d s :=
    orderEnergy_nonneg 1 (U.velocity (projIcc 0 T hT s))
  have hcρ : ContinuousOn ρ (Icc a b) := by
    dsimp [ρ, loss]
    apply ContinuousOn.neg
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro s hs
      have hh : 0 < H - s := sub_pos.mpr (hs.2.trans_lt hH)
      have hps := hep s
      positivity
  have hcR : ContinuousOn (energyReserve U C H ε) (Icc a b) := by
    change ContinuousOn (fun s ↦ reserve C ν (H - s) (e s)) _
    unfold reserve
    fun_prop
  have hder (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (energyReserve U C H ε) (ρ s) s := by
    have hs0 : s ∈ Ioo (0 : ℝ) T := ⟨ha.trans_lt hs.1, hs.2.trans_le hb⟩
    have hdR := actual_reserve_derivative U C H ε s hν hε hs0 (hs.2.trans hH)
    simpa only [ρ, e, d, extendPath, projIcc_of_mem hT (Ioo_subset_Icc_self hs0),
      NSEvolution.orderEnergyPath, ContinuousMap.coe_mk] using hdR
  have hcost : Continuous (fun s ↦ C * Real.sqrt (d s)) := by fun_prop
  have hpayment (s : ℝ) (hs : s ∈ Icc a b) : ρ s + C * Real.sqrt (d s) ≤ (0 : ℝ) := by
    have hp := observation_paid C ν (H - s) (e s) (d s) hC hν
      (sub_pos.mpr (hs.2.trans_lt hH)) (hep s) (hdp s)
    dsimp [ρ]
    linarith
  have hi := PlanarParentReserve.interval_payment (energyReserve U C H ε) ρ
    (fun s ↦ C * Real.sqrt (d s)) (fun _ ↦ 0) a b hab hcR hder
    (hcρ.intervalIntegrable_of_Icc hab) (hcost.intervalIntegrable a b)
    intervalIntegrable_const hpayment
  simpa only [intervalIntegral.integral_zero, add_zero, d] using hi

theorem actual_initial_allowance {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT)
    (C H ε : ℝ) (hC : 0 ≤ C) (hν : 0 < ν) (hε : 0 < ε) (hH : T < H) :
    (∫ s in (0 : ℝ)..T, C * Real.sqrt (extendPath T hT (U.orderEnergyPath 1) s)) ≤
      reserve C ν H (orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩) + ε) := by
  have hi := actual_interval_payment U C H ε 0 T hC hν hε le_rfl hT le_rfl hH
  have hn : 0 ≤ energyReserve U C H ε T := reserve_nonneg _ _ _ _ hC
  have hz : energyReserve U C H ε 0 =
      reserve C ν H (orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩) + ε) := by
    simp [energyReserve, extendPath, NSEvolution.orderEnergyPath]
  rw [hz] at hi
  linarith

/-- Paying the low-strain observation leaves exactly the signed
high-strain production and the complete viscous loss. -/
theorem weighted_enstrophy_rate (ν r r' X X' L N D q : ℝ)
    (hX : 0 ≤ X) (hL : L ≤ q * X) (hr : r' + q ≤ 0)
    (hX' : X' = 2 * L + 2 * N - 2 * ν * D) :
    Real.exp (2 * r) * (X' + 2 * r' * X) ≤
      2 * Real.exp (2 * r) * N - 2 * ν * Real.exp (2 * r) * D := by
  have hp := mul_nonpos_of_nonpos_of_nonneg hr hX
  have hi : X' + 2 * r' * X ≤ 2 * N - 2 * ν * D := by rw [hX']; nlinarith
  have hm := mul_le_mul_of_nonneg_left hi (Real.exp_pos (2 * r)).le
  nlinarith only [hm]

end Mettapedia.FluidDynamics.NavierStokes.FullEnergyParentReserve
