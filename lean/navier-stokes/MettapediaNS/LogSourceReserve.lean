import MettapediaNS.FullEnergyParentReserve

/-!
# Full-energy payment of logarithmically weighted sources

The reserve `C ((H-t) + L²/(2ν)) E(t)` pays `C (E(t) + L² d(t))`
along the actual unforced whole-space energy law `E' = -2νd`.
The same reserve pays every compatible subinterval, including its endpoints.

The companion source/receiver calculation bounds the lifted axisymmetric
swirl source by this cost, using `log(1+x) ≤ x` and the angular part of
the physical gradient energy. That spatial identification, the heat kernel
duality and the transport remainder are analytic, not formalized here.
No bound on an evolving deformation receiver or global regularity is claimed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LogSourceReserve

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceOrderEnergy
  WholeSpaceViscousFlow

theorem logarithmic_weight_le (L r : ℝ) :
    1 + Real.log (1 + L ^ 2 / r ^ 2) ≤ 1 + L ^ 2 / r ^ 2 := by
  have hp : 0 < 1 + L ^ 2 / r ^ 2 := by positivity
  have h := Real.log_le_sub_one_of_pos hp
  linarith

def reserve (C ν h L E : ℝ) : ℝ := C * (h + L ^ 2 / (2 * ν)) * E

def loss (C ν h L E d : ℝ) : ℝ := C * (E + (2 * ν * h + L ^ 2) * d)

theorem reserve_nonneg (C ν h L E : ℝ) (hC : 0 ≤ C) (hν : 0 < ν)
    (hh : 0 ≤ h) (hE : 0 ≤ E) : 0 ≤ reserve C ν h L E := by
  unfold reserve
  positivity

theorem reserve_derivative (C ν H L t d : ℝ) (E : ℝ → ℝ) (hν : 0 < ν)
    (hE : HasDerivAt E (-2 * ν * d) t) :
    HasDerivAt (fun s ↦ reserve C ν (H - s) L (E s))
      (-loss C ν (H - t) L (E t) d) t := by
  have hh : HasDerivAt (fun s : ℝ ↦ H - s + L ^ 2 / (2 * ν)) (-1) t := by
    simpa using ((hasDerivAt_const t H).sub (hasDerivAt_id t)).add_const
      (L ^ 2 / (2 * ν))
  have hd := (hh.const_mul C).mul hE
  change HasDerivAt (fun s ↦ reserve C ν (H - s) L (E s)) _ t at hd
  apply hd.congr_deriv
  unfold loss
  field_simp [ne_of_gt hν]
  ring

theorem cost_paid (C ν h L E d : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hh : 0 ≤ h) (hd : 0 ≤ d) :
    -loss C ν h L E d + C * (E + L ^ 2 * d) ≤ 0 := by
  have hp : 0 ≤ 2 * C * ν * h * d := by positivity
  unfold loss
  nlinarith only [hp]

def energyReserve {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT)
    (C H L t : ℝ) : ℝ :=
  reserve C ν (H - t) L (extendPath T hT (U.orderEnergyPath 0) t)

theorem actual_reserve_derivative {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT)
    (C H L t : ℝ) (hν : 0 < ν) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (energyReserve U C H L)
      (-loss C ν (H - t) L (orderEnergy 0 (U.velocity ⟨t, ht.1.le, ht.2.le⟩))
        (orderEnergy 1 (U.velocity ⟨t, ht.1.le, ht.2.le⟩))) t := by
  let ti : Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
  have hd := (U.orderEnergy_hasDerivWithinAt 0 ti).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  rw [FullEnergyParentReserve.actual_kinetic_rate] at hd
  have heq : extendPath T hT (U.orderEnergyPath 0) t = orderEnergy 0 (U.velocity ti) := by
    simp [extendPath, NSEvolution.orderEnergyPath, projIcc_of_mem hT ti.property, ti]
  have h := reserve_derivative C ν H L t (orderEnergy 1 (U.velocity ti)) _ hν hd
  unfold energyReserve
  simpa only [heq, ti] using h

/-- Payment on any compatible subinterval; the original horizon and length
scale remain fixed instead of renewing the initial allowance. -/
theorem actual_interval_payment {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT)
    (C H L a b : ℝ) (hC : 0 ≤ C) (hν : 0 < ν)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (hH : b ≤ H) :
    (∫ s in a..b, C * (extendPath T hT (U.orderEnergyPath 0) s +
      L ^ 2 * extendPath T hT (U.orderEnergyPath 1) s)) ≤
      energyReserve U C H L a - energyReserve U C H L b := by
  let e := extendPath T hT (U.orderEnergyPath 0)
  let d := extendPath T hT (U.orderEnergyPath 1)
  let ρ : ℝ → ℝ := fun s ↦ -loss C ν (H - s) L (e s) (d s)
  have he : Continuous e := extendPath_continuous T hT (U.orderEnergyPath 0)
  have hd : Continuous d := extendPath_continuous T hT (U.orderEnergyPath 1)
  have hcρ : Continuous ρ := by dsimp [ρ, loss]; fun_prop
  have hcR : Continuous (energyReserve U C H L) := by
    change Continuous (fun s ↦ reserve C ν (H - s) L (e s))
    unfold reserve
    fun_prop
  have hder (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (energyReserve U C H L) (ρ s) s := by
    have hs0 : s ∈ Ioo (0 : ℝ) T := ⟨ha.trans_lt hs.1, hs.2.trans_le hb⟩
    have hdR := actual_reserve_derivative U C H L s hν hs0
    simpa only [ρ, e, d, extendPath, projIcc_of_mem hT (Ioo_subset_Icc_self hs0),
      NSEvolution.orderEnergyPath, ContinuousMap.coe_mk] using hdR
  have hcost : Continuous (fun s ↦ C * (e s + L ^ 2 * d s)) := by fun_prop
  have hpayment (s : ℝ) (hs : s ∈ Icc a b) :
      ρ s + C * (e s + L ^ 2 * d s) ≤ (0 : ℝ) := by
    exact cost_paid C ν (H - s) L (e s) (d s) hC hν.le
      (sub_nonneg.mpr (hs.2.trans hH))
      (orderEnergy_nonneg 1 (U.velocity (projIcc 0 T hT s)))
  have hi := PlanarParentReserve.interval_payment (energyReserve U C H L) ρ
    (fun s ↦ C * (e s + L ^ 2 * d s)) (fun _ ↦ 0) a b hab hcR.continuousOn hder
    (hcρ.intervalIntegrable a b) (hcost.intervalIntegrable a b)
    intervalIntegrable_const hpayment
  simpa only [intervalIntegral.integral_zero, add_zero, e, d] using hi

theorem actual_initial_allowance {ν T : ℝ} {hT : 0 ≤ T} (U : NSEvolution ν T hT)
    (C H L : ℝ) (hC : 0 ≤ C) (hν : 0 < ν) (hH : T ≤ H) :
    (∫ s in (0 : ℝ)..T, C * (extendPath T hT (U.orderEnergyPath 0) s +
      L ^ 2 * extendPath T hT (U.orderEnergyPath 1) s)) ≤
      reserve C ν H L (orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩)) := by
  have hi := actual_interval_payment U C H L 0 T hC hν le_rfl hT le_rfl hH
  have hE : 0 ≤ extendPath T hT (U.orderEnergyPath 0) T := by
    change 0 ≤ orderEnergy 0 (U.velocity (projIcc 0 T hT T))
    exact orderEnergy_nonneg _ _
  have hn : 0 ≤ energyReserve U C H L T := reserve_nonneg _ _ _ _ _ hC hν
    (sub_nonneg.mpr hH) hE
  have hz : energyReserve U C H L 0 =
      reserve C ν H L (orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩)) := by
    simp [energyReserve, extendPath, NSEvolution.orderEnergyPath]
  rw [hz] at hi
  linarith

end Mettapedia.FluidDynamics.NavierStokes.LogSourceReserve
