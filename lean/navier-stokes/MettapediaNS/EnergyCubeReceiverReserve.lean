import MettapediaNS.WholeSpaceParentFeedback

/-!
# Energy-cube payment for a controlled receiver

The companion periodic calculation bounds the complete source-square storage
rate by `receiverBound`. The scalar estimates below pay that bound when the
receiver is small in H3 and an observed parent supplies a lower energy bound.
The Sobolev identification and construction of the parent-refeeding history
remain analytic. These are not arbitrary-data regularity hypotheses proved here.

The whole-space adapter derives the energy-cube rate from an actual unforced
`NSEvolution`. The interval theorem uses one reserve through every seam.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.EnergyCubeReceiverReserve

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceOrderEnergy
  WholeSpaceViscousFlow

def coefficient : ℝ := 1 / 100000000

def reserve (ν E : ℝ) : ℝ := coefficient * E ^ 3 / ν ^ 4

def loss (ν E Z : ℝ) : ℝ := 6 * coefficient * E ^ 2 * Z / ν ^ 3

def receiverBound (C B W ν : ℝ) : ℝ :=
  3 * C * B * W ^ 2 * (1 + C * W / ν) ^ 2

theorem reserve_nonneg (ν E : ℝ) (hE : 0 ≤ E) : 0 ≤ reserve ν E := by
  unfold reserve coefficient
  positivity

theorem reserve_derivative (ν Z t : ℝ) (E : ℝ → ℝ) (hν : ν ≠ 0)
    (hE : HasDerivAt E (-2 * ν * Z) t) :
    HasDerivAt (fun s ↦ reserve ν (E s)) (-loss ν (E t) Z) t := by
  have hd := ((hE.pow 3).const_mul coefficient).div_const (ν ^ 4)
  apply hd.congr_deriv
  simp only [Nat.cast_ofNat, Nat.reduceSub]
  unfold loss
  field_simp
  ring

theorem receiver_bound (C B W ν A : ℝ) (hC : 1 ≤ C) (_hB : 0 ≤ B)
    (hBA : B ≤ 5 * A) (hW : 0 ≤ W) (hν : 0 < ν) (hA : 0 ≤ A)
    (hsmall : C * W ≤ ν) : receiverBound C B W ν ≤ 60 * A * ν ^ 2 := by
  have hC0 : 0 ≤ C := by linarith
  have hr0 : 0 ≤ C * W / ν := by positivity
  have hr1 : C * W / ν ≤ 1 := (div_le_one hν).mpr hsmall
  have hf : (1 + C * W / ν) ^ 2 ≤ (2 : ℝ) ^ 2 := by gcongr; linarith
  have hCW : C * W ^ 2 ≤ ν ^ 2 := by
    calc
      _ ≤ (C * W) ^ 2 := by
        have hcc : C ≤ C ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hcc (sq_nonneg W)]
      _ ≤ ν ^ 2 := by gcongr
  calc
    receiverBound C B W ν ≤ 3 * C * (5 * A) * W ^ 2 * 4 := by
      unfold receiverBound
      norm_num at hf
      gcongr
    _ = 60 * A * (C * W ^ 2) := by ring
    _ ≤ 60 * A * ν ^ 2 := by gcongr

theorem dominant_parent_payment (ν A E Z : ℝ) (hν : 0 < ν)
    (hscale : 256 * ν ≤ A) (hE : A ^ 2 / 9 ≤ E) (hZ : A ^ 2 / 9 ≤ Z) :
    60 * A * ν ^ 2 ≤ loss ν E Z := by
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hscale
  have hE0 : 0 ≤ E := (by positivity : 0 ≤ A ^ 2 / 9).trans hE
  have hZ0 : 0 ≤ Z := (by positivity : 0 ≤ A ^ 2 / 9).trans hZ
  have hpow : (256 * ν) ^ 5 ≤ A ^ 5 := by gcongr
  have hbase : 60 * ν ^ 5 ≤ (2 * coefficient / 243) * A ^ 5 := by
    calc
      _ ≤ (2 * coefficient / 243) * (256 * ν) ^ 5 := by
        unfold coefficient
        nlinarith [pow_nonneg hν.le 5]
      _ ≤ _ := by gcongr; norm_num [coefficient]
  calc
    60 * A * ν ^ 2 ≤ (2 * coefficient / 243) * A ^ 6 / ν ^ 3 := by
      apply (le_div_iff₀ (pow_pos hν 3)).mpr
      convert mul_le_mul_of_nonneg_left hbase hA.le using 1 <;> ring
    _ = 6 * coefficient * (A ^ 2 / 9) ^ 2 * (A ^ 2 / 9) / ν ^ 3 := by ring
    _ ≤ loss ν E Z := by
      unfold loss coefficient
      gcongr

/-- The named physical consumer has `B = ||u||H3`, `W = ||Pi u||H3`,
and energy/enstrophy lower bounds from the retained parent observation. -/
theorem receiver_paid (C B W ν A E Z : ℝ) (hC : 1 ≤ C) (hB : 0 ≤ B)
    (hBA : B ≤ 5 * A) (hW : 0 ≤ W) (hν : 0 < ν) (hsmall : C * W ≤ ν)
    (hscale : 256 * ν ≤ A) (hE : A ^ 2 / 9 ≤ E) (hZ : A ^ 2 / 9 ≤ Z) :
    receiverBound C B W ν ≤ loss ν E Z := by
  have hA : 0 ≤ A := (by positivity : (0 : ℝ) ≤ 256 * ν).trans hscale
  exact (receiver_bound C B W ν A hC hB hBA hW hν hA hsmall).trans
    (dominant_parent_payment ν A E Z hν hscale hE hZ)

/-- The analytic heat bounds give this explicit initial allowance. -/
theorem heat_allowance_bound (C W ν : ℝ) (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hν : 0 < ν) (hsmall : C * W ≤ ν) :
    W ^ 2 / 2 + 2 * C * W ^ 3 / (3 * ν) + C ^ 2 * W ^ 4 / (4 * ν ^ 2) ≤
      (17 / 12 : ℝ) * W ^ 2 := by
  have hr0 : 0 ≤ C * W / ν := by positivity
  have hr1 : C * W / ν ≤ 1 := (div_le_one hν).mpr hsmall
  have hr2 : (C * W / ν) ^ 2 ≤ (1 : ℝ) ^ 2 := by gcongr
  have hc : (1 / 2 : ℝ) + (2 / 3 : ℝ) * (C * W / ν) +
      (1 / 4 : ℝ) * (C * W / ν) ^ 2 ≤ 17 / 12 := by nlinarith
  calc
    _ = W ^ 2 * ((1 / 2 : ℝ) + (2 / 3 : ℝ) * (C * W / ν) +
        (1 / 4 : ℝ) * (C * W / ν) ^ 2) := by field_simp
    _ ≤ W ^ 2 * (17 / 12) := mul_le_mul_of_nonneg_left hc (sq_nonneg W)
    _ = _ := by ring

/-- The remaining geometric storage may vary. Its complete signed rate
must be bounded by the energy-cube loss on the entire physical interval. -/
theorem interval_payment (ν a b : ℝ) (V E Z ρ cost : ℝ → ℝ)
    (hν : 0 < ν) (hab : a ≤ b)
    (hV : Continuous V) (hE : Continuous E) (hZ : Continuous Z)
    (hρ : Continuous ρ) (hc : Continuous cost)
    (hdV : ∀ t ∈ Ioo a b, HasDerivAt V (ρ t) t)
    (hdE : ∀ t ∈ Ioo a b, HasDerivAt E (-2 * ν * Z t) t)
    (hpay : ∀ t ∈ Icc a b, ρ t + cost t ≤ loss ν (E t) (Z t)) :
    (∫ t in a..b, cost t) + (V b + reserve ν (E b)) ≤
      V a + reserve ν (E a) := by
  let J : ℝ → ℝ := fun t ↦ V t + reserve ν (E t)
  let rate : ℝ → ℝ := fun t ↦ ρ t - loss ν (E t) (Z t)
  have hJ : Continuous J := by dsimp [J, reserve]; fun_prop
  have hr : Continuous rate := by dsimp [rate, loss]; fun_prop
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt J (rate t) t := by
    exact (hdV t ht).add (reserve_derivative ν (Z t) t E hν.ne' (hdE t ht))
  have hp (t : ℝ) (ht : t ∈ Icc a b) : rate t + cost t ≤ 0 := by
    have := hpay t ht
    dsimp [rate]
    linarith
  have hi := PlanarParentReserve.interval_payment J rate cost (fun _ ↦ 0) a b hab
    hJ.continuousOn hd (hr.intervalIntegrable a b) (hc.intervalIntegrable a b)
    intervalIntegrable_const hp
  simp only [intervalIntegral.integral_zero, add_zero] at hi
  dsimp [J] at hi
  linarith

variable {ν T : ℝ} {hT : 0 ≤ T}

def actualReserve (U : NSEvolution ν T hT) (t : ℝ) : ℝ :=
  reserve ν (extendPath T hT (U.orderEnergyPath 0) t)

/-- The resource derivative follows from actual whole-space unforced NS;
no observer, receiver smallness, or future size bound is assumed here. -/
theorem actual_reserve_derivative (U : NSEvolution ν T hT) (t : ℝ)
    (hν : 0 < ν) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (actualReserve U)
      (-loss ν (extendPath T hT (U.orderEnergyPath 0) t)
        (extendPath T hT (U.orderEnergyPath 1) t)) t := by
  let ti : Icc (0 : ℝ) T := ⟨t, ht.1.le, ht.2.le⟩
  have hd := (U.orderEnergy_hasDerivWithinAt 0 ti).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  rw [FullEnergyParentReserve.actual_kinetic_rate] at hd
  have heq : extendPath T hT (U.orderEnergyPath 1) t = orderEnergy 1 (U.velocity ti) := by
    simp [extendPath, NSEvolution.orderEnergyPath, projIcc_of_mem hT ti.property, ti]
  unfold actualReserve
  rw [heq]
  exact reserve_derivative ν (orderEnergy 1 (U.velocity ti)) t _ hν.ne' hd

end Mettapedia.FluidDynamics.NavierStokes.EnergyCubeReceiverReserve
