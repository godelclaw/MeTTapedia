import MettapediaNS.WholeSpaceOrderEnergy
import MettapediaNS.WholeSpaceOfficialStatement

/-!
# Continuation from a bounded gradient energy on `ℝ³`

Along a smooth Navier–Stokes evolution with positive viscosity, suppose the gradient
energy `E₁ = ‖∇u‖₂²` stays below `Z`. The order-two energy then grows at most
exponentially, `E₂(t) ≤ E₂(0) exp(M t)`, and its dissipation `∫ E₃` is bounded. The
order-three energy obeys `E₃' ≤ k E₃` with a rate `k` whose time integral is bounded by
these two facts, so `E₃` stays bounded. The `H³` energy is therefore bounded on every
finite horizon, and the restart argument of `WholeSpaceNSContinuation` extends the
evolution. At a finite maximal time the gradient energy is unbounded (Leray's criterion),
and finite-horizon bounds on it for all data give the official statement (A).

All constants are explicit; no bound is assumed along the evolution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow

open Set Filter MeasureTheory InnerProductSpace
open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanClassical EulerVolterraConvolution EulerContinuousTimeIntegral
  WholeSpaceViscousEnergy WholeSpaceOrderEnergy
open scoped Topology

/-! ## Interval integrals of paths -/

theorem realIntegral_const (T : ℝ) (hT : 0 ≤ T) (c : ℝ) (t : ℝ) :
    realIntegral T hT (ContinuousMap.const (Icc (0 : ℝ) T) c) t = c * t := by
  simp only [realIntegral, extendPath, ContinuousMap.const_apply, intervalIntegral.integral_const,
    smul_eq_mul, sub_zero]
  ring

theorem realIntegral_zero (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) :
    realIntegral T hT f 0 = 0 := by
  simp only [realIntegral, intervalIntegral.integral_same]

/-- A pointwise affine bound integrates to an affine bound. -/
theorem realIntegral_le_affine (T : ℝ) (hT : 0 ≤ T) (f g : C(Icc (0 : ℝ) T, ℝ)) (a b : ℝ)
    (hle : ∀ s, f s ≤ a + b * g s) (t : ℝ) (ht : 0 ≤ t) :
    realIntegral T hT f t ≤ a * t + b * realIntegral T hT g t := by
  have hf := (extendPath_continuous T hT f).intervalIntegrable (μ := volume) 0 t
  have hg := (extendPath_continuous T hT g).intervalIntegrable (μ := volume) 0 t
  have hmono : realIntegral T hT f t ≤ ∫ s in (0 : ℝ)..t, (a + b * extendPath T hT g s) :=
    intervalIntegral.integral_mono_on ht hf (intervalIntegrable_const.add (hg.const_mul b))
      fun s _ ↦ hle _
  rw [intervalIntegral.integral_add intervalIntegrable_const (hg.const_mul b),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hmono
  simpa only [smul_eq_mul, sub_zero, realIntegral, mul_comm t a] using hmono

namespace NSEvolution

variable {ν T : ℝ} {hT : 0 ≤ T}

/-! ## Order energies along an evolution -/

theorem orderEnergy_continuous (U : NSEvolution ν T hT) (n : ℕ) :
    Continuous (fun t ↦ orderEnergy n (U.velocity t)) := by
  cases n with
  | zero =>
    simpa only [wordEnergy_zero] using wordEnergy_continuous U.velocity U.velocity_continuous 0
  | succ m =>
    have h := (wordEnergy_continuous U.velocity U.velocity_continuous (m + 1)).sub
      (wordEnergy_continuous U.velocity U.velocity_continuous m)
    refine h.congr fun t ↦ ?_
    simp only [Pi.sub_apply, wordEnergy_succ]
    ring

/-- The order-`n` energy along the evolution. -/
def orderEnergyPath (U : NSEvolution ν T hT) (n : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ orderEnergy n (U.velocity t), U.orderEnergy_continuous n⟩

theorem orderEnergyPath_apply (U : NSEvolution ν T hT) (n : ℕ) (t : Icc (0 : ℝ) T) :
    U.orderEnergyPath n t = orderEnergy n (U.velocity t) := rfl

theorem orderEnergy_hasDerivWithinAt (U : NSEvolution ν T hT) (n : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (U.orderEnergyPath n))
      (orderProduction n (U.velocity t) (U.derivative t)) (Icc (0 : ℝ) T) t := by
  cases n with
  | zero =>
    have h := U.energy_hasDerivWithinAt 0 t
    have he : extendPath T hT (U.energyPath 0) = extendPath T hT (U.orderEnergyPath 0) := by
      funext r
      simp only [extendPath, energyPath, orderEnergyPath, ContinuousMap.coe_mk, wordEnergy_zero]
    have hp : integerEnergyProduction 0 (U.velocity t) (U.derivative t) =
        orderProduction 0 (U.velocity t) (U.derivative t) := by
      simp only [integerEnergyProduction, orderProduction, zero_add, Finset.range_one,
        Finset.sum_singleton]
    rw [he, hp] at h
    exact h
  | succ m =>
    have h := (U.energy_hasDerivWithinAt (m + 1) t).sub (U.energy_hasDerivWithinAt m t)
    have he : extendPath T hT (U.energyPath (m + 1)) - extendPath T hT (U.energyPath m) =
        extendPath T hT (U.orderEnergyPath (m + 1)) := by
      funext r
      simp only [Pi.sub_apply, extendPath, energyPath, orderEnergyPath, ContinuousMap.coe_mk,
        wordEnergy_succ]
      ring
    rw [he, integerEnergyProduction_succ, add_sub_cancel_left] at h
    exact h

theorem velocity_divergence (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    ∀ x, divergence (U.velocity t).field x = 0 :=
  solenoidal_representative_divergence _ (U.solenoidal t) _ (U.velocity t).smooth
    (U.velocity t).toLp_ae

/-! ## The energy does not increase -/

theorem orderProduction_zero_le (U : NSEvolution ν T hT) (hν : 0 ≤ ν) (t : Icc (0 : ℝ) T) :
    orderProduction 0 (U.velocity t) (U.derivative t) ≤ 0 := by
  rw [U.derivative_eq_navierStokesRhs, orderProduction_navierStokesRhs 0 ν _ _
    (U.velocity_divergence t) (U.solenoidal t) (U.gradient t)]
  simp only [transportCommutator_zero, inner_zero_left, Finset.sum_const_zero, mul_zero,
    zero_sub]
  have h := orderEnergy_nonneg 1 (U.velocity t)
  nlinarith

theorem orderEnergy_zero_le (U : NSEvolution ν T hT) (hν : 0 ≤ ν) (t : Icc (0 : ℝ) T) :
    orderEnergy 0 (U.velocity t) ≤ orderEnergy 0 (U.velocity ⟨0, le_rfl, hT⟩) := by
  have h := variable_linear_stability T hT (extendPath T hT (U.orderEnergyPath 0))
    (fun r ↦ orderProduction 0 (U.velocity (projIcc 0 T hT r)) (U.derivative (projIcc 0 T hT r)))
    0 (ContinuousMap.const _ 0) ((U.orderEnergyPath 0).continuous.comp continuous_projIcc).continuousOn
    (fun r hr ↦ by
      have h := U.orderEnergy_hasDerivWithinAt 0 ⟨r, hr.1, hr.2.le⟩
      simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using h)
    (fun r _ ↦ by simpa only [zero_mul] using U.orderProduction_zero_le hν _) t
  simpa only [zero_mul, Real.exp_zero, mul_one, extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩), orderEnergyPath,
    ContinuousMap.coe_mk] using h

/-! ## Order two -/

theorem orderProduction_two_le_along (U : NSEvolution ν T hT) (hν : 0 < ν) {Z : ℝ}
    (hZ : ∀ t, orderEnergy 1 (U.velocity t) ≤ Z) (t : Icc (0 : ℝ) T) :
    orderProduction 2 (U.velocity t) (U.derivative t) ≤
      -(ν * orderEnergy 3 (U.velocity t)) + rungTwoConstant ν Z * orderEnergy 2 (U.velocity t) := by
  rw [U.derivative_eq_navierStokesRhs]
  exact orderProduction_two_le hν _ _ (U.velocity_divergence t) (U.solenoidal t) (U.gradient t)
    (hZ t)

theorem rungTwoConstant_nonneg (ν Z : ℝ) (hν : 0 < ν) : 0 ≤ rungTwoConstant ν Z := by
  unfold rungTwoConstant
  have := sobolevReal_nonneg
  positivity

/-- **The order-two energy grows at most exponentially.** -/
theorem orderEnergy_two_le (U : NSEvolution ν T hT) (hν : 0 < ν) {Z : ℝ}
    (hZ : ∀ t, orderEnergy 1 (U.velocity t) ≤ Z) (t : Icc (0 : ℝ) T) :
    orderEnergy 2 (U.velocity t) ≤
      orderEnergy 2 (U.velocity ⟨0, le_rfl, hT⟩) * Real.exp (rungTwoConstant ν Z * t) := by
  have h := variable_linear_stability T hT (extendPath T hT (U.orderEnergyPath 2))
    (fun r ↦ orderProduction 2 (U.velocity (projIcc 0 T hT r)) (U.derivative (projIcc 0 T hT r)))
    (rungTwoConstant ν Z) (ContinuousMap.const _ 1)
    ((U.orderEnergyPath 2).continuous.comp continuous_projIcc).continuousOn
    (fun r hr ↦ by
      have h := U.orderEnergy_hasDerivWithinAt 2 ⟨r, hr.1, hr.2.le⟩
      simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using h)
    (fun r _ ↦ by
      have h := U.orderProduction_two_le_along hν hZ (projIcc 0 T hT r)
      have h3 := orderEnergy_nonneg 3 (U.velocity (projIcc 0 T hT r))
      simp only [extendPath, ContinuousMap.const_apply, mul_one, orderEnergyPath,
        ContinuousMap.coe_mk]
      nlinarith) t
  rw [realIntegral_const, one_mul] at h
  simpa only [extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩), orderEnergyPath,
    ContinuousMap.coe_mk] using h

/-- **The order-three dissipation is integrable.** -/
theorem dissipation_three_le (U : NSEvolution ν T hT) (hν : 0 < ν) {Z : ℝ}
    (hZ : ∀ t, orderEnergy 1 (U.velocity t) ≤ Z) (t : Icc (0 : ℝ) T) :
    ν * realIntegral T hT (U.orderEnergyPath 3) t ≤
      orderEnergy 2 (U.velocity ⟨0, le_rfl, hT⟩) +
        rungTwoConstant ν Z * realIntegral T hT (U.orderEnergyPath 2) t := by
  set M := rungTwoConstant ν Z
  set X : ℝ → ℝ := fun r ↦ extendPath T hT (U.orderEnergyPath 2) r +
    ν * realIntegral T hT (U.orderEnergyPath 3) r - M * realIntegral T hT (U.orderEnergyPath 2) r
  have hI2 (r : ℝ) := realIntegral_hasDerivAt T hT (U.orderEnergyPath 2) r
  have hI3 (r : ℝ) := realIntegral_hasDerivAt T hT (U.orderEnergyPath 3) r
  have hcont : ContinuousOn X (Icc 0 T) := by
    refine Continuous.continuousOn ?_
    exact ((extendPath_continuous T hT _).add (continuous_const.mul
      (show Differentiable ℝ (realIntegral T hT (U.orderEnergyPath 3)) from
        fun r ↦ (hI3 r).differentiableAt).continuous)).sub (continuous_const.mul
      (show Differentiable ℝ (realIntegral T hT (U.orderEnergyPath 2)) from
        fun r ↦ (hI2 r).differentiableAt).continuous)
  have h := variable_linear_stability T hT X
    (fun r ↦ orderProduction 2 (U.velocity (projIcc 0 T hT r)) (U.derivative (projIcc 0 T hT r)) +
      ν * extendPath T hT (U.orderEnergyPath 3) r - M * extendPath T hT (U.orderEnergyPath 2) r)
    0 (ContinuousMap.const _ 0) hcont
    (fun r hr ↦ by
      have h2 := U.orderEnergy_hasDerivWithinAt 2 ⟨r, hr.1, hr.2.le⟩
      rw [show ((⟨r, hr.1, hr.2.le⟩ : Icc (0 : ℝ) T) : ℝ) = r from rfl] at h2
      have he : (⟨r, hr.1, hr.2.le⟩ : Icc (0 : ℝ) T) = projIcc 0 T hT r :=
        (projIcc_of_mem hT ⟨hr.1, hr.2.le⟩).symm
      rw [he] at h2
      exact (h2.add ((hI3 r).hasDerivWithinAt.const_mul ν)).sub
        ((hI2 r).hasDerivWithinAt.const_mul M))
    (fun r _ ↦ by
      have hb := U.orderProduction_two_le_along hν hZ (projIcc 0 T hT r)
      simp only [zero_mul]
      simp only [extendPath, orderEnergyPath, ContinuousMap.coe_mk]
      linarith) t
  simp only [zero_mul, Real.exp_zero, mul_one, X, realIntegral_zero, mul_zero, add_zero,
    sub_zero] at h
  have h0 : extendPath T hT (U.orderEnergyPath 2) 0 = orderEnergy 2 (U.velocity ⟨0, le_rfl, hT⟩) := by
    simp only [extendPath, projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
      orderEnergyPath, ContinuousMap.coe_mk]
  have ht : extendPath T hT (U.orderEnergyPath 2) t = orderEnergy 2 (U.velocity t) := by
    simp only [extendPath, projIcc_of_mem hT t.property, orderEnergyPath, ContinuousMap.coe_mk]
  rw [h0, ht] at h
  have hnn := orderEnergy_nonneg 2 (U.velocity t)
  linarith

theorem orderProduction_three_le_along (U : NSEvolution ν T hT) (hν : 0 < ν) {Z : ℝ}
    (hZ : ∀ t, orderEnergy 1 (U.velocity t) ≤ Z) (t : Icc (0 : ℝ) T) :
    orderProduction 3 (U.velocity t) (U.derivative t) ≤
      -(ν * orderEnergy 4 (U.velocity t)) + (rungThreeConstant ν Z + rungThreeGrowth *
        (1 + orderEnergy 2 (U.velocity t)) * (1 + orderEnergy 3 (U.velocity t))) *
          orderEnergy 3 (U.velocity t) := by
  rw [U.derivative_eq_navierStokesRhs]
  exact orderProduction_three_le hν _ _ (U.velocity_divergence t) (U.solenoidal t) (U.gradient t)
    (hZ t)

/-- The growth rate of the order-three energy, as a continuous path. -/
def rungThreeRate (U : NSEvolution ν T hT) (Z : ℝ) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ rungThreeConstant ν Z + rungThreeGrowth * (1 + U.orderEnergyPath 2 t) *
    (1 + U.orderEnergyPath 3 t), by fun_prop⟩

/-- **Grönwall for the order-three energy.** -/
theorem orderEnergy_three_le (U : NSEvolution ν T hT) (hν : 0 < ν) {Z : ℝ}
    (hZ : ∀ t, orderEnergy 1 (U.velocity t) ≤ Z) (t : Icc (0 : ℝ) T) :
    orderEnergy 3 (U.velocity t) ≤ orderEnergy 3 (U.velocity ⟨0, le_rfl, hT⟩) *
      Real.exp (realIntegral T hT (U.rungThreeRate Z) t) := by
  have h := variable_linear_stability T hT (extendPath T hT (U.orderEnergyPath 3))
    (fun r ↦ orderProduction 3 (U.velocity (projIcc 0 T hT r)) (U.derivative (projIcc 0 T hT r)))
    1 (U.rungThreeRate Z)
    ((U.orderEnergyPath 3).continuous.comp continuous_projIcc).continuousOn
    (fun r hr ↦ by
      have h := U.orderEnergy_hasDerivWithinAt 3 ⟨r, hr.1, hr.2.le⟩
      simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using h)
    (fun r _ ↦ by
      have h := U.orderProduction_three_le_along hν hZ (projIcc 0 T hT r)
      have h4 := orderEnergy_nonneg 4 (U.velocity (projIcc 0 T hT r))
      simp only [extendPath, one_mul, rungThreeRate, orderEnergyPath, ContinuousMap.coe_mk]
      nlinarith) t
  rw [one_mul] at h
  simpa only [extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩), orderEnergyPath,
    ContinuousMap.coe_mk] using h

end NSEvolution

/-! ## A uniform `H³` bound -/

/-- The bound on the order-two energy on a horizon `H`. -/
def secondBound (ν Z H : ℝ) (A : SmoothL2Field Space) : ℝ :=
  orderEnergy 2 A * Real.exp (rungTwoConstant ν Z * H)

/-- The bound on the order-three dissipation on a horizon `H`, times the viscosity. -/
def dissipationBound (ν Z H : ℝ) (A : SmoothL2Field Space) : ℝ :=
  orderEnergy 2 A + rungTwoConstant ν Z * secondBound ν Z H A * H

/-- The bound on the time integral of the order-three growth rate. -/
def rateIntegralBound (ν Z H : ℝ) (A : SmoothL2Field Space) : ℝ :=
  (rungThreeConstant ν Z + rungThreeGrowth * (1 + secondBound ν Z H A)) * H +
    rungThreeGrowth * (1 + secondBound ν Z H A) * (dissipationBound ν Z H A / ν)

/-- The `H³` bound on a horizon `H` for gradient energy at most `Z`. -/
def h3Bound (ν Z H : ℝ) (A : SmoothL2Field Space) : ℝ :=
  orderEnergy 0 A + Z + secondBound ν Z H A +
    orderEnergy 3 A * Real.exp (rateIntegralBound ν Z H A)

theorem wordEnergy_three_eq (A : SmoothL2Field Space) :
    wordEnergy 3 A = orderEnergy 0 A + orderEnergy 1 A + orderEnergy 2 A + orderEnergy 3 A := by
  simp only [wordEnergy, orderEnergy, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add]

theorem rungThreeConstant_nonneg (ν Z : ℝ) (hν : 0 < ν) : 0 ≤ rungThreeConstant ν Z := by
  unfold rungThreeConstant
  have := sobolevReal_nonneg
  positivity

theorem rungThreeGrowth_nonneg : 0 ≤ rungThreeGrowth := by
  unfold rungThreeGrowth
  exact mul_nonneg (by norm_num) (sq_nonneg _)

namespace NSEvolution

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- **A bounded gradient energy bounds the `H³` energy on every finite horizon.** -/
theorem wordEnergy_three_le (U : NSEvolution ν T hT) (hν : 0 < ν) {Z H : ℝ}
    (hZ : ∀ t, orderEnergy 1 (U.velocity t) ≤ Z) (hTH : T ≤ H) (t : Icc (0 : ℝ) T) :
    wordEnergy 3 (U.velocity t) ≤ h3Bound ν Z H (U.velocity ⟨0, le_rfl, hT⟩) := by
  set A := U.velocity ⟨0, le_rfl, hT⟩
  have hM := rungTwoConstant_nonneg ν Z hν
  have hM3 := rungThreeConstant_nonneg ν Z hν
  have hG := rungThreeGrowth_nonneg
  have hA2 := orderEnergy_nonneg 2 A
  have hA3 := orderEnergy_nonneg 3 A
  have hB (s : Icc (0 : ℝ) T) : orderEnergy 2 (U.velocity s) ≤ secondBound ν Z H A :=
    (U.orderEnergy_two_le hν hZ s).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (s.2.2.trans hTH) hM)) hA2)
  have hB0 : 0 ≤ secondBound ν Z H A := (orderEnergy_nonneg 2 _).trans (hB t)
  have hH : 0 ≤ H := hT.trans hTH
  have hI2 : realIntegral T hT (U.orderEnergyPath 2) t ≤ secondBound ν Z H A * H := by
    have h := realIntegral_le_affine T hT (U.orderEnergyPath 2) (U.orderEnergyPath 2)
      (secondBound ν Z H A) 0 (fun s ↦ by rw [zero_mul, add_zero]; exact hB s) t t.2.1
    rw [zero_mul, add_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (t.2.2.trans hTH) hB0)
  have hI3 : realIntegral T hT (U.orderEnergyPath 3) t ≤ dissipationBound ν Z H A / ν := by
    rw [le_div_iff₀ hν, mul_comm]
    have h := U.dissipation_three_le hν hZ t
    have h2 := mul_le_mul_of_nonneg_left hI2 hM
    unfold dissipationBound
    nlinarith
  have hK : realIntegral T hT (U.rungThreeRate Z) t ≤ rateIntegralBound ν Z H A := by
    have h := realIntegral_le_affine T hT (U.rungThreeRate Z) (U.orderEnergyPath 3)
      (rungThreeConstant ν Z + rungThreeGrowth * (1 + secondBound ν Z H A))
      (rungThreeGrowth * (1 + secondBound ν Z H A)) (fun s ↦ by
        have h2 := hB s
        have h3 := orderEnergy_nonneg 3 (U.velocity s)
        simp only [rungThreeRate, orderEnergyPath, ContinuousMap.coe_mk]
        have hprod : rungThreeGrowth * (1 + orderEnergy 2 (U.velocity s)) *
            (1 + orderEnergy 3 (U.velocity s)) ≤
            rungThreeGrowth * (1 + secondBound ν Z H A) * (1 + orderEnergy 3 (U.velocity s)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hG) (by linarith)
        nlinarith) t t.2.1
    unfold rateIntegralBound
    have hc : 0 ≤ rungThreeConstant ν Z + rungThreeGrowth * (1 + secondBound ν Z H A) := by
      positivity
    have hc2 : 0 ≤ rungThreeGrowth * (1 + secondBound ν Z H A) := by positivity
    calc _ ≤ _ := h
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (t.2.2.trans hTH) hc)
        (mul_le_mul_of_nonneg_left hI3 hc2)
  have h3 : orderEnergy 3 (U.velocity t) ≤ orderEnergy 3 A * Real.exp (rateIntegralBound ν Z H A) :=
    (U.orderEnergy_three_le hν hZ t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hK) hA3)
  rw [wordEnergy_three_eq, h3Bound]
  have h0 := U.orderEnergy_zero_le hν.le t
  linarith [hZ t, hB t]

end NSEvolution

/-! ## Continuation -/

namespace NSLifespan

variable {ν : ℝ} {A : SmoothL2Field Space} (L : NSLifespan ν A)

/-- **Restart from a uniform `H³` bound.** If the `H³` energies of the shorter evolutions
at their end times are bounded, the lifespan is not maximal. -/
theorem not_wordEnergy_bounded (hν : 0 ≤ ν) (E : ℝ) (hE0 : 0 ≤ E)
    (hE : ∀ S (hS : 0 < S) (hSL : S < L.duration),
      wordEnergy 3 ((L.evolution S hS hSL).velocity ⟨S, hS.le, le_rfl⟩) ≤ E) : False := by
  have hc := tameEnergyConstant_nonneg 3
  have hδpos : 0 < 2 * (1 + tameEnergyConstant 3) * (1 + E) :=
    mul_pos (mul_pos two_pos (by linarith)) (by linarith)
  obtain ⟨δ, hδ, hδdef⟩ : ∃ δ, 0 < δ ∧ δ = (2 * (1 + tameEnergyConstant 3) * (1 + E))⁻¹ :=
    ⟨_, inv_pos.mpr hδpos, rfl⟩
  obtain ⟨S, hSmax⟩ : ∃ S, S = max (L.duration - δ / 2) (L.duration / 2) := ⟨_, rfl⟩
  have hS : 0 < S := by
    rw [hSmax]
    exact lt_of_lt_of_le (half_pos L.duration_pos) (le_max_right _ _)
  have hSL : S < L.duration := by
    rw [hSmax]
    exact max_lt (by linarith) (half_lt_self L.duration_pos)
  have hSδ : L.duration - δ / 2 ≤ S := by
    rw [hSmax]
    exact le_max_left _ _
  have hEU := hE S hS hSL
  have hδR : δ ≤ regularizedTime ((L.evolution S hS hSL).velocity ⟨S, hS.le, le_rfl⟩) := by
    rw [hδdef, regularizedTime]
    have hw := wordEnergy_nonneg 3 ((L.evolution S hS hSL).velocity ⟨S, hS.le, le_rfl⟩)
    apply inv_anti₀ (mul_pos (mul_pos two_pos (by linarith)) (by linarith))
    have h2 : 0 ≤ 2 * (1 + tameEnergyConstant 3) := by linarith
    exact mul_le_mul_of_nonneg_left (by linarith) h2
  obtain ⟨V, hV, -⟩ := (L.evolution S hS hSL).exists_extension hν hS
  apply L.maximal (S + regularizedTime ((L.evolution S hS hSL).velocity ⟨S, hS.le, le_rfl⟩))
  · linarith
  · exact ⟨add_pos hS (regularizedTime_pos _), V, hV.trans (L.evolution_initial S hS hSL)⟩

/-- **Leray's criterion.** At a finite maximal time the gradient energies of the shorter
evolutions are unbounded. -/
theorem not_orderOne_bounded (hν : 0 < ν) (Z : ℝ)
    (hZ : ∀ S (hS : 0 < S) (hSL : S < L.duration) t,
      orderEnergy 1 ((L.evolution S hS hSL).velocity t) ≤ Z) : False := by
  have hZ0 : 0 ≤ Z := (orderEnergy_nonneg 1 _).trans
    (hZ (L.duration / 2) (half_pos L.duration_pos) (half_lt_self L.duration_pos) ⟨0, le_rfl,
      (half_pos L.duration_pos).le⟩)
  refine L.not_wordEnergy_bounded hν.le (h3Bound ν Z L.duration A) ?_ fun S hS hSL ↦ ?_
  · unfold h3Bound
    have := orderEnergy_nonneg 0 A
    have : 0 ≤ secondBound ν Z L.duration A :=
      mul_nonneg (orderEnergy_nonneg 2 A) (Real.exp_pos _).le
    have : 0 ≤ orderEnergy 3 A * Real.exp (rateIntegralBound ν Z L.duration A) :=
      mul_nonneg (orderEnergy_nonneg 3 A) (Real.exp_pos _).le
    linarith
  · have h := (L.evolution S hS hSL).wordEnergy_three_le hν (hZ S hS hSL) hSL.le
      ⟨S, hS.le, le_rfl⟩
    rwa [L.evolution_initial S hS hSL] at h

/-- The gradient energy blows up at a finite maximal time. -/
theorem orderOne_unbounded (hν : 0 < ν) (Z : ℝ) :
    ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) (t : Icc (0 : ℝ) S),
      Z < orderEnergy 1 ((L.evolution S hS hSL).velocity t) := by
  by_contra h
  push Not at h
  exact L.not_orderOne_bounded hν Z h

end NSLifespan

/-- **Finite-horizon gradient-energy bounds give global evolutions.** -/
theorem hasNSEvolution_of_orderOne_bound {ν : ℝ} (hν : 0 < ν)
    (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace)
    (hbound : ∀ H, ∃ Z, ∀ S (hS : 0 < S), S ≤ H → ∀ U : NSEvolution ν S hS.le,
      U.velocity ⟨0, le_rfl, hS.le⟩ = A → ∀ t, orderEnergy 1 (U.velocity t) ≤ Z) :
    ∀ T, 0 < T → HasNSEvolution ν A T := by
  rcases global_or_lifespan hν.le A hA with h | hne
  · exact h
  · refine hne.elim fun L ↦ ?_
    exfalso
    obtain ⟨Z, hZ⟩ := hbound L.duration
    exact L.not_orderOne_bounded hν Z fun S hS hSL t ↦
      hZ S hS hSL.le (L.evolution S hS hSL) (L.evolution_initial S hS hSL) t

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceOfficial

open EulerSmoothLimit EulerLpTranslation EulerMeanSolenoidal WholeSpaceViscousFlow
  WholeSpaceOrderEnergy
open Mettapedia.FluidDynamics.NavierStokes.OfficialWholeSpaceProblem

/-- **Finite-horizon gradient-energy bounds give the official statement (A).** If, for every
viscosity and every smooth solenoidal datum with all derivatives in `L²`, the gradient
energy `‖∇u‖₂²` of every smooth evolution from the datum is bounded on each finite horizon,
the official whole-space statement holds. -/
theorem wholeSpaceStatementA_of_orderOne_bound
    (hbound : ∀ ν : ℝ, 0 < ν → ∀ A : SmoothL2Field Space, A.toLp ∈ solenoidalSpace →
      ∀ H, ∃ Z, ∀ S (hS : 0 < S), S ≤ H → ∀ U : NSEvolution ν S hS.le,
        U.velocity ⟨0, le_rfl, hS.le⟩ = A → ∀ t, orderEnergy 1 (U.velocity t) ≤ Z) :
    WholeSpaceStatementA :=
  wholeSpaceStatementA_of_global fun ν hν A hA ↦
    hasNSEvolution_of_orderOne_bound hν A hA (hbound ν hν A hA)

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceOfficial
