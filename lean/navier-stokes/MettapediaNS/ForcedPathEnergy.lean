import MettapediaNS.WholeSpaceBetchov

/-!
# Energy estimates for forced smooth `L²` paths on `ℝ³`

A forced path is a path of smooth solenoidal fields with all derivatives in `L²` whose time
derivative is the Navier–Stokes right-hand side plus a force. The production of every
order energy splits into the unforced production and the pairing with the force, and the
latter is at most `2 √Eₙ(u) √Eₙ(f)` by Cauchy–Schwarz.

With Betchov's identity on `ℝ³`, a continuous majorant `K ≥ 0` of the middle strain
eigenvalue bounds the gradient energy:
`1 + E₁(t) ≤ (1 + E₁(0)) exp ∫₀ᵗ (2K + √E₁(f))`. A bound `E₁ ≤ Z` bounds the order-two
energy in the same way, with the order-two absorption constant of `WholeSpaceOrderEnergy`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ForcedPathEnergy

open Set MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal EulerMeanClassical
  EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceViscousEnergy
  WholeSpaceOrderEnergy MiddleEigenvalueAlgebra WholeSpaceBetchov
open PancakeSpectralProjectorRegularity.SymmetricStrain

/-! ## Splitting the production -/

theorem orderProduction_addField (n : ℕ) (A Q R : SmoothL2Field Space) :
    orderProduction n A (addField Q R) = orderProduction n A Q + orderProduction n A R := by
  simp only [orderProduction, wordField_add, toLp_addField, inner_add_right,
    Finset.sum_add_distrib]
  ring

/-- **Cauchy–Schwarz for the production.** -/
theorem orderProduction_le (n : ℕ) (A F : SmoothL2Field Space) :
    orderProduction n A F ≤ 2 * (Real.sqrt (orderEnergy n A) * Real.sqrt (orderEnergy n F)) := by
  unfold orderProduction orderEnergy
  have h1 : ∑ w : Fin n → Fin 3, ⟪(wordField A w).toLp, (wordField F w).toLp⟫_ℝ ≤
      ∑ w : Fin n → Fin 3, ‖(wordField A w).toLp‖ * ‖(wordField F w).toLp‖ :=
    Finset.sum_le_sum fun w _ ↦ real_inner_le_norm _ _
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun w : Fin n → Fin 3 ↦ ‖(wordField A w).toLp‖) (fun w ↦ ‖(wordField F w).toLp‖)
  linarith

/-- `2 √E φ ≤ φ (1 + E)`. -/
theorem two_sqrt_mul_le {E φ : ℝ} (hE : 0 ≤ E) (hφ : 0 ≤ φ) :
    2 * (Real.sqrt E * φ) ≤ φ * (1 + E) := by
  have hs := Real.sq_sqrt hE
  have h : 0 ≤ (Real.sqrt E - 1) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hφ h]

theorem orderEnergy_continuous_of {K : Type*} [TopologicalSpace K] (A : K → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t ↦ orderEnergy n (A t)) := by
  cases n with
  | zero =>
    simpa only [wordEnergy_zero] using wordEnergy_continuous A hA 0
  | succ m =>
    refine ((wordEnergy_continuous A hA (m + 1)).sub (wordEnergy_continuous A hA m)).congr
      fun t ↦ ?_
    simp only [Pi.sub_apply, wordEnergy_succ]
    ring

/-! ## Forced paths -/

/-- A smooth forced Navier–Stokes path on `[0, T]`. -/
structure ForcedPath (ν T : ℝ) (hT : 0 ≤ T) where
  velocity : Icc (0 : ℝ) T → SmoothL2Field Space
  derivative : Icc (0 : ℝ) T → SmoothL2Field Space
  pressureForce : Icc (0 : ℝ) T → SmoothL2Field Space
  force : Icc (0 : ℝ) T → SmoothL2Field Space
  velocity_continuous : ∀ n, Continuous (fun t ↦ (velocity t).jetLp n)
  derivative_continuous : ∀ n, Continuous (fun t ↦ (derivative t).jetLp n)
  force_continuous : ∀ n, Continuous (fun t ↦ (force t).jetLp n)
  solenoidal : ∀ t, (velocity t).toLp ∈ solenoidalSpace
  gradient : ∀ t, (pressureForce t).toLp ∈ gradientSpace
  time_law : ∀ t (ht : t ∈ Ioo 0 T) x,
    HasDerivAt (fun r ↦ (velocity (projIcc 0 T hT r)).field x)
      ((derivative ⟨t, ht.1.le, ht.2.le⟩).field x) t
  equation : ∀ t, derivative t =
    addField (navierStokesRhs ν (velocity t) (pressureForce t)) (force t)

namespace ForcedPath

variable {ν T : ℝ} {hT : 0 ≤ T}

theorem velocity_divergence (U : ForcedPath ν T hT) (t : Icc (0 : ℝ) T) :
    ∀ x, divergence (U.velocity t).field x = 0 :=
  solenoidal_representative_divergence _ (U.solenoidal t) _ (U.velocity t).smooth
    (U.velocity t).toLp_ae

/-- The order-`n` energy of the velocity, as a path. -/
def energyPath (U : ForcedPath ν T hT) (n : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ orderEnergy n (U.velocity t), orderEnergy_continuous_of _ U.velocity_continuous n⟩

/-- The square root of the order-`n` energy of the force, as a path. -/
def forcePath (U : ForcedPath ν T hT) (n : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ Real.sqrt (orderEnergy n (U.force t)),
    Real.continuous_sqrt.comp (orderEnergy_continuous_of _ U.force_continuous n)⟩

theorem forcePath_nonneg (U : ForcedPath ν T hT) (n : ℕ) (t : Icc (0 : ℝ) T) :
    0 ≤ U.forcePath n t := Real.sqrt_nonneg _

theorem energy_hasDerivWithinAt (U : ForcedPath ν T hT) (n : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (U.energyPath n))
      (orderProduction n (U.velocity t) (U.derivative t)) (Icc (0 : ℝ) T) t := by
  have hw (m : ℕ) := wordEnergy_hasDerivWithinAt T hT U.velocity U.derivative
    U.velocity_continuous U.derivative_continuous U.time_law m t
  cases n with
  | zero =>
    have h := hw 0
    have he : (fun r ↦ wordEnergy 0 (U.velocity (projIcc 0 T hT r))) =
        extendPath T hT (U.energyPath 0) := by
      funext r
      simp only [extendPath, energyPath, ContinuousMap.coe_mk, wordEnergy_zero]
    rw [he] at h
    refine h.congr_deriv ?_
    simp only [orderProduction, zero_add, Finset.range_one, Finset.sum_singleton]
  | succ m =>
    have h := (hw (m + 1)).sub (hw m)
    have he : (fun r ↦ wordEnergy (m + 1) (U.velocity (projIcc 0 T hT r))) -
        (fun r ↦ wordEnergy m (U.velocity (projIcc 0 T hT r))) =
        extendPath T hT (U.energyPath (m + 1)) := by
      funext r
      simp only [Pi.sub_apply, extendPath, energyPath, ContinuousMap.coe_mk, wordEnergy_succ]
      ring
    rw [he] at h
    refine h.congr_deriv ?_
    have hs := integerEnergyProduction_succ m (U.velocity t) (U.derivative t)
    simp only [integerEnergyProduction] at hs
    linarith

/-- The production of a forced path splits into the unforced production and the force. -/
theorem production_le (U : ForcedPath ν T hT) (n : ℕ) (t : Icc (0 : ℝ) T) :
    orderProduction n (U.velocity t) (U.derivative t) ≤
      orderProduction n (U.velocity t) (navierStokesRhs ν (U.velocity t) (U.pressureForce t)) +
        U.forcePath n t * (1 + orderEnergy n (U.velocity t)) := by
  rw [U.equation t, orderProduction_addField]
  have h := orderProduction_le n (U.velocity t) (U.force t)
  have h2 := two_sqrt_mul_le (orderEnergy_nonneg n (U.velocity t)) (U.forcePath_nonneg n t)
  simp only [forcePath, ContinuousMap.coe_mk] at h2 ⊢
  linarith

/-! ## The gradient energy -/

/-- The growth rate of the gradient energy, from a majorant of the middle eigenvalue. -/
def rateOne (U : ForcedPath ν T hT) (K : C(Icc (0 : ℝ) T, ℝ)) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ 2 * K t + U.forcePath 1 t, by fun_prop⟩

/-- **The gradient energy of a forced path is controlled by the middle eigenvalue.** -/
theorem orderEnergy_one_le (U : ForcedPath ν T hT) (hν : 0 ≤ ν) (K : C(Icc (0 : ℝ) T, ℝ))
    (hK0 : ∀ t, 0 ≤ K t)
    (hK : ∀ t x, secondEigenvalue
      (toStrain (symm (gradMatrix (U.velocity t) x)) (symm_symm _)) ≤ K t)
    (t : Icc (0 : ℝ) T) :
    1 + orderEnergy 1 (U.velocity t) ≤ (1 + orderEnergy 1 (U.velocity ⟨0, le_rfl, hT⟩)) *
      Real.exp (realIntegral T hT (U.rateOne K) t) := by
  have h := variable_linear_stability T hT (fun r ↦ 1 + extendPath T hT (U.energyPath 1) r)
    (fun r ↦ orderProduction 1 (U.velocity (projIcc 0 T hT r)) (U.derivative (projIcc 0 T hT r)))
    1 (U.rateOne K)
    (continuous_const.add ((U.energyPath 1).continuous.comp continuous_projIcc)).continuousOn
    (fun r hr ↦ by
      have h := U.energy_hasDerivWithinAt 1 ⟨r, hr.1, hr.2.le⟩
      have h' := h.const_add 1
      simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using h')
    (fun r _ ↦ by
      have hp := U.production_le 1 (projIcc 0 T hT r)
      have hb := orderProduction_one_le hν (U.velocity (projIcc 0 T hT r))
        (U.pressureForce (projIcc 0 T hT r)) (U.velocity_divergence _) (U.solenoidal _)
        (U.gradient _) (hK0 _) (hK _)
      have hE := orderEnergy_nonneg 1 (U.velocity (projIcc 0 T hT r))
      have hk := hK0 (projIcc 0 T hT r)
      simp only [extendPath, rateOne, energyPath, ContinuousMap.coe_mk, one_mul]
      nlinarith) t
  simpa only [extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩), energyPath,
    ContinuousMap.coe_mk, one_mul] using h

/-! ## The order-two energy -/

/-- The growth rate of the order-two energy, for gradient energy at most `Z`. -/
def rateTwo (U : ForcedPath ν T hT) (Z : ℝ) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ rungTwoConstant ν Z + U.forcePath 2 t, by fun_prop⟩

/-- **A bounded gradient energy controls the order-two energy of a forced path.** -/
theorem orderEnergy_two_le (U : ForcedPath ν T hT) (hν : 0 < ν) {Z : ℝ}
    (hZ : ∀ t, orderEnergy 1 (U.velocity t) ≤ Z) (t : Icc (0 : ℝ) T) :
    1 + orderEnergy 2 (U.velocity t) ≤ (1 + orderEnergy 2 (U.velocity ⟨0, le_rfl, hT⟩)) *
      Real.exp (realIntegral T hT (U.rateTwo Z) t) := by
  have hM := WholeSpaceViscousFlow.NSEvolution.rungTwoConstant_nonneg ν Z hν
  have h := variable_linear_stability T hT (fun r ↦ 1 + extendPath T hT (U.energyPath 2) r)
    (fun r ↦ orderProduction 2 (U.velocity (projIcc 0 T hT r)) (U.derivative (projIcc 0 T hT r)))
    1 (U.rateTwo Z)
    (continuous_const.add ((U.energyPath 2).continuous.comp continuous_projIcc)).continuousOn
    (fun r hr ↦ by
      have h := U.energy_hasDerivWithinAt 2 ⟨r, hr.1, hr.2.le⟩
      have h' := h.const_add 1
      simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using h')
    (fun r _ ↦ by
      have hp := U.production_le 2 (projIcc 0 T hT r)
      have hb := orderProduction_two_le hν (U.velocity (projIcc 0 T hT r))
        (U.pressureForce (projIcc 0 T hT r)) (U.velocity_divergence _) (U.solenoidal _)
        (U.gradient _) (hZ _)
      have hE := orderEnergy_nonneg 2 (U.velocity (projIcc 0 T hT r))
      have hE3 := orderEnergy_nonneg 3 (U.velocity (projIcc 0 T hT r))
      have hf := U.forcePath_nonneg 2 (projIcc 0 T hT r)
      simp only [extendPath, rateTwo, energyPath, ContinuousMap.coe_mk, one_mul]
      nlinarith) t
  simpa only [extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩), energyPath,
    ContinuousMap.coe_mk, one_mul] using h

/-! ## Bounds uniform over shorter time slabs -/

/-- A nonnegative path bounded by `F` has integral at most `F` on a slab of length at most one. -/
theorem realIntegral_le_bound (a : C(Icc (0 : ℝ) T, ℝ)) (hT1 : T ≤ 1)
    {F : ℝ} (hF : 0 ≤ F) (ha0 : ∀ t, 0 ≤ a t) (ha : ∀ t, a t ≤ F)
    (t : Icc (0 : ℝ) T) : realIntegral T hT a t ≤ F := by
  have hn : ‖a‖ ≤ F := (ContinuousMap.norm_le _ hF).mpr fun s ↦ by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (ha0 s)] using ha s
  have hi := integralLinear_bound T hT a
  calc realIntegral T hT a t ≤ ‖integralLinear T hT a t‖ := le_abs_self _
    _ ≤ ‖integralLinear T hT a‖ := (integralLinear T hT a).norm_coe_le_norm t
    _ ≤ T * ‖a‖ := hi
    _ ≤ F := by nlinarith

/-- The first energy bound uses the integral of the majorant, not its supremum. -/
theorem orderEnergy_one_uniform (U : ForcedPath ν T hT) (hν : 0 ≤ ν) (hT1 : T ≤ 1)
    (K : C(Icc (0 : ℝ) T, ℝ)) (hK0 : ∀ t, 0 ≤ K t)
    (hK : ∀ t x, secondEigenvalue
      (toStrain (symm (gradMatrix (U.velocity t) x)) (symm_symm _)) ≤ K t)
    {G F : ℝ} (hG : realIntegral T hT K T ≤ G) (hF0 : 0 ≤ F)
    (hF : ∀ t, U.forcePath 1 t ≤ F) (t : Icc (0 : ℝ) T) :
    orderEnergy 1 (U.velocity t) ≤
      (1 + orderEnergy 1 (U.velocity ⟨0, le_rfl, hT⟩)) * Real.exp (2 * G + F) := by
  have hI : realIntegral T hT (U.rateOne K) t ≤ 2 * G + F := by
    have he : U.rateOne K = (2 : ℝ) • K + U.forcePath 1 := by ext s; rfl
    change (integral T hT (U.rateOne K)) t ≤ _
    rw [he, map_add, map_smul]
    change 2 * realIntegral T hT K t + realIntegral T hT (U.forcePath 1) t ≤ _
    have hk := (WholeSpaceViscousFlow.realIntegral_le_of_nonneg T hT K hK0
      t.property.1 t.property.2).trans hG
    have hf := realIntegral_le_bound (hT := hT) (U.forcePath 1) hT1 hF0
      (U.forcePath_nonneg 1) hF t
    linarith
  have he := U.orderEnergy_one_le hν K hK0 hK t
  have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hI)
    (show 0 ≤ 1 + orderEnergy 1 (U.velocity ⟨0, le_rfl, hT⟩) by
      linarith [orderEnergy_nonneg 1 (U.velocity ⟨0, le_rfl, hT⟩)])
  linarith

/-- A uniform first-energy and force bound gives a uniform second-energy bound. -/
theorem orderEnergy_two_uniform (U : ForcedPath ν T hT) (hν : 0 < ν) (hT1 : T ≤ 1)
    {Z F : ℝ} (hZ : ∀ t, orderEnergy 1 (U.velocity t) ≤ Z) (hF0 : 0 ≤ F)
    (hF : ∀ t, U.forcePath 2 t ≤ F) (t : Icc (0 : ℝ) T) :
    orderEnergy 2 (U.velocity t) ≤
      (1 + orderEnergy 2 (U.velocity ⟨0, le_rfl, hT⟩)) *
        Real.exp (rungTwoConstant ν Z + F) := by
  have hc := WholeSpaceViscousFlow.NSEvolution.rungTwoConstant_nonneg ν Z hν
  have hI : realIntegral T hT (U.rateTwo Z) t ≤ rungTwoConstant ν Z + F :=
    realIntegral_le_bound (U.rateTwo Z) hT1 (add_nonneg hc hF0)
      (fun s ↦ add_nonneg hc (U.forcePath_nonneg 2 s))
      (fun s ↦ add_le_add le_rfl (hF s)) t
  have he := U.orderEnergy_two_le hν hZ t
  have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hI)
    (show 0 ≤ 1 + orderEnergy 2 (U.velocity ⟨0, le_rfl, hT⟩) by
      linarith [orderEnergy_nonneg 2 (U.velocity ⟨0, le_rfl, hT⟩)])
  linarith

end ForcedPath

end Mettapedia.FluidDynamics.NavierStokes.ForcedPathEnergy
