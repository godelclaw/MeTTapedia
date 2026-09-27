import MettapediaNS.ForcedCandidatePancake
import NavierStokes.R3.Theorem

/-!
# Signed production budgets fail for the constructed forced singularities

The order-one energy balance retains the signed nonlinear production, the full
viscous dissipation, and the force work separately. Integration by parts moves
both derivatives in the force work onto the force. Thus bounded kinetic energy
and a bounded second-order force energy give a uniform, finite force allowance.

For OpenAI's actual compactly supported forced candidates, even the signed
nonlinear production minus the *full* viscous dissipation has no uniform upper
bound over the slabs exhausting `[1/2, 1)`. In particular, subtracting half of
the dissipation cannot give such a bound. These are full-field statements; no
frequency projection or estimate for an unforced solution is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ForcedPathEnergy

open Set MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerMeanClassical EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceViscousEnergy
  WholeSpaceOrderEnergy WholeSpaceBetchov

/-- Both derivatives in the gradient-energy force work can be placed on the force. -/
theorem orderProduction_one_force_eq (A F : SmoothL2Field Space) :
    orderProduction 1 A F = -2 * ⟪A.toLp, (laplacianField F).toLp⟫_ℝ := by
  rw [orderProduction, sum_words_one]
  simp only [wordField_snoc, wordField_zero, field_directional_inner,
    laplacianField, toLp_sumField, inner_sum, Finset.sum_neg_distrib]
  ring

/-- A convenient non-sharp bound using only the second-order force energy. -/
theorem norm_laplacian_le_sqrt_orderEnergy (F : SmoothL2Field Space) :
    ‖(laplacianField F).toLp‖ ≤ 3 * Real.sqrt (orderEnergy 2 F) := by
  rw [WholeSpaceViscousFlow.toLp_laplacianField]
  calc
    _ ≤ ∑ i : Fin 3, ‖(wordField F (WholeSpaceViscousFlow.doubleWord i)).toLp‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, Real.sqrt (orderEnergy 2 F) :=
      Finset.sum_le_sum fun i _ ↦ norm_le_sqrt_orderEnergy F _
    _ = _ := by simp

/-- Force work is bounded by kinetic energy and derivatives of the force, without
spending any of the viscous dissipation or using a gradient bound on the velocity. -/
theorem abs_orderProduction_one_force_le (A F : SmoothL2Field Space) :
    |orderProduction 1 A F| ≤
      6 * Real.sqrt (orderEnergy 0 A) * Real.sqrt (orderEnergy 2 F) := by
  rw [orderProduction_one_force_eq, abs_mul]
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hA : ‖A.toLp‖ ≤ Real.sqrt (orderEnergy 0 A) :=
    norm_le_sqrt_orderEnergy A (Fin.elim0 : Fin 0 → Fin 3)
  have hF := norm_laplacian_le_sqrt_orderEnergy F
  have hi := abs_real_inner_le_norm A.toLp (laplacianField F).toLp
  have hm := mul_le_mul hA hF (norm_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

theorem orderProduction_continuous_of {K : Type*} [TopologicalSpace K]
    (A B : K → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t ↦ (B t).jetLp n)) (n : ℕ) :
    Continuous (fun t ↦ orderProduction n (A t) (B t)) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro w _
  have ha := (ordinaryWordPath A hA w).continuous.congr (ordinaryWordPath_apply A hA w)
  have hb := (ordinaryWordPath B hB w).continuous.congr (ordinaryWordPath_apply B hB w)
  exact ha.inner hb

namespace ForcedPath

variable {ν T : ℝ} {hT : 0 ≤ T}

def productionPath (U : ForcedPath ν T hT) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ orderProduction 1 (U.velocity t) (U.derivative t),
    orderProduction_continuous_of _ _ U.velocity_continuous U.derivative_continuous 1⟩

def forceWorkPath (U : ForcedPath ν T hT) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ orderProduction 1 (U.velocity t) (U.force t),
    orderProduction_continuous_of _ _ U.velocity_continuous U.force_continuous 1⟩

/-- Twice the physical signed enstrophy production. The next theorem identifies
this continuous path with the spatial cubic integral of the actual velocity. -/
def nonlinearProductionPath (U : ForcedPath ν T hT) : C(Icc (0 : ℝ) T, ℝ) :=
  U.productionPath - U.forceWorkPath + (2 * ν) • U.energyPath 2

theorem nonlinearProductionPath_apply (U : ForcedPath ν T hT) (t : Icc (0 : ℝ) T) :
    U.nonlinearProductionPath t =
      -2 * ∫ x, cubicSelf (gradMatrix (U.velocity t) x) := by
  change orderProduction 1 (U.velocity t) (U.derivative t) -
    orderProduction 1 (U.velocity t) (U.force t) +
      (2 * ν) * orderEnergy 2 (U.velocity t) = _
  rw [U.equation, orderProduction_addField, orderProduction_one_eq ν _ _
    (U.velocity_divergence t) (U.solenoidal t) (U.gradient t)]
  ring

/-- The exact time-integrated gradient-energy balance, with force work separate. -/
theorem energy_one_balance (U : ForcedPath ν T hT) (t : Icc (0 : ℝ) T) :
    orderEnergy 1 (U.velocity t) =
      orderEnergy 1 (U.velocity ⟨0, le_rfl, hT⟩) +
        realIntegral T hT U.nonlinearProductionPath t -
        2 * ν * realIntegral T hT (U.energyPath 2) t +
        realIntegral T hT U.forceWorkPath t := by
  have hi := eq_initial_add_integral T hT U.productionPath
    (extendPath T hT (U.energyPath 1)) (U.energy_hasDerivWithinAt 1) t
  have he : U.productionPath =
      U.nonlinearProductionPath - (2 * ν) • U.energyPath 2 + U.forceWorkPath := by
    ext s
    simp only [nonlinearProductionPath, ContinuousMap.add_apply, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    ring
  rw [he, map_add, map_sub, map_smul] at hi
  simpa only [extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩), energyPath,
    ContinuousMap.coe_mk, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, smul_eq_mul, integral_apply, add_sub_assoc, add_assoc] using hi

theorem forceWorkPath_le (U : ForcedPath ν T hT) {E F : ℝ}
    (hE : ∀ t, orderEnergy 0 (U.velocity t) ≤ E)
    (hF : ∀ t, U.forcePath 2 t ≤ F) (t : Icc (0 : ℝ) T) :
    U.forceWorkPath t ≤ 6 * Real.sqrt E * F := by
  have h := abs_orderProduction_one_force_le (U.velocity t) (U.force t)
  have hm := mul_le_mul (Real.sqrt_le_sqrt (hE t)) (hF t)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg E)
  change Real.sqrt (orderEnergy 0 (U.velocity t)) *
    Real.sqrt (orderEnergy 2 (U.force t)) ≤ Real.sqrt E * F at hm
  change orderProduction 1 (U.velocity t) (U.force t) ≤ _
  nlinarith [le_abs_self (orderProduction 1 (U.velocity t) (U.force t))]

/-- A finite signed production allowance bounds the gradient energy. The force
allowance uses no future gradient energy or dissipation of the velocity. -/
theorem energy_one_le_of_signed_budget (U : ForcedPath ν T hT) (hT1 : T ≤ 1)
    {E F A c : ℝ} (hF0 : 0 ≤ F) (hc : c ≤ 2 * ν)
    (hE : ∀ t, orderEnergy 0 (U.velocity t) ≤ E)
    (hF : ∀ t, U.forcePath 2 t ≤ F) (t : Icc (0 : ℝ) T)
    (hbudget : realIntegral T hT U.nonlinearProductionPath t ≤
      c * realIntegral T hT (U.energyPath 2) t + A) :
    orderEnergy 1 (U.velocity t) ≤
      orderEnergy 1 (U.velocity ⟨0, le_rfl, hT⟩) + A + 6 * Real.sqrt E * F := by
  have hforce := WholeSpaceViscousFlow.realIntegral_le_affine T hT U.forceWorkPath
    (ContinuousMap.const _ 0) (6 * Real.sqrt E * F) 0
    (fun s ↦ by simpa using U.forceWorkPath_le hE hF s) t t.property.1
  have hD : 0 ≤ realIntegral T hT (U.energyPath 2) t := by
    apply intervalIntegral.integral_nonneg t.property.1
    intro s _
    exact orderEnergy_nonneg 2 _
  have ht1 : (t : ℝ) ≤ 1 := t.property.2.trans hT1
  have hf0 : 0 ≤ 6 * Real.sqrt E * F := by positivity
  have hft := mul_le_mul_of_nonneg_left ht1 hf0
  have hd := mul_le_mul_of_nonneg_right hc hD
  rw [U.energy_one_balance t]
  nlinarith

end ForcedPath
end Mettapedia.FluidDynamics.NavierStokes.ForcedPathEnergy

namespace Mettapedia.FluidDynamics.NavierStokes.ForcedCandidatePancake

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerSmoothSobolev
  EulerContinuousTimeIntegral WholeSpaceOrderEnergy ForcedPathEnergy
open NavierStokesR3.ProblemStatement hiding Space

variable {ν : ℝ} {u : VelocityField} {p : PressureField} {f : VelocityField}
  {K : Set Space} (h : CandidateProperties ν u p f K)

/-- The gradient energy of the actual candidate cannot be bounded uniformly on
the shorter slabs. The force's second-order energy stays bounded throughout. -/
theorem no_uniform_gradient_energy (hν : 0 < ν) :
    ¬ ∃ Z : ℝ, ∀ (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2)
      (s : Icc (0 : ℝ) T), orderEnergy 1 ((forcedPath h T hT hT1).velocity s) ≤ Z := by
  rintro ⟨Z, hZ⟩
  let F := ‖forceEnergyPath h 2‖
  let A := velocitySlice h ⟨1 / 2, by norm_num⟩
  let W := (1 + orderEnergy 2 A) * Real.exp (rungTwoConstant ν Z + F)
  obtain ⟨E, hE0, hE⟩ := h.energy_bounded
  have hbounds (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2) (s : Icc (0 : ℝ) T) :
      orderEnergy 2 ((forcedPath h T hT hT1).velocity s) ≤ W := by
    have hw := (forcedPath h T hT hT1).orderEnergy_two_uniform hν (by linarith)
      (hZ T hT hT1) (norm_nonneg _) (forcedPath_forcePath_le h T hT hT1 2) s
    simpa only [forcedPath_initial] using hw
  let M := (13 * smoothEmbeddingConstant) * Real.sqrt (2 * E + Z + W)
  have hM0 : 0 ≤ M := mul_nonneg
    (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) (Real.sqrt_nonneg _)
  obtain ⟨t, x, ht, hnear, hspeed⟩ := h.speed_unbounded (M + 1) (by linarith) (1 / 2)
    (by norm_num)
  let T := t - 1 / 2
  have hT : 0 ≤ T := by dsimp [T]; linarith
  have hT1 : T < 1 / 2 := by dsimp [T]; linarith [ht.2]
  let s : Icc (0 : ℝ) T := ⟨T, hT, le_rfl⟩
  let U := forcedPath h T hT hT1
  have hu : U.velocity s = velocitySlice h ⟨t, ht⟩ := by
    apply field_ext
    funext y
    change u (1 / 2 + (t - 1 / 2), y) = u (t, y)
    congr 1
    ext <;> simp
  have h0 : orderEnergy 0 (U.velocity s) ≤ 2 * E := by
    rw [hu, orderEnergy_zero_eq]
    exact mul_le_mul_of_nonneg_left (hE t ⟨ht.1.le, ht.2⟩).2 (by norm_num)
  have h1 := hZ T hT hT1 s
  have h2 := hbounds T hT hT1 s
  have hw : wordEnergy 2 (U.velocity s) ≤ 2 * E + Z + W := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, wordEnergy_succ, wordEnergy_succ, wordEnergy_zero]
    linarith
  have hp := wordBound_pointwise (wordBound_sqrt_energy 2 (U.velocity s)) x
  have hm : ‖(U.velocity s).field x‖ ≤ M := hp.trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hw)
      (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg))
  rw [hu, velocitySlice_field] at hm
  linarith

/-- A signed production allowance independent of the shorter slab and its time.
The coefficient `c = 2ν` subtracts full dissipation; `c = ν` subtracts half. -/
def UniformSignedProductionBudget (c : ℝ) : Prop :=
  ∃ A : ℝ, ∀ (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2) (s : Icc (0 : ℝ) T),
    realIntegral T hT (forcedPath h T hT hT1).nonlinearProductionPath s ≤
      c * realIntegral T hT ((forcedPath h T hT hT1).energyPath 2) s + A

/-- Even subtracting the full viscous dissipation leaves an unbounded signed
nonlinear integral on the actual forced candidate. The force allowance is finite. -/
theorem no_uniform_signed_production_budget (hν : 0 < ν) {c : ℝ} (hc : c ≤ 2 * ν) :
    ¬ UniformSignedProductionBudget h c := by
  rintro ⟨A, hA⟩
  obtain ⟨E, hE0, hE⟩ := h.energy_bounded
  let F := ‖forceEnergyPath h 2‖
  apply no_uniform_gradient_energy h hν
  refine ⟨orderEnergy 1 (velocitySlice h ⟨1 / 2, by norm_num⟩) + A +
    6 * Real.sqrt (2 * E) * F, ?_⟩
  intro T hT hT1 s
  have he (r : Icc (0 : ℝ) T) :
      orderEnergy 0 ((forcedPath h T hT hT1).velocity r) ≤ 2 * E := by
    rw [forcedPath_velocity, orderEnergy_zero_eq]
    exact mul_le_mul_of_nonneg_left
      (hE (slabTime T hT1 r) ⟨(slabTime T hT1 r).property.1.le,
        (slabTime T hT1 r).property.2⟩).2 (by norm_num)
  have hb := (forcedPath h T hT hT1).energy_one_le_of_signed_budget (by linarith)
    (norm_nonneg _) hc he (forcedPath_forcePath_le h T hT hT1 2) s (hA T hT hT1 s)
  simpa only [forcedPath_initial] using hb

/-- This is a theorem about the imported construction for every positive viscosity,
not a hypothetical forced path or a numerical surrogate. -/
theorem openAI_solution_no_uniform_signed_production_budget (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      ∃ hc : CandidateProperties ν u p f K,
        ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
          ∀ c : ℝ, c ≤ 2 * ν → ¬ UniformSignedProductionBudget hc c := by
  obtain ⟨u, p, f, K, hc, hg⟩ := NavierStokesR3.theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc, hg, fun c hcle ↦ no_uniform_signed_production_budget hc hν hcle⟩

end Mettapedia.FluidDynamics.NavierStokes.ForcedCandidatePancake
