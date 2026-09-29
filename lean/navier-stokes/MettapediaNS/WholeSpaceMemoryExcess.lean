import MettapediaNS.WholeSpaceMemoryEnvelope

/-!
# A space-time memory excess suffices for continuation

The spatial mass in `MassEnvelope` may vary in time. Only a finite bound
on its time integral is needed. In the geometric application one writes
`Y ≤ B h + e`, with `e = max (Y-B h) 0`, and absorbs `e` into the scalar
majorant. This permits unbounded pointwise normalized values while keeping
the actual continuation implication.

The theorems concern actual smooth whole-space NS evolutions and actual
forced paths. They do not construct the proposed memory or prove an a
priori excess bound. The imported forced singularity admits no such
uniform integrated capacity either.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes

namespace WholeSpaceMemoryEnvelope

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field WholeSpaceBetchov MiddleEigenvalueAlgebra

/-- An integrable excess can be added to the memory majorant. The excess
need not have any pointwise upper bound. -/
theorem massEnvelope_of_excess (u : SmoothL2Field Space) (c e : Space → ℝ)
    {M B E : ℝ} (hM : 0 < M) (hc : Integrable c) (he : Integrable e)
    (hc0 : ∀ x, 0 ≤ c x) (he0 : ∀ x, 0 ≤ e x)
    (hcB : (∫ x, c x) ≤ B) (heE : (∫ x, e x) ≤ E)
    (h : ∀ x, vortSq (gradMatrix u x) ^ 2 ≤ M * (1 + c x) + e x) :
    MassEnvelope u M (B + E / M) := by
  refine ⟨fun x ↦ c x + e x / M, hc.add (he.div_const M),
    fun x ↦ add_nonneg (hc0 x) (div_nonneg (he0 x) hM.le), ?_, ?_⟩
  · rw [integral_add hc (he.div_const M), integral_div]
    exact add_le_add hcB (div_le_div_of_nonneg_right heE hM.le)
  · intro x
    have hh : M * (1 + (c x + e x / M)) = M * (1 + c x) + e x := by
      field_simp
      ring
    rw [hh]
    exact h x

end WholeSpaceMemoryEnvelope

namespace WholeSpaceViscousFlow.NSEvolution

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceOrderEnergy
  WholeSpaceMemoryEnvelope

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- The time integral of spatial capacity replaces its uniform time bound. -/
theorem orderEnergy_one_le_memory_capacity (U : NSEvolution ν T hT) (hν : 0 ≤ ν)
    {M : ℝ} (hM : 0 ≤ M) (B : C(Icc (0 : ℝ) T, ℝ)) (hB : ∀ t, 0 ≤ B t)
    (hm : ∀ t, MassEnvelope (U.velocity t) M (B t)) (t : Icc (0 : ℝ) T) :
    1 + orderEnergy 1 (U.velocity t) ≤
      (1 + orderEnergy 1 (U.velocity ⟨0, le_rfl, hT⟩)) *
        Real.exp ((1 + Real.sqrt (2 * M)) * t + 2 * M * realIntegral T hT B t) := by
  let K : C(Icc (0 : ℝ) T, ℝ) :=
    ⟨fun s ↦ 1 + Real.sqrt (2 * M) + 2 * M * B s, by fun_prop⟩
  have hg := variable_linear_stability T hT
    (fun r ↦ 1 + extendPath T hT (U.orderEnergyPath 1) r)
    (fun r ↦ orderProduction 1 (U.velocity (projIcc 0 T hT r)) (U.derivative (projIcc 0 T hT r)))
    1 K
    (continuous_const.add ((U.orderEnergyPath 1).continuous.comp continuous_projIcc)).continuousOn
    (fun r hr ↦ by
      have hd := (U.orderEnergy_hasDerivWithinAt 1 ⟨r, hr.1, hr.2.le⟩).const_add 1
      simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using hd)
    (fun r _ ↦ by
      have hp := production_le_mass_envelope hν
        (U.velocity (projIcc 0 T hT r)) (U.pressureForce (projIcc 0 T hT r))
        (U.velocity_divergence _) (U.solenoidal _) (U.gradient _) hM (hm _)
      rw [← U.derivative_eq_navierStokesRhs] at hp
      have hE := orderEnergy_nonneg 1 (U.velocity (projIcc 0 T hT r))
      have hb := hB (projIcc 0 T hT r)
      have hh := mul_nonneg (show 0 ≤ 2 * M * B (projIcc 0 T hT r) by positivity) hE
      simp only [extendPath, orderEnergyPath, ContinuousMap.coe_mk, one_mul, K]
      nlinarith [Real.sqrt_nonneg (2 * M)]) t
  have hi := realIntegral_le_affine T hT K B (1 + Real.sqrt (2 * M)) (2 * M)
    (fun _ ↦ le_rfl) t t.property.1
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hi)
    (add_nonneg zero_le_one (orderEnergy_nonneg 1 (U.velocity ⟨0, le_rfl, hT⟩)))
  simp only [extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
    orderEnergyPath, ContinuousMap.coe_mk, one_mul] at hg
  exact hg.trans he

end WholeSpaceViscousFlow.NSEvolution

namespace WholeSpaceViscousFlow

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSolenoidal EulerContinuousTimeIntegral WholeSpaceOrderEnergy WholeSpaceMemoryEnvelope

/-- A uniform finite space-time capacity gives global whole-space evolutions.
The capacity path may depend on the actual solution; its integral allowance
and `M` are fixed from the initial datum and prescribed horizon. -/
theorem hasNSEvolution_of_memory_capacity {ν : ℝ} (hν : 0 < ν)
    (u0 : SmoothL2Field Space) (hu0 : u0.toLp ∈ solenoidalSpace)
    (hbound : ∀ H, ∃ M : ℝ, 0 ≤ M ∧ ∃ A : ℝ,
      ∀ S (hS : 0 < S), S ≤ H → ∀ U : NSEvolution ν S hS.le,
        U.velocity ⟨0, le_rfl, hS.le⟩ = u0 →
          ∃ B : C(Icc (0 : ℝ) S, ℝ), (∀ t, 0 ≤ B t) ∧
            (∀ t, MassEnvelope (U.velocity t) M (B t)) ∧
            ∀ t : Icc (0 : ℝ) S, realIntegral S hS.le B t ≤ A) :
    ∀ T, 0 < T → HasNSEvolution ν u0 T := by
  apply hasNSEvolution_of_orderOne_bound hν u0 hu0
  intro H
  obtain ⟨M, hM, A, hb⟩ := hbound H
  refine ⟨(1 + orderEnergy 1 u0) * Real.exp ((1 + Real.sqrt (2 * M)) * H + 2 * M * A), ?_⟩
  intro S hS hSH U hU t
  obtain ⟨B, hB, hm, hi⟩ := hb S hS hSH U hU
  have he := U.orderEnergy_one_le_memory_capacity hν.le hM B hB hm t
  rw [hU] at he
  have hr : (1 + Real.sqrt (2 * M)) * (t : ℝ) + 2 * M * realIntegral S hS.le B t ≤
      (1 + Real.sqrt (2 * M)) * H + 2 * M * A :=
    add_le_add (mul_le_mul_of_nonneg_left (t.property.2.trans hSH) (by positivity))
      (mul_le_mul_of_nonneg_left (hi t) (by positivity))
  have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hr)
    (add_nonneg zero_le_one (orderEnergy_nonneg 1 u0))
  linarith

end WholeSpaceViscousFlow

namespace WholeSpaceOfficial

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSolenoidal EulerContinuousTimeIntegral WholeSpaceViscousFlow WholeSpaceMemoryEnvelope

theorem wholeSpaceStatementA_of_memory_capacity
    (hbound : ∀ ν : ℝ, 0 < ν → ∀ u0 : SmoothL2Field Space, u0.toLp ∈ solenoidalSpace →
      ∀ H, ∃ M : ℝ, 0 ≤ M ∧ ∃ A : ℝ,
        ∀ S (hS : 0 < S), S ≤ H → ∀ U : NSEvolution ν S hS.le,
          U.velocity ⟨0, le_rfl, hS.le⟩ = u0 →
            ∃ B : C(Icc (0 : ℝ) S, ℝ), (∀ t, 0 ≤ B t) ∧
              (∀ t, MassEnvelope (U.velocity t) M (B t)) ∧
              ∀ t : Icc (0 : ℝ) S, realIntegral S hS.le B t ≤ A) :
    OfficialWholeSpaceProblem.WholeSpaceStatementA :=
  wholeSpaceStatementA_of_global fun ν hν u0 hu0 ↦
    hasNSEvolution_of_memory_capacity hν u0 hu0 (hbound ν hν u0 hu0)

end WholeSpaceOfficial

namespace ForcedPathEnergy.ForcedPath

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceOrderEnergy WholeSpaceMemoryEnvelope

variable {ν T : ℝ} {hT : 0 ≤ T}

theorem orderEnergy_one_le_memory_capacity (U : ForcedPath ν T hT) (hν : 0 ≤ ν)
    {M F : ℝ} (hM : 0 ≤ M) (hF : ∀ t, U.forcePath 1 t ≤ F)
    (B : C(Icc (0 : ℝ) T, ℝ)) (hB : ∀ t, 0 ≤ B t)
    (hm : ∀ t, MassEnvelope (U.velocity t) M (B t)) (t : Icc (0 : ℝ) T) :
    1 + orderEnergy 1 (U.velocity t) ≤
      (1 + orderEnergy 1 (U.velocity ⟨0, le_rfl, hT⟩)) *
        Real.exp ((1 + Real.sqrt (2 * M) + F) * t + 2 * M * realIntegral T hT B t) := by
  let K : C(Icc (0 : ℝ) T, ℝ) :=
    ⟨fun s ↦ 1 + Real.sqrt (2 * M) + F + 2 * M * B s, by fun_prop⟩
  have hg := variable_linear_stability T hT
    (fun r ↦ 1 + extendPath T hT (U.energyPath 1) r)
    (fun r ↦ orderProduction 1 (U.velocity (projIcc 0 T hT r)) (U.derivative (projIcc 0 T hT r)))
    1 K
    (continuous_const.add ((U.energyPath 1).continuous.comp continuous_projIcc)).continuousOn
    (fun r hr ↦ by
      have hd := (U.energy_hasDerivWithinAt 1 ⟨r, hr.1, hr.2.le⟩).const_add 1
      simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using hd)
    (fun r _ ↦ by
      have hp := production_le_mass_envelope hν
        (U.velocity (projIcc 0 T hT r)) (U.pressureForce (projIcc 0 T hT r))
        (U.velocity_divergence _) (U.solenoidal _) (U.gradient _) hM (hm _)
      have hf := U.production_le 1 (projIcc 0 T hT r)
      have hE := orderEnergy_nonneg 1 (U.velocity (projIcc 0 T hT r))
      have hb := hB (projIcc 0 T hT r)
      have hh := mul_nonneg (show 0 ≤ 2 * M * B (projIcc 0 T hT r) by positivity) hE
      have hfb := mul_le_mul_of_nonneg_right (hF (projIcc 0 T hT r))
        (by positivity : 0 ≤ 1 + orderEnergy 1 (U.velocity (projIcc 0 T hT r)))
      simp only [extendPath, energyPath, ContinuousMap.coe_mk, one_mul, K]
      nlinarith [Real.sqrt_nonneg (2 * M)]) t
  have hi := WholeSpaceViscousFlow.realIntegral_le_affine T hT K B
    (1 + Real.sqrt (2 * M) + F) (2 * M) (fun _ ↦ le_rfl) t t.property.1
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hi)
    (add_nonneg zero_le_one (orderEnergy_nonneg 1 (U.velocity ⟨0, le_rfl, hT⟩)))
  simp only [extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
    energyPath, ContinuousMap.coe_mk, one_mul] at hg
  exact hg.trans he

end ForcedPathEnergy.ForcedPath

namespace ForcedCandidatePancake

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev EulerContinuousTimeIntegral WholeSpaceOrderEnergy WholeSpaceMemoryEnvelope
open NavierStokesR3.ProblemStatement hiding Space

variable {ν : ℝ} {u : VelocityField} {p : PressureField} {f : VelocityField}
  {K : Set Space} (h : CandidateProperties ν u p f K)

theorem no_uniform_memory_capacity (hν : 0 < ν) :
    ¬ ∃ M : ℝ, 0 ≤ M ∧ ∃ A : ℝ,
      ∀ (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2),
        ∃ B : C(Icc (0 : ℝ) T, ℝ), (∀ t, 0 ≤ B t) ∧
          (∀ t, MassEnvelope ((forcedPath h T hT hT1).velocity t) M (B t)) ∧
          ∀ t : Icc (0 : ℝ) T, realIntegral T hT B t ≤ A := by
  rintro ⟨M, hM, A, hm⟩
  let F := ‖forceEnergyPath h 1‖
  apply no_uniform_gradient_energy h hν
  refine ⟨(1 + orderEnergy 1 (velocitySlice h ⟨1 / 2, by norm_num⟩)) *
    Real.exp (1 + Real.sqrt (2 * M) + F + 2 * M * A), ?_⟩
  intro T hT hT1 t
  obtain ⟨B, hB, hb, hi⟩ := hm T hT hT1
  have he := (forcedPath h T hT hT1).orderEnergy_one_le_memory_capacity hν.le hM
    (forcedPath_forcePath_le h T hT hT1 1) B hB hb t
  rw [forcedPath_initial] at he
  have ht : (t : ℝ) ≤ 1 := by linarith [t.property.2]
  have hr : 0 ≤ 1 + Real.sqrt (2 * M) + F := by dsimp [F]; positivity
  have hleft := mul_le_mul_of_nonneg_left ht hr
  have hright := mul_le_mul_of_nonneg_left (hi t) (show 0 ≤ 2 * M by positivity)
  have hx := Real.exp_le_exp.mpr (show
      (1 + Real.sqrt (2 * M) + F) * t + 2 * M * realIntegral T hT B t ≤
        1 + Real.sqrt (2 * M) + F + 2 * M * A by linarith)
  have hh := mul_le_mul_of_nonneg_left hx
    (add_nonneg zero_le_one (orderEnergy_nonneg 1 (velocitySlice h ⟨1 / 2, by norm_num⟩)))
  linarith

theorem openAI_solution_no_uniform_memory_capacity (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      ∃ hc : CandidateProperties ν u p f K,
        ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
          ¬ ∃ M : ℝ, 0 ≤ M ∧ ∃ A : ℝ,
            ∀ (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2),
              ∃ B : C(Icc (0 : ℝ) T, ℝ), (∀ t, 0 ≤ B t) ∧
                (∀ t, MassEnvelope ((forcedPath hc T hT hT1).velocity t) M (B t)) ∧
                ∀ t : Icc (0 : ℝ) T, realIntegral T hT B t ≤ A := by
  obtain ⟨u, p, f, K, hc, hg⟩ := NavierStokesR3.theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc, hg, no_uniform_memory_capacity hc hν⟩

end ForcedCandidatePancake

end Mettapedia.FluidDynamics.NavierStokes
