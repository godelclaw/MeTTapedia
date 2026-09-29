import MettapediaNS.ForcedSignedBudget
import MettapediaNS.ViscousMemoryNormalization

/-!
# Continuation from a vorticity envelope with finite memory mass

The normalized pressure/strain candidate would give
`|ω|⁴ ≤ M (1+c)`, with `c ≥ 0` and a uniform bound on `∫ c`.
This file connects that precise spatial estimate to the actual NS energy
production and whole-space continuation. The amplitude split avoids
integrating a constant on infinite volume. No pressure singular-integral
estimate or interpolation inequality is needed for this implication.

The same implication, with the actual force work retained, rules out a
uniform mass envelope for the imported forced singularity. The memory
may depend on the complete history; the obstruction does not reset it.
Existence of the envelope for arbitrary unforced flows is not proved.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes

namespace WholeSpaceMemoryEnvelope

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerMeanClassical EulerVolterraConvolution EulerContinuousTimeIntegral
  WholeSpaceViscousEnergy WholeSpaceOrderEnergy WholeSpaceBetchov
  MiddleEigenvalueAlgebra

/-- The scalar memory majorant is integrable, including on infinite volume.
Its existence is a physical estimate to be supplied, not a state definition. -/
def MassEnvelope (u : SmoothL2Field Space) (M B : ℝ) : Prop :=
  ∃ c : Space → ℝ, Integrable c ∧ (∀ x, 0 ≤ c x) ∧ (∫ x, c x) ≤ B ∧
    ∀ x, vortSq (gradMatrix u x) ^ 2 ≤ M * (1 + c x)

/-- A normalized coercive observable supplies the exact spatial hypothesis.
The determinant bound is supplied separately by the physical memory theory. -/
theorem massEnvelope_of_normalized (u : SmoothL2Field Space)
    (Y h c : Space → ℝ) {k Z B : ℝ} (hk : 0 < k) (hZ : 0 ≤ Z)
    (hc : Integrable c) (hc0 : ∀ x, 0 ≤ c x) (hcB : (∫ x, c x) ≤ B)
    (hh : ∀ x, 0 < h x) (hhc : ∀ x, h x ≤ 1 + c x)
    (hY : ∀ x, k * vortSq (gradMatrix u x) ^ 2 ≤ Y x)
    (hbound : ∀ x, Y x / h x ≤ Z) : MassEnvelope u (Z / k) B := by
  exact ⟨c, hc, hc0, hcB, fun x ↦
    ViscousMemoryNormalization.normalized_quartic _ _ _ _ _ _ hk (hh x)
      hZ (hY x) (hhc x) (hbound x)⟩

/-- A sum-of-squares estimate for the literal stretching contraction. -/
theorem stretch_le (A : GradMatrix) :
    2 * stretch A ≤ normSq A + vortSq A ^ 2 := by
  have h : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      (A i j - vort A i * vort A j) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have he : (∑ i : Fin 3, ∑ j : Fin 3,
      (A i j - vort A i * vort A j) ^ 2) =
      normSq A + vortSq A ^ 2 - 2 * stretch A := by
    simp only [normSq, vortSq, stretch, Fin.sum_univ_three]
    ring
  rw [he] at h
  linarith

theorem vortSq_eq (A : GradMatrix) : vortSq A = normSq A - trSq A := by
  simp only [vortSq, vort, normSq, trSq, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem vortSq_integrable (u : SmoothL2Field Space) (hu : u.toLp ∈ solenoidalSpace) :
    Integrable (fun x ↦ vortSq (gradMatrix u x)) := by
  simp only [vortSq_eq]
  exact (normSq_integrable u).sub (trSq_integrable u hu)

theorem integral_vortSq (u : SmoothL2Field Space) (hu : u.toLp ∈ solenoidalSpace) :
    (∫ x, vortSq (gradMatrix u x)) = orderEnergy 1 u := by
  simp only [vortSq_eq]
  rw [integral_sub (normSq_integrable u) (trSq_integrable u hu),
    integral_trSq_eq_zero u hu, sub_zero, orderEnergy_one_eq]

/-- The infinite-volume split applies to the actual curl of the field. -/
theorem quartic_of_mass_envelope (u : SmoothL2Field Space)
    (hu : u.toLp ∈ solenoidalSpace) {M B : ℝ} (hM : 0 ≤ M)
    (h : MassEnvelope u M B) :
    Integrable (fun x ↦ vortSq (gradMatrix u x) ^ 2) ∧
      (∫ x, vortSq (gradMatrix u x) ^ 2) ≤
        Real.sqrt (2 * M) * orderEnergy 1 u + 2 * M * B := by
  obtain ⟨c, hc, hc0, hcB, hm⟩ := h
  obtain ⟨hi, hb⟩ := ViscousMemoryNormalization.integrable_quartic_of_memory
    volume (fun x ↦ vortSq (gradMatrix u x)) c M hM
    (vortSq_integrable u hu) hc
    (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) hc0 hm
  refine ⟨hi, ?_⟩
  rw [integral_vortSq u hu] at hb
  have hp := mul_le_mul_of_nonneg_left hcB (show 0 ≤ 2 * M by positivity)
  linarith

/-- The actual unforced production is bounded by gradient energy and the
fourth vorticity moment. Only Betchov's identity and a sum of squares enter. -/
theorem production_le_quartic {ν : ℝ} (hν : 0 ≤ ν) (u P : SmoothL2Field Space)
    (hdiv : ∀ x, divergence u.field x = 0)
    (hu : u.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace)
    (hq : Integrable (fun x ↦ vortSq (gradMatrix u x) ^ 2)) :
    orderProduction 1 u (navierStokesRhs ν u P) ≤
      orderEnergy 1 u + ∫ x, vortSq (gradMatrix u x) ^ 2 := by
  have ht := trCube_integrable u hu
  have hc := cubicSelf_integrable u
  have he : (fun x ↦ stretch (gradMatrix u x)) =
      fun x ↦ trCube (gradMatrix u x) - cubicSelf (gradMatrix u x) := by
    funext x
    rw [cubicSelf_eq _ (gradMatrix_trace u hu x), trCube_eq _ (gradMatrix_trace u hu x)]
    ring
  have hs : Integrable (fun x ↦ stretch (gradMatrix u x)) := by
    rw [he]
    exact ht.sub hc
  have hi : (∫ x, stretch (gradMatrix u x)) = -∫ x, cubicSelf (gradMatrix u x) := by
    rw [he, integral_sub ht hc, integral_trCube_eq_zero u hu, zero_sub]
  have hb := integral_mono (hs.const_mul 2) ((normSq_integrable u).add hq)
    (fun x ↦ stretch_le (gradMatrix u x))
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add (normSq_integrable u) hq,
    ← orderEnergy_one_eq, hi] at hb
  rw [orderProduction_one_eq ν u P hdiv hu hP]
  have hd := mul_nonneg hν (orderEnergy_nonneg 2 u)
  linarith

theorem production_le_mass_envelope {ν : ℝ} (hν : 0 ≤ ν)
    (u P : SmoothL2Field Space) (hdiv : ∀ x, divergence u.field x = 0)
    (hu : u.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace)
    {M B : ℝ} (hM : 0 ≤ M) (h : MassEnvelope u M B) :
    orderProduction 1 u (navierStokesRhs ν u P) ≤
      (1 + Real.sqrt (2 * M)) * orderEnergy 1 u + 2 * M * B := by
  obtain ⟨hi, hb⟩ := quartic_of_mass_envelope u hu hM h
  have hp := production_le_quartic hν u P hdiv hu hP hi
  linarith

/-- A fixed rate determined by the two spatial-envelope constants. -/
def rate (M B : ℝ) : ℝ := 1 + Real.sqrt (2 * M) + 2 * M * B

theorem rate_nonneg {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) : 0 ≤ rate M B := by
  unfold rate
  positivity

end WholeSpaceMemoryEnvelope

namespace WholeSpaceViscousFlow.NSEvolution

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceOrderEnergy
  WholeSpaceMemoryEnvelope

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- The memory envelope bounds the gradient energy of an actual unforced evolution. -/
theorem orderEnergy_one_le_mass_envelope (U : NSEvolution ν T hT) (hν : 0 ≤ ν)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hm : ∀ t, MassEnvelope (U.velocity t) M B) (t : Icc (0 : ℝ) T) :
    1 + orderEnergy 1 (U.velocity t) ≤
      (1 + orderEnergy 1 (U.velocity ⟨0, le_rfl, hT⟩)) * Real.exp (rate M B * t) := by
  have h := variable_linear_stability T hT
    (fun r ↦ 1 + extendPath T hT (U.orderEnergyPath 1) r)
    (fun r ↦ orderProduction 1 (U.velocity (projIcc 0 T hT r)) (U.derivative (projIcc 0 T hT r)))
    (rate M B) (ContinuousMap.const _ 1)
    (continuous_const.add ((U.orderEnergyPath 1).continuous.comp continuous_projIcc)).continuousOn
    (fun r hr ↦ by
      have hd := (U.orderEnergy_hasDerivWithinAt 1 ⟨r, hr.1, hr.2.le⟩).const_add 1
      simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using hd)
    (fun r _ ↦ by
      have hp := production_le_mass_envelope hν
        (U.velocity (projIcc 0 T hT r)) (U.pressureForce (projIcc 0 T hT r))
        (U.velocity_divergence _) (U.solenoidal _) (U.gradient _) hM (hm (projIcc 0 T hT r))
      rw [← U.derivative_eq_navierStokesRhs] at hp
      have hE := orderEnergy_nonneg 1 (U.velocity (projIcc 0 T hT r))
      have hh := mul_nonneg (show 0 ≤ 2 * M * B by positivity) hE
      simp only [extendPath, orderEnergyPath, ContinuousMap.coe_mk,
        ContinuousMap.const_apply, mul_one, rate]
      nlinarith [Real.sqrt_nonneg (2 * M)]) t
  rw [realIntegral_const] at h
  simpa only [extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
    orderEnergyPath, ContinuousMap.coe_mk, one_mul] using h

end WholeSpaceViscousFlow.NSEvolution

namespace WholeSpaceViscousFlow

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSolenoidal WholeSpaceOrderEnergy WholeSpaceMemoryEnvelope

/-- Constants fixed from the datum and horizon suffice. The physical memory
construction and its normalized envelope bound remain separate obligations. -/
theorem hasNSEvolution_of_mass_envelope {ν : ℝ} (hν : 0 < ν)
    (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace)
    (hbound : ∀ H, ∃ M : ℝ, 0 ≤ M ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ S (hS : 0 < S), S ≤ H → ∀ U : NSEvolution ν S hS.le,
        U.velocity ⟨0, le_rfl, hS.le⟩ = A → ∀ t, MassEnvelope (U.velocity t) M B) :
    ∀ T, 0 < T → HasNSEvolution ν A T := by
  apply hasNSEvolution_of_orderOne_bound hν A hA
  intro H
  obtain ⟨M, hM, B, hB, hb⟩ := hbound H
  refine ⟨(1 + orderEnergy 1 A) * Real.exp (rate M B * H), ?_⟩
  intro S hS hSH U hU t
  have he := U.orderEnergy_one_le_mass_envelope hν.le hM hB (hb S hS hSH U hU) t
  rw [hU] at he
  have hx := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (t.property.2.trans hSH) (rate_nonneg hM hB))
  have hm := mul_le_mul_of_nonneg_left hx (add_nonneg zero_le_one (orderEnergy_nonneg 1 A))
  linarith

end WholeSpaceViscousFlow

namespace WholeSpaceOfficial

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSolenoidal WholeSpaceViscousFlow WholeSpaceMemoryEnvelope

/-- The official whole-space assertion follows from the displayed physical
envelope uniformly on finite horizons, for every admissible datum. -/
theorem wholeSpaceStatementA_of_mass_envelope
    (hbound : ∀ ν : ℝ, 0 < ν → ∀ A : SmoothL2Field Space, A.toLp ∈ solenoidalSpace →
      ∀ H, ∃ M : ℝ, 0 ≤ M ∧ ∃ B : ℝ, 0 ≤ B ∧
        ∀ S (hS : 0 < S), S ≤ H → ∀ U : NSEvolution ν S hS.le,
          U.velocity ⟨0, le_rfl, hS.le⟩ = A → ∀ t, MassEnvelope (U.velocity t) M B) :
    OfficialWholeSpaceProblem.WholeSpaceStatementA :=
  wholeSpaceStatementA_of_global fun ν hν A hA ↦
    hasNSEvolution_of_mass_envelope hν A hA (hbound ν hν A hA)

end WholeSpaceOfficial

namespace ForcedPathEnergy.ForcedPath

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSolenoidal
  EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceOrderEnergy
  WholeSpaceMemoryEnvelope

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- The same physical implication retains a uniform first-derivative force
bound. Smooth compact forcing is within this class. -/
theorem orderEnergy_one_le_mass_envelope (U : ForcedPath ν T hT) (hν : 0 ≤ ν)
    {M B F : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hF : ∀ t, U.forcePath 1 t ≤ F)
    (hm : ∀ t, MassEnvelope (U.velocity t) M B) (t : Icc (0 : ℝ) T) :
    1 + orderEnergy 1 (U.velocity t) ≤
      (1 + orderEnergy 1 (U.velocity ⟨0, le_rfl, hT⟩)) *
        Real.exp ((rate M B + F) * t) := by
  have h := variable_linear_stability T hT
    (fun r ↦ 1 + extendPath T hT (U.energyPath 1) r)
    (fun r ↦ orderProduction 1 (U.velocity (projIcc 0 T hT r)) (U.derivative (projIcc 0 T hT r)))
    (rate M B + F) (ContinuousMap.const _ 1)
    (continuous_const.add ((U.energyPath 1).continuous.comp continuous_projIcc)).continuousOn
    (fun r hr ↦ by
      have hd := (U.energy_hasDerivWithinAt 1 ⟨r, hr.1, hr.2.le⟩).const_add 1
      simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using hd)
    (fun r _ ↦ by
      have hp := production_le_mass_envelope hν
        (U.velocity (projIcc 0 T hT r)) (U.pressureForce (projIcc 0 T hT r))
        (U.velocity_divergence _) (U.solenoidal _) (U.gradient _) hM (hm (projIcc 0 T hT r))
      have hf := U.production_le 1 (projIcc 0 T hT r)
      have hE := orderEnergy_nonneg 1 (U.velocity (projIcc 0 T hT r))
      have hh := mul_nonneg (show 0 ≤ 2 * M * B by positivity) hE
      have hb := mul_le_mul_of_nonneg_right (hF (projIcc 0 T hT r))
        (by positivity : 0 ≤ 1 + orderEnergy 1 (U.velocity (projIcc 0 T hT r)))
      simp only [extendPath, energyPath, ContinuousMap.coe_mk,
        ContinuousMap.const_apply, mul_one, rate]
      nlinarith [Real.sqrt_nonneg (2 * M)]) t
  rw [WholeSpaceViscousFlow.realIntegral_const] at h
  simpa only [extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
    energyPath, ContinuousMap.coe_mk, one_mul] using h

end ForcedPathEnergy.ForcedPath

namespace ForcedCandidatePancake

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev WholeSpaceOrderEnergy WholeSpaceMemoryEnvelope
open NavierStokesR3.ProblemStatement hiding Space

variable {ν : ℝ} {u : VelocityField} {p : PressureField} {f : VelocityField}
  {K : Set Space} (h : CandidateProperties ν u p f K)

/-- No common constants can bound the candidate by arbitrary nonnegative
finite-mass majorants on all shorter slabs. This allows different majorants
at every time, so in particular includes any retained physical memory. -/
theorem no_uniform_mass_envelope (hν : 0 < ν) :
    ¬ ∃ M : ℝ, 0 ≤ M ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2)
        (t : Icc (0 : ℝ) T), MassEnvelope ((forcedPath h T hT hT1).velocity t) M B := by
  rintro ⟨M, hM, B, hB, hm⟩
  let F := ‖forceEnergyPath h 1‖
  apply no_uniform_gradient_energy h hν
  refine ⟨(1 + orderEnergy 1 (velocitySlice h ⟨1 / 2, by norm_num⟩)) *
    Real.exp (rate M B + F), ?_⟩
  intro T hT hT1 t
  have he := (forcedPath h T hT hT1).orderEnergy_one_le_mass_envelope hν.le hM hB
    (forcedPath_forcePath_le h T hT hT1 1) (hm T hT hT1) t
  rw [forcedPath_initial] at he
  have ht : (t : ℝ) ≤ 1 := by linarith [t.property.2]
  have hr : 0 ≤ rate M B + F := add_nonneg (rate_nonneg hM hB) (norm_nonneg _)
  have hx := Real.exp_le_exp.mpr (show (rate M B + F) * t ≤ rate M B + F by
    nlinarith)
  have hb := mul_le_mul_of_nonneg_left hx
    (add_nonneg zero_le_one (orderEnergy_nonneg 1 (velocitySlice h ⟨1 / 2, by norm_num⟩)))
  linarith

/-- Applies the mass-envelope obstruction to the actual imported fields,
with all their forcing and support hypotheses retained. -/
theorem openAI_solution_no_uniform_mass_envelope (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      ∃ hc : CandidateProperties ν u p f K,
        ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
          ¬ ∃ M : ℝ, 0 ≤ M ∧ ∃ B : ℝ, 0 ≤ B ∧
            ∀ (T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1 / 2) (t : Icc (0 : ℝ) T),
              MassEnvelope ((forcedPath hc T hT hT1).velocity t) M B := by
  obtain ⟨u, p, f, K, hc, hg⟩ := NavierStokesR3.theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc, hg, no_uniform_mass_envelope hc hν⟩

end ForcedCandidatePancake

end Mettapedia.FluidDynamics.NavierStokes
