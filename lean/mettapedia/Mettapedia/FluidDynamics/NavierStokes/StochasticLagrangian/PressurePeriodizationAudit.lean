import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputPeriodization

/-! Wrapped-distance, Fourier-phase, and nonzero-pressure periodization regressions. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressurePeriodizationAudit

open MeasureTheory FrequencyPairPeriodization PressureLowOutputPeriodization
open PeriodicFourierTriad FourierPressureCommutator PancakeBilinearPeriodization
open PressureLowOutputSymbol PressureLowOutputPhysicalKernel PressureLowOutputCutoff
open PressureBilinearOperator PressureOperatorCoordinates
open Mettapedia.Analysis.SmoothAnnulus Mettapedia.Analysis.EuclideanCrossProduct
open PressureTiltSymbol PancakeAnisotropyDepletion
open scoped FourierTransform SchwartzMap RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace Op := ContinuousLinearMap.instCompleteSpace

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The raw displacement has norm one but represents zero wrapped displacement. -/
example : ‖(EuclideanSpace.single (0 : Fin 6) (1 : ℝ))‖ = 1 ∧
    torusProjection (EuclideanSpace.single (0 : Fin 6) (1 : ℝ)) = 0 := by
  refine ⟨by simp, ?_⟩
  ext i
  by_cases hi : i = 0
  · subst i
    exact AddCircle.coe_period 1
  · simp [torusProjection, hi]

/-- The wrapped quarter-period distance is not the raw three-quarter coordinate. -/
example : ‖torusProjection (EuclideanSpace.single (0 : Fin 6) (3 / 4 : ℝ))‖ = 1 / 4 := by
  have h : torusProjection (EuclideanSpace.single (0 : Fin 6) (3 / 4 : ℝ)) =
      Pi.single 0 ((3 / 4 : ℝ) : UnitAddCircle) := by
    ext i
    by_cases hi : i = 0 <;> simp [torusProjection, hi]
  rw [h, Pi.norm_single, UnitAddCircle.norm_eq]
  norm_num

/-- Both inputs can attain the pair-torus distance simultaneously: their sum costs two. -/
example :
    (‖firstTorusDisplacement (fun _ : Fin 6 ↦ ((1 / 4 : ℝ) : UnitAddCircle))‖ +
      ‖secondTorusDisplacement (fun _ : Fin 6 ↦ ((1 / 4 : ℝ) : UnitAddCircle))‖ = 1 / 2) ∧
    ‖(fun _ : Fin 6 ↦ ((1 / 4 : ℝ) : UnitAddCircle))‖ = 1 / 4 := by
  change (‖(fun _ : Fin 3 ↦ ((1 / 4 : ℝ) : UnitAddCircle))‖ +
      ‖(fun _ : Fin 3 ↦ ((1 / 4 : ℝ) : UnitAddCircle))‖ = 1 / 2) ∧
    ‖(fun _ : Fin 6 ↦ ((1 / 4 : ℝ) : UnitAddCircle))‖ = 1 / 4
  norm_num [pi_norm_const, UnitAddCircle.norm_eq]

example (K : 𝓢(E6, ℂ)) :
    (∫ q : T6, ‖q‖ ^ 2 * ‖periodize K q‖) ≤ ∫ x : E6, ‖x‖ ^ 2 * ‖K x‖ :=
  integral_moment_periodize_le K 2

/-- The coefficient convention is the same negative character as the Euclidean transform. -/
example (K : 𝓢(E6, ℂ)) (n : Fin 6 → ℤ) :
    UnitAddTorus.mFourierCoeff (periodize K) n = (𝓕 K) (euclideanFrequencyPairOfWavevector n) := by
  rw [mFourierCoeff_periodize K K.continuous.measurable K.integrable, ← SchwartzMap.fourier_coe]

/-- Double imaginary phase is retained by the periodized pressure coefficient. -/
example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (he : ‖e‖ = 1)
    (k p : Wavevector) (w v : C3) :
    (UnitAddTorus.mFourierCoeff (periodicKernel N hN t e) (pairWavevector k p))
        (Complex.I • w) (Complex.I • v) =
      -((physicalCutoff t (N⁻¹ • pairEquiv.symm (realFrequency k, realFrequency p)) : ℂ) •
        pressurePairOperator e he k p w v) := by
  rw [mFourierCoeff_periodicKernel N hN t e he]
  simp [smul_smul]

private def vec3 (a b c : ℝ) : R3 := WithLp.toLp 2 ![a, b, c]
@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

private theorem norm_vec3_sq (a b c : ℝ) : ‖vec3 a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp [vec3, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

/-- A lattice-sampled low-output coefficient is nonzero after actual periodization. -/
example : Mettapedia.Analysis.EuclideanBilinearCoordinates.entry
    (UnitAddTorus.mFourierCoeff (periodicKernel 256 (by norm_num) (1 / 2)
      (EuclideanSpace.single 0 1)) (pairWavevector ![256, 0, 0] ![-255, 1, 0])) 1 2 2 =
      (-1 / 130052 : ℂ) := by
  have hk : ‖vec3 1 0 0‖ = 1 := by
    have h := norm_vec3_sq 1 0 0
    nlinarith [norm_nonneg (vec3 1 0 0)]
  have hq0 : 1 ≤ ‖vec3 1 1 0‖ := by
    have h := norm_vec3_sq 1 1 0
    nlinarith [norm_nonneg (vec3 1 1 0)]
  have hq1 : ‖vec3 1 1 0‖ ≤ 2 := by
    have h := norm_vec3_sq 1 1 0
    nlinarith [norm_nonneg (vec3 1 1 0)]
  have hq : (ratio (1 / 2))⁻¹ • (vec3 1 0 0 + vec3 (-255 / 256) (1 / 256) 0) = vec3 1 1 0 := by
    ext i
    fin_cases i <;> norm_num [ratio, vec3]
  have hscale : (256 : ℝ)⁻¹ • pairEquiv.symm
      (realFrequency ![256, 0, 0], realFrequency ![-255, 1, 0]) =
        pairEquiv.symm (vec3 1 0 0, vec3 (-255 / 256) (1 / 256) 0) := by
    ext i
    fin_cases i <;> norm_num [pairEquiv, pairLinearEquiv, vec3, realFrequency]
  have hc : physicalCutoff (1 / 2) ((256 : ℝ)⁻¹ • pairEquiv.symm
      (realFrequency ![256, 0, 0], realFrequency ![-255, 1, 0])) = 1 := by
    rw [hscale, physicalCutoff, pairEquiv.apply_symm_apply, hq,
      parameterCutoff_eq_one (1 / 2) (by constructor <;> norm_num),
      cutoff_eq_one (vec3 1 0 0) (by rw [hk]) (by rw [hk]; norm_num),
      cutoff_eq_one (vec3 1 1 0) hq0 hq1]
    norm_num
  rw [mFourierCoeff_periodicKernel _ _ _ _ (by simp), hc]
  simp only [Complex.ofReal_one, one_smul]
  rw [entry_pressurePairOperator]
  norm_num [CoherentPressurePair.tiltPair, CoherentPressurePair.tracePair, tiltSymbol,
    lineRemainder, cross, cross_apply, realFrequency, EuclideanSpace.norm_sq_eq,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

end Mettapedia.FluidDynamics.NavierStokes.PressurePeriodizationAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.continuous_torusProjection
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.torusProjection_representative
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.torusProjection_vadd
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.norm_torusProjection_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.norm_firstTorusDisplacement_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.norm_secondTorusDisplacement_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.integral_representative
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.lintegral_representative
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.measurable_periodize
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.lintegral_moment_periodize_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.mFourierCoeff_periodize
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.integrable_moment_periodize
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.integral_moment_periodize_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.integrable_periodize
#print axioms Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization.integral_twoInputMoment_periodize_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPeriodization.measurable_periodicKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPeriodization.integrable_periodicKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPeriodization.mFourierCoeff_periodicKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPeriodization.integrable_moment_periodicKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPeriodization.moment_periodicKernel_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPeriodization.exists_uniform_mass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPeriodization.exists_uniform_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPeriodization.exists_uniform_mass_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPeriodization.exists_uniform_firstMoment_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPeriodization.exists_uniform_twoInputMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputPeriodization.exists_uniform_twoInputMoment_budget
