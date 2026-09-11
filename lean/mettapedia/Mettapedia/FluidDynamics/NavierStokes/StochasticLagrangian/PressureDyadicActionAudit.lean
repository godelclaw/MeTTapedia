import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootIntegrableKernelBudget

/-! Nonzero coefficients, complex phases, and full-field dyadic convergence. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicActionAudit

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator PancakeBilinearPeriodization
open PressureDyadicPeriodization PressureDyadicAction PressureBilinearOperator PressureOperatorCoordinates
open PressureLowOutputSymbol (pairEquiv pairLinearEquiv)
open PressureLowOutputCutoff (ratio parameterCutoff_eq_one)
open PressureLowOutputDyadicBudget (dyadicParameter)
open PressureDyadicPhysicalKernel (physicalCutoff)
open PressureKernelAction (kernelAction)
open Mettapedia.Analysis.DyadicAnnulus Mettapedia.Analysis.EuclideanCrossProduct
open Mettapedia.Analysis.EuclideanBilinearCoordinates
open PressureTiltSymbol PancakeAnisotropyDepletion
open scoped RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
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

private def vec3 (a b c : ℝ) : R3 := WithLp.toLp 2 ![a, b, c]
@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

private theorem norm_vec3_sq (a b c : ℝ) : ‖vec3 a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp [vec3, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

private theorem norm_axis : ‖vec3 1 0 0‖ = 1 := by
  have h := norm_vec3_sq 1 0 0
  nlinarith [norm_nonneg (vec3 1 0 0)]

private theorem character_origin (k : Wavevector) : UnitAddTorus.mFourier k (0 : T3) = 1 := by
  simp [UnitAddTorus.mFourier]

private theorem cutoff_example : physicalCutoff (1 / 2) ((1280 : ℝ)⁻¹ • pairEquiv.symm
    (realFrequency ![1280, 0, 0], realFrequency ![-1277, 4, 0])) = 1 / 4 := by
  have hqnorm : ‖vec3 (3 / 5) (4 / 5) 0‖ = 1 := by
    have h := norm_vec3_sq (3 / 5) (4 / 5) 0
    nlinarith [norm_nonneg (vec3 (3 / 5) (4 / 5) 0)]
  have hq : (ratio (1 / 2))⁻¹ • (vec3 1 0 0 + vec3 (-1277 / 1280) (1 / 320) 0) =
      vec3 (3 / 5) (4 / 5) 0 := by
    ext i
    fin_cases i <;> norm_num [ratio, vec3]
  have hscale : (1280 : ℝ)⁻¹ • pairEquiv.symm
      (realFrequency ![1280, 0, 0], realFrequency ![-1277, 4, 0]) =
        pairEquiv.symm (vec3 1 0 0, vec3 (-1277 / 1280) (1 / 320) 0) := by
    ext i
    fin_cases i <;> norm_num [pairEquiv, pairLinearEquiv, vec3, realFrequency]
  rw [hscale, physicalCutoff, pairEquiv.apply_symm_apply, hq,
    parameterCutoff_eq_one (1 / 2) (by constructor <;> norm_num),
    normalizedCutoff_eq_half_of_norm_eq_one _ norm_axis,
    normalizedCutoff_eq_half_of_norm_eq_one _ hqnorm]
  norm_num

private theorem pressure_entry_example :
    entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2 = (-192 / 40768625 : ℂ) := by
  rw [entry_pressurePairOperator]
  norm_num [CoherentPressurePair.tiltPair, CoherentPressurePair.tracePair, tiltSymbol,
    lineRemainder, cross, cross_apply, realFrequency, EuclideanSpace.norm_sq_eq,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-- An actual corrected periodic coefficient is nonzero, with both half-weights retained. -/
example : entry (UnitAddTorus.mFourierCoeff
    (periodicKernel 1280 (by norm_num) (1 / 2) (EuclideanSpace.single 0 1))
    (pairWavevector ![1280, 0, 0] ![-1277, 4, 0])) 1 2 2 = (-48 / 40768625 : ℂ) := by
  rw [mFourierCoeff_periodicKernel _ _ _ _ (by simp), cutoff_example]
  change ((1 / 4 : ℝ) : ℂ) * entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
    ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2 = _
  rw [pressure_entry_example]
  norm_num

/-- The nonzero coefficient acts with the same sign on actual Fourier monomials. -/
example : (kernelAction
    (periodicKernel 1280 (by norm_num) (1 / 2) (EuclideanSpace.single 0 1))
    (fun y ↦ UnitAddTorus.mFourier ![1280, 0, 0] y • EuclideanSpace.single 2 (1 : ℂ))
    (fun y ↦ UnitAddTorus.mFourier ![-1277, 4, 0] y • EuclideanSpace.single 2 (1 : ℂ)) 0) 1 =
      (-48 / 40768625 : ℂ) := by
  rw [kernelAction_monomials _ _ _ _ (by simp), cutoff_example]
  simp only [character_origin, mul_one, one_smul]
  change ((1 / 4 : ℝ) : ℂ) * entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
    ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2 = _
  rw [pressure_entry_example]
  norm_num

/-- Multiplying both inputs by the imaginary unit reverses this nonzero output. -/
example : (kernelAction
    (periodicKernel 1280 (by norm_num) (1 / 2) (EuclideanSpace.single 0 1))
    (fun y ↦ UnitAddTorus.mFourier ![1280, 0, 0] y •
      (Complex.I • EuclideanSpace.single 2 (1 : ℂ)))
    (fun y ↦ UnitAddTorus.mFourier ![-1277, 4, 0] y •
      (Complex.I • EuclideanSpace.single 2 (1 : ℂ))) 0) 1 = (48 / 40768625 : ℂ) := by
  rw [kernelAction_monomials _ _ _ _ (by simp), cutoff_example]
  simp only [character_origin, mul_one, one_mul, map_smul, smul_apply, smul_smul]
  change (((1 / 4 : ℝ) : ℂ) * (Complex.I * Complex.I)) *
    entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2 = _
  rw [pressure_entry_example]
  norm_num

/-- Summing the actual monomial actions removes only the output-annulus weight. -/
example : HasSum (fun n : ℕ ↦ (kernelAction
    (periodicKernel 1280 (by norm_num) (dyadicParameter n) (EuclideanSpace.single 0 1))
    (fun y ↦ UnitAddTorus.mFourier ![1280, 0, 0] y • EuclideanSpace.single 2 (1 : ℂ))
    (fun y ↦ UnitAddTorus.mFourier ![-1277, 4, 0] y • EuclideanSpace.single 2 (1 : ℂ)) 0) 1)
    (-96 / 40768625 : ℂ) := by
  have hsmall : ‖realFrequency ![1280, 0, 0] + realFrequency ![-1277, 4, 0]‖ ≤ (1280 : ℝ) / 256 := by
    have he : realFrequency ![1280, 0, 0] + realFrequency ![-1277, 4, 0] = vec3 3 4 0 := by
      ext i
      fin_cases i <;> norm_num [realFrequency, vec3]
    rw [he]
    have h := norm_vec3_sq 3 4 0
    nlinarith [norm_nonneg (vec3 3 4 0)]
  have hscale : (1280 : ℝ)⁻¹ • realFrequency ![1280, 0, 0] = vec3 1 0 0 := by
    ext i
    fin_cases i <;> norm_num [realFrequency, vec3]
  have h := (PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 3 ↦ ℂ) 1).hasSum
    (hasSum_kernelAction_monomials 1280 (by norm_num) (EuclideanSpace.single 0 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0] hsmall (EuclideanSpace.single 2 1)
      (EuclideanSpace.single 2 1) 0)
  simp only [hscale, normalizedCutoff_eq_half_of_norm_eq_one _ norm_axis,
    character_origin, mul_one, one_smul] at h
  have hvalue : (PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 3 ↦ ℂ) 1)
      (((1 / 2 : ℝ) : ℂ) • pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
        ![1280, 0, 0] ![-1277, 4, 0] (EuclideanSpace.single 2 1) (EuclideanSpace.single 2 1)) =
      (-96 / 40768625 : ℂ) := by
    change ((1 / 2 : ℝ) : ℂ) * entry (pressurePairOperator (EuclideanSpace.single 0 1) (by simp)
      ![1280, 0, 0] ![-1277, 4, 0]) 1 2 2 = _
    rw [pressure_entry_example]
    norm_num
  simpa only [hvalue, PiLp.proj_apply] using h

/-- No absolute summability of input Fourier coefficients is assumed here. -/
example (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1) (f g : C(T3, C3)) :
    Summable (fun n : ℕ ↦ action N hN (dyadicParameter n) e f g) :=
  summable_action N hN e he f g

/-- Opposite input waves give zero pressure output in the full band sum. -/
example (N : ℝ) (hN : 0 < N) (e : R3) (he : ‖e‖ = 1)
    (k : Wavevector) (u v : C3) (x : T3) :
    HasSum (fun n : ℕ ↦ kernelAction (periodicKernel N hN (dyadicParameter n) e)
      (fun y ↦ UnitAddTorus.mFourier k y • u) (fun y ↦ UnitAddTorus.mFourier (-k) y • v) x) 0 := by
  have hzero : realFrequency (0 : Wavevector) = 0 := by
    ext j
    simp [realFrequency]
  have hneg : realFrequency (-k) = -realFrequency k := by
    ext j
    simp [realFrequency]
  have hz : pressurePairOperator e he k (-k) u v = 0 := by
    rw [pressurePairOperator_apply, ComplexPressurePair.tiltPair,
      FourierPressureTraceSymbol.complexTiltSymbol, add_neg_cancel, hzero, tiltSymbol_zero]
    ext j
    simp [FourierPressureTraceSymbol.complexifyVector, PancakeFrequencyProjectorCommutator.coefficientVec]
  have h := hasSum_kernelAction_monomials N hN e he k (-k)
    (by simpa [hneg] using div_nonneg hN.le (by norm_num : (0 : ℝ) ≤ 256)) u v x
  simpa only [hz, smul_zero] using h

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicActionAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureIntegrableKernelAction.integrable_action_integrand
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureIntegrableKernelAction.kernelAction_congr_ae
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureIntegrableKernelAction.norm_kernelAction_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureIntegrableKernelAction.continuous_kernelAction
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureIntegrableKernelAction.kernelAction_localization
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureIntegrableKernelAction.norm_kernelAction_localization_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureIntegrableKernelAction.kernelAction_monomials
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicOperatorKernel.fourier_operatorKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicOperatorKernel.moment_operatorKernel_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicOperatorKernel.hasSum_fourier_operatorKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicOperatorKernel.exists_uniform_mass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicOperatorKernel.exists_uniform_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicOperatorKernel.exists_uniform_mass_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicOperatorKernel.exists_uniform_firstMoment_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization.measurable_periodicKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization.integrable_periodicKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization.mFourierCoeff_periodicKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization.integrable_moment_periodicKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization.hasSum_mFourierCoeff_periodicKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization.moment_periodicKernel_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization.exists_uniform_mass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization.exists_uniform_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization.exists_uniform_mass_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization.exists_uniform_firstMoment_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization.exists_uniform_twoInputMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPeriodization.exists_uniform_twoInputMoment_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAction.action_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAction.norm_action_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAction.exists_uniform_action_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAction.summable_action
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAction.exists_uniform_sumAction_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAction.hasSum_action_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAction.action_localization
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAction.hasSum_localization
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAction.kernelAction_monomials
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureDyadicAction.hasSum_kernelAction_monomials
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootIntegrableKernelBudget.norm_rootLocalization_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootIntegrableKernelBudget.norm_periodic_rootLocalization_le
