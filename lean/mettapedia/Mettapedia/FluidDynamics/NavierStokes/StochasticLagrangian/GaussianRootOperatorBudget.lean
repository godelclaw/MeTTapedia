import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootSpatialBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicLocalization

/-!
# Spatial budgets for the integrated Gaussian pressure operator

The localization residual is defined from the actual pressure kernel action,
not an abstract field satisfying a budget. Finite-family Minkowski transfers
the first-moment spatial estimate through the kernel integral. The resulting
operator norms are summable over output bands at each fixed input scale.
The vorticity supremum and squared-patch gradient energy remain explicit costs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootOperatorBudget

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeFrequencyProjectorCommutator FourierPressureTraceSymbol
open LocalLowDiffusionBudget LocalGaussianPressurePartition GaussianRootVorticity GaussianRootPartition
open GaussianSquaredRootTranslation GaussianRootEnvelope GaussianRootSpatialBudget
open PancakeBilinearPeriodization PressureDyadicPeriodization PressureLocalizationField
open PressureKernelAction (kernelAction)
open PressureDyadicLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def rootLocalizationAction (N : ℝ) (hN : 0 < N) (t gamma : ℝ)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) (x : T3) (i : ↑centers) : C3 :=
  let c := rootPatch gamma chi modes u centers tau i
  let w := fun y ↦ complexifyVector (fullVorticity u y)
  let K := periodicKernel N hN t (localDirection chi modes u i.1)
  ((c x : ℂ) * (c x : ℂ)) • kernelAction K w w x -
    kernelAction K (fun y ↦ (c y : ℂ) • w y) (fun y ↦ (c y : ℂ) • w y) x

def rootLocalizationActionNorm (N : ℝ) (hN : 0 < N) (t gamma : ℝ)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) : ℝ :=
  Real.sqrt (∫ x : T3, ∑ i : ↑centers,
    ‖rootLocalizationAction N hN t gamma chi modes u centers tau x i‖ ^ 2)

theorem rootLocalizationActionNorm_nonneg (N : ℝ) (hN : 0 < N) (t gamma : ℝ)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) :
    0 ≤ rootLocalizationActionNorm N hN t gamma chi modes u centers tau := Real.sqrt_nonneg _

theorem rootLocalizationAction_eq_integral (N : ℝ) (hN : 0 < N)
    (t gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (x : T3) (i : ↑centers) :
    rootLocalizationAction N hN t gamma chi modes u centers tau x i =
      ∫ q : T6, rootLocalizationIntegrand N hN t gamma chi modes u centers tau q x i := by
  have hw := continuous_fullVorticity u hu
  have hwc : Continuous (fun y ↦ complexifyVector (fullVorticity u y)) := by
    unfold complexifyVector coefficientVec
    fun_prop
  let w : C(T3, C3) := ⟨_, hwc⟩
  let c : C(T3, ℂ) := ⟨fun y ↦ (rootPatch gamma chi modes u centers tau i y : ℂ),
    Complex.continuous_ofReal.comp (continuous_rootPatch gamma hg chi modes u hu centers hc tau i)⟩
  let K := periodicKernel N hN t (localDirection chi modes u i.1)
  have hK : Integrable K := integrable_periodicKernel N hN t _
  change (c x * c x) • kernelAction K w w x -
    kernelAction K (fun y ↦ c y • w y) (fun y ↦ c y • w y) x =
      ∫ q : T6, localizationField w w c c q (K q) x
  rw [← ContinuousMap.integral_apply (integrable_localizationField K hK w w c c)]
  exact (integral_localizationField_apply K hK w w c c x).symm

theorem rootLocalizationActionNorm_le (N : ℝ) (hN : 0 < N)
    (t gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) :
    rootLocalizationActionNorm N hN t gamma chi modes u centers tau ≤
      ∫ q : T6, rootLocalizationSpatialNorm N hN t gamma chi modes u centers tau q := by
  have hw := continuous_fullVorticity u hu
  have hwc : Continuous (fun y ↦ complexifyVector (fullVorticity u y)) := by
    unfold complexifyVector coefficientVec
    fun_prop
  let w : C(T3, C3) := ⟨_, hwc⟩
  let c : ↑centers → C(T3, ℂ) := fun i ↦
    ⟨fun y ↦ (rootPatch gamma chi modes u centers tau i y : ℂ),
      Complex.continuous_ofReal.comp (continuous_rootPatch gamma hg chi modes u hu centers hc tau i)⟩
  exact finite_localization_spatial_norm_le
    (fun i : ↑centers ↦ periodicKernel N hN t (localDirection chi modes u i.1))
    (fun i ↦ integrable_periodicKernel N hN t _) w w c c

/-- Uniform kernel constant, with the actual field-size and geometry costs retained. -/
theorem exists_uniform_operator_budget_for_fullVorticity :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ gamma : ℝ, 0 < gamma → ∀ chi : Wavevector → ℂ, ∀ modes : Finset Wavevector,
      ∀ u : FourierVelocity, ∀ hu : Summable (fourierMoment 2 u),
      ∀ centers : Finset T3, centers.Nonempty → ∀ tau : ℝ,
      let w : C(T3, R3) := ⟨fullVorticity u, continuous_fullVorticity u
        (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu)⟩
      Summable (fun n : ℕ ↦ rootLocalizationActionNorm N hN
        (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau) ∧
      (∑' n : ℕ, rootLocalizationActionNorm N hN
        (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau) ≤
        (C / N) * (‖w‖ ^ 2 * Real.sqrt (6 *
          ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x)) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_spatial_budget_for_fullVorticity
  refine ⟨C, hC, ?_⟩
  intro N hN gamma hg chi modes u hu centers hc tau
  obtain ⟨_, hs, hb⟩ := h N hN gamma hg chi modes u hu centers hc tau
  have hn (n : ℕ) := rootLocalizationActionNorm_le N hN
    (PressureLowOutputDyadicBudget.dyadicParameter n) gamma hg chi modes u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau
  have ha := hs.of_nonneg_of_le
    (fun n ↦ rootLocalizationActionNorm_nonneg N hN
      (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau) hn
  exact ⟨ha, (ha.tsum_le_tsum hn hs).trans hb⟩

def complexVorticityField (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) : C(T3, C3) :=
  ⟨fun x ↦ complexifyVector (fullVorticity u x), by
    have hw := continuous_fullVorticity u hu
    unfold complexifyVector coefficientVec
    fun_prop⟩

def complexRootPatch (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (i : ↑centers) : C(T3, ℂ) :=
  ⟨fun x ↦ (rootPatch gamma chi modes u centers tau i x : ℂ),
    Complex.continuous_ofReal.comp (continuous_rootPatch gamma hg chi modes u hu centers hc tau i)⟩

def rootLocalizationSumAction (N : ℝ) (hN : 0 < N) (gamma : ℝ)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) (x : T3) (i : ↑centers) : C3 :=
  ∑' n : ℕ, rootLocalizationAction N hN (PressureLowOutputDyadicBudget.dyadicParameter n)
    gamma chi modes u centers tau x i

theorem hasSum_rootLocalizationAction (N : ℝ) (hN : 0 < N)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (x : T3) (i : ↑centers) :
    HasSum (fun n : ℕ ↦ rootLocalizationAction N hN
      (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau x i)
      (sumLocalizationAction N hN (localDirection chi modes u i.1)
        (complexVorticityField u hu) (complexVorticityField u hu)
        (complexRootPatch gamma hg chi modes u hu centers hc tau i)
        (complexRootPatch gamma hg chi modes u hu centers hc tau i) x) :=
  (ContinuousMap.evalCLM ℂ x).hasSum (hasSum_localizationAction N hN _
    (PancakeSpectralFiniteDifference.topVector_norm _)
    (complexVorticityField u hu) (complexVorticityField u hu)
    (complexRootPatch gamma hg chi modes u hu centers hc tau i)
    (complexRootPatch gamma hg chi modes u hu centers hc tau i))

/-- The pointwise series is the localization of the already constructed
continuous-field pressure sum; its value is not a nonsummable-series default. -/
theorem rootLocalizationSumAction_eq (N : ℝ) (hN : 0 < N)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (x : T3) (i : ↑centers) :
    rootLocalizationSumAction N hN gamma chi modes u centers tau x i =
      sumLocalizationAction N hN (localDirection chi modes u i.1)
        (complexVorticityField u hu) (complexVorticityField u hu)
        (complexRootPatch gamma hg chi modes u hu centers hc tau i)
        (complexRootPatch gamma hg chi modes u hu centers hc tau i) x :=
  (hasSum_rootLocalizationAction N hN gamma hg chi modes u hu centers hc tau x i).tsum_eq

theorem rootLocalizationSumAction_spatial_norm_le (N : ℝ) (hN : 0 < N)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ)
    (hs : Summable (fun n : ℕ ↦ rootLocalizationActionNorm N hN
      (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau)) :
    Real.sqrt (∫ x : T3, ∑ i : ↑centers,
      ‖rootLocalizationSumAction N hN gamma chi modes u centers tau x i‖ ^ 2) ≤
      ∑' n : ℕ, rootLocalizationActionNorm N hN
        (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau := by
  simp_rw [rootLocalizationSumAction_eq N hN gamma hg chi modes u hu centers hc tau]
  exact finite_sumLocalization_spatial_norm_le N hN
    (fun i : ↑centers ↦ localDirection chi modes u i.1)
    (fun i ↦ PancakeSpectralFiniteDifference.topVector_norm _)
    (complexVorticityField u hu) (complexVorticityField u hu)
    (complexRootPatch gamma hg chi modes u hu centers hc tau)
    (complexRootPatch gamma hg chi modes u hu centers hc tau) hs

/-- The same inverse-scale budget controls the actual complete output-band
sum. No input-scale sum or dynamical bound is asserted. -/
theorem exists_uniform_sum_operator_budget_for_fullVorticity :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ gamma : ℝ, 0 < gamma → ∀ chi : Wavevector → ℂ, ∀ modes : Finset Wavevector,
      ∀ u : FourierVelocity, ∀ hu : Summable (fourierMoment 2 u),
      ∀ centers : Finset T3, centers.Nonempty → ∀ tau : ℝ,
      let w : C(T3, R3) := ⟨fullVorticity u, continuous_fullVorticity u
        (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu)⟩
      Real.sqrt (∫ x : T3, ∑ i : ↑centers,
        ‖rootLocalizationSumAction N hN gamma chi modes u centers tau x i‖ ^ 2) ≤
        (C / N) * (‖w‖ ^ 2 * Real.sqrt (6 *
          ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x)) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_operator_budget_for_fullVorticity
  refine ⟨C, hC, ?_⟩
  intro N hN gamma hg chi modes u hu centers hc tau
  obtain ⟨hs, hb⟩ := h N hN gamma hg chi modes u hu centers hc tau
  exact (rootLocalizationSumAction_spatial_norm_le N hN gamma hg chi modes u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau hs).trans hb

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootOperatorBudget
