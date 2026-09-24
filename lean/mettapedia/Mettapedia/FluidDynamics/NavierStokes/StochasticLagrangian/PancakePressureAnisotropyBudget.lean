import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLowPressureBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralDefectEvolution

/-!
# Spatial pressure anisotropy paid by physical energy

The low-pressure amplitude envelope is connected to the actual quadratic
anisotropy of the reconstructed pressure Hessian. Finite Parseval converts
the spatial receiver norm to the physical coefficient enstrophy, with no
receiver-cardinality factor. Complex amplitudes are regarded as a real
Hilbert space; real-valued fields are a special case, not an assumption
needed for this upper bound.

This controls low pressure output frequencies only. It does not assert a
uniform estimate as that output cutoff tends to infinity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePressureAnisotropyBudget

open scoped BigOperators RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy
open PancakeViscousMisalignmentAbsorption PancakeLowPressureBudget
open PancakeSpectralDefectEvolution PancakeArbitraryDataBlocks

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def pressureAnisotropyDensity (outputs modes : Finset Wavevector) (u : FourierVelocity)
    (e : T3 → C3) (x : T3) : ℝ :=
  remainderAnisotropy ((pressureHessianField outputs modes u x).restrictScalars ℝ)
    (e x) (coefficientVec (finiteFourierReconstruction modes (fourierCurl u) x))

theorem abs_pressureAnisotropyDensity_le (outputs modes : Finset Wavevector)
    (u : FourierVelocity) (e : T3 → C3) (x : T3) (he : ‖e x‖ = 1) :
    |pressureAnisotropyDensity outputs modes u e x| ≤
      2 * pressureHessianAmplitude outputs modes u *
        ‖coefficientVec (finiteFourierReconstruction modes (fourierCurl u) x)‖ ^ 2 := by
  apply (abs_remainderAnisotropy_le _ _ _ he).trans
  rw [ContinuousLinearMap.norm_restrictScalars]
  gcongr
  exact norm_pressureHessianField_le_amplitude outputs modes u x

theorem continuous_pressureHessianField (outputs modes : Finset Wavevector)
    (u : FourierVelocity) : Continuous (pressureHessianField outputs modes u) := by
  unfold pressureHessianField
  fun_prop

theorem continuous_coefficientReconstruction (modes : Finset Wavevector)
    (w : FourierVelocity) : Continuous (fun x : T3 ↦
      coefficientVec (finiteFourierReconstruction modes w x)) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℂ)).comp
    (continuous_finiteFourierReconstruction modes w)

theorem integral_norm_coefficientReconstruction_sq (modes : Finset Wavevector)
    (w : FourierVelocity) :
    (∫ x : T3, ‖coefficientVec (finiteFourierReconstruction modes w x)‖ ^ 2) =
      fullEnergy modes w := by
  simp_rw [norm_coefficientVec_sq]
  simpa only [coefficientEnergy, Fin.sum_univ_three,
    PancakeMisalignmentEnergyBridge.complexEuclideanNormSq, fullEnergy] using
    integral_complexEuclideanNormSq_finiteFourierReconstruction modes w

theorem integrable_pressureAnisotropyEnvelope (outputs modes : Finset Wavevector)
    (u : FourierVelocity) : Integrable (fun x : T3 ↦
      2 * pressureHessianAmplitude outputs modes u *
        ‖coefficientVec (finiteFourierReconstruction modes (fourierCurl u) x)‖ ^ 2) := by
  exact (continuous_const.mul
    ((continuous_coefficientReconstruction modes (fourierCurl u)).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem aestronglyMeasurable_pressureAnisotropyDensity (outputs modes : Finset Wavevector)
    (u : FourierVelocity) (e : T3 → C3) (he : AEStronglyMeasurable e) :
    AEStronglyMeasurable (pressureAnisotropyDensity outputs modes u e) := by
  have hH : AEStronglyMeasurable (fun x : T3 ↦
      (pressureHessianField outputs modes u x).restrictScalars ℝ) := by
    apply Continuous.aestronglyMeasurable
    exact (ContinuousLinearMap.restrictScalarsIsometry ℂ C3 C3 ℝ ℝ).continuous.comp
      (continuous_pressureHessianField outputs modes u)
  have hw : AEStronglyMeasurable (fun x : T3 ↦
      coefficientVec (finiteFourierReconstruction modes (fourierCurl u) x)) :=
    (continuous_coefficientReconstruction modes (fourierCurl u)).aestronglyMeasurable
  have happly : Continuous (fun p : (C3 →L[ℝ] C3) × C3 ↦ p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact ((he.inner (happly.comp_aestronglyMeasurable (hH.prodMk he))).mul (hw.norm.pow 2)).sub
    (hw.inner (happly.comp_aestronglyMeasurable (hH.prodMk hw)))

/-- No continuity of the chosen direction is needed. Measurability and
unit norm suffice, including direction choices across eigenvalue collisions. -/
theorem integrable_pressureAnisotropyDensity (outputs modes : Finset Wavevector)
    (u : FourierVelocity) (e : T3 → C3) (hem : AEStronglyMeasurable e)
    (he : ∀ x, ‖e x‖ = 1) :
    Integrable (pressureAnisotropyDensity outputs modes u e) := by
  apply (integrable_pressureAnisotropyEnvelope outputs modes u).mono'
    (aestronglyMeasurable_pressureAnisotropyDensity outputs modes u e hem)
  exact Filter.Eventually.of_forall (fun x ↦ by
    simpa only [Real.norm_eq_abs] using abs_pressureAnisotropyDensity_le outputs modes u e x (he x))

/-- The space integral of absolute pressure anisotropy is bounded by the
previously constructed cost, with Parseval accounting for all receivers. -/
theorem integral_abs_pressureAnisotropyDensity_le (outputs modes : Finset Wavevector)
    (u : FourierVelocity) (e : T3 → C3) (he : ∀ x, ‖e x‖ = 1) :
    (∫ x : T3, |pressureAnisotropyDensity outputs modes u e x|) ≤
      lowPressureCost outputs modes u := by
  have hm := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x : T3 ↦ abs_nonneg
      (pressureAnisotropyDensity outputs modes u e x)))
    (integrable_pressureAnisotropyEnvelope outputs modes u)
    (Filter.Eventually.of_forall (fun x ↦ abs_pressureAnisotropyDensity_le outputs modes u e x (he x)))
  rw [integral_const_mul, integral_norm_coefficientReconstruction_sq] at hm
  exact hm

/-- Physical energy pays the space-time low-pressure anisotropy. Time
measurability is explicit, but its integrability and bound are conclusions,
not separately assumed dynamical budgets. -/
theorem spacetime_pressureAnisotropy_of_velocityRHS
    (outputs modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (e : ℝ → T3 → C3) (nu T : ℝ) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, u t (-k) = PancakeBlockReality.coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t)
    (hen : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, ‖e t x‖ = 1)
    (hem : AEStronglyMeasurable (fun t ↦
      ∫ x : T3, |pressureAnisotropyDensity outputs modes (u t) (e t) x|)
        (volume.restrict (Set.Icc (0 : ℝ) T))) :
    IntervalIntegrable (fun t ↦
      ∫ x : T3, |pressureAnisotropyDensity outputs modes (u t) (e t) x|) volume 0 T ∧
    (∫ t in (0 : ℝ)..T, ∫ x : T3,
      |pressureAnisotropyDensity outputs modes (u t) (e t) x|) ≤
        pressureCutoffWeight outputs * fullEnergy modes (u 0) ^ 2 / nu := by
  have hc := continuousOn_coefficients_of_velocityRHS modes u nu (Set.Icc 0 T) he
  have hP := continuousOn_pressureHessianAmplitude outputs modes u (Set.Icc 0 T) hc
  have hO := continuousOn_enstrophy_of_velocityRHS modes u nu (Set.Icc 0 T) he
  have hcost : IntervalIntegrable (fun t ↦ lowPressureCost outputs modes (u t)) volume 0 T :=
    ContinuousOn.intervalIntegrable_of_Icc hT ((continuousOn_const.mul hP).mul hO)
  have hp : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ x : T3, |pressureAnisotropyDensity outputs modes (u t) (e t) x|) ≤
        lowPressureCost outputs modes (u t) := fun t ht ↦
    integral_abs_pressureAnisotropyDensity_le outputs modes (u t) (e t) (hen t ht)
  have hg : IntervalIntegrable (fun t ↦
      ∫ x : T3, |pressureAnisotropyDensity outputs modes (u t) (e t) x|) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT] at hcost ⊢
    apply hcost.mono' hem
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x ↦ abs_nonneg _))]
    exact hp t ht
  refine ⟨hg, ?_⟩
  exact (intervalIntegral.integral_mono_on hT hg hcost hp).trans
    (lowPressureCost_integral_of_velocityRHS outputs modes u nu T hnu hT hs hr hu he)

end Mettapedia.FluidDynamics.NavierStokes.PancakePressureAnisotropyBudget
