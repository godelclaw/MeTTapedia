import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteSpatialPressure

/-!
# The actual local velocity-pressure Navier--Stokes equation

The same local infinite velocity has a real, zero-mean scalar pressure.
The ordinary time derivative equals negative physical advection, negative
ordinary pressure gradient, and the viscous spatial Laplacian.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalPressureEquation

open scoped BigOperators ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian
open PancakeInfiniteFourierTime PancakeIndexedFourierMoments PancakeCurlOutputTail
open PancakeCoefficientLimitEquation PancakeInfinitePressureCoefficients PancakeInfiniteSpatialPressure
open PancakeLocalProjectedEquation PancakePhysicalConvectionCoefficients PancakePeriodicVorticityEquation
open PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity PancakeHigherLocalVelocity
open PancakeArbitraryDataBlocks PancakeContinuousCoordinateJet
open PancakeFourierTranslationCurve

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fullFourierField_sub (u v : FourierVelocity)
    (hu : Summable (fun q ↦ ‖u q‖)) (hv : Summable (fun q ↦ ‖v q‖)) :
    fullFourierField id (fun q ↦ u q - v q) = fullFourierField id u - fullFourierField id v := by
  have he (q : Wavevector) :
      modeField q (u q - v q) = modeField q (u q) - modeField q (v q) :=
    (modeFieldCLM q).map_sub _ _
  simp only [fullFourierField, id_eq, he]
  exact (summable_modeField id u hu).tsum_sub (summable_modeField id v hv)

theorem fullVelocityRHS_eq_spatial_pressure (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    fullFourierField id (infiniteVelocityRHS nu u) x =
      -spatialAdvection (fullFourierField id u) x -
        spatialGradient (spatialPressure u) x +
          (nu : ℂ) • spatialLaplacian (fullFourierField id u) x := by
  have hc : Summable (fun q ↦ ‖infiniteConvection u q‖) :=
    (summable_norm_infiniteConvection u hu).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun _ ↦ norm_coefficient_sup_le_euclidean _)
  have hn : Summable (fun q ↦ ‖(-unitTorusDerivativePhase) • infiniteConvection u q‖) := by
    simpa only [norm_smul] using hc.mul_left ‖-unitTorusDerivativePhase‖
  have hp := summable_norm_infinitePressureGradient u hu
  have hsub : Summable (fun q ↦ ‖(-unitTorusDerivativePhase) • infiniteConvection u q -
      infinitePressureGradientCoeff u q‖) :=
    (hn.of_norm.sub hp.of_norm).norm
  have he :
      (fun q ↦ (-unitTorusDerivativePhase) • infiniteConvection u q) =
        fun q ↦ (-1 : ℂ) • (unitTorusDerivativePhase • infiniteConvection u q) := by
    funext q
    simp only [smul_smul, neg_one_mul]
  have hdec := funext (infiniteVelocityRHS_pressure_decomposition nu u)
  rw [hdec, fullFourierField_add _ _ hsub (summable_norm_viscous nu u hu),
    fullFourierField_sub _ _ hn hp]
  simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply]
  rw [he, fullFourierField_smul]
  simp only [neg_one_smul, ContinuousMap.neg_apply]
  rw [fullFourierField_advection u hu hd, ← spatialGradient_spatialPressure u hu,
    fullFourierField_viscous nu u hu x]

theorem spatialField_pressure_equation {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ τ, τ ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 2 (s.coefficients τ) k ≤ g k)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    HasDerivAt (fun τ ↦ spatialField s τ x)
      (-spatialAdvection (spatialField s t) x -
        spatialGradient (spatialPressure (s.coefficients t)) x +
          (nu : ℂ) • spatialLaplacian (spatialField s t) x) t := by
  have hm : Summable (fourierMoment 2 (s.coefficients t)) :=
    hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  have h := spatialField_hasDerivAt_pointwise s g hg hSum hu t ht x
  rwa [fullVelocityRHS_eq_spatial_pressure nu _ hm (s.transverse t) x] at h

/-- Physical initial data construct the same local real velocity and its
real zero-mean pressure satisfying the ordinary spatial momentum equation. -/
theorem exists_physical_local_pressure_equation (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 8 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
        ⇑(spatialField s 0) = f ∧
        (∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ x i,
          conj (spatialField s t x i) = spatialField s t x i) ∧
        (∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ x, spatialDivergence (spatialField s t) x = 0) ∧
        (∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ x,
          conj (spatialPressure (s.coefficients t) x) = spatialPressure (s.coefficients t) x) ∧
        (∀ t, t ∈ Set.Icc (0 : ℝ) T →
          (∫ x : T3, spatialPressure (s.coefficients t) x) = 0) ∧
        ∀ t, t ∈ Set.Ioo (0 : ℝ) T → ∀ x,
          HasDerivAt (fun τ ↦ spatialField s τ x)
            (-spatialAdvection (spatialField s t) x -
              spatialGradient (spatialPressure (s.coefficients t)) x +
                (nu : ℂ) • spatialLaplacian (spatialField s t) x) t := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 2 nu hnu f hf hr hd hzero
  have hc (i : Fin 3) : Continuous (fun x ↦ f x i) := by
    simpa only [coordinateJet_zero] using (hf i).1 0 0 (by omega)
  have hm (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      Summable (fourierMoment 2 (s.coefficients t)) :=
    hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)
  refine ⟨T, hT, B, hB, s, spatialField_initial hT.le f hc s, spatialField_reality s,
    fun t ht x ↦ ?_, fun t ht x ↦ ?_, fun t ht ↦ ?_,
    spatialField_pressure_equation s g hg hSum hu⟩
  · exact spatialDivergence_fullFourierField _ (hm t ht) (s.transverse t) x
  · exact spatialPressure_reality _ (hm t ht) (s.reality t) x
  · exact spatialPressure_mean_zero _ (hm t ht)

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalPressureEquation
