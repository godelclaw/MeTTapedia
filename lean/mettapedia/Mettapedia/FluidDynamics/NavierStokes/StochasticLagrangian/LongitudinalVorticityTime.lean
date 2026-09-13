import Mettapedia.Analysis.ContinuousFieldBilinear
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalCurvatureWork

/-!
# Time differentiation of the actual longitudinal field

The vorticity and its first spatial jet are differentiated in the uniform
continuous-field norm. Bilinear calculus and the continuous map into spatial
`L²` then differentiate the actual longitudinal energy. A common fourth
absolute Fourier moment justifies these operations, not a global budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LongitudinalVorticityTime

open scoped Topology RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis ContinuousFieldBilinear
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative PancakeInfiniteFourierTime
open PancakeInfiniteSpatialLaplacian PancakeInfiniteRealCurl PancakeGalerkinKineticEnergy
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeCoefficientLimitEquation
open PancakeLocalInfiniteVelocity PancakeInfiniteVelocityEnvelope PancakeFourierMaterialPaths
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityGradientEvolution
open LocalVorticityTime LocalVorticityDiffusion LocalWeightedCurlCancellation
open FullVorticityGradientTransport LocalLongitudinalVorticity LongitudinalCurvatureWork
open PancakePeriodicVorticityEquation PancakePeriodicComplexStretch

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def realField (u : FourierVelocity) : C(T3, R3) :=
  (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3) (fullFourierField id u)

def vorticityField (u : FourierVelocity) : C(T3, R3) := realField (fourierCurl u)

def gradientField (u : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  realField (indexedDerivativeCoeff id j (fourierCurl u))

def componentField (j : Fin 3) : C(T3, R3) →L[ℝ] C(T3, ℝ) :=
  (EuclideanSpace.proj j).compLeftContinuous ℝ T3

def longitudinalField (u : FourierVelocity) : C(T3, R3) :=
  ∑ j, pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (gradientField u j)

def eulerianRateField (ν : ℝ) (u : FourierVelocity) : C(T3, R3) :=
  ∑ j, (pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (gradientField (infiniteVelocityRHS ν u) j) +
      pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
        (componentField j (vorticityField (infiniteVelocityRHS ν u))) (gradientField u j))

def eulerianRate (ν : ℝ) (u : FourierVelocity) (x : T3) : R3 :=
  LongitudinalJetEvolution.rate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (realField (fourierCurl (infiniteVelocityRHS ν u)) x)
    (fun j ↦ fullCurlGradient (infiniteVelocityRHS ν u) j x)

def meanEnergy (u : FourierVelocity) : ℝ := ∫ x : T3, ‖longitudinalVorticity u x‖ ^ 2

def eulerianWork (ν : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ⟪longitudinalVorticity u x, eulerianRate ν u x⟫

theorem vorticityField_apply (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (x : T3) :
    vorticityField u x = fullVorticity u x := by
  rw [fullVorticity_eq_realFullField u hu]
  rfl

theorem gradientField_apply (u : FourierVelocity) (j : Fin 3) (x : T3) :
    gradientField u j x = fullCurlGradient u j x := rfl

theorem componentField_apply (j : Fin 3) (f : C(T3, R3)) (x : T3) :
    componentField j f x = f x j := rfl

theorem longitudinalField_apply (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) :
    longitudinalField u x = longitudinalVorticity u x := by
  simp only [longitudinalField, ContinuousMap.sum_apply, pointwise, ContinuousMap.coe_mk,
    ContinuousLinearMap.lsmul_apply, componentField_apply,
    vorticityField_apply u hu, gradientField_apply,
    longitudinalVorticity, LongitudinalJetEvolution.longitudinal]

theorem eulerianRateField_apply (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (x : T3) :
    eulerianRateField ν u x = eulerianRate ν u x := by
  simp only [eulerianRateField, ContinuousMap.sum_apply, ContinuousMap.add_apply,
    pointwise, ContinuousMap.coe_mk, ContinuousLinearMap.lsmul_apply, componentField_apply,
    vorticityField_apply u hu, gradientField_apply,
    eulerianRate, LongitudinalJetEvolution.rate, Finset.sum_add_distrib]
  exact add_comm _ _

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)

include hg hSum hu in
theorem hasDerivAt_gradientField (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ gradientField (s.coefficients τ) j)
      (gradientField (infiniteVelocityRHS ν (s.coefficients t)) j) t := by
  have hfield : HasDerivAt
      (fun τ ↦ fullFourierField id (indexedDerivativeCoeff id j (fourierCurl (s.coefficients τ))))
      (fullFourierField id (indexedDerivativeCoeff id j
        (fourierCurl (infiniteVelocityRHS ν (s.coefficients t))))) t := by
    apply hasDerivAt_fullFourierField_time
      (fun τ ↦ indexedDerivativeCoeff id j (fourierCurl (s.coefficients τ)))
      (fun τ ↦ indexedDerivativeCoeff id j (fourierCurl (infiniteVelocityRHS ν (s.coefficients τ))))
      (Set.Ioo (0 : ℝ) T) isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
      (fun q ↦ (2 * Real.pi) ^ 2 * velocityEnvelope ν g q)
      ((summable_velocityEnvelope ν g hg hSum).mul_left _)
    · intro τ hτ q i
      simpa only [indexedDerivativeCoeff, Pi.smul_apply, smul_eq_mul, id_eq] using
        (PancakeGalerkinVorticityBridge.hasDerivAt_fourierCurl s.coefficients _ τ q
          (s.equation τ hτ q) i).const_mul (unitTorusDerivativePhase * (q j : ℂ))
    · intro τ hτ q
      exact norm_gradientCurl_velocityRHS_le ν _ g hg hSum (hu τ ⟨hτ.1.le, hτ.2.le⟩) j q
    · exact ht
    · have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
      have hd := summable_fourierMoment_derivative 1 (fourierCurl (s.coefficients t))
        (summable_fourierMoment_curl 2 _ (summable_fourierMoment_of_le _ (by omega : 3 ≤ 4) hm)) j
      exact summable_norm_coefficients id _ (by simpa only [indexedFirstMoment_id] using hd)
  exact (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).hasFDerivAt.comp_hasDerivAt t hfield

include hg hSum hu in
theorem hasDerivAt_vorticityField (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ vorticityField (s.coefficients τ))
      (vorticityField (infiniteVelocityRHS ν (s.coefficients t))) t :=
  (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).hasFDerivAt.comp_hasDerivAt t
    (fullCurlField_hasDerivAt s g hg hSum
      (fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ hτ q)) t ht)

include hg hSum hu in
theorem hasDerivAt_longitudinalField (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ longitudinalField (s.coefficients τ))
      (eulerianRateField ν (s.coefficients t)) t := by
  have ha := hasDerivAt_vorticityField s g hg hSum hu t ht
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦
    hasDerivAt_pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
      ((componentField j).hasFDerivAt.comp_hasDerivAt t ha)
      (hasDerivAt_gradientField s g hg hSum hu j t ht))

include hg hSum hu in
theorem hasDerivAt_meanEnergy (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ meanEnergy (s.coefficients τ)) (2 * eulerianWork ν (s.coefficients t)) t := by
  have hm (τ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) T) : Summable (fourierMoment 1 (s.coefficients τ)) :=
    summable_fourierMoment_of_le _ (by omega : 1 ≤ 4)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ ⟨hτ.1.le, hτ.2.le⟩))
  have h := hasDerivAt_integral_norm_sq (volume : Measure T3)
    (hasDerivAt_longitudinalField s g hg hSum hu t ht)
  simp only [longitudinalField_apply _ (hm t ht), eulerianRateField_apply ν _ (hm t ht)] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
  simp only [meanEnergy, longitudinalField_apply _ (hm τ hτ)]

include hSum hu in
theorem continuous_vorticityField :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ vorticityField (s.coefficients t)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hm (t : Set.Icc (0 : ℝ) T) : Summable (fourierMoment 1 (s.coefficients t)) :=
    summable_fourierMoment_of_le _ (by omega : 1 ≤ 4)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t t.2))
  change Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ vorticityField (s.coefficients z.1) z.2)
  simp_rw [vorticityField_apply _ (hm _)]
  exact continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 4) q).trans (hu t ht q))

include hSum hu in
theorem continuous_gradientField (j : Fin 3) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ gradientField (s.coefficients t) j) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact LocalVorticityEighthMoment.continuous_fullCurlGradient_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t ht q)) j

include hSum hu in
theorem continuous_longitudinalField :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ longitudinalField (s.coefficients t)) := by
  apply continuous_finsetSum
  intro j _
  exact ((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp
    ((componentField j).continuous.comp (continuous_vorticityField s g hSum hu))).clm_apply
      (continuous_gradientField s g hSum hu j)

include hg hSum hu in
theorem continuous_vorticityRHSField (hB : 0 ≤ B) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      vorticityField (infiniteVelocityRHS ν (s.coefficients t))) := by
  apply (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).continuous.comp
  refine continuous_fullFourierField_of_norm_le _ ?_ (fun q ↦ (2 * Real.pi) * velocityEnvelope ν g q)
    ((summable_velocityEnvelope ν g hg hSum).mul_left _) ?_
  · intro q i
    have hc := continuous_velocityRHS_component s hB q
    fin_cases i <;> simp only [fourierCurl, coefficientCross, Pi.smul_apply, smul_eq_mul] <;> fun_prop
  · intro t q
    exact norm_curl_velocityRHS_le ν _ g hg hSum
      (fun q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t t.2 q)) q

include hg hSum hu in
theorem continuous_gradientRHSField (hB : 0 ≤ B) (j : Fin 3) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      gradientField (infiniteVelocityRHS ν (s.coefficients t)) j) := by
  apply (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).continuous.comp
  refine continuous_fullFourierField_of_norm_le _ ?_
    (fun q ↦ (2 * Real.pi) ^ 2 * velocityEnvelope ν g q)
    ((summable_velocityEnvelope ν g hg hSum).mul_left _) ?_
  · intro q i
    have hc := continuous_velocityRHS_component s hB q
    fin_cases i <;> simp only [indexedDerivativeCoeff, fourierCurl, coefficientCross,
      Pi.smul_apply, smul_eq_mul] <;> fun_prop
  · intro t q
    exact norm_gradientCurl_velocityRHS_le ν _ g hg hSum (hu t t.2) j q

include hg hSum hu in
theorem continuous_eulerianRateField (hB : 0 ≤ B) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ eulerianRateField ν (s.coefficients t)) := by
  apply continuous_finsetSum
  intro j _
  apply Continuous.add
  · exact ((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp
      ((componentField j).continuous.comp (continuous_vorticityField s g hSum hu))).clm_apply
        (continuous_gradientRHSField s g hg hSum hu hB j)
  · exact ((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp
      ((componentField j).continuous.comp (continuous_vorticityRHSField s g hg hSum hu hB))).clm_apply
        (continuous_gradientField s g hSum hu j)

include hSum hu in
theorem continuous_meanEnergy : ContinuousOn (fun t ↦ meanEnergy (s.coefficients t)) (Set.Icc 0 T) := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun t : Set.Icc (0 : ℝ) T ↦ meanEnergy (s.coefficients t))
  have h := ((ContinuousMap.toLp 2 (volume : Measure T3) ℝ).continuous.comp
    (continuous_longitudinalField s g hSum hu)).norm.pow 2
  have hm (t : Set.Icc (0 : ℝ) T) : Summable (fourierMoment 1 (s.coefficients t)) :=
    summable_fourierMoment_of_le _ (by omega : 1 ≤ 4)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t t.2))
  simpa only [Function.comp_def, ContinuousFieldMinkowski.norm_toL2_sq,
    longitudinalField_apply _ (hm _), meanEnergy] using h

include hg hSum hu in
theorem continuous_eulerianWork (hB : 0 ≤ B) :
    ContinuousOn (fun t ↦ eulerianWork ν (s.coefficients t)) (Set.Icc 0 T) := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun t : Set.Icc (0 : ℝ) T ↦ eulerianWork ν (s.coefficients t))
  have h := ((ContinuousMap.toLp 2 (volume : Measure T3) ℝ).continuous.comp
    (continuous_longitudinalField s g hSum hu)).inner (𝕜 := ℝ)
      ((ContinuousMap.toLp 2 (volume : Measure T3) ℝ).continuous.comp
        (continuous_eulerianRateField s g hg hSum hu hB))
  have hm (t : Set.Icc (0 : ℝ) T) : Summable (fourierMoment 1 (s.coefficients t)) :=
    summable_fourierMoment_of_le _ (by omega : 1 ≤ 4)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t t.2))
  simpa only [Function.comp_def, ContinuousFieldInnerProduct.inner_toLp,
    longitudinalField_apply _ (hm _), eulerianRateField_apply ν _ (hm _), eulerianWork] using h

include hg hSum hu in
theorem meanEnergy_eq_initial_add_integral (hB : 0 ≤ B) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    meanEnergy (s.coefficients t) = meanEnergy u₀ + 2 * ∫ τ in (0 : ℝ)..t,
      eulerianWork ν (s.coefficients τ) := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hi : IntervalIntegrable (fun τ ↦ eulerianWork ν (s.coefficients τ)) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1
      ((continuous_eulerianWork s g hg hSum hu hB).mono hsub)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    ((continuous_meanEnergy s g hSum hu).mono hsub)
    (fun τ hτ ↦ hasDerivAt_meanEnergy s g hg hSum hu τ ⟨hτ.1, hτ.2.trans_le ht.2⟩)
    (hi.const_mul 2)
  rw [intervalIntegral.integral_const_mul] at h
  rw [s.initial] at h
  linarith

end Mettapedia.FluidDynamics.NavierStokes.LongitudinalVorticityTime
