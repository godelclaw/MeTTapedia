import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalVorticityTime

/-!
# Actual longitudinal energy balance

The Eulerian derivative is matched to the material rate and the transport
work vanishes by incompressibility. Both remaining signed fluxes are retained.
The local Fourier regularity hypotheses justify the identities; they do not
provide an initial-data bound for the fluxes.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LongitudinalEnergyBalance

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative PancakeInfiniteSpatialLaplacian
open PancakeInfiniteRealCurl PancakeGalerkinKineticEnergy PancakeDyadicDirectionEvolution
open PancakeTransverseEnergyFreezing PancakeCoefficientLimitEquation PancakeInfiniteVelocityEnvelope
open PancakeFourierMaterialPaths PancakePeriodicVorticityEquation PancakeLocalProjectedEquation
open PancakeGalerkinVorticityBridge PancakeInfiniteSpatialCurl PancakeFourierTranslationCurve
open PancakeHaarTransportRate PancakeLocalInfiniteVelocity
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityGradientEvolution
open LocalVorticityTime LocalVorticityDiffusion LocalWeightedCurlCancellation LocalJointDiffusionBudget
open FullVorticityGradientTransport LocalLongitudinalVorticity LongitudinalCurvatureWork
open LongitudinalVorticityTime LongitudinalVorticityDiffusion LocalAlignmentForcing
open FullLambVector SpatialVorticityInviscidRate LocalProjectionTransport LocalHelicityCenterEvolution
open PancakePeriodicComplexStretch PancakeHigherLocalVelocity PancakeArbitraryDataBlocks
open PancakeContinuousCoordinateJet

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem real_curl_velocityRHS_eq (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (x : T3) :
    realField (fourierCurl (infiniteVelocityRHS ν u)) x =
      realField (fourierCurl (infiniteVelocityRHS 0 u)) x + ν • fullVorticityLaplacian u x := by
  have hc2 := summable_fourierMoment_curl 2 u hu
  have h0 : Summable (fun q ↦ ‖fourierCurl (infiniteVelocityRHS 0 u) q‖) :=
    ((summable_velocityEnvelope 0 (fourierMoment 3 u) (fourierMoment_nonneg _ _) hu).mul_left
      (2 * Real.pi)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        (norm_curl_velocityRHS_le 0 u _ (fourierMoment_nonneg _ _) hu (fun _ ↦ le_rfl))
  have hc : fourierCurl (infiniteVelocityRHS ν u) = fun q ↦
      fourierCurl (infiniteVelocityRHS 0 u) q + unitTorusViscousVorticityCoeff ν (fourierCurl u) q := by
    rw [infiniteVelocityRHS_eq_zero_add_viscous, LocalFilteredVorticity.fourierCurl_add,
      funext (curl_viscous u ν)]
    rfl
  change complexRealPartEuclideanCLM (fullFourierField id _ x) = _
  rw [hc, fullFourierField_add _ _ h0 (summable_norm_viscous ν _ hc2)]
  simp only [ContinuousMap.add_apply, fullFourierField_viscous ν _ hc2 x, map_add]
  have hs (z : VelocityCoefficient) :
      complexRealPartEuclideanCLM ((ν : ℂ) • z) = ν • complexRealPartEuclideanCLM z := by
    ext i
    simp [complexRealPartEuclideanCLM_apply, complexRealPartEuclidean]
  rw [hs]
  rw [fullVorticityLaplacian, spatialCurl_velocity u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)]
  rfl

theorem vorticity_materialRate_eq_eulerian_add_transport (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) (x : T3) :
    fullStrainOperator u x (fullVorticity u x) + ν • fullVorticityLaplacian u x =
      realField (fourierCurl (infiniteVelocityRHS ν u)) x +
        ∑ j, realFullField u x j • fullCurlGradient u j x := by
  rw [real_curl_velocityRHS_eq ν u hu x]
  have hR : Summable (fourierMoment 1 (infiniteVelocityRHS 0 u)) :=
    VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 0 u hu
  have he := fullVorticity_inviscidRHS u hu hd hr x
  rw [fullVorticity_eq_realFullField _ hR] at he
  change realField (fourierCurl (infiniteVelocityRHS 0 u)) x +
    (∑ j, realFullField u x j • fullCurlGradient u j x) = _ at he
  rw [← he]
  module

theorem gradientMaterialRate_eq_eulerian_add_transport (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (v : Fin 3 → ℝ) (j : Fin 3) (x : T3) :
    gradientMaterialRate ν u v j x = fullCurlGradient (infiniteVelocityRHS ν u) j x +
      ∑ k, v k • mixedGradient (fourierCurl u) j k x := by
  have hc := summable_fourierMoment_derivative 1 (fourierCurl u)
    (summable_fourierMoment_curl 2 u hu) j
  unfold gradientMaterialRate
  rw [map_add, real_directionalCoeff _ hc v x]
  rfl

theorem materialRate_eq_eulerian_add_transport (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) (x : T3) :
    materialRate ν u (fun j ↦ realFullField u x j) x = eulerianRate ν u x +
      ∑ j, realFullField u x j • longitudinalGradient u j x := by
  unfold LocalLongitudinalVorticity.materialRate
  rw [vorticity_materialRate_eq_eulerian_add_transport ν u hu hd hr x]
  simp_rw [gradientMaterialRate_eq_eulerian_add_transport ν u hu]
  rw [LongitudinalJetEvolution.rate_add]
  congr 1
  simp only [LongitudinalJetEvolution.rate, longitudinalGradient,
    Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  module

theorem integral_longitudinal_transport_eq_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0) :
    (∫ x : T3, ⟪longitudinalVorticity u x,
      ∑ j, realFullField u x j • longitudinalGradient u j x⟫) = 0 := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hq := continuous_longitudinalVorticity u hu1
  have h := UnitTorusTransportPairing.integral_inner_transport
    (longitudinalVorticity u) (longitudinalVorticity u)
    (longitudinalGradient u) (longitudinalGradient u)
    (fun j x ↦ realFullField u x j) (fun j x ↦ velocityJet u j x j) coordinateShift
    hq hq (continuous_longitudinalGradient u hu1) (continuous_longitudinalGradient u hu1)
    (fun j ↦ (EuclideanSpace.proj j).continuous.comp (continuous_realFullField u))
    (fun j ↦ (EuclideanSpace.proj j).continuous.comp (continuous_velocityJet u j))
    continuous_coordinateShift coordinateShift_zero
    (hasDerivAt_longitudinal_shift u hu) (hasDerivAt_longitudinal_shift u hu)
    (fun j x h ↦ by
      simpa [EuclideanSpace.inner_single_left] using
        (hasDerivAt_const h (EuclideanSpace.single j (1 : ℝ))).inner ℝ
          (hasDerivAt_realFullField_shift u hu1 j x h))
    (sum_velocityJet_diagonal u hu2 hd)
  have he (x : T3) := real_inner_comm (∑ j, realFullField u x j • longitudinalGradient u j x)
    (longitudinalVorticity u x)
  simp_rw [he] at h
  simp_rw [he]
  linarith

theorem eulerianWork_eq_materialWork (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) :
    eulerianWork ν u = ∫ x : T3, ⟪longitudinalVorticity u x,
      materialRate ν u (fun j ↦ realFullField u x j) x⟫ := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hq := continuous_longitudinalVorticity u hu1
  have he : Continuous (eulerianRate ν u) := by
    exact (eulerianRateField ν u).continuous.congr (eulerianRateField_apply ν u hu1)
  have ht : Continuous (fun x ↦ ∑ j, realFullField u x j • longitudinalGradient u j x) :=
    continuous_finsetSum _ (fun j _ ↦ ((EuclideanSpace.proj j).continuous.comp
      (continuous_realFullField u)).smul
      (continuous_longitudinalGradient u hu1 j))
  simp_rw [materialRate_eq_eulerian_add_transport ν u hu hd hr, inner_add_right]
  rw [integral_add ((hq.inner he).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hq.inner ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    integral_longitudinal_transport_eq_zero u hu hd, add_zero]
  rfl

def dissipation (u : FourierVelocity) : ℝ :=
  ∑ j : Fin 3, ∫ x : T3, ‖longitudinalGradient u j x‖ ^ 2

def stretchingFlux (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ⟪∑ j, fullVorticity u x j • longitudinalGradient u j x,
    fullStrainOperator u x (fullVorticity u x)⟫

def viscousFlux (u : FourierVelocity) : ℝ :=
  ∑ k : Fin 3, ∫ x : T3, ⟪∑ j, fullCurlGradient u k x j • longitudinalGradient u j x,
    fullCurlGradient u k x⟫

/-- Both fluxes remain signed and combined; no positivity is asserted. -/
def sourceWork (ν : ℝ) (u : FourierVelocity) : ℝ :=
  -stretchingFlux u + (2 * ν) * viscousFlux u

theorem dissipation_nonneg (u : FourierVelocity) : 0 ≤ dissipation u :=
  Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))

theorem eulerianWork_add_dissipation (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) :
    eulerianWork ν u + ν * dissipation u = sourceWork ν u := by
  rw [eulerianWork_eq_materialWork ν u
    (summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu) hd hr]
  exact integral_materialRate_balance ν u hu hd hr

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)

include hSum hu in
theorem continuous_mixedCurlGradient_spaceTime (j k : Fin 3) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ mixedGradient (fourierCurl (s.coefficients z.1)) j k z.2) := by
  have hc : Continuous (fun t : Set.Icc (0 : ℝ) T ↦ fullFourierField id
      (indexedDerivativeCoeff id k (indexedDerivativeCoeff id j (fourierCurl (s.coefficients t))))) := by
    refine continuous_fullFourierField_of_norm_le _ ?_ (fun q ↦ (2 * Real.pi)^3 * g q)
      (hSum.mul_left _) ?_
    · intro q i
      have hc (l : Fin 3) : Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q l) :=
        (s.continuous q l).comp continuous_subtype_val
      fin_cases i <;> simp only [indexedDerivativeCoeff, fourierCurl, coefficientCross,
        Pi.smul_apply, smul_eq_mul] <;> fun_prop
    · intro t q
      calc
        _ ≤ fourierMoment 0 (indexedDerivativeCoeff id k
            (indexedDerivativeCoeff id j (fourierCurl (s.coefficients t)))) q := by
          simpa only [fourierMoment, pow_zero, one_mul] using norm_coefficient_sup_le_euclidean
            (indexedDerivativeCoeff id k (indexedDerivativeCoeff id j (fourierCurl (s.coefficients t))) q)
        _ ≤ (2 * Real.pi) * fourierMoment 1
            (indexedDerivativeCoeff id j (fourierCurl (s.coefficients t))) q :=
          fourierMoment_derivative_le 0 _ k q
        _ ≤ (2 * Real.pi) * ((2 * Real.pi) * fourierMoment 2 (fourierCurl (s.coefficients t)) q) :=
          mul_le_mul_of_nonneg_left (fourierMoment_derivative_le 1 _ j q) (by positivity)
        _ ≤ (2 * Real.pi) * ((2 * Real.pi) * ((2 * Real.pi) * fourierMoment 3 (s.coefficients t) q)) := by
          gcongr
          exact fourierMoment_curl_le 2 _ q
        _ ≤ (2 * Real.pi) * ((2 * Real.pi) * ((2 * Real.pi) * g q)) := by
          gcongr
          exact (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t t.2 q)
        _ = _ := by ring
  exact complexRealPartEuclideanCLM.continuous.comp
    (continuous_eval.comp ((hc.comp continuous_fst).prodMk continuous_snd))

include hSum hu in
theorem continuous_longitudinalGradient_spaceTime (k : Fin 3) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ longitudinalGradient (s.coefficients z.1) k z.2) := by
  have hw := continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 4) q).trans (hu t ht q))
  have hd := LocalVorticityEighthMoment.continuous_fullCurlGradient_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu t ht q))
  exact LongitudinalJetEvolution.continuous_rate hw hd (hd k)
    (fun j ↦ continuous_mixedCurlGradient_spaceTime s g hSum hu j k)

include hSum hu in
theorem continuousOn_dissipation :
    ContinuousOn (fun t ↦ dissipation (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  apply continuousOn_finsetSum
  intro k _
  exact LocalAlignmentContinuity.continuousOn_spatialIntegral _
    ((continuous_longitudinalGradient_spaceTime s g hSum hu k).norm.pow 2)

include hg hSum hu in
theorem continuousOn_sourceWork (hB : 0 ≤ B) :
    ContinuousOn (fun t ↦ sourceWork ν (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  apply ((continuous_eulerianWork s g hg hSum hu hB).add
    ((continuousOn_dissipation s g hSum hu).const_mul ν)).congr
  intro t ht
  exact (eulerianWork_add_dissipation ν _
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)) (s.transverse t) (s.reality t)).symm

include hg hSum hu in
theorem hasDerivAt_meanEnergy_balance (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ meanEnergy (s.coefficients τ))
      (2 * (sourceWork ν (s.coefficients t) - ν * dissipation (s.coefficients t))) t := by
  have h := hasDerivAt_meanEnergy s g hg hSum hu t ht
  have he := eulerianWork_add_dissipation ν _
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩))
    (s.transverse t) (s.reality t)
  convert h using 1
  linarith

include hg hSum hu in
/-- Time-integrated balance from the initial data, with positive diffusion
and the combined signed flux. It is not an estimate for the source work. -/
theorem energy_identity (hB : 0 ≤ B) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    meanEnergy (s.coefficients t) + 2 * ν * (∫ τ in (0 : ℝ)..t, dissipation (s.coefficients τ)) =
      meanEnergy u₀ + 2 * (∫ τ in (0 : ℝ)..t, sourceWork ν (s.coefficients τ)) := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hi : IntervalIntegrable (fun τ ↦ eulerianWork ν (s.coefficients τ)) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuous_eulerianWork s g hg hSum hu hB).mono hsub)
  have hd : IntervalIntegrable (fun τ ↦ dissipation (s.coefficients τ)) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_dissipation s g hSum hu).mono hsub)
  have he : (∫ τ in (0 : ℝ)..t, sourceWork ν (s.coefficients τ)) =
      (∫ τ in (0 : ℝ)..t, eulerianWork ν (s.coefficients τ) + ν * dissipation (s.coefficients τ)) := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [Set.uIcc_of_le ht.1] at hτ
    exact (eulerianWork_add_dissipation ν _
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ)))
      (s.transverse τ) (s.reality τ)).symm
  rw [he, intervalIntegral.integral_add hi (hd.const_mul ν), intervalIntegral.integral_const_mul]
  have h := meanEnergy_eq_initial_add_integral s g hg hSum hu hB t ht
  linarith

/-- Smooth real transverse mean-zero periodic data construct a local
solution satisfying the identity; no moment envelope is left as a premise. -/
theorem exists_physical_local_energy_identity (ν : ℝ) (hν : 0 < ν)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 10 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          meanEnergy (s.coefficients t) + 2 * ν * (∫ τ in (0 : ℝ)..t, dissipation (s.coefficients τ)) =
            meanEnergy (torusFourierVelocity f) + 2 * (∫ τ in (0 : ℝ)..t, sourceWork ν (s.coefficients τ)) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 4 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, energy_identity s g hg hSum hu hB⟩

end Mettapedia.FluidDynamics.NavierStokes.LongitudinalEnergyBalance
