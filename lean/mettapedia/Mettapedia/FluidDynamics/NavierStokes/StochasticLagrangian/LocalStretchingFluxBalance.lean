import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxProjectedEvolution

/-!
# Integrated signed balance for the actual projected stretching flux

The local Fourier solution supplies continuity of the Eulerian flux rate.
After the material-transport identity, this proves integrability of the
combined signed work and its exact time balance. No global bound on that
work, or on the high Fourier envelope, is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalStretchingFluxBalance

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis ContinuousFieldBilinear UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeCurlOutputTail PancakeCoefficientLimitEquation
open PancakeInfiniteFourierTime PancakeIndexedFourierMoments PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeDyadicDirectionEvolution PancakeLocalInfiniteVelocity
open PancakeVelocityGradientEnvelope PancakeInfiniteVelocityEnvelope LocalVorticityTime
open LocalVorticityDiffusion LocalLowDiffusionBudget PancakeHigherLocalVelocity PancakeContinuousCoordinateJet
open PancakeArbitraryDataBlocks LongitudinalVorticityTime LongitudinalGradientFlux
open LocalStretchingFluxTime StretchingFluxMaterialRate StretchingFluxProjectedEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hB hg hSum hu

theorem continuous_vorticityRHSField :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      vorticityField (infiniteVelocityRHS ν (s.coefficients t))) := by
  apply (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).continuous.comp
  refine continuous_fullFourierField_of_norm_le _ ?_ (fun q ↦ (2 * Real.pi) * velocityEnvelope ν g q)
    ((summable_velocityEnvelope ν g hg hSum).mul_left _) ?_
  · intro q i
    have hc := continuous_velocityRHS_component s hB q
    fin_cases i <;> simp only [fourierCurl, coefficientCross, Pi.smul_apply, smul_eq_mul] <;> fun_prop
  · intro t q
    exact norm_curl_velocityRHS_le ν _ g hg hSum (hu t t.2) q

theorem continuous_velocityDerivativeRHSField (j : Fin 3) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      velocityDerivativeField (infiniteVelocityRHS ν (s.coefficients t)) j) := by
  apply (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).continuous.comp
  refine continuous_fullFourierField_of_norm_le _ ?_ (fun q ↦ (2 * Real.pi) * velocityEnvelope ν g q)
    ((summable_velocityEnvelope ν g hg hSum).mul_left _) ?_
  · intro q i
    have hc := continuous_velocityRHS_component s hB q
    simp only [indexedDerivativeCoeff, Pi.smul_apply, smul_eq_mul]
    fun_prop
  · intro t q
    exact norm_velocityRHS_derivative_le ν _ g hg hSum (hu t t.2) j q

omit hB hg in
theorem continuousOn_vorticityField :
    ContinuousOn (fun t ↦ vorticityField (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_restrict]
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hm (t : Set.Icc (0 : ℝ) T) : Summable (fourierMoment 1 (s.coefficients t)) :=
    summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t t.2))
  change Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ vorticityField (s.coefficients z.1) z.2)
  simp_rw [vorticityField_apply _ (hm _)]
  exact continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))

omit hB hg in
theorem continuousOn_velocityDerivativeField (j : Fin 3) :
    ContinuousOn (fun t ↦ velocityDerivativeField (s.coefficients t) j) (Set.Icc (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_restrict]
  apply (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).continuous.comp
  refine continuous_fullFourierField_of_norm_le _ ?_ (fun q ↦ (2 * Real.pi) * g q)
    (hSum.mul_left _) ?_
  · intro q i
    have hc : Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
      (s.continuous q i).comp continuous_subtype_val
    simp only [indexedDerivativeCoeff, Pi.smul_apply, smul_eq_mul]
    fun_prop
  · intro t q
    exact (norm_indexedDerivative_le_firstMoment id _ j q).trans
      (mul_le_mul_of_nonneg_left
        ((show indexedFirstMoment id (s.coefficients t) q ≤ fourierMoment 3 (s.coefficients t) q by
          rw [indexedFirstMoment_id]
          exact fourierMoment_mono _ (by omega : 1 ≤ 3) q).trans (hu t t.2 q)) (by positivity))

omit hB hg in
theorem continuousOn_stretchingField :
    ContinuousOn (fun t ↦ stretchingField (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  apply continuousOn_finsetSum
  intro j _
  exact ((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp_continuousOn
    ((componentField j).continuous.comp_continuousOn
      (continuousOn_vorticityField s g hSum hu))).clm_apply
        (continuousOn_velocityDerivativeField s g hSum hu j)

omit hB hg in
theorem continuousOn_fluxField (j : Fin 3) :
    ContinuousOn (fun t ↦ fluxField 0 (s.coefficients t) j) (Set.Icc (0 : ℝ) T) := by
  simp only [fluxField_zero_eq]
  have hh := (((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp_continuousOn
    ((componentField j).continuous.comp_continuousOn
      (continuousOn_vorticityField s g hSum hu))).clm_apply
        (continuousOn_stretchingField s g hSum hu)).neg
  convert! hh using 1

omit hB hg in
theorem continuousOn_projectedFlux :
    ContinuousOn (fun t ↦ projectedFlux 0 (s.coefficients t)) (Set.Icc (0 : ℝ) T) :=
  ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))).continuous.comp_continuousOn
      (continuousOn_pi.mpr (continuousOn_fluxField s g hSum hu))

theorem continuousOn_stretchingRateField :
    ContinuousOn (fun t ↦ stretchingRateField ν (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  have hw : ContinuousOn (fun t ↦ vorticityField (infiniteVelocityRHS ν (s.coefficients t)))
      (Set.Icc (0 : ℝ) T) :=
    (continuousOn_iff_continuous_restrict.mpr
      (continuous_vorticityRHSField s hB g hg hSum hu))
  have ha (j : Fin 3) : ContinuousOn (fun t ↦
      velocityDerivativeField (infiniteVelocityRHS ν (s.coefficients t)) j) (Set.Icc (0 : ℝ) T) :=
    (continuousOn_iff_continuous_restrict.mpr
      (continuous_velocityDerivativeRHSField s hB g hg hSum hu j))
  apply continuousOn_finsetSum
  intro j _
  apply ContinuousOn.add
  · exact ((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp_continuousOn
      ((componentField j).continuous.comp_continuousOn
        (continuousOn_vorticityField s g hSum hu))).clm_apply (ha j)
  · exact ((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp_continuousOn
      ((componentField j).continuous.comp_continuousOn hw)).clm_apply
        (continuousOn_velocityDerivativeField s g hSum hu j)

theorem continuousOn_fluxRateField (j : Fin 3) :
    ContinuousOn (fun t ↦ fluxRateField ν (s.coefficients t) j) (Set.Icc (0 : ℝ) T) := by
  have hw : ContinuousOn (fun t ↦ vorticityField (infiniteVelocityRHS ν (s.coefficients t)))
      (Set.Icc (0 : ℝ) T) :=
    (continuousOn_iff_continuous_restrict.mpr
      (continuous_vorticityRHSField s hB g hg hSum hu))
  have ha := continuousOn_stretchingField s g hSum hu
  apply ContinuousOn.neg
  apply ContinuousOn.add
  · exact ((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp_continuousOn
      ((componentField j).continuous.comp_continuousOn
        (continuousOn_vorticityField s g hSum hu))).clm_apply
          (continuousOn_stretchingRateField s hB g hg hSum hu)
  · exact ((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp_continuousOn
      ((componentField j).continuous.comp_continuousOn hw)).clm_apply ha

theorem continuousOn_eulerianWork :
    ContinuousOn (fun t ↦ LocalStretchingFluxTime.eulerianWork ν (s.coefficients t))
      (Set.Icc (0 : ℝ) T) := by
  have hF := continuousOn_projectedFlux s g hSum hu
  have hdF := ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))).continuous.comp_continuousOn
      (continuousOn_pi.mpr (continuousOn_fluxRateField s hB g hg hSum hu))
  exact hF.inner hdF

theorem continuousOn_signed_work :
    ContinuousOn (fun t ↦ materialWork ν (s.coefficients t) - transportWork (s.coefficients t))
      (Set.Icc (0 : ℝ) T) := by
  apply (continuousOn_eulerianWork s hB g hg hSum hu).congr
  intro t ht
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)
  exact (eulerianWork_eq_material_sub_transport ν _ hm (s.transverse t) (s.reality t)).symm

theorem intervalIntegrable_signed_work {a b : ℝ} (hab : a ≤ b)
    (hI : Set.Icc a b ⊆ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun t ↦ materialWork ν (s.coefficients t) - transportWork (s.coefficients t))
      volume a b :=
  ContinuousOn.intervalIntegrable_of_Icc hab ((continuousOn_signed_work s hB g hg hSum hu).mono hI)

theorem energy_identity {a b : ℝ} (hab : a ≤ b)
    (hI : Set.Icc a b ⊆ Set.Icc (0 : ℝ) T) :
    projectedFluxSquare 0 (s.coefficients b) = projectedFluxSquare 0 (s.coefficients a) +
      2 * ∫ t in a..b, materialWork ν (s.coefficients t) - transportWork (s.coefficients t) := by
  have hi := (intervalIntegrable_signed_work s hB g hg hSum hu hab hI).const_mul 2
  have hc := (((continuousOn_projectedFlux s g hSum hu).norm).pow 2).mono hI
  have ha := (hI (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)).1
  have hb := (hI (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩)).2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
    (fun t ht ↦ StretchingFluxProjectedEvolution.hasDerivAt_projectedFluxSquare s g hg hSum hu t
      ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩) hi
  rw [intervalIntegral.integral_const_mul] at he
  change ‖projectedFlux 0 (s.coefficients b)‖ ^ 2 =
    ‖projectedFlux 0 (s.coefficients a)‖ ^ 2 + _
  linarith

theorem energy_identity_from_initial (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    projectedFluxSquare 0 (s.coefficients t) = projectedFluxSquare 0 u₀ +
      2 * ∫ τ in (0 : ℝ)..t, materialWork ν (s.coefficients τ) - transportWork (s.coefficients τ) := by
  simpa only [s.initial] using energy_identity s hB g hg hSum hu ht.1
    (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩)

omit hB hg hSum hu in
/-- Smooth physical data construct every object used in the local balance. -/
theorem exists_physical_local_projected_flux_balance (ν : ℝ) (hν : 0 < ν)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ Set.Icc (0 : ℝ) T →
          projectedFluxSquare 0 (s.coefficients b) = projectedFluxSquare 0 (s.coefficients a) +
            2 * ∫ t in a..b, materialWork ν (s.coefficients t) - transportWork (s.coefficients t) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, fun a b hab hI ↦ energy_identity s hB g hg hSum hu hab hI⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalStretchingFluxBalance
