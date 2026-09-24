import Mettapedia.Analysis.UnitTorusGradientProjection
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalJointFlux

/-!
# The gradient-active part of the actual longitudinal flux

The closed-gradient orthogonal projection is applied to the full joint
flux in tensor-valued `L²`. It preserves source work, lowers the residual
cost, and enters the actual initial-endpoint energy inequality. No budget
for this projected cost is assumed or inferred from its construction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LongitudinalGradientFlux

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity PancakeFourierTranslationCurve
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalAlignmentForcing
open LocalLongitudinalVorticity LongitudinalVorticityDiffusion LongitudinalCurvatureWork
open LongitudinalVorticityTime LongitudinalEnergyBalance LongitudinalJointFlux
open FullLambVector FullVorticityGradientTransport
open PancakeFourierMaterialPaths PancakeCentralDifferenceLimit
open PancakeHigherLocalVelocity PancakeArbitraryDataBlocks PancakeContinuousCoordinateJet

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def fluxField (ν : ℝ) (u : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  ⟨fun x ↦ -(vorticityField u x j • ∑ k, vorticityField u x k • velocityJet u k x) +
    (2 * ν) • ∑ k, fullCurlGradient u k x j • fullCurlGradient u k x, by
    have hw := (vorticityField u).continuous
    have hd := LocalSquaredGapGradient.continuous_fullCurlGradient u
    exact (((EuclideanSpace.proj j).continuous.comp hw).smul
      (continuous_finsetSum _ (fun k _ ↦ ((EuclideanSpace.proj k).continuous.comp hw).smul
        (continuous_velocityJet u k)))).neg.add
      (continuous_const.smul (continuous_finsetSum _ (fun k _ ↦
        ((EuclideanSpace.proj j).continuous.comp (hd k)).smul (hd k))))⟩

theorem fluxField_apply (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) (x : T3) :
    fluxField ν u j x = flux ν u j x := by
  change -(vorticityField u x j • ∑ k, vorticityField u x k • velocityJet u k x) + _ = _
  rw [vorticityField_apply u hu]
  change -(fullVorticity u x j • vorticityStretch u x) + _ = _
  rw [vorticityStretch_eq u hu]
  rfl

def gradientField (u : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  ⟨fun x ↦ LongitudinalJetEvolution.rate (vorticityField u x) (fun k ↦ fullCurlGradient u k x)
    (fullCurlGradient u j x) (fun k ↦ mixedGradient (fourierCurl u) k j x),
    LongitudinalJetEvolution.continuous_rate (vorticityField u).continuous
      (LocalSquaredGapGradient.continuous_fullCurlGradient u)
      (LocalSquaredGapGradient.continuous_fullCurlGradient u j)
      (fun k ↦ continuous_velocityJet (PancakeInfiniteFourierDerivative.indexedDerivativeCoeff id k (fourierCurl u)) j)⟩

theorem gradientField_apply (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) (x : T3) :
    gradientField u j x = longitudinalGradient u j x := by
  change LongitudinalJetEvolution.rate (vorticityField u x) _ _ _ = _
  rw [vorticityField_apply u hu]
  rfl

def longitudinalJet (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) : TranslationJet (Fin 3) R3 where
  value := longitudinalField u
  gradient := gradientField u
  hasDerivAt j x h := by
    have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
    have hshift : UnitTorusWeakDerivative.coordinateShift j = coordinateShift j := by
      funext t
      rfl
    simpa only [hshift, longitudinalField_apply u hu1, gradientField_apply u hu1] using
      hasDerivAt_longitudinal_shift u hu j x h

def projectedFlux (ν : ℝ) (u : FourierVelocity) : TensorL2 (Fin 3) R3 :=
  gradientProjection (toTensorL2 (fluxField ν u))

def projectedFluxSquare (ν : ℝ) (u : FourierVelocity) : ℝ := ‖projectedFlux ν u‖ ^ 2

theorem projectedFluxSquare_nonneg (ν : ℝ) (u : FourierVelocity) : 0 ≤ projectedFluxSquare ν u :=
  sq_nonneg _

theorem gradientField_norm_sq (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    ‖toTensorL2 (gradientField u)‖ ^ 2 = dissipation u := by
  rw [norm_toTensorL2_sq]
  simp_rw [gradientField_apply u hu]
  exact integral_finsetSum _ (fun j _ ↦ ((continuous_longitudinalGradient u hu j).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

theorem fluxField_norm_sq (ν : ℝ) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    ‖toTensorL2 (fluxField ν u)‖ ^ 2 = fluxSquare ν u := by
  rw [norm_toTensorL2_sq]
  simp only [fluxField_apply ν u hu, fluxSquare]

theorem projectedFluxSquare_le (ν : ℝ) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    projectedFluxSquare ν u ≤ fluxSquare ν u := by
  rw [← fluxField_norm_sq ν u hu]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradientProjection_le (toTensorL2 (fluxField ν u))) 2

theorem sourceWork_eq_projected_pairing (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    sourceWork ν u = ⟪toTensorL2 (gradientField u), projectedFlux ν u⟫ := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have h := inner_gradient_projection (longitudinalJet u hu) (toTensorL2 (fluxField ν u))
  change ⟪toTensorL2 (gradientField u), projectedFlux ν u⟫ = _ at h
  rw [h, inner_toTensorL2]
  change sourceWork ν u = ∫ x : T3, ∑ j, ⟪gradientField u j x, fluxField ν u j x⟫
  simp_rw [gradientField_apply u hu1, fluxField_apply ν u hu1]
  exact sourceWork_eq_pairing ν u hu1

theorem scaled_sourceWork_le_projected (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) :
    (2 * ν) * sourceWork ν u ≤ ν ^ 2 * dissipation u + projectedFluxSquare ν u := by
  have h := sq_nonneg ‖ν • toTensorL2 (gradientField u) - projectedFlux ν u‖
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, mul_pow, Real.norm_eq_abs, sq_abs,
    gradientField_norm_sq u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu),
    ← sourceWork_eq_projected_pairing ν u hu] at h
  change _ ≤ _ + ‖projectedFlux ν u‖ ^ 2
  nlinarith

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)

include hSum hu in
theorem continuous_fluxField (j : Fin 3) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ fluxField ν (s.coefficients t) j) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ fluxField ν (s.coefficients z.1) j z.2)
  have hm (t : Set.Icc (0 : ℝ) T) : Summable (fourierMoment 1 (s.coefficients t)) :=
    summable_fourierMoment_of_le _ (by omega : 1 ≤ 4)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t t.2))
  simp_rw [fluxField_apply ν _ (hm _)]
  exact continuous_flux_spaceTime s g hSum hu j

include hSum hu in
theorem continuous_projectedFlux :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ projectedFlux ν (s.coefficients t)) :=
  (gradientProjectionCLM (d := Fin 3) (E := R3)).continuous.comp
    ((tensorEmbedding (d := Fin 3) (E := R3)).continuous.comp
      (continuous_pi (continuous_fluxField s g hSum hu)))

include hSum hu in
theorem continuousOn_projectedFluxSquare :
    ContinuousOn (fun t ↦ projectedFluxSquare ν (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_restrict]
  exact (continuous_projectedFlux s g hSum hu).norm.pow 2

include hg hSum hu in
/-- The actual local energy inequality charges only the gradient-active
part of the full joint flux. Its global affordability remains a separate problem. -/
theorem energy_le_initial_add_projectedFluxSquare (hB : 0 ≤ B)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ν * meanEnergy (s.coefficients t) + ν ^ 2 * (∫ τ in (0 : ℝ)..t, dissipation (s.coefficients τ)) ≤
      ν * meanEnergy u₀ + ∫ τ in (0 : ℝ)..t, projectedFluxSquare ν (s.coefficients τ) := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hs : IntervalIntegrable (fun τ ↦ sourceWork ν (s.coefficients τ)) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_sourceWork s g hg hSum hu hB).mono hsub)
  have hd : IntervalIntegrable (fun τ ↦ dissipation (s.coefficients τ)) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_dissipation s g hSum hu).mono hsub)
  have hf : IntervalIntegrable (fun τ ↦ projectedFluxSquare ν (s.coefficients τ)) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 ((continuousOn_projectedFluxSquare s g hSum hu).mono hsub)
  have h := intervalIntegral.integral_mono_on ht.1 (hs.const_mul (2 * ν))
    ((hd.const_mul (ν ^ 2)).add hf) (fun τ hτ ↦ scaled_sourceWork_le_projected ν _
      (summable_fourierMoment_of_le _ (by omega : 3 ≤ 4)
        (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ (hsub hτ)))))
  rw [intervalIntegral.integral_add (hd.const_mul (ν ^ 2)) hf,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  have he := congrArg (fun r : ℝ ↦ ν * r) (energy_identity s g hg hSum hu hB t ht)
  nlinarith

theorem exists_physical_local_projected_flux_bound (ν : ℝ) (hν : 0 < ν)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 10 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          ν * meanEnergy (s.coefficients t) + ν ^ 2 * (∫ τ in (0 : ℝ)..t, dissipation (s.coefficients τ)) ≤
            ν * meanEnergy (torusFourierVelocity f) + ∫ τ in (0 : ℝ)..t, projectedFluxSquare ν (s.coefficients τ) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 4 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, energy_le_initial_add_projectedFluxSquare s g hg hSum hu hB⟩

end Mettapedia.FluidDynamics.NavierStokes.LongitudinalGradientFlux
