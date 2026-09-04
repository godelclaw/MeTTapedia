import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeDyadicKernelScaling

/-!
# Square-dyadic coherent kernel on finite Fourier fields

This module descends the exact square-dyadic six-dimensional kernel to the
standard unit torus and transfers its coefficient and endpoint estimates to
finite periodic Fourier fields.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeSquareDyadicFiniteTransfer

open MeasureTheory
open PancakeBilinearKernelScaling
open PancakeBilinearPeriodization
open PancakeDyadicKernelScaling
open PancakeFiniteFourierBilinearTransfer
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentSymbol
open PancakeSmoothCoherentStretchSymbol
open PeriodicFourierTriad
open Set

/-- Pull a Euclidean function back to the unit six-torus through the canonical
half-open-cell representative. -/
def unitTorusKernelOfEuclideanRepresentative
    {E : Type*} (K : EuclideanFrequencyPair → E)
    (q : FrequencyPairUnitTorus) : E :=
  K (unitTorusFrequencyPairRepresentative q)

/-- Measurability is preserved by the canonical representative pullback. -/
theorem measurable_unitTorusKernelOfEuclideanRepresentative
    {E : Type*} [MeasurableSpace E]
    (K : EuclideanFrequencyPair → E) (hK : Measurable K) :
    Measurable (unitTorusKernelOfEuclideanRepresentative K) :=
  hK.comp measurable_unitTorusFrequencyPairRepresentative

/-- Fourier coefficients of a canonical-representative pullback are exactly
the character integrals over the standard Euclidean fundamental cell. -/
theorem frequencyPairUnitTorusFourierCoeff_unitTorusKernelOfEuclideanRepresentative
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (n : FrequencyPairWavevector) :
    frequencyPairUnitTorusFourierCoeff
        (unitTorusKernelOfEuclideanRepresentative K) n =
      ∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x • K x := by
  unfold frequencyPairUnitTorusFourierCoeff
  calc
    (∫ q : FrequencyPairUnitTorus,
        UnitAddTorus.mFourier (-n) q •
          unitTorusKernelOfEuclideanRepresentative K q
            ∂frequencyPairUnitTorusMeasure) =
        ∫ x : Fin 6 → ℝ in rawFrequencyPairCellIoc,
          UnitAddTorus.mFourier (-n)
              (fun i ↦ (x i : UnitAddCircle)) •
            unitTorusKernelOfEuclideanRepresentative K
              (fun i ↦ (x i : UnitAddCircle)) := by
      have hpre := UnitAddTorus.integral_preimage
        (fun q : FrequencyPairUnitTorus ↦
          UnitAddTorus.mFourier (-n) q •
            unitTorusKernelOfEuclideanRepresentative K q)
        (fun _ : Fin 6 ↦ (0 : ℝ))
      change (∫ q : FrequencyPairUnitTorus,
          UnitAddTorus.mFourier (-n) q •
            unitTorusKernelOfEuclideanRepresentative K q
              ∂frequencyPairUnitTorusMeasure) =
        ∫ x : Fin 6 → ℝ in
          {x | ∀ i, x i ∈ Ioc (0 : ℝ) (0 + 1)},
          UnitAddTorus.mFourier (-n)
              (fun i ↦ (x i : UnitAddCircle)) •
            unitTorusKernelOfEuclideanRepresentative K
              (fun i ↦ (x i : UnitAddCircle)) at hpre
      simpa [rawFrequencyPairCellIoc] using hpre
    _ = ∫ x : Fin 6 → ℝ in rawFrequencyPairCellIoc,
          euclideanFrequencyPairCharacter n (WithLp.toLp 2 x) •
            K (WithLp.toLp 2 x) := by
      have hcellmeas : MeasurableSet rawFrequencyPairCellIoc := by
        simpa [rawFrequencyPairCellIoc] using
          (MeasurableSet.univ_pi' (fun _ : Fin 6 ↦
            (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))))
      apply setIntegral_congr_fun hcellmeas
      intro x hx
      change UnitAddTorus.mFourier (-n)
            (fun i ↦ (x i : UnitAddCircle)) •
          unitTorusKernelOfEuclideanRepresentative K
            (fun i ↦ (x i : UnitAddCircle)) = _
      rw [mFourier_neg_coe_eq_euclideanFrequencyPairCharacter]
      change euclideanFrequencyPairCharacter n (WithLp.toLp 2 x) •
          K (unitTorusFrequencyPairRepresentative
            (fun i ↦ (x i : UnitAddCircle))) = _
      rw [unitTorusFrequencyPairRepresentative_coe x hx]
    _ = ∫ x : Fin 6 → ℝ in rawFrequencyPairCellIco,
          euclideanFrequencyPairCharacter n (WithLp.toLp 2 x) •
            K (WithLp.toLp 2 x) :=
      setIntegral_congr_set rawFrequencyPairCellIco_ae_eq_Ioc.symm
    _ = ∫ x : EuclideanFrequencyPair in standardFrequencyPairCell,
          euclideanFrequencyPairCharacter n x • K x := by
      let F : EuclideanFrequencyPair → CoherentBilinearOperator := fun x ↦
        euclideanFrequencyPairCharacter n x • K x
      have hpres :=
        (PiLp.volume_preserving_toLp (Fin 6)).setIntegral_preimage_emb
          (MeasurableEquiv.toLp 2 (Fin 6 → ℝ)).measurableEmbedding
          F standardFrequencyPairCell
      have hpre :
          (WithLp.toLp 2 : (Fin 6 → ℝ) → EuclideanFrequencyPair) ⁻¹'
              standardFrequencyPairCell = rawFrequencyPairCellIco :=
        preimage_standardFrequencyPairCell_toLp
      rw [hpre] at hpres
      simpa [F] using hpres

/-- The torus `L¹` mass of a representative pullback is the fundamental-cell
mass of the Euclidean function. -/
theorem lintegral_enorm_unitTorusKernelOfEuclideanRepresentative
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (hK : Measurable K) :
    (∫⁻ q : FrequencyPairUnitTorus,
        ‖unitTorusKernelOfEuclideanRepresentative K q‖ₑ
          ∂frequencyPairUnitTorusMeasure) =
      ∫⁻ x in standardFrequencyPairCell, ‖K x‖ₑ := by
  calc
    (∫⁻ q : FrequencyPairUnitTorus,
        ‖unitTorusKernelOfEuclideanRepresentative K q‖ₑ
          ∂frequencyPairUnitTorusMeasure) =
        ∫⁻ x : Fin 6 → ℝ in rawFrequencyPairCellIoc,
          ‖unitTorusKernelOfEuclideanRepresentative K
            (fun i ↦ (x i : UnitAddCircle))‖ₑ := by
      have hpre := UnitAddTorus.lintegral_preimage
        (fun q : FrequencyPairUnitTorus ↦
          ‖unitTorusKernelOfEuclideanRepresentative K q‖ₑ)
        (fun _ : Fin 6 ↦ (0 : ℝ))
      change (∫⁻ q : FrequencyPairUnitTorus,
          ‖unitTorusKernelOfEuclideanRepresentative K q‖ₑ
            ∂frequencyPairUnitTorusMeasure) =
        ∫⁻ x : Fin 6 → ℝ in
          {x | ∀ i, x i ∈ Ioc (0 : ℝ) (0 + 1)},
          ‖unitTorusKernelOfEuclideanRepresentative K
            (fun i ↦ (x i : UnitAddCircle))‖ₑ at hpre
      simpa [rawFrequencyPairCellIoc] using hpre
    _ = ∫⁻ x : Fin 6 → ℝ in rawFrequencyPairCellIoc,
          ‖K (WithLp.toLp 2 x)‖ₑ := by
      have hcellmeas : MeasurableSet rawFrequencyPairCellIoc := by
        simpa [rawFrequencyPairCellIoc] using
          (MeasurableSet.univ_pi' (fun _ : Fin 6 ↦
            (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))))
      apply setLIntegral_congr_fun hcellmeas
      intro x hx
      unfold unitTorusKernelOfEuclideanRepresentative
      change ‖K (unitTorusFrequencyPairRepresentative
        (fun i ↦ (x i : UnitAddCircle)))‖ₑ = ‖K (WithLp.toLp 2 x)‖ₑ
      rw [unitTorusFrequencyPairRepresentative_coe x hx]
    _ = ∫⁻ x : Fin 6 → ℝ in rawFrequencyPairCellIco,
          ‖K (WithLp.toLp 2 x)‖ₑ :=
      setLIntegral_congr rawFrequencyPairCellIco_ae_eq_Ioc.symm
    _ = ∫⁻ x : EuclideanFrequencyPair in standardFrequencyPairCell,
          ‖K x‖ₑ := by
      have hpres :=
        (PiLp.volume_preserving_toLp (Fin 6)).setLIntegral_comp_preimage
          (ZSpan.fundamentalDomain_measurableSet standardFrequencyPairBasis)
          hK.enorm
      have hpre :
          (WithLp.toLp 2 : (Fin 6 → ℝ) → EuclideanFrequencyPair) ⁻¹'
              standardFrequencyPairCell = rawFrequencyPairCellIco :=
        preimage_standardFrequencyPairCell_toLp
      have hpre' :
          (WithLp.toLp 2 : (Fin 6 → ℝ) → EuclideanFrequencyPair) ⁻¹'
              ZSpan.fundamentalDomain standardFrequencyPairBasis =
            rawFrequencyPairCellIco := by
        simpa [standardFrequencyPairCell] using hpre
      rw [hpre'] at hpres
      simpa [standardFrequencyPairCell] using hpres

/-- The exact square-dyadic coherent kernel on the standard unit six-torus. -/
def unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel
    (N : ℕ) (q : FrequencyPairUnitTorus) : CoherentBilinearOperator :=
  unitTorusKernelOfEuclideanRepresentative
    (periodizedSquareDyadicNormalizedStretchTensorKernel N) q

/-- The square-dyadic torus kernel is measurable. -/
theorem measurable_unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel
    (N : ℕ) :
    Measurable
      (unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel N) := by
  apply measurable_unitTorusKernelOfEuclideanRepresentative
  unfold periodizedSquareDyadicNormalizedStretchTensorKernel
    periodizedIsotropicAnisotropicNormalizedStretchTensorKernel
  exact measurable_periodizedIsotropicFrequencyPairKernel _ _
    (anisotropicNormalizedStretchTensorKernel_continuous ((1 : ℝ) / N))

/-- Every torus Fourier coefficient is the intended square-dyadic coherent
symbol with its genuine `1/N` prefactor. -/
theorem frequencyPairUnitTorusFourierCoeff_periodizedSquareDyadicNormalizedStretchTensorKernel
    {N : ℕ} (hN : 0 < N) (k l : Wavevector) :
    frequencyPairUnitTorusFourierCoeff
        (unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel N)
        (pairWavevector k l) =
      ((((1 : ℝ) / N) : ℂ)) •
        normalizedStretchTensorSymbol explicitBufferedStretchCutoff
          ((1 : ℝ) / N) (squareDyadicEuclideanFrequencyPair N k l) := by
  unfold unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel
  rw [frequencyPairUnitTorusFourierCoeff_unitTorusKernelOfEuclideanRepresentative]
  exact
    setIntegral_character_periodizedSquareDyadicNormalizedStretchTensorKernel
      hN k l

/-- The unit-torus square-dyadic kernel inherits the uniform `C/N` mass
bound from its Euclidean fundamental cell. -/
theorem exists_uniform_unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      (∫⁻ q : FrequencyPairUnitTorus,
        ‖unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel N q‖ₑ
          ∂frequencyPairUnitTorusMeasure) ≤ ENNReal.ofReal (C / N) := by
  rcases
      exists_uniform_periodizedSquareDyadicNormalizedStretchTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro N hN
  unfold unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel
  rw [lintegral_enorm_unitTorusKernelOfEuclideanRepresentative]
  · exact hmass N hN
  · unfold periodizedSquareDyadicNormalizedStretchTensorKernel
      periodizedIsotropicAnisotropicNormalizedStretchTensorKernel
    exact measurable_periodizedIsotropicFrequencyPairKernel _ _
      (anisotropicNormalizedStretchTensorKernel_continuous ((1 : ℝ) / N))

/-- For every square-dyadic scale `N ≥ 2`, the torus kernel is Bochner
integrable. -/
theorem integrable_unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel
    {N : ℕ} (hN : 2 ≤ N) :
    Integrable (unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel N)
      frequencyPairUnitTorusMeasure := by
  rcases
      exists_uniform_unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel_mass with
    ⟨C, _hC, hmass⟩
  refine
    ⟨(measurable_unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel
      N).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (hmass N hN) ENNReal.ofReal_lt_top

/-- The square-dyadic kernel acts on a pair of Fourier monomials through its
exact square-dyadic coherent multiplier. -/
theorem unitTorusPeriodizedSquareDyadicNormalizedStretch_action_monomials
    {N : ℕ} (hN : 2 ≤ N)
    (k l : Wavevector) (u v : ComplexVec3) (x : BilinearSpatialTorus) :
    torusBilinearKernelAction
        (unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel N)
        (fun z ↦ UnitAddTorus.mFourier k z • u)
        (fun z ↦ UnitAddTorus.mFourier l z • v) x =
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
        applyCoherentBilinearOperator
          (((((1 : ℝ) / N) : ℂ)) •
            normalizedStretchTensorSymbol explicitBufferedStretchCutoff
              ((1 : ℝ) / N)
              (squareDyadicEuclideanFrequencyPair N k l)) u v := by
  rw [torusBilinearKernelAction_monomials _
    (integrable_unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel
      hN)]
  rw [frequencyPairUnitTorusFourierCoeff_periodizedSquareDyadicNormalizedStretchTensorKernel
    (lt_of_lt_of_le (by norm_num) hN)]

/-- Exact double-sum multiplier formula on arbitrary finite Fourier fields. -/
theorem unitTorusPeriodizedSquareDyadicNormalizedStretch_action_finiteFourierReconstruction
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    torusBilinearKernelAction
        (unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel N)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      ∑ k ∈ s, ∑ l ∈ t,
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          applyCoherentBilinearOperator
            (((((1 : ℝ) / N) : ℂ)) •
              normalizedStretchTensorSymbol explicitBufferedStretchCutoff
                ((1 : ℝ) / N)
                (squareDyadicEuclideanFrequencyPair N k l))
            (omega k) (eta l) := by
  rw [torusBilinearKernelAction_finiteFourierReconstruction _
    (integrable_unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel
      hN)]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [frequencyPairUnitTorusFourierCoeff_periodizedSquareDyadicNormalizedStretchTensorKernel
    (lt_of_lt_of_le (by norm_num) hN)]

/-- The finite-field formula written directly as the retained coherent
Biot--Savart stretching interaction in the square-dyadic chart. -/
theorem unitTorusPeriodizedSquareDyadicNormalizedStretch_action_finiteFourierReconstruction_eq_coherent
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    torusBilinearKernelAction
        (unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel N)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      ∑ k ∈ s, ∑ l ∈ t,
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          (((((1 : ℝ) / N) : ℂ)) •
            localizedCoherentProjectedNormalizedStretch
              explicitBufferedStretchCutoff ((1 : ℝ) / N)
              (squareDyadicFrequencyPairChart N k l)
              (omega k) (eta l)) := by
  rw [unitTorusPeriodizedSquareDyadicNormalizedStretch_action_finiteFourierReconstruction
    hN]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  have hident :=
    apply_localizedStretchTensorSymbol_eq_delta_localizedCoherentProjection
      ((1 : ℝ) / N) (squareDyadicEuclideanFrequencyPair N k l)
      (omega k) (eta l)
  unfold localizedStretchTensorSymbol at hident
  push_cast at hident
  rw [euclideanToFrequencyPairEquiv_squareDyadicEuclideanFrequencyPair] at hident
  convert hident using 1 <;> norm_num

/-- Real-valued form of the uniform torus mass estimate, together with the
integrability certificate used by the bilinear Young inequality. -/
theorem exists_uniform_unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel_integral_norm :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      Integrable
          (unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel N)
          frequencyPairUnitTorusMeasure ∧
        (∫ q : FrequencyPairUnitTorus,
          ‖unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel N q‖
            ∂frequencyPairUnitTorusMeasure) ≤ C / N := by
  rcases
      exists_uniform_unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hKint :=
    integrable_unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel hN
  refine ⟨hKint, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (div_nonneg hC hNR.le)).mp
  rw [ofReal_integral_norm_eq_lintegral_enorm hKint]
  exact hmass N hN

/-- **Cardinality-free square-dyadic endpoint estimate.**  The exact finite
Fourier realization is bounded by `C/N` with no dependence on either Fourier
support cardinality. -/
theorem exists_uniform_finiteFourierSquareDyadicStretch_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ (s t : Finset Wavevector) (omega eta : FourierVelocity)
        (x : BilinearSpatialTorus) (M P : ℝ),
        (∀ y, ‖finiteFourierReconstruction s omega y‖ ≤ M) →
        (∀ y, ‖finiteFourierReconstruction t eta y‖ ≤ P) →
        ‖torusBilinearKernelAction
            (unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel N)
            (finiteFourierReconstruction s omega)
            (finiteFourierReconstruction t eta) x‖ ≤
          9 * (C / N) * M * P := by
  rcases
      exists_uniform_unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel_integral_norm with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro N hN s t omega eta x M P homega heta
  rcases hmass N hN with ⟨hKint, hKmass⟩
  have hM : 0 ≤ M :=
    (norm_nonneg (finiteFourierReconstruction s omega x)).trans (homega x)
  have hP : 0 ≤ P :=
    (norm_nonneg (finiteFourierReconstruction t eta x)).trans (heta x)
  calc
    ‖torusBilinearKernelAction
        (unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel N)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x‖ ≤
        9 * (∫ q : FrequencyPairUnitTorus,
          ‖unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel N q‖
            ∂frequencyPairUnitTorusMeasure) * M * P := by
      exact norm_torusBilinearKernelAction_le _ _ _ x M P hKint
        (measurable_unitTorusPeriodizedSquareDyadicNormalizedStretchTensorKernel
          N)
        (continuous_finiteFourierReconstruction s omega)
        (continuous_finiteFourierReconstruction t eta) homega heta
    _ ≤ 9 * (C / N) * M * P := by
      gcongr

end PancakeSquareDyadicFiniteTransfer
end NavierStokes
end FluidDynamics
end Mettapedia
