import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBufferedAnnularMultiplier
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFrozenFrameKernelTransfer

/-!
# Frozen-frame transfer of the assembled annular multiplier

This module carries the fixed four-chart annular kernel through aperture
scaling, square-dyadic shell scaling, frozen rotations, periodization, and the
unit-torus bilinear action.  The result is an exact finite-Fourier formula on
the full normalized annular support and a cardinality-free `C/N` endpoint
uniform in the frozen frame.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeBufferedAnnularFrozenFrameTransfer

open MeasureTheory
open Set
open PeriodicFourierTriad
open PancakeBilinearKernelScaling
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentSymbol
open PancakeFiniteFourierBilinearTransfer
open PancakeDyadicKernelScaling
open PancakeSquareDyadicFiniteTransfer
open PancakeFrozenFrameKernelTransfer
open PancakeSmoothCoherentStretchSymbol
open PancakeAnnularChartCutoff
open PancakeAnnularMultiplierAssembly
open PancakeBufferedAnnularMultiplier
open scoped ENNReal FourierTransform SchwartzMap

/-! ## Aperture and square-dyadic cover scaling -/

def anisotropicLocalizationTensorKernel
    (delta : ℝ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  anisotropicFrequencyPairKernelRescaling delta
    (localizationFourChartTensorKernel delta) x

theorem anisotropicLocalizationTensorKernel_continuous (delta : ℝ) :
    Continuous (anisotropicLocalizationTensorKernel delta) :=
  continuous_anisotropicFrequencyPairKernelRescaling delta _
    (localizationFourChartTensorKernel delta).continuous

theorem anisotropicLocalizationTensorKernel_integrable
    {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (anisotropicLocalizationTensorKernel delta) :=
  anisotropicFrequencyPairKernelRescaling_integrable delta hdelta.ne'
    (localizationFourChartTensorKernel delta)

theorem fourier_anisotropicLocalizationTensorKernel
    {delta : ℝ} (hdelta : 0 < delta) (xi : EuclideanFrequencyPair) :
    FourierTransform.fourier (anisotropicLocalizationTensorKernel delta) xi =
      ((delta : ℝ) : ℂ) • localizationFourChartTensorSymbol delta
        (anisotropicFrequencyPairReciprocalScaling delta xi) := by
  unfold anisotropicLocalizationTensorKernel
  rw [fourier_anisotropicFrequencyPairKernelRescaling
    (localizationFourChartTensorKernel delta)
    (localizationFourChartTensorKernel delta).integrable hdelta
    (rescaledBilinearKernel_kernelInBilinearCoordinates_integrable
      delta hdelta.ne' (localizationFourChartTensorKernel delta))]
  congr 1
  change FourierTransform.fourier
      ((localizationFourChartTensorKernel delta :
        SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator) :
          EuclideanFrequencyPair → CoherentBilinearOperator)
      (anisotropicFrequencyPairReciprocalScaling delta xi) = _
  rw [← SchwartzMap.fourier_coe]
  exact congrArg
    (fun f : SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator ↦
      f (anisotropicFrequencyPairReciprocalScaling delta xi))
    (fourier_localizationFourChartTensorKernel delta)

theorem integral_norm_anisotropicLocalizationTensorKernel
    {delta : ℝ} (hdelta : 0 < delta) :
    (∫ x, ‖anisotropicLocalizationTensorKernel delta x‖) =
      delta * ∫ x, ‖localizationFourChartTensorKernel delta x‖ :=
  integral_norm_anisotropicSchwartzFrequencyPairKernelRescaling
    (localizationFourChartTensorKernel delta) hdelta

def localizationSquareDyadicCoverKernel
    (N : ℕ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  isotropicFrequencyPairKernelRescaling ((N : ℝ) ^ 2)
    (anisotropicLocalizationTensorKernel ((1 : ℝ) / N)) x

def rotatedLocalizationSquareDyadicCoverKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  rotateFrequencyPairKernel R (localizationSquareDyadicCoverKernel N) x

theorem rotatedLocalizationSquareDyadicCoverKernel_continuous
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) : Continuous (rotatedLocalizationSquareDyadicCoverKernel R N) := by
  apply continuous_rotateFrequencyPairKernel
  unfold localizationSquareDyadicCoverKernel isotropicFrequencyPairKernelRescaling
  exact ((anisotropicLocalizationTensorKernel_continuous ((1 : ℝ) / N)).comp
    (continuous_id.const_smul ((N : ℝ) ^ 2))).const_smul ((((N : ℝ) ^ 2) ^ 6 : ℝ) : ℂ)

theorem rotatedLocalizationSquareDyadicCoverKernel_integrable
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) :
    Integrable (rotatedLocalizationSquareDyadicCoverKernel R N) := by
  apply (integrable_rotateFrequencyPairKernel_iff R _).2
  unfold localizationSquareDyadicCoverKernel
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  exact integrable_isotropicFrequencyPairKernelRescaling _
    (anisotropicLocalizationTensorKernel_integrable (one_div_pos.mpr hNR))
    (pow_pos hNR 2)

theorem fourier_rotatedLocalizationSquareDyadicCoverKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) (xi : EuclideanFrequencyPair) :
    FourierTransform.fourier
        (rotatedLocalizationSquareDyadicCoverKernel R N) xi =
      ((((1 : ℝ) / N) : ℂ)) •
        localizationFourChartTensorSymbol ((1 : ℝ) / N)
          (anisotropicFrequencyPairReciprocalScaling ((1 : ℝ) / N)
            ((((N : ℝ) ^ 2)⁻¹) • R xi)) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  unfold rotatedLocalizationSquareDyadicCoverKernel localizationSquareDyadicCoverKernel
  rw [fourier_rotateFrequencyPairKernel,
    fourier_isotropicFrequencyPairKernelRescaling _ (pow_pos hNR 2),
    fourier_anisotropicLocalizationTensorKernel (one_div_pos.mpr hNR)]
  push_cast
  congr 1

theorem integral_norm_rotatedLocalizationSquareDyadicCoverKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) :
    (∫ x, ‖rotatedLocalizationSquareDyadicCoverKernel R N x‖) =
      ((1 : ℝ) / N) *
        ∫ x, ‖localizationFourChartTensorKernel ((1 : ℝ) / N) x‖ := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  unfold rotatedLocalizationSquareDyadicCoverKernel
  rw [integral_norm_rotateFrequencyPairKernel]
  unfold localizationSquareDyadicCoverKernel
  rw [integral_norm_isotropicFrequencyPairKernelRescaling _ (pow_pos hNR 2),
    integral_norm_anisotropicLocalizationTensorKernel (one_div_pos.mpr hNR)]

/-! ## Periodization and exact Fourier coefficients -/

def periodizedRotatedLocalizationSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  addPeriodization (G := StandardFrequencyPairLattice)
    (rotatedLocalizationSquareDyadicCoverKernel R N) x

theorem measurable_periodizedRotatedLocalizationSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair) (N : ℕ) :
    Measurable (periodizedRotatedLocalizationSquareDyadicKernel R N) :=
  measurable_addPeriodization _
    (rotatedLocalizationSquareDyadicCoverKernel_continuous R N).measurable

theorem setIntegral_character_periodizedRotatedLocalizationSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) (n : FrequencyPairWavevector) :
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x •
          periodizedRotatedLocalizationSquareDyadicKernel R N x) =
      ((((1 : ℝ) / N) : ℂ)) •
        localizationFourChartTensorSymbol ((1 : ℝ) / N)
          (anisotropicFrequencyPairReciprocalScaling ((1 : ℝ) / N)
            ((((N : ℝ) ^ 2)⁻¹) •
              R (euclideanFrequencyPairOfWavevector n))) := by
  let K := rotatedLocalizationSquareDyadicCoverKernel R N
  have hKint : Integrable K :=
    rotatedLocalizationSquareDyadicCoverKernel_integrable R hN
  have htransfer := setIntegral_character_smul_addPeriodization_eq
    standardFrequencyPairCell_isAddFundamentalDomain K
    (rotatedLocalizationSquareDyadicCoverKernel_continuous R N).measurable hKint
    (euclideanFrequencyPairCharacter n)
    (continuous_euclideanFrequencyPairCharacter n).measurable
    (norm_euclideanFrequencyPairCharacter n)
    (euclideanFrequencyPairCharacter_vadd n)
  calc
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x •
          periodizedRotatedLocalizationSquareDyadicKernel R N x) =
        ∫ x, euclideanFrequencyPairCharacter n x • K x := by
      simpa [periodizedRotatedLocalizationSquareDyadicKernel, K] using htransfer
    _ = FourierTransform.fourier K
        (euclideanFrequencyPairOfWavevector n) := by
      rw [Real.fourier_eq]
      rfl
    _ = _ := fourier_rotatedLocalizationSquareDyadicCoverKernel R hN _

theorem exists_uniform_periodizedRotatedLocalizationSquareDyadicKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
        (N : ℕ), 2 ≤ N →
        (∫⁻ x in standardFrequencyPairCell,
          ‖periodizedRotatedLocalizationSquareDyadicKernel R N x‖ₑ) ≤
            ENNReal.ofReal (C / N) := by
  rcases exists_uniform_localizationFourChartTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro R N hN
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hdelta : (1 : ℝ) / N ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor
    · exact (one_div_pos.mpr hNR).le
    · apply (div_le_iff₀' hNR).2
      have hNR2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
  let K := rotatedLocalizationSquareDyadicCoverKernel R N
  have hKint : Integrable K :=
    rotatedLocalizationSquareDyadicCoverKernel_integrable R hN
  calc
    (∫⁻ x in standardFrequencyPairCell,
        ‖periodizedRotatedLocalizationSquareDyadicKernel R N x‖ₑ) ≤
        ∫⁻ x, ‖K x‖ₑ := by
      simpa [periodizedRotatedLocalizationSquareDyadicKernel, K] using
        setLIntegral_enorm_addPeriodization_le
          standardFrequencyPairCell_isAddFundamentalDomain K
            (rotatedLocalizationSquareDyadicCoverKernel_continuous R N).measurable
    _ = ENNReal.ofReal (∫ x, ‖K x‖) := by
      rw [ofReal_integral_eq_lintegral_ofReal hKint.norm]
      · simp only [ofReal_norm]
      · exact ae_of_all _ fun x ↦ norm_nonneg (K x)
    _ = ENNReal.ofReal
        (((1 : ℝ) / N) *
          ∫ x, ‖localizationFourChartTensorKernel ((1 : ℝ) / N) x‖) := by
      congr 1
      exact integral_norm_rotatedLocalizationSquareDyadicCoverKernel R hN
    _ ≤ ENNReal.ofReal (C / N) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        ((1 : ℝ) / N) *
            ∫ x, ‖localizationFourChartTensorKernel ((1 : ℝ) / N) x‖ ≤
            ((1 : ℝ) / N) * C :=
          mul_le_mul_of_nonneg_left (hmass _ hdelta) (one_div_pos.mpr hNR).le
        _ = C / N := by field_simp

/-! ## Unit-torus action -/

def unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) (q : FrequencyPairUnitTorus) : CoherentBilinearOperator :=
  unitTorusKernelOfEuclideanRepresentative
    (periodizedRotatedLocalizationSquareDyadicKernel R N) q

theorem measurable_unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair) (N : ℕ) :
    Measurable (unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel R N) :=
  measurable_unitTorusKernelOfEuclideanRepresentative _
    (measurable_periodizedRotatedLocalizationSquareDyadicKernel R N)

theorem frequencyPairUnitTorusFourierCoeff_rotatedLocalizationSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) (n : FrequencyPairWavevector) :
    frequencyPairUnitTorusFourierCoeff
        (unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel R N) n =
      ((((1 : ℝ) / N) : ℂ)) •
        localizationFourChartTensorSymbol ((1 : ℝ) / N)
          (anisotropicFrequencyPairReciprocalScaling ((1 : ℝ) / N)
            ((((N : ℝ) ^ 2)⁻¹) •
              R (euclideanFrequencyPairOfWavevector n))) := by
  unfold unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel
  rw [frequencyPairUnitTorusFourierCoeff_unitTorusKernelOfEuclideanRepresentative]
  exact setIntegral_character_periodizedRotatedLocalizationSquareDyadicKernel R hN n

theorem exists_uniform_unitTorusRotatedLocalizationSquareDyadicKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
        (N : ℕ), 2 ≤ N →
        (∫⁻ q : FrequencyPairUnitTorus,
          ‖unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel R N q‖ₑ
            ∂frequencyPairUnitTorusMeasure) ≤ ENNReal.ofReal (C / N) := by
  rcases exists_uniform_periodizedRotatedLocalizationSquareDyadicKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro R N hN
  unfold unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel
  rw [lintegral_enorm_unitTorusKernelOfEuclideanRepresentative]
  · exact hmass R N hN
  · exact measurable_periodizedRotatedLocalizationSquareDyadicKernel R N

theorem integrable_unitTorusRotatedLocalizationSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) :
    Integrable (unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel R N)
      frequencyPairUnitTorusMeasure := by
  rcases exists_uniform_unitTorusRotatedLocalizationSquareDyadicKernel_mass with
    ⟨C, _hC, hmass⟩
  refine ⟨(measurable_unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel
    R N).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (hmass R N hN) ENNReal.ofReal_lt_top

theorem unitTorusRotatedLocalizationSquareDyadic_action_finiteFourierReconstruction
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    torusBilinearKernelAction
        (unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel R N)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      ∑ k ∈ s, ∑ l ∈ t,
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          applyCoherentBilinearOperator
            (((((1 : ℝ) / N) : ℂ)) •
              localizationFourChartTensorSymbol ((1 : ℝ) / N)
                (frozenFrameSquareDyadicEuclideanFrequencyPair R N k l))
            (omega k) (eta l) := by
  rw [torusBilinearKernelAction_finiteFourierReconstruction _
    (integrable_unitTorusRotatedLocalizationSquareDyadicKernel R hN)]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [frequencyPairUnitTorusFourierCoeff_rotatedLocalizationSquareDyadicKernel R hN]
  rfl

/-- Exact uncut coherent interaction for finite Fourier fields whose rotated
normalized mode pairs lie in the annular support. -/
theorem unitTorusRotatedLocalizationSquareDyadic_action_eq_coherent
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus)
    (hbuffer : ∀ k ∈ s, ∀ l ∈ t,
      InLocalizationBufferedPancakeAnnulus
          (frozenFrameSquareDyadicFrequencyPairChart R N k l).1 ∧
        InLocalizationBufferedPancakeAnnulus
          (frozenFrameSquareDyadicFrequencyPairChart R N k l).2) :
    torusBilinearKernelAction
        (unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel R N)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      ∑ k ∈ s, ∑ l ∈ t,
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          (((((1 : ℝ) / N) : ℂ)) •
            coherentProjectedNormalizedStretch ((1 : ℝ) / N)
              (frozenFrameSquareDyadicFrequencyPairChart R N k l)
              (omega k) (eta l)) := by
  rw [unitTorusRotatedLocalizationSquareDyadic_action_finiteFourierReconstruction
    R hN]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  rw [applyCoherentBilinearOperator_smul_tensor]
  congr 1
  exact apply_localizationFourChartTensorSymbol_eq_coherent
    ((1 : ℝ) / N)
    (frozenFrameSquareDyadicEuclideanFrequencyPair R N k l)
    (omega k) (eta l) (hbuffer k hk l hl).1 (hbuffer k hk l hl).2

theorem exists_uniform_frozenFrameLocalizationSquareDyadic_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
        (N : ℕ), 2 ≤ N →
      ∀ (f g : BilinearSpatialTorus → ComplexVec3)
        (x : BilinearSpatialTorus) (M P : ℝ),
        Continuous f → Continuous g →
        (∀ y, ‖f y‖ ≤ M) → (∀ y, ‖g y‖ ≤ P) →
        ‖torusBilinearKernelAction
            (unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel R N)
            f g x‖ ≤ 9 * (C / N) * M * P := by
  rcases exists_uniform_unitTorusRotatedLocalizationSquareDyadicKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro R N hN f g x M P hf hg hfb hgb
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hKint := integrable_unitTorusRotatedLocalizationSquareDyadicKernel R hN
  have hmassReal :
      (∫ q : FrequencyPairUnitTorus,
        ‖unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel R N q‖
          ∂frequencyPairUnitTorusMeasure) ≤ C / N := by
    apply (ENNReal.ofReal_le_ofReal_iff (div_nonneg hC hNR.le)).mp
    rw [ofReal_integral_norm_eq_lintegral_enorm hKint]
    exact hmass R N hN
  calc
    ‖torusBilinearKernelAction
        (unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel R N)
        f g x‖ ≤
        9 * (∫ q : FrequencyPairUnitTorus,
          ‖unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel R N q‖
            ∂frequencyPairUnitTorusMeasure) * M * P := by
      exact norm_torusBilinearKernelAction_le _ f g x M P hKint
        (measurable_unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel R N)
        hf hg hfb hgb
    _ ≤ 9 * (C / N) * M * P := by
      have hM : 0 ≤ M := (norm_nonneg (f x)).trans (hfb x)
      have hP : 0 ≤ P := (norm_nonneg (g x)).trans (hgb x)
      gcongr

end PancakeBufferedAnnularFrozenFrameTransfer
end NavierStokes
end FluidDynamics
end Mettapedia
