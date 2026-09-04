import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAnnularMultiplierAssembly
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
namespace PancakeAnnularFrozenFrameTransfer

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
open scoped ENNReal FourierTransform SchwartzMap

/-! ## Aperture and square-dyadic cover scaling -/

def anisotropicAnnularTensorKernel
    (delta : ℝ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  anisotropicFrequencyPairKernelRescaling delta
    (annularFourChartTensorKernel delta) x

theorem anisotropicAnnularTensorKernel_continuous (delta : ℝ) :
    Continuous (anisotropicAnnularTensorKernel delta) :=
  continuous_anisotropicFrequencyPairKernelRescaling delta _
    (annularFourChartTensorKernel delta).continuous

theorem anisotropicAnnularTensorKernel_integrable
    {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (anisotropicAnnularTensorKernel delta) :=
  anisotropicFrequencyPairKernelRescaling_integrable delta hdelta.ne'
    (annularFourChartTensorKernel delta)

theorem fourier_anisotropicAnnularTensorKernel
    {delta : ℝ} (hdelta : 0 < delta) (xi : EuclideanFrequencyPair) :
    FourierTransform.fourier (anisotropicAnnularTensorKernel delta) xi =
      ((delta : ℝ) : ℂ) • annularFourChartTensorSymbol delta
        (anisotropicFrequencyPairReciprocalScaling delta xi) := by
  unfold anisotropicAnnularTensorKernel
  rw [fourier_anisotropicFrequencyPairKernelRescaling
    (annularFourChartTensorKernel delta)
    (annularFourChartTensorKernel delta).integrable hdelta
    (rescaledBilinearKernel_kernelInBilinearCoordinates_integrable
      delta hdelta.ne' (annularFourChartTensorKernel delta))]
  congr 1
  change FourierTransform.fourier
      ((annularFourChartTensorKernel delta :
        SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator) :
          EuclideanFrequencyPair → CoherentBilinearOperator)
      (anisotropicFrequencyPairReciprocalScaling delta xi) = _
  rw [← SchwartzMap.fourier_coe]
  exact congrArg
    (fun f : SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator ↦
      f (anisotropicFrequencyPairReciprocalScaling delta xi))
    (fourier_annularFourChartTensorKernel delta)

theorem integral_norm_anisotropicAnnularTensorKernel
    {delta : ℝ} (hdelta : 0 < delta) :
    (∫ x, ‖anisotropicAnnularTensorKernel delta x‖) =
      delta * ∫ x, ‖annularFourChartTensorKernel delta x‖ :=
  integral_norm_anisotropicSchwartzFrequencyPairKernelRescaling
    (annularFourChartTensorKernel delta) hdelta

def annularSquareDyadicCoverKernel
    (N : ℕ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  isotropicFrequencyPairKernelRescaling ((N : ℝ) ^ 2)
    (anisotropicAnnularTensorKernel ((1 : ℝ) / N)) x

def rotatedAnnularSquareDyadicCoverKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  rotateFrequencyPairKernel R (annularSquareDyadicCoverKernel N) x

theorem rotatedAnnularSquareDyadicCoverKernel_continuous
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) : Continuous (rotatedAnnularSquareDyadicCoverKernel R N) := by
  apply continuous_rotateFrequencyPairKernel
  unfold annularSquareDyadicCoverKernel isotropicFrequencyPairKernelRescaling
  exact continuous_const.smul
    ((anisotropicAnnularTensorKernel_continuous ((1 : ℝ) / N)).comp
      (continuous_const.smul continuous_id))

theorem rotatedAnnularSquareDyadicCoverKernel_integrable
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) :
    Integrable (rotatedAnnularSquareDyadicCoverKernel R N) := by
  apply (integrable_rotateFrequencyPairKernel_iff R _).2
  unfold annularSquareDyadicCoverKernel
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  exact integrable_isotropicFrequencyPairKernelRescaling _
    (anisotropicAnnularTensorKernel_integrable (one_div_pos.mpr hNR))
    (pow_pos hNR 2)

theorem fourier_rotatedAnnularSquareDyadicCoverKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) (xi : EuclideanFrequencyPair) :
    FourierTransform.fourier
        (rotatedAnnularSquareDyadicCoverKernel R N) xi =
      ((((1 : ℝ) / N) : ℂ)) •
        annularFourChartTensorSymbol ((1 : ℝ) / N)
          (anisotropicFrequencyPairReciprocalScaling ((1 : ℝ) / N)
            ((((N : ℝ) ^ 2)⁻¹) • R xi)) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  unfold rotatedAnnularSquareDyadicCoverKernel annularSquareDyadicCoverKernel
  rw [fourier_rotateFrequencyPairKernel,
    fourier_isotropicFrequencyPairKernelRescaling _ (pow_pos hNR 2),
    fourier_anisotropicAnnularTensorKernel (one_div_pos.mpr hNR)]
  push_cast
  congr 1

theorem integral_norm_rotatedAnnularSquareDyadicCoverKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) :
    (∫ x, ‖rotatedAnnularSquareDyadicCoverKernel R N x‖) =
      ((1 : ℝ) / N) *
        ∫ x, ‖annularFourChartTensorKernel ((1 : ℝ) / N) x‖ := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  unfold rotatedAnnularSquareDyadicCoverKernel
  rw [integral_norm_rotateFrequencyPairKernel]
  unfold annularSquareDyadicCoverKernel
  rw [integral_norm_isotropicFrequencyPairKernelRescaling _ (pow_pos hNR 2),
    integral_norm_anisotropicAnnularTensorKernel (one_div_pos.mpr hNR)]

/-! ## Periodization and exact Fourier coefficients -/

def periodizedRotatedAnnularSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  addPeriodization (G := StandardFrequencyPairLattice)
    (rotatedAnnularSquareDyadicCoverKernel R N) x

theorem measurable_periodizedRotatedAnnularSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair) (N : ℕ) :
    Measurable (periodizedRotatedAnnularSquareDyadicKernel R N) :=
  measurable_addPeriodization _
    (rotatedAnnularSquareDyadicCoverKernel_continuous R N).measurable

theorem setIntegral_character_periodizedRotatedAnnularSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) (n : FrequencyPairWavevector) :
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x •
          periodizedRotatedAnnularSquareDyadicKernel R N x) =
      ((((1 : ℝ) / N) : ℂ)) •
        annularFourChartTensorSymbol ((1 : ℝ) / N)
          (anisotropicFrequencyPairReciprocalScaling ((1 : ℝ) / N)
            ((((N : ℝ) ^ 2)⁻¹) •
              R (euclideanFrequencyPairOfWavevector n))) := by
  let K := rotatedAnnularSquareDyadicCoverKernel R N
  have hKint : Integrable K :=
    rotatedAnnularSquareDyadicCoverKernel_integrable R hN
  have htransfer := setIntegral_character_smul_addPeriodization_eq
    standardFrequencyPairCell_isAddFundamentalDomain K
    (rotatedAnnularSquareDyadicCoverKernel_continuous R N).measurable hKint
    (euclideanFrequencyPairCharacter n)
    (continuous_euclideanFrequencyPairCharacter n).measurable
    (norm_euclideanFrequencyPairCharacter n)
    (euclideanFrequencyPairCharacter_vadd n)
  calc
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x •
          periodizedRotatedAnnularSquareDyadicKernel R N x) =
        ∫ x, euclideanFrequencyPairCharacter n x • K x := by
      simpa [periodizedRotatedAnnularSquareDyadicKernel, K] using htransfer
    _ = FourierTransform.fourier K
        (euclideanFrequencyPairOfWavevector n) := by
      rw [Real.fourier_eq]
      rfl
    _ = _ := fourier_rotatedAnnularSquareDyadicCoverKernel R hN _

theorem exists_uniform_periodizedRotatedAnnularSquareDyadicKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
        (N : ℕ), 2 ≤ N →
        (∫⁻ x in standardFrequencyPairCell,
          ‖periodizedRotatedAnnularSquareDyadicKernel R N x‖ₑ) ≤
            ENNReal.ofReal (C / N) := by
  rcases exists_uniform_annularFourChartTensorKernel_mass with
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
  let K := rotatedAnnularSquareDyadicCoverKernel R N
  have hKint : Integrable K :=
    rotatedAnnularSquareDyadicCoverKernel_integrable R hN
  calc
    (∫⁻ x in standardFrequencyPairCell,
        ‖periodizedRotatedAnnularSquareDyadicKernel R N x‖ₑ) ≤
        ∫⁻ x, ‖K x‖ₑ := by
      simpa [periodizedRotatedAnnularSquareDyadicKernel, K] using
        setLIntegral_enorm_addPeriodization_le
          standardFrequencyPairCell_isAddFundamentalDomain K
            (rotatedAnnularSquareDyadicCoverKernel_continuous R N).measurable
    _ = ENNReal.ofReal (∫ x, ‖K x‖) := by
      rw [ofReal_integral_eq_lintegral_ofReal hKint.norm]
      · simp only [ofReal_norm]
      · exact ae_of_all _ fun x ↦ norm_nonneg (K x)
    _ = ENNReal.ofReal
        (((1 : ℝ) / N) *
          ∫ x, ‖annularFourChartTensorKernel ((1 : ℝ) / N) x‖) := by
      congr 1
      exact integral_norm_rotatedAnnularSquareDyadicCoverKernel R hN
    _ ≤ ENNReal.ofReal (C / N) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        ((1 : ℝ) / N) *
            ∫ x, ‖annularFourChartTensorKernel ((1 : ℝ) / N) x‖ ≤
            ((1 : ℝ) / N) * C :=
          mul_le_mul_of_nonneg_left (hmass _ hdelta) (one_div_pos.mpr hNR).le
        _ = C / N := by field_simp

/-! ## Unit-torus action -/

def unitTorusPeriodizedRotatedAnnularSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) (q : FrequencyPairUnitTorus) : CoherentBilinearOperator :=
  unitTorusKernelOfEuclideanRepresentative
    (periodizedRotatedAnnularSquareDyadicKernel R N) q

theorem measurable_unitTorusPeriodizedRotatedAnnularSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair) (N : ℕ) :
    Measurable (unitTorusPeriodizedRotatedAnnularSquareDyadicKernel R N) :=
  measurable_unitTorusKernelOfEuclideanRepresentative _
    (measurable_periodizedRotatedAnnularSquareDyadicKernel R N)

theorem frequencyPairUnitTorusFourierCoeff_rotatedAnnularSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) (n : FrequencyPairWavevector) :
    frequencyPairUnitTorusFourierCoeff
        (unitTorusPeriodizedRotatedAnnularSquareDyadicKernel R N) n =
      ((((1 : ℝ) / N) : ℂ)) •
        annularFourChartTensorSymbol ((1 : ℝ) / N)
          (anisotropicFrequencyPairReciprocalScaling ((1 : ℝ) / N)
            ((((N : ℝ) ^ 2)⁻¹) •
              R (euclideanFrequencyPairOfWavevector n))) := by
  unfold unitTorusPeriodizedRotatedAnnularSquareDyadicKernel
  rw [frequencyPairUnitTorusFourierCoeff_unitTorusKernelOfEuclideanRepresentative]
  exact setIntegral_character_periodizedRotatedAnnularSquareDyadicKernel R hN n

theorem exists_uniform_unitTorusRotatedAnnularSquareDyadicKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
        (N : ℕ), 2 ≤ N →
        (∫⁻ q : FrequencyPairUnitTorus,
          ‖unitTorusPeriodizedRotatedAnnularSquareDyadicKernel R N q‖ₑ
            ∂frequencyPairUnitTorusMeasure) ≤ ENNReal.ofReal (C / N) := by
  rcases exists_uniform_periodizedRotatedAnnularSquareDyadicKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro R N hN
  unfold unitTorusPeriodizedRotatedAnnularSquareDyadicKernel
  rw [lintegral_enorm_unitTorusKernelOfEuclideanRepresentative]
  · exact hmass R N hN
  · exact measurable_periodizedRotatedAnnularSquareDyadicKernel R N

theorem integrable_unitTorusRotatedAnnularSquareDyadicKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) :
    Integrable (unitTorusPeriodizedRotatedAnnularSquareDyadicKernel R N)
      frequencyPairUnitTorusMeasure := by
  rcases exists_uniform_unitTorusRotatedAnnularSquareDyadicKernel_mass with
    ⟨C, _hC, hmass⟩
  refine ⟨(measurable_unitTorusPeriodizedRotatedAnnularSquareDyadicKernel
    R N).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (hmass R N hN) ENNReal.ofReal_lt_top

theorem unitTorusRotatedAnnularSquareDyadic_action_finiteFourierReconstruction
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    torusBilinearKernelAction
        (unitTorusPeriodizedRotatedAnnularSquareDyadicKernel R N)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      ∑ k ∈ s, ∑ l ∈ t,
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          applyCoherentBilinearOperator
            (((((1 : ℝ) / N) : ℂ)) •
              annularFourChartTensorSymbol ((1 : ℝ) / N)
                (frozenFrameSquareDyadicEuclideanFrequencyPair R N k l))
            (omega k) (eta l) := by
  rw [torusBilinearKernelAction_finiteFourierReconstruction _
    (integrable_unitTorusRotatedAnnularSquareDyadicKernel R hN)]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [frequencyPairUnitTorusFourierCoeff_rotatedAnnularSquareDyadicKernel R hN]
  rfl

/-- Exact uncut coherent interaction for finite Fourier fields whose rotated
normalized mode pairs lie in the annular support. -/
theorem unitTorusRotatedAnnularSquareDyadic_action_eq_coherent
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus)
    (hannular : ∀ k ∈ s, ∀ l ∈ t,
      InNormalizedPancakeAnnulus
          (frozenFrameSquareDyadicFrequencyPairChart R N k l).1 ∧
        InNormalizedPancakeAnnulus
          (frozenFrameSquareDyadicFrequencyPairChart R N k l).2) :
    torusBilinearKernelAction
        (unitTorusPeriodizedRotatedAnnularSquareDyadicKernel R N)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      ∑ k ∈ s, ∑ l ∈ t,
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          (((((1 : ℝ) / N) : ℂ)) •
            coherentProjectedNormalizedStretch ((1 : ℝ) / N)
              (frozenFrameSquareDyadicFrequencyPairChart R N k l)
              (omega k) (eta l)) := by
  rw [unitTorusRotatedAnnularSquareDyadic_action_finiteFourierReconstruction
    R hN]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  rw [applyCoherentBilinearOperator_smul_tensor]
  congr 1
  exact apply_annularFourChartTensorSymbol_eq_coherent
    ((1 : ℝ) / N)
    (frozenFrameSquareDyadicEuclideanFrequencyPair R N k l)
    (omega k) (eta l) (hannular k hk l hl).1 (hannular k hk l hl).2

theorem exists_uniform_frozenFrameAnnularSquareDyadic_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
        (N : ℕ), 2 ≤ N →
      ∀ (f g : BilinearSpatialTorus → ComplexVec3)
        (x : BilinearSpatialTorus) (M P : ℝ),
        Continuous f → Continuous g →
        (∀ y, ‖f y‖ ≤ M) → (∀ y, ‖g y‖ ≤ P) →
        ‖torusBilinearKernelAction
            (unitTorusPeriodizedRotatedAnnularSquareDyadicKernel R N)
            f g x‖ ≤ 9 * (C / N) * M * P := by
  rcases exists_uniform_unitTorusRotatedAnnularSquareDyadicKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro R N hN f g x M P hf hg hfb hgb
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hKint := integrable_unitTorusRotatedAnnularSquareDyadicKernel R hN
  have hmassReal :
      (∫ q : FrequencyPairUnitTorus,
        ‖unitTorusPeriodizedRotatedAnnularSquareDyadicKernel R N q‖
          ∂frequencyPairUnitTorusMeasure) ≤ C / N := by
    apply (ENNReal.ofReal_le_ofReal_iff (div_nonneg hC hNR.le)).mp
    rw [ofReal_integral_norm_eq_lintegral_enorm hKint]
    exact hmass R N hN
  calc
    ‖torusBilinearKernelAction
        (unitTorusPeriodizedRotatedAnnularSquareDyadicKernel R N)
        f g x‖ ≤
        9 * (∫ q : FrequencyPairUnitTorus,
          ‖unitTorusPeriodizedRotatedAnnularSquareDyadicKernel R N q‖
            ∂frequencyPairUnitTorusMeasure) * M * P := by
      exact norm_torusBilinearKernelAction_le _ f g x M P hKint
        (measurable_unitTorusPeriodizedRotatedAnnularSquareDyadicKernel R N)
        hf hg hfb hgb
    _ ≤ 9 * (C / N) * M * P := by
      have hM : 0 ≤ M := (norm_nonneg (f x)).trans (hfb x)
      have hP : 0 ≤ P := (norm_nonneg (g x)).trans (hgb x)
      gcongr

end PancakeAnnularFrozenFrameTransfer
end NavierStokes
end FluidDynamics
end Mettapedia
