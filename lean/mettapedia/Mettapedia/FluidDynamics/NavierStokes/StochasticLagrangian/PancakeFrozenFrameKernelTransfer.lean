import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSquareDyadicFiniteTransfer
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFrameCovariance

/-!
# Frozen-frame transfer for the square-dyadic pancake kernel

An arbitrary spatial rotation does not preserve the integer lattice.  The
correct operation is therefore to rotate the Euclidean cover kernel first and
only then periodize it on the fixed standard lattice.  This module establishes
the generic orthogonal covariance facts needed for that construction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeFrozenFrameKernelTransfer

open MeasureTheory
open PancakeBilinearKernelScaling
open PancakeBilinearPeriodization
open PancakeDyadicKernelScaling
open PancakeFiniteFourierBilinearTransfer
open PancakeFrameCovariance
open PancakePeriodicCoherentSplit
open PancakeRealCoherentPairEstimate
open PancakeSquareDyadicFiniteTransfer
open PancakeSmoothCoherentSymbol
open PancakeSmoothCoherentStretchSymbol
open PancakeUniformKernelFamily
open PeriodicFourierTriad
open Set
open scoped FourierTransform

/-- Three-dimensional Euclidean frequency space for a single input. -/
abbrev EuclideanWavevector := EuclideanSpace ℝ (Fin 3)

/-- Isometric splitting of six Euclidean coordinates into two Euclidean
three-vectors, retaining the Hilbert product norm. -/
def frequencyPairSplitLinearIsometryEquiv :
    EuclideanFrequencyPair ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanWavevector × EuclideanWavevector) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin (3 + 3)).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2
      (fun _ : Fin 3 ⊕ Fin 3 ↦ ℝ))

/-- Apply the same frozen orthogonal frame to the source and receiver
frequency variables. -/
def pairFrameLinearIsometryEquiv
    (R : EuclideanWavevector ≃ₗᵢ[ℝ] EuclideanWavevector) :
    EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair :=
  frequencyPairSplitLinearIsometryEquiv.trans
    ((LinearIsometryEquiv.withLpProdCongr 2 R R).trans
      frequencyPairSplitLinearIsometryEquiv.symm)

/-! ## Bridge from algebraic oriented frames to Euclidean isometries -/

/-- The real-linear equivalence carried by an algebraic oriented frame. -/
def orientedFrameRealLinearEquiv (F : OrientedFrameEquiv) :
    RealVec3 ≃ₗ[ℝ] RealVec3 :=
  LinearEquiv.ofBijective
    { toFun := F.toFun
      map_add' := F.map_add
      map_smul' := F.map_smul }
    F.bijective

/-- Conjugate an algebraic oriented frame through the coordinate
identification with three-dimensional Euclidean space. -/
def orientedFrameEuclideanLinearEquiv (F : OrientedFrameEquiv) :
    EuclideanWavevector ≃ₗ[ℝ] EuclideanWavevector :=
  euclideanToRealVec3LinearEquiv.trans
    ((orientedFrameRealLinearEquiv F).trans
      euclideanToRealVec3LinearEquiv.symm)

/-- Dot-product preservation of the algebraic frame gives exact Euclidean
norm preservation after coordinate transport. -/
theorem orientedFrameEuclideanLinearEquiv_norm_map
    (F : OrientedFrameEquiv) (xi : EuclideanWavevector) :
    ‖orientedFrameEuclideanLinearEquiv F xi‖ = ‖xi‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_three]
  have h := F.map_normSq (euclideanToRealVec3LinearEquiv xi)
  simp [orientedFrameEuclideanLinearEquiv,
    orientedFrameRealLinearEquiv, euclideanToRealVec3LinearEquiv,
    normSq, dot, pow_two] at h ⊢
  exact h

/-- Every algebraic oriented frame therefore determines the Euclidean
linear isometry used by the Fourier kernel construction. -/
def orientedFrameEuclideanLinearIsometryEquiv (F : OrientedFrameEquiv) :
    EuclideanWavevector ≃ₗᵢ[ℝ] EuclideanWavevector :=
  ⟨orientedFrameEuclideanLinearEquiv F,
    orientedFrameEuclideanLinearEquiv_norm_map F⟩

@[simp]
theorem orientedFrameEuclideanLinearIsometryEquiv_coordinates
    (F : OrientedFrameEquiv) (xi : EuclideanWavevector) :
    euclideanToRealVec3LinearEquiv
        (orientedFrameEuclideanLinearIsometryEquiv F xi) =
      F.toFun (euclideanToRealVec3LinearEquiv xi) := rfl

/-- Diagonal six-frequency lift of a physical oriented frame. -/
def orientedFrameFrequencyPairLinearIsometryEquiv
    (F : OrientedFrameEquiv) :
    EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair :=
  pairFrameLinearIsometryEquiv
    (orientedFrameEuclideanLinearIsometryEquiv F)

/-- Rotate the Euclidean cover kernel before lattice periodization. -/
def rotateFrequencyPairKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  K (R x)

/-- Orthogonal precomposition preserves continuity. -/
theorem continuous_rotateFrequencyPairKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (hK : Continuous K) :
    Continuous (rotateFrequencyPairKernel R K) :=
  hK.comp R.continuous

/-- Orthogonal precomposition preserves integrability. -/
theorem integrable_rotateFrequencyPairKernel_iff
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (K : EuclideanFrequencyPair → CoherentBilinearOperator) :
    Integrable (rotateFrequencyPairKernel R K) ↔ Integrable K := by
  exact MeasureTheory.integrable_comp R K

/-- Orthogonal precomposition preserves exact `L¹` mass. -/
theorem integral_norm_rotateFrequencyPairKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (K : EuclideanFrequencyPair → CoherentBilinearOperator) :
    (∫ x, ‖rotateFrequencyPairKernel R K x‖) = ∫ x, ‖K x‖ := by
  exact MeasureTheory.integral_comp R (fun x ↦ ‖K x‖)

/-- Orthogonal precomposition rotates the reciprocal argument of the Fourier
transform with no Jacobian loss. -/
theorem fourier_rotateFrequencyPairKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (xi : EuclideanFrequencyPair) :
    FourierTransform.fourier (rotateFrequencyPairKernel R K) xi =
      FourierTransform.fourier K (R xi) := by
  exact Real.fourier_comp_linearIsometry R K xi

/-! ## Rotated square-dyadic cover kernel -/

/-- The nonperiodic square-dyadic cover kernel before a frozen frame is
applied. -/
def squareDyadicCoverKernel
    (N : ℕ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  isotropicFrequencyPairKernelRescaling ((N : ℝ) ^ 2)
    (anisotropicNormalizedStretchTensorKernel ((1 : ℝ) / N)) x

/-- Rotate the square-dyadic Euclidean cover kernel in a frozen orthogonal
frame. -/
def rotatedSquareDyadicCoverKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  rotateFrequencyPairKernel R (squareDyadicCoverKernel N) x

/-- The rotated cover kernel is continuous. -/
theorem rotatedSquareDyadicCoverKernel_continuous
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) : Continuous (rotatedSquareDyadicCoverKernel R N) := by
  apply continuous_rotateFrequencyPairKernel
  unfold squareDyadicCoverKernel isotropicFrequencyPairKernelRescaling
  exact ((anisotropicNormalizedStretchTensorKernel_continuous ((1 : ℝ) / N)).comp
    (continuous_id.const_smul ((N : ℝ) ^ 2))).const_smul ((((N : ℝ) ^ 2) ^ 6 : ℝ) : ℂ)

/-- The rotated cover kernel is integrable at every square-dyadic scale
`N ≥ 2`. -/
theorem rotatedSquareDyadicCoverKernel_integrable
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) :
    Integrable (rotatedSquareDyadicCoverKernel R N) := by
  apply (integrable_rotateFrequencyPairKernel_iff R _).2
  unfold squareDyadicCoverKernel
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  exact integrable_isotropicFrequencyPairKernelRescaling _
    (anisotropicNormalizedStretchTensorKernel_integrable
      (one_div_pos.mpr hNR)) (pow_pos hNR 2)

/-- Exact multiplier of the rotated square-dyadic cover kernel. -/
theorem fourier_rotatedSquareDyadicCoverKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) (xi : EuclideanFrequencyPair) :
    FourierTransform.fourier (rotatedSquareDyadicCoverKernel R N) xi =
      ((((1 : ℝ) / N) : ℂ)) •
        normalizedStretchTensorSymbol explicitBufferedStretchCutoff
          ((1 : ℝ) / N)
          (anisotropicFrequencyPairReciprocalScaling ((1 : ℝ) / N)
            ((((N : ℝ) ^ 2)⁻¹) • R xi)) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  unfold rotatedSquareDyadicCoverKernel squareDyadicCoverKernel
  rw [fourier_rotateFrequencyPairKernel,
    fourier_isotropicFrequencyPairKernelRescaling _ (pow_pos hNR 2),
    fourier_anisotropicNormalizedStretchTensorKernel (one_div_pos.mpr hNR)]
  push_cast
  congr 1

/-- Periodize the rotated Euclidean cover kernel only after the frame has
been applied. -/
def periodizedRotatedSquareDyadicNormalizedStretchTensorKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  addPeriodization (G := StandardFrequencyPairLattice)
    (rotatedSquareDyadicCoverKernel R N) x

/-- The periodized rotated kernel is measurable. -/
theorem measurable_periodizedRotatedSquareDyadicNormalizedStretchTensorKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) :
    Measurable
      (periodizedRotatedSquareDyadicNormalizedStretchTensorKernel R N) :=
  measurable_addPeriodization _
    (rotatedSquareDyadicCoverKernel_continuous R N).measurable

/-- **Exact frozen-frame lattice coefficient.**  The standard lattice is
kept fixed; the reciprocal argument of the cover symbol is rotated instead. -/
theorem setIntegral_character_periodizedRotatedSquareDyadicNormalizedStretchTensorKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) (n : FrequencyPairWavevector) :
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x •
          periodizedRotatedSquareDyadicNormalizedStretchTensorKernel R N x) =
      ((((1 : ℝ) / N) : ℂ)) •
        normalizedStretchTensorSymbol explicitBufferedStretchCutoff
          ((1 : ℝ) / N)
          (anisotropicFrequencyPairReciprocalScaling ((1 : ℝ) / N)
            ((((N : ℝ) ^ 2)⁻¹) •
              R (euclideanFrequencyPairOfWavevector n))) := by
  let K := rotatedSquareDyadicCoverKernel R N
  have hKint : Integrable K := rotatedSquareDyadicCoverKernel_integrable R hN
  have htransfer := setIntegral_character_smul_addPeriodization_eq
    standardFrequencyPairCell_isAddFundamentalDomain K
    (rotatedSquareDyadicCoverKernel_continuous R N).measurable hKint
    (euclideanFrequencyPairCharacter n)
    (continuous_euclideanFrequencyPairCharacter n).measurable
    (norm_euclideanFrequencyPairCharacter n)
    (euclideanFrequencyPairCharacter_vadd n)
  calc
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x •
          periodizedRotatedSquareDyadicNormalizedStretchTensorKernel R N x) =
        ∫ x, euclideanFrequencyPairCharacter n x • K x := by
      simpa [periodizedRotatedSquareDyadicNormalizedStretchTensorKernel, K]
        using htransfer
    _ = FourierTransform.fourier K
        (euclideanFrequencyPairOfWavevector n) := by
      rw [Real.fourier_eq]
      rfl
    _ = _ := fourier_rotatedSquareDyadicCoverKernel R hN _

/-- Frozen orthogonal frames do not alter the exact square-dyadic cover mass. -/
theorem integral_norm_rotatedSquareDyadicCoverKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) :
    (∫ x, ‖rotatedSquareDyadicCoverKernel R N x‖) =
      ((1 : ℝ) / N) *
        ∫ x, ‖normalizedStretchTensorKernel
          explicitBufferedStretchCutoff ((1 : ℝ) / N) x‖ := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  unfold rotatedSquareDyadicCoverKernel
  rw [integral_norm_rotateFrequencyPairKernel]
  unfold squareDyadicCoverKernel
  rw [integral_norm_isotropicFrequencyPairKernelRescaling _ (pow_pos hNR 2),
    integral_norm_anisotropicNormalizedStretchTensorKernel
      (one_div_pos.mpr hNR)]

/-- One `C/N` fundamental-cell mass bound holds uniformly for every frozen
orthogonal frame. -/
theorem exists_uniform_periodizedRotatedSquareDyadicNormalizedStretchTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
        (N : ℕ), 2 ≤ N →
        (∫⁻ x in standardFrequencyPairCell,
          ‖periodizedRotatedSquareDyadicNormalizedStretchTensorKernel R N x‖ₑ) ≤
            ENNReal.ofReal (C / N) := by
  rcases exists_uniform_normalizedStretchTensorKernel_mass with
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
  let K := rotatedSquareDyadicCoverKernel R N
  have hKint : Integrable K := rotatedSquareDyadicCoverKernel_integrable R hN
  calc
    (∫⁻ x in standardFrequencyPairCell,
        ‖periodizedRotatedSquareDyadicNormalizedStretchTensorKernel R N x‖ₑ) ≤
        ∫⁻ x, ‖K x‖ₑ := by
      simpa [periodizedRotatedSquareDyadicNormalizedStretchTensorKernel, K]
        using
          setLIntegral_enorm_addPeriodization_le
            standardFrequencyPairCell_isAddFundamentalDomain K
              (rotatedSquareDyadicCoverKernel_continuous R N).measurable
    _ = ENNReal.ofReal (∫ x, ‖K x‖) := by
      rw [ofReal_integral_eq_lintegral_ofReal hKint.norm]
      · simp only [ofReal_norm]
      · exact ae_of_all _ fun x ↦ norm_nonneg (K x)
    _ = ENNReal.ofReal
        (((1 : ℝ) / N) *
          ∫ x, ‖normalizedStretchTensorKernel
            explicitBufferedStretchCutoff ((1 : ℝ) / N) x‖) := by
      congr 1
      exact integral_norm_rotatedSquareDyadicCoverKernel R hN
    _ ≤ ENNReal.ofReal (C / N) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        ((1 : ℝ) / N) *
            ∫ x, ‖normalizedStretchTensorKernel
              explicitBufferedStretchCutoff ((1 : ℝ) / N) x‖ ≤
            ((1 : ℝ) / N) * C := by
          exact mul_le_mul_of_nonneg_left
            (hmass ((1 : ℝ) / N) hdelta) (one_div_pos.mpr hNR).le
        _ = C / N := by
          field_simp

/-! ## Frozen-frame unit-torus transfer -/

/-- The rotated square-dyadic kernel on the standard unit six-torus. -/
def unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) (q : FrequencyPairUnitTorus) : CoherentBilinearOperator :=
  unitTorusKernelOfEuclideanRepresentative
    (periodizedRotatedSquareDyadicNormalizedStretchTensorKernel R N) q

/-- The frozen-frame unit-torus kernel is measurable. -/
theorem measurable_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) :
    Measurable
      (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
        R N) :=
  measurable_unitTorusKernelOfEuclideanRepresentative _
    (measurable_periodizedRotatedSquareDyadicNormalizedStretchTensorKernel R N)

/-- Exact frozen-frame coefficient on the standard unit torus. -/
theorem frequencyPairUnitTorusFourierCoeff_periodizedRotatedSquareDyadicNormalizedStretchTensorKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) (n : FrequencyPairWavevector) :
    frequencyPairUnitTorusFourierCoeff
        (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
          R N) n =
      ((((1 : ℝ) / N) : ℂ)) •
        normalizedStretchTensorSymbol explicitBufferedStretchCutoff
          ((1 : ℝ) / N)
          (anisotropicFrequencyPairReciprocalScaling ((1 : ℝ) / N)
            ((((N : ℝ) ^ 2)⁻¹) •
              R (euclideanFrequencyPairOfWavevector n))) := by
  unfold unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
  rw [frequencyPairUnitTorusFourierCoeff_unitTorusKernelOfEuclideanRepresentative]
  exact
    setIntegral_character_periodizedRotatedSquareDyadicNormalizedStretchTensorKernel
      R hN n

/-- The `C/N` unit-torus mass estimate is uniform in the frozen frame. -/
theorem exists_uniform_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
        (N : ℕ), 2 ≤ N →
        (∫⁻ q : FrequencyPairUnitTorus,
          ‖unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
            R N q‖ₑ ∂frequencyPairUnitTorusMeasure) ≤
          ENNReal.ofReal (C / N) := by
  rcases
      exists_uniform_periodizedRotatedSquareDyadicNormalizedStretchTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro R N hN
  unfold unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
  rw [lintegral_enorm_unitTorusKernelOfEuclideanRepresentative]
  · exact hmass R N hN
  · exact
      measurable_periodizedRotatedSquareDyadicNormalizedStretchTensorKernel R N

/-- Every frozen-frame unit-torus kernel at scale `N ≥ 2` is Bochner
integrable. -/
theorem integrable_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N) :
    Integrable
      (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel R N)
      frequencyPairUnitTorusMeasure := by
  rcases
      exists_uniform_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel_mass with
    ⟨C, _hC, hmass⟩
  refine
    ⟨(measurable_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
      R N).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (hmass R N hN) ENNReal.ofReal_lt_top

/-- Exact finite-Fourier multiplier formula for an arbitrary frozen
orthogonal frequency frame. -/
theorem unitTorusPeriodizedRotatedSquareDyadicNormalizedStretch_action_finiteFourierReconstruction
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    torusBilinearKernelAction
        (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
          R N)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      ∑ k ∈ s, ∑ l ∈ t,
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          applyCoherentBilinearOperator
            (((((1 : ℝ) / N) : ℂ)) •
              normalizedStretchTensorSymbol explicitBufferedStretchCutoff
                ((1 : ℝ) / N)
                (anisotropicFrequencyPairReciprocalScaling ((1 : ℝ) / N)
                  ((((N : ℝ) ^ 2)⁻¹) •
                    R (euclideanFrequencyPairOfWavevector
                      (pairWavevector k l)))))
            (omega k) (eta l) := by
  rw [torusBilinearKernelAction_finiteFourierReconstruction _
    (integrable_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
      R hN)]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [frequencyPairUnitTorusFourierCoeff_periodizedRotatedSquareDyadicNormalizedStretchTensorKernel
    R hN]

/-! ## Exact coherent interaction in the rotated chart -/

/-- Euclidean source/receiver chart obtained by first expressing a lattice
frequency pair in the frozen frame and then applying the square-dyadic
normalization. -/
def frozenFrameSquareDyadicEuclideanFrequencyPair
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) (k l : Wavevector) : EuclideanFrequencyPair :=
  anisotropicFrequencyPairReciprocalScaling ((1 : ℝ) / N)
    ((((N : ℝ) ^ 2)⁻¹) •
      R (euclideanFrequencyPairOfWavevector (pairWavevector k l)))

/-- Algebraic source/receiver coordinates of the rotated square-dyadic
chart. -/
def frozenFrameSquareDyadicFrequencyPairChart
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    (N : ℕ) (k l : Wavevector) : FrequencyPair :=
  euclideanToFrequencyPairEquiv
    (frozenFrameSquareDyadicEuclideanFrequencyPair R N k l)

/-- The exact finite-field formula written as the retained coherent
Biot--Savart stretching interaction in the frozen square-dyadic chart. -/
theorem unitTorusPeriodizedRotatedSquareDyadicNormalizedStretch_action_finiteFourierReconstruction_eq_coherent
    (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    torusBilinearKernelAction
        (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
          R N)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      ∑ k ∈ s, ∑ l ∈ t,
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          (((((1 : ℝ) / N) : ℂ)) •
            localizedCoherentProjectedNormalizedStretch
              explicitBufferedStretchCutoff ((1 : ℝ) / N)
              (frozenFrameSquareDyadicFrequencyPairChart R N k l)
              (omega k) (eta l)) := by
  rw [unitTorusPeriodizedRotatedSquareDyadicNormalizedStretch_action_finiteFourierReconstruction
    R hN]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  have hident :=
    apply_localizedStretchTensorSymbol_eq_delta_localizedCoherentProjection
      ((1 : ℝ) / N)
      (frozenFrameSquareDyadicEuclideanFrequencyPair R N k l)
      (omega k) (eta l)
  unfold localizedStretchTensorSymbol at hident
  push_cast at hident
  simpa [frozenFrameSquareDyadicEuclideanFrequencyPair,
    frozenFrameSquareDyadicFrequencyPairChart] using hident

/-- Real-valued frozen-frame torus mass estimate. -/
theorem exists_uniform_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel_integral_norm :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
        (N : ℕ), 2 ≤ N →
        Integrable
          (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
            R N) frequencyPairUnitTorusMeasure ∧
        (∫ q : FrequencyPairUnitTorus,
          ‖unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
            R N q‖ ∂frequencyPairUnitTorusMeasure) ≤ C / N := by
  rcases
      exists_uniform_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro R N hN
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hKint :=
    integrable_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
      R hN
  refine ⟨hKint, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (div_nonneg hC hNR.le)).mp
  rw [ofReal_integral_norm_eq_lintegral_enorm hKint]
  exact hmass R N hN

/-- **Uniform frozen-frame finite-field endpoint estimate.**  The `C/N`
constant is independent of the orthogonal frame and both Fourier support
cardinalities. -/
theorem exists_uniform_frozenFrameFiniteFourierSquareDyadicStretch_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : EuclideanFrequencyPair ≃ₗᵢ[ℝ] EuclideanFrequencyPair)
        (N : ℕ), 2 ≤ N →
      ∀ (s t : Finset Wavevector) (omega eta : FourierVelocity)
        (x : BilinearSpatialTorus) (M P : ℝ),
        (∀ y, ‖finiteFourierReconstruction s omega y‖ ≤ M) →
        (∀ y, ‖finiteFourierReconstruction t eta y‖ ≤ P) →
        ‖torusBilinearKernelAction
            (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
              R N)
            (finiteFourierReconstruction s omega)
            (finiteFourierReconstruction t eta) x‖ ≤
          9 * (C / N) * M * P := by
  rcases
      exists_uniform_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel_integral_norm with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro R N hN s t omega eta x M P homega heta
  rcases hmass R N hN with ⟨hKint, hKmass⟩
  calc
    ‖torusBilinearKernelAction
        (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel R N)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x‖ ≤
        9 * (∫ q : FrequencyPairUnitTorus,
          ‖unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
            R N q‖ ∂frequencyPairUnitTorusMeasure) * M * P := by
      exact norm_torusBilinearKernelAction_le _ _ _ x M P hKint
        (measurable_unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
          R N)
        (continuous_finiteFourierReconstruction s omega)
        (continuous_finiteFourierReconstruction t eta) homega heta
    _ ≤ 9 * (C / N) * M * P := by
      have hM : 0 ≤ M :=
        (norm_nonneg (finiteFourierReconstruction s omega x)).trans (homega x)
      have hP : 0 ≤ P :=
        (norm_nonneg (finiteFourierReconstruction t eta x)).trans (heta x)
      gcongr

/-! ## Specialization to the physical oriented-frame interface -/

/-- Exact coherent finite-field identity for an algebraic oriented frame,
transported through its canonical Euclidean isometry. -/
theorem unitTorusPeriodizedOrientedFrameSquareDyadicNormalizedStretch_action_finiteFourierReconstruction_eq_coherent
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    torusBilinearKernelAction
        (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
          (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      ∑ k ∈ s, ∑ l ∈ t,
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          (((((1 : ℝ) / N) : ℂ)) •
            localizedCoherentProjectedNormalizedStretch
              explicitBufferedStretchCutoff ((1 : ℝ) / N)
              (frozenFrameSquareDyadicFrequencyPairChart
                (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l)
              (omega k) (eta l)) :=
  unitTorusPeriodizedRotatedSquareDyadicNormalizedStretch_action_finiteFourierReconstruction_eq_coherent
    (orientedFrameFrequencyPairLinearIsometryEquiv F) hN s t omega eta x

/-- The cardinality-free `C/N` endpoint is uniform over the manuscript's
algebraic oriented frames, not merely over an unrelated analytic rotation
parameter. -/
theorem exists_uniform_orientedFrameFiniteFourierSquareDyadicStretch_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ), 2 ≤ N →
      ∀ (s t : Finset Wavevector) (omega eta : FourierVelocity)
        (x : BilinearSpatialTorus) (M P : ℝ),
        (∀ y, ‖finiteFourierReconstruction s omega y‖ ≤ M) →
        (∀ y, ‖finiteFourierReconstruction t eta y‖ ≤ P) →
        ‖torusBilinearKernelAction
            (unitTorusPeriodizedRotatedSquareDyadicNormalizedStretchTensorKernel
              (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
            (finiteFourierReconstruction s omega)
            (finiteFourierReconstruction t eta) x‖ ≤
          9 * (C / N) * M * P := by
  rcases
      exists_uniform_frozenFrameFiniteFourierSquareDyadicStretch_bilinear_bound with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro F N hN s t omega eta x M P homega heta
  exact hbound (orientedFrameFrequencyPairLinearIsometryEquiv F) N hN
    s t omega eta x M P homega heta

end PancakeFrozenFrameKernelTransfer
end NavierStokes
end FluidDynamics
end Mettapedia
