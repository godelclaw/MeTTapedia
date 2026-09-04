import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteFourierBilinearTransfer
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dyadic scaling of the coherent six-dimensional kernel

Littlewood--Paley blocks do not use the base-scale symbol directly.  Their
Fourier variables must first be divided by the dyadic frequency.  This module
begins that scale transfer by proving the exact dimension-six isotropic
rescaling laws for a tensor-valued Euclidean kernel: its `L¹` mass is
unchanged and its Fourier transform is evaluated at the inversely rescaled
frequency.

The pancake chart additionally has four transverse coordinates scaled by the
aperture.  That anisotropic step is kept separate so the dyadic and aperture
Jacobians cannot be conflated.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeDyadicKernelScaling

open MeasureTheory
open PancakeBilinearKernelScaling
open PancakeBilinearPeriodization
open PancakeSmoothCoherentStretchSymbol
open PancakeCoherentStretchFactorization
open PancakeRealCoherentPairEstimate
open PeriodicFourierTriad
open scoped FourierTransform

/-- Dimension-six spatial rescaling of a Euclidean tensor kernel. -/
def isotropicFrequencyPairKernelRescaling
    (r : ℝ) (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  (((r ^ 6 : ℝ) : ℂ) • K (r • x))

/-- Positive isotropic rescaling leaves the Euclidean `L¹` kernel mass
unchanged. -/
theorem integral_norm_isotropicFrequencyPairKernelRescaling
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    {r : ℝ} (hr : 0 < r) :
    (∫ x, ‖isotropicFrequencyPairKernelRescaling r K x‖) =
      ∫ x, ‖K x‖ := by
  unfold isotropicFrequencyPairKernelRescaling
  simp_rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos hr 6)]
  rw [integral_const_mul,
    Measure.integral_comp_smul
      (volume : Measure EuclideanFrequencyPair) (fun x ↦ ‖K x‖) r]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  have hr6 : r ^ 6 ≠ 0 := pow_ne_zero 6 hr.ne'
  rw [abs_of_pos (inv_pos.mpr (pow_pos hr 6))]
  field_simp

/-- Rescaling an integrable Euclidean tensor kernel by a positive factor
preserves integrability. -/
theorem integrable_isotropicFrequencyPairKernelRescaling
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (hK : Integrable K) {r : ℝ} (hr : 0 < r) :
    Integrable (isotropicFrequencyPairKernelRescaling r K) := by
  have hcomp : Integrable (fun x : EuclideanFrequencyPair ↦ K (r • x)) :=
    hK.comp_smul hr.ne'
  change Integrable
    ((fun _ : EuclideanFrequencyPair ↦ (((r ^ 6 : ℝ) : ℂ))) •
      fun x : EuclideanFrequencyPair ↦ K (r • x))
  apply hcomp.bdd_smul ‖(((r ^ 6 : ℝ) : ℂ))‖ aestronglyMeasurable_const
  exact Filter.Eventually.of_forall fun _ ↦ le_rfl

/-- The Fourier transform of the dimension-six rescaled kernel is the
original transform evaluated at the inversely rescaled frequency. -/
theorem fourier_isotropicFrequencyPairKernelRescaling
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    {r : ℝ} (hr : 0 < r) (xi : EuclideanFrequencyPair) :
    FourierTransform.fourier
        (isotropicFrequencyPairKernelRescaling r K) xi =
      FourierTransform.fourier K (r⁻¹ • xi) := by
  let F : EuclideanFrequencyPair → CoherentBilinearOperator := fun y ↦
    𝐞 (-(inner ℝ y (r⁻¹ • xi))) • K y
  have hchar (x : EuclideanFrequencyPair) :
      𝐞 (-(inner ℝ (r • x) (r⁻¹ • xi))) =
        𝐞 (-(inner ℝ x xi)) := by
    congr 1
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  rw [Real.fourier_eq, Real.fourier_eq]
  change
    (∫ x : EuclideanFrequencyPair,
      𝐞 (-(inner ℝ x xi)) •
        (((r ^ 6 : ℝ) : ℂ) • K (r • x))) = ∫ y, F y
  calc
    (∫ x : EuclideanFrequencyPair,
        𝐞 (-(inner ℝ x xi)) •
          (((r ^ 6 : ℝ) : ℂ) • K (r • x))) =
        (((r ^ 6 : ℝ) : ℂ) •
          ∫ x : EuclideanFrequencyPair, F (r • x)) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with x
      unfold F
      rw [hchar]
      exact smul_comm _ _ _
    _ = (((r ^ 6 : ℝ) : ℂ) •
          ((r ^ 6)⁻¹ • ∫ y : EuclideanFrequencyPair, F y)) := by
      congr 1
      simpa only [finrank_euclideanSpace, Fintype.card_fin] using
        (Measure.integral_comp_smul_of_nonneg
          (volume : Measure EuclideanFrequencyPair) F r (hR := hr.le))
    _ = ∫ y : EuclideanFrequencyPair, F y := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rw [smul_smul]
      norm_num [hr.ne']

/-! ## Periodization after dyadic rescaling -/

/-- Periodization of an isotropically rescaled six-dimensional kernel. -/
def periodizedIsotropicFrequencyPairKernel
    (r : ℝ) (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  addPeriodization (G := StandardFrequencyPairLattice)
    (isotropicFrequencyPairKernelRescaling r K) x

/-- The periodized rescaled kernel is measurable when the cover kernel is
continuous. -/
theorem measurable_periodizedIsotropicFrequencyPairKernel
    (r : ℝ) (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (hK : Continuous K) :
    Measurable (periodizedIsotropicFrequencyPairKernel r K) := by
  apply measurable_addPeriodization
  unfold isotropicFrequencyPairKernelRescaling
  have hcomp : Continuous (fun x : EuclideanFrequencyPair ↦ K (r • x)) :=
    hK.comp (continuous_const.smul continuous_id)
  exact (continuous_const.smul hcomp).measurable

/-- Rescaling and then periodizing does not increase `L¹` mass on the
standard fundamental cell. -/
theorem setLIntegral_enorm_periodizedIsotropicFrequencyPairKernel_le
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (hKcont : Continuous K) (hKint : Integrable K)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ x in standardFrequencyPairCell,
        ‖periodizedIsotropicFrequencyPairKernel r K x‖ₑ) ≤
      ∫⁻ x, ‖K x‖ₑ := by
  let Kr := isotropicFrequencyPairKernelRescaling r K
  have hKrcont : Continuous Kr := by
    unfold Kr isotropicFrequencyPairKernelRescaling
    fun_prop
  have hKrint : Integrable Kr :=
    integrable_isotropicFrequencyPairKernelRescaling K hKint hr
  calc
    (∫⁻ x in standardFrequencyPairCell,
        ‖periodizedIsotropicFrequencyPairKernel r K x‖ₑ) ≤
        ∫⁻ x, ‖Kr x‖ₑ := by
      simpa [periodizedIsotropicFrequencyPairKernel, Kr] using
        setLIntegral_enorm_addPeriodization_le
          standardFrequencyPairCell_isAddFundamentalDomain Kr hKrcont.measurable
    _ = ENNReal.ofReal (∫ x, ‖Kr x‖) := by
      rw [ofReal_integral_eq_lintegral_ofReal hKrint.norm]
      · simp only [ofReal_norm]
      · exact ae_of_all _ fun x ↦ norm_nonneg (Kr x)
    _ = ENNReal.ofReal (∫ x, ‖K x‖) := by
      rw [integral_norm_isotropicFrequencyPairKernelRescaling K hr]
    _ = ∫⁻ x, ‖K x‖ₑ := by
      rw [ofReal_integral_eq_lintegral_ofReal hKint.norm]
      · simp only [ofReal_norm]
      · exact ae_of_all _ fun x ↦ norm_nonneg (K x)

/-- The fundamental-cell Fourier coefficient of the periodized rescaled
kernel is the original Fourier transform at the inversely rescaled lattice
frequency. -/
theorem setIntegral_character_periodizedIsotropicFrequencyPairKernel
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (hKcont : Continuous K) (hKint : Integrable K)
    {r : ℝ} (hr : 0 < r) (n : FrequencyPairWavevector) :
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x •
          periodizedIsotropicFrequencyPairKernel r K x) =
      FourierTransform.fourier K
        (r⁻¹ • euclideanFrequencyPairOfWavevector n) := by
  let Kr := isotropicFrequencyPairKernelRescaling r K
  have hKrcont : Continuous Kr := by
    unfold Kr isotropicFrequencyPairKernelRescaling
    fun_prop
  have hKrint : Integrable Kr :=
    integrable_isotropicFrequencyPairKernelRescaling K hKint hr
  have htransfer := setIntegral_character_smul_addPeriodization_eq
    standardFrequencyPairCell_isAddFundamentalDomain Kr hKrcont.measurable
    hKrint (euclideanFrequencyPairCharacter n)
    (continuous_euclideanFrequencyPairCharacter n).measurable
    (norm_euclideanFrequencyPairCharacter n)
    (euclideanFrequencyPairCharacter_vadd n)
  calc
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x •
          periodizedIsotropicFrequencyPairKernel r K x) =
        ∫ x, euclideanFrequencyPairCharacter n x • Kr x := by
      simpa [periodizedIsotropicFrequencyPairKernel, Kr] using htransfer
    _ = FourierTransform.fourier Kr
          (euclideanFrequencyPairOfWavevector n) := by
      rw [Real.fourier_eq]
      rfl
    _ = FourierTransform.fourier K
          (r⁻¹ • euclideanFrequencyPairOfWavevector n) :=
      fourier_isotropicFrequencyPairKernelRescaling K hr _

/-- The normalized coherent-stretching kernel after isotropic dyadic
rescaling and lattice periodization. -/
def periodizedIsotropicNormalizedStretchTensorKernel
    (r delta : ℝ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  periodizedIsotropicFrequencyPairKernel r
    (normalizedStretchTensorKernel explicitBufferedStretchCutoff delta) x

/-- **Exact dyadic-scale cover coefficient.**  Periodization after isotropic
rescaling samples the normalized coherent symbol at the lattice frequency
divided by the dyadic scale. -/
theorem setIntegral_character_periodizedIsotropicNormalizedStretchTensorKernel
    {r : ℝ} (hr : 0 < r) (delta : ℝ) (n : FrequencyPairWavevector) :
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x •
          periodizedIsotropicNormalizedStretchTensorKernel r delta x) =
      normalizedStretchTensorSymbol explicitBufferedStretchCutoff delta
        (r⁻¹ • euclideanFrequencyPairOfWavevector n) := by
  unfold periodizedIsotropicNormalizedStretchTensorKernel
  rw [setIntegral_character_periodizedIsotropicFrequencyPairKernel
      (normalizedStretchTensorKernel explicitBufferedStretchCutoff delta)
      (normalizedStretchTensorKernel_continuous
        explicitBufferedStretchCutoff delta)
      (normalizedStretchTensorKernel_integrable
        explicitBufferedStretchCutoff delta) hr]
  change FourierTransform.fourier
      ((normalizedStretchTensorKernel explicitBufferedStretchCutoff delta :
        SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator) :
          EuclideanFrequencyPair → CoherentBilinearOperator)
      (r⁻¹ • euclideanFrequencyPairOfWavevector n) = _
  rw [← SchwartzMap.fourier_coe]
  exact congrArg
    (fun f : SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator ↦
      f (r⁻¹ • euclideanFrequencyPairOfWavevector n))
    (fourier_normalizedStretchTensorKernel explicitBufferedStretchCutoff delta)

/-! ## The square-dyadic pancake chart -/

/-- A lattice wavevector regarded as an algebraic real three-vector. -/
def realWavevector (k : Wavevector) : RealVec3 :=
  ((k 0 : ℝ), (k 1 : ℝ), (k 2 : ℝ))

/-- Normalized chart coordinates for a square-dyadic pancake block.  The two
transverse coordinates are divided by `N`, while the axial coordinate is
divided by `N²`. -/
def squareDyadicNormalizedWavevector (N : ℕ) (k : Wavevector) : RealVec3 :=
  ((k 0 : ℝ) / N, (k 1 : ℝ) / N, (k 2 : ℝ) / (N ^ 2))

/-- At aperture `1/N`, the square-dyadic chart reconstructs the physical
wavevector normalized by the shell frequency `N²`. -/
theorem scaledPancakeFrequency_squareDyadicNormalizedWavevector
    {N : ℕ} (hN : 0 < N) (k : Wavevector) :
    scaledPancakeFrequency ((1 : ℝ) / N)
        (squareDyadicNormalizedWavevector N k).1
        (squareDyadicNormalizedWavevector N k).2.1
        (squareDyadicNormalizedWavevector N k).2.2 =
      smul ((1 : ℝ) / (N ^ 2)) (realWavevector k) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [scaledPancakeFrequency, squareDyadicNormalizedWavevector,
      realWavevector, smul] <;>
    field_simp

/-- Source/receiver chart coordinates for a pair of square-dyadic lattice
wavevectors. -/
def squareDyadicFrequencyPairChart
    (N : ℕ) (k l : Wavevector) : FrequencyPair :=
  (squareDyadicNormalizedWavevector N k,
    squareDyadicNormalizedWavevector N l)

/-- The same square-dyadic chart in the Euclidean six-space used by Fourier
transformation. -/
def squareDyadicEuclideanFrequencyPair
    (N : ℕ) (k l : Wavevector) : EuclideanFrequencyPair :=
  euclideanToFrequencyPairEquiv.symm
    (squareDyadicFrequencyPairChart N k l)

@[simp]
theorem euclideanToFrequencyPairEquiv_squareDyadicEuclideanFrequencyPair
    (N : ℕ) (k l : Wavevector) :
    euclideanToFrequencyPairEquiv
        (squareDyadicEuclideanFrequencyPair N k l) =
      squareDyadicFrequencyPairChart N k l := by
  simp [squareDyadicEuclideanFrequencyPair]

/-- Both chart frequencies reconstruct the corresponding physical lattice
frequencies at the square-dyadic shell scale. -/
theorem source_receiver_squareDyadicFrequencyPairChart
    {N : ℕ} (hN : 0 < N) (k l : Wavevector) :
    sourceFrequency ((1 : ℝ) / N)
        (squareDyadicFrequencyPairChart N k l) =
        smul ((1 : ℝ) / (N ^ 2)) (realWavevector k) ∧
      receiverFrequency ((1 : ℝ) / N)
        (squareDyadicFrequencyPairChart N k l) =
        smul ((1 : ℝ) / (N ^ 2)) (realWavevector l) := by
  constructor
  · simpa [sourceFrequency, squareDyadicFrequencyPairChart] using
      scaledPancakeFrequency_squareDyadicNormalizedWavevector hN k
  · simpa [receiverFrequency, squareDyadicFrequencyPairChart] using
      scaledPancakeFrequency_squareDyadicNormalizedWavevector hN l

end PancakeDyadicKernelScaling
end NavierStokes
end FluidDynamics
end Mettapedia
