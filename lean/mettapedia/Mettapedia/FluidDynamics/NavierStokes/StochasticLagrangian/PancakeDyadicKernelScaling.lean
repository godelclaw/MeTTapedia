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
open PancakeUniformKernelFamily
open PeriodicFourierTriad
open Set
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

/-! ## Regrouping into four transverse and two axial coordinates -/

/-- Coordinate permutation sending the original source/receiver order
`(a,b,c,d,e,f)` to the transverse/axial order `(a,b,d,e,c,f)`. -/
def transverseAxialCoordinateEquiv : Fin 6 ≃ Fin 6 :=
  { toFun := fun i : Fin 6 ↦ ![(0 : Fin 6), 1, 4, 2, 3, 5] i
    invFun := fun i : Fin 6 ↦ ![(0 : Fin 6), 1, 3, 4, 2, 5] i
    left_inv := by
      intro i
      fin_cases i <;> rfl
    right_inv := by
      intro i
      fin_cases i <;> rfl }

/-- Linear coordinate regrouping from Euclidean source/receiver order to the
product of four transverse and two axial kernel coordinates. -/
def frequencyPairToBilinearKernelCoordinates :
    EuclideanFrequencyPair ≃L[ℝ] BilinearKernelSpace :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      transverseAxialCoordinateEquiv).toContinuousLinearEquiv.trans
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 4) (m := 2))

/-- The coordinate regrouping has the intended explicit component order. -/
theorem frequencyPairToBilinearKernelCoordinates_apply
    (x : EuclideanFrequencyPair) :
    frequencyPairToBilinearKernelCoordinates x =
      (!₂[x 0, x 1, x 3, x 4], !₂[x 2, x 5]) := by
  ext i <;> fin_cases i <;>
    simp [frequencyPairToBilinearKernelCoordinates,
      transverseAxialCoordinateEquiv, EuclideanSpace.finAddEquivProd,
      EuclideanSpace.sumEquivProd, PiLp.sumPiLpEquivProdLpPiLp]
  all_goals
    apply congrArg (fun j : Fin 6 ↦ x j)
    rfl

/-- Product coordinates of a concatenated pair of lattice wavevectors. -/
theorem frequencyPairToBilinearKernelCoordinates_pairWavevector
    (k l : Wavevector) :
    frequencyPairToBilinearKernelCoordinates
        (euclideanFrequencyPairOfWavevector (pairWavevector k l)) =
      (!₂[(k 0 : ℝ), (k 1 : ℝ), (l 0 : ℝ), (l 1 : ℝ)],
        !₂[(k 2 : ℝ), (l 2 : ℝ)]) := by
  rw [frequencyPairToBilinearKernelCoordinates_apply]
  ext i <;> fin_cases i <;>
    simp [euclideanFrequencyPairOfWavevector, pairWavevector, Fin.append,
      Fin.addCases]

/-- Product coordinates of the square-dyadic normalized frequency pair. -/
theorem frequencyPairToBilinearKernelCoordinates_squareDyadic
    (N : ℕ) (k l : Wavevector) :
    frequencyPairToBilinearKernelCoordinates
        (squareDyadicEuclideanFrequencyPair N k l) =
      (!₂[(k 0 : ℝ) / N, (k 1 : ℝ) / N,
          (l 0 : ℝ) / N, (l 1 : ℝ) / N],
        !₂[(k 2 : ℝ) / (N ^ 2), (l 2 : ℝ) / (N ^ 2)]) := by
  rw [frequencyPairToBilinearKernelCoordinates_apply]
  ext i <;> fin_cases i <;>
    simp [squareDyadicEuclideanFrequencyPair,
      squareDyadicFrequencyPairChart, squareDyadicNormalizedWavevector,
      euclideanToFrequencyPairEquiv, euclideanToFrequencyPairLinearEquiv]

/-- Regrouping the six Euclidean coordinates into the `4 + 2` product chart
preserves Lebesgue measure exactly. -/
theorem frequencyPairToBilinearKernelCoordinates_measurePreserving :
    MeasurePreserving frequencyPairToBilinearKernelCoordinates
      (volume : Measure EuclideanFrequencyPair) bilinearKernelVolume := by
  let P := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    transverseAxialCoordinateEquiv
  let Q := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSumFinEquiv : (Fin 4 ⊕ Fin 2) ≃ Fin (4 + 2)).symm
  let R := PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2
    (fun _ : Fin 4 ⊕ Fin 2 ↦ ℝ)
  have hP := LinearIsometryEquiv.measurePreserving P
  have hQ := LinearIsometryEquiv.measurePreserving Q
  have hR := LinearIsometryEquiv.measurePreserving R
  have hS := WithLp.volume_preserving_ofLp BilinearTransverseSpace
    BilinearAxialSpace
  have hRS := hS.comp hR
  have hQRS := hRS.comp hQ
  have hPQRS := hQRS.comp hP
  convert hPQRS using 1 <;> rfl

/-- The measurable equivalence underlying the coordinate regrouping. -/
def frequencyPairToBilinearKernelMeasurableEquiv :
    EuclideanFrequencyPair ≃ᵐ BilinearKernelSpace :=
  frequencyPairToBilinearKernelCoordinates.toHomeomorph.toMeasurableEquiv

/-- Measure preservation in a form that remembers the measurable inverse. -/
theorem frequencyPairToBilinearKernelMeasurableEquiv_measurePreserving :
    MeasurePreserving frequencyPairToBilinearKernelMeasurableEquiv
      (volume : Measure EuclideanFrequencyPair) bilinearKernelVolume := by
  simpa [frequencyPairToBilinearKernelMeasurableEquiv] using
    frequencyPairToBilinearKernelCoordinates_measurePreserving

/-- The inverse regrouping also preserves volume. -/
theorem frequencyPairToBilinearKernelMeasurableEquiv_symm_measurePreserving :
    MeasurePreserving frequencyPairToBilinearKernelMeasurableEquiv.symm
      bilinearKernelVolume (volume : Measure EuclideanFrequencyPair) :=
  MeasurePreserving.symm frequencyPairToBilinearKernelMeasurableEquiv
    frequencyPairToBilinearKernelMeasurableEquiv_measurePreserving

/-- A Euclidean six-kernel expressed in transverse/axial product
coordinates. -/
def kernelInBilinearCoordinates
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (p : BilinearKernelSpace) : CoherentBilinearOperator :=
  K (frequencyPairToBilinearKernelCoordinates.symm p)

/-- Coordinate regrouping preserves continuity of kernels. -/
theorem continuous_kernelInBilinearCoordinates
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (hK : Continuous K) :
    Continuous (kernelInBilinearCoordinates K) := by
  exact hK.comp frequencyPairToBilinearKernelCoordinates.symm.continuous

/-- Coordinate regrouping preserves kernel integrability. -/
theorem integrable_kernelInBilinearCoordinates_iff
    (K : EuclideanFrequencyPair → CoherentBilinearOperator) :
    Integrable (kernelInBilinearCoordinates K) bilinearKernelVolume ↔
      Integrable K := by
  change Integrable
      (fun p ↦ K (frequencyPairToBilinearKernelCoordinates.symm p))
        bilinearKernelVolume ↔ Integrable K
  exact
    frequencyPairToBilinearKernelMeasurableEquiv_symm_measurePreserving.integrable_comp_emb
      frequencyPairToBilinearKernelMeasurableEquiv.symm.measurableEmbedding

/-- Coordinate regrouping preserves the exact operator-norm mass. -/
theorem integral_norm_kernelInBilinearCoordinates
    (K : EuclideanFrequencyPair → CoherentBilinearOperator) :
    (∫ p, ‖kernelInBilinearCoordinates K p‖ ∂bilinearKernelVolume) =
      ∫ x, ‖K x‖ := by
  simpa [kernelInBilinearCoordinates, frequencyPairToBilinearKernelMeasurableEquiv]
    using
      (frequencyPairToBilinearKernelMeasurableEquiv_symm_measurePreserving.integral_comp'
        (fun x : EuclideanFrequencyPair ↦ ‖K x‖))

/-- The coordinate regrouping splits the Euclidean pairing into its four
transverse and two axial parts. -/
theorem inner_frequencyPairToBilinearKernelCoordinates
    (x xi : EuclideanFrequencyPair) :
    inner ℝ x xi =
      inner ℝ (frequencyPairToBilinearKernelCoordinates x).1
          (frequencyPairToBilinearKernelCoordinates xi).1 +
        inner ℝ (frequencyPairToBilinearKernelCoordinates x).2
          (frequencyPairToBilinearKernelCoordinates xi).2 := by
  rw [frequencyPairToBilinearKernelCoordinates_apply,
    frequencyPairToBilinearKernelCoordinates_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_succ]
  ring

/-- Fourier integral written in the product chart, with the transverse and
axial characters displayed separately. -/
def bilinearKernelFourier
    (K : BilinearKernelSpace → CoherentBilinearOperator)
    (q : BilinearKernelSpace) : CoherentBilinearOperator :=
  ∫ p, 𝐞 (- (inner ℝ p.1 q.1 + inner ℝ p.2 q.2)) • K p
    ∂bilinearKernelVolume

/-- Euclidean Fourier transformation is exactly the product-chart Fourier
integral after coordinate regrouping. -/
theorem fourier_eq_bilinearKernelFourier
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (xi : EuclideanFrequencyPair) :
    FourierTransform.fourier K xi =
      bilinearKernelFourier (kernelInBilinearCoordinates K)
        (frequencyPairToBilinearKernelCoordinates xi) := by
  rw [Real.fourier_eq]
  let q := frequencyPairToBilinearKernelCoordinates xi
  let F : BilinearKernelSpace → CoherentBilinearOperator := fun p ↦
    𝐞 (- (inner ℝ p.1 q.1 + inner ℝ p.2 q.2)) •
      kernelInBilinearCoordinates K p
  calc
    (∫ x : EuclideanFrequencyPair,
        𝐞 (-(inner ℝ x xi)) • K x) =
        ∫ x : EuclideanFrequencyPair,
          F (frequencyPairToBilinearKernelMeasurableEquiv x) := by
      apply integral_congr_ae
      filter_upwards with x
      unfold F q kernelInBilinearCoordinates
      rw [inner_frequencyPairToBilinearKernelCoordinates]
      simp [frequencyPairToBilinearKernelMeasurableEquiv]
    _ = ∫ p : BilinearKernelSpace, F p ∂bilinearKernelVolume :=
      frequencyPairToBilinearKernelMeasurableEquiv_measurePreserving.integral_comp'
        F
    _ = bilinearKernelFourier (kernelInBilinearCoordinates K)
        (frequencyPairToBilinearKernelCoordinates xi) := rfl

/-- Multiplication by the product Fourier character preserves
integrability. -/
theorem integrable_bilinearKernelFourier_integrand
    (K : BilinearKernelSpace → CoherentBilinearOperator)
    (hK : Integrable K bilinearKernelVolume) (q : BilinearKernelSpace) :
    Integrable
      (fun p ↦
        𝐞 (- (inner ℝ p.1 q.1 + inner ℝ p.2 q.2)) • K p)
      bilinearKernelVolume := by
  apply hK.bdd_smul 1
  · exact (show Continuous (fun p : BilinearKernelSpace ↦
        ((𝐞 (- (inner ℝ p.1 q.1 + inner ℝ p.2 q.2)) : ℂ))) by
      fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p ↦ by simp

/-- Fubini form of the product-chart Fourier integral. -/
theorem bilinearKernelFourier_eq_iterated
    (K : BilinearKernelSpace → CoherentBilinearOperator)
    (hK : Integrable K bilinearKernelVolume) (q : BilinearKernelSpace) :
    bilinearKernelFourier K q =
      ∫ y : BilinearTransverseSpace,
        ∫ z : BilinearAxialSpace,
          𝐞 (- (inner ℝ y q.1 + inner ℝ z q.2)) • K (y, z) := by
  unfold bilinearKernelFourier bilinearKernelVolume
  exact integral_prod _ (integrable_bilinearKernelFourier_integrand K hK q)

/-- Moving the transverse dilation from physical variables to reciprocal
variables leaves the product Fourier character unchanged. -/
theorem bilinearFourierCharacter_transverse_smul
    {delta : ℝ} (hdelta : delta ≠ 0)
    (y : BilinearTransverseSpace) (z : BilinearAxialSpace)
    (q : BilinearKernelSpace) :
    𝐞 (- (inner ℝ y q.1 + inner ℝ z q.2)) =
      𝐞 (- (inner ℝ (delta • y) (delta⁻¹ • q.1) +
        inner ℝ z q.2)) := by
  congr 1
  rw [real_inner_smul_left, real_inner_smul_right]
  field_simp

/-- Exact reciprocal-variable law for the four-transverse kernel scaling. -/
theorem bilinearKernelFourier_rescaledBilinearKernel
    (K : BilinearKernelSpace → CoherentBilinearOperator)
    (hK : Integrable K bilinearKernelVolume)
    {delta : ℝ} (hdelta : 0 < delta)
    (hKdelta : Integrable (rescaledBilinearKernel delta K)
      bilinearKernelVolume)
    (q : BilinearKernelSpace) :
    bilinearKernelFourier (rescaledBilinearKernel delta K) q =
      ((delta : ℝ) : ℂ) •
        bilinearKernelFourier K (delta⁻¹ • q.1, q.2) := by
  let q' : BilinearKernelSpace := (delta⁻¹ • q.1, q.2)
  let F : BilinearKernelSpace → CoherentBilinearOperator := fun p ↦
    𝐞 (- (inner ℝ p.1 q'.1 + inner ℝ p.2 q'.2)) • K p
  let G : BilinearTransverseSpace → CoherentBilinearOperator := fun y ↦
    ∫ z : BilinearAxialSpace, F (y, z)
  have hscale :
      (∫ y : BilinearTransverseSpace, G (delta • y)) =
        (delta ^ 4)⁻¹ • ∫ y : BilinearTransverseSpace, G y := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      (Measure.integral_comp_smul_of_nonneg
        (volume : Measure BilinearTransverseSpace) G delta
        (hR := hdelta.le))
  rw [bilinearKernelFourier_eq_iterated _ hKdelta,
    bilinearKernelFourier_eq_iterated _ hK]
  change
    (∫ y : BilinearTransverseSpace,
      ∫ z : BilinearAxialSpace,
        𝐞 (- (inner ℝ y q.1 + inner ℝ z q.2)) •
          rescaledBilinearKernel delta K (y, z)) =
      ((delta : ℝ) : ℂ) •
        ∫ y : BilinearTransverseSpace,
          ∫ z : BilinearAxialSpace, F (y, z)
  calc
    (∫ y : BilinearTransverseSpace,
      ∫ z : BilinearAxialSpace,
        𝐞 (- (inner ℝ y q.1 + inner ℝ z q.2)) •
          rescaledBilinearKernel delta K (y, z)) =
        (((delta ^ 5 : ℝ) : ℂ)) •
          ∫ y : BilinearTransverseSpace, G (delta • y) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with z
      unfold F q' rescaledBilinearKernel
      rw [bilinearFourierCharacter_transverse_smul hdelta.ne' y z q]
      exact smul_comm _ _ _
    _ = (((delta ^ 5 : ℝ) : ℂ)) •
        ((delta ^ 4)⁻¹ •
          ∫ y : BilinearTransverseSpace, G y) := by
      rw [hscale]
    _ = ((delta : ℝ) : ℂ) •
        ∫ y : BilinearTransverseSpace, G y := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      congr 1
      push_cast
      field_simp [hdelta.ne']
      rfl
    _ = ((delta : ℝ) : ℂ) •
        ∫ y : BilinearTransverseSpace,
          ∫ z : BilinearAxialSpace, F (y, z) := rfl

/-- Reciprocal-variable chart map: divide the four transverse frequencies
by the aperture and leave the two axial frequencies unchanged. -/
def anisotropicFrequencyPairReciprocalScaling
    (delta : ℝ) (xi : EuclideanFrequencyPair) : EuclideanFrequencyPair :=
  frequencyPairToBilinearKernelCoordinates.symm
    (delta⁻¹ • (frequencyPairToBilinearKernelCoordinates xi).1,
      (frequencyPairToBilinearKernelCoordinates xi).2)

@[simp]
theorem frequencyPairToBilinearKernelCoordinates_reciprocalScaling
    (delta : ℝ) (xi : EuclideanFrequencyPair) :
    frequencyPairToBilinearKernelCoordinates
        (anisotropicFrequencyPairReciprocalScaling delta xi) =
      (delta⁻¹ • (frequencyPairToBilinearKernelCoordinates xi).1,
        (frequencyPairToBilinearKernelCoordinates xi).2) := by
  simp [anisotropicFrequencyPairReciprocalScaling]

/-- At aperture `1/N` and shell scale `N²`, reciprocal anisotropic scaling
is exactly the square-dyadic chart `(k₁/N,k₂/N,k₃/N²)` for both
bilinear input frequencies. -/
theorem anisotropicFrequencyPairReciprocalScaling_squareDyadic
    {N : ℕ} (hN : 0 < N) (k l : Wavevector) :
    anisotropicFrequencyPairReciprocalScaling ((1 : ℝ) / N)
        ((((N : ℝ) ^ 2)⁻¹) •
          euclideanFrequencyPairOfWavevector (pairWavevector k l)) =
      squareDyadicEuclideanFrequencyPair N k l := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  apply frequencyPairToBilinearKernelCoordinates.injective
  rw [frequencyPairToBilinearKernelCoordinates_reciprocalScaling,
    map_smul,
    frequencyPairToBilinearKernelCoordinates_pairWavevector,
    frequencyPairToBilinearKernelCoordinates_squareDyadic]
  ext i <;> fin_cases i <;> simp
  all_goals
    field_simp [hNR]

/-! ## Four-transverse/two-axial aperture scaling -/

/-- The physical six-dimensional kernel obtained by scaling exactly the four
transverse coordinates and retaining the one symbol-level aperture factor. -/
def anisotropicFrequencyPairKernelRescaling
    (delta : ℝ) (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  rescaledBilinearKernel delta (kernelInBilinearCoordinates K)
    (frequencyPairToBilinearKernelCoordinates x)

/-- In product coordinates, Euclidean anisotropic rescaling is definitionally
the four-transverse rescaling used by the Fubini calculation. -/
theorem kernelInBilinearCoordinates_anisotropicFrequencyPairKernelRescaling
    (delta : ℝ) (K : EuclideanFrequencyPair → CoherentBilinearOperator) :
    kernelInBilinearCoordinates
        (anisotropicFrequencyPairKernelRescaling delta K) =
      rescaledBilinearKernel delta (kernelInBilinearCoordinates K) := by
  funext p
  simp [kernelInBilinearCoordinates,
    anisotropicFrequencyPairKernelRescaling]

/-- Fourier transform of the physical four-transverse rescaling. -/
theorem fourier_anisotropicFrequencyPairKernelRescaling
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (hK : Integrable K)
    {delta : ℝ} (hdelta : 0 < delta)
    (hKdelta : Integrable
      (rescaledBilinearKernel delta (kernelInBilinearCoordinates K))
      bilinearKernelVolume)
    (xi : EuclideanFrequencyPair) :
    FourierTransform.fourier
        (anisotropicFrequencyPairKernelRescaling delta K) xi =
      ((delta : ℝ) : ℂ) • FourierTransform.fourier K
        (anisotropicFrequencyPairReciprocalScaling delta xi) := by
  have hKprod : Integrable (kernelInBilinearCoordinates K)
      bilinearKernelVolume :=
    (integrable_kernelInBilinearCoordinates_iff K).2 hK
  calc
    FourierTransform.fourier
        (anisotropicFrequencyPairKernelRescaling delta K) xi =
        bilinearKernelFourier
          (rescaledBilinearKernel delta (kernelInBilinearCoordinates K))
          (frequencyPairToBilinearKernelCoordinates xi) := by
      rw [fourier_eq_bilinearKernelFourier,
        kernelInBilinearCoordinates_anisotropicFrequencyPairKernelRescaling]
    _ = ((delta : ℝ) : ℂ) •
        bilinearKernelFourier (kernelInBilinearCoordinates K)
          (delta⁻¹ • (frequencyPairToBilinearKernelCoordinates xi).1,
            (frequencyPairToBilinearKernelCoordinates xi).2) :=
      bilinearKernelFourier_rescaledBilinearKernel
        (kernelInBilinearCoordinates K) hKprod hdelta hKdelta _
    _ = ((delta : ℝ) : ℂ) • FourierTransform.fourier K
        (anisotropicFrequencyPairReciprocalScaling delta xi) := by
      rw [fourier_eq_bilinearKernelFourier]
      simp

/-- The Euclidean anisotropic rescaling is continuous when the base kernel
is continuous. -/
theorem continuous_anisotropicFrequencyPairKernelRescaling
    (delta : ℝ) (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (hK : Continuous K) :
    Continuous (anisotropicFrequencyPairKernelRescaling delta K) := by
  unfold anisotropicFrequencyPairKernelRescaling rescaledBilinearKernel
  exact continuous_const.smul
    ((continuous_kernelInBilinearCoordinates K hK).comp (by fun_prop))

/-- Integrability of the Euclidean anisotropic kernel is equivalent to
integrability of its product-coordinate representative. -/
theorem integrable_anisotropicFrequencyPairKernelRescaling_iff
    (delta : ℝ) (K : EuclideanFrequencyPair → CoherentBilinearOperator) :
    Integrable (anisotropicFrequencyPairKernelRescaling delta K) ↔
      Integrable
        (rescaledBilinearKernel delta (kernelInBilinearCoordinates K))
        bilinearKernelVolume := by
  rw [← integrable_kernelInBilinearCoordinates_iff]
  simp only [
    kernelInBilinearCoordinates_anisotropicFrequencyPairKernelRescaling]

/-- Exact Euclidean `L¹` aperture law.  Four Jacobian powers cancel four of
the five kernel powers, leaving precisely one factor of `delta`. -/
theorem integral_norm_anisotropicFrequencyPairKernelRescaling
    (K : EuclideanFrequencyPair → CoherentBilinearOperator)
    (hK : Integrable K)
    {delta : ℝ} (hdelta : 0 < delta)
    (hKdelta : Integrable
      (rescaledBilinearKernel delta (kernelInBilinearCoordinates K))
      bilinearKernelVolume) :
    (∫ x, ‖anisotropicFrequencyPairKernelRescaling delta K x‖) =
      delta * ∫ x, ‖K x‖ := by
  have hKprod : Integrable (kernelInBilinearCoordinates K)
      bilinearKernelVolume :=
    (integrable_kernelInBilinearCoordinates_iff K).2 hK
  calc
    (∫ x, ‖anisotropicFrequencyPairKernelRescaling delta K x‖) =
        ∫ p, ‖kernelInBilinearCoordinates
          (anisotropicFrequencyPairKernelRescaling delta K) p‖
            ∂bilinearKernelVolume :=
      (integral_norm_kernelInBilinearCoordinates
        (anisotropicFrequencyPairKernelRescaling delta K)).symm
    _ = iteratedBilinearKernelL1
        (rescaledBilinearKernel delta (kernelInBilinearCoordinates K)) := by
      rw [kernelInBilinearCoordinates_anisotropicFrequencyPairKernelRescaling]
      exact integral_norm_eq_iteratedBilinearKernelL1 _ hKdelta
    _ = delta * iteratedBilinearKernelL1
        (kernelInBilinearCoordinates K) :=
      iteratedBilinearKernelL1_rescaled _ hdelta
    _ = delta * ∫ p, ‖kernelInBilinearCoordinates K p‖
          ∂bilinearKernelVolume := by
      rw [integral_norm_eq_iteratedBilinearKernelL1 _ hKprod]
    _ = delta * ∫ x, ‖K x‖ := by
      rw [integral_norm_kernelInBilinearCoordinates]

/-- The four-transverse dilation transported back to Euclidean six-space. -/
def anisotropicFrequencyPairDilationContinuousLinearEquiv
    (delta : ℝ) (hdelta : delta ≠ 0) :
    EuclideanFrequencyPair ≃L[ℝ] EuclideanFrequencyPair :=
  frequencyPairToBilinearKernelCoordinates.trans
    ((bilinearTransverseDilationContinuousLinearEquiv delta hdelta).trans
      frequencyPairToBilinearKernelCoordinates.symm)

@[simp]
theorem anisotropicFrequencyPairDilationContinuousLinearEquiv_apply
    (delta : ℝ) (hdelta : delta ≠ 0) (x : EuclideanFrequencyPair) :
    anisotropicFrequencyPairDilationContinuousLinearEquiv delta hdelta x =
      frequencyPairToBilinearKernelCoordinates.symm
        (delta • (frequencyPairToBilinearKernelCoordinates x).1,
          (frequencyPairToBilinearKernelCoordinates x).2) := rfl

/-- Four-transverse rescaling preserves Schwartz class. -/
def anisotropicSchwartzFrequencyPairKernelRescaling
    (delta : ℝ) (hdelta : delta ≠ 0)
    (K : SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator) :
    SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator :=
  (((delta ^ 5 : ℝ) : ℂ)) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (anisotropicFrequencyPairDilationContinuousLinearEquiv delta hdelta) K

@[simp]
theorem anisotropicSchwartzFrequencyPairKernelRescaling_apply
    (delta : ℝ) (hdelta : delta ≠ 0)
    (K : SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator)
    (x : EuclideanFrequencyPair) :
    anisotropicSchwartzFrequencyPairKernelRescaling delta hdelta K x =
      anisotropicFrequencyPairKernelRescaling delta K x := by
  rfl

/-- A four-transverse rescaling of a Schwartz six-kernel is integrable. -/
theorem anisotropicFrequencyPairKernelRescaling_integrable
    (delta : ℝ) (hdelta : delta ≠ 0)
    (K : SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator) :
    Integrable (anisotropicFrequencyPairKernelRescaling delta K) := by
  refine
    (anisotropicSchwartzFrequencyPairKernelRescaling delta hdelta K).integrable.congr ?_
  filter_upwards with x
  exact anisotropicSchwartzFrequencyPairKernelRescaling_apply delta hdelta K x

/-- The corresponding product-coordinate representative is integrable. -/
theorem rescaledBilinearKernel_kernelInBilinearCoordinates_integrable
    (delta : ℝ) (hdelta : delta ≠ 0)
    (K : SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator) :
    Integrable (rescaledBilinearKernel delta (kernelInBilinearCoordinates K))
      bilinearKernelVolume :=
  (integrable_anisotropicFrequencyPairKernelRescaling_iff delta K).1
    (anisotropicFrequencyPairKernelRescaling_integrable delta hdelta K)

/-- Exact aperture mass law specialized to Schwartz kernels. -/
theorem integral_norm_anisotropicSchwartzFrequencyPairKernelRescaling
    (K : SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator)
    {delta : ℝ} (hdelta : 0 < delta) :
    (∫ x, ‖anisotropicFrequencyPairKernelRescaling delta K x‖) =
      delta * ∫ x, ‖K x‖ :=
  integral_norm_anisotropicFrequencyPairKernelRescaling K K.integrable hdelta
    (rescaledBilinearKernel_kernelInBilinearCoordinates_integrable
      delta hdelta.ne' K)

/-- The coherent-stretching kernel in physical pancake coordinates: four
transverse variables are aperture-rescaled, while the two axial variables
remain at unit chart scale. -/
def anisotropicNormalizedStretchTensorKernel
    (delta : ℝ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  anisotropicFrequencyPairKernelRescaling delta
    (normalizedStretchTensorKernel explicitBufferedStretchCutoff delta) x

/-- The physical pancake kernel is continuous. -/
theorem anisotropicNormalizedStretchTensorKernel_continuous
    (delta : ℝ) :
    Continuous (anisotropicNormalizedStretchTensorKernel delta) :=
  continuous_anisotropicFrequencyPairKernelRescaling delta _
    (normalizedStretchTensorKernel_continuous
      explicitBufferedStretchCutoff delta)

/-- At positive aperture, the physical pancake kernel is integrable. -/
theorem anisotropicNormalizedStretchTensorKernel_integrable
    {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (anisotropicNormalizedStretchTensorKernel delta) :=
  anisotropicFrequencyPairKernelRescaling_integrable delta hdelta.ne'
    (normalizedStretchTensorKernel explicitBufferedStretchCutoff delta)

/-- Exact Fourier multiplier of the anisotropically rescaled coherent
kernel: one aperture factor remains, and the four transverse reciprocal
coordinates are divided by the aperture. -/
theorem fourier_anisotropicNormalizedStretchTensorKernel
    {delta : ℝ} (hdelta : 0 < delta) (xi : EuclideanFrequencyPair) :
    FourierTransform.fourier
        (anisotropicNormalizedStretchTensorKernel delta) xi =
      ((delta : ℝ) : ℂ) •
        normalizedStretchTensorSymbol explicitBufferedStretchCutoff delta
          (anisotropicFrequencyPairReciprocalScaling delta xi) := by
  unfold anisotropicNormalizedStretchTensorKernel
  rw [fourier_anisotropicFrequencyPairKernelRescaling
    (normalizedStretchTensorKernel explicitBufferedStretchCutoff delta)
    (normalizedStretchTensorKernel_integrable
      explicitBufferedStretchCutoff delta) hdelta
    (rescaledBilinearKernel_kernelInBilinearCoordinates_integrable
      delta hdelta.ne'
      (normalizedStretchTensorKernel explicitBufferedStretchCutoff delta))]
  congr 1
  change FourierTransform.fourier
      ((normalizedStretchTensorKernel explicitBufferedStretchCutoff delta :
        SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator) :
          EuclideanFrequencyPair → CoherentBilinearOperator)
      (anisotropicFrequencyPairReciprocalScaling delta xi) = _
  rw [← SchwartzMap.fourier_coe]
  exact congrArg
    (fun f : SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator ↦
      f (anisotropicFrequencyPairReciprocalScaling delta xi))
    (fourier_normalizedStretchTensorKernel explicitBufferedStretchCutoff delta)

/-- Exact `L¹` gain for the constructed physical coherent-stretching
kernel. -/
theorem integral_norm_anisotropicNormalizedStretchTensorKernel
    {delta : ℝ} (hdelta : 0 < delta) :
    (∫ x, ‖anisotropicNormalizedStretchTensorKernel delta x‖) =
      delta * ∫ x, ‖normalizedStretchTensorKernel
        explicitBufferedStretchCutoff delta x‖ :=
  integral_norm_anisotropicSchwartzFrequencyPairKernelRescaling
    (normalizedStretchTensorKernel explicitBufferedStretchCutoff delta) hdelta

/-- Uniform endpoint gain for the actual anisotropically rescaled kernel. -/
theorem exists_uniform_anisotropicNormalizedStretchTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta ∈ Ioc (0 : ℝ) (1 / 2),
      (∫ x, ‖anisotropicNormalizedStretchTensorKernel delta x‖) ≤
        delta * C := by
  rcases exists_uniform_normalizedStretchTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta
  rw [integral_norm_anisotropicNormalizedStretchTensorKernel hdelta.1]
  exact mul_le_mul_of_nonneg_left
    (hmass delta ⟨hdelta.1.le, hdelta.2⟩) hdelta.1.le

/-! ## Combined aperture, shell, and lattice transfer -/

/-- First apply the physical pancake aperture scaling, then the isotropic
shell scaling, and finally periodize on the standard six-dimensional
lattice. -/
def periodizedIsotropicAnisotropicNormalizedStretchTensorKernel
    (r delta : ℝ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  periodizedIsotropicFrequencyPairKernel r
    (anisotropicNormalizedStretchTensorKernel delta) x

/-- Exact lattice coefficient after aperture scaling and isotropic shell
scaling. -/
theorem setIntegral_character_periodizedIsotropicAnisotropicNormalizedStretchTensorKernel
    {r : ℝ} (hr : 0 < r) {delta : ℝ} (hdelta : 0 < delta)
    (n : FrequencyPairWavevector) :
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x •
          periodizedIsotropicAnisotropicNormalizedStretchTensorKernel
            r delta x) =
      ((delta : ℝ) : ℂ) •
        normalizedStretchTensorSymbol explicitBufferedStretchCutoff delta
          (anisotropicFrequencyPairReciprocalScaling delta
            (r⁻¹ • euclideanFrequencyPairOfWavevector n)) := by
  unfold periodizedIsotropicAnisotropicNormalizedStretchTensorKernel
  rw [setIntegral_character_periodizedIsotropicFrequencyPairKernel
    (anisotropicNormalizedStretchTensorKernel delta)
    (anisotropicNormalizedStretchTensorKernel_continuous delta)
    (anisotropicNormalizedStretchTensorKernel_integrable hdelta) hr]
  exact fourier_anisotropicNormalizedStretchTensorKernel hdelta _

/-- The fully transferred kernel on a square-dyadic pancake block. -/
def periodizedSquareDyadicNormalizedStretchTensorKernel
    (N : ℕ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  periodizedIsotropicAnisotropicNormalizedStretchTensorKernel
    ((N : ℝ) ^ 2) ((1 : ℝ) / N) x

/-- **Exact square-dyadic coefficient theorem.**  At shell frequency `N²`
and aperture `1/N`, the periodized kernel coefficient is the coherent
stretching symbol evaluated at the source/receiver chart
`(k₁/N,k₂/N,k₃/N²)`, with the genuine prefactor `1/N`. -/
theorem setIntegral_character_periodizedSquareDyadicNormalizedStretchTensorKernel
    {N : ℕ} (hN : 0 < N) (k l : Wavevector) :
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter (pairWavevector k l) x •
          periodizedSquareDyadicNormalizedStretchTensorKernel N x) =
      ((((1 : ℝ) / N) : ℂ)) •
        normalizedStretchTensorSymbol explicitBufferedStretchCutoff
          ((1 : ℝ) / N) (squareDyadicEuclideanFrequencyPair N k l) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold periodizedSquareDyadicNormalizedStretchTensorKernel
  rw [setIntegral_character_periodizedIsotropicAnisotropicNormalizedStretchTensorKernel
      (pow_pos hNR 2) (one_div_pos.mpr hNR),
    anisotropicFrequencyPairReciprocalScaling_squareDyadic hN]
  push_cast
  congr 1

/-- Periodization and isotropic shell scaling do not lose the exact
anisotropic `L¹` gain. -/
theorem setLIntegral_enorm_periodizedIsotropicAnisotropicNormalizedStretchTensorKernel_le
    {r : ℝ} (hr : 0 < r) {delta : ℝ} (hdelta : 0 < delta) :
    (∫⁻ x in standardFrequencyPairCell,
        ‖periodizedIsotropicAnisotropicNormalizedStretchTensorKernel
          r delta x‖ₑ) ≤
      ENNReal.ofReal
        (delta * ∫ x, ‖normalizedStretchTensorKernel
          explicitBufferedStretchCutoff delta x‖) := by
  let K := anisotropicNormalizedStretchTensorKernel delta
  have hKint : Integrable K :=
    anisotropicNormalizedStretchTensorKernel_integrable hdelta
  calc
    (∫⁻ x in standardFrequencyPairCell,
        ‖periodizedIsotropicAnisotropicNormalizedStretchTensorKernel
          r delta x‖ₑ) ≤ ∫⁻ x, ‖K x‖ₑ := by
      simpa [periodizedIsotropicAnisotropicNormalizedStretchTensorKernel, K]
        using
          setLIntegral_enorm_periodizedIsotropicFrequencyPairKernel_le K
            (anisotropicNormalizedStretchTensorKernel_continuous delta)
            hKint hr
    _ = ENNReal.ofReal (∫ x, ‖K x‖) := by
      rw [ofReal_integral_eq_lintegral_ofReal hKint.norm]
      · simp only [ofReal_norm]
      · exact ae_of_all _ fun x ↦ norm_nonneg (K x)
    _ = ENNReal.ofReal
        (delta * ∫ x, ‖normalizedStretchTensorKernel
          explicitBufferedStretchCutoff delta x‖) := by
      congr 1
      exact integral_norm_anisotropicNormalizedStretchTensorKernel hdelta

/-- One constant controls every positive aperture up to `1/2` and every
positive shell scale after periodization. -/
theorem exists_uniform_periodizedIsotropicAnisotropicNormalizedStretchTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (r : ℝ), 0 < r → ∀ delta ∈ Ioc (0 : ℝ) (1 / 2),
        (∫⁻ x in standardFrequencyPairCell,
          ‖periodizedIsotropicAnisotropicNormalizedStretchTensorKernel
            r delta x‖ₑ) ≤ ENNReal.ofReal (delta * C) := by
  rcases exists_uniform_normalizedStretchTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro r hr delta hdelta
  calc
    (∫⁻ x in standardFrequencyPairCell,
        ‖periodizedIsotropicAnisotropicNormalizedStretchTensorKernel
          r delta x‖ₑ) ≤
        ENNReal.ofReal
          (delta * ∫ x, ‖normalizedStretchTensorKernel
            explicitBufferedStretchCutoff delta x‖) :=
      setLIntegral_enorm_periodizedIsotropicAnisotropicNormalizedStretchTensorKernel_le
        hr hdelta.1
    _ ≤ ENNReal.ofReal (delta * C) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (hmass delta ⟨hdelta.1.le, hdelta.2⟩) hdelta.1.le

/-- Consequently the square-dyadic periodic kernel has the sharp
fundamental-cell bound `C/N`, uniformly for every integer `N ≥ 2`. -/
theorem exists_uniform_periodizedSquareDyadicNormalizedStretchTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      (∫⁻ x in standardFrequencyPairCell,
        ‖periodizedSquareDyadicNormalizedStretchTensorKernel N x‖ₑ) ≤
          ENNReal.ofReal (C / N) := by
  rcases
      exists_uniform_periodizedIsotropicAnisotropicNormalizedStretchTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hdelta : (1 : ℝ) / N ∈ Ioc (0 : ℝ) (1 / 2) := by
    constructor
    · exact one_div_pos.mpr hNR
    · apply (div_le_iff₀' hNR).2
      have hNR2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
  unfold periodizedSquareDyadicNormalizedStretchTensorKernel
  convert hmass ((N : ℝ) ^ 2) (pow_pos hNR 2) ((1 : ℝ) / N) hdelta using 1
  congr 2
  field_simp

end PancakeDyadicKernelScaling
end NavierStokes
end FluidDynamics
end Mettapedia
