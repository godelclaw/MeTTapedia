import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeUniformKernelFamily
import Mettapedia.Analysis.FundamentalDomainPeriodization
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Periodization of the coherent bilinear kernel

This module transfers an integrable Euclidean kernel to a lattice-periodic
kernel.  The key estimate is generic: periodization over any countable,
measure-preserving additive action does not increase `L¹` mass when the
periodic kernel is integrated over a fundamental domain.

The final theorem applies that result to the explicit six-dimensional
normalized coherent-stretching kernel and the standard integer lattice.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeBilinearPeriodization

open MeasureTheory
open PancakeBilinearKernelScaling
open PancakeSmoothCoherentSymbol
open PancakeSmoothCoherentStretchSymbol
open PancakeUniformKernelFamily
open Set
open scoped ENNReal FourierTransform Pointwise

export Mettapedia.Analysis.FundamentalDomainPeriodization
  (addPeriodization
    measurable_addPeriodization
    addPeriodization_vadd
    setLIntegral_enorm_addPeriodization_le
    integrableOn_addPeriodization
    setIntegral_character_smul_addPeriodization_eq)

/-- The standard orthonormal basis of the Euclidean six-space used for the
two three-dimensional input frequencies. -/
def standardFrequencyPairBasis :
    Module.Basis (Fin 6) ℝ EuclideanFrequencyPair :=
  (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis

/-- The integer lattice in the Euclidean six-space. -/
abbrev StandardFrequencyPairLatticeSubmodule :
    Submodule ℤ EuclideanFrequencyPair :=
  Submodule.span ℤ (Set.range standardFrequencyPairBasis)

/-- The Euclidean basis, restricted to integer coefficients, is a concrete
basis of the standard lattice. -/
noncomputable abbrev standardFrequencyPairLatticeBasis :
    Module.Basis (Fin 6) ℤ StandardFrequencyPairLatticeSubmodule :=
  standardFrequencyPairBasis.restrictScalars ℤ

/-- Coordinate description of the standard six-dimensional lattice. -/
noncomputable abbrev standardFrequencyPairLatticeEquiv :
    StandardFrequencyPairLatticeSubmodule ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  standardFrequencyPairLatticeBasis.repr.trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin 6))

noncomputable instance : Countable StandardFrequencyPairLatticeSubmodule :=
  standardFrequencyPairLatticeEquiv.injective.countable

/-- The additive group underlying the standard integer lattice. -/
abbrev StandardFrequencyPairLattice :=
  StandardFrequencyPairLatticeSubmodule.toAddSubgroup

noncomputable instance : Countable StandardFrequencyPairLattice := by
  let f : StandardFrequencyPairLattice →
      StandardFrequencyPairLatticeSubmodule := fun x ↦ ⟨x.1, x.2⟩
  have hf : Function.Injective f := fun x y h ↦
    Subtype.ext (congrArg Subtype.val h)
  exact hf.countable

/-- The half-open standard cell associated to the integer lattice. -/
def standardFrequencyPairCell : Set EuclideanFrequencyPair :=
  ZSpan.fundamentalDomain standardFrequencyPairBasis

/-- The standard six-dimensional cell is a fundamental domain for the
integer lattice. -/
theorem standardFrequencyPairCell_isAddFundamentalDomain :
    IsAddFundamentalDomain StandardFrequencyPairLattice
      standardFrequencyPairCell
      (volume : Measure EuclideanFrequencyPair) := by
  exact ZSpan.isAddFundamentalDomain' standardFrequencyPairBasis volume

/-- Integer wavevectors dual to the standard six-dimensional period lattice. -/
abbrev FrequencyPairWavevector := Fin 6 → ℤ

/-- Embed an integer wavevector in Euclidean six-space. -/
def euclideanFrequencyPairOfWavevector
    (n : FrequencyPairWavevector) : EuclideanFrequencyPair :=
  WithLp.toLp 2 (fun i ↦ (n i : ℝ))

/-- The Euclidean Fourier character associated to an integer wavevector. -/
def euclideanFrequencyPairCharacter
    (n : FrequencyPairWavevector) (x : EuclideanFrequencyPair) : ℂ :=
  Real.fourierChar (-(inner ℝ x (euclideanFrequencyPairOfWavevector n)))

@[fun_prop]
theorem continuous_euclideanFrequencyPairCharacter
    (n : FrequencyPairWavevector) :
    Continuous (euclideanFrequencyPairCharacter n) := by
  unfold euclideanFrequencyPairCharacter euclideanFrequencyPairOfWavevector
  fun_prop

theorem norm_euclideanFrequencyPairCharacter
    (n : FrequencyPairWavevector) (x : EuclideanFrequencyPair) :
    ‖euclideanFrequencyPairCharacter n x‖ = 1 := by
  unfold euclideanFrequencyPairCharacter
  exact Circle.norm_coe _

theorem inner_euclideanFrequencyPairOfWavevector
    (x : EuclideanFrequencyPair) (n : FrequencyPairWavevector) :
    inner ℝ x (euclideanFrequencyPairOfWavevector n) =
      ∑ i : Fin 6, x i * (n i : ℝ) := by
  simp [euclideanFrequencyPairOfWavevector, PiLp.inner_apply,
    RCLike.inner_apply, mul_comm]

/-- Every point of the standard lattice has integer coordinates in the
Euclidean standard basis. -/
theorem exists_integerCoordinates_standardFrequencyPairLattice
    (g : StandardFrequencyPairLattice) :
    ∃ z : Fin 6 → ℤ,
      (g : EuclideanFrequencyPair) =
        WithLp.toLp 2 (fun i ↦ (z i : ℝ)) := by
  obtain ⟨z, hz⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp g.property
  refine ⟨z, ?_⟩
  rw [← hz]
  classical
  ext i
  simp [standardFrequencyPairBasis, EuclideanSpace.basisFun_apply,
    Pi.single_apply]

/-- Integer-frequency Euclidean characters are invariant under the standard
period lattice. -/
theorem euclideanFrequencyPairCharacter_vadd
    (n : FrequencyPairWavevector) (g : StandardFrequencyPairLattice)
    (x : EuclideanFrequencyPair) :
    euclideanFrequencyPairCharacter n (g +ᵥ x) =
      euclideanFrequencyPairCharacter n x := by
  rcases exists_integerCoordinates_standardFrequencyPairLattice g with
    ⟨z, hz⟩
  let m : ℤ := ∑ i : Fin 6, z i * n i
  have hginner :
      inner ℝ (g : EuclideanFrequencyPair)
          (euclideanFrequencyPairOfWavevector n) = (m : ℝ) := by
    rw [hz, inner_euclideanFrequencyPairOfWavevector]
    simp [m]
  have hinner :
      inner ℝ (g +ᵥ x) (euclideanFrequencyPairOfWavevector n) =
        (m : ℝ) +
          inner ℝ x (euclideanFrequencyPairOfWavevector n) := by
    rw [show g +ᵥ x = (g : EuclideanFrequencyPair) + x by rfl,
      inner_add_left, hginner]
  have hmchar : Real.fourierChar (-(m : ℝ)) = 1 := by
    rw [Real.fourierChar_apply']
    have harg : 2 * Real.pi * -(m : ℝ) =
        (-m : ℤ) * (2 * Real.pi) := by
      push_cast
      ring
    rw [harg, Circle.exp_intCast_mul, Circle.exp_two_pi, one_zpow]
  unfold euclideanFrequencyPairCharacter
  rw [hinner, neg_add, Real.fourierChar.map_add_eq_mul, hmchar, Circle.coe_mul,
    Circle.coe_one, one_mul]

/-- On raw coordinates, the multivariate torus monomial and the Euclidean
integer-frequency character use exactly the same Fourier normalization. -/
theorem mFourier_neg_coe_eq_euclideanFrequencyPairCharacter
    (n : FrequencyPairWavevector) (x : Fin 6 → ℝ) :
    UnitAddTorus.mFourier (-n)
        (fun i ↦ (x i : UnitAddCircle)) =
      euclideanFrequencyPairCharacter n (WithLp.toLp 2 x) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    fourier_coe_apply]
  unfold euclideanFrequencyPairCharacter
  rw [inner_euclideanFrequencyPairOfWavevector, Real.fourierChar_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [div_one]
  calc
    (∑ i : Fin 6,
        2 * (Real.pi : ℂ) * Complex.I * -(n i : ℂ) * (x i : ℂ)) =
        ∑ i : Fin 6,
          -(2 * (Real.pi : ℂ) * Complex.I *
            ((x i : ℂ) * (n i : ℂ))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = -(∑ i : Fin 6,
          2 * (Real.pi : ℂ) * Complex.I *
            ((x i : ℂ) * (n i : ℂ))) := by
      rw [Finset.sum_neg_distrib]
    _ = -(2 * (Real.pi : ℂ) * Complex.I *
          (∑ i : Fin 6, (x i : ℂ) * (n i : ℂ))) := by
      rw [Finset.mul_sum]
    _ = (2 * (Real.pi : ℂ) *
          -(∑ i : Fin 6, (x i : ℂ) * (n i : ℂ))) *
          Complex.I := by
      ring

/-- The explicit normalized coherent-stretching kernel, periodized over the
standard integer lattice. -/
def periodizedNormalizedStretchTensorKernel
    (delta : ℝ) (x : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  addPeriodization
    (G := StandardFrequencyPairLattice)
    (normalizedStretchTensorKernel explicitBufferedStretchCutoff delta) x

/-- The cover-side periodized coherent kernel is invariant under the standard
integer lattice. -/
theorem periodizedNormalizedStretchTensorKernel_vadd
    (delta : ℝ) (g : StandardFrequencyPairLattice)
    (x : EuclideanFrequencyPair) :
    periodizedNormalizedStretchTensorKernel delta (g +ᵥ x) =
      periodizedNormalizedStretchTensorKernel delta x :=
  addPeriodization_vadd _ g x

/-- The integer-character coefficient of the periodized kernel on one
fundamental cell is exactly the Euclidean Fourier transform of the original
kernel, hence the normalized coherent-stretching symbol at that wavevector. -/
theorem setIntegral_character_periodizedNormalizedStretchTensorKernel
    (delta : ℝ) (n : FrequencyPairWavevector) :
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x •
          periodizedNormalizedStretchTensorKernel delta x) =
      normalizedStretchTensorSymbol explicitBufferedStretchCutoff delta
        (euclideanFrequencyPairOfWavevector n) := by
  let K : EuclideanFrequencyPair → CoherentBilinearOperator :=
    normalizedStretchTensorKernel explicitBufferedStretchCutoff delta
  have htransfer := setIntegral_character_smul_addPeriodization_eq
    standardFrequencyPairCell_isAddFundamentalDomain K
    ((normalizedStretchTensorKernel_continuous
      explicitBufferedStretchCutoff delta).measurable)
    (normalizedStretchTensorKernel_integrable
      explicitBufferedStretchCutoff delta)
    (euclideanFrequencyPairCharacter n)
    (continuous_euclideanFrequencyPairCharacter n).measurable
    (norm_euclideanFrequencyPairCharacter n)
    (euclideanFrequencyPairCharacter_vadd n)
  calc
    (∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x •
          periodizedNormalizedStretchTensorKernel delta x) =
        ∫ x, euclideanFrequencyPairCharacter n x • K x := by
      simpa [periodizedNormalizedStretchTensorKernel, K] using htransfer
    _ = FourierTransform.fourier K (euclideanFrequencyPairOfWavevector n) := by
      rw [Real.fourier_eq]
      rfl
    _ = normalizedStretchTensorSymbol explicitBufferedStretchCutoff delta
          (euclideanFrequencyPairOfWavevector n) := by
      change FourierTransform.fourier
          ((normalizedStretchTensorKernel explicitBufferedStretchCutoff delta :
            SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator) :
              EuclideanFrequencyPair → CoherentBilinearOperator)
          (euclideanFrequencyPairOfWavevector n) = _
      rw [← SchwartzMap.fourier_coe]
      exact congrArg
        (fun f : SchwartzMap EuclideanFrequencyPair CoherentBilinearOperator ↦
          f (euclideanFrequencyPairOfWavevector n))
        (fourier_normalizedStretchTensorKernel
          explicitBufferedStretchCutoff delta)

/-- The geometric six-torus obtained by quotienting Euclidean frequency-pair
space by its standard integer lattice. -/
abbrev FrequencyPairLatticeTorus :=
  Quotient (AddAction.orbitRel
    StandardFrequencyPairLattice EuclideanFrequencyPair)

/-- The genuinely quotient-valued periodization of the normalized coherent
kernel. -/
def quotientPeriodizedNormalizedStretchTensorKernel
    (delta : ℝ) : FrequencyPairLatticeTorus → CoherentBilinearOperator :=
  AddAction.automorphize
    (α := StandardFrequencyPairLattice)
    (normalizedStretchTensorKernel explicitBufferedStretchCutoff delta)

@[simp]
theorem quotientPeriodizedNormalizedStretchTensorKernel_mk
    (delta : ℝ) (x : EuclideanFrequencyPair) :
    quotientPeriodizedNormalizedStretchTensorKernel delta
        (Quotient.mk
          (AddAction.orbitRel
            StandardFrequencyPairLattice EuclideanFrequencyPair) x) =
      periodizedNormalizedStretchTensorKernel delta x :=
  rfl

/-- The quotient-periodized kernel is measurable on the lattice torus. -/
theorem measurable_quotientPeriodizedNormalizedStretchTensorKernel
    (delta : ℝ) :
    Measurable (quotientPeriodizedNormalizedStretchTensorKernel delta) := by
  rw [measurable_from_quotient]
  change Measurable (periodizedNormalizedStretchTensorKernel delta)
  exact measurable_addPeriodization
    (G := StandardFrequencyPairLattice)
    (normalizedStretchTensorKernel explicitBufferedStretchCutoff delta)
    ((normalizedStretchTensorKernel_continuous
      explicitBufferedStretchCutoff delta).measurable)

/-- The quotient measure obtained by pushing the Euclidean measure on the
standard fundamental cell to the lattice torus. -/
def frequencyPairLatticeTorusMeasure : Measure FrequencyPairLatticeTorus :=
  Measure.map
    (Quotient.mk
      (AddAction.orbitRel
        StandardFrequencyPairLattice EuclideanFrequencyPair))
    ((volume : Measure EuclideanFrequencyPair).restrict
      standardFrequencyPairCell)

/-- The periodized normalized coherent-stretching kernel has one fundamental-
cell `L¹` bound, uniform in the aperture parameter. -/
theorem exists_uniform_periodizedNormalizedStretchTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        (∫⁻ x in standardFrequencyPairCell,
          ‖periodizedNormalizedStretchTensorKernel delta x‖ₑ) ≤
            ENNReal.ofReal C := by
  rcases exists_uniform_normalizedStretchTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta
  let K : EuclideanFrequencyPair → CoherentBilinearOperator :=
    normalizedStretchTensorKernel explicitBufferedStretchCutoff delta
  have hKmeas : Measurable K :=
    (normalizedStretchTensorKernel_continuous
      explicitBufferedStretchCutoff delta).measurable
  have hKint : Integrable K :=
    normalizedStretchTensorKernel_integrable
      explicitBufferedStretchCutoff delta
  calc
    (∫⁻ x in standardFrequencyPairCell,
        ‖periodizedNormalizedStretchTensorKernel delta x‖ₑ) ≤
        ∫⁻ x, ‖K x‖ₑ := by
      simpa [periodizedNormalizedStretchTensorKernel, K] using
        setLIntegral_enorm_addPeriodization_le
          standardFrequencyPairCell_isAddFundamentalDomain K hKmeas
    _ = ENNReal.ofReal (∫ x, ‖K x‖) := by
      rw [ofReal_integral_eq_lintegral_ofReal hKint.norm]
      · simp only [ofReal_norm]
      · exact ae_of_all _ fun x ↦ norm_nonneg (K x)
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hmass delta hdelta)

/-- **Uniform torus kernel mass.**  The normalized coherent-stretching kernel
descends to the geometric six-torus and has one `L¹` bound there, uniform in
the aperture parameter. -/
theorem exists_uniform_quotientPeriodizedNormalizedStretchTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        (∫⁻ q : FrequencyPairLatticeTorus,
          ‖quotientPeriodizedNormalizedStretchTensorKernel delta q‖ₑ
            ∂frequencyPairLatticeTorusMeasure) ≤ ENNReal.ofReal C := by
  rcases exists_uniform_periodizedNormalizedStretchTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta
  rw [frequencyPairLatticeTorusMeasure, lintegral_map]
  · simpa only [quotientPeriodizedNormalizedStretchTensorKernel_mk] using
      hmass delta hdelta
  · exact (measurable_quotientPeriodizedNormalizedStretchTensorKernel
      delta).enorm
  · exact measurable_quotient_mk''

/-! ## Transfer to mathlib's standard six-torus -/

/-- The standard unit six-torus, viewed as the product of six unit additive
circles. -/
abbrev FrequencyPairUnitTorus := UnitAddTorus (Fin 6)

/-- The probability Haar measure used by mathlib's multivariate unit-torus
Fourier theory. -/
def frequencyPairUnitTorusMeasure : Measure (UnitAddTorus (Fin 6)) :=
  Measure.pi (fun _ : Fin 6 ↦ AddCircle.haarAddCircle)

/-- The half-open coordinate cube matching the standard lattice cell. -/
def rawFrequencyPairCellIco : Set (Fin 6 → ℝ) :=
  {x | ∀ i, x i ∈ Ico (0 : ℝ) 1}

/-- The alternate half-open cube used by mathlib's additive-circle chart. -/
def rawFrequencyPairCellIoc : Set (Fin 6 → ℝ) :=
  {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1}

theorem preimage_standardFrequencyPairCell_toLp :
    (WithLp.toLp 2 : (Fin 6 → ℝ) → EuclideanFrequencyPair) ⁻¹'
        standardFrequencyPairCell = rawFrequencyPairCellIco := by
  ext x
  simp [standardFrequencyPairCell, rawFrequencyPairCellIco,
    ZSpan.mem_fundamentalDomain, standardFrequencyPairBasis,
    EuclideanSpace.basisFun_repr]

/-- The two choices of half-open unit cube differ only on their boundary. -/
theorem rawFrequencyPairCellIco_ae_eq_Ioc :
    rawFrequencyPairCellIco =ᵐ[(volume : Measure (Fin 6 → ℝ))]
      rawFrequencyPairCellIoc := by
  rw [volume_pi]
  have h :=
    ((Measure.univ_pi_Ico_ae_eq_Icc
      (μ := fun _ : Fin 6 ↦ (volume : Measure ℝ))
      (f := fun _ : Fin 6 ↦ (0 : ℝ))
      (g := fun _ : Fin 6 ↦ (1 : ℝ))).trans
    (Measure.univ_pi_Ioc_ae_eq_Icc
      (μ := fun _ : Fin 6 ↦ (volume : Measure ℝ))
      (f := fun _ : Fin 6 ↦ (0 : ℝ))
      (g := fun _ : Fin 6 ↦ (1 : ℝ))).symm)
  have hIco : rawFrequencyPairCellIco =
      Set.pi Set.univ (fun _ : Fin 6 ↦ Ico (0 : ℝ) 1) := by
    ext x
    simp only [rawFrequencyPairCellIco, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, forall_true_left]
  have hIoc : rawFrequencyPairCellIoc =
      Set.pi Set.univ (fun _ : Fin 6 ↦ Ioc (0 : ℝ) 1) := by
    ext x
    simp only [rawFrequencyPairCellIoc, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, forall_true_left]
  rw [hIco, hIoc]
  exact h

/-- The canonical representative in the `Ioc 0 1` coordinate cube. -/
def unitTorusFrequencyPairRepresentative
    (q : UnitAddTorus (Fin 6)) : EuclideanFrequencyPair :=
  WithLp.toLp 2 (fun i ↦ (AddCircle.equivIoc 1 0 (q i)).1)

theorem measurable_unitTorusFrequencyPairRepresentative :
    Measurable unitTorusFrequencyPairRepresentative := by
  exact (MeasurableEquiv.toLp 2 (Fin 6 → ℝ)).measurable.comp
    (measurable_subtype_coe.comp
      (UnitAddTorus.measurableEquivPiIoc
        (fun _ : Fin 6 ↦ (0 : ℝ))).measurable)

/-- On the chosen half-open cell, taking the torus class and then its
canonical representative returns the original Euclidean point. -/
theorem unitTorusFrequencyPairRepresentative_coe
    (x : Fin 6 → ℝ) (hx : x ∈ rawFrequencyPairCellIoc) :
    unitTorusFrequencyPairRepresentative (fun i ↦ (x i : UnitAddCircle)) =
      WithLp.toLp 2 x := by
  have hx' : ∀ i, x i ∈ Ioc (0 : ℝ) 1 := by
    simpa [rawFrequencyPairCellIoc] using hx
  unfold unitTorusFrequencyPairRepresentative
  apply congrArg (WithLp.toLp 2)
  funext i
  exact congrArg Subtype.val
    (AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ))
      (by simpa using hx' i))

/-- The normalized coherent kernel on the standard unit six-torus. -/
def unitTorusPeriodizedNormalizedStretchTensorKernel
    (delta : ℝ) (q : UnitAddTorus (Fin 6)) : CoherentBilinearOperator :=
  periodizedNormalizedStretchTensorKernel delta
    (unitTorusFrequencyPairRepresentative q)

theorem measurable_unitTorusPeriodizedNormalizedStretchTensorKernel
    (delta : ℝ) :
    Measurable (unitTorusPeriodizedNormalizedStretchTensorKernel delta) := by
  exact (measurable_addPeriodization
    (G := StandardFrequencyPairLattice)
    (normalizedStretchTensorKernel explicitBufferedStretchCutoff delta)
    ((normalizedStretchTensorKernel_continuous
      explicitBufferedStretchCutoff delta).measurable)).comp
    measurable_unitTorusFrequencyPairRepresentative

/-- Fourier coefficient on the standard six-torus, tied explicitly to the
product Haar measure used in this module. -/
def frequencyPairUnitTorusFourierCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : FrequencyPairUnitTorus → E) (n : FrequencyPairWavevector) : E :=
  ∫ q, UnitAddTorus.mFourier (-n) q • F q
    ∂frequencyPairUnitTorusMeasure

/-- **Exact standard-torus symbol realization.**  Every integer Fourier
coefficient of the periodized normalized kernel is the intended Euclidean
coherent-stretching symbol sampled at that lattice wavevector. -/
theorem frequencyPairUnitTorusFourierCoeff_periodizedNormalizedStretchTensorKernel
    (delta : ℝ) (n : FrequencyPairWavevector) :
    frequencyPairUnitTorusFourierCoeff
        (unitTorusPeriodizedNormalizedStretchTensorKernel delta) n =
      normalizedStretchTensorSymbol explicitBufferedStretchCutoff delta
        (euclideanFrequencyPairOfWavevector n) := by
  unfold frequencyPairUnitTorusFourierCoeff
  calc
    (∫ q : FrequencyPairUnitTorus,
        UnitAddTorus.mFourier (-n) q •
          unitTorusPeriodizedNormalizedStretchTensorKernel delta q
            ∂frequencyPairUnitTorusMeasure) =
        ∫ x : Fin 6 → ℝ in rawFrequencyPairCellIoc,
          UnitAddTorus.mFourier (-n)
              (fun i ↦ (x i : UnitAddCircle)) •
            unitTorusPeriodizedNormalizedStretchTensorKernel delta
              (fun i ↦ (x i : UnitAddCircle)) := by
      have hpre := UnitAddTorus.integral_preimage
        (fun q : FrequencyPairUnitTorus ↦
          UnitAddTorus.mFourier (-n) q •
            unitTorusPeriodizedNormalizedStretchTensorKernel delta q)
        (fun _ : Fin 6 ↦ (0 : ℝ))
      change (∫ q : FrequencyPairUnitTorus,
          UnitAddTorus.mFourier (-n) q •
            unitTorusPeriodizedNormalizedStretchTensorKernel delta q
              ∂frequencyPairUnitTorusMeasure) =
        ∫ x : Fin 6 → ℝ in
          {x | ∀ i, x i ∈ Ioc (0 : ℝ) (0 + 1)},
          UnitAddTorus.mFourier (-n)
              (fun i ↦ (x i : UnitAddCircle)) •
            unitTorusPeriodizedNormalizedStretchTensorKernel delta
              (fun i ↦ (x i : UnitAddCircle)) at hpre
      simpa [rawFrequencyPairCellIoc] using hpre
    _ = ∫ x : Fin 6 → ℝ in rawFrequencyPairCellIoc,
          euclideanFrequencyPairCharacter n (WithLp.toLp 2 x) •
            periodizedNormalizedStretchTensorKernel delta
              (WithLp.toLp 2 x) := by
      have hcellmeas : MeasurableSet rawFrequencyPairCellIoc := by
        simpa [rawFrequencyPairCellIoc] using
          (MeasurableSet.univ_pi' (fun _ : Fin 6 ↦
            (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))))
      apply setIntegral_congr_fun hcellmeas
      intro x hx
      change UnitAddTorus.mFourier (-n)
            (fun i ↦ (x i : UnitAddCircle)) •
          unitTorusPeriodizedNormalizedStretchTensorKernel delta
            (fun i ↦ (x i : UnitAddCircle)) = _
      rw [mFourier_neg_coe_eq_euclideanFrequencyPairCharacter]
      change euclideanFrequencyPairCharacter n (WithLp.toLp 2 x) •
          periodizedNormalizedStretchTensorKernel delta
            (unitTorusFrequencyPairRepresentative
              (fun i ↦ (x i : UnitAddCircle))) = _
      rw [unitTorusFrequencyPairRepresentative_coe x hx]
    _ = ∫ x : Fin 6 → ℝ in rawFrequencyPairCellIco,
          euclideanFrequencyPairCharacter n (WithLp.toLp 2 x) •
            periodizedNormalizedStretchTensorKernel delta
              (WithLp.toLp 2 x) :=
      setIntegral_congr_set rawFrequencyPairCellIco_ae_eq_Ioc.symm
    _ = ∫ x : EuclideanFrequencyPair in standardFrequencyPairCell,
          euclideanFrequencyPairCharacter n x •
            periodizedNormalizedStretchTensorKernel delta x := by
      let F : EuclideanFrequencyPair → CoherentBilinearOperator := fun x ↦
        euclideanFrequencyPairCharacter n x •
          periodizedNormalizedStretchTensorKernel delta x
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
    _ = normalizedStretchTensorSymbol explicitBufferedStretchCutoff delta
          (euclideanFrequencyPairOfWavevector n) :=
      setIntegral_character_periodizedNormalizedStretchTensorKernel delta n

/-- **Uniform standard-torus kernel mass.**  The normalized coherent kernel
has one `L¹` bound on mathlib's standard unit six-torus, uniformly in the
aperture parameter. -/
theorem exists_uniform_unitTorusPeriodizedNormalizedStretchTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        (∫⁻ q : UnitAddTorus (Fin 6),
          ‖unitTorusPeriodizedNormalizedStretchTensorKernel delta q‖ₑ
            ∂frequencyPairUnitTorusMeasure) ≤
            ENNReal.ofReal C := by
  rcases exists_uniform_periodizedNormalizedStretchTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta
  calc
    (∫⁻ q : UnitAddTorus (Fin 6),
        ‖unitTorusPeriodizedNormalizedStretchTensorKernel delta q‖ₑ
          ∂frequencyPairUnitTorusMeasure) =
        ∫⁻ x : Fin 6 → ℝ in rawFrequencyPairCellIoc,
          ‖periodizedNormalizedStretchTensorKernel delta
            (WithLp.toLp 2 x)‖ₑ := by
      calc
        _ = ∫⁻ x : Fin 6 → ℝ in rawFrequencyPairCellIoc,
              ‖unitTorusPeriodizedNormalizedStretchTensorKernel delta
                (fun i ↦ (x i : UnitAddCircle))‖ₑ :=
          by
            have hpre := UnitAddTorus.lintegral_preimage
              (fun q : UnitAddTorus (Fin 6) ↦
                ‖unitTorusPeriodizedNormalizedStretchTensorKernel delta q‖ₑ)
              (fun _ : Fin 6 ↦ (0 : ℝ))
            change (∫⁻ q : UnitAddTorus (Fin 6),
                ‖unitTorusPeriodizedNormalizedStretchTensorKernel delta q‖ₑ
                  ∂frequencyPairUnitTorusMeasure) =
              ∫⁻ x : Fin 6 → ℝ in
                {x | ∀ i, x i ∈ Ioc (0 : ℝ) (0 + 1)},
                ‖unitTorusPeriodizedNormalizedStretchTensorKernel delta
                  (fun i ↦ (x i : UnitAddCircle))‖ₑ at hpre
            simpa [rawFrequencyPairCellIoc] using hpre
        _ = _ := by
          have hcellmeas : MeasurableSet rawFrequencyPairCellIoc := by
            simpa [rawFrequencyPairCellIoc] using
              (MeasurableSet.univ_pi' (fun _ : Fin 6 ↦
                (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))))
          apply setLIntegral_congr_fun hcellmeas
          intro x hx
          change ‖periodizedNormalizedStretchTensorKernel delta
            (unitTorusFrequencyPairRepresentative
              (fun i ↦ (x i : UnitAddCircle)))‖ₑ = _
          rw [unitTorusFrequencyPairRepresentative_coe x hx]
    _ = ∫⁻ x : Fin 6 → ℝ in rawFrequencyPairCellIco,
          ‖periodizedNormalizedStretchTensorKernel delta
            (WithLp.toLp 2 x)‖ₑ :=
      setLIntegral_congr rawFrequencyPairCellIco_ae_eq_Ioc.symm
    _ = ∫⁻ x : EuclideanFrequencyPair in standardFrequencyPairCell,
          ‖periodizedNormalizedStretchTensorKernel delta x‖ₑ := by
      have hpres := (PiLp.volume_preserving_toLp (Fin 6)).setLIntegral_comp_preimage
        (ZSpan.fundamentalDomain_measurableSet standardFrequencyPairBasis)
        ((measurable_addPeriodization
          (G := StandardFrequencyPairLattice)
          (normalizedStretchTensorKernel explicitBufferedStretchCutoff delta)
          ((normalizedStretchTensorKernel_continuous
            explicitBufferedStretchCutoff delta).measurable)).enorm)
      have hpre :
          (WithLp.toLp 2 : (Fin 6 → ℝ) → EuclideanFrequencyPair) ⁻¹'
              ZSpan.fundamentalDomain standardFrequencyPairBasis =
            rawFrequencyPairCellIco := by
        simpa [standardFrequencyPairCell] using
          preimage_standardFrequencyPairCell_toLp
      rw [hpre] at hpres
      simpa [standardFrequencyPairCell,
        periodizedNormalizedStretchTensorKernel] using hpres
    _ ≤ ENNReal.ofReal C := hmass delta hdelta

/-- On the admissible aperture interval, the periodized normalized kernel is
Bochner integrable on the standard six-torus. -/
theorem integrable_unitTorusPeriodizedNormalizedStretchTensorKernel
    {delta : ℝ} (hdelta : delta ∈ Icc (0 : ℝ) (1 / 2)) :
    Integrable (unitTorusPeriodizedNormalizedStretchTensorKernel delta)
      frequencyPairUnitTorusMeasure := by
  rcases exists_uniform_unitTorusPeriodizedNormalizedStretchTensorKernel_mass with
    ⟨C, _hC, hmass⟩
  refine ⟨(measurable_unitTorusPeriodizedNormalizedStretchTensorKernel
    delta).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (hmass delta hdelta) ENNReal.ofReal_lt_top

/-- **Real-valued uniform torus mass bound.**  The same constant controls the
Bochner-integral `L¹` mass and simultaneously certifies integrability. -/
theorem exists_uniform_unitTorusPeriodizedNormalizedStretchTensorKernel_integral_norm :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        Integrable (unitTorusPeriodizedNormalizedStretchTensorKernel delta)
            frequencyPairUnitTorusMeasure ∧
          (∫ q : UnitAddTorus (Fin 6),
            ‖unitTorusPeriodizedNormalizedStretchTensorKernel delta q‖
              ∂frequencyPairUnitTorusMeasure) ≤ C := by
  rcases exists_uniform_unitTorusPeriodizedNormalizedStretchTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta
  have hKint := integrable_unitTorusPeriodizedNormalizedStretchTensorKernel hdelta
  refine ⟨hKint, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_norm_eq_lintegral_enorm hKint]
  exact hmass delta hdelta

/-! ## Periodic bilinear Young inequality -/

/-- The physical three-torus on which the two input fields live. -/
abbrev BilinearSpatialTorus := UnitAddTorus (Fin 3)

/-- The first three coordinates of a frequency-pair torus displacement. -/
def firstTorusDisplacement
    (q : FrequencyPairUnitTorus) : BilinearSpatialTorus :=
  fun i ↦ q ⟨i.1, Nat.lt_trans i.2 (by norm_num)⟩

/-- The last three coordinates of a frequency-pair torus displacement. -/
def secondTorusDisplacement
    (q : FrequencyPairUnitTorus) : BilinearSpatialTorus :=
  fun i ↦ q ⟨i.1 + 3, by omega⟩

/-- Concatenate the two physical three-wavevectors into the corresponding
six-dimensional frequency-pair wavevector. -/
def pairWavevector (k l : Fin 3 → ℤ) : FrequencyPairWavevector :=
  Fin.append k l

theorem neg_pairWavevector (k l : Fin 3 → ℤ) :
    -(pairWavevector k l) = pairWavevector (-k) (-l) := by
  unfold pairWavevector
  apply funext
  exact @Fin.addCases 3 3
    (fun i : Fin (3 + 3) ↦
      (-Fin.append k l) i = Fin.append (-k) (-l) i)
    (fun j ↦ by
      change -(Fin.append k l (Fin.castAdd 3 j)) =
        Fin.append (-k) (-l) (Fin.castAdd 3 j)
      rw [Fin.append_left, Fin.append_left, Pi.neg_apply])
    (fun j ↦ by
      change -(Fin.append k l (Fin.natAdd 3 j)) =
        Fin.append (-k) (-l) (Fin.natAdd 3 j)
      rw [Fin.append_right, Fin.append_right, Pi.neg_apply])

@[fun_prop]
theorem continuous_firstTorusDisplacement :
    Continuous firstTorusDisplacement := by
  unfold firstTorusDisplacement
  fun_prop

@[fun_prop]
theorem continuous_secondTorusDisplacement :
    Continuous secondTorusDisplacement := by
  unfold secondTorusDisplacement
  fun_prop

/-- A six-torus character at a concatenated wavevector factors into the two
three-torus characters seen by the displacement projections. -/
theorem mFourier_pairWavevector
    (k l : Fin 3 → ℤ) (q : FrequencyPairUnitTorus) :
    UnitAddTorus.mFourier (pairWavevector k l) q =
      UnitAddTorus.mFourier k (firstTorusDisplacement q) *
        UnitAddTorus.mFourier l (secondTorusDisplacement q) := by
  unfold UnitAddTorus.mFourier pairWavevector firstTorusDisplacement
    secondTorusDisplacement
  simp only [ContinuousMap.coe_mk]
  change (∏ i : Fin (3 + 3), (fourier ((Fin.append k l) i)) (q i)) = _
  rw [Fin.prod_univ_add]
  congr 1

/-- Translation identity for a Fourier monomial on the physical torus. -/
theorem mFourier_sub_apply_spatial
    (k : Fin 3 → ℤ) (x y : BilinearSpatialTorus) :
    UnitAddTorus.mFourier k (x - y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.sub_apply,
    fourier_apply, zsmul_sub]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [← Circle.coe_mul, ← AddCircle.toCircle_add]
  congr 2
  rw [Pi.neg_apply, neg_zsmul, sub_eq_add_neg]

/-- Applying a coefficient tensor is complex bilinear in its two vector
arguments. -/
theorem applyCoherentBilinearOperator_smul_smul
    (A : CoherentBilinearOperator) (c d : ℂ) (u v : ComplexVec3) :
    applyCoherentBilinearOperator A (c • u) (d • v) =
      (c * d) • applyCoherentBilinearOperator A u v := by
  ext i
  simp only [applyCoherentBilinearOperator, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _hl
  ring

/-- Evaluation of a coefficient tensor on two fixed vectors as a continuous
linear map in the tensor variable. -/
def applyCoherentBilinearOperatorCLM (u v : ComplexVec3) :
    CoherentBilinearOperator →L[ℂ] ComplexVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ applyCoherentBilinearOperator A u v
      map_add' := by
        intro A B
        ext i
        simp only [applyCoherentBilinearOperator, Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro l _hl
        ring
      map_smul' := by
        intro c A
        ext i
        simp only [applyCoherentBilinearOperator, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _hl
        simp only [RingHom.id_apply]
        ring }

@[simp]
theorem applyCoherentBilinearOperatorCLM_apply
    (u v : ComplexVec3) (A : CoherentBilinearOperator) :
    applyCoherentBilinearOperatorCLM u v A =
      applyCoherentBilinearOperator A u v := rfl

theorem applyCoherentBilinearOperator_smul_tensor
    (c : ℂ) (A : CoherentBilinearOperator) (u v : ComplexVec3) :
    applyCoherentBilinearOperator (c • A) u v =
      c • applyCoherentBilinearOperator A u v := by
  simpa only [applyCoherentBilinearOperatorCLM_apply, RingHom.id_apply] using
    (applyCoherentBilinearOperatorCLM u v).map_smul c A

/-- Translation-invariant bilinear action of a six-torus tensor kernel on
two vector fields on the physical three-torus. -/
def torusBilinearKernelAction
    (K : FrequencyPairUnitTorus → CoherentBilinearOperator)
    (f g : BilinearSpatialTorus → ComplexVec3)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  ∫ q, applyCoherentBilinearOperator (K q)
      (f (x - firstTorusDisplacement q))
      (g (x - secondTorusDisplacement q))
        ∂frequencyPairUnitTorusMeasure

/-- A periodic bilinear kernel acts on a pair of Fourier monomials through
its genuine six-dimensional Fourier coefficient. -/
theorem torusBilinearKernelAction_monomials
    (K : FrequencyPairUnitTorus → CoherentBilinearOperator)
    (hKint : Integrable K frequencyPairUnitTorusMeasure)
    (k l : Fin 3 → ℤ) (u v : ComplexVec3) (x : BilinearSpatialTorus) :
    torusBilinearKernelAction K
        (fun z ↦ UnitAddTorus.mFourier k z • u)
        (fun z ↦ UnitAddTorus.mFourier l z • v) x =
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
        applyCoherentBilinearOperator
          (frequencyPairUnitTorusFourierCoeff K (pairWavevector k l)) u v := by
  let n : FrequencyPairWavevector := pairWavevector k l
  have hweighted : Integrable
      (fun q : FrequencyPairUnitTorus ↦
        UnitAddTorus.mFourier (-n) q • K q)
      frequencyPairUnitTorusMeasure := by
    change Integrable
      ((fun q : FrequencyPairUnitTorus ↦
        UnitAddTorus.mFourier (-n) q) • K)
      frequencyPairUnitTorusMeasure
    apply hKint.bdd_smul 1
    · exact (UnitAddTorus.mFourier (-n)).continuous.aestronglyMeasurable
    · filter_upwards with q
      simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
        fourier_apply, Circle.norm_coe, Finset.prod_const_one, le_rfl]
  have hintegrand (q : FrequencyPairUnitTorus) :
      applyCoherentBilinearOperator (K q)
          (UnitAddTorus.mFourier k (x - firstTorusDisplacement q) • u)
          (UnitAddTorus.mFourier l (x - secondTorusDisplacement q) • v) =
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          applyCoherentBilinearOperator
            (UnitAddTorus.mFourier (-n) q • K q) u v := by
    rw [mFourier_sub_apply_spatial, mFourier_sub_apply_spatial,
      applyCoherentBilinearOperator_smul_smul,
      applyCoherentBilinearOperator_smul_tensor]
    have hchar :
        UnitAddTorus.mFourier (-n) q =
          UnitAddTorus.mFourier (-k) (firstTorusDisplacement q) *
            UnitAddTorus.mFourier (-l) (secondTorusDisplacement q) := by
      rw [show -n = pairWavevector (-k) (-l) by
        simpa [n] using neg_pairWavevector k l]
      exact mFourier_pairWavevector (-k) (-l) q
    rw [hchar, smul_smul]
    congr 1
    ring
  unfold torusBilinearKernelAction
  calc
    (∫ q : FrequencyPairUnitTorus,
        applyCoherentBilinearOperator (K q)
          (UnitAddTorus.mFourier k (x - firstTorusDisplacement q) • u)
          (UnitAddTorus.mFourier l (x - secondTorusDisplacement q) • v)
            ∂frequencyPairUnitTorusMeasure) =
        ∫ q : FrequencyPairUnitTorus,
          (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
            applyCoherentBilinearOperator
              (UnitAddTorus.mFourier (-n) q • K q) u v
                ∂frequencyPairUnitTorusMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hintegrand
    _ = (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          ∫ q : FrequencyPairUnitTorus,
            applyCoherentBilinearOperator
              (UnitAddTorus.mFourier (-n) q • K q) u v
                ∂frequencyPairUnitTorusMeasure := by
      rw [integral_smul]
    _ = (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          applyCoherentBilinearOperator
            (∫ q : FrequencyPairUnitTorus,
              UnitAddTorus.mFourier (-n) q • K q
                ∂frequencyPairUnitTorusMeasure) u v := by
      apply congrArg (fun z : ComplexVec3 ↦
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) • z)
      simpa only [applyCoherentBilinearOperatorCLM_apply] using
        (applyCoherentBilinearOperatorCLM u v).integral_comp_comm hweighted
    _ = (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
        applyCoherentBilinearOperator
          (frequencyPairUnitTorusFourierCoeff K (pairWavevector k l)) u v := by
      rfl

/-- The normalized periodized kernel realizes the normalized coherent symbol
on every pair of Fourier monomials. -/
theorem unitTorusPeriodizedNormalizedStretch_action_monomials
    {delta : ℝ} (hdelta : delta ∈ Icc (0 : ℝ) (1 / 2))
    (k l : Fin 3 → ℤ) (u v : ComplexVec3) (x : BilinearSpatialTorus) :
    torusBilinearKernelAction
        (unitTorusPeriodizedNormalizedStretchTensorKernel delta)
        (fun z ↦ UnitAddTorus.mFourier k z • u)
        (fun z ↦ UnitAddTorus.mFourier l z • v) x =
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
        applyCoherentBilinearOperator
          (normalizedStretchTensorSymbol explicitBufferedStretchCutoff delta
            (euclideanFrequencyPairOfWavevector (pairWavevector k l))) u v := by
  rw [torusBilinearKernelAction_monomials _
    (integrable_unitTorusPeriodizedNormalizedStretchTensorKernel hdelta)]
  rw [frequencyPairUnitTorusFourierCoeff_periodizedNormalizedStretchTensorKernel]

/-- The localized coherent-stretching symbol with its exact aperture factor
restored. -/
def localizedStretchTensorSymbol
    (delta : ℝ) (xi : EuclideanFrequencyPair) : CoherentBilinearOperator :=
  ((delta : ℂ) •
    normalizedStretchTensorSymbol explicitBufferedStretchCutoff delta xi)

/-- The periodic coherent-stretching kernel with its exact aperture factor
restored. -/
def unitTorusPeriodizedStretchTensorKernel
    (delta : ℝ) (q : FrequencyPairUnitTorus) : CoherentBilinearOperator :=
  (delta : ℂ) •
    unitTorusPeriodizedNormalizedStretchTensorKernel delta q

theorem measurable_unitTorusPeriodizedStretchTensorKernel (delta : ℝ) :
    Measurable (unitTorusPeriodizedStretchTensorKernel delta) := by
  exact (continuous_const_smul (delta : ℂ)).measurable.comp
    (measurable_unitTorusPeriodizedNormalizedStretchTensorKernel delta)

theorem integrable_unitTorusPeriodizedStretchTensorKernel
    {delta : ℝ} (hdelta : delta ∈ Icc (0 : ℝ) (1 / 2)) :
    Integrable (unitTorusPeriodizedStretchTensorKernel delta)
      frequencyPairUnitTorusMeasure := by
  change Integrable
    ((fun _ : FrequencyPairUnitTorus ↦ (delta : ℂ)) •
      unitTorusPeriodizedNormalizedStretchTensorKernel delta)
    frequencyPairUnitTorusMeasure
  apply
    (integrable_unitTorusPeriodizedNormalizedStretchTensorKernel hdelta).bdd_smul
      ‖(delta : ℂ)‖
  · exact aestronglyMeasurable_const
  · exact Filter.Eventually.of_forall fun _ ↦ le_rfl

/-- Restoring the aperture factor commutes with periodization and Fourier
coefficient extraction. -/
theorem frequencyPairUnitTorusFourierCoeff_periodizedStretchTensorKernel
    (delta : ℝ) (n : FrequencyPairWavevector) :
    frequencyPairUnitTorusFourierCoeff
        (unitTorusPeriodizedStretchTensorKernel delta) n =
      localizedStretchTensorSymbol delta
        (euclideanFrequencyPairOfWavevector n) := by
  unfold frequencyPairUnitTorusFourierCoeff
    unitTorusPeriodizedStretchTensorKernel localizedStretchTensorSymbol
  calc
    (∫ q : FrequencyPairUnitTorus,
        UnitAddTorus.mFourier (-n) q •
          ((delta : ℂ) •
            unitTorusPeriodizedNormalizedStretchTensorKernel delta q)
              ∂frequencyPairUnitTorusMeasure) =
        ∫ q : FrequencyPairUnitTorus,
          (delta : ℂ) •
            (UnitAddTorus.mFourier (-n) q •
              unitTorusPeriodizedNormalizedStretchTensorKernel delta q)
                ∂frequencyPairUnitTorusMeasure := by
      apply integral_congr_ae
      filter_upwards with q
      simp only [smul_smul]
      congr 1
      ring
    _ = (delta : ℂ) •
        ∫ q : FrequencyPairUnitTorus,
          UnitAddTorus.mFourier (-n) q •
            unitTorusPeriodizedNormalizedStretchTensorKernel delta q
              ∂frequencyPairUnitTorusMeasure := by
      rw [integral_smul]
    _ = (delta : ℂ) •
        normalizedStretchTensorSymbol explicitBufferedStretchCutoff delta
          (euclideanFrequencyPairOfWavevector n) := by
      congr 1
      exact
        frequencyPairUnitTorusFourierCoeff_periodizedNormalizedStretchTensorKernel
          delta n

/-- The actual aperture-weighted periodic kernel realizes the localized
coherent-stretching symbol on every pair of Fourier monomials. -/
theorem unitTorusPeriodizedStretch_action_monomials
    {delta : ℝ} (hdelta : delta ∈ Icc (0 : ℝ) (1 / 2))
    (k l : Fin 3 → ℤ) (u v : ComplexVec3) (x : BilinearSpatialTorus) :
    torusBilinearKernelAction
        (unitTorusPeriodizedStretchTensorKernel delta)
        (fun z ↦ UnitAddTorus.mFourier k z • u)
        (fun z ↦ UnitAddTorus.mFourier l z • v) x =
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
        applyCoherentBilinearOperator
          (localizedStretchTensorSymbol delta
            (euclideanFrequencyPairOfWavevector (pairWavevector k l))) u v := by
  rw [torusBilinearKernelAction_monomials _
    (integrable_unitTorusPeriodizedStretchTensorKernel hdelta)]
  rw [frequencyPairUnitTorusFourierCoeff_periodizedStretchTensorKernel]

/-- Periodic bilinear endpoint Young inequality.  The tensor sup norm costs
the explicit finite-dimensional factor `3 * 3 = 9`, and both inputs remain at
the `L∞` endpoint. -/
theorem norm_torusBilinearKernelAction_le
    (K : FrequencyPairUnitTorus → CoherentBilinearOperator)
    (f g : BilinearSpatialTorus → ComplexVec3)
    (x : BilinearSpatialTorus) (M N : ℝ)
    (hKint : Integrable K frequencyPairUnitTorusMeasure)
    (hKmeas : Measurable K) (hf : Continuous f) (hg : Continuous g)
    (hfb : ∀ y, ‖f y‖ ≤ M) (hgb : ∀ y, ‖g y‖ ≤ N) :
    ‖torusBilinearKernelAction K f g x‖ ≤
      9 * (∫ q, ‖K q‖ ∂frequencyPairUnitTorusMeasure) * M * N := by
  have hM : 0 ≤ M := (norm_nonneg (f x)).trans (hfb x)
  have hN : 0 ≤ N := (norm_nonneg (g x)).trans (hgb x)
  have hmeas : Measurable (fun q : FrequencyPairUnitTorus ↦
      applyCoherentBilinearOperator (K q)
        (f (x - firstTorusDisplacement q))
        (g (x - secondTorusDisplacement q))) := by
    unfold applyCoherentBilinearOperator
    fun_prop
  have hdom : Integrable
      (fun q : FrequencyPairUnitTorus ↦ 9 * ‖K q‖ * M * N)
      frequencyPairUnitTorusMeasure :=
    (hKint.norm.const_mul 9).mul_const M |>.mul_const N
  have hpoint : ∀ q : FrequencyPairUnitTorus,
      ‖applyCoherentBilinearOperator (K q)
          (f (x - firstTorusDisplacement q))
          (g (x - secondTorusDisplacement q))‖ ≤
        9 * ‖K q‖ * M * N := by
    intro q
    refine (norm_applyCoherentBilinearOperator_le (K q) _ _).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hfb _)
        (mul_nonneg (by norm_num) (norm_nonneg (K q))))
      (hgb _) (norm_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg (K q))) hM)
  have hint : Integrable (fun q : FrequencyPairUnitTorus ↦
      applyCoherentBilinearOperator (K q)
        (f (x - firstTorusDisplacement q))
        (g (x - secondTorusDisplacement q)))
      frequencyPairUnitTorusMeasure := by
    exact hdom.mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  unfold torusBilinearKernelAction
  calc
    ‖∫ q : FrequencyPairUnitTorus,
        applyCoherentBilinearOperator (K q)
          (f (x - firstTorusDisplacement q))
          (g (x - secondTorusDisplacement q))
            ∂frequencyPairUnitTorusMeasure‖ ≤
        ∫ q : FrequencyPairUnitTorus,
          ‖applyCoherentBilinearOperator (K q)
            (f (x - firstTorusDisplacement q))
            (g (x - secondTorusDisplacement q))‖
              ∂frequencyPairUnitTorusMeasure :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ q : FrequencyPairUnitTorus, 9 * ‖K q‖ * M * N
          ∂frequencyPairUnitTorusMeasure :=
      integral_mono hint.norm hdom hpoint
    _ = 9 * (∫ q : FrequencyPairUnitTorus,
          ‖K q‖ ∂frequencyPairUnitTorusMeasure) * M * N := by
      rw [integral_mul_const, integral_mul_const, integral_const_mul]

/-- **Uniform periodic coherent endpoint bound.**  One aperture-independent
constant controls the normalized coherent bilinear kernel action on the
physical three-torus. -/
theorem exists_uniform_unitTorusNormalizedStretch_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        ∀ (f g : BilinearSpatialTorus → ComplexVec3)
          (x : BilinearSpatialTorus) (M N : ℝ),
          Continuous f → Continuous g →
          (∀ y, ‖f y‖ ≤ M) → (∀ y, ‖g y‖ ≤ N) →
          ‖torusBilinearKernelAction
              (unitTorusPeriodizedNormalizedStretchTensorKernel delta)
              f g x‖ ≤ 9 * C * M * N := by
  rcases
      exists_uniform_unitTorusPeriodizedNormalizedStretchTensorKernel_integral_norm with
    ⟨C, hC, hkernel⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta f g x M N hf hg hfb hgb
  rcases hkernel delta hdelta with ⟨hKint, hmass⟩
  have hyoung := norm_torusBilinearKernelAction_le
    (unitTorusPeriodizedNormalizedStretchTensorKernel delta)
    f g x M N hKint
    (measurable_unitTorusPeriodizedNormalizedStretchTensorKernel delta)
    hf hg hfb hgb
  have hM : 0 ≤ M := (norm_nonneg (f x)).trans (hfb x)
  have hN : 0 ≤ N := (norm_nonneg (g x)).trans (hgb x)
  exact hyoung.trans (by
    gcongr)

/-- **Frequency-uniform coherent aperture gain on the periodic domain.**
After restoring the exact factor extracted from the coherent stretching
symbol, the bilinear `L∞ × L∞ → L∞` operator norm is `O(delta)` with one
constant valid for every aperture in `[0, 1/2]`. -/
theorem exists_uniform_unitTorusStretch_bilinear_aperture_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        ∀ (f g : BilinearSpatialTorus → ComplexVec3)
          (x : BilinearSpatialTorus) (M N : ℝ),
          Continuous f → Continuous g →
          (∀ y, ‖f y‖ ≤ M) → (∀ y, ‖g y‖ ≤ N) →
          ‖torusBilinearKernelAction
              (unitTorusPeriodizedStretchTensorKernel delta) f g x‖ ≤
            9 * delta * C * M * N := by
  rcases
      exists_uniform_unitTorusPeriodizedNormalizedStretchTensorKernel_integral_norm with
    ⟨C, hC, hkernel⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta f g x M N hf hg hfb hgb
  rcases hkernel delta hdelta with ⟨_hKintNormalized, hmass⟩
  have hmassActual :
      (∫ q : FrequencyPairUnitTorus,
          ‖unitTorusPeriodizedStretchTensorKernel delta q‖
            ∂frequencyPairUnitTorusMeasure) =
        delta *
          ∫ q : FrequencyPairUnitTorus,
            ‖unitTorusPeriodizedNormalizedStretchTensorKernel delta q‖
              ∂frequencyPairUnitTorusMeasure := by
    unfold unitTorusPeriodizedStretchTensorKernel
    simp_rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hdelta.1]
    rw [integral_const_mul]
  have hmassActual_le :
      (∫ q : FrequencyPairUnitTorus,
          ‖unitTorusPeriodizedStretchTensorKernel delta q‖
            ∂frequencyPairUnitTorusMeasure) ≤ delta * C := by
    rw [hmassActual]
    exact mul_le_mul_of_nonneg_left hmass hdelta.1
  have hyoung := norm_torusBilinearKernelAction_le
    (unitTorusPeriodizedStretchTensorKernel delta)
    f g x M N
    (integrable_unitTorusPeriodizedStretchTensorKernel hdelta)
    (measurable_unitTorusPeriodizedStretchTensorKernel delta)
    hf hg hfb hgb
  have hM : 0 ≤ M := (norm_nonneg (f x)).trans (hfb x)
  have hN : 0 ≤ N := (norm_nonneg (g x)).trans (hgb x)
  calc
    ‖torusBilinearKernelAction
        (unitTorusPeriodizedStretchTensorKernel delta) f g x‖ ≤
        9 * (∫ q : FrequencyPairUnitTorus,
          ‖unitTorusPeriodizedStretchTensorKernel delta q‖
            ∂frequencyPairUnitTorusMeasure) * M * N := hyoung
    _ ≤ 9 * (delta * C) * M * N := by
      gcongr
    _ = 9 * delta * C * M * N := by ring

end PancakeBilinearPeriodization
end NavierStokes
end FluidDynamics
end Mettapedia
