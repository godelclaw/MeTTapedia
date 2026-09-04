import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBilinearPeriodization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicCoherentSplit

/-!
# Finite Fourier realization of the coherent bilinear kernel

The periodized six-dimensional kernel is already known to act through the
localized coherent-stretching symbol on one pair of Fourier monomials.  This
module proves the corresponding exact identity for arbitrary finite Fourier
fields.  In particular, summing modes introduces no cardinality factor: the
whole trigonometric polynomial is still controlled by the periodic bilinear
endpoint estimate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeFiniteFourierBilinearTransfer

open MeasureTheory
open Set
open PeriodicFourierTriad
open PancakeBilinearKernelScaling
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentSymbol
open PancakeSmoothCoherentStretchSymbol
open PancakeRealCoherentPairEstimate
open scoped BigOperators

/-! ## Identification of the assembled tensor symbol -/

/-- Evaluation of the assembled tensor at one output/source/receiver entry
recovers the scalar localized symbol used to build it. -/
theorem normalizedStretchTensorSymbol_apply_entry
    (D : BufferedStretchCutoff) (delta : ℝ) (xi : EuclideanFrequencyPair)
    (i j l : Fin 3) :
    normalizedStretchTensorSymbol D delta xi i j l =
      localizedNormalizedStretchEntry D delta i j l
        (euclideanToFrequencyPairEquiv xi) := by
  classical
  simp +contextual [normalizedStretchTensorSymbol, elementaryBilinearTensor,
    scalarMultipleBilinearTensorCLM, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp +contextual [Pi.single_apply]
    rw [Finset.sum_eq_single j]
    · simp +contextual [Pi.single_apply]
    · intro c hc hcj
      rw [if_neg (Ne.symm hcj)]
      rfl
    · simp
  · intro c hc hci
    rw [if_neg (Ne.symm hci)]
    rfl
  · simp

/-- Coordinatewise complexification of an algebraic real three-vector. -/
def realVec3ToComplexVec3 (w : RealVec3) : ComplexVec3 :=
  ![(w.1 : ℂ), (w.2.1 : ℂ), (w.2.2 : ℂ)]

@[simp]
theorem realVec3ToComplexVec3_apply (w : RealVec3) (i : Fin 3) :
    realVec3ToComplexVec3 w i = (coordinate w i : ℂ) := by
  fin_cases i <;> rfl

/-- Complex-linear coefficient of a vector along the real coherent line in a
fixed frequency chart. -/
def complexCoherentChartCoeff (k : RealVec3) (u : ComplexVec3) : ℂ :=
  ∑ j : Fin 3,
    (coordinate (coherentW k) j / normSq (coherentW k) : ℂ) * u j

/-- The complexified normalized coherent projection of two amplitudes in one
source/receiver frequency chart, including its retained cutoff. -/
def localizedCoherentProjectedNormalizedStretch
    (D : BufferedStretchCutoff) (delta : ℝ) (p : FrequencyPair)
    (u v : ComplexVec3) : ComplexVec3 :=
  ((D.inner p : ℂ) *
      complexCoherentChartCoeff (receiverFrequency delta p) v *
      complexCoherentChartCoeff (sourceFrequency delta p) u) •
    realVec3ToComplexVec3 (normalizedStretch delta p)

/-- **Inner-chart PDE identification.**  On the retained chart, applying the
assembled normalized tensor is exactly the complex-bilinear extension of the
coherent-projected normalized Biot--Savart stretching interaction. -/
theorem apply_normalizedStretchTensorSymbol_eq_localizedCoherentProjection
    (D : BufferedStretchCutoff) (delta : ℝ) (xi : EuclideanFrequencyPair)
    (u v : ComplexVec3)
    (hxi : D.inner (euclideanToFrequencyPairEquiv xi) ≠ 0) :
    applyCoherentBilinearOperator
        (normalizedStretchTensorSymbol D delta xi) u v =
      localizedCoherentProjectedNormalizedStretch D delta
        (euclideanToFrequencyPairEquiv xi) u v := by
  ext i
  simp only [applyCoherentBilinearOperator,
    normalizedStretchTensorSymbol_apply_entry,
    localizedCoherentProjectedNormalizedStretch, Pi.smul_apply,
    realVec3ToComplexVec3_apply, smul_eq_mul]
  simp_rw [localizedNormalizedStretchEntry_eq_on_inner D delta _ _ _
    (euclideanToFrequencyPairEquiv xi) hxi]
  unfold complexCoherentChartCoeff
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro l _hl
  ring

/-- The localized tensor symbol is globally the retained coherent-projection
interaction: off the inner cutoff both sides vanish, while on it the buffer
is exactly one. -/
theorem apply_localizedStretchTensorSymbol_eq_delta_localizedCoherentProjection
    (delta : ℝ) (xi : EuclideanFrequencyPair) (u v : ComplexVec3) :
    applyCoherentBilinearOperator (localizedStretchTensorSymbol delta xi) u v =
      (delta : ℂ) •
        localizedCoherentProjectedNormalizedStretch
          explicitBufferedStretchCutoff delta
          (euclideanToFrequencyPairEquiv xi) u v := by
  by_cases hinner :
      explicitBufferedStretchCutoff.inner
        (euclideanToFrequencyPairEquiv xi) = 0
  · have hsymbol :
        normalizedStretchTensorSymbol explicitBufferedStretchCutoff delta xi = 0 := by
      ext i j l
      rw [normalizedStretchTensorSymbol_apply_entry]
      simp [localizedNormalizedStretchEntry, hinner]
    rw [localizedStretchTensorSymbol,
      applyCoherentBilinearOperator_smul_tensor, hsymbol]
    have happlyZero :
        applyCoherentBilinearOperator (0 : CoherentBilinearOperator) u v = 0 := by
      ext i
      simp [applyCoherentBilinearOperator]
    rw [happlyZero]
    simp [localizedCoherentProjectedNormalizedStretch, hinner]
  · rw [localizedStretchTensorSymbol,
      applyCoherentBilinearOperator_smul_tensor,
      apply_normalizedStretchTensorSymbol_eq_localizedCoherentProjection
        explicitBufferedStretchCutoff delta xi u v hinner]

/-- Tensor evaluation is additive in its first vector input. -/
theorem applyCoherentBilinearOperator_add_left
    (A : CoherentBilinearOperator) (u₁ u₂ v : ComplexVec3) :
    applyCoherentBilinearOperator A (u₁ + u₂) v =
      applyCoherentBilinearOperator A u₁ v +
        applyCoherentBilinearOperator A u₂ v := by
  ext i
  simp only [applyCoherentBilinearOperator, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _hl
  ring

/-- Tensor evaluation is additive in its second vector input. -/
theorem applyCoherentBilinearOperator_add_right
    (A : CoherentBilinearOperator) (u v₁ v₂ : ComplexVec3) :
    applyCoherentBilinearOperator A u (v₁ + v₂) =
      applyCoherentBilinearOperator A u v₁ +
        applyCoherentBilinearOperator A u v₂ := by
  ext i
  simp only [applyCoherentBilinearOperator, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _hl
  ring

@[simp]
theorem applyCoherentBilinearOperator_zero_left
    (A : CoherentBilinearOperator) (v : ComplexVec3) :
    applyCoherentBilinearOperator A 0 v = 0 := by
  ext i
  simp [applyCoherentBilinearOperator]

@[simp]
theorem applyCoherentBilinearOperator_zero_right
    (A : CoherentBilinearOperator) (u : ComplexVec3) :
    applyCoherentBilinearOperator A u 0 = 0 := by
  ext i
  simp [applyCoherentBilinearOperator]

/-- Tensor evaluation distributes over a finite sum in the first input. -/
theorem applyCoherentBilinearOperator_finset_sum_left
    {I : Type*} (A : CoherentBilinearOperator) (s : Finset I)
    (u : I → ComplexVec3) (v : ComplexVec3) :
    applyCoherentBilinearOperator A (∑ i ∈ s, u i) v =
      ∑ i ∈ s, applyCoherentBilinearOperator A (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, applyCoherentBilinearOperator_add_left, ih,
        Finset.sum_insert hi]

/-- Tensor evaluation distributes over a finite sum in the second input. -/
theorem applyCoherentBilinearOperator_finset_sum_right
    {I : Type*} (A : CoherentBilinearOperator) (u : ComplexVec3)
    (s : Finset I) (v : I → ComplexVec3) :
    applyCoherentBilinearOperator A u (∑ i ∈ s, v i) =
      ∑ i ∈ s, applyCoherentBilinearOperator A u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, applyCoherentBilinearOperator_add_right, ih,
        Finset.sum_insert hi]

/-- The kernel integrand for a pair of Fourier monomials is integrable
whenever the tensor kernel is integrable. -/
theorem integrable_torusBilinearKernelAction_monomial_integrand
    (K : FrequencyPairUnitTorus → CoherentBilinearOperator)
    (hKint : Integrable K frequencyPairUnitTorusMeasure)
    (k l : Wavevector) (u v : ComplexVec3) (x : BilinearSpatialTorus) :
    Integrable
      (fun q : FrequencyPairUnitTorus ↦
        applyCoherentBilinearOperator (K q)
          (UnitAddTorus.mFourier k (x - firstTorusDisplacement q) • u)
          (UnitAddTorus.mFourier l (x - secondTorusDisplacement q) • v))
      frequencyPairUnitTorusMeasure := by
  let n : FrequencyPairWavevector := pairWavevector k l
  let c : ℂ := UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x
  let weighted : FrequencyPairUnitTorus → CoherentBilinearOperator :=
    fun q ↦ UnitAddTorus.mFourier (-n) q • K q
  have hweighted : Integrable weighted frequencyPairUnitTorusMeasure := by
    change Integrable
      ((fun q : FrequencyPairUnitTorus ↦
        UnitAddTorus.mFourier (-n) q) • K)
      frequencyPairUnitTorusMeasure
    apply hKint.bdd_smul 1
    · exact (UnitAddTorus.mFourier (-n)).continuous.aestronglyMeasurable
    · filter_upwards with q
      simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
        fourier_apply, Circle.norm_coe, Finset.prod_const_one, le_rfl]
  let L := applyCoherentBilinearOperatorCLM u v
  have hLweighted : Integrable (fun q ↦ L (weighted q))
      frequencyPairUnitTorusMeasure := by
    have hdom := hweighted.norm.const_mul ‖L‖
    apply hdom.mono'
      (L.continuous.comp_aestronglyMeasurable hweighted.aestronglyMeasurable)
    filter_upwards with q
    exact L.le_opNorm (weighted q)
  have hscaled : Integrable (fun q ↦ c • L (weighted q))
      frequencyPairUnitTorusMeasure := by
    change Integrable ((fun _ : FrequencyPairUnitTorus ↦ c) •
      fun q ↦ L (weighted q)) frequencyPairUnitTorusMeasure
    apply hLweighted.bdd_smul ‖c‖ aestronglyMeasurable_const
    exact Filter.Eventually.of_forall fun _ ↦ le_rfl
  apply hscaled.congr
  filter_upwards with q
  symm
  rw [mFourier_sub_apply_spatial, mFourier_sub_apply_spatial,
    applyCoherentBilinearOperator_smul_smul]
  change _ = c • applyCoherentBilinearOperator (weighted q) u v
  rw [show weighted q = UnitAddTorus.mFourier (-n) q • K q by rfl,
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
  simp only [c]
  ring

/-- Exact expansion of the integrand for two finite Fourier fields into its
pairwise mode interactions. -/
theorem applyCoherentBilinearOperator_finiteFourierReconstruction
    (A : CoherentBilinearOperator) (s t : Finset Wavevector)
    (omega eta : FourierVelocity) (y z : BilinearSpatialTorus) :
    applyCoherentBilinearOperator A
        (finiteFourierReconstruction s omega y)
        (finiteFourierReconstruction t eta z) =
      ∑ k ∈ s, ∑ l ∈ t,
        applyCoherentBilinearOperator A
          (UnitAddTorus.mFourier k y • omega k)
          (UnitAddTorus.mFourier l z • eta l) := by
  unfold finiteFourierReconstruction
  rw [applyCoherentBilinearOperator_finset_sum_left]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [applyCoherentBilinearOperator_finset_sum_right]

/-- **Finite Fourier bilinear multiplier formula.**  A periodic tensor kernel
acts on arbitrary finite Fourier reconstructions by the expected double sum
of its genuine six-dimensional Fourier coefficients. -/
theorem torusBilinearKernelAction_finiteFourierReconstruction
    (K : FrequencyPairUnitTorus → CoherentBilinearOperator)
    (hKint : Integrable K frequencyPairUnitTorusMeasure)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    torusBilinearKernelAction K
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      ∑ k ∈ s, ∑ l ∈ t,
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          applyCoherentBilinearOperator
            (frequencyPairUnitTorusFourierCoeff K (pairWavevector k l))
            (omega k) (eta l) := by
  unfold torusBilinearKernelAction
  rw [show
      (fun q : FrequencyPairUnitTorus ↦
        applyCoherentBilinearOperator (K q)
          (finiteFourierReconstruction s omega
            (x - firstTorusDisplacement q))
          (finiteFourierReconstruction t eta
            (x - secondTorusDisplacement q))) =
        (fun q : FrequencyPairUnitTorus ↦
          ∑ k ∈ s, ∑ l ∈ t,
            applyCoherentBilinearOperator (K q)
              (UnitAddTorus.mFourier k
                (x - firstTorusDisplacement q) • omega k)
              (UnitAddTorus.mFourier l
                (x - secondTorusDisplacement q) • eta l)) by
      funext q
      exact applyCoherentBilinearOperator_finiteFourierReconstruction
        (K q) s t omega eta _ _]
  rw [integral_finsetSum s]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_finsetSum t]
    · apply Finset.sum_congr rfl
      intro l hl
      exact torusBilinearKernelAction_monomials K hKint k l
        (omega k) (eta l) x
    · intro l hl
      exact integrable_torusBilinearKernelAction_monomial_integrand
        K hKint k l (omega k) (eta l) x
  · intro k hk
    exact integrable_finsetSum t fun l hl ↦
      integrable_torusBilinearKernelAction_monomial_integrand
        K hKint k l (omega k) (eta l) x

/-- The aperture-weighted periodized kernel realizes the localized coherent
stretching symbol on arbitrary finite Fourier fields. -/
theorem unitTorusPeriodizedStretch_action_finiteFourierReconstruction
    {delta : ℝ} (hdelta : delta ∈ Icc (0 : ℝ) (1 / 2))
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    torusBilinearKernelAction
        (unitTorusPeriodizedStretchTensorKernel delta)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      ∑ k ∈ s, ∑ l ∈ t,
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          applyCoherentBilinearOperator
            (localizedStretchTensorSymbol delta
              (euclideanFrequencyPairOfWavevector (pairWavevector k l)))
            (omega k) (eta l) := by
  rw [torusBilinearKernelAction_finiteFourierReconstruction _
    (integrable_unitTorusPeriodizedStretchTensorKernel hdelta)]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [frequencyPairUnitTorusFourierCoeff_periodizedStretchTensorKernel]

/-- Real source/receiver chart coordinates associated with a pair of lattice
wavevectors at the base normalization. -/
def latticeFrequencyPairChart (k l : Wavevector) : FrequencyPair :=
  euclideanToFrequencyPairEquiv
    (euclideanFrequencyPairOfWavevector (pairWavevector k l))

/-- **Exact coherent-PDE finite-field formula.**  The periodized operator on
two finite Fourier fields is the double sum of the retained, coherently
projected normalized stretching interactions, with the aperture factor
visible in every term. -/
theorem unitTorusPeriodizedStretch_action_finiteFourierReconstruction_eq_coherent
    {delta : ℝ} (hdelta : delta ∈ Icc (0 : ℝ) (1 / 2))
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    torusBilinearKernelAction
        (unitTorusPeriodizedStretchTensorKernel delta)
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      ∑ k ∈ s, ∑ l ∈ t,
        (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
          ((delta : ℂ) •
            localizedCoherentProjectedNormalizedStretch
              explicitBufferedStretchCutoff delta
              (latticeFrequencyPairChart k l) (omega k) (eta l)) := by
  rw [unitTorusPeriodizedStretch_action_finiteFourierReconstruction hdelta]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [apply_localizedStretchTensorSymbol_eq_delta_localizedCoherentProjection]
  rfl

/-- **Cardinality-free finite-field aperture estimate.**  The exact finite
Fourier realization inherits the periodic `O(delta)` endpoint bound without
any factor depending on the numbers of Fourier modes. -/
theorem exists_uniform_finiteFourierStretch_bilinear_aperture_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        ∀ (s t : Finset Wavevector) (omega eta : FourierVelocity)
          (x : BilinearSpatialTorus) (M N : ℝ),
          (∀ y, ‖finiteFourierReconstruction s omega y‖ ≤ M) →
          (∀ y, ‖finiteFourierReconstruction t eta y‖ ≤ N) →
          ‖torusBilinearKernelAction
              (unitTorusPeriodizedStretchTensorKernel delta)
              (finiteFourierReconstruction s omega)
              (finiteFourierReconstruction t eta) x‖ ≤
            9 * delta * C * M * N := by
  rcases exists_uniform_unitTorusStretch_bilinear_aperture_bound with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta s t omega eta x M N homega heta
  exact hbound delta hdelta
    (finiteFourierReconstruction s omega)
    (finiteFourierReconstruction t eta) x M N
    (continuous_finiteFourierReconstruction s omega)
    (continuous_finiteFourierReconstruction t eta) homega heta

end PancakeFiniteFourierBilinearTransfer
end NavierStokes
end FluidDynamics
end Mettapedia
