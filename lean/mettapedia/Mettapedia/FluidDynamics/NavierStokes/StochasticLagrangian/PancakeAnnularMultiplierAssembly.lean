import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAnnularUniformKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteFourierBilinearTransfer

/-!
# Assembly of the four annular coherent-stretching multipliers

The four signed cutoffs are not four alternative choices.  Their sum is one
fixed multiplier.  On the normalized pancake annulus their inner cutoffs form
an exact partition, so the assembled multiplier is exactly the uncut coherent
projection interaction.  Off the annulus it remains a genuine Schwartz
multiplier with aperture-uniform inverse-Fourier mass.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeAnnularMultiplierAssembly

open MeasureTheory
open Set
open PeriodicFourierTriad
open PancakeBilinearKernelScaling
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentSymbol
open PancakeRealCoherentPairEstimate
open PancakeSmoothCoherentStretchSymbol
open PancakeFiniteFourierBilinearTransfer
open PancakeUniformKernelFamily
open PancakeAnnularChartCutoff
open PancakeAnnularUniformKernel
open scoped FourierTransform SchwartzMap

/-- Coherent-projected normalized stretching without a cutoff factor. -/
def coherentProjectedNormalizedStretch
    (delta : ℝ) (p : FrequencyPair) (u v : ComplexVec3) : ComplexVec3 :=
  (complexCoherentChartCoeff (receiverFrequency delta p) v *
      complexCoherentChartCoeff (sourceFrequency delta p) u) •
    realVec3ToComplexVec3 (normalizedStretch delta p)

/-- The assembled four-chart Schwartz symbol. -/
def annularFourChartTensorSymbol (delta : ℝ) :
    𝓢(EuclideanFrequencyPair, CoherentBilinearOperator) :=
  normalizedStretchTensorSymbol
      (annularBufferedStretchCutoff .positive .positive) delta +
    normalizedStretchTensorSymbol
      (annularBufferedStretchCutoff .positive .negative) delta +
    normalizedStretchTensorSymbol
      (annularBufferedStretchCutoff .negative .positive) delta +
    normalizedStretchTensorSymbol
      (annularBufferedStretchCutoff .negative .negative) delta

/-- The assembled inverse-Fourier kernel. -/
def annularFourChartTensorKernel (delta : ℝ) :
    𝓢(EuclideanFrequencyPair, CoherentBilinearOperator) :=
  normalizedStretchTensorKernel
      (annularBufferedStretchCutoff .positive .positive) delta +
    normalizedStretchTensorKernel
      (annularBufferedStretchCutoff .positive .negative) delta +
    normalizedStretchTensorKernel
      (annularBufferedStretchCutoff .negative .positive) delta +
    normalizedStretchTensorKernel
      (annularBufferedStretchCutoff .negative .negative) delta

theorem fourier_annularFourChartTensorKernel (delta : ℝ) :
    𝓕 (annularFourChartTensorKernel delta) =
      annularFourChartTensorSymbol delta := by
  simp [annularFourChartTensorKernel, annularFourChartTensorSymbol,
    fourier_normalizedStretchTensorKernel]

/-- Tensor evaluation is additive in the multiplier tensor. -/
theorem applyCoherentBilinearOperator_add_tensor
    (A B : CoherentBilinearOperator) (u v : ComplexVec3) :
    applyCoherentBilinearOperator (A + B) u v =
      applyCoherentBilinearOperator A u v +
        applyCoherentBilinearOperator B u v := by
  simpa only [applyCoherentBilinearOperatorCLM_apply] using
    (applyCoherentBilinearOperatorCLM u v).map_add A B

/-- The normalized tensor of any buffered cutoff globally equals its
cutoff-localized coherent projection. -/
theorem apply_normalizedStretchTensorSymbol_eq_localized
    (D : BufferedStretchCutoff) (delta : ℝ) (xi : EuclideanFrequencyPair)
    (u v : ComplexVec3) :
    applyCoherentBilinearOperator
        (normalizedStretchTensorSymbol D delta xi) u v =
      localizedCoherentProjectedNormalizedStretch D delta
        (euclideanToFrequencyPairEquiv xi) u v := by
  by_cases hinner : D.inner (euclideanToFrequencyPairEquiv xi) = 0
  · have hsymbol : normalizedStretchTensorSymbol D delta xi = 0 := by
      ext i j l
      rw [normalizedStretchTensorSymbol_apply_entry]
      simp [localizedNormalizedStretchEntry, hinner]
    rw [hsymbol]
    have happlyZero :
        applyCoherentBilinearOperator (0 : CoherentBilinearOperator) u v = 0 := by
      ext i
      simp [applyCoherentBilinearOperator]
    rw [happlyZero]
    simp [localizedCoherentProjectedNormalizedStretch, hinner]
  · exact apply_normalizedStretchTensorSymbol_eq_localizedCoherentProjection
      D delta xi u v hinner

/-- **Exact annular multiplier identification.**  On the full normalized
pancake annulus, the assembled four-chart multiplier is the uncut coherent
Biot--Savart stretching interaction. -/
theorem apply_annularFourChartTensorSymbol_eq_coherent
    (delta : ℝ) (xi : EuclideanFrequencyPair) (u v : ComplexVec3)
    (hsource : InNormalizedPancakeAnnulus
      (euclideanToFrequencyPairEquiv xi).1)
    (hreceiver : InNormalizedPancakeAnnulus
      (euclideanToFrequencyPairEquiv xi).2) :
    applyCoherentBilinearOperator
        (annularFourChartTensorSymbol delta xi) u v =
      coherentProjectedNormalizedStretch delta
        (euclideanToFrequencyPairEquiv xi) u v := by
  let p := euclideanToFrequencyPairEquiv xi
  have hpartition : annularFourChartInner p = 1 :=
    annularFourChartInner_eq_one_of_mem_normalizedAnnulus hsource hreceiver
  rw [annularFourChartTensorSymbol]
  change applyCoherentBilinearOperator
      (normalizedStretchTensorSymbol
          (annularBufferedStretchCutoff .positive .positive) delta xi +
        normalizedStretchTensorSymbol
          (annularBufferedStretchCutoff .positive .negative) delta xi +
        normalizedStretchTensorSymbol
          (annularBufferedStretchCutoff .negative .positive) delta xi +
        normalizedStretchTensorSymbol
          (annularBufferedStretchCutoff .negative .negative) delta xi) u v = _
  rw [applyCoherentBilinearOperator_add_tensor,
    applyCoherentBilinearOperator_add_tensor,
    applyCoherentBilinearOperator_add_tensor]
  rw [apply_normalizedStretchTensorSymbol_eq_localized,
    apply_normalizedStretchTensorSymbol_eq_localized,
    apply_normalizedStretchTensorSymbol_eq_localized,
    apply_normalizedStretchTensorSymbol_eq_localized]
  ext i
  simp only [localizedCoherentProjectedNormalizedStretch,
    coherentProjectedNormalizedStretch, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  change
    (((annularStretchInner .positive .positive p : ℝ) : ℂ) *
          complexCoherentChartCoeff (receiverFrequency delta p) v *
          complexCoherentChartCoeff (sourceFrequency delta p) u) *
          realVec3ToComplexVec3 (normalizedStretch delta p) i +
      (((annularStretchInner .positive .negative p : ℝ) : ℂ) *
          complexCoherentChartCoeff (receiverFrequency delta p) v *
          complexCoherentChartCoeff (sourceFrequency delta p) u) *
          realVec3ToComplexVec3 (normalizedStretch delta p) i +
      (((annularStretchInner .negative .positive p : ℝ) : ℂ) *
          complexCoherentChartCoeff (receiverFrequency delta p) v *
          complexCoherentChartCoeff (sourceFrequency delta p) u) *
          realVec3ToComplexVec3 (normalizedStretch delta p) i +
      (((annularStretchInner .negative .negative p : ℝ) : ℂ) *
          complexCoherentChartCoeff (receiverFrequency delta p) v *
          complexCoherentChartCoeff (sourceFrequency delta p) u) *
          realVec3ToComplexVec3 (normalizedStretch delta p) i =
      (complexCoherentChartCoeff (receiverFrequency delta p) v *
          complexCoherentChartCoeff (sourceFrequency delta p) u) *
          realVec3ToComplexVec3 (normalizedStretch delta p) i
  have hpartitionComplex :
      (((annularStretchInner .positive .positive p +
        annularStretchInner .positive .negative p +
        annularStretchInner .negative .positive p +
        annularStretchInner .negative .negative p : ℝ) : ℂ)) = 1 := by
    simpa [annularFourChartInner] using congrArg Complex.ofReal hpartition
  calc
    _ = (((annularStretchInner .positive .positive p +
          annularStretchInner .positive .negative p +
          annularStretchInner .negative .positive p +
          annularStretchInner .negative .negative p : ℝ) : ℂ) *
        complexCoherentChartCoeff (receiverFrequency delta p) v *
        complexCoherentChartCoeff (sourceFrequency delta p) u) *
        realVec3ToComplexVec3 (normalizedStretch delta p) i := by
      push_cast
      ring
    _ = _ := by rw [hpartitionComplex]; ring

/-- The sum of the four inverse kernels has one aperture-uniform `L¹` mass
bound. -/
theorem exists_uniform_annularFourChartTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
      (∫ x : EuclideanFrequencyPair,
        ‖annularFourChartTensorKernel delta x‖) ≤ C := by
  rcases exists_uniform_annularTensorKernel_mass with ⟨C, hC, hmass⟩
  refine ⟨4 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro delta hdelta
  let Kpp := normalizedStretchTensorKernel
    (annularBufferedStretchCutoff .positive .positive) delta
  let Kpn := normalizedStretchTensorKernel
    (annularBufferedStretchCutoff .positive .negative) delta
  let Knp := normalizedStretchTensorKernel
    (annularBufferedStretchCutoff .negative .positive) delta
  let Knn := normalizedStretchTensorKernel
    (annularBufferedStretchCutoff .negative .negative) delta
  have hpp : Integrable (fun x : EuclideanFrequencyPair ↦ ‖Kpp x‖) := Kpp.integrable.norm
  have hpn : Integrable (fun x : EuclideanFrequencyPair ↦ ‖Kpn x‖) := Kpn.integrable.norm
  have hnp : Integrable (fun x : EuclideanFrequencyPair ↦ ‖Knp x‖) := Knp.integrable.norm
  have hnn : Integrable (fun x : EuclideanFrequencyPair ↦ ‖Knn x‖) := Knn.integrable.norm
  have hsum : Integrable (fun x : EuclideanFrequencyPair ↦
      ‖Kpp x‖ + ‖Kpn x‖ + ‖Knp x‖ + ‖Knn x‖) :=
    ((hpp.add hpn).add hnp).add hnn
  calc
    (∫ x : EuclideanFrequencyPair,
      ‖annularFourChartTensorKernel delta x‖) ≤
        ∫ x : EuclideanFrequencyPair,
          (‖Kpp x‖ + ‖Kpn x‖ + ‖Knp x‖ + ‖Knn x‖) := by
      apply integral_mono
        (annularFourChartTensorKernel delta).integrable.norm hsum
      intro x
      change ‖Kpp x + Kpn x + Knp x + Knn x‖ ≤ _
      calc
        _ ≤ ‖Kpp x + Kpn x + Knp x‖ + ‖Knn x‖ := norm_add_le _ _
        _ ≤ (‖Kpp x + Kpn x‖ + ‖Knp x‖) + ‖Knn x‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ (‖Kpp x‖ + ‖Kpn x‖) + ‖Knp x‖ + ‖Knn x‖ := by
          gcongr
          exact norm_add_le _ _
    _ = (∫ x, ‖Kpp x‖ + ‖Kpn x‖ + ‖Knp x‖) +
        (∫ x, ‖Knn x‖) := by
      exact integral_add ((hpp.add hpn).add hnp) hnn
    _ = ((∫ x, ‖Kpp x‖ + ‖Kpn x‖) + (∫ x, ‖Knp x‖)) +
        (∫ x, ‖Knn x‖) := by
      congr 1
      exact integral_add (hpp.add hpn) hnp
    _ = (((∫ x, ‖Kpp x‖) + (∫ x, ‖Kpn x‖)) +
        (∫ x, ‖Knp x‖)) + (∫ x, ‖Knn x‖) := by
      rw [integral_add hpp hpn]
    _ ≤ C + C + C + C := by
      gcongr
      · exact hmass .positive .positive delta hdelta
      · exact hmass .positive .negative delta hdelta
      · exact hmass .negative .positive delta hdelta
      · exact hmass .negative .negative delta hdelta
    _ = 4 * C := by ring

end PancakeAnnularMultiplierAssembly
end NavierStokes
end FluidDynamics
end Mettapedia
