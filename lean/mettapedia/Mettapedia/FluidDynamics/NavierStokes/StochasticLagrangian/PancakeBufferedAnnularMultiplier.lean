import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAnnularMultiplierAssembly
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteFourierLocalization

/-!
# A localization-stable annular multiplier

Multiplication by a physical cutoff shifts Fourier modes.  For cutoff modes in
the normalized box with transverse margin `1/4` and axial margin `1/8`, the
original pancake annulus therefore thickens to transverse radius `9/4` and
axial magnitudes in `[5/8, 17/8]`.

This module enlarges the retained axial gates just enough to cover that box,
while keeping the existing outer buffers.  Consequently the four enlarged
charts still define valid buffered stretch cutoffs, form an exact partition on
the thickened annulus, and inherit an aperture-uniform inverse-Fourier `L¹`
bound from the generic cutoff theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeBufferedAnnularMultiplier

open MeasureTheory
open Set
open PeriodicFourierTriad
open PancakeBilinearKernelScaling
open PancakePeriodicCoherentSplit
open PancakeRealCoherentPairEstimate
open PancakeSmoothCoherentSymbol
open PancakeSmoothCoherentStretchSymbol
open PancakeFiniteFourierBilinearTransfer
open PancakeAnnularChartCutoff
open PancakeAnnularUniformKernel
open PancakeAnnularMultiplierAssembly
open PancakeFiniteFourierLocalization
open scoped ContDiff FourierTransform SchwartzMap

/-- The fixed transverse frequency margin used for physical localization. -/
def localizationTransverseMargin : ℝ := 1 / 4

/-- The fixed axial frequency margin used for physical localization. -/
def localizationAxialMargin : ℝ := 1 / 8

/-- The annulus enlarged by the fixed localization-frequency box. -/
def InLocalizationBufferedPancakeAnnulus (v : RealVec3) : Prop :=
  InExpandedNormalizedPancakeAnnulus
    localizationTransverseMargin localizationAxialMargin v

/-- The retained signed axial gate enlarged from radius `3/4` to `7/8`.
Its support is unchanged at radius `1`, so the old outer gate is still one on
its support. -/
def localizationAnnularAxialInnerBump (sign : AxialSign) :
    ContDiffBump (axialChartCenter sign) :=
  ⟨7 / 8, 1, by norm_num, by norm_num⟩

/-- The retained cutoff for one source/receiver chart after localization. -/
def localizationAnnularStretchInner
    (sourceSign receiverSign : AxialSign) (p : FrequencyPair) : ℝ :=
  annularPairInnerBump sourceSign receiverSign p *
    localizationAnnularAxialInnerBump sourceSign p.1.2.2 *
    localizationAnnularAxialInnerBump receiverSign p.2.2.2

theorem contDiff_localizationAnnularStretchInner
    (sourceSign receiverSign : AxialSign) :
    ContDiff ℝ ∞ (localizationAnnularStretchInner sourceSign receiverSign) := by
  exact ((annularPairInnerBump sourceSign receiverSign).contDiff.mul
      ((localizationAnnularAxialInnerBump sourceSign).contDiff.comp
        contDiff_sourceAxial)).mul
    ((localizationAnnularAxialInnerBump receiverSign).contDiff.comp
      contDiff_receiverAxial)

theorem hasCompactSupport_localizationAnnularStretchInner
    (sourceSign receiverSign : AxialSign) :
    HasCompactSupport
      (localizationAnnularStretchInner sourceSign receiverSign) := by
  exact (annularPairInnerBump sourceSign receiverSign).hasCompactSupport.mul_right.mul_right

theorem annularAxialOuterBump_eq_one_of_localizationInner_ne_zero
    (sign : AxialSign) (z : ℝ)
    (hz : localizationAnnularAxialInnerBump sign z ≠ 0) :
    annularAxialOuterBump sign z = 1 := by
  apply (annularAxialOuterBump sign).one_of_mem_closedBall
  have hmem : z ∈ Function.support
      (localizationAnnularAxialInnerBump sign) := hz
  rw [(localizationAnnularAxialInnerBump sign).support_eq] at hmem
  change dist z (axialChartCenter sign) < 1 at hmem
  exact hmem.le

theorem annularStretchOuter_eq_one_of_localizationInner_ne_zero
    (sourceSign receiverSign : AxialSign) (p : FrequencyPair)
    (hp : localizationAnnularStretchInner sourceSign receiverSign p ≠ 0) :
    annularStretchOuter sourceSign receiverSign p = 1 := by
  have hpair : annularPairInnerBump sourceSign receiverSign p ≠ 0 := by
    intro hzero
    apply hp
    simp [localizationAnnularStretchInner, hzero]
  have hsource :
      localizationAnnularAxialInnerBump sourceSign p.1.2.2 ≠ 0 := by
    intro hzero
    apply hp
    simp [localizationAnnularStretchInner, hzero]
  have hreceiver :
      localizationAnnularAxialInnerBump receiverSign p.2.2.2 ≠ 0 := by
    intro hzero
    apply hp
    simp [localizationAnnularStretchInner, hzero]
  rw [annularStretchOuter,
    annularPairOuterBump_eq_one_of_inner_ne_zero _ _ _ hpair,
    annularAxialOuterBump_eq_one_of_localizationInner_ne_zero _ _ hsource,
    annularAxialOuterBump_eq_one_of_localizationInner_ne_zero _ _ hreceiver]
  norm_num

/-- One localization-stable signed chart.  Only the retained axial gate is
enlarged; the old outer cutoff continues to regularize both denominators. -/
def localizationBufferedStretchCutoff
    (sourceSign receiverSign : AxialSign) : BufferedStretchCutoff where
  inner := localizationAnnularStretchInner sourceSign receiverSign
  outer := annularStretchOuter sourceSign receiverSign
  inner_contDiff :=
    contDiff_localizationAnnularStretchInner sourceSign receiverSign
  outer_contDiff := contDiff_annularStretchOuter sourceSign receiverSign
  inner_compact :=
    hasCompactSupport_localizationAnnularStretchInner sourceSign receiverSign
  outer_eq_one_on_inner :=
    annularStretchOuter_eq_one_of_localizationInner_ne_zero
      sourceSign receiverSign
  source_denominator_ne := annular_source_denominator_ne sourceSign receiverSign
  receiver_denominator_ne :=
    annular_receiver_denominator_ne sourceSign receiverSign

/-! ## Exact coverage of the thickened annulus -/

theorem exists_sign_center_dist_le_of_mem_localizationBuffer
    {v : RealVec3} (hv : InLocalizationBufferedPancakeAnnulus v) :
    ∃ sign : AxialSign,
      dist v.2.2 (axialChartCenter sign) ≤ 7 / 8 := by
  change |v.1| ≤ 2 + 1 / 4 ∧ |v.2.1| ≤ 2 + 1 / 4 ∧
    3 / 4 - 1 / 8 ≤ |v.2.2| ∧ |v.2.2| ≤ 2 + 1 / 8 at hv
  norm_num at hv
  by_cases hz : 0 ≤ v.2.2
  · refine ⟨.positive, ?_⟩
    have hzlo : 5 / 8 ≤ v.2.2 := by
      simpa [abs_of_nonneg hz] using hv.2.2.1
    have hzhi : v.2.2 ≤ 17 / 8 := by
      simpa [abs_of_nonneg hz] using hv.2.2.2
    change dist v.2.2 (3 / 2) ≤ 7 / 8
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  · refine ⟨.negative, ?_⟩
    have hzneg : v.2.2 < 0 := lt_of_not_ge hz
    have hzlo : 5 / 8 ≤ -v.2.2 := by
      simpa [abs_of_neg hzneg] using hv.2.2.1
    have hzhi : -v.2.2 ≤ 17 / 8 := by
      simpa [abs_of_neg hzneg] using hv.2.2.2
    change dist v.2.2 (-(3 / 2)) ≤ 7 / 8
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith

theorem localizationAnnularAxialInnerBump_opposite_eq_zero
    (sign : AxialSign) (z : ℝ)
    (hdist : dist z (axialChartCenter sign) ≤ 7 / 8) :
    localizationAnnularAxialInnerBump sign.opposite z = 0 := by
  by_contra hne
  have hmem : z ∈ Function.support
      (localizationAnnularAxialInnerBump sign.opposite) := hne
  rw [(localizationAnnularAxialInnerBump sign.opposite).support_eq] at hmem
  have hopposite : dist z (axialChartCenter sign.opposite) < 1 := by
    simpa [localizationAnnularAxialInnerBump] using hmem
  cases sign with
  | positive =>
      have hnear : |z - 3 / 2| ≤ 7 / 8 := by
        simpa [axialChartCenter, Real.dist_eq] using hdist
      have hfar : |z - (-(3 / 2))| < 1 := by
        simpa [AxialSign.opposite, axialChartCenter, Real.dist_eq] using hopposite
      have hnearBounds := abs_le.mp hnear
      have hfarBounds := abs_lt.mp hfar
      linarith
  | negative =>
      have hnear : |z - (-(3 / 2))| ≤ 7 / 8 := by
        simpa [axialChartCenter, Real.dist_eq] using hdist
      have hfar : |z - 3 / 2| < 1 := by
        simpa [AxialSign.opposite, axialChartCenter, Real.dist_eq] using hopposite
      have hnearBounds := abs_le.mp hnear
      have hfarBounds := abs_lt.mp hfar
      linarith

/-- Explicit sum of the four localization-stable retained cutoffs. -/
def localizationFourChartInner (p : FrequencyPair) : ℝ :=
  localizationAnnularStretchInner .positive .positive p +
  localizationAnnularStretchInner .positive .negative p +
  localizationAnnularStretchInner .negative .positive p +
  localizationAnnularStretchInner .negative .negative p

/-- The enlarged four charts form an exact partition on every output mode
permitted by the fixed localization-frequency box. -/
theorem localizationFourChartInner_eq_one_of_mem_buffer
    {u v : RealVec3} (hu : InLocalizationBufferedPancakeAnnulus u)
    (hv : InLocalizationBufferedPancakeAnnulus v) :
    localizationFourChartInner (u, v) = 1 := by
  obtain ⟨sourceSign, hsourceDist⟩ :=
    exists_sign_center_dist_le_of_mem_localizationBuffer hu
  obtain ⟨receiverSign, hreceiverDist⟩ :=
    exists_sign_center_dist_le_of_mem_localizationBuffer hv
  have hsource :
      localizationAnnularAxialInnerBump sourceSign u.2.2 = 1 :=
    (localizationAnnularAxialInnerBump sourceSign).one_of_mem_closedBall
      hsourceDist
  have hsourceOpposite :
      localizationAnnularAxialInnerBump sourceSign.opposite u.2.2 = 0 :=
    localizationAnnularAxialInnerBump_opposite_eq_zero
      sourceSign u.2.2 hsourceDist
  have hreceiver :
      localizationAnnularAxialInnerBump receiverSign v.2.2 = 1 :=
    (localizationAnnularAxialInnerBump receiverSign).one_of_mem_closedBall
      hreceiverDist
  have hreceiverOpposite :
      localizationAnnularAxialInnerBump receiverSign.opposite v.2.2 = 0 :=
    localizationAnnularAxialInnerBump_opposite_eq_zero
      receiverSign v.2.2 hreceiverDist
  have hpair : annularPairInnerBump sourceSign receiverSign (u, v) = 1 := by
    apply (annularPairInnerBump sourceSign receiverSign).one_of_mem_closedBall
    change dist (u, v) (annularPairCenter sourceSign receiverSign) ≤ 9 / 4
    simp only [annularPairCenter, Prod.dist_eq, max_le_iff]
    change |u.1| ≤ 2 + 1 / 4 ∧ |u.2.1| ≤ 2 + 1 / 4 ∧
      3 / 4 - 1 / 8 ≤ |u.2.2| ∧ |u.2.2| ≤ 2 + 1 / 8 at hu
    change |v.1| ≤ 2 + 1 / 4 ∧ |v.2.1| ≤ 2 + 1 / 4 ∧
      3 / 4 - 1 / 8 ≤ |v.2.2| ∧ |v.2.2| ≤ 2 + 1 / 8 at hv
    norm_num at hu hv
    constructor
    · constructor
      · simpa [Real.dist_eq] using hu.1
      · constructor
        · simpa [Real.dist_eq] using hu.2.1
        · exact hsourceDist.trans (by norm_num)
    · constructor
      · simpa [Real.dist_eq] using hv.1
      · constructor
        · simpa [Real.dist_eq] using hv.2.1
        · exact hreceiverDist.trans (by norm_num)
  cases sourceSign <;> cases receiverSign <;>
    simp [AxialSign.opposite] at hsourceOpposite hreceiverOpposite <;>
    simp [localizationFourChartInner, localizationAnnularStretchInner,
      hpair, hsource, hsourceOpposite, hreceiver, hreceiverOpposite]

/-! ## Uniform kernel and exact assembled multiplier -/

/-- One aperture-uniform constant controls all four enlarged chart kernels. -/
theorem exists_uniform_localizationTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ sourceSign receiverSign : AxialSign,
        ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
          (∫ x : EuclideanFrequencyPair,
            ‖normalizedStretchTensorKernel
              (localizationBufferedStretchCutoff sourceSign receiverSign)
              delta x‖) ≤ C := by
  classical
  choose C hCnonneg hCbound using
    (fun sourceSign : AxialSign ↦ fun receiverSign : AxialSign ↦
      exists_uniform_tensorKernel_mass_for_cutoff
        (localizationBufferedStretchCutoff sourceSign receiverSign))
  let M : ℝ := ∑ sourceSign : AxialSign,
    ∑ receiverSign : AxialSign, C sourceSign receiverSign
  have hM : 0 ≤ M := by
    unfold M
    exact Finset.sum_nonneg fun sourceSign _ ↦
      Finset.sum_nonneg fun receiverSign _ ↦ hCnonneg sourceSign receiverSign
  refine ⟨M, hM, ?_⟩
  intro sourceSign receiverSign delta hdelta
  apply (hCbound sourceSign receiverSign delta hdelta).trans
  unfold M
  have hinner : C sourceSign receiverSign ≤
      ∑ r : AxialSign, C sourceSign r :=
    Finset.single_le_sum (fun r _ ↦ hCnonneg sourceSign r)
      (Finset.mem_univ receiverSign)
  have houter : (∑ r : AxialSign, C sourceSign r) ≤
      ∑ s : AxialSign, ∑ r : AxialSign, C s r :=
    Finset.single_le_sum
      (fun s _ ↦ Finset.sum_nonneg fun r _ ↦ hCnonneg s r)
      (Finset.mem_univ sourceSign)
  exact hinner.trans houter

/-- The assembled localization-stable four-chart symbol. -/
def localizationFourChartTensorSymbol (delta : ℝ) :
    𝓢(EuclideanFrequencyPair, CoherentBilinearOperator) :=
  normalizedStretchTensorSymbol
      (localizationBufferedStretchCutoff .positive .positive) delta +
    normalizedStretchTensorSymbol
      (localizationBufferedStretchCutoff .positive .negative) delta +
    normalizedStretchTensorSymbol
      (localizationBufferedStretchCutoff .negative .positive) delta +
    normalizedStretchTensorSymbol
      (localizationBufferedStretchCutoff .negative .negative) delta

/-- The assembled localization-stable inverse-Fourier kernel. -/
def localizationFourChartTensorKernel (delta : ℝ) :
    𝓢(EuclideanFrequencyPair, CoherentBilinearOperator) :=
  normalizedStretchTensorKernel
      (localizationBufferedStretchCutoff .positive .positive) delta +
    normalizedStretchTensorKernel
      (localizationBufferedStretchCutoff .positive .negative) delta +
    normalizedStretchTensorKernel
      (localizationBufferedStretchCutoff .negative .positive) delta +
    normalizedStretchTensorKernel
      (localizationBufferedStretchCutoff .negative .negative) delta

theorem fourier_localizationFourChartTensorKernel (delta : ℝ) :
    𝓕 (localizationFourChartTensorKernel delta) =
      localizationFourChartTensorSymbol delta := by
  simp [localizationFourChartTensorKernel, localizationFourChartTensorSymbol,
    fourier_normalizedStretchTensorKernel]

/-- On the thickened annulus, the assembled multiplier is still exactly the
uncut coherent Biot--Savart stretching interaction. -/
theorem apply_localizationFourChartTensorSymbol_eq_coherent
    (delta : ℝ) (xi : EuclideanFrequencyPair) (u v : ComplexVec3)
    (hsource : InLocalizationBufferedPancakeAnnulus
      (euclideanToFrequencyPairEquiv xi).1)
    (hreceiver : InLocalizationBufferedPancakeAnnulus
      (euclideanToFrequencyPairEquiv xi).2) :
    applyCoherentBilinearOperator
        (localizationFourChartTensorSymbol delta xi) u v =
      coherentProjectedNormalizedStretch delta
        (euclideanToFrequencyPairEquiv xi) u v := by
  let p := euclideanToFrequencyPairEquiv xi
  have hpartition : localizationFourChartInner p = 1 :=
    localizationFourChartInner_eq_one_of_mem_buffer hsource hreceiver
  rw [localizationFourChartTensorSymbol]
  change applyCoherentBilinearOperator
      (normalizedStretchTensorSymbol
          (localizationBufferedStretchCutoff .positive .positive) delta xi +
        normalizedStretchTensorSymbol
          (localizationBufferedStretchCutoff .positive .negative) delta xi +
        normalizedStretchTensorSymbol
          (localizationBufferedStretchCutoff .negative .positive) delta xi +
        normalizedStretchTensorSymbol
          (localizationBufferedStretchCutoff .negative .negative) delta xi) u v = _
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
    (((localizationAnnularStretchInner .positive .positive p : ℝ) : ℂ) *
          complexCoherentChartCoeff (receiverFrequency delta p) v *
          complexCoherentChartCoeff (sourceFrequency delta p) u) *
          realVec3ToComplexVec3 (normalizedStretch delta p) i +
      (((localizationAnnularStretchInner .positive .negative p : ℝ) : ℂ) *
          complexCoherentChartCoeff (receiverFrequency delta p) v *
          complexCoherentChartCoeff (sourceFrequency delta p) u) *
          realVec3ToComplexVec3 (normalizedStretch delta p) i +
      (((localizationAnnularStretchInner .negative .positive p : ℝ) : ℂ) *
          complexCoherentChartCoeff (receiverFrequency delta p) v *
          complexCoherentChartCoeff (sourceFrequency delta p) u) *
          realVec3ToComplexVec3 (normalizedStretch delta p) i +
      (((localizationAnnularStretchInner .negative .negative p : ℝ) : ℂ) *
          complexCoherentChartCoeff (receiverFrequency delta p) v *
          complexCoherentChartCoeff (sourceFrequency delta p) u) *
          realVec3ToComplexVec3 (normalizedStretch delta p) i =
      (complexCoherentChartCoeff (receiverFrequency delta p) v *
          complexCoherentChartCoeff (sourceFrequency delta p) u) *
          realVec3ToComplexVec3 (normalizedStretch delta p) i
  have hpartitionComplex :
      (((localizationAnnularStretchInner .positive .positive p +
        localizationAnnularStretchInner .positive .negative p +
        localizationAnnularStretchInner .negative .positive p +
        localizationAnnularStretchInner .negative .negative p : ℝ) : ℂ)) = 1 := by
    simpa [localizationFourChartInner] using congrArg Complex.ofReal hpartition
  calc
    _ = (((localizationAnnularStretchInner .positive .positive p +
          localizationAnnularStretchInner .positive .negative p +
          localizationAnnularStretchInner .negative .positive p +
          localizationAnnularStretchInner .negative .negative p : ℝ) : ℂ) *
        complexCoherentChartCoeff (receiverFrequency delta p) v *
        complexCoherentChartCoeff (sourceFrequency delta p) u) *
        realVec3ToComplexVec3 (normalizedStretch delta p) i := by
      push_cast
      ring
    _ = _ := by rw [hpartitionComplex]; ring

/-- The sum of the four localization-stable inverse kernels has one
aperture-uniform `L¹` mass bound. -/
theorem exists_uniform_localizationFourChartTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
      (∫ x : EuclideanFrequencyPair,
        ‖localizationFourChartTensorKernel delta x‖) ≤ C := by
  rcases exists_uniform_localizationTensorKernel_mass with
    ⟨C, hC, hmass⟩
  refine ⟨4 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro delta hdelta
  let Kpp := normalizedStretchTensorKernel
    (localizationBufferedStretchCutoff .positive .positive) delta
  let Kpn := normalizedStretchTensorKernel
    (localizationBufferedStretchCutoff .positive .negative) delta
  let Knp := normalizedStretchTensorKernel
    (localizationBufferedStretchCutoff .negative .positive) delta
  let Knn := normalizedStretchTensorKernel
    (localizationBufferedStretchCutoff .negative .negative) delta
  have hpp : Integrable (fun x : EuclideanFrequencyPair ↦ ‖Kpp x‖) :=
    Kpp.integrable.norm
  have hpn : Integrable (fun x : EuclideanFrequencyPair ↦ ‖Kpn x‖) :=
    Kpn.integrable.norm
  have hnp : Integrable (fun x : EuclideanFrequencyPair ↦ ‖Knp x‖) :=
    Knp.integrable.norm
  have hnn : Integrable (fun x : EuclideanFrequencyPair ↦ ‖Knn x‖) :=
    Knn.integrable.norm
  have hsum : Integrable (fun x : EuclideanFrequencyPair ↦
      ‖Kpp x‖ + ‖Kpn x‖ + ‖Knp x‖ + ‖Knn x‖) :=
    ((hpp.add hpn).add hnp).add hnn
  calc
    (∫ x : EuclideanFrequencyPair,
      ‖localizationFourChartTensorKernel delta x‖) ≤
        ∫ x : EuclideanFrequencyPair,
          (‖Kpp x‖ + ‖Kpn x‖ + ‖Knp x‖ + ‖Knn x‖) := by
      apply integral_mono
        (localizationFourChartTensorKernel delta).integrable.norm hsum
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

end PancakeBufferedAnnularMultiplier
end NavierStokes
end FluidDynamics
end Mettapedia
