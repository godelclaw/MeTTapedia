import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAnnularChartCutoff
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeUniformKernelFamily

/-!
# Uniform inverse-Fourier mass for the four annular charts

The original uniform-kernel proof was specialized to one demonstration bump.
This module extracts the argument for an arbitrary `BufferedStretchCutoff`.
The hypotheses already stored in that structure--smooth compact inner cutoff,
smooth outer buffer, and globally nonzero denominators--are exactly what the
parametric Schwartz estimate needs.  We then specialize the generic result to
the four signed annular charts and take one common finite constant.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeAnnularUniformKernel

open MeasureTheory
open Set
open PancakeBilinearKernelScaling
open PancakeRealCoherentPairEstimate
open PancakeCoherentStretchFactorization
open PancakeSmoothCoherentSymbol
open PancakeSmoothCoherentStretchSymbol
open PancakeUniformKernelFamily
open PancakeAnnularChartCutoff
open scoped ContDiff FourierTransform SchwartzMap

/-- The localized symbol associated to any buffered cutoff is jointly smooth
in aperture and normalized frequency. -/
theorem contDiff_joint_localizedNormalizedStretchEntry_for_cutoff
    (D : BufferedStretchCutoff) (i j l : Fin 3) :
    ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      localizedNormalizedStretchEntry D q.1 i j l q.2) := by
  have hinner : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦ D.inner q.2) :=
    D.inner_contDiff.comp contDiff_snd
  have hscoord : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      coordinate (coherentW (sourceFrequency q.1 q.2)) j) := by
    fin_cases j <;>
      simp [coordinate, sourceFrequency, scaledPancakeFrequency,
        coherentW, normSq, dot, add, smul, ex] <;>
      fun_prop
  have hrcoord : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      coordinate (coherentW (receiverFrequency q.1 q.2)) l) := by
    fin_cases l <;>
      simp [coordinate, receiverFrequency, scaledPancakeFrequency,
        coherentW, normSq, dot, add, smul, ex] <;>
      fun_prop
  have hncoord : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      coordinate (normalizedStretch q.1 q.2) i) := by
    fin_cases i <;>
      simp [coordinate, normalizedStretch, coherentStretchNormalized,
        receiverCoupling, scaledPancakeFrequency, smul, add] <;>
      fun_prop
  have hsden : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      sourceBufferedDenominator D q.1 q.2) := by
    have ho : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦ D.outer q.2) :=
      D.outer_contDiff.comp contDiff_snd
    have hcoord (r : Fin 3) : ContDiff ℝ ∞
        (fun q : ℝ × FrequencyPair ↦
          coordinate (coherentW (sourceFrequency q.1 q.2)) r) := by
      fin_cases r <;>
        simp [coordinate, sourceFrequency, scaledPancakeFrequency,
          coherentW, normSq, dot, add, smul, ex] <;>
        fun_prop
    unfold sourceBufferedDenominator normSq dot
    exact ((((hcoord 0).mul (hcoord 0)).add
      ((hcoord 1).mul (hcoord 1))).add
      ((hcoord 2).mul (hcoord 2))).add
      ((contDiff_const.sub ho).pow 2)
  have hrden : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      receiverBufferedDenominator D q.1 q.2) := by
    have ho : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦ D.outer q.2) :=
      D.outer_contDiff.comp contDiff_snd
    have hcoord (r : Fin 3) : ContDiff ℝ ∞
        (fun q : ℝ × FrequencyPair ↦
          coordinate (coherentW (receiverFrequency q.1 q.2)) r) := by
      fin_cases r <;>
        simp [coordinate, receiverFrequency, scaledPancakeFrequency,
          coherentW, normSq, dot, add, smul, ex] <;>
        fun_prop
    unfold receiverBufferedDenominator normSq dot
    exact ((((hcoord 0).mul (hcoord 0)).add
      ((hcoord 1).mul (hcoord 1))).add
      ((hcoord 2).mul (hcoord 2))).add
      ((contDiff_const.sub ho).pow 2)
  unfold localizedNormalizedStretchEntry
  exact (((hinner.mul
      (hscoord.div hsden (fun q ↦ D.source_denominator_ne q.1 q.2))).mul
      (hrcoord.div hrden (fun q ↦ D.receiver_denominator_ne q.1 q.2))).mul
      hncoord)

/-- The support of every localized entry lies in the fixed inner support,
independently of aperture and tensor indices. -/
theorem tsupport_localizedNormalizedStretchEntry_subset_inner
    (D : BufferedStretchCutoff) (delta : ℝ) (i j l : Fin 3) :
    tsupport (localizedNormalizedStretchEntry D delta i j l) ⊆
      tsupport D.inner := by
  unfold localizedNormalizedStretchEntry
  exact tsupport_mul_subset_left.trans
    (tsupport_mul_subset_left.trans tsupport_mul_subset_left)

/-- Every Schwartz seminorm of a complex symbol entry is bounded uniformly in
the aperture for any buffered cutoff. -/
theorem exists_uniform_complexEntry_seminorm_for_cutoff
    (D : BufferedStretchCutoff) (i j l : Fin 3) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        SchwartzMap.seminorm ℂ k n
          (complexNormalizedStretchEntrySchwartz D delta i j l) ≤ C := by
  let F : ℝ × EuclideanFrequencyPair → ℂ := fun q ↦
    Complex.ofReal
      (localizedNormalizedStretchEntry D q.1 i j l
        (euclideanToFrequencyPairEquiv q.2))
  let L : Set EuclideanFrequencyPair :=
    euclideanToFrequencyPairEquiv ⁻¹' tsupport D.inner
  have hpair : ContDiff ℝ ∞ (fun q : ℝ × EuclideanFrequencyPair ↦
      (q.1, euclideanToFrequencyPairEquiv q.2)) :=
    contDiff_fst.prodMk
      (euclideanToFrequencyPairEquiv.contDiff.comp contDiff_snd)
  have hF : ContDiff ℝ ∞ F := by
    exact Complex.ofRealCLM.contDiff.comp
      ((contDiff_joint_localizedNormalizedStretchEntry_for_cutoff
        D i j l).comp hpair)
  have hL : IsCompact L :=
    euclideanToFrequencyPairEquiv.toHomeomorph.isCompact_preimage.mpr
      D.inner_compact
  have hsupport : ∀ delta,
      tsupport (fun ξ ↦ F (delta, ξ)) ⊆ L := by
    intro delta
    have hreal : tsupport
        (fun ξ : EuclideanFrequencyPair ↦
          localizedNormalizedStretchEntry D delta i j l
            (euclideanToFrequencyPairEquiv ξ)) ⊆ L := by
      rw [show (fun ξ : EuclideanFrequencyPair ↦
          localizedNormalizedStretchEntry D delta i j l
            (euclideanToFrequencyPairEquiv ξ)) =
          (localizedNormalizedStretchEntry D delta i j l) ∘
            euclideanToFrequencyPairEquiv from rfl]
      rw [show tsupport
          ((localizedNormalizedStretchEntry D delta i j l) ∘
            euclideanToFrequencyPairEquiv) =
          euclideanToFrequencyPairEquiv ⁻¹'
            tsupport (localizedNormalizedStretchEntry D delta i j l) by
        simpa using tsupport_comp_eq_preimage
          (localizedNormalizedStretchEntry D delta i j l)
          euclideanToFrequencyPairEquiv.toHomeomorph]
      exact preimage_mono
        (tsupport_localizedNormalizedStretchEntry_subset_inner D delta i j l)
    exact (tsupport_comp_subset Complex.ofReal_zero
      (fun ξ : EuclideanFrequencyPair ↦
        localizedNormalizedStretchEntry D delta i j l
          (euclideanToFrequencyPairEquiv ξ))).trans hreal
  rcases exists_uniform_pow_mul_iteratedFDeriv_bound
      F hF L hL hsupport k n with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta
  apply SchwartzMap.seminorm_le_bound ℂ k n _ hC
  intro ξ
  change ‖ξ‖ ^ k *
    ‖iteratedFDeriv ℝ n
      (fun x : EuclideanFrequencyPair ↦ F (delta, x)) ξ‖ ≤ C
  exact hbound delta hdelta ξ

/-- Uniform `L¹` bounds for every derivative of an arbitrary buffered symbol
entry. -/
theorem exists_uniform_integral_norm_symbol_deriv_for_cutoff
    (D : BufferedStretchCutoff) (i j l : Fin 3) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        (∫ ξ : EuclideanFrequencyPair,
          ‖iteratedFDeriv ℝ n
            (complexNormalizedStretchEntrySchwartz D delta i j l) ξ‖) ≤ C := by
  let p : ℕ := (volume : Measure EuclideanFrequencyPair).integrablePower
  rcases exists_uniform_complexEntry_seminorm_for_cutoff
      D i j l 0 n with ⟨C0, hC0, h0⟩
  rcases exists_uniform_complexEntry_seminorm_for_cutoff
      D i j l p n with ⟨Cp, hCp, hp⟩
  let A : ℝ :=
    2 ^ p * ∫ x : EuclideanFrequencyPair, (1 + ‖x‖) ^ (-(p : ℝ))
  have hA : 0 ≤ A := by unfold A; positivity
  refine ⟨A * (C0 + Cp), mul_nonneg hA (add_nonneg hC0 hCp), ?_⟩
  intro delta hdelta
  let f := complexNormalizedStretchEntrySchwartz D delta i j l
  have hmass := f.integral_pow_mul_iteratedFDeriv_le
    ℂ (volume : Measure EuclideanFrequencyPair) 0 n
  have hmass' :
      (∫ ξ : EuclideanFrequencyPair,
        ‖iteratedFDeriv ℝ n f ξ‖) ≤
        A * (SchwartzMap.seminorm ℂ 0 n f +
          SchwartzMap.seminorm ℂ p n f) := by
    simpa [A, p] using hmass
  apply hmass'.trans
  apply mul_le_mul_of_nonneg_left _ hA
  exact add_le_add (h0 delta hdelta) (hp delta hdelta)

/-- Fourier decay for an arbitrary buffered inverse-kernel entry. -/
theorem pow_mul_norm_kernelEntry_le_for_cutoff
    (D : BufferedStretchCutoff) (i j l : Fin 3) (m : ℕ) (delta : ℝ)
    (x : EuclideanFrequencyPair) :
    ‖x‖ ^ m * ‖normalizedStretchKernelEntry D delta i j l x‖ ≤
      2 ^ m * ∑ r ∈ Finset.range (m + 1),
        ∫ ξ : EuclideanFrequencyPair,
          ‖iteratedFDeriv ℝ r
            (complexNormalizedStretchEntrySchwartz D delta i j l) ξ‖ := by
  let f := complexNormalizedStretchEntrySchwartz D delta i j l
  have hFourier := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (f.smooth ⊤)
    (fun k n _ _ ↦ f.integrable_pow_mul_iteratedFDeriv
      (volume : Measure EuclideanFrequencyPair) k n)
    (k := 0) (n := m) le_top le_top (-x)
  simp only [norm_neg, norm_iteratedFDeriv_zero, pow_zero, one_mul,
    Nat.cast_zero, zero_add, Finset.range_one] at hFourier
  change ‖x‖ ^ m * ‖𝓕 f (-x)‖ ≤ _ at hFourier
  unfold normalizedStretchKernelEntry
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
    ← SchwartzMap.fourier_coe]
  simpa [f, Finset.sum_product] using hFourier

theorem exists_uniform_pow_mul_norm_kernelEntry_for_cutoff
    (D : BufferedStretchCutoff) (i j l : Fin 3) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2), ∀ x : EuclideanFrequencyPair,
        ‖x‖ ^ m * ‖normalizedStretchKernelEntry D delta i j l x‖ ≤ C := by
  classical
  choose C hCnonneg hCbound using
    (fun r : ℕ ↦
      exists_uniform_integral_norm_symbol_deriv_for_cutoff D i j l r)
  let M : ℝ := 2 ^ m * ∑ r ∈ Finset.range (m + 1), C r
  have hM : 0 ≤ M := by
    unfold M
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun r _ ↦ hCnonneg r)
  refine ⟨M, hM, ?_⟩
  intro delta hdelta x
  apply (pow_mul_norm_kernelEntry_le_for_cutoff D i j l m delta x).trans
  unfold M
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 2 ^ m)
  exact Finset.sum_le_sum fun r hr ↦ hCbound r delta hdelta

/-- Scalar inverse-kernel entries have aperture-uniform mass for every
buffered cutoff. -/
theorem exists_uniform_kernelEntry_mass_for_cutoff
    (D : BufferedStretchCutoff) (i j l : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        (∫ x : EuclideanFrequencyPair,
          ‖normalizedStretchKernelEntry D delta i j l x‖) ≤ C := by
  let p : ℕ := (volume : Measure EuclideanFrequencyPair).integrablePower
  rcases exists_uniform_pow_mul_norm_kernelEntry_for_cutoff
      D i j l 0 with ⟨C0, hC0, h0⟩
  rcases exists_uniform_pow_mul_norm_kernelEntry_for_cutoff
      D i j l p with ⟨Cp, hCp, hp⟩
  let A : ℝ :=
    2 ^ p * ∫ x : EuclideanFrequencyPair, (1 + ‖x‖) ^ (-(p : ℝ))
  have hA : 0 ≤ A := by unfold A; positivity
  refine ⟨A * (C0 + Cp), mul_nonneg hA (add_nonneg hC0 hCp), ?_⟩
  intro delta hdelta
  have hmass := integral_pow_mul_le_of_le_of_pow_mul_le
    (μ := (volume : Measure EuclideanFrequencyPair))
    (f := normalizedStretchKernelEntry D delta i j l)
    (k := 0)
    (by simpa using h0 delta hdelta)
    (by simpa [p] using hp delta hdelta)
  simpa [A, p] using hmass

/-- The tensor norm is bounded by the sum of its 27 scalar entries for an
arbitrary buffered cutoff. -/
theorem norm_tensorKernel_le_sum_entries_for_cutoff
    (D : BufferedStretchCutoff) (delta : ℝ) (x : EuclideanFrequencyPair) :
    ‖normalizedStretchTensorKernel D delta x‖ ≤
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        ‖normalizedStretchKernelEntry D delta i j l x‖ := by
  change ‖∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
    scalarMultipleBilinearTensorCLM (elementaryBilinearTensor i j l)
      (normalizedStretchKernelEntry D delta i j l x)‖ ≤ _
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3, ∑ l : Fin 3,
        scalarMultipleBilinearTensorCLM (elementaryBilinearTensor i j l)
          (normalizedStretchKernelEntry D delta i j l x)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖∑ l : Fin 3,
        scalarMultipleBilinearTensorCLM (elementaryBilinearTensor i j l)
          (normalizedStretchKernelEntry D delta i j l x)‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        ‖scalarMultipleBilinearTensorCLM (elementaryBilinearTensor i j l)
          (normalizedStretchKernelEntry D delta i j l x)‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      rw [scalarMultipleBilinearTensorCLM_apply, norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (norm_elementaryBilinearTensor_le_one i j l)

/-- Any buffered cutoff has one tensor-kernel mass bound independent of the
aperture on `[0,1/2]`. -/
theorem exists_uniform_tensorKernel_mass_for_cutoff
    (D : BufferedStretchCutoff) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
      (∫ x : EuclideanFrequencyPair,
        ‖normalizedStretchTensorKernel D delta x‖) ≤ C := by
  classical
  choose C hCnonneg hCbound using
    (fun i : Fin 3 ↦ fun j : Fin 3 ↦ fun l : Fin 3 ↦
      exists_uniform_kernelEntry_mass_for_cutoff D i j l)
  let M : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, C i j l
  have hM : 0 ≤ M := by
    unfold M
    exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      Finset.sum_nonneg fun l _ ↦ hCnonneg i j l
  refine ⟨M, hM, ?_⟩
  intro delta hdelta
  have hentry (i j l : Fin 3) : Integrable
      (fun x : EuclideanFrequencyPair ↦
        ‖normalizedStretchKernelEntry D delta i j l x‖) :=
    (normalizedStretchKernelEntry_integrable D delta i j l).norm
  have hsum : Integrable (fun x : EuclideanFrequencyPair ↦
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        ‖normalizedStretchKernelEntry D delta i j l x‖) := by
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro i _
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro j _
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro l _
    exact hentry i j l
  calc
    (∫ x : EuclideanFrequencyPair,
      ‖normalizedStretchTensorKernel D delta x‖) ≤
        ∫ x : EuclideanFrequencyPair,
          ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
            ‖normalizedStretchKernelEntry D delta i j l x‖ :=
      integral_mono
        (normalizedStretchTensorKernel_integrable D delta).norm hsum
        (norm_tensorKernel_le_sum_entries_for_cutoff D delta)
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        ∫ x : EuclideanFrequencyPair,
          ‖normalizedStretchKernelEntry D delta i j l x‖ := by
      rw [MeasureTheory.integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i _
        rw [MeasureTheory.integral_finsetSum Finset.univ]
        · apply Finset.sum_congr rfl
          intro j _
          rw [MeasureTheory.integral_finsetSum Finset.univ]
          exact fun l _ ↦ hentry i j l
        · intro j _
          exact MeasureTheory.integrable_finsetSum Finset.univ fun l _ ↦
            hentry i j l
      · intro i _
        exact MeasureTheory.integrable_finsetSum Finset.univ fun j _ ↦
          MeasureTheory.integrable_finsetSum Finset.univ fun l _ ↦
            hentry i j l
    _ ≤ M := by
      unfold M
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      exact hCbound i j l delta hdelta

/-- **One constant for all four annular charts.** -/
theorem exists_uniform_annularTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ sourceSign receiverSign : AxialSign,
        ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
          (∫ x : EuclideanFrequencyPair,
            ‖normalizedStretchTensorKernel
              (annularBufferedStretchCutoff sourceSign receiverSign)
              delta x‖) ≤ C := by
  classical
  choose C hCnonneg hCbound using
    (fun sourceSign : AxialSign ↦ fun receiverSign : AxialSign ↦
      exists_uniform_tensorKernel_mass_for_cutoff
        (annularBufferedStretchCutoff sourceSign receiverSign))
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

end PancakeAnnularUniformKernel
end NavierStokes
end FluidDynamics
end Mettapedia
