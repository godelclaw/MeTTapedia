import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSmoothCoherentStretchSymbol
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Uniform mass for compact continuous Schwartz families

This module isolates the functional-analytic endpoint needed by the coherent
pancake multiplier.  A family of six-dimensional Schwartz kernels that is
continuous in the Schwartz topology over a compact aperture interval has one
common `L¹`-mass bound.  Thus the remaining symbol-specific obligation is to
prove Schwartz-topology continuity of the explicit normalized tensor family;
pointwise-in-aperture integrability is no longer the endpoint.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeUniformKernelFamily

open MeasureTheory
open PancakeBilinearKernelScaling
open PancakeSmoothCoherentStretchSymbol
open Set
open scoped ContDiff FourierTransform SchwartzMap

abbrev TensorSchwartz :=
  𝓢(EuclideanFrequencyPair, CoherentBilinearOperator)

/-- Restricting a jointly smooth function to a fixed parameter slice cannot
increase the norm of any iterated derivative in the spatial variables. -/
theorem norm_iteratedFDeriv_parameter_section_le_joint
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ℝ × P → V) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (delta : ℝ) (p : P) :
    ‖iteratedFDeriv ℝ n (fun x : P ↦ F (delta, x)) p‖ ≤
      ‖iteratedFDeriv ℝ n F (delta, p)‖ := by
  let L : P →L[ℝ] ℝ × P := ContinuousLinearMap.inr ℝ ℝ P
  let a : ℝ × P := (delta, 0)
  let G : ℝ × P → V := fun z ↦ F (a + z)
  have hG : ContDiff ℝ ∞ G :=
    hF.comp (contDiff_const.add contDiff_id)
  have hderiv := L.iteratedFDeriv_comp_right hG p
    (show (n : ℕ∞) ≤ ∞ by exact_mod_cast le_top)
  have hfun : (fun x : P ↦ F (delta, x)) = G ∘ L := by
    funext x
    simp [G, L, a]
  rw [hfun, hderiv]
  rw [show iteratedFDeriv ℝ n G (L p) =
      iteratedFDeriv ℝ n F (delta, p) by
    simp [G, L, a, iteratedFDeriv_comp_add_left]]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact pow_le_one₀ (norm_nonneg _)
    (ContinuousLinearMap.norm_inr_le_one ℝ ℝ P)

/-- Joint smoothness plus a fixed compact spatial support gives simultaneous
bounds for every weighted spatial derivative over a compact parameter
interval.  This is the parametric Schwartz estimate used below. -/
theorem exists_uniform_pow_mul_iteratedFDeriv_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ℝ × P → V) (hF : ContDiff ℝ ∞ F)
    (L : Set P) (hL : IsCompact L)
    (hsupport : ∀ delta, tsupport (fun p ↦ F (delta, p)) ⊆ L)
    (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2), ∀ p : P,
        ‖p‖ ^ k *
          ‖iteratedFDeriv ℝ n (fun x : P ↦ F (delta, x)) p‖ ≤ C := by
  let H : ℝ × P → ℝ := fun q ↦
    ‖q.2‖ ^ k * ‖iteratedFDeriv ℝ n F q‖
  let K : Set (ℝ × P) := Icc (0 : ℝ) (1 / 2) ×ˢ L
  have hderiv : Continuous (fun q ↦ iteratedFDeriv ℝ n F q) :=
    hF.continuous_iteratedFDeriv
      (show (n : ℕ∞) ≤ ∞ by exact_mod_cast le_top)
  have hH : Continuous H := by
    exact ((continuous_norm.comp continuous_snd).pow k).mul hderiv.norm
  have hK : IsCompact K := isCompact_Icc.prod hL
  have hbounded : BddAbove (H '' K) :=
    hK.bddAbove_image hH.continuousOn
  rcases hbounded with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro delta hdelta p
  by_cases hp : p ∈ L
  · have hHM : H (delta, p) ≤ M :=
      hM (mem_image_of_mem H ⟨hdelta, hp⟩)
    calc
      ‖p‖ ^ k *
          ‖iteratedFDeriv ℝ n (fun x : P ↦ F (delta, x)) p‖ ≤
          ‖p‖ ^ k * ‖iteratedFDeriv ℝ n F (delta, p)‖ :=
        mul_le_mul_of_nonneg_left
          (norm_iteratedFDeriv_parameter_section_le_joint F hF n delta p)
          (pow_nonneg (norm_nonneg _) _)
      _ = H (delta, p) := rfl
      _ ≤ M := hHM
      _ ≤ max M 0 := le_max_left _ _
  · have hpnot : p ∉ tsupport (fun x : P ↦ F (delta, x)) :=
      fun h ↦ hp (hsupport delta h)
    have hpnotderiv : p ∉ Function.support
        (iteratedFDeriv ℝ n (fun x : P ↦ F (delta, x))) :=
      fun h ↦ hpnot (support_iteratedFDeriv_subset n h)
    have hzero : iteratedFDeriv ℝ n (fun x : P ↦ F (delta, x)) p = 0 :=
      Function.notMem_support.mp hpnotderiv
    rw [hzero, norm_zero, mul_zero]
    exact le_max_right _ _

/-- Every Schwartz seminorm of each explicit complex six-frequency symbol
entry is bounded uniformly in the aperture. -/
theorem exists_uniform_complexNormalizedStretchEntry_seminorm
    (i j l : Fin 3) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        SchwartzMap.seminorm ℂ k n
          (complexNormalizedStretchEntrySchwartz
            explicitBufferedStretchCutoff delta i j l) ≤ C := by
  let F : ℝ × EuclideanFrequencyPair → ℂ := fun q ↦
    Complex.ofReal
      (localizedNormalizedStretchEntry explicitBufferedStretchCutoff
        q.1 i j l (euclideanToFrequencyPairEquiv q.2))
  let L : Set EuclideanFrequencyPair :=
    euclideanToFrequencyPairEquiv ⁻¹'
      Metric.closedBall pairCenter retainedPairBump.rOut
  have hpair : ContDiff ℝ ∞ (fun q : ℝ × EuclideanFrequencyPair ↦
      (q.1, euclideanToFrequencyPairEquiv q.2)) :=
    contDiff_fst.prodMk
      (euclideanToFrequencyPairEquiv.contDiff.comp contDiff_snd)
  have hF : ContDiff ℝ ∞ F := by
    exact Complex.ofRealCLM.contDiff.comp
      ((contDiff_joint_localizedNormalizedStretchEntry i j l).comp hpair)
  have hL : IsCompact L :=
    euclideanToFrequencyPairEquiv.toHomeomorph.isCompact_preimage.mpr
      (isCompact_closedBall pairCenter retainedPairBump.rOut)
  have hsupport : ∀ delta,
      tsupport (fun ξ ↦ F (delta, ξ)) ⊆ L := by
    intro delta
    have hreal : tsupport
        (fun ξ : EuclideanFrequencyPair ↦
          localizedNormalizedStretchEntry explicitBufferedStretchCutoff
            delta i j l (euclideanToFrequencyPairEquiv ξ)) ⊆ L := by
      rw [show (fun ξ : EuclideanFrequencyPair ↦
          localizedNormalizedStretchEntry explicitBufferedStretchCutoff
            delta i j l (euclideanToFrequencyPairEquiv ξ)) =
          (localizedNormalizedStretchEntry explicitBufferedStretchCutoff
            delta i j l) ∘ euclideanToFrequencyPairEquiv from rfl]
      rw [show tsupport
          ((localizedNormalizedStretchEntry explicitBufferedStretchCutoff
            delta i j l) ∘ euclideanToFrequencyPairEquiv) =
          euclideanToFrequencyPairEquiv ⁻¹'
            tsupport (localizedNormalizedStretchEntry
              explicitBufferedStretchCutoff delta i j l) by
        simpa using tsupport_comp_eq_preimage
          (localizedNormalizedStretchEntry explicitBufferedStretchCutoff
            delta i j l) euclideanToFrequencyPairEquiv.toHomeomorph]
      exact preimage_mono
        (tsupport_localizedNormalizedStretchEntry_subset_closedBall
          delta i j l)
    exact (tsupport_comp_subset Complex.ofReal_zero
      (fun ξ : EuclideanFrequencyPair ↦
        localizedNormalizedStretchEntry explicitBufferedStretchCutoff
          delta i j l (euclideanToFrequencyPairEquiv ξ))).trans hreal
  rcases exists_uniform_pow_mul_iteratedFDeriv_bound
      F hF L hL hsupport k n with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta
  apply SchwartzMap.seminorm_le_bound ℂ k n _ hC
  intro ξ
  change ‖ξ‖ ^ k *
    ‖iteratedFDeriv ℝ n (fun x : EuclideanFrequencyPair ↦
      F (delta, x)) ξ‖ ≤ C
  exact hbound delta hdelta ξ

/-- Every spatial derivative of an explicit complex symbol entry has a
uniform `L¹` bound over the aperture interval. -/
theorem exists_uniform_integral_norm_symbol_deriv
    (i j l : Fin 3) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        (∫ ξ : EuclideanFrequencyPair,
          ‖iteratedFDeriv ℝ n
            (complexNormalizedStretchEntrySchwartz
              explicitBufferedStretchCutoff delta i j l)
            ξ‖) ≤ C := by
  let p : ℕ := (volume : Measure EuclideanFrequencyPair).integrablePower
  rcases exists_uniform_complexNormalizedStretchEntry_seminorm
      i j l 0 n with ⟨C0, hC0, h0⟩
  rcases exists_uniform_complexNormalizedStretchEntry_seminorm
      i j l p n with ⟨Cp, hCp, hp⟩
  let A : ℝ :=
    2 ^ p *
      ∫ x : EuclideanFrequencyPair,
        (1 + ‖x‖) ^ (-(p : ℝ))
  have hA : 0 ≤ A := by
    unfold A
    positivity
  refine ⟨A * (C0 + Cp), mul_nonneg hA (add_nonneg hC0 hCp), ?_⟩
  intro delta hdelta
  let f := complexNormalizedStretchEntrySchwartz
    explicitBufferedStretchCutoff delta i j l
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

/-- Fourier decay of one normalized inverse-kernel entry, with every source
derivative integral displayed explicitly. -/
theorem pow_mul_norm_normalizedStretchKernelEntry_le
    (i j l : Fin 3) (m : ℕ) (delta : ℝ)
    (x : EuclideanFrequencyPair) :
    ‖x‖ ^ m *
        ‖normalizedStretchKernelEntry explicitBufferedStretchCutoff
          delta i j l x‖ ≤
      2 ^ m * ∑ r ∈ Finset.range (m + 1),
        ∫ ξ : EuclideanFrequencyPair,
          ‖iteratedFDeriv ℝ r
            (complexNormalizedStretchEntrySchwartz
              explicitBufferedStretchCutoff delta i j l) ξ‖ := by
  let f := complexNormalizedStretchEntrySchwartz
    explicitBufferedStretchCutoff delta i j l
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

/-- Every polynomially weighted normalized kernel entry has a common
pointwise bound over the aperture interval. -/
theorem exists_uniform_pow_mul_norm_kernelEntry_bound
    (i j l : Fin 3) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        ∀ x : EuclideanFrequencyPair,
          ‖x‖ ^ m *
            ‖normalizedStretchKernelEntry explicitBufferedStretchCutoff
              delta i j l x‖ ≤ C := by
  classical
  choose C hCnonneg hCbound using
    (fun r : ℕ ↦ exists_uniform_integral_norm_symbol_deriv i j l r)
  let M : ℝ := 2 ^ m * ∑ r ∈ Finset.range (m + 1), C r
  have hM : 0 ≤ M := by
    unfold M
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun r _ ↦ hCnonneg r)
  refine ⟨M, hM, ?_⟩
  intro delta hdelta x
  apply (pow_mul_norm_normalizedStretchKernelEntry_le
    i j l m delta x).trans
  unfold M
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 2 ^ m)
  exact Finset.sum_le_sum fun r hr ↦ hCbound r delta hdelta

/-- The desired frequency-uniform `L¹` mass bound for every scalar entry of
the normalized six-dimensional bilinear kernel. -/
theorem exists_uniform_normalizedStretchKernelEntry_mass
    (i j l : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
        (∫ x : EuclideanFrequencyPair,
          ‖normalizedStretchKernelEntry explicitBufferedStretchCutoff
            delta i j l x‖) ≤ C := by
  let p : ℕ := (volume : Measure EuclideanFrequencyPair).integrablePower
  rcases exists_uniform_pow_mul_norm_kernelEntry_bound
      i j l 0 with ⟨C0, hC0, h0⟩
  rcases exists_uniform_pow_mul_norm_kernelEntry_bound
      i j l p with ⟨Cp, hCp, hp⟩
  let A : ℝ :=
    2 ^ p *
      ∫ x : EuclideanFrequencyPair,
        (1 + ‖x‖) ^ (-(p : ℝ))
  have hA : 0 ≤ A := by
    unfold A
    positivity
  refine ⟨A * (C0 + Cp), mul_nonneg hA (add_nonneg hC0 hCp), ?_⟩
  intro delta hdelta
  have hmass := integral_pow_mul_le_of_le_of_pow_mul_le
    (μ := (volume : Measure EuclideanFrequencyPair))
    (f := normalizedStretchKernelEntry explicitBufferedStretchCutoff
      delta i j l)
    (k := 0)
    (by simpa using h0 delta hdelta)
    (by simpa [p] using hp delta hdelta)
  simpa [A, p] using hmass

theorem norm_elementaryBilinearTensor_le_one (i j l : Fin 3) :
    ‖elementaryBilinearTensor i j l‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro a
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro b
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro c
  by_cases hai : a = i <;> by_cases hbj : b = j <;>
      by_cases hcl : c = l <;>
    simp [elementaryBilinearTensor, hai, hbj, hcl]

/-- The full tensor norm is controlled without loss beyond summing its 27
scalar inverse-Fourier entries. -/
theorem norm_normalizedStretchTensorKernel_le_sum_entries
    (delta : ℝ) (x : EuclideanFrequencyPair) :
    ‖normalizedStretchTensorKernel explicitBufferedStretchCutoff delta x‖ ≤
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        ‖normalizedStretchKernelEntry explicitBufferedStretchCutoff
          delta i j l x‖ := by
  change ‖∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
    scalarMultipleBilinearTensorCLM (elementaryBilinearTensor i j l)
      (normalizedStretchKernelEntry explicitBufferedStretchCutoff
        delta i j l x)‖ ≤ _
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3, ∑ l : Fin 3,
        scalarMultipleBilinearTensorCLM (elementaryBilinearTensor i j l)
          (normalizedStretchKernelEntry explicitBufferedStretchCutoff
            delta i j l x)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖∑ l : Fin 3,
        scalarMultipleBilinearTensorCLM (elementaryBilinearTensor i j l)
          (normalizedStretchKernelEntry explicitBufferedStretchCutoff
            delta i j l x)‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        ‖scalarMultipleBilinearTensorCLM (elementaryBilinearTensor i j l)
          (normalizedStretchKernelEntry explicitBufferedStretchCutoff
            delta i j l x)‖ := by
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

/-- **Uniform normalized tensor-kernel mass.**  The complete 27-entry
six-dimensional coherent-stretching kernel has one `L¹` bound independent of
the aperture on `0 ≤ delta ≤ 1/2`. -/
theorem exists_uniform_normalizedStretchTensorKernel_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
      (∫ x : EuclideanFrequencyPair,
        ‖normalizedStretchTensorKernel explicitBufferedStretchCutoff
          delta x‖) ≤ C := by
  classical
  choose C hCnonneg hCbound using
    (fun i : Fin 3 ↦ fun j : Fin 3 ↦ fun l : Fin 3 ↦
      exists_uniform_normalizedStretchKernelEntry_mass i j l)
  let M : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, C i j l
  have hM : 0 ≤ M := by
    unfold M
    exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      Finset.sum_nonneg fun l _ ↦ hCnonneg i j l
  refine ⟨M, hM, ?_⟩
  intro delta hdelta
  have hentry (i j l : Fin 3) : Integrable
      (fun x : EuclideanFrequencyPair ↦
        ‖normalizedStretchKernelEntry explicitBufferedStretchCutoff
          delta i j l x‖) :=
    (normalizedStretchKernelEntry_integrable
      explicitBufferedStretchCutoff delta i j l).norm
  have hsum : Integrable (fun x : EuclideanFrequencyPair ↦
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        ‖normalizedStretchKernelEntry explicitBufferedStretchCutoff
          delta i j l x‖) := by
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro i _
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro j _
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro l _
    exact hentry i j l
  calc
    (∫ x : EuclideanFrequencyPair,
      ‖normalizedStretchTensorKernel explicitBufferedStretchCutoff
        delta x‖) ≤
        ∫ x : EuclideanFrequencyPair,
          ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
            ‖normalizedStretchKernelEntry explicitBufferedStretchCutoff
              delta i j l x‖ :=
      integral_mono
        (normalizedStretchTensorKernel_integrable
          explicitBufferedStretchCutoff delta).norm
        hsum (norm_normalizedStretchTensorKernel_le_sum_entries delta)
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        ∫ x : EuclideanFrequencyPair,
          ‖normalizedStretchKernelEntry explicitBufferedStretchCutoff
            delta i j l x‖ := by
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

/-- A compact continuous family of six-dimensional tensor-valued Schwartz
kernels has a common `L¹` mass bound. -/
theorem exists_uniform_integral_norm_bound
    (K : ℝ → TensorSchwartz)
    (hK : ContinuousOn K (Icc (0 : ℝ) (1 / 2))) :
    ∃ C : ℝ, ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
      (∫ x : EuclideanFrequencyPair, ‖K delta x‖) ≤ C := by
  let p : ℕ := (volume : Measure EuclideanFrequencyPair).integrablePower
  let envelope : TensorSchwartz → ℝ := fun f ↦
    SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ p 0 f
  have hseminorm (k n : ℕ) :
      Continuous (SchwartzMap.seminorm ℂ k n : TensorSchwartz → ℝ) := by
    simpa only [SchwartzMap.schwartzSeminormFamily_apply] using
      (schwartz_withSeminorms ℂ EuclideanFrequencyPair
        CoherentBilinearOperator).continuous_seminorm (k, n)
  have henvelope : Continuous envelope :=
    (hseminorm 0 0).add (hseminorm p 0)
  have hbound : BddAbove ((envelope ∘ K) '' Icc (0 : ℝ) (1 / 2)) :=
    isCompact_Icc.bddAbove_image (henvelope.comp_continuousOn hK)
  rcases hbound with ⟨M, hM⟩
  let A : ℝ :=
    2 ^ p *
      ∫ x : EuclideanFrequencyPair,
        (1 + ‖x‖) ^ (-(p : ℝ))
  refine ⟨A * M, ?_⟩
  intro delta hdelta
  have henv : envelope (K delta) ≤ M :=
    hM (mem_image_of_mem (envelope ∘ K) hdelta)
  have hA : 0 ≤ A := by
    unfold A
    positivity
  have hmass := (K delta).integral_pow_mul_iteratedFDeriv_le
    ℂ (volume : Measure EuclideanFrequencyPair) 0 0
  have hmass' :
      (∫ x : EuclideanFrequencyPair, ‖K delta x‖) ≤
        A * envelope (K delta) := by
    simpa [A, envelope, p] using hmass
  exact hmass'.trans (mul_le_mul_of_nonneg_left henv hA)

/-- Specialization showing exactly what remains for the explicit normalized
coherent-stretching kernel family. -/
theorem exists_uniform_explicit_kernel_mass
    (hcontinuous : ContinuousOn
      (fun delta ↦ normalizedStretchTensorKernel
        explicitBufferedStretchCutoff delta)
      (Icc (0 : ℝ) (1 / 2))) :
    ∃ C : ℝ, ∀ delta ∈ Icc (0 : ℝ) (1 / 2),
      (∫ x : EuclideanFrequencyPair,
        ‖normalizedStretchTensorKernel explicitBufferedStretchCutoff
          delta x‖) ≤ C :=
  exists_uniform_integral_norm_bound _ hcontinuous

end PancakeUniformKernelFamily
end NavierStokes
end FluidDynamics
end Mettapedia
