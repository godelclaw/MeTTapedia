import Mettapedia.Analysis.SignedCrossKernel

/-!
# Exchange cancellation with an arbitrary strain test vector

Polarization extends the quadratic stretching kernel to a test vector
which need not be parallel to vorticity. Exchange leaves two endpoint
terms as well as a test-vector increment. Only radial tests reduce to the
usual single cross-product pairing. No dynamical estimate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PolarizedCrossKernel

open scoped RealInnerProductSpace
open MeasureTheory EuclideanCrossProduct SignedCrossKernel
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def polarizedStretch (H : R3 →L[ℝ] R3) (a b f : R3) : ℝ :=
  ⟪cross f b, H a⟫ + ⟪cross a b, H f⟫

def pairedTest (H : R3 →L[ℝ] R3) (a b f g : R3) : ℝ :=
  ⟪cross f b, H a⟫ + ⟪cross g a, H b⟫ + ⟪cross a b, H (f - g)⟫

theorem polarizedStretch_eq_quadratic_difference (H : R3 →L[ℝ] R3) (a b f : R3) :
    polarizedStretch H a b f =
      ⟪cross (a + f) b, H (a + f)⟫ - ⟪cross a b, H a⟫ - ⟪cross f b, H f⟫ := by
  simp only [polarizedStretch, cross_add_left, map_add, inner_add_left, inner_add_right]
  ring

theorem polarizedStretch_add_swap (H : R3 →L[ℝ] R3) (a b f g : R3) :
    polarizedStretch H a b f + polarizedStretch H b a g = pairedTest H a b f g := by
  simp only [polarizedStretch, pairedTest, cross_swap b a, inner_neg_left,
    map_sub, inner_sub_right]
  ring

theorem pairedTest_swap (H : R3 →L[ℝ] R3) (a b f g : R3) :
    pairedTest H b a g f = pairedTest H a b f g := by
  rw [← polarizedStretch_add_swap, ← polarizedStretch_add_swap]
  exact add_comm _ _

theorem pairedTest_sub_smul (H : R3 →L[ℝ] R3) (a b f g v w : R3) (c : ℝ) :
    pairedTest H a b (f - c • v) (g - c • w) =
      pairedTest H a b f g - c * pairedTest H a b v w := by
  simp only [pairedTest, cross_sub_left, cross_smul_left, map_sub, map_smul,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  ring

theorem pairedTest_radial (H : R3 →L[ℝ] R3) (a b : R3) (r s : ℝ) :
    pairedTest H a b (r • a) (s • b) = 2 * ⟪cross a b, H (r • a - s • b)⟫ := by
  simp only [pairedTest, cross_smul_left, cross_swap b a, inner_neg_left,
    map_sub, map_smul, real_inner_smul_left, real_inner_smul_right, inner_sub_right]
  ring

theorem pairedTest_radialPower (n : ℕ) (H : R3 →L[ℝ] R3) (a b : R3) :
    pairedTest H a b (RadialPower.radialPower n a) (RadialPower.radialPower n b) =
      2 * pairedStretch n H a b := pairedTest_radial H a b _ _

/-- Radial exchange and transverse variation remain separate signed terms. -/
theorem pairedTest_radial_sub_smul (H : R3 →L[ℝ] R3) (a b v w : R3) (r s c : ℝ) :
    pairedTest H a b (r • a - c • v) (s • b - c • w) =
      2 * ⟪cross a b, H (r • a - s • b)⟫ - c * pairedTest H a b v w := by
  rw [pairedTest_sub_smul, pairedTest_radial]

/-- Equal endpoint values and tests do not remove transverse work. -/
theorem pairedTest_diagonal (H : R3 →L[ℝ] R3) (a f : R3) :
    pairedTest H a a f f = 2 * ⟪cross f a, H a⟫ := by
  simp only [pairedTest, sub_self, map_zero, inner_zero_right]
  ring

/-- Isotropic kernel contributions cancel even for nonradial tests. -/
theorem pairedTest_scalar_identity (a b f g : R3) (c : ℝ) :
    pairedTest (c • ContinuousLinearMap.id ℝ R3) a b f g = 0 := by
  simp [pairedTest, cross, cross_apply, PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem pairedTest_add_scalar_identity (H : R3 →L[ℝ] R3) (a b f g : R3) (c : ℝ) :
    pairedTest (H + c • ContinuousLinearMap.id ℝ R3) a b f g = pairedTest H a b f g := by
  have h := pairedTest_scalar_identity a b f g c
  simp only [pairedTest, add_apply, inner_add_right] at h ⊢
  linarith only [h]

section Continuity

variable {X : Type*} [TopologicalSpace X]
  (H : X → R3 →L[ℝ] R3) (a b f g : X → R3)
  (hH : Continuous H) (ha : Continuous a) (hb : Continuous b)
  (hf : Continuous f) (hg : Continuous g)

include hH ha hb hf in
theorem continuous_polarizedStretch :
    Continuous (fun x ↦ polarizedStretch (H x) (a x) (b x) (f x)) :=
  ((SignedCrossKernel.continuous_cross.comp (hf.prodMk hb)).inner (hH.clm_apply ha)).add
    ((SignedCrossKernel.continuous_cross.comp (ha.prodMk hb)).inner (hH.clm_apply hf))

include hH ha hb hf hg in
theorem continuous_pairedTest :
    Continuous (fun x ↦ pairedTest (H x) (a x) (b x) (f x) (g x)) :=
  (((SignedCrossKernel.continuous_cross.comp (hf.prodMk hb)).inner (hH.clm_apply ha)).add
    ((SignedCrossKernel.continuous_cross.comp (hg.prodMk ha)).inner (hH.clm_apply hb))).add
    ((SignedCrossKernel.continuous_cross.comp (ha.prodMk hb)).inner (hH.clm_apply (hf.sub hg)))

end Continuity

section Integration

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ]
  (H : X → X → R3 →L[ℝ] R3) (w f : X → R3)
  (hH : Continuous H.uncurry) (hw : Continuous w) (hf : Continuous f)

include hH hw hf

/-- The factor one half is exchange only; polarization supplies its own
factor one half when this is identified with symmetric strain work. -/
theorem integral_polarizedStretch_eq_half_pair (hs : ∀ x y, H y x = H x y) :
    (∫ x, ∫ y, polarizedStretch (H x y) (w x) (w y) (f x) ∂μ ∂μ) =
      (1 / 2 : ℝ) * ∫ x, ∫ y, pairedTest (H x y) (w x) (w y) (f x) (f y) ∂μ ∂μ := by
  have hi : Integrable (fun p : X × X ↦ polarizedStretch (H p.1 p.2) (w p.1) (w p.2) (f p.1))
      (μ.prod μ) := (continuous_polarizedStretch _ _ _ _ hH
        (hw.comp continuous_fst) (hw.comp continuous_snd) (hf.comp continuous_fst)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hj := hi.swap
  change Integrable (fun p : X × X ↦ polarizedStretch (H p.2 p.1) (w p.2) (w p.1) (f p.2))
    (μ.prod μ) at hj
  have hp : Integrable (fun p : X × X ↦ pairedTest (H p.1 p.2) (w p.1) (w p.2) (f p.1) (f p.2))
      (μ.prod μ) := (continuous_pairedTest _ _ _ _ _ hH
        (hw.comp continuous_fst) (hw.comp continuous_snd) (hf.comp continuous_fst)
        (hf.comp continuous_snd)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫ p : X × X, pairedTest (H p.1 p.2) (w p.1) (w p.2) (f p.1) (f p.2) ∂μ.prod μ) =
      (∫ p : X × X, polarizedStretch (H p.1 p.2) (w p.1) (w p.2) (f p.1) ∂μ.prod μ) +
      (∫ p : X × X, polarizedStretch (H p.2 p.1) (w p.2) (w p.1) (f p.2) ∂μ.prod μ) := by
    rw [← integral_add hi hj]
    apply integral_congr_ae
    filter_upwards with p
    rw [hs p.1 p.2, polarizedStretch_add_swap]
  have hswap := integral_prod_swap (μ := μ) (ν := μ)
    (fun p : X × X ↦ polarizedStretch (H p.1 p.2) (w p.1) (w p.2) (f p.1))
  simp only [Prod.fst_swap, Prod.snd_swap] at hswap
  rw [hswap, integral_prod _ hi, integral_prod _ hp] at he
  linarith only [he]

end Integration

end Mettapedia.Analysis.PolarizedCrossKernel
