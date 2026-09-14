import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Periodization over a fundamental domain

A countable measure-preserving additive action transfers integrable kernels
to a fundamental domain. The Fourier-character identity and weighted mass
estimate retain the actual orbit sum.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FundamentalDomainPeriodization

open MeasureTheory Set
open scoped ENNReal

/-- The periodization of a kernel under a countable additive action. -/
def addPeriodization
    {G α E : Type*} [AddGroup G] [AddAction G α]
    [NormedAddCommGroup E]
    (K : α → E) (x : α) : E :=
  ∑' g : G, K (g +ᵥ x)

/-- A periodization of a measurable function is measurable. -/
theorem measurable_addPeriodization
    {G α E : Type*} [AddGroup G] [Countable G] [AddAction G α]
    [MeasurableSpace α] [MeasurableConstVAdd G α]
    [NormedAddCommGroup E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (K : α → E) (hK : Measurable K) :
    Measurable (addPeriodization (G := G) K) := by
  exact Measurable.tsum fun g ↦ hK.comp (measurable_const_vadd g)

/-- The cover-side periodization is invariant under every lattice shift. -/
theorem addPeriodization_vadd
    {G α E : Type*} [AddCommGroup G] [AddAction G α]
    [NormedAddCommGroup E]
    (K : α → E) (g₀ : G) (x : α) :
    addPeriodization (G := G) K (g₀ +ᵥ x) =
      addPeriodization (G := G) K x := by
  unfold addPeriodization
  calc
    (∑' g : G, K (g +ᵥ (g₀ +ᵥ x))) =
        ∑' g : G, K ((g + g₀) +ᵥ x) := by
      apply tsum_congr
      intro g
      rw [add_vadd]
    _ = ∑' g : G, K (g +ᵥ x) := by
      simpa only [Equiv.coe_addRight] using
        (Equiv.addRight g₀).tsum_eq (fun g : G ↦ K (g +ᵥ x))

/-- Periodization does not increase `L¹` mass when measured on a fundamental
domain.  The statement uses the lower integral, so it also records the bound
before any separate measurability proof for the vector-valued periodization.
-/
theorem setLIntegral_enorm_addPeriodization_le
    {G α E : Type*} [AddGroup G] [Countable G] [AddAction G α]
    [MeasurableSpace α] [MeasurableConstVAdd G α]
    {μ : Measure α} [VAddInvariantMeasure G α μ]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {s : Set α} (hfund : IsAddFundamentalDomain G s μ)
    (K : α → E) (hK : Measurable K) :
    (∫⁻ x in s, ‖addPeriodization (G := G) K x‖ₑ ∂μ) ≤
      ∫⁻ x, ‖K x‖ₑ ∂μ := by
  calc
    (∫⁻ x in s, ‖addPeriodization (G := G) K x‖ₑ ∂μ) ≤
        ∫⁻ x in s, ∑' g : G, ‖K (g +ᵥ x)‖ₑ ∂μ := by
      apply lintegral_mono
      intro x
      simpa [addPeriodization] using
        (enorm_tsum_le_tsum_enorm
          (f := fun g : G ↦ K (g +ᵥ x)))
    _ = ∑' g : G, ∫⁻ x in s, ‖K (g +ᵥ x)‖ₑ ∂μ := by
      rw [lintegral_tsum]
      intro g
      exact ((hK.comp (measurable_const_vadd g)).enorm).aemeasurable
    _ = ∫⁻ x, ‖K x‖ₑ ∂μ :=
      (hfund.lintegral_eq_tsum'' fun x ↦ ‖K x‖ₑ).symm

/-- If the original kernel is integrable, its periodization is integrable on
one fundamental domain. -/
theorem integrableOn_addPeriodization
    {G α E : Type*} [AddGroup G] [Countable G] [AddAction G α]
    [MeasurableSpace α] [MeasurableConstVAdd G α]
    {μ : Measure α} [VAddInvariantMeasure G α μ]
    [NormedAddCommGroup E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {s : Set α} (hfund : IsAddFundamentalDomain G s μ)
    (K : α → E) (hKmeas : Measurable K) (hKint : Integrable K μ) :
    IntegrableOn (addPeriodization (G := G) K) s μ := by
  refine ⟨(measurable_addPeriodization K hKmeas).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt
    (setLIntegral_enorm_addPeriodization_le hfund K hKmeas)
    hKint.hasFiniteIntegral

/-- A lattice-invariant scalar weight can be unfolded from a periodized
kernel whenever the weighted kernel is integrable. The weight need not be
a unit character or have constant norm. -/
theorem setIntegral_smul_addPeriodization_eq
    {G α E : Type*} [AddGroup G] [Countable G] [AddAction G α]
    [MeasurableSpace α] [MeasurableConstVAdd G α]
    {μ : Measure α} [VAddInvariantMeasure G α μ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {s : Set α} (hfund : IsAddFundamentalDomain G s μ)
    (K : α → E) (hKmeas : Measurable K)
    (χ : α → ℂ) (hχmeas : Measurable χ)
    (hχvadd : ∀ (g : G) (x : α), χ (g +ᵥ x) = χ x)
    (hweighted : Integrable (fun x ↦ χ x • K x) μ) :
    (∫ x in s, χ x • addPeriodization (G := G) K x ∂μ) =
      ∫ x, χ x • K x ∂μ := by
  let F : G → α → E := fun g x ↦ χ x • K (g +ᵥ x)
  have hFmeas (g : G) : AEStronglyMeasurable (F g) (μ.restrict s) := by
    exact (hχmeas.smul (hKmeas.comp (measurable_const_vadd g))).aestronglyMeasurable
  have hFshift (g : G) (x : α) : F g x = χ (g +ᵥ x) • K (g +ᵥ x) := by
    simp only [F, hχvadd]
  have hsumFinite :
      ∑' g : G, ∫⁻ x in s, ‖F g x‖ₑ ∂μ ≠ ∞ := by
    have hcover :
        (∑' g : G, ∫⁻ x in s, ‖F g x‖ₑ ∂μ) =
          ∫⁻ x, ‖χ x • K x‖ₑ ∂μ := by
      simp_rw [hFshift]
      exact (hfund.lintegral_eq_tsum'' fun x ↦ ‖χ x • K x‖ₑ).symm
    rw [hcover]
    exact (hasFiniteIntegral_iff_enorm.mp hweighted.hasFiniteIntegral).ne
  calc
    (∫ x in s, χ x • addPeriodization (G := G) K x ∂μ) =
        ∫ x in s, ∑' g : G, F g x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [F, addPeriodization]
      exact (tsum_const_smul'' (χ x)).symm
    _ = ∑' g : G, ∫ x in s, F g x ∂μ := by
      exact integral_tsum hFmeas hsumFinite
    _ = ∑' g : G, ∫ x in s, (χ (g +ᵥ x) • K (g +ᵥ x)) ∂μ := by
      apply tsum_congr
      intro g
      apply integral_congr_ae
      filter_upwards with x
      rw [hχvadd]
    _ = ∫ x, χ x • K x ∂μ :=
      (hfund.integral_eq_tsum'' (fun x ↦ χ x • K x) hweighted).symm

/-- The unit-character interface is a specialization of weighted unfolding. -/
theorem setIntegral_character_smul_addPeriodization_eq
    {G α E : Type*} [AddGroup G] [Countable G] [AddAction G α]
    [MeasurableSpace α] [MeasurableConstVAdd G α]
    {μ : Measure α} [VAddInvariantMeasure G α μ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {s : Set α} (hfund : IsAddFundamentalDomain G s μ)
    (K : α → E) (hKmeas : Measurable K) (hKint : Integrable K μ)
    (χ : α → ℂ) (hχmeas : Measurable χ)
    (hχnorm : ∀ x, ‖χ x‖ = 1)
    (hχvadd : ∀ (g : G) (x : α), χ (g +ᵥ x) = χ x) :
    (∫ x in s, χ x • addPeriodization (G := G) K x ∂μ) =
      ∫ x, χ x • K x ∂μ := by
  apply setIntegral_smul_addPeriodization_eq hfund K hKmeas χ hχmeas hχvadd
  exact hKint.bdd_smul 1 hχmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by rw [hχnorm x])


/-- A nonnegative lattice-invariant weight survives periodization without
increasing the weighted mass on a fundamental domain. -/
theorem setLIntegral_weight_mul_enorm_addPeriodization_le
    {G α E : Type*} [AddGroup G] [Countable G] [AddAction G α]
    [MeasurableSpace α] [MeasurableConstVAdd G α]
    {μ : Measure α} [VAddInvariantMeasure G α μ]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {s : Set α} (hfund : IsAddFundamentalDomain G s μ)
    (K : α → E) (hK : Measurable K) (w : α → ℝ≥0∞) (hw : Measurable w)
    (hinv : ∀ (g : G) (x : α), w (g +ᵥ x) = w x) :
    (∫⁻ x in s, w x * ‖addPeriodization (G := G) K x‖ₑ ∂μ) ≤
      ∫⁻ x, w x * ‖K x‖ₑ ∂μ := by
  calc
    _ ≤ ∫⁻ x in s, ∑' g : G, w x * ‖K (g +ᵥ x)‖ₑ ∂μ := by
      apply lintegral_mono
      intro x
      change w x * ‖addPeriodization (G := G) K x‖ₑ ≤ ∑' g : G, w x * ‖K (g +ᵥ x)‖ₑ
      rw [ENNReal.tsum_mul_left]
      exact mul_le_mul_right (enorm_tsum_le_tsum_enorm (f := fun g : G ↦ K (g +ᵥ x))) _
    _ = ∑' g : G, ∫⁻ x in s, w x * ‖K (g +ᵥ x)‖ₑ ∂μ := by
      rw [lintegral_tsum]
      intro g
      exact (hw.mul (hK.comp (measurable_const_vadd g)).enorm).aemeasurable
    _ = ∑' g : G, ∫⁻ x in s, w (g +ᵥ x) * ‖K (g +ᵥ x)‖ₑ ∂μ := by
      simp_rw [hinv]
    _ = _ := (hfund.lintegral_eq_tsum'' fun x ↦ w x * ‖K x‖ₑ).symm

end Mettapedia.Analysis.FundamentalDomainPeriodization
