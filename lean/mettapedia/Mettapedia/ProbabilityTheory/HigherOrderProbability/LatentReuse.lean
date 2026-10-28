import Mettapedia.ProbabilityTheory.HigherOrderProbability.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Moments.Variance

/-!
# Reusing a latent parameter

`sharedPair` samples one parameter and then two conditionally independent outcomes.
`freshPair` samples twice from the flattened law, resampling the parameter implicitly.
Both have the same one-step marginals. Their same-event probability difference is
the variance of the component event probability. Flattening a single outcome
therefore does not determine the law of repeated observations at a retained parameter.
-/

noncomputable section

open MeasureTheory _root_.ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]

/-- Draw two outcomes using the same latent parameter. -/
def sharedPair (pd : ParametrizedDistribution Θ X) : Measure (X × X) :=
  (pd.kernel ×ₖ pd.kernel) ∘ₘ pd.mixingMeasure

/-- Draw independently from the marginal, without retaining the parameter. -/
def freshPair (pd : ParametrizedDistribution Θ X) : Measure (X × X) :=
  (flatten pd).prod (flatten pd)

/-- Retain an observed outcome and draw again using its original parameter. -/
def observeAgain (pd : ParametrizedDistribution Θ X) : Kernel (Θ × X) (X × X) :=
  Kernel.deterministic Prod.snd measurable_snd ×ₖ
    pd.kernel.comap Prod.fst measurable_fst

instance sharedPair_isProbability (pd : ParametrizedDistribution Θ X) :
    IsProbabilityMeasure (sharedPair pd) := by unfold sharedPair; infer_instance

instance freshPair_isProbability (pd : ParametrizedDistribution Θ X) :
    IsProbabilityMeasure (freshPair pd) := by unfold freshPair; infer_instance

instance observeAgain_isMarkov (pd : ParametrizedDistribution Θ X) :
    IsMarkovKernel (observeAgain pd) := by unfold observeAgain; infer_instance

theorem observeAgain_kyburgJoint (pd : ParametrizedDistribution Θ X) :
    observeAgain pd ∘ₘ kyburgJoint pd = sharedPair pd := by
  ext s hs
  rw [Measure.bind_apply hs (observeAgain pd).aemeasurable]
  change (∫⁻ z, observeAgain pd z s ∂pd.mixingMeasure ⊗ₘ pd.kernel) = _
  rw [Measure.lintegral_compProd ((observeAgain pd).measurable_coe hs), sharedPair,
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro θ
  rw [Kernel.prod_apply, Measure.prod_apply hs]
  apply lintegral_congr
  intro x
  exact Kernel.deterministic_prod_apply' measurable_snd
    (pd.kernel.comap Prod.fst measurable_fst) (θ, x) hs

theorem sharedPair_apply_prod (pd : ParametrizedDistribution Θ X)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    sharedPair pd (A ×ˢ B) = ∫⁻ θ, pd.kernel θ A * pd.kernel θ B ∂pd.mixingMeasure := by
  rw [sharedPair, Measure.bind_apply (hA.prod hB) (Kernel.aemeasurable _)]
  simp_rw [Kernel.prod_apply_prod]

theorem freshPair_apply_prod (pd : ParametrizedDistribution Θ X) (A B : Set X) :
    freshPair pd (A ×ˢ B) = flatten pd A * flatten pd B := Measure.prod_prod A B

@[simp] theorem fst_sharedPair (pd : ParametrizedDistribution Θ X) :
    (sharedPair pd).fst = flatten pd := by
  rw [Measure.fst, sharedPair, Measure.map_comp _ _ measurable_fst]
  rw [← Kernel.fst_eq, Kernel.fst_prod]
  rfl

@[simp] theorem snd_sharedPair (pd : ParametrizedDistribution Θ X) :
    (sharedPair pd).snd = flatten pd := by
  rw [Measure.snd, sharedPair, Measure.map_comp _ _ measurable_snd]
  rw [← Kernel.snd_eq, Kernel.snd_prod]
  rfl

@[simp] theorem fst_freshPair (pd : ParametrizedDistribution Θ X) :
    (freshPair pd).fst = flatten pd := by simp [freshPair]

@[simp] theorem snd_freshPair (pd : ParametrizedDistribution Θ X) :
    (freshPair pd).snd = flatten pd := by simp [freshPair]

/-- Component event probabilities are bounded, hence square-integrable. -/
theorem event_memLp (pd : ParametrizedDistribution Θ X) {A : Set X}
    (hA : MeasurableSet A) : MemLp (fun θ => (pd.kernel θ A).toReal) 2 pd.mixingMeasure := by
  refine MemLp.of_bound (pd.kernel.measurable_coe hA).ennreal_toReal.aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun θ => by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_le_one

theorem integral_event (pd : ParametrizedDistribution Θ X) {A : Set X}
    (hA : MeasurableSet A) :
    (∫ θ, (pd.kernel θ A).toReal ∂pd.mixingMeasure) = (flatten pd A).toReal := by
  rw [flatten_apply pd A hA]
  exact integral_toReal (pd.kernel.measurable_coe hA).aemeasurable
    (Filter.Eventually.of_forall fun θ => measure_lt_top (pd.kernel θ) A)

/-- Reusing a parameter adds exactly its variance to the same-event probability. -/
theorem sharedPair_sub_freshPair_eq_variance (pd : ParametrizedDistribution Θ X)
    {A : Set X} (hA : MeasurableSet A) :
    (sharedPair pd (A ×ˢ A)).toReal - (freshPair pd (A ×ˢ A)).toReal =
      variance (fun θ => (pd.kernel θ A).toReal) pd.mixingMeasure := by
  rw [variance_eq_sub (event_memLp pd hA), integral_event pd hA,
    sharedPair_apply_prod pd hA hA, freshPair_apply_prod, ENNReal.toReal_mul]
  congr 1
  · have hi := integral_toReal (μ := pd.mixingMeasure)
      (f := fun θ => pd.kernel θ A * pd.kernel θ A)
      ((pd.kernel.measurable_coe hA).mul (pd.kernel.measurable_coe hA)).aemeasurable
      (Filter.Eventually.of_forall fun θ =>
        ENNReal.mul_lt_top (measure_lt_top (pd.kernel θ) A) (measure_lt_top (pd.kernel θ) A))
    simpa only [ENNReal.toReal_mul, Pi.pow_apply, pow_two] using hi.symm
  · exact (pow_two _).symm

theorem freshPair_same_event_le_sharedPair (pd : ParametrizedDistribution Θ X)
    {A : Set X} (hA : MeasurableSet A) :
    (freshPair pd (A ×ˢ A)).toReal ≤ (sharedPair pd (A ×ˢ A)).toReal :=
  sub_nonneg.mp ((sharedPair_sub_freshPair_eq_variance pd hA).symm ▸ variance_nonneg _ _)

/-- This is a per-event almost-everywhere criterion, with no shared null set asserted. -/
theorem sharedPair_same_event_eq_iff (pd : ParametrizedDistribution Θ X)
    {A : Set X} (hA : MeasurableSet A) :
    sharedPair pd (A ×ˢ A) = freshPair pd (A ×ˢ A) ↔
      ∀ᵐ θ ∂pd.mixingMeasure, (pd.kernel θ A).toReal = (flatten pd A).toReal := by
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _),
    ← sub_eq_zero, sharedPair_sub_freshPair_eq_variance pd hA]
  constructor
  · intro h
    simpa only [integral_event pd hA] using
      ae_eq_integral_of_variance_eq_zero (event_memLp pd hA) h
  · intro h
    rw [variance_congr h, variance_eq_integral measurable_const.aemeasurable]
    simp

/-- A constant family has no latent dependence to lose. -/
theorem sharedPair_eq_freshPair_of_constant (pd : ParametrizedDistribution Θ X)
    (ν : Measure X) (h : ∀ θ, pd.kernel θ = ν) : sharedPair pd = freshPair pd := by
  have hk : pd.kernel = Kernel.const Θ ν := Kernel.ext fun θ => h θ
  have hf : flatten pd = ν := by simp [flatten, hk]
  have : IsProbabilityMeasure ν := by rw [← hf]; infer_instance
  simp [sharedPair, freshPair, hk, Kernel.prod_const, hf]

end Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution
