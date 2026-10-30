/-
LLM primer:
- `ProbSimplex k = ↥(stdSimplex ℝ (Fin k))` — subtype of `Fin k → ℝ`
- `catWeight θ xs = ENNReal.ofReal (categoricalProductPMF θ xs)`
- `catPMF θ n` is a `PMF (Fin n → Fin k)` via `PMF.ofFintype` + `sum_catWeight_eq_one`
- `catKernel k n` is the Markov kernel `ProbSimplex k → Measure (Fin n → Fin k)`
- Measurability of the kernel uses polynomial structure of categoricalProductPMF
- The flatten bridge identifies `flatten(pd M n) {xs} = ENNReal.ofReal (M.prob xs)`
-/
import Mettapedia.ProbabilityTheory.Exchangeability.CategoricalMixture
import Mettapedia.ProbabilityTheory.HigherOrderProbability.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Categorical de Finetti as Kyburg Flattening

This file packages categorical mixtures from `CategoricalMixture.lean` as instances of
Kyburg's higher-order probability structure (`ParametrizedDistribution`).

This generalizes `DeFinettiConnection.lean` from binary (Bool/Bernoulli) to k-ary
(Fin k / Categorical) observations.

## Main Definitions

* `CategoricalConnection.catWeight` : ENNReal weight of a word under parameter θ
* `CategoricalConnection.catPMF` : PMF on `Fin n → Fin k` from a simplex point
* `CategoricalConnection.catKernel` : Markov kernel ProbSimplex k → Measure (Fin n → Fin k)
* `CategoricalConnection.pd` : Kyburg parametrized distribution for a categorical mixture

## Main Theorems

* `CategoricalConnection.sum_catWeight_eq_one` : Weight function is a valid PMF
* `CategoricalConnection.catKernel_isMarkov` : The kernel is Markov
* `CategoricalConnection.flatten_apply_singleton` : The Kyburg flattening bridge

## References

* `DeFinettiConnection.lean` (the binary case)
* `CategoricalMixture.lean` (the categorical mixture structure)
* `Basic.lean` (Kyburg's ParametrizedDistribution)
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.HigherOrderProbability

open MeasureTheory _root_.ProbabilityTheory Finset BigOperators ENNReal
open Mettapedia.ProbabilityTheory.Exchangeability.CategoricalDeFinetti

namespace CategoricalConnection

/-! ## ENNReal weight and PMF -/

/-- The `ENNReal` weight of a word `xs` under a simplex parameter `θ`. -/
def catWeight {k n : ℕ} (θ : ProbSimplex k) (xs : Fin n → Fin k) : ENNReal :=
  ENNReal.ofReal (categoricalProductPMF (↑θ : Fin k → ℝ) xs)

/-- The categorical weight function sums to `1` over all words of length `n`.

    This is the key normalization lemma enabling the PMF construction.
    The proof proceeds by induction on `n`, decomposing `Fin (n+1) → Fin k`
    via `Fin.consEquiv` and using `∑ₐ θ(a) = 1` at each step. -/
theorem sum_catWeight_eq_one {k n : ℕ} (θ : ProbSimplex k) :
    ∑ xs : Fin n → Fin k, catWeight θ xs = 1 := by
  classical
  have hweight (xs : Fin n → Fin k) :
      catWeight θ xs = ∏ i, ENNReal.ofReal ((θ : Fin k → ℝ) (xs i)) :=
    ENNReal.ofReal_prod_of_nonneg (fun i _ => probSimplex_nonneg θ (xs i))
  have hnorm : (∑ a : Fin k, ENNReal.ofReal ((θ : Fin k → ℝ) a)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => probSimplex_nonneg θ a)]
    simp
  simp_rw [hweight]
  rw [← Fintype.prod_sum (fun _ : Fin n => fun a : Fin k => ENNReal.ofReal ((θ : Fin k → ℝ) a))]
  simp only [hnorm, Finset.prod_const_one]

/-- The `PMF` on `Fin n → Fin k` induced by a simplex point `θ`. -/
def catPMF {k : ℕ} (θ : ProbSimplex k) (n : ℕ) : PMF (Fin n → Fin k) :=
  PMF.ofFintype (catWeight θ) (sum_catWeight_eq_one θ)

@[simp] lemma catPMF_apply {k : ℕ} (θ : ProbSimplex k) (n : ℕ) (xs : Fin n → Fin k) :
    catPMF θ n xs = catWeight θ xs := by
  simp [catPMF]

@[simp] lemma catPMF_toMeasure_apply_singleton {k : ℕ} (θ : ProbSimplex k) (n : ℕ)
    (xs : Fin n → Fin k) :
    (catPMF θ n).toMeasure {xs} = catWeight θ xs := by
  simp [catPMF]

/-! ## Markov kernel -/

/-- The categorical product kernel: for each simplex point θ, produces the
    product measure on `Fin n → Fin k` with step distribution θ.

    This generalizes `DeFinettiConnection.kernel` from Bool to Fin k. -/
def catKernel (k n : ℕ) : _root_.ProbabilityTheory.Kernel (ProbSimplex k) (Fin n → Fin k) :=
  { toFun := fun θ => (catPMF θ n).toMeasure
    measurable' := by
      refine Measure.measurable_of_measurable_coe _ ?_
      intro s _hs
      classical
      -- Rewrite as finite sum of indicators
      have hrewrite :
          (fun θ : ProbSimplex k => (catPMF θ n).toMeasure s) =
            fun θ => ∑ x : Fin n → Fin k,
              (if x ∈ s then catWeight θ x else 0) := by
        funext θ
        simp [PMF.toMeasure_apply_fintype, catPMF, catWeight, Set.indicator]
      rw [hrewrite]
      refine Finset.measurable_fun_sum _ (fun x _ => ?_)
      by_cases hx : x ∈ s
      · simp only [hx, ↓reduceIte]
        -- catWeight is measurable: polynomial in θ-coordinates
        unfold catWeight categoricalProductPMF
        refine ENNReal.measurable_ofReal.comp ?_
        refine Finset.measurable_prod _ (fun i _ => ?_)
        exact (measurable_pi_apply (x i)).comp measurable_subtype_coe
      · simp [hx] }

instance catKernel_isMarkov (k n : ℕ) : _root_.ProbabilityTheory.IsMarkovKernel (catKernel k n) := by
  refine ⟨fun θ => ?_⟩
  show IsProbabilityMeasure ((catPMF θ n).toMeasure)
  infer_instance

/-! ## Kyburg parametrized distribution -/

/-- Pull a mixing measure supported on the simplex back to the `ProbSimplex k` subtype. -/
def mixingMeasureSimplex {k : ℕ} (M : CategoricalMixture k) : Measure (ProbSimplex k) :=
  M.mixingMeasure.comap (fun θ : ProbSimplex k => (θ : Fin k → ℝ))

instance mixingMeasureSimplex_isProbability {k : ℕ} (M : CategoricalMixture k) :
    IsProbabilityMeasure (mixingMeasureSimplex M) := by
  have : IsProbabilityMeasure M.mixingMeasure := M.isProbability
  refine (MeasurableEmbedding.subtype_coe (measurableSet_stdSimplex k)).isProbabilityMeasure_comap ?_
  simpa only [Subtype.range_val, ae_iff, Set.compl_def] using M.support_simplex

/-- The Kyburg parametrized distribution for a categorical mixture at horizon `n`. -/
def pd {k : ℕ} (M : CategoricalMixture k) (n : ℕ) :
    ParametrizedDistribution (ProbSimplex k) (Fin n → Fin k) :=
  { kernel := catKernel k n
    kernel_isMarkov := catKernel_isMarkov k n
    mixingMeasure := mixingMeasureSimplex M
    mixing_isProbability := inferInstance }

/-! ## Bridge lemma -/

/-- **The Kyburg flattening bridge for categorical mixtures**:

    `flatten(pd M n) {xs} = ENNReal.ofReal (M.prob xs)`

    This identifies the Kyburg-flattened distribution evaluated at a singleton
    with the categorical mixture probability. It generalizes
    `DeFinettiConnection.flatten_apply_singleton` from Bool to Fin k. -/
theorem flatten_apply_singleton {k : ℕ} (M : CategoricalMixture k) (n : ℕ)
    (xs : Fin n → Fin k) :
    (ParametrizedDistribution.flatten (pd M n)) {xs}
      = ENNReal.ofReal (M.prob xs) := by
  classical
  -- Expand flatten as lintegral
  have hmeas : MeasurableSet ({xs} : Set (Fin n → Fin k)) := by simp
  have hflat :
      (ParametrizedDistribution.flatten (pd M n)) {xs} =
        ∫⁻ θ : ProbSimplex k,
          ENNReal.ofReal (categoricalProductPMF (↑θ : Fin k → ℝ) xs)
            ∂mixingMeasureSimplex M := by
    simpa [pd, catKernel, catPMF_toMeasure_apply_singleton, catPMF, catWeight] using
      (ParametrizedDistribution.flatten_apply (pd M n) {xs} hmeas)
  -- Convert subtype integral to set integral
  have hs : MeasurableSet (stdSimplex ℝ (Fin k)) := measurableSet_stdSimplex k
  have hsub :
      (∫⁻ θ : ProbSimplex k,
        ENNReal.ofReal (categoricalProductPMF (↑θ : Fin k → ℝ) xs)
          ∂mixingMeasureSimplex M) =
        ∫⁻ t in stdSimplex ℝ (Fin k),
          ENNReal.ofReal (categoricalProductPMF t xs) ∂M.mixingMeasure := by
    simpa [mixingMeasureSimplex, hs] using!
      (lintegral_subtype_comap (μ := M.mixingMeasure) (s := stdSimplex ℝ (Fin k)) hs
        (f := fun t : Fin k → ℝ => ENNReal.ofReal (categoricalProductPMF t xs)))
  -- Convert lintegral of ofReal to ofReal of integral
  have hcont : Continuous fun t : Fin k → ℝ => categoricalProductPMF t xs := by
    unfold categoricalProductPMF
    exact continuous_finsetProd _ (fun i _ => continuous_apply (xs i))
  have : IsProbabilityMeasure M.mixingMeasure := M.isProbability
  have hbounds : ∀ᵐ t ∂M.mixingMeasure.restrict (stdSimplex ℝ (Fin k)),
      categoricalProductPMF t xs ∈ Set.Icc 0 1 :=
    ae_restrict_of_forall_mem hs fun t ht =>
      ⟨categoricalProductPMF_nonneg ⟨t, ht⟩ xs, categoricalProductPMF_le_one ⟨t, ht⟩ xs⟩
  have hint := (memLp_of_bounded hbounds
    hcont.measurable.aestronglyMeasurable 1).integrable (by simp)
  have hnonneg := hbounds.mono fun _ ht => ht.1
  have hconv :
      ∫⁻ t in stdSimplex ℝ (Fin k),
        ENNReal.ofReal (categoricalProductPMF t xs) ∂M.mixingMeasure =
      ENNReal.ofReal (∫ t in stdSimplex ℝ (Fin k),
        categoricalProductPMF t xs ∂M.mixingMeasure) := by
    simpa using
      (ofReal_integral_eq_lintegral_ofReal
        (μ := M.mixingMeasure.restrict (stdSimplex ℝ (Fin k)))
        (f := fun t => categoricalProductPMF t xs) hint hnonneg).symm
  -- Assemble
  calc
    (ParametrizedDistribution.flatten (pd M n)) {xs}
        = ∫⁻ θ : ProbSimplex k,
            ENNReal.ofReal (categoricalProductPMF (↑θ) xs)
              ∂mixingMeasureSimplex M := hflat
    _ = ∫⁻ t in stdSimplex ℝ (Fin k),
            ENNReal.ofReal (categoricalProductPMF t xs) ∂M.mixingMeasure := hsub
    _ = ENNReal.ofReal (∫ t in stdSimplex ℝ (Fin k),
            categoricalProductPMF t xs ∂M.mixingMeasure) := hconv
    _ = ENNReal.ofReal (M.prob xs) := by
          simp [CategoricalMixture.prob]

end CategoricalConnection

end Mettapedia.ProbabilityTheory.HigherOrderProbability
