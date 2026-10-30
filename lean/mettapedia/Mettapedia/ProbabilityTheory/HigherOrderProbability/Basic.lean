import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mettapedia.ProbabilityTheory.Basic

/-!
# Parametrized probability laws

A `ParametrizedDistribution` retains a Markov kernel and its supplied mixing law.
`kyburgJoint` retains both parameter and outcome; `flatten` retains only the outcome.
The latter preserves one-outcome probabilities and outcome-only expectations.
It need not preserve dependence between repeated draws at a shared parameter.

References: Kyburg (1988), *Higher Order Probabilities*; Giry (1982),
*A categorical approach to probability theory*.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

/-- A measurable family of probability laws together with its probability mixing law. -/
structure Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution
    (Θ X : Type*) [MeasurableSpace Θ] [MeasurableSpace X] where
  /-- The supplied family of conditional probability laws. -/
  kernel : Kernel Θ X
  /-- Each kernel row has total mass one. -/
  kernel_isMarkov : ProbabilityTheory.IsMarkovKernel kernel
  /-- The supplied distribution over parameters. -/
  mixingMeasure : Measure Θ
  /-- The mixing law has total mass one. -/
  mixing_isProbability : IsProbabilityMeasure mixingMeasure

namespace Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]

instance instIsMarkovKernel (pd : ParametrizedDistribution Θ X) :
    ProbabilityTheory.IsMarkovKernel pd.kernel :=
  pd.kernel_isMarkov

instance instIsProbKernel (pd : ParametrizedDistribution Θ X) (θ : Θ) :
    IsProbabilityMeasure (pd.kernel θ) :=
  inferInstance  -- Uses IsMarkovKernel.is_probability_measure'

instance instIsProbMixing (pd : ParametrizedDistribution Θ X) :
    IsProbabilityMeasure pd.mixingMeasure :=
  pd.mixing_isProbability

/-- The outcome marginal: integrate each kernel row against the mixing law. -/
noncomputable def flatten (pd : ParametrizedDistribution Θ X) : Measure X :=
  pd.mixingMeasure.bind pd.kernel

/-- The outcome marginal is a probability measure. -/
instance flatten_isProbability (pd : ParametrizedDistribution Θ X) :
    IsProbabilityMeasure (flatten pd) := by
  unfold flatten
  infer_instance

/-- The joint law retaining both parameter and outcome. -/
noncomputable def kyburgJoint (pd : ParametrizedDistribution Θ X) : Measure (Θ × X) :=
  pd.mixingMeasure.compProd pd.kernel

/-- The joint law is a probability measure. -/
instance kyburgJoint_isProbability (pd : ParametrizedDistribution Θ X) :
    IsProbabilityMeasure (kyburgJoint pd) := by
  unfold kyburgJoint
  infer_instance

/-- Evaluate the outcome marginal on a measurable set. -/
theorem flatten_apply (pd : ParametrizedDistribution Θ X) (s : Set X) (hs : MeasurableSet s) :
    (flatten pd) s = ∫⁻ θ, (pd.kernel θ) s ∂pd.mixingMeasure := by
  unfold flatten
  rw [Measure.bind_apply hs pd.kernel.aemeasurable]

/-- The outcome marginal is the second marginal of the joint law. -/
theorem flatten_eq_snd_kyburgJoint (pd : ParametrizedDistribution Θ X) :
    flatten pd = (kyburgJoint pd).snd := by
  unfold flatten kyburgJoint
  rw [Measure.snd_compProd]

/-- The mixing law is the first marginal of the joint law. -/
theorem mixingMeasure_eq_fst_kyburgJoint (pd : ParametrizedDistribution Θ X) :
    pd.mixingMeasure = (kyburgJoint pd).fst := by
  unfold kyburgJoint
  rw [Measure.fst_compProd]

/-- Countable parameter spaces give a weighted sum of the supplied kernel rows. -/
theorem flatten_eq_sum_countable [Countable Θ] [MeasurableSingletonClass Θ]
    (pd : ParametrizedDistribution Θ X) :
    flatten pd = Measure.sum (fun θ => pd.mixingMeasure {θ} • pd.kernel θ) := by
  unfold flatten
  exact Measure.comp_eq_sum_of_countable

/-- A deterministic kernel gives the pushforward of the mixing law. -/
theorem flatten_deterministic {Y : Type*} [MeasurableSpace Y]
    (f : Θ → Y) (hf : Measurable f)
    (μ : Measure Θ) [IsProbabilityMeasure μ] :
    (Kernel.deterministic f hf) ∘ₘ μ = μ.map f :=
  Measure.deterministic_comp_eq_map hf

end Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution
