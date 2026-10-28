import Mettapedia.ProbabilityTheory.HigherOrderProbability.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Marginals and fixed outcome-only utilities

Flattening integrates out the latent parameter. For each fixed action and a
measurable nonnegative utility depending only on the outcome, its expected value
is unchanged. These results do not cover policies observing the parameter, or
repeated sampling with a retained parameter; see `LatentReuse` for that boundary.

Reference: Kyburg (1988), *Higher Order Probabilities*.
-/

namespace Mettapedia.ProbabilityTheory.HigherOrderProbability

open MeasureTheory _root_.ProbabilityTheory ParametrizedDistribution
open scoped ENNReal

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]

/-- The flattened probability of a measurable event is its mixed component probability. -/
theorem kyburg_flattening (pd : ParametrizedDistribution Θ X) (A : Set X)
    (hA : MeasurableSet A) :
    (flatten pd) A = ∫⁻ θ, (pd.kernel θ) A ∂pd.mixingMeasure := by
  exact flatten_apply pd A hA

/-- Flattening is the outcome pushforward of the joint law. -/
theorem flatten_is_marginal (pd : ParametrizedDistribution Θ X) :
    flatten pd = (kyburgJoint pd).map Prod.snd := by
  rw [flatten_eq_snd_kyburgJoint]
  rfl

/-- Integrating a fixed outcome-only utility commutes with mixing. -/
theorem expectation_consistency (pd : ParametrizedDistribution Θ X)
    (U : X → ℝ≥0∞) (hU : Measurable U) :
    ∫⁻ x, U x ∂(flatten pd) = ∫⁻ θ, (∫⁻ x, U x ∂(pd.kernel θ)) ∂pd.mixingMeasure := by
  unfold flatten
  rw [Measure.lintegral_bind pd.kernel.aemeasurable hU.aemeasurable]

/-- Every fixed action has the same outcome-only expected utility after flattening. -/
theorem kyburg_no_advantage {Action : Type*} (pd : ParametrizedDistribution Θ X)
    (U : Action → X → ℝ≥0∞) (hU : ∀ a, Measurable (U a)) (a : Action) :
    ∫⁻ x, U a x ∂(flatten pd) =
    ∫⁻ θ, (∫⁻ x, U a x ∂(pd.kernel θ)) ∂pd.mixingMeasure := by
  exact expectation_consistency pd (U a) (hU a)

section FiniteSpaces

variable (Θ_fin : Type*) [Fintype Θ_fin] [MeasurableSpace Θ_fin]
  [MeasurableSingletonClass Θ_fin]

/-- For a finite parameter space the integral is a weighted sum. -/
theorem kyburg_flattening_finite (pd : ParametrizedDistribution Θ_fin X)
    (A : Set X) (hA : MeasurableSet A) :
    (flatten pd) A = ∑' θ : Θ_fin, (pd.mixingMeasure {θ}) * (pd.kernel θ A) := by
  simp [kyburg_flattening pd A hA, lintegral_fintype, mul_comm]

end FiniteSpaces

/-- The definition agrees with Giry bind. -/
theorem flatten_is_monad_multiplication (pd : ParametrizedDistribution Θ X) :
    flatten pd = pd.mixingMeasure.bind pd.kernel := by
  rfl  -- This is definitional

end Mettapedia.ProbabilityTheory.HigherOrderProbability
