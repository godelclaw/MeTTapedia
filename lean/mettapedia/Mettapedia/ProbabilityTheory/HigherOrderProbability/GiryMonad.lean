import Mettapedia.ProbabilityTheory.HigherOrderProbability.Basic
import Mettapedia.ProbabilityTheory.HigherOrderProbability.KyburgFlattening
import Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Basic

/-!
# Flattening and the Giry monad

Flattening is the supplied mixing measure bound through its kernel. Mathlib's
unit and associativity laws apply to these actual measures. The right unit is
the Dirac identity kernel, not a constant kernel. These laws establish composition;
they establish neither uniqueness of monad multiplication nor preservation of
latent information, evidence sufficiency, or a characterization of exchangeability.

References: Giry (1982), *A categorical approach to probability theory*;
Kyburg (1988), *Higher Order Probabilities*.
-/

namespace Mettapedia.ProbabilityTheory.HigherOrderProbability

open MeasureTheory _root_.ProbabilityTheory ParametrizedDistribution
open ProbabilityTheory.Kernel
open scoped ENNReal

/-- The definition agrees with Giry bind. -/
theorem flatten_is_bind {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (pd : ParametrizedDistribution Θ X) :
    flatten pd = pd.mixingMeasure.bind pd.kernel := by
  rfl

/-- Equivalently, flattening is join after mapping the supplied kernel. -/
theorem flatten_is_join {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (pd : ParametrizedDistribution Θ X) :
    flatten pd = Measure.join (pd.mixingMeasure.map pd.kernel) := by
  rw [flatten_is_bind]
  rfl  -- bind is defined as join ∘ map

/-- A Dirac mixing law selects the kernel row at its parameter. -/
theorem flatten_left_identity {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (kernel : Θ → Measure X) (hkernel : Measurable kernel)
    (hprob : ∀ θ, IsProbabilityMeasure (kernel θ))
    (θ : Θ) :
    let κ : ProbabilityTheory.Kernel Θ X := ProbabilityTheory.Kernel.mk kernel hkernel
    have hmarkov : ProbabilityTheory.IsMarkovKernel κ :=  { isProbabilityMeasure := hprob }
    flatten ⟨κ, hmarkov, Measure.dirac θ, inferInstance⟩ = kernel θ := by
  simp only [flatten_is_bind]
  rw [ProbabilityTheory.Kernel.coe_mk]
  exact Measure.dirac_bind hkernel θ

/-- The Dirac identity kernel returns the original mixing law. -/
theorem flatten_right_identity {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ] :
    let κ := ProbabilityTheory.Kernel.deterministic id measurable_id
    have hmarkov : ProbabilityTheory.IsMarkovKernel κ := {
      isProbabilityMeasure := fun a => by
        rw [ProbabilityTheory.Kernel.deterministic_apply]
        infer_instance
    }
    flatten ⟨κ, hmarkov, μ, inferInstance⟩ = μ := by
  simp only [flatten_is_bind]
  exact Measure.bind_dirac

/-- Binding after flattening equals binding inside each component before mixing. -/
theorem flatten_associativity {Θ X Y : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y]
    (pd : ParametrizedDistribution Θ X)
    (k : X → Measure Y)
    (hk : AEMeasurable k (flatten pd)) :
    (flatten pd).bind k = pd.mixingMeasure.bind (fun θ => (pd.kernel θ).bind k) := by
  rw [flatten_is_bind]
  exact Measure.bind_bind pd.kernel.aemeasurable hk

/-- The kernel specialization supplies the measurability premise automatically. -/
theorem flatten_associativity_kernel {Θ X Y : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y]
    (pd : ParametrizedDistribution Θ X)
    (k : ProbabilityTheory.Kernel X Y) :
    (flatten pd).bind k = pd.mixingMeasure.bind (fun θ => (pd.kernel θ).bind k) := by
  exact flatten_associativity (pd := pd) (k := k) k.aemeasurable

/-- Fixed outcome-only expectation consistency, reused from the flattening theorem. -/
theorem kyburg_no_advantage_via_monad {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (pd : ParametrizedDistribution Θ X)
    (U : X → ℝ≥0∞) (hU : Measurable U) :
    ∫⁻ x, U x ∂(flatten pd) =
    ∫⁻ θ, (∫⁻ x, U x ∂(pd.kernel θ)) ∂pd.mixingMeasure := by
  exact expectation_consistency pd U hU

/-- The Bernoulli-mixture bridge specializes the same flattening operation. -/
theorem bernoulliMixture_flatten_apply_singleton
    (M : Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti.BernoulliMixture) (n : ℕ) (xs : Fin n → Bool) :
    (ParametrizedDistribution.flatten (DeFinettiConnection.pd M n)) {xs} =
      ENNReal.ofReal (M.prob xs) := by
  simpa using DeFinettiConnection.flatten_apply_singleton (M := M) (n := n) (xs := xs)

end Mettapedia.ProbabilityTheory.HigherOrderProbability
