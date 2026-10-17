import Mettapedia.UniversalAI.UniversalHyperprior.DyadicRealization
import Mathlib.Algebra.Field.ZMod

/-!
# Accuracy-sensitive dyadic convergence and an impossible posterior interface

A dyadic value cannot equal one third.  Nevertheless, the Normal-Normal model
with prior mean zero, prior variance one, observation variance two and one
observation equal to one has posterior mean one third.  Both the context and
the sufficient statistics are represented exactly by constant dyadic inputs.

A fixed function from context/evidence to a single dyadic result therefore
cannot satisfy the input-convergence contract quantified in
`no_precision_free_posterior_method`: constant exact input sequences satisfy
all its premises, but the constant result cannot converge to one third.

The positive result uses an explicit, increasing accuracy parameter.  The
actual fixed-grid `DyadicValue.div` converges (by `DyadicValue.tendsto_div`) to real division, including for
signed divisors, along any filter whose precision tends to infinity.  This
establishes the arithmetic interface; it does not provide an implementation
or correctness theorem for posterior means or log marginal likelihoods.

Only the completed realization layer and Mathlib are imported.  The unfinished
posterior arithmetic and approximation-bound modules are not used.
-/

set_option autoImplicit false
namespace Mettapedia.UniversalAI.UniversalHyperprior.Dyadic.ApproximationControls
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGamma
open Mettapedia.UniversalAI.UniversalHyperprior

theorem dyadic_toReal_ne_third (value : DyadicValue) : value.toReal ≠ 1 / 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro equal
  have denominator_ne : (2 : ℝ) ^ value.denom_pow ≠ 0 := pow_ne_zero _ (by norm_num)
  have real_equation : (3 : ℝ) * value.num = (2 : ℝ) ^ value.denom_pow := by
    unfold DyadicValue.toReal at equal
    have cleared := (div_eq_iff denominator_ne).mp equal
    linarith
  have integer_equation : (3 : ℤ) * value.num = (2 : ℤ) ^ value.denom_pow := by
    exact_mod_cast real_equation
  have residue := congrArg (fun integer : ℤ => (integer : ZMod 3)) integer_equation
  push_cast at residue
  have three_zero : (3 : ZMod 3) = 0 := by decide
  rw [three_zero, zero_mul] at residue
  exact pow_ne_zero value.denom_pow (by decide : (2 : ZMod 3) ≠ 0) residue.symm

def exactContext : DyadicContext := DyadicContext.atK 0 2 0 (by decide)

def exactEvidence : DyadicEvidence := ⟨1, 1, 0, 0, 0⟩

def semanticContext : NormalNormalContext where
  μ₀ := 0
  τ₀_sq := 1
  σ_sq := 2
  τ₀_sq_pos := by norm_num
  σ_sq_pos := by norm_num

noncomputable def semanticEvidence : NormalGammaEvidence := NormalGammaEvidence.single 1

theorem exact_context_mean : exactContext.toReal.μ₀ = semanticContext.μ₀ := by
  norm_num [exactContext, DyadicContext.atK, DyadicContext.toReal, semanticContext]

theorem exact_context_prior_variance : exactContext.toReal.τ₀_sq = semanticContext.τ₀_sq := by
  norm_num [exactContext, DyadicContext.atK, DyadicContext.toReal, semanticContext]

theorem exact_context_observation_variance : exactContext.toReal.σ_sq = semanticContext.σ_sq := by
  norm_num [exactContext, DyadicContext.atK, DyadicContext.toReal, semanticContext]

theorem exact_evidence_mean : exactEvidence.toMean.toReal = semanticEvidence.toMean := by
  norm_num [exactEvidence, DyadicEvidence.toMean, DyadicValue.toReal,
    semanticEvidence, NormalGammaEvidence.single, NormalGammaEvidence.toMean]

theorem exact_evidence_count : exactEvidence.n = semanticEvidence.n := rfl

theorem exact_context_realization : exactContext.toReal = semanticContext := by
  norm_num [exactContext, DyadicContext.atK, DyadicContext.toReal, semanticContext]

theorem exact_evidence_realization : exactEvidence.toReal = semanticEvidence := by
  ext <;> norm_num [exactEvidence, DyadicEvidence.toReal, semanticEvidence,
    NormalGammaEvidence.single]

theorem exact_posterior_third : posteriorMean semanticContext semanticEvidence = 1 / 3 := by
  norm_num [posteriorMean, posteriorPrecision, semanticContext, semanticEvidence,
    NormalGammaEvidence.single, NormalNormalContext.priorPrecision,
    NormalNormalContext.obsPrecision]

theorem no_constant_output_convergence
    (compute : DyadicContext → DyadicEvidence → DyadicValue) :
    ¬ Filter.Tendsto (fun _ : ℕ => (compute exactContext exactEvidence).toReal)
      Filter.atTop (nhds (posteriorMean semanticContext semanticEvidence)) := by
  intro converges
  have limit_equal := tendsto_nhds_unique tendsto_const_nhds converges
  exact dyadic_toReal_ne_third (compute exactContext exactEvidence)
    (limit_equal.trans exact_posterior_third)


/-- Explicitly refining the grid converges to the same non-dyadic target. -/
theorem precision_sensitive_thirds_converge :
    Filter.Tendsto (fun precision : ℕ =>
      (DyadicValue.div DyadicValue.one ⟨3, 0⟩ precision).toReal)
      Filter.atTop (nhds (1 / 3 : ℝ)) := by
  simpa [DyadicValue.one, DyadicValue.toReal] using
    DyadicValue.tendsto_div DyadicValue.one ⟨3, 0⟩ (by decide)

/-- This is the precise shape of the precision-free posterior convergence claim.
The admissible constant sequence above refutes it for every proposed method. -/
theorem no_precision_free_posterior_method
    (compute : DyadicContext → DyadicEvidence → DyadicValue) :
    ¬ (∀ (contextLimit : NormalNormalContext) (evidenceLimit : NormalGammaEvidence)
      (contextSequence : ℕ → DyadicContext) (evidenceSequence : ℕ → DyadicEvidence),
      (∀ n, |(contextSequence n).toReal.μ₀ - contextLimit.μ₀| ≤ (2 : ℝ) ^ (-n : ℤ)) →
      (∀ n, (contextSequence n).toReal.τ₀_sq = contextLimit.τ₀_sq) →
      (∀ n, |(contextSequence n).toReal.σ_sq - contextLimit.σ_sq| ≤ (2 : ℝ) ^ (-n : ℤ)) →
      (∀ n, |(evidenceSequence n).toMean.toReal - evidenceLimit.toMean| ≤
        (2 : ℝ) ^ (-n : ℤ)) →
      (∀ n, (evidenceSequence n).n = evidenceLimit.n) →
      evidenceLimit.n ≠ 0 →
      Filter.Tendsto (fun n => (compute (contextSequence n) (evidenceSequence n)).toReal)
        Filter.atTop (nhds (posteriorMean contextLimit evidenceLimit))) := by
  intro universal
  apply no_constant_output_convergence compute
  apply universal semanticContext semanticEvidence (fun _ => exactContext) (fun _ => exactEvidence)
  · intro n
    rw [exact_context_mean, sub_self, abs_zero]
    exact (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le
  · intro _; exact exact_context_prior_variance
  · intro n
    rw [exact_context_observation_variance, sub_self, abs_zero]
    exact (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le
  · intro n
    rw [exact_evidence_mean, sub_self, abs_zero]
    exact (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le
  · intro _; exact exact_evidence_count
  · norm_num [semanticEvidence, NormalGammaEvidence.single]

end Mettapedia.UniversalAI.UniversalHyperprior.Dyadic.ApproximationControls
