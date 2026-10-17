/-
# A Countable Normal-Normal Hyperprior Mixture

This file studies a fixed family of centered Normal priors with variances
`2 ^ k`, indexed by integers, and positive geometric mixing weights.  The
observation variance is known.  A hyperprior represents uncertainty about the
prior scale; this construction does not assert that the scale is structurally
unidentifiable or that empirical Bayes is inherently invalid.

The supplied Normal-Normal closed-form expressions are treated as definitions.
The file proves summability, a positive partition function, normalized posterior
weights, componentwise log-loss dominance and shrinkage of the mixture mean.
It does not derive these expressions from a Gaussian likelihood integral or
prove the underlying conjugacy theorem.

The extended nonnegative variance formula retains infinite moments.  Positive
observation count gives finite component and between-mean moments.  At zero
count the expected component variance diverges, so returning a real-valued
`tsum` would incorrectly conceal the infinite uncertainty.

Dominance compares this specified mixture with each member of its fixed family;
it is not a universality or optimality theorem over all statistical models.

## References

- `UniversalPrediction/MarkovHyperpriorMixture.lean` (the separate prefix-measure mixture)
- `PLN/Bridges/ProbabilityTheory/EvidenceNormalGamma.lean` (sufficient statistics)
- Murphy, "Conjugate Bayesian analysis of the Gaussian distribution" (2007)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic
import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGamma

namespace Mettapedia.UniversalAI.UniversalHyperprior

open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGamma
open scoped BigOperators

/-! ## Normal-Normal Context with Known Variance

For single-level inference where σ² is known, we need only three parameters:
- μ₀: prior mean (typically 0)
- τ₀²: prior variance on μ
- σ²: known observation variance
-/

/-- Context for Normal-Normal inference with known observation variance σ².

This is simpler than the full Normal-Gamma context because we don't need to
estimate the observation variance - it's assumed known.

The prior on μ is: μ ~ N(μ₀, τ₀²)
The likelihood is: xᵢ | μ ~ N(μ, σ²) -/
structure NormalNormalContext where
  /-- Prior mean for μ -/
  μ₀ : ℝ
  /-- Prior variance for μ. -/
  τ₀_sq : ℝ
  /-- Known observation variance -/
  σ_sq : ℝ
  /-- Prior variance is positive -/
  τ₀_sq_pos : 0 < τ₀_sq
  /-- Observation variance is positive -/
  σ_sq_pos : 0 < σ_sq

namespace NormalNormalContext

/-- Prior precision: κ₀ = 1/τ₀² -/
noncomputable def priorPrecision (ctx : NormalNormalContext) : ℝ := 1 / ctx.τ₀_sq

theorem priorPrecision_pos (ctx : NormalNormalContext) : 0 < ctx.priorPrecision := by
  unfold priorPrecision
  exact one_div_pos.mpr ctx.τ₀_sq_pos

/-- Observation precision per sample: 1/σ² -/
noncomputable def obsPrecision (ctx : NormalNormalContext) : ℝ := 1 / ctx.σ_sq

theorem obsPrecision_pos (ctx : NormalNormalContext) : 0 < ctx.obsPrecision := by
  unfold obsPrecision
  exact one_div_pos.mpr ctx.σ_sq_pos

end NormalNormalContext

/-! ## Posterior Computations

For Normal-Normal conjugate model:
- Prior: μ ~ N(μ₀, τ₀²)
- Likelihood: x₁,...,xₙ | μ ~ N(μ, σ²) iid
- Posterior: μ | x₁,...,xₙ ~ N(μₙ, τₙ²)

Where:
- τₙ² = 1/(1/τ₀² + n/σ²)  (posterior variance)
- μₙ = τₙ² · (μ₀/τ₀² + n·xbar/σ²)  (posterior mean)
-/

/-- Posterior precision: 1/τₙ² = 1/τ₀² + n/σ² -/
noncomputable def posteriorPrecision (ctx : NormalNormalContext) (n : ℕ) : ℝ :=
  ctx.priorPrecision + n * ctx.obsPrecision

theorem posteriorPrecision_pos (ctx : NormalNormalContext) (n : ℕ) :
    0 < posteriorPrecision ctx n := by
  unfold posteriorPrecision
  have h1 := ctx.priorPrecision_pos
  have h2 : 0 ≤ (n : ℝ) * ctx.obsPrecision := by
    apply mul_nonneg (Nat.cast_nonneg n) (le_of_lt ctx.obsPrecision_pos)
  linarith

/-- Posterior variance: τₙ² = 1/(1/τ₀² + n/σ²) -/
noncomputable def posteriorVariance (ctx : NormalNormalContext) (n : ℕ) : ℝ :=
  1 / posteriorPrecision ctx n

theorem posteriorVariance_pos (ctx : NormalNormalContext) (n : ℕ) :
    0 < posteriorVariance ctx n := by
  unfold posteriorVariance
  exact one_div_pos.mpr (posteriorPrecision_pos ctx n)

/-- Posterior mean: μₙ = (μ₀/τ₀² + Σxᵢ/σ²) / (1/τ₀² + n/σ²) -/
noncomputable def posteriorMean (ctx : NormalNormalContext) (ev : NormalGammaEvidence) : ℝ :=
  if ev.n = 0 then ctx.μ₀
  else (ctx.priorPrecision * ctx.μ₀ + ev.sum * ctx.obsPrecision) / posteriorPrecision ctx ev.n

/-- The posterior mean is a precision-weighted average of prior mean and sample mean -/
theorem posteriorMean_weighted_avg (ctx : NormalNormalContext) (ev : NormalGammaEvidence)
    (hn : ev.n ≠ 0) :
    posteriorMean ctx ev =
      (ctx.priorPrecision / posteriorPrecision ctx ev.n) * ctx.μ₀ +
      ((ev.n : ℝ) * ctx.obsPrecision / posteriorPrecision ctx ev.n) * ev.toMean := by
  unfold posteriorMean NormalGammaEvidence.toMean
  simp only [hn, ↓reduceIte]
  have hpost_pos := posteriorPrecision_pos ctx ev.n
  have hn_pos : 0 < (ev.n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  unfold NormalNormalContext.obsPrecision
  field_simp [ne_of_gt hpost_pos, ne_of_gt hn_pos]

/-! ## Context Family: τ₀² = 2^k for k ∈ ℤ

The mixture represents uncertainty over a specified dyadic grid of prior variances.
The grid contains arbitrarily small and arbitrarily large values; it does not
contain every positive real variance.
-/

/-- Context with τ₀² = 2^k -/
noncomputable def contextAtK (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq) : NormalNormalContext where
  μ₀ := 0  -- Centered prior
  τ₀_sq := (2 : ℝ) ^ k
  σ_sq := σ_sq
  τ₀_sq_pos := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact zpow_pos h2 k
  σ_sq_pos := hσ

/-- The context family spans τ₀² from nearly 0 to arbitrarily large -/
theorem contextAtK_τ₀_sq (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq) :
    (contextAtK k σ_sq hσ).τ₀_sq = (2 : ℝ) ^ k := rfl

/-! ## Integer Geometric Weights

For k ∈ ℤ, we use unnormalized weights u(k) = 2^{-(|k|+1)} which sum to 3/2:
  Σ_{k∈ℤ} u(k) = 2^{-1} + 2·Σ_{n≥1} 2^{-(n+1)}
               = 1/2 + 2·(1/4 + 1/8 + ...)
               = 1/2 + 2·(1/2) = 3/2

The normalized weights are w(k) = u(k) / (3/2) = (2/3) · 2^{-(|k|+1)}.

The negative log weight is bounded in `weight_codelength_bound`.  No explicit
prefix code construction is supplied here.
-/

/-- Unnormalized weight: 2^{-(|k|+1)} -/
noncomputable def unnormWeight (k : ℤ) : ℝ := (2 : ℝ) ^ (-(|k| + 1 : ℤ))

theorem unnormWeight_pos (k : ℤ) : 0 < unnormWeight k := by
  unfold unnormWeight
  have h2 : (0 : ℝ) < 2 := by norm_num
  exact zpow_pos h2 _

/-- Helper: |n| = n for n : ℕ when cast to ℤ -/
theorem abs_natCast (n : ℕ) : |↑n| = (n : ℤ) := abs_of_nonneg (Int.natCast_nonneg n)

/-- Helper: |(-(n+1))| = n+1 -/
theorem abs_neg_succ (n : ℕ) : |-(↑n + 1 : ℤ)| = n + 1 := by
  rw [abs_neg]
  exact abs_of_pos (by linarith [Int.natCast_nonneg n])

/-- The unnormalized weights sum to 3/2.

Proof sketch: Split into k≥0 and k<0 using tsum_of_nat_of_neg_add_one:
- k≥0: Σ_{n:ℕ} 2^{-(n+1)} = 1/2 + 1/4 + ... = 1 (geometric series)
- k<0: Σ_{n:ℕ} 2^{-(n+2)} = 1/4 + 1/8 + ... = 1/2 (geometric series)
Total: 1 + 1/2 = 3/2

The technical details involve showing summability and using tsum_geometric_two. -/
theorem tsum_unnormWeight_eq_threeHalves : (∑' k : ℤ, unnormWeight k) = 3/2 := by
  -- Reduce to geometric series by splitting ℤ into nonnegative and negative parts.
  -- We intentionally keep this proof self-contained and avoid ENNReal/toReal conversion.
  have zpow_split_nat (n : ℕ) : (2 : ℝ) ^ (-1 + -(n : ℤ)) = (1 : ℝ) / 2 / 2 ^ n := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    rw [zpow_add₀ h2]
    simp [div_eq_mul_inv, zpow_natCast]

  have unnormWeight_nat (n : ℕ) : unnormWeight (n : ℤ) = (1 : ℝ) / 2 / 2 ^ n := by
    unfold unnormWeight
    simp [zpow_split_nat]

  have abs_neg_one_add_neg_natCast (n : ℕ) : |(-1 : ℤ) + -(n : ℤ)| = (n + 1 : ℤ) := by
    have : (-1 : ℤ) + -(n : ℤ) = -(↑n + 1 : ℤ) := by omega
    rw [this]
    simpa [Int.natCast_succ] using (abs_neg_succ n)

  have unnormWeight_negSucc (n : ℕ) :
      unnormWeight (-(n + 1 : ℤ)) = (1/2 : ℝ) / 2 / 2 ^ n := by
    unfold unnormWeight
    have hk : (-(n + 1 : ℤ)) = (-1 : ℤ) + -(n : ℤ) := by omega
    rw [hk]
    have habs : |(-1 : ℤ) + -(n : ℤ)| = (n + 1 : ℤ) := abs_neg_one_add_neg_natCast n
    rw [habs]
    have hexp : (-( (n + 1 : ℤ) + 1)) = (-1 : ℤ) + (-((n+1 : ℕ) : ℤ)) := by omega
    rw [hexp]
    have hz := zpow_split_nat (n + 1)
    have hz' : (2 : ℝ) ^ (-1 + -((n+1 : ℕ) : ℤ)) = (2 : ℝ)⁻¹ / 2 ^ (n+1) := by
      simpa [div_eq_mul_inv] using hz
    have hR : (2 : ℝ)⁻¹ / 2 ^ (n+1) = (1/2 : ℝ) / 2 / 2 ^ n := by
      ring
    exact hz'.trans hR

  have hs_pos : Summable (fun n : ℕ ↦ unnormWeight (n : ℤ)) := by
    have : Summable (fun n : ℕ ↦ (1 : ℝ) / 2 / 2 ^ n) := summable_geometric_two' (a := (1 : ℝ))
    exact (summable_congr unnormWeight_nat).2 this

  have hs_neg : Summable (fun n : ℕ ↦ unnormWeight (-(n + 1 : ℤ))) := by
    have : Summable (fun n : ℕ ↦ (1/2 : ℝ) / 2 / 2 ^ n) :=
      summable_geometric_two' (a := (1/2 : ℝ))
    exact (summable_congr unnormWeight_negSucc).2 this

  -- Split the ℤ-sum.
  rw [tsum_of_nat_of_neg_add_one hs_pos hs_neg]

  have tsum_pos : (∑' n : ℕ, unnormWeight (n : ℤ)) = (1 : ℝ) := by
    calc
      (∑' n : ℕ, unnormWeight (n : ℤ)) = ∑' n : ℕ, (1 : ℝ) / 2 / 2 ^ n := by
        simpa using (tsum_congr unnormWeight_nat)
      _ = (1 : ℝ) := by
        simpa using (tsum_geometric_two' (a := (1 : ℝ)))

  have tsum_neg : (∑' n : ℕ, unnormWeight (-(n + 1 : ℤ))) = (1/2 : ℝ) := by
    calc
      (∑' n : ℕ, unnormWeight (-(n + 1 : ℤ))) = ∑' n : ℕ, (1/2 : ℝ) / 2 / 2 ^ n := by
        simpa using (tsum_congr unnormWeight_negSucc)
      _ = (1/2 : ℝ) := by
        simpa using (tsum_geometric_two' (a := (1/2 : ℝ)))

  -- Conclude.
  rw [tsum_pos, tsum_neg]
  norm_num

/-- Normalization constant for weights: Z = 3/2 -/
noncomputable def normConstant : ℝ := 3/2

theorem normConstant_pos : 0 < normConstant := by norm_num [normConstant]

/-- Normalized weight: w(k) = 2^{-(|k|+1)} / (3/2) -/
noncomputable def weight (k : ℤ) : ℝ := unnormWeight k / normConstant

theorem weight_pos (k : ℤ) : 0 < weight k := by
  unfold weight
  exact div_pos (unnormWeight_pos k) normConstant_pos

/-- The normalized weights sum to 1 -/
theorem tsum_weight_eq_one : (∑' k : ℤ, weight k) = 1 := by
  unfold weight normConstant
  rw [tsum_div_const, tsum_unnormWeight_eq_threeHalves]
  norm_num

/-- Normalization excludes the nonsummable `tsum = 0` convention. -/
theorem summable_weight : Summable weight := by
  by_contra notSummable
  have zero := tsum_eq_zero_of_not_summable notSummable
  rw [tsum_weight_eq_one] at zero
  norm_num at zero

/-! ## Log Marginal Likelihood

The supplied formula allows a general prior μ ~ N(μ₀, τ₀²) and data
x₁,...,xₙ ~ N(μ, σ²):

log P(x₁,...,xₙ | τ₀², σ²) = -n/2 log(2π) - n/2 log(σ²)
                            - 1/2 log(1 + n·τ₀²/σ²)
                            - (SS + n·(xbar-μ₀)²·σ²/(σ² + n·τ₀²)) / (2σ²)

Here SS is the reconstructed sum of squared deviations.  This expression is
a model definition, not an integral identity established in this file.
-/

/-- Log marginal likelihood under a specific context -/
noncomputable def logMarginalLikelihood (ctx : NormalNormalContext)
    (ev : NormalGammaEvidence) : ℝ :=
  if ev.n = 0 then 0
  else
    let n : ℝ := ev.n;
    let xbar := ev.sum / n;
    let ss := ev.sumSquaredDeviations;
    let ratio := n * ctx.τ₀_sq / ctx.σ_sq;
    let shrinkage := ctx.σ_sq / (ctx.σ_sq + n * ctx.τ₀_sq);
    let log2pi_term := n / 2 * Real.log (2 * Real.pi);
    let logsigma_term := n / 2 * Real.log ctx.σ_sq;
    let logdet_term := (1 / 2) * Real.log (1 + ratio);
    let quad_term := (ss + n * shrinkage * (xbar - ctx.μ₀)^2) / (2 * ctx.σ_sq);
    -(log2pi_term + logsigma_term + logdet_term + quad_term)

/-- The Gaussian base factor bounds the supplied log-likelihood formula uniformly
over prior means and variances.  Its exponential need not be at most one. -/
theorem logMarginalLikelihood_le_base (ctx : NormalNormalContext)
    (ev : NormalGammaEvidence) :
    logMarginalLikelihood ctx ev ≤
      -((ev.n : ℝ) / 2 * Real.log (2 * Real.pi) +
        (ev.n : ℝ) / 2 * Real.log ctx.σ_sq) := by
  by_cases hn : ev.n = 0
  · simp [logMarginalLikelihood, hn]
  have count_nonneg : (0 : ℝ) ≤ ev.n := Nat.cast_nonneg _
  have variance_nonneg : 0 ≤ ev.sumSquaredDeviations := by
    unfold NormalGammaEvidence.sumSquaredDeviations
    simp only [hn, ↓reduceIte]
    have count_pos : (0 : ℝ) < ev.n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have constraint := ev.cauchy_schwarz
    have : ev.sum ^ 2 / ev.n ≤ ev.sumSq := by
      rw [div_le_iff₀ count_pos]
      nlinarith [constraint]
    linarith
  have ratio_nonneg : 0 ≤ (ev.n : ℝ) * ctx.τ₀_sq / ctx.σ_sq :=
    div_nonneg (mul_nonneg count_nonneg ctx.τ₀_sq_pos.le) ctx.σ_sq_pos.le
  have logdet_nonneg : 0 ≤ (1 / 2 : ℝ) *
      Real.log (1 + (ev.n : ℝ) * ctx.τ₀_sq / ctx.σ_sq) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have shrinkage_nonneg : 0 ≤ ctx.σ_sq / (ctx.σ_sq + ev.n * ctx.τ₀_sq) :=
    div_nonneg ctx.σ_sq_pos.le
      (add_nonneg ctx.σ_sq_pos.le (mul_nonneg count_nonneg ctx.τ₀_sq_pos.le))
  have quadratic_nonneg :
      0 ≤ (ev.sumSquaredDeviations + ev.n *
        (ctx.σ_sq / (ctx.σ_sq + ev.n * ctx.τ₀_sq)) * (ev.sum / ev.n - ctx.μ₀) ^ 2) /
        (2 * ctx.σ_sq) :=
    div_nonneg (add_nonneg variance_nonneg
      (mul_nonneg (mul_nonneg count_nonneg shrinkage_nonneg) (sq_nonneg _)))
      (mul_nonneg (by norm_num) ctx.σ_sq_pos.le)
  simp only [logMarginalLikelihood, hn, ↓reduceIte]
  linarith

/-- The context likelihoods are dominated by a fixed multiple of the summable
prior weights. -/
theorem summable_weighted_likelihood (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) :
    Summable (fun k : ℤ => weight k *
      Real.exp (logMarginalLikelihood (contextAtK k σ_sq hσ) ev)) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (weight_pos k).le (Real.exp_pos _).le) ?_
    (summable_weight.mul_right (Real.exp (-((ev.n : ℝ) / 2 * Real.log (2 * Real.pi) +
      (ev.n : ℝ) / 2 * Real.log σ_sq))))
  intro k
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (logMarginalLikelihood_le_base (contextAtK k σ_sq hσ) ev))
    (weight_pos k).le

/-! ## Mixture Posterior

The mixture posterior combines posteriors from all contexts weighted by
their posterior probabilities (prior weight × likelihood).

Mixture mean: E[μ | data] = Σ_k w_k · E[μ | data, C_k]
Mixture var:  Var[μ | data] = E[Var[μ|C]] + Var[E[μ|C]]  (law of total variance)
-/

/-- Posterior weight for context k (unnormalized log scale) -/
noncomputable def logPosteriorWeight (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ :=
  Real.log (weight k) + logMarginalLikelihood (contextAtK k σ_sq hσ) ev

/-- Exponentiating the log weight recovers prior weight times likelihood. -/
theorem exp_logPosteriorWeight (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) :
    Real.exp (logPosteriorWeight k σ_sq hσ ev) =
      weight k * Real.exp (logMarginalLikelihood (contextAtK k σ_sq hσ) ev) := by
  rw [logPosteriorWeight, Real.exp_add, Real.exp_log (weight_pos k)]

theorem summable_exp_logPosteriorWeight (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) :
    Summable (fun k : ℤ => Real.exp (logPosteriorWeight k σ_sq hσ ev)) := by
  simpa only [exp_logPosteriorWeight] using summable_weighted_likelihood σ_sq hσ ev

/-- The partition function is finite as a summable real series and strictly
positive because it contains a positive term. -/
theorem posteriorPartition_pos (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) :
    0 < ∑' k : ℤ, Real.exp (logPosteriorWeight k σ_sq hσ ev) := by
  exact (Real.exp_pos (logPosteriorWeight 0 σ_sq hσ ev)).trans_le
    ((summable_exp_logPosteriorWeight σ_sq hσ ev).le_tsum 0
      (fun k _ => (Real.exp_pos _).le))

/-- Normalized posterior weight for context k -/
noncomputable def posteriorWeight (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ :=
  let logZ := Real.log (∑' k', Real.exp (logPosteriorWeight k' σ_sq hσ ev))
  Real.exp (logPosteriorWeight k σ_sq hσ ev - logZ)

/-- Posterior weights are positive (since they're exponentials) -/
theorem posteriorWeight_pos (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq) (ev : NormalGammaEvidence) :
    0 < posteriorWeight k σ_sq hσ ev := by
  unfold posteriorWeight
  exact Real.exp_pos _

/-- The normalized exponential is an ordinary ratio with a positive partition function. -/
theorem posteriorWeight_eq_exp_div (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) :
    posteriorWeight k σ_sq hσ ev = Real.exp (logPosteriorWeight k σ_sq hσ ev) /
      (∑' j : ℤ, Real.exp (logPosteriorWeight j σ_sq hσ ev)) := by
  unfold posteriorWeight
  rw [Real.exp_sub, Real.exp_log (posteriorPartition_pos σ_sq hσ ev)]

theorem summable_posteriorWeight (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) :
    Summable (fun k : ℤ => posteriorWeight k σ_sq hσ ev) := by
  simpa only [posteriorWeight_eq_exp_div] using
    (summable_exp_logPosteriorWeight σ_sq hσ ev).div_const
      (∑' j : ℤ, Real.exp (logPosteriorWeight j σ_sq hσ ev))

/-- Posterior weights sum to one; no positivity or convergence premise is added. -/
theorem tsum_posteriorWeight_eq_one (σ_sq : ℝ) (hσ : 0 < σ_sq) (ev : NormalGammaEvidence) :
    (∑' k : ℤ, posteriorWeight k σ_sq hσ ev) = 1 := by
  simp_rw [posteriorWeight_eq_exp_div]
  rw [tsum_div_const]
  exact div_self (ne_of_gt (posteriorPartition_pos σ_sq hσ ev))

/-- Mixture posterior mean: Σ_k w_k · E[μ | data, C_k] -/
noncomputable def mixturePosteriorMean (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ :=
  ∑' k : ℤ, posteriorWeight k σ_sq hσ ev * posteriorMean (contextAtK k σ_sq hσ) ev

/-- Component posterior variance under context k -/
noncomputable def componentPosteriorVar (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ :=
  posteriorVariance (contextAtK k σ_sq hσ) ev.n

/-- At zero count the likelihood is one and the posterior retains the prior weights. -/
theorem posteriorWeight_of_count_zero (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (empty : ev.n = 0) :
    posteriorWeight k σ_sq hσ ev = weight k := by
  rw [posteriorWeight_eq_exp_div]
  have likelihood_one (j : ℤ) :
      Real.exp (logMarginalLikelihood (contextAtK j σ_sq hσ) ev) = 1 := by
    simp [logMarginalLikelihood, empty]
  simp_rw [exp_logPosteriorWeight, likelihood_one, mul_one]
  rw [tsum_weight_eq_one, div_one]

theorem weight_natCast (n : ℕ) : weight (n : ℤ) = 1 / (3 * (2 : ℝ) ^ n) := by
  unfold weight unnormWeight normConstant
  rw [abs_natCast]
  have exponent : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by omega
  rw [exponent, zpow_neg, zpow_natCast, pow_succ]
  field_simp

theorem componentPosteriorVar_of_count_zero (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (empty : ev.n = 0) :
    componentPosteriorVar k σ_sq hσ ev = (2 : ℝ) ^ k := by
  simp [componentPosteriorVar, posteriorVariance, posteriorPrecision,
    NormalNormalContext.priorPrecision, empty, contextAtK]

/-- Every nonnegative-index variance contribution is the same positive constant. -/
theorem zero_count_variance_tail (n : ℕ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (empty : ev.n = 0) :
    posteriorWeight (n : ℤ) σ_sq hσ ev *
      componentPosteriorVar (n : ℤ) σ_sq hσ ev = 1 / 3 := by
  rw [posteriorWeight_of_count_zero _ _ _ _ empty,
    componentPosteriorVar_of_count_zero _ _ _ _ empty, weight_natCast, zpow_natCast]
  field_simp

/-- The prior has divergent expected component variance; a real-valued `tsum`
would conceal this by taking its default value zero. -/
theorem not_summable_zero_count_variance (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (empty : ev.n = 0) :
    ¬ Summable (fun k : ℤ => posteriorWeight k σ_sq hσ ev *
      componentPosteriorVar k σ_sq hσ ev) := by
  intro summable
  have naturalTail := summable.comp_injective Int.ofNat_injective
  change Summable (fun n : ℕ => posteriorWeight (n : ℤ) σ_sq hσ ev *
    componentPosteriorVar (n : ℤ) σ_sq hσ ev) at naturalTail
  have constantTail : Summable (fun _ : ℕ => (1 / 3 : ℝ)) := by
    simpa only [zero_count_variance_tail _ _ _ _ empty] using naturalTail
  rw [summable_const_iff] at constantTail
  norm_num at constantTail

/-- Positive observation count bounds each component variance uniformly in the prior index. -/
theorem componentPosteriorVar_le_observation (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (positive : ev.n ≠ 0) :
    componentPosteriorVar k σ_sq hσ ev ≤ σ_sq / ev.n := by
  have count_pos : (0 : ℝ) < ev.n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero positive)
  change 1 / posteriorPrecision (contextAtK k σ_sq hσ) ev.n ≤ σ_sq / ev.n
  rw [div_le_div_iff₀ (posteriorPrecision_pos _ _) count_pos]
  have prior_pos := (contextAtK k σ_sq hσ).priorPrecision_pos
  unfold posteriorPrecision NormalNormalContext.obsPrecision
  change 1 * (ev.n : ℝ) ≤ σ_sq *
    ((contextAtK k σ_sq hσ).priorPrecision + ev.n * (1 / σ_sq))
  have cancel : σ_sq * ((ev.n : ℝ) * (1 / σ_sq)) = ev.n := by field_simp
  nlinarith [mul_nonneg hσ.le prior_pos.le]

theorem summable_componentVariance (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (positive : ev.n ≠ 0) :
    Summable (fun k : ℤ => posteriorWeight k σ_sq hσ ev *
      componentPosteriorVar k σ_sq hσ ev) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (posteriorWeight_pos k σ_sq hσ ev).le
      (posteriorVariance_pos _ _).le) ?_
    ((summable_posteriorWeight σ_sq hσ ev).mul_right (σ_sq / ev.n))
  intro k
  exact mul_le_mul_of_nonneg_left
    (componentPosteriorVar_le_observation k σ_sq hσ ev positive)
    (posteriorWeight_pos k σ_sq hσ ev).le

/-- The supplied within/between variance formula in the extended nonnegative reals.
Divergent moments remain infinite instead of becoming the default real `tsum = 0`. -/
noncomputable def mixturePosteriorVar (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ENNReal :=
  (∑' k : ℤ, ENNReal.ofReal (posteriorWeight k σ_sq hσ ev *
    componentPosteriorVar k σ_sq hσ ev)) +
  (∑' k : ℤ, ENNReal.ofReal (posteriorWeight k σ_sq hσ ev *
    (posteriorMean (contextAtK k σ_sq hσ) ev - mixturePosteriorMean σ_sq hσ ev) ^ 2))

/-! ## Dominance Theorem (Universal Hyperprior)

For every fixed index k, the mixture log loss is at most the component log loss
plus `-log (weight k)`.  The logarithms use nats.  The normalized weights include
the factor `2/3`; `weight_codelength_bound` bounds their exact overhead by
`(|k| + 2) * log 2`.
-/

/-- Log mixture marginal likelihood -/
noncomputable def logMixtureMarginalLikelihood (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ :=
  Real.log (∑' k : ℤ, weight k * Real.exp (logMarginalLikelihood (contextAtK k σ_sq hσ) ev))

/-- **Universal Hyperprior Dominance Theorem** (precise form):

The mixture marginal likelihood dominates each component by its weight.

For any k : -ln P_mix(data) ≤ -ln P_k(data) - ln(weight k)

Since weight k = 2^{-(|k|+1)} / (3/2), we have:
  -ln(weight k) = (|k|+1)·ln(2) + ln(3/2) ≤ (|k|+2)·ln(2)

This bound compares the supplied mixture with every fixed variance `2 ^ k`.
It does not establish optimality relative to models outside that family. -/
theorem dominance (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq) (ev : NormalGammaEvidence) :
    -logMixtureMarginalLikelihood σ_sq hσ ev ≤
      -logMarginalLikelihood (contextAtK k σ_sq hσ) ev - Real.log (weight k) := by
  have term_pos : 0 < weight k *
      Real.exp (logMarginalLikelihood (contextAtK k σ_sq hσ) ev) :=
    mul_pos (weight_pos k) (Real.exp_pos _)
  have contains_term := (summable_weighted_likelihood σ_sq hσ ev).le_tsum k
    (fun j _ => mul_nonneg (weight_pos j).le (Real.exp_pos _).le)
  have log_bound := Real.log_le_log term_pos contains_term
  rw [Real.log_mul (ne_of_gt (weight_pos k)) (ne_of_gt (Real.exp_pos _)),
    Real.log_exp] at log_bound
  unfold logMixtureMarginalLikelihood
  linarith

/-- The redundancy (extra nats of information) when using the mixture vs context k. -/
theorem redundancy_bound (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq) (ev : NormalGammaEvidence) :
    -logMixtureMarginalLikelihood σ_sq hσ ev - (-logMarginalLikelihood (contextAtK k σ_sq hσ) ev) ≤
      -Real.log (weight k) := by
  have h := dominance k σ_sq hσ ev
  linarith

/-- Codelength bound: -ln(weight k) ≤ (|k| + 2) · ln(2)

Since weight k = 2^{-(|k|+1)} / (3/2), we have:
  -ln(weight k) = (|k|+1)·ln(2) + ln(3/2) < (|k|+2)·ln(2)

because ln(3/2) ≈ 0.405 < ln(2) ≈ 0.693 -/
theorem weight_codelength_bound (k : ℤ) : -Real.log (weight k) ≤ (|k| + 2) * Real.log 2 := by
  -- The normalized weight contributes the positive overhead log (3/2).
  unfold weight unnormWeight normConstant
  have h2pos : (0:ℝ) < 2 := by norm_num
  have hzpow_pos := zpow_pos h2pos (-(|k| + 1 : ℤ))
  have h32pos : (0:ℝ) < 3/2 := by norm_num
  have h32_lt_2 : (3:ℝ)/2 < 2 := by norm_num
  -- Compute -log(2^{-(|k|+1)} / (3/2))
  -- -log(A/B) = -log A + log B = -(log A - log B)
  -- = -log(2^{-(|k|+1)}) + log(3/2)
  -- = (|k|+1)·log 2 + log(3/2)
  have h_expand : -Real.log (2 ^ (-(|k| + 1 : ℤ)) / (3 / 2)) =
                  (|k| + 1 : ℝ) * Real.log 2 + Real.log (3 / 2) := by
    rw [Real.log_div (ne_of_gt hzpow_pos) (ne_of_gt h32pos)]
    -- -log(2^{-(|k|+1)}) + log(3/2)
    rw [← Real.rpow_intCast 2 (-(|k| + 1))]
    rw [Real.log_rpow h2pos]
    -- -(-(|k|+1)·log 2) + log(3/2) = (|k|+1)·log 2 + log(3/2)
    push_cast
    ring
  rw [h_expand]
  -- Show (|k|+1)·log 2 + log(3/2) ≤ (|k|+2)·log 2
  -- i.e., log(3/2) ≤ log 2
  have h32_le_2 : Real.log (3/2) ≤ Real.log 2 := le_of_lt (Real.log_lt_log h32pos h32_lt_2)
  calc (|k| + 1 : ℝ) * Real.log 2 + Real.log (3 / 2)
      ≤ (|k| + 1 : ℝ) * Real.log 2 + Real.log 2 := by linarith [h32_le_2]
    _ = (|k| + 2 : ℝ) * Real.log 2 := by ring

/-! ## Connection to PLN Modal BinaryEvidence Theory

The separation used by this construction is:

1. **BinaryEvidence** = (n, Σx, Σx²) - context-free sufficient statistics
2. **Context** = (μ₀, τ₀², σ²) - interpretation parameters
3. **Universal Hyperprior** = mixture over {(0, 2^k, σ²) : k ∈ ℤ}

The same sufficient statistics can be interpreted under multiple prior scales.
This is a mathematical mixture construction; no deployed PLN implementation is
verified here.
-/

/-- The supplied mixture formulas return a real mean and extended standard deviation. -/
noncomputable def plnUniversalHyperpriorInference (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) : ℝ × ENNReal :=
  let mean := mixturePosteriorMean σ_sq hσ ev
  let var := mixturePosteriorVar σ_sq hσ ev
  (mean, var ^ (1 / 2 : ℝ))

/-- For μ₀ = 0, posterior mean magnitude is bounded by sample mean -/
theorem posteriorMean_abs_le_sampleMean (k : ℤ) (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (hn : ev.n ≠ 0) :
    |posteriorMean (contextAtK k σ_sq hσ) ev| ≤ |ev.toMean| := by
  -- Use `let` (not `have`) so definitional reduction works smoothly.
  let ctx := contextAtK k σ_sq hσ
  -- μ₀ = 0 for contextAtK
  have hμ₀ : ctx.μ₀ = 0 := by rfl
  -- Posterior mean is a weighted average with coefficient ∈ [0, 1]
  rw [posteriorMean_weighted_avg _ _ hn, hμ₀]
  simp only [mul_zero, zero_add]
  -- Now: |coeff * toMean| ≤ |toMean| where coeff = n * obsPrecision / posteriorPrecision ∈ [0, 1]
  have hcoeff : 0 ≤ (ev.n : ℝ) * ctx.obsPrecision / posteriorPrecision ctx ev.n ∧
                    (ev.n : ℝ) * ctx.obsPrecision / posteriorPrecision ctx ev.n ≤ 1 := by
    constructor
    · apply div_nonneg
      · apply mul_nonneg; exact Nat.cast_nonneg _; exact le_of_lt ctx.obsPrecision_pos
      · exact le_of_lt (posteriorPrecision_pos ctx ev.n)
    · -- n * obsPrecision ≤ priorPrecision + n * obsPrecision = posteriorPrecision
      have h : (ev.n : ℝ) * ctx.obsPrecision ≤ posteriorPrecision ctx ev.n := by
        unfold posteriorPrecision
        linarith [le_of_lt ctx.priorPrecision_pos]
      exact div_le_one_of_le₀ h (le_of_lt (posteriorPrecision_pos ctx ev.n))
  rw [abs_mul]
  calc |((ev.n : ℝ) * ctx.obsPrecision / posteriorPrecision ctx ev.n)| * |ev.toMean|
       = ((ev.n : ℝ) * ctx.obsPrecision / posteriorPrecision ctx ev.n) * |ev.toMean| := by
          rw [abs_of_nonneg hcoeff.1]
     _ ≤ 1 * |ev.toMean| := by apply mul_le_mul_of_nonneg_right hcoeff.2 (abs_nonneg _)
     _ = |ev.toMean| := one_mul _

theorem summable_posteriorMean (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) :
    Summable (fun k : ℤ => posteriorWeight k σ_sq hσ ev *
      posteriorMean (contextAtK k σ_sq hσ) ev) := by
  by_cases empty : ev.n = 0
  · simp [posteriorMean, empty, contextAtK]
  refine Summable.of_norm_bounded
    ((summable_posteriorWeight σ_sq hσ ev).mul_right |ev.toMean|) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (posteriorWeight_pos k σ_sq hσ ev)]
  exact mul_le_mul_of_nonneg_left
    (posteriorMean_abs_le_sampleMean k σ_sq hσ ev empty)
    (posteriorWeight_pos k σ_sq hσ ev).le

theorem summable_centeredMean_square (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (center : ℝ) (positive : ev.n ≠ 0) :
    Summable (fun k : ℤ => posteriorWeight k σ_sq hσ ev *
      (posteriorMean (contextAtK k σ_sq hσ) ev - center) ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (posteriorWeight_pos k σ_sq hσ ev).le (sq_nonneg _)) ?_
    ((summable_posteriorWeight σ_sq hσ ev).mul_right ((|ev.toMean| + |center|) ^ 2))
  intro k
  apply mul_le_mul_of_nonneg_left _ (posteriorWeight_pos k σ_sq hσ ev).le
  have triangle : |posteriorMean (contextAtK k σ_sq hσ) ev - center| ≤
      |posteriorMean (contextAtK k σ_sq hσ) ev| + |center| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (posteriorMean (contextAtK k σ_sq hσ) ev) 0 center
  have component := posteriorMean_abs_le_sampleMean k σ_sq hσ ev positive
  have abs_bound : |posteriorMean (contextAtK k σ_sq hσ) ev - center| ≤
      |ev.toMean| + |center| := by linarith
  have bound := (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).2 abs_bound
  simpa only [sq_abs] using bound


/-- Positive data make both component and between-mean variance sums finite. -/
theorem mixturePosteriorVar_ne_top (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (positive : ev.n ≠ 0) :
    mixturePosteriorVar σ_sq hσ ev ≠ ⊤ := by
  exact ENNReal.add_ne_top.mpr
    ⟨ne_of_lt (summable_componentVariance σ_sq hσ ev positive).tsum_ofReal_lt_top,
      ne_of_lt (summable_centeredMean_square σ_sq hσ ev
        (mixturePosteriorMean σ_sq hσ ev) positive).tsum_ofReal_lt_top⟩

/-- Under positive observation count, the extended formula agrees exactly with
the finite real-series formula. -/
theorem mixturePosteriorVar_eq_ofReal (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (positive : ev.n ≠ 0) :
    mixturePosteriorVar σ_sq hσ ev = ENNReal.ofReal
      ((∑' k : ℤ, posteriorWeight k σ_sq hσ ev * componentPosteriorVar k σ_sq hσ ev) +
      (∑' k : ℤ, posteriorWeight k σ_sq hσ ev *
        (posteriorMean (contextAtK k σ_sq hσ) ev - mixturePosteriorMean σ_sq hσ ev) ^ 2)) := by
  have within_nonneg (k : ℤ) : 0 ≤ posteriorWeight k σ_sq hσ ev *
      componentPosteriorVar k σ_sq hσ ev :=
    mul_nonneg (posteriorWeight_pos k σ_sq hσ ev).le (posteriorVariance_pos _ _).le
  have between_nonneg (k : ℤ) : 0 ≤ posteriorWeight k σ_sq hσ ev *
      (posteriorMean (contextAtK k σ_sq hσ) ev - mixturePosteriorMean σ_sq hσ ev) ^ 2 :=
    mul_nonneg (posteriorWeight_pos k σ_sq hσ ev).le (sq_nonneg _)
  rw [ENNReal.ofReal_add (tsum_nonneg within_nonneg) (tsum_nonneg between_nonneg),
    ENNReal.ofReal_tsum_of_nonneg within_nonneg (summable_componentVariance σ_sq hσ ev positive),
    ENNReal.ofReal_tsum_of_nonneg between_nonneg
      (summable_centeredMean_square σ_sq hσ ev (mixturePosteriorMean σ_sq hσ ev) positive)]
  rfl

/-- With no observations, the heavy-tailed prior retains infinite variance. -/
theorem mixturePosteriorVar_of_count_zero (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (empty : ev.n = 0) :
    mixturePosteriorVar σ_sq hσ ev = ⊤ := by
  have within_top : (∑' k : ℤ, ENNReal.ofReal (posteriorWeight k σ_sq hσ ev *
      componentPosteriorVar k σ_sq hσ ev)) = ⊤ := by
    by_contra finite
    have summable_real := ENNReal.summable_toReal finite
    have at_each (k : ℤ) :
        (ENNReal.ofReal (posteriorWeight k σ_sq hσ ev *
          componentPosteriorVar k σ_sq hσ ev)).toReal =
          posteriorWeight k σ_sq hσ ev * componentPosteriorVar k σ_sq hσ ev :=
      ENNReal.toReal_ofReal
        (mul_nonneg (posteriorWeight_pos k σ_sq hσ ev).le (posteriorVariance_pos _ _).le)
    simp_rw [at_each] at summable_real
    exact not_summable_zero_count_variance σ_sq hσ ev empty summable_real
  unfold mixturePosteriorVar
  rw [within_top, top_add]

/-- The public readout retains an infinite standard deviation at zero count. -/
theorem inference_of_count_zero (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (empty : ev.n = 0) :
    plnUniversalHyperpriorInference σ_sq hσ ev = (0, ⊤) := by
  have mean_zero : mixturePosteriorMean σ_sq hσ ev = 0 := by
    simp [mixturePosteriorMean, posteriorMean, empty, contextAtK]
  simp only [plnUniversalHyperpriorInference, mean_zero,
    mixturePosteriorVar_of_count_zero σ_sq hσ ev empty,
    ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]


/-- The mixture mean shrinks toward the prior mean (0) -/
theorem mixture_shrinks_toward_prior (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) (hn : ev.n ≠ 0) :
    |mixturePosteriorMean σ_sq hσ ev| ≤ |ev.toMean| := by
  have majorant := (summable_posteriorWeight σ_sq hσ ev).mul_right |ev.toMean|
  have component_bound (k : ℤ) :
      posteriorWeight k σ_sq hσ ev * |posteriorMean (contextAtK k σ_sq hσ) ev| ≤
        posteriorWeight k σ_sq hσ ev * |ev.toMean| :=
    mul_le_mul_of_nonneg_left (posteriorMean_abs_le_sampleMean k σ_sq hσ ev hn)
      (posteriorWeight_pos k σ_sq hσ ev).le
  have absolute_term (k : ℤ) :
      |posteriorWeight k σ_sq hσ ev * posteriorMean (contextAtK k σ_sq hσ) ev| =
        posteriorWeight k σ_sq hσ ev * |posteriorMean (contextAtK k σ_sq hσ) ev| := by
    rw [abs_mul, abs_of_pos (posteriorWeight_pos k σ_sq hσ ev)]
  have summable_absolute : Summable (fun k : ℤ => posteriorWeight k σ_sq hσ ev *
      |posteriorMean (contextAtK k σ_sq hσ) ev|) := by
    simpa only [absolute_term] using (summable_posteriorMean σ_sq hσ ev).abs
  have summable_norm : Summable (fun k : ℤ =>
      ‖posteriorWeight k σ_sq hσ ev * posteriorMean (contextAtK k σ_sq hσ) ev‖) := by
    simpa only [Real.norm_eq_abs, absolute_term] using summable_absolute
  unfold mixturePosteriorMean
  calc
    |∑' k : ℤ, posteriorWeight k σ_sq hσ ev * posteriorMean (contextAtK k σ_sq hσ) ev| ≤
        ∑' k : ℤ, |posteriorWeight k σ_sq hσ ev *
          posteriorMean (contextAtK k σ_sq hσ) ev| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm summable_norm
    _ = ∑' k : ℤ, posteriorWeight k σ_sq hσ ev *
        |posteriorMean (contextAtK k σ_sq hσ) ev| := tsum_congr absolute_term
    _ ≤ ∑' k : ℤ, posteriorWeight k σ_sq hσ ev * |ev.toMean| :=
      Summable.tsum_le_tsum component_bound summable_absolute majorant
    _ = (∑' k : ℤ, posteriorWeight k σ_sq hσ ev) * |ev.toMean| := tsum_mul_right
    _ = |ev.toMean| := by rw [tsum_posteriorWeight_eq_one σ_sq hσ ev, one_mul]

/-- The variance formula is at least the expected component variance.  This
comparison does not claim a lower bound by the largest component variance. -/
theorem mixture_var_ge_expected_var (σ_sq : ℝ) (hσ : 0 < σ_sq)
    (ev : NormalGammaEvidence) :
    mixturePosteriorVar σ_sq hσ ev ≥
      ∑' k : ℤ, ENNReal.ofReal (posteriorWeight k σ_sq hσ ev *
        componentPosteriorVar k σ_sq hσ ev) := by
  exact le_add_of_nonneg_right bot_le

theorem logMarginalLikelihood_single_at_prior_mean (ctx : NormalNormalContext) :
    logMarginalLikelihood ctx (NormalGammaEvidence.single ctx.μ₀) =
      -((1 / 2 : ℝ) * Real.log (2 * Real.pi) +
        (1 / 2 : ℝ) * Real.log ctx.σ_sq +
        (1 / 2 : ℝ) * Real.log (1 + ctx.τ₀_sq / ctx.σ_sq)) := by
  simp [logMarginalLikelihood, NormalGammaEvidence.single,
    NormalGammaEvidence.sumSquaredDeviations]

namespace Controls

def unitContext (mean : ℝ) : NormalNormalContext where
  μ₀ := mean
  τ₀_sq := 1
  σ_sq := 1
  τ₀_sq_pos := by norm_num
  σ_sq_pos := by norm_num

theorem nonzero_prior_center_changes_likelihood :
    logMarginalLikelihood (unitContext 2) (NormalGammaEvidence.single 2) =
        logMarginalLikelihood (unitContext 0) (NormalGammaEvidence.single 2) + 1 ∧
      logMarginalLikelihood (unitContext 0) (NormalGammaEvidence.single 2) <
        logMarginalLikelihood (unitContext 2) (NormalGammaEvidence.single 2) := by
  norm_num [logMarginalLikelihood, unitContext, NormalGammaEvidence.single,
    NormalGammaEvidence.sumSquaredDeviations]
  linarith

end Controls
/-! ## Scope of the results

The fixed-family mixture has normalized positive posterior weights, a finite
partition function, a componentwise redundancy bound and a bounded mixture
mean.  The variance formula uses extended nonnegative sums; positive data give
finite moments, while zero-count inputs retain infinite variance.

These are results about the displayed formulas and their countable index set.
No theorem here establishes a Gaussian integral representation, full conjugacy,
coverage of credible intervals, optimal choice of the grid or coding weights,
identifiability of a hyperparameter, or superiority to empirical Bayes.
-/

end Mettapedia.UniversalAI.UniversalHyperprior
