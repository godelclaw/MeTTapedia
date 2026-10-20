import Mettapedia.PLN.Evidence.BinaryEvidence
import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
import Mettapedia.PLN.Evidence.HeytingValuationOnEvidence

/-!
# Algebra of the binary-evidence tensor

This file records algebraic facts about PLN's coordinatewise tensor
`(n₁⁺, n₁⁻) * (n₂⁺, n₂⁻) = (n₁⁺ n₂⁺, n₁⁻ n₂⁻)`: it is commutative and
associative with unit `(1, 1)`, its total is `n₁⁺ n₂⁺ + n₁⁻ n₂⁻` (not the product
of the totals), and it multiplies the odds `n⁺ / n⁻`.

## What the tensor means

* Read as **likelihood evidence**, the pair of masses of a hypothesis and of its
  negation jointly with a report, the tensor is the evidence of two reports
  that are conditionally independent given the hypothesis, under a uniform
  prior; its strength is the posterior probability, the logarithmic opinion
  pool (`Mettapedia.PLN.WorldModel.EvidenceContracts.testimony_fuse_uniform`,
  `strength_fuse_uniform`, `strength_fuse`).  Fusing two posteriors that each
  contain a non-uniform prior counts the prior twice.
* Read as **counts of samples**, it is not likelihood combination: the
  Bernoulli likelihoods `θ^k (1-θ)^m` of independent samples multiply by
  *adding* the counts, which is revision.  Pairing samples gives the paired
  product of `Mettapedia.PLN.WorldModel.EvidenceSpaces.ofSamples_product`, not
  the tensor.
* It is not the direct path of PLN deduction: on two half-strength premises its
  strength is `1/2`, while `s_AB · s_BC = 1/4` is the strength of the paired
  product (`Mettapedia.PLN.WorldModel.EvidenceContracts.Controls.fuse_not_direct_path`).

The theorems below are the algebraic facts only; none of them derives a
confidence for a conclusion.

## References

- PLN tensor product (BinaryEvidence.lean)
- BinaryEvidence-Beta connection (EvidenceBeta.lean)
-/

namespace Mettapedia.PLN.Evidence.ConfidenceCompoundingTheorem

open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
open Mettapedia.PLN.Evidence.HeytingValuationOnEvidence

/-! ## Total BinaryEvidence and Tensor -/

section TensorTotalEvidence

/-- The total of a tensor product: `n1+ * n2+ + n1- * n2-`, which is not the
    product of the totals in general. -/
theorem tensor_total_evidence_eq (e1 e2 : BinaryEvidence) :
    totalEvidence (e1 * e2) = e1.pos * e2.pos + e1.neg * e2.neg := by
  simp only [totalEvidence, BinaryEvidence.tensor_def]

/-- Tensor of unit evidence preserves total evidence. -/
theorem tensor_one_total_evidence (e : BinaryEvidence) :
    totalEvidence (e * BinaryEvidence.one) = totalEvidence e := by
  simp only [BinaryEvidence.tensor_one]

/-- The tensor product scales total evidence when one factor is uniform.

    For E = (n, n) (uniform evidence with strength 1/2):
    totalEvidence(E * F) = n * F.pos + n * F.neg
-/
theorem tensor_uniform_scaling (n : ENNReal) (e : BinaryEvidence) :
    let uniform : BinaryEvidence := { pos := n, neg := n }
    totalEvidence (uniform * e) = n * e.pos + n * e.neg := by
  simp only [totalEvidence, BinaryEvidence.tensor_def]

end TensorTotalEvidence

/-! ## Coordinatewise products

The tensor multiplies the two coordinates separately.  For Bernoulli samples the
likelihood `theta^(n+) * (1-theta)^(n-)` of independent samples multiplies by
adding counts, so these products are not likelihood combination of counts.
-/

section LikelihoodRatios

/-- The two counts as a pair. -/
noncomputable def likelihoodExponent (e : BinaryEvidence) : ENNReal × ENNReal :=
  (e.pos, e.neg)

/-- The tensor multiplies the two counts componentwise. -/
theorem tensor_likelihood_exponent_mul (e1 e2 : BinaryEvidence) :
    likelihoodExponent (e1 * e2) =
      (e1.pos * e2.pos, e1.neg * e2.neg) := by
  unfold likelihoodExponent
  simp only [BinaryEvidence.tensor_def]

/-- The tensor multiplies the two counts componentwise (restated). -/
theorem tensor_log_likelihood_additive (e1 e2 : BinaryEvidence) :
    -- The evidence counts add logarithmically
    (e1 * e2).pos = e1.pos * e2.pos ∧
    (e1 * e2).neg = e1.neg * e2.neg := by
  simp only [BinaryEvidence.tensor_def, and_self]

end LikelihoodRatios

/-! ## Positivity of products -/

section ConfidenceCompounding

/-- The tensor product of positive evidence has positive total evidence. -/
theorem tensor_positive_total (e1 e2 : BinaryEvidence)
    (h1_pos : e1.pos ≠ 0) (h2_pos : e2.pos ≠ 0) :
    (e1 * e2).pos ≠ 0 := by
  simp only [BinaryEvidence.tensor_def]
  exact mul_ne_zero h1_pos h2_pos

/-- Tensor preserves non-negativity. -/
theorem tensor_nonneg (e1 e2 : BinaryEvidence) :
    0 ≤ (e1 * e2).pos ∧ 0 ≤ (e1 * e2).neg := by
  simp only [BinaryEvidence.tensor_def]
  exact ⟨bot_le, bot_le⟩

/-- The tensor product has non-zero positive when both inputs have non-zero positive. -/
theorem tensor_pos_ne_zero (e1 e2 : BinaryEvidence)
    (h1 : e1.pos ≠ 0) (h2 : e2.pos ≠ 0) :
    (e1 * e2).pos ≠ 0 := by
  simp only [BinaryEvidence.tensor_def]
  exact mul_ne_zero h1 h2

/-- The tensor product has non-zero negative when both inputs have non-zero negative. -/
theorem tensor_neg_ne_zero (e1 e2 : BinaryEvidence)
    (h1 : e1.neg ≠ 0) (h2 : e2.neg ≠ 0) :
    (e1 * e2).neg ≠ 0 := by
  simp only [BinaryEvidence.tensor_def]
  exact mul_ne_zero h1 h2

end ConfidenceCompounding

/-! ## Algebraic laws -/

section SequentialInference

/-- The tensor is associative and commutative with unit `(1, 1)`.  Its derived
    meaning is fusion of conditionally independent likelihood evidence; it is
    not the composition of conditional probabilities `P(B|A) · P(C|B)`, whose
    strength is that of the paired product. -/
theorem sequential_independent_inference :
    -- Tensor is associative (can chain multiple steps)
    (∀ e1 e2 e3 : BinaryEvidence, (e1 * e2) * e3 = e1 * (e2 * e3)) ∧
    -- Tensor is commutative (order doesn't matter for independent sources)
    (∀ e1 e2 : BinaryEvidence, e1 * e2 = e2 * e1) ∧
    -- Unit evidence is neutral
    (∀ e : BinaryEvidence, e * BinaryEvidence.one = e) := by
  exact ⟨BinaryEvidence.tensor_assoc, BinaryEvidence.tensor_comm, BinaryEvidence.tensor_one⟩

/-- The tensor multiplies the odds `pos / neg`.  For likelihood evidence these
    are likelihood ratios, which multiply for conditionally independent
    reports; for counts of independent samples, likelihoods combine by adding
    counts instead. -/
theorem tensor_captures_odds_composition (e1 e2 : BinaryEvidence)
    (h1_neg : e1.neg ≠ 0) (h2_neg : e2.neg ≠ 0) :
    -- If we define odds ratio as pos/neg (when neg is nonzero)
    -- Then tensor gives multiplicative composition
    (e1 * e2).pos / (e1 * e2).neg =
      (e1.pos / e1.neg) * (e2.pos / e2.neg) := by
  simp only [BinaryEvidence.tensor_def]
  -- (e1.pos * e2.pos) / (e1.neg * e2.neg) = (e1.pos / e1.neg) * (e2.pos / e2.neg)
  -- Use: a/b * c/d = (a*c) / (b*d) (when b,d ≠ 0)
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  -- Goal: e1.pos * e2.pos * (e1.neg * e2.neg)⁻¹ = e1.pos * e1.neg⁻¹ * (e2.pos * e2.neg⁻¹)
  rw [ENNReal.mul_inv (Or.inl h1_neg) (Or.inr h2_neg)]
  -- Goal: e1.pos * e2.pos * (e1.neg⁻¹ * e2.neg⁻¹) = e1.pos * e1.neg⁻¹ * (e2.pos * e2.neg⁻¹)
  -- Rearrange: (a * b) * (c * d) = (a * c) * (b * d)
  rw [mul_mul_mul_comm]

end SequentialInference

/-! ## Contrast with revision -/

section BetaConnection

/-- The tensor multiplies the two counts componentwise (restated). -/
theorem tensor_independent_beta_interpretation (e1 e2 : BinaryEvidence) :
    -- The tensor of two evidence values combines their "votes" multiplicatively
    -- This is appropriate for combining ODDS, not raw counts
    (e1 * e2).pos = e1.pos * e2.pos ∧
    (e1 * e2).neg = e1.neg * e2.neg := by
  simp only [BinaryEvidence.tensor_def, and_self]

/-- Revision adds counts, the Beta posterior update for more samples of the same
    proposition; the tensor multiplies them componentwise. -/
theorem hplus_vs_tensor_contrast (e1 e2 : BinaryEvidence) :
    -- hplus is additive
    ((e1 + e2).pos = e1.pos + e2.pos ∧ (e1 + e2).neg = e1.neg + e2.neg) ∧
    -- tensor is multiplicative
    ((e1 * e2).pos = e1.pos * e2.pos ∧ (e1 * e2).neg = e1.neg * e2.neg) := by
  constructor
  · -- hplus adds
    constructor <;> rfl
  · -- tensor multiplies
    simp only [BinaryEvidence.tensor_def, and_self]

end BetaConnection

/-! ## Main Theorem: Confidence Compounding -/

section MainTheorem

/-- The algebraic laws of the tensor: commutative, associative, unital, and
    componentwise.  These laws do not derive a confidence for a conclusion. -/
theorem confidence_compounding_main :
    -- Tensor is the correct operation for independent evidence
    (∀ e1 e2 : BinaryEvidence,
      -- 1. Commutative (order of independent sources doesn't matter)
      e1 * e2 = e2 * e1) ∧
    (∀ e1 e2 e3 : BinaryEvidence,
      -- 2. Associative (can chain multiple independent sources)
      (e1 * e2) * e3 = e1 * (e2 * e3)) ∧
    (∀ e : BinaryEvidence,
      -- 3. Unit evidence is neutral
      e * BinaryEvidence.one = e) ∧
    (∀ e1 e2 : BinaryEvidence,
      -- 4. Correctly multiplies counts
      (e1 * e2).pos = e1.pos * e2.pos ∧ (e1 * e2).neg = e1.neg * e2.neg) := by
  refine ⟨BinaryEvidence.tensor_comm, BinaryEvidence.tensor_assoc, BinaryEvidence.tensor_one, ?_⟩
  intro e1 e2
  simp only [BinaryEvidence.tensor_def, and_self]

/-- Corollary: Odds ratio composition for non-zero denominators. -/
theorem odds_ratio_composition (e1 e2 : BinaryEvidence)
    (h1 : e1.neg ≠ 0) (h2 : e2.neg ≠ 0) :
    (e1 * e2).pos / (e1 * e2).neg = (e1.pos / e1.neg) * (e2.pos / e2.neg) := by
  exact tensor_captures_odds_composition e1 e2 h1 h2

end MainTheorem

/-! ## Summary

This file establishes the algebra of the tensor: componentwise products, the
total `n1+ * n2+ + n1- * n2-`, multiplication of odds, commutativity,
associativity and the unit `(1, 1)`.

- **hplus (+)**: adds counts, the Bayesian update for more samples of the same
  proposition, exact for disjoint samples.
- **tensor (*)**: multiplies coordinates, the fusion of conditionally
  independent likelihood evidence about one hypothesis.

Neither law derives the confidence of a deduction; composing `A → B` and
`B → C` along a direct path has the strength of the paired product.
-/

end Mettapedia.PLN.Evidence.ConfidenceCompoundingTheorem
