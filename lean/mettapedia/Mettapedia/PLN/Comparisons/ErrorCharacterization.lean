import Mettapedia.PLN.Core.CompletePLN
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
import Mettapedia.PLN.Evidence.BinaryEvidence

/-!
# Error Characterization: Fast PLN vs Complete PLN

This file formally characterizes the error between fast (heuristic) PLN and
complete (exact Bayesian) PLN, providing:

1. **Exact error formula**: The difference is precisely the independence violation
2. **Error bounds**: Upper bounds in terms of measurable quantities
3. **Zero-error conditions**: Sufficient screening conditions, allowing cancellation
4. **Decision criteria**: When to use fast vs complete mode

## The Key Insight

Fast PLN assumes: P(C|A,B) = P(C|B) and P(C|A,¬B) = P(C|¬B)

The weighted screening violation has the form:
  error = |P(B|A) · [P(C|A,B) - P(C|B)] + P(¬B|A) · [P(C|A,¬B) - P(C|¬B)]|

## Algebraic Structure (K&S-inspired)

The decision of when to use fast vs complete PLN can be grounded in:
1. Branch probabilities determine a convex combination of signed violations.
2. Unit-interval endpoint bounds give a conservative estimate.
3. Quantitative divergence bounds require additional information-theoretic results.

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- Pearl, "Probabilistic Reasoning in Intelligent Systems" (1988)
- Goertzel et al., "Probabilistic Logic Networks" (2009)
-/

namespace Mettapedia.PLN.Comparisons.ErrorCharacterization

open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation

/-! ## Part 1: The Independence Violation

The core quantity that determines PLN approximation error.
-/

/-- Independence violation for positive case: P(C|A,B) - P(C|B)

    When this is zero, the "positive path" through B is exact.
-/
noncomputable def positiveViolation (J : JointDistribution n) (a b c : Fin n) : ℝ :=
  condProb2 J c a b - condProb J c b

/-- Independence violation for negative case: P(C|A,¬B) - P(C|¬B)

    When this is zero, the "negative path" through ¬B is exact.
-/
noncomputable def negativeViolation (J : JointDistribution n) (a b c : Fin n) : ℝ :=
  condProb2Neg J c a b - condProbNeg J c b

/-- Total weighted violation: the exact error formula.

    error = P(B|A) · positiveViolation + P(¬B|A) · negativeViolation

    This is EXACTLY how much fast PLN deviates from complete PLN.
-/
noncomputable def totalViolation (J : JointDistribution n) (a b c : Fin n) : ℝ :=
  condProb J b a * positiveViolation J a b c +
  (1 - condProb J b a) * negativeViolation J a b c

/-- Weighted violation is the signed difference between the exact query and
its independently defined screening approximation. Empty internal branches
are handled by the total-probability theorem. -/
theorem exact_sub_screening_eq_totalViolation (J : JointDistribution n) (a b c : Fin n)
    (possible : marginalProb J a ≠ 0) :
    completeDeduction J a b c - screeningDeduction J a b c = totalViolation J a b c := by
  unfold completeDeduction screeningDeduction totalViolation positiveViolation negativeViolation
  rw [conditional_total_probability J a b c possible]
  ring

/-! ## Part 2: Zero Error Characterization

Branch screening is sufficient for zero error. Opposite signed branch errors can also cancel.
-/

/-- Sufficient condition for zero total violation:
    Both violations are zero, OR the corresponding weight is zero/one. -/
theorem sufficient_for_zero_violation (J : JointDistribution n) (a b c : Fin n)
    (hpos : positiveViolation J a b c = 0 ∨ condProb J b a = 0)
    (hneg : negativeViolation J a b c = 0 ∨ condProb J b a = 1) :
    totalViolation J a b c = 0 := by
  unfold totalViolation
  cases hpos with
  | inl hp =>
    cases hneg with
    | inl hn => simp only [hp, hn, mul_zero, add_zero]
    | inr hn => simp only [hp, hn, mul_zero, sub_self, zero_mul, add_zero]
  | inr hp =>
    cases hneg with
    | inl hn => simp only [hp, hn, zero_mul, sub_zero, one_mul, zero_add]
    | inr hn =>
      -- hp: condProb = 0, hn: condProb = 1 → contradiction (0 ≠ 1)
      have hcontra : (0 : ℝ) = 1 := hp.symm.trans hn
      exact absurd hcontra (by norm_num)

/-- Independence conditions imply zero violation -/
theorem independent_implies_zero_violation (J : JointDistribution n) (a b c : Fin n)
    (h_pos : hasPositiveIndependence J a b c)
    (h_neg : hasNegativeIndependence J a b c) :
    positiveViolation J a b c = 0 ∧ negativeViolation J a b c = 0 := by
  unfold hasPositiveIndependence at h_pos
  unfold hasNegativeIndependence at h_neg
  unfold positiveViolation negativeViolation
  exact ⟨sub_eq_zero.mpr h_pos, sub_eq_zero.mpr h_neg⟩

/-- Under independence, total violation is zero -/
theorem independent_implies_exact (J : JointDistribution n) (a b c : Fin n)
    (h_pos : hasPositiveIndependence J a b c)
    (h_neg : hasNegativeIndependence J a b c) :
    totalViolation J a b c = 0 := by
  have ⟨hp, hn⟩ := independent_implies_zero_violation J a b c h_pos h_neg
  unfold totalViolation
  simp [hp, hn]

/-! ## Part 3: Error Bounds

Upper bounds on the error in terms of measurable quantities.
-/

/-- The error is bounded by the maximum violation times path weights -/
theorem error_bound_by_max_violation (J : JointDistribution n) (a b c : Fin n)
    (h_bounds : 0 ≤ condProb J b a ∧ condProb J b a ≤ 1) :
    |totalViolation J a b c| ≤
    condProb J b a * |positiveViolation J a b c| +
    (1 - condProb J b a) * |negativeViolation J a b c| := by
  unfold totalViolation
  have h1 : |condProb J b a| = condProb J b a := abs_of_nonneg h_bounds.1
  have h2 : |1 - condProb J b a| = 1 - condProb J b a := abs_of_nonneg (by linarith)
  calc |condProb J b a * positiveViolation J a b c +
        (1 - condProb J b a) * negativeViolation J a b c|
      ≤ |condProb J b a * positiveViolation J a b c| +
        |(1 - condProb J b a) * negativeViolation J a b c| := abs_add_le _ _
    _ = |condProb J b a| * |positiveViolation J a b c| +
        |1 - condProb J b a| * |negativeViolation J a b c| := by
          rw [abs_mul, abs_mul]
    _ = condProb J b a * |positiveViolation J a b c| +
        (1 - condProb J b a) * |negativeViolation J a b c| := by
          rw [h1, h2]

/-- Worst-case error bound: error ≤ max(|pos_violation|, |neg_violation|) -/
theorem error_bound_by_max (J : JointDistribution n) (a b c : Fin n)
    (h_prob : 0 ≤ condProb J b a ∧ condProb J b a ≤ 1) :
    |totalViolation J a b c| ≤
    max (|positiveViolation J a b c|) (|negativeViolation J a b c|) := by
  -- Use the bound from error_bound_by_max_violation
  have hbound := error_bound_by_max_violation J a b c h_prob
  have hp : |positiveViolation J a b c| ≤ max (|positiveViolation J a b c|) (|negativeViolation J a b c|) :=
    le_max_left _ _
  have hn : |negativeViolation J a b c| ≤ max (|positiveViolation J a b c|) (|negativeViolation J a b c|) :=
    le_max_right _ _
  have h1 : 0 ≤ 1 - condProb J b a := by linarith
  calc |totalViolation J a b c|
      ≤ condProb J b a * |positiveViolation J a b c| +
        (1 - condProb J b a) * |negativeViolation J a b c| := hbound
    _ ≤ condProb J b a * max (|positiveViolation J a b c|) (|negativeViolation J a b c|) +
        (1 - condProb J b a) * max (|positiveViolation J a b c|) (|negativeViolation J a b c|) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hp h_prob.1
          · exact mul_le_mul_of_nonneg_left hn h1
    _ = max (|positiveViolation J a b c|) (|negativeViolation J a b c|) := by ring

/-- Since conditional probabilities are in [0,1], violations are in [-1,1] -/
theorem violation_bounded (J : JointDistribution n) (a b c : Fin n)
    (h_pos_bounds : 0 ≤ condProb2 J c a b ∧ condProb2 J c a b ≤ 1)
    (h_cond_bounds : 0 ≤ condProb J c b ∧ condProb J c b ≤ 1) :
    |positiveViolation J a b c| ≤ 1 := by
  unfold positiveViolation
  have h1 : -1 ≤ condProb2 J c a b - condProb J c b := by linarith [h_pos_bounds.1, h_cond_bounds.2]
  have h2 : condProb2 J c a b - condProb J c b ≤ 1 := by linarith [h_pos_bounds.2, h_cond_bounds.1]
  rw [abs_le]
  exact ⟨by linarith, h2⟩

/-- Ultimate error bound: |error| ≤ 1 -/
theorem error_bounded_by_one (J : JointDistribution n) (a b c : Fin n)
    (h_all_bounds : ∀ i j, 0 ≤ condProb J i j ∧ condProb J i j ≤ 1)
    (h_pos2_bounds : 0 ≤ condProb2 J c a b ∧ condProb2 J c a b ≤ 1)
    (h_neg2_bounds : 0 ≤ condProb2Neg J c a b ∧ condProb2Neg J c a b ≤ 1)
    (h_neg_bounds : 0 ≤ condProbNeg J c b ∧ condProbNeg J c b ≤ 1) :
    |totalViolation J a b c| ≤ 1 := by
  -- Each violation is in [-1, 1]
  have h_pos_viol := violation_bounded J a b c h_pos2_bounds (h_all_bounds c b)
  -- Similarly for negative violation
  have h_neg_viol : |negativeViolation J a b c| ≤ 1 := by
    unfold negativeViolation
    have h1 : -1 ≤ condProb2Neg J c a b - condProbNeg J c b := by
      linarith [h_neg2_bounds.1, h_neg_bounds.2]
    have h2 : condProb2Neg J c a b - condProbNeg J c b ≤ 1 := by
      linarith [h_neg2_bounds.2, h_neg_bounds.1]
    rw [abs_le]
    exact ⟨by linarith, h2⟩
  -- Use error_bound_by_max
  have hmax := error_bound_by_max J a b c (h_all_bounds b a)
  have hmax_le : max (|positiveViolation J a b c|) (|negativeViolation J a b c|) ≤ 1 :=
    max_le h_pos_viol h_neg_viol
  linarith

/-! ## Part 4: Algebraic Decision Criteria (K&S-inspired)

When should we use fast vs complete PLN? Algebraic characterization.
-/

/-- Confidence-weighted error: accounts for our certainty about the distribution -/
noncomputable def confidenceWeightedError (J : JointDistribution n) (a b c : Fin n)
    (confidence : ℝ) : ℝ :=
  confidence * |totalViolation J a b c|

/-- Expected regret from using fast PLN instead of complete -/
noncomputable def expectedRegret (J : JointDistribution n) (a b c : Fin n)
    (decision_weight : ℝ) : ℝ :=
  decision_weight * |totalViolation J a b c|

/-- Decision criterion: use complete PLN when expected regret exceeds threshold -/
def shouldUseComplete (expected_regret : ℝ) (threshold : ℝ) : Prop :=
  expected_regret > threshold

/-- Algebraic criterion based on independence measure.

    The "independence score" measures how close the distribution is to
    satisfying the independence assumptions. Score of 0 = perfect independence.
-/
noncomputable def independenceScore (J : JointDistribution n) (a b c : Fin n) : ℝ :=
  |positiveViolation J a b c| + |negativeViolation J a b c|

/-- Independence score of 0 implies fast PLN is exact -/
theorem zero_independence_score_exact (J : JointDistribution n) (a b c : Fin n)
    (h : independenceScore J a b c = 0) :
    totalViolation J a b c = 0 := by
  unfold independenceScore at h
  have hp : |positiveViolation J a b c| = 0 := by
    have : |positiveViolation J a b c| + |negativeViolation J a b c| = 0 := h
    have h1 : 0 ≤ |positiveViolation J a b c| := abs_nonneg _
    have h2 : 0 ≤ |negativeViolation J a b c| := abs_nonneg _
    linarith
  have hn : |negativeViolation J a b c| = 0 := by
    have : |positiveViolation J a b c| + |negativeViolation J a b c| = 0 := h
    have h1 : 0 ≤ |positiveViolation J a b c| := abs_nonneg _
    have h2 : 0 ≤ |negativeViolation J a b c| := abs_nonneg _
    linarith
  have hp' : positiveViolation J a b c = 0 := abs_eq_zero.mp hp
  have hn' : negativeViolation J a b c = 0 := abs_eq_zero.mp hn
  unfold totalViolation
  simp [hp', hn']

/-- Decision threshold based on K&S-style information content.

    Use complete mode when:
    1. Independence score > ε (significant violation), AND
    2. Decision importance > δ (high stakes), AND
    3. Computation is tractable (n ≤ 10)
-/
structure DecisionCriteria where
  /-- Maximum acceptable independence violation -/
  independence_threshold : ℝ
  /-- Minimum decision importance to warrant complete mode -/
  importance_threshold : ℝ
  /-- Maximum number of propositions for tractable complete inference -/
  tractability_limit : ℕ
  /-- Thresholds are positive -/
  thresholds_pos : 0 < independence_threshold ∧ 0 < importance_threshold

/-- Formal decision function: when to use complete PLN -/
def formalShouldUseComplete (criteria : DecisionCriteria) (n : ℕ)
    (independence_score : ℝ) (importance : ℝ) : Prop :=
  independence_score > criteria.independence_threshold ∧
  importance > criteria.importance_threshold ∧
  n ≤ criteria.tractability_limit

/-! ## Branch screening and conservative error estimates

The screening predicate below names precisely the two conditional equalities.
It is not a definition of conditional mutual information. Quantitative
information-theoretic bounds require a separate divergence construction.
-/

/-- The two branch-screening equalities used by PLN deduction. -/
def branchScreening (J : JointDistribution n) (a b c : Fin n) : Prop :=
  hasPositiveIndependence J a b c ∧ hasNegativeIndependence J a b c

theorem branch_screening_implies_exact (J : JointDistribution n) (a b c : Fin n)
    (h : branchScreening J a b c) :
    totalViolation J a b c = 0 :=
  independent_implies_exact J a b c h.1 h.2

/-- Distance from a unit-interval value to a reference probability is bounded
by the farther endpoint. -/
theorem abs_sub_le_max_complement {actual reference : ℝ}
    (hactual : actual ∈ Set.Icc (0 : ℝ) 1) :
    |actual - reference| ≤ max reference (1 - reference) := by
  rw [abs_le]
  constructor
  · linarith [le_max_left reference (1 - reference), hactual.1]
  · linarith [le_max_right reference (1 - reference), hactual.2]

/-- A bound available from the three branch readouts alone. The farther
endpoint is necessary: a reference probability near zero can have an error
near one. Additional joint information can give a tighter bound. -/
noncomputable def conservativeErrorEstimate
    (p_ba p_cb p_c_not_b : ℝ) : ℝ :=
  p_ba * max p_cb (1 - p_cb) + (1 - p_ba) * max p_c_not_b (1 - p_c_not_b)

/-- The conservative estimate is a unit-interval quantity. -/
theorem conservative_estimate_mem_unit
    (p_ba p_cb p_c_not_b : ℝ)
    (h_ba : p_ba ∈ Set.Icc (0 : ℝ) 1)
    (h_cb : p_cb ∈ Set.Icc (0 : ℝ) 1)
    (h_cnb : p_c_not_b ∈ Set.Icc (0 : ℝ) 1) :
    conservativeErrorEstimate p_ba p_cb p_c_not_b ∈ Set.Icc (0 : ℝ) 1 := by
  have pos0 : 0 ≤ max p_cb (1 - p_cb) := le_trans h_cb.1 (le_max_left _ _)
  have neg0 : 0 ≤ max p_c_not_b (1 - p_c_not_b) := le_trans h_cnb.1 (le_max_left _ _)
  have pos1 : max p_cb (1 - p_cb) ≤ 1 := max_le h_cb.2 (by linarith [h_cb.1])
  have neg1 : max p_c_not_b (1 - p_c_not_b) ≤ 1 := max_le h_cnb.2 (by linarith [h_cnb.1])
  unfold conservativeErrorEstimate
  constructor
  · exact add_nonneg (mul_nonneg h_ba.1 pos0) (mul_nonneg (by linarith [h_ba.2]) neg0)
  · calc
      _ ≤ p_ba * 1 + (1 - p_ba) * 1 := add_le_add
        (mul_le_mul_of_nonneg_left pos1 h_ba.1)
        (mul_le_mul_of_nonneg_left neg1 (by linarith [h_ba.2]))
      _ = 1 := by ring

/-- This is the missing connection between the estimate and the actual
weighted screening violation. No independence hypothesis is used. -/
theorem error_le_conservative_estimate (J : JointDistribution n) (a b c : Fin n)
    (h_weight : condProb J b a ∈ Set.Icc (0 : ℝ) 1)
    (h_positive : condProb2 J c a b ∈ Set.Icc (0 : ℝ) 1)
    (h_negative : condProb2Neg J c a b ∈ Set.Icc (0 : ℝ) 1) :
    |totalViolation J a b c| ≤ conservativeErrorEstimate
      (condProb J b a) (condProb J c b) (condProbNeg J c b) := by
  apply le_trans (error_bound_by_max_violation J a b c h_weight)
  exact add_le_add
    (mul_le_mul_of_nonneg_left (abs_sub_le_max_complement h_positive) h_weight.1)
    (mul_le_mul_of_nonneg_left (abs_sub_le_max_complement h_negative) (by linarith [h_weight.2]))

/-- A query-level error bound whose interval side conditions are discharged
from the joint distribution, rather than supplied as approximation assumptions. -/
theorem query_error_le_conservative_estimate (J : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb J a) :
    |completeDeduction J a b c - screeningDeduction J a b c| ≤
      conservativeErrorEstimate (condProb J b a) (condProb J c b) (condProbNeg J c b) := by
  rw [exact_sub_screening_eq_totalViolation J a b c possible.ne']
  exact error_le_conservative_estimate J a b c (cond_prob_bounds J b a possible)
    (condProb2_mem_unit J a b c) (condProb2Neg_mem_unit J a b c)

/-- Separate bounds on the two screening defects give a weighted query bound.
A rarely visited branch contributes proportionally to its query weight. -/
theorem query_error_le_weighted_violations (J : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb J a) {positiveBound negativeBound : ℝ}
    (positive : |positiveViolation J a b c| ≤ positiveBound)
    (negative : |negativeViolation J a b c| ≤ negativeBound) :
    |completeDeduction J a b c - screeningDeduction J a b c| ≤
      condProb J b a * positiveBound + (1 - condProb J b a) * negativeBound := by
  rw [exact_sub_screening_eq_totalViolation J a b c possible.ne']
  have weights := cond_prob_bounds J b a possible
  exact le_trans (error_bound_by_max_violation J a b c weights) (add_le_add
    (mul_le_mul_of_nonneg_left positive weights.1)
    (mul_le_mul_of_nonneg_left negative (by linarith [weights.2])))

/-- A branch probability of 0.9 can differ from its 0.1 reference by 0.8.
The nearer-endpoint expression is 0.1 and therefore cannot bound the error. -/
theorem nearer_endpoint_is_not_an_error_bound :
    |(9 / 10 : ℝ) - 1 / 10| > min (1 / 10 : ℝ) (1 - 1 / 10) := by norm_num

/-- The repaired farther-endpoint estimate covers that discrepancy. -/
theorem farther_endpoint_covers_error :
    |(9 / 10 : ℝ) - 1 / 10| ≤ conservativeErrorEstimate 1 (1 / 10) (1 / 2) := by
  norm_num [conservativeErrorEstimate]

/-! ## Part 7: Classification of Error Regimes

Different types of errors PLN approximation can make.
-/

/-- Error regimes based on which independence assumption fails -/
inductive ErrorRegime
  | exact           -- Both independences hold, error = 0
  | positiveOnly    -- Only positive independence fails
  | negativeOnly    -- Only negative independence fails
  | bothFail        -- Both independences fail
  deriving DecidableEq, Repr

/-- Classify the error regime from violations (takes pre-computed Bools) -/
def classifyErrorRegime (pos_significant neg_significant : Bool) : ErrorRegime :=
  match pos_significant, neg_significant with
  | false, false => ErrorRegime.exact
  | true, false => ErrorRegime.positiveOnly
  | false, true => ErrorRegime.negativeOnly
  | true, true => ErrorRegime.bothFail

/-- Predicate: positive violation is significant -/
def posViolationSignificant (pos_violation : ℝ) (ε : ℝ) : Prop :=
  |pos_violation| > ε

/-- Predicate: negative violation is significant -/
def negViolationSignificant (neg_violation : ℝ) (ε : ℝ) : Prop :=
  |neg_violation| > ε

/-- If both branch violations are at most `ε`, their convex combination is
at most `ε`; the previous factor two is unnecessary. -/
theorem exact_regime_bounded (J : JointDistribution n) (a b c : Fin n) (ε : ℝ) (_hε : 0 < ε)
    (h_pos : |positiveViolation J a b c| ≤ ε)
    (h_neg : |negativeViolation J a b c| ≤ ε)
    (h_bounds : 0 ≤ condProb J b a ∧ condProb J b a ≤ 1) :
    |totalViolation J a b c| ≤ ε := by
  exact le_trans (error_bound_by_max J a b c h_bounds) (max_le h_pos h_neg)

/-!
The exactness result is one-way: branch screening implies zero weighted
violation. It is not necessary because signed violations may cancel. The
conservative estimate bounds weighted violation when the actual conditionals
lie in the unit interval. Relating that violation to a concrete query answer
requires the total-probability identity for the chosen world model.
-/

/-- The bound applies to the existing PLN formula on coherent WM readouts,
not only to the branch-reference spelling used in the derivation. -/
theorem pln_query_error_le_conservative_estimate (J : JointDistribution n) (a b c : Fin n)
    (possible : 0 < marginalProb J a) :
    |completeDeduction J a b c -
      plnDeductionStrength (condProb J b a) (condProb J c b)
        (marginalProb J b) (marginalProb J c)| ≤
      conservativeErrorEstimate (condProb J b a) (condProb J c b) (condProbNeg J c b) := by
  simpa only [screeningDeduction_eq_plnDeductionStrength] using
    query_error_le_conservative_estimate J a b c possible

namespace Controls

private theorem sum_boolean_three (f : Fin (2 ^ 3) → ℝ) :
    (∑ x, f x) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + f 7)))))) := by
  change (∑ x : Fin 8, f x) = _
  simp [Fin.sum_univ_succ]

/-- `B` always holds and the rare event `A` coincides with `C`. A small
reference conditional therefore permits a large positive branch error. -/
noncomputable def rareSubsetDistribution : JointDistribution 3 where
  prob world := if world.val = 2 then 9 / 10 else if world.val = 7 then 1 / 10 else 0
  prob_nonneg world := by split_ifs <;> norm_num
  prob_sum_one := by
    change (∑ world : Fin 8,
      if world.val = 2 then (9 / 10 : ℝ) else if world.val = 7 then 1 / 10 else 0) = 1
    norm_num [Fin.sum_univ_succ]

/-- The nearer-endpoint estimate fails on an actual coherent joint model:
the query error is `9/10`, while that estimate reports only `1/10`. -/
theorem nearer_endpoint_estimate_fails_on_joint_model :
    |completeDeduction rareSubsetDistribution 0 1 2 -
      screeningDeduction rareSubsetDistribution 0 1 2| = (9 / 10 : ℝ) ∧
    (condProb rareSubsetDistribution 1 0 *
        min (condProb rareSubsetDistribution 2 1) (1 - condProb rareSubsetDistribution 2 1) +
      (1 - condProb rareSubsetDistribution 1 0) *
        min (condProbNeg rareSubsetDistribution 2 1) (1 - condProbNeg rareSubsetDistribution 2 1)) =
      (1 / 10 : ℝ) := by
  norm_num [completeDeduction, screeningDeduction, condProb, condProbNeg,
    marginalProb, marginalProbNeg, jointProb2, rareSubsetDistribution,
    sum_boolean_three, worldToAssignment]

/-- Within the `b` branch `a` and `c` agree, while outside it they disagree.
The unconditional query is nevertheless predicted exactly by cancellation. -/
noncomputable def cancellingDistribution : JointDistribution 3 where
  prob world := if world.val = 1 ∨ world.val = 2 ∨ world.val = 4 ∨ world.val = 7 then 1 / 4 else 0
  prob_nonneg world := by split_ifs <;> norm_num
  prob_sum_one := by
    change (∑ world : Fin 8,
      if world.val = 1 ∨ world.val = 2 ∨ world.val = 4 ∨ world.val = 7 then (1 / 4 : ℝ) else 0) = 1
    norm_num [Fin.sum_univ_succ]

theorem exact_query_need_not_have_branch_screening :
    completeDeduction cancellingDistribution 0 1 2 = screeningDeduction cancellingDistribution 0 1 2 ∧
      positiveViolation cancellingDistribution 0 1 2 = (1 / 2 : ℝ) ∧
      negativeViolation cancellingDistribution 0 1 2 = -(1 / 2 : ℝ) ∧
      ¬ branchScreening cancellingDistribution 0 1 2 := by
  norm_num [completeDeduction, screeningDeduction, positiveViolation, negativeViolation,
    branchScreening, hasPositiveIndependence, hasNegativeIndependence,
    condProb, condProb2, condProbNeg, condProb2Neg, marginalProb, marginalProbNeg,
    jointProb2, jointProb2Neg, jointProb3, jointProb3Neg, cancellingDistribution,
    sum_boolean_three, worldToAssignment]

end Controls

end Mettapedia.PLN.Comparisons.ErrorCharacterization
