import Mettapedia.UniversalAI.UniversalPrediction.ConvergenceCriteria
import Mettapedia.DecisionTheory.FiniteRisk
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Error Bounds (Hutter 2005, Theorem 3.36)

This file formalizes the error bounds for universal prediction from
Chapter 3 of Hutter's "Universal Artificial Intelligence".

## Main Definitions

* `optimalPrediction` - The optimal prediction given the true distribution μ
* `universalPrediction` - The prediction using the universal semimeasure ξ
* `errorProb` - Probability of prediction error at time t
* `expectedOptimalErrors` - Total expected errors for optimal predictor
* `expectedUniversalErrors` - Total expected errors for universal predictor

## Main Results

* Sharp error regret: `S + sqrt (4 E S + S²)`, hence `2 S + 2 sqrt (E S)`.

## References

- Hutter, M. (2005). "Universal Artificial Intelligence", Theorem 3.36
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction

open scoped Classical BigOperators
open FiniteHorizon Convergence ConvergenceCriteria

namespace ErrorBounds

/-! ## Definitions for Prediction Errors -/

/-- Optimal prediction at time t given history x: predict argmax_b μ(b|x).
    For binary alphabet, predict true if μ(true|x) ≥ 1/2. -/
def optimalPrediction (μ : PrefixMeasure) (x : BinString) : Bool :=
  FiniteHorizon.condProb μ.toSemimeasure x true ≥ 1/2

/-- Threshold prediction at time t given history x.
    For binary alphabet, predict true if ξ(true|x) ≥ 1/2. -/
def universalPrediction (ξ : Semimeasure) (x : BinString) : Bool :=
  FiniteHorizon.condProb ξ x true ≥ 1/2

/-- Probability of error for a prediction when true distribution is μ.
    Error occurs when predicted symbol ≠ actual symbol.

    For prediction b: error = 1 - μ(b|x) -/
def errorProb (μ : PrefixMeasure) (prediction : Bool) (x : BinString) : ℝ :=
  1 - FiniteHorizon.condProb μ.toSemimeasure x prediction

/-- Error probability for optimal predictor Θ_μ.
    e^μ_t(x_{<t}) = 1 - max{μ(b|x_{<t}) : b} = min{1 - μ(b|x_{<t}) : b} -/
def optimalErrorProb (μ : PrefixMeasure) (x : BinString) : ℝ :=
  errorProb μ (optimalPrediction μ x) x

/-- Error probability for universal predictor Θ_ξ (using true distribution μ). -/
def universalErrorProb (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString) : ℝ :=
  errorProb μ (universalPrediction ξ x) x

/-- Expected errors at horizon n for optimal predictor:
    E^μ_n = ∑_{t<n} E_μ[e^μ_t(x_{<t})]. -/
def expectedOptimalErrors (μ : PrefixMeasure) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, expectPrefix μ k (optimalErrorProb μ)

/-- Expected errors at horizon n for universal predictor:
    E^ξ_n = ∑_{t<n} E_μ[e^ξ_t(x_{<t})]. -/
def expectedUniversalErrors (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, expectPrefix μ k (universalErrorProb μ ξ)

/-! ## Key Properties -/

/-- Conditional probability is at most 1.
    This follows from ρ(x ++ b) ≤ ρ(x) by semimeasure monotonicity. -/
theorem condProb_le_one' (ρ : Semimeasure) (x : BinString) (b : Bool) :
    FiniteHorizon.condProb ρ x b ≤ 1 := by
  unfold FiniteHorizon.condProb conditionalENN
  -- condProb = ρ(x++b) / ρ(x) ≤ ρ(x) / ρ(x) = 1 when ρ(x) > 0
  -- When ρ(x) = 0, the division gives 0 ≤ 1
  by_cases hx0 : ρ x = 0
  · -- When ρ(x) = 0, division by 0 gives 0
    simp [hx0]
  · -- When ρ(x) > 0, use monotonicity
    have hxTop : ρ x ≠ ⊤ := semimeasure_ne_top ρ x
    have hmono : ρ (x ++ [b]) ≤ ρ x := by simpa using ρ.mono x b
    have h1Top : (1 : ENNReal) ≠ ⊤ := by simp
    -- The child is also finite
    have hchildTop : ρ (x ++ [b]) ≠ ⊤ := ne_top_of_le_ne_top hxTop hmono
    -- Now ρ(x++b)/ρ(x) ≤ ρ(x)/ρ(x) = 1
    have hdiv_le : ρ (x ++ [b]) / ρ x ≤ 1 := by
      rw [ENNReal.div_le_iff hx0 hxTop]
      simp [hmono]
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top h1Top hdiv_le) h1Top).mpr hdiv_le

/-- Error probability is in [0, 1]. -/
theorem errorProb_nonneg (μ : PrefixMeasure) (b : Bool) (x : BinString) :
    0 ≤ errorProb μ b x := by
  unfold errorProb
  have h := condProb_le_one' μ.toSemimeasure x b
  linarith

/-- The optimal predictor minimizes error probability.
    This is inequality (3.35): E^μ_n ≤ E^p_n for any predictor p. -/
theorem optimalErrorProb_le_errorProb (μ : PrefixMeasure) (x : BinString) (b : Bool) :
    optimalErrorProb μ x ≤ errorProb μ b x := by
  by_cases zero : μ x = 0
  · have values (b : Bool) : FiniteHorizon.condProb μ.toSemimeasure x b = 0 := by
      simp [FiniteHorizon.condProb, conditionalENN, zero]
    simp only [optimalErrorProb, errorProb, values, sub_zero, le_refl]
  · have total := Convergence.condProb_sum_eq_one μ x zero
    unfold optimalErrorProb optimalPrediction errorProb
    by_cases h : FiniteHorizon.condProb μ.toSemimeasure x true ≥ 1 / 2
    · simp only [h, decide_true]
      cases b <;> linarith
    · simp only [h, decide_false]
      have smaller := lt_of_not_ge h
      cases b <;> linarith

/-- Integrating pointwise optimality preserves the comparison. -/
theorem expectedOptimalErrors_le_universal (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) :
    expectedOptimalErrors μ n ≤ expectedUniversalErrors μ ξ n := by
  unfold expectedOptimalErrors expectedUniversalErrors
  apply Finset.sum_le_sum
  intro k _hk
  unfold expectPrefix
  apply Finset.sum_le_sum
  intro f _hf
  apply mul_le_mul_of_nonneg_left
  · exact optimalErrorProb_le_errorProb μ (List.ofFn f) _
  · exact ENNReal.toReal_nonneg

/-! ## Theorem 3.36: Error Bounds -/

/-- Key algebraic lemma for error bounds: u ≤ A + B·u²/2 when 2AB ≥ 1.
    This follows from analyzing the quadratic f(u) = A + Bu²/2 - u. -/
lemma am_gm_error_bound {A B u : ℝ} (hAB : 2 * A * B ≥ 1) (hA : A > 0) (hB : B > 0)
    (_hu0 : 0 ≤ u) (_hu1 : u ≤ 1) : u ≤ A + B * u ^ 2 / 2 := by
  -- The function f(u) = A + Bu²/2 - u has minimum at u = 1/B.
  -- We need f(u) ≥ 0 for all u ∈ [0, 1].
  -- Key: from 2AB ≥ 1, we get A ≥ 1/(2B).
  have hA_ge : A ≥ 1 / (2 * B) := by
    have h := hAB
    have hBpos : B > 0 := hB
    have : A * (2 * B) ≥ 1 := by linarith
    calc A = A * (2 * B) / (2 * B) := by field_simp
      _ ≥ 1 / (2 * B) := by apply div_le_div_of_nonneg_right this; linarith
  -- Now show u ≤ A + B*u²/2 via completing the square
  -- Rewrite as: A + B*u²/2 - u ≥ 0
  -- = B/2 * (u² - 2u/B) + A
  -- = B/2 * ((u - 1/B)² - 1/B²) + A
  -- = B/2 * (u - 1/B)² - 1/(2B) + A
  -- ≥ 0 - 1/(2B) + A = A - 1/(2B) ≥ 0 (by hA_ge)
  have hkey : A + B * u ^ 2 / 2 - u = B / 2 * (u - 1 / B) ^ 2 + (A - 1 / (2 * B)) := by
    field_simp
    ring
  have hsq_ge : B / 2 * (u - 1 / B) ^ 2 ≥ 0 := by
    apply mul_nonneg
    · linarith
    · exact sq_nonneg _
  have hdiff_ge : A - 1 / (2 * B) ≥ 0 := by linarith
  have hrhs_ge : B / 2 * (u - 1 / B) ^ 2 + (A - 1 / (2 * B)) ≥ 0 := by linarith
  linarith

/-- Helper: sqDistStep is non-negative -/
lemma sqDistStep_nonneg (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString) :
    0 ≤ sqDistStep μ ξ x := by
  unfold sqDistStep
  rw [Entropy.sqDistBinary_eq_two_mul]
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  exact sq_nonneg _

/-- Helper: When predictions agree, universalErrorProb = optimalErrorProb -/
lemma error_eq_when_predictions_agree (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (h : universalPrediction ξ x = optimalPrediction μ x) :
    universalErrorProb μ ξ x = optimalErrorProb μ x := by
  unfold universalErrorProb optimalErrorProb
  rw [h]

/-- Helper: Error probabilities for opposite predictions sum to 1 (when μ x ≠ 0) -/
lemma errorProb_true_add_false_eq_one (μ : PrefixMeasure) (x : BinString) (hμx : μ x ≠ 0) :
    errorProb μ true x + errorProb μ false x = 1 := by
  unfold errorProb
  have hsum := Convergence.condProb_sum_eq_one μ x hμx
  linarith

/-- Helper: When predictions disagree and μ x ≠ 0, error sum = 1 -/
lemma error_sum_eq_one_when_disagree (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (hμx : μ x ≠ 0) (h_disagree : universalPrediction ξ x ≠ optimalPrediction μ x) :
    optimalErrorProb μ x + universalErrorProb μ ξ x = 1 := by
  unfold optimalErrorProb universalErrorProb
  -- When they disagree, one is true and one is false
  cases h1 : optimalPrediction μ x with
  | false =>
    cases h2 : universalPrediction ξ x with
    | false =>
      rw [h1, h2] at h_disagree
      exact absurd rfl h_disagree
    | true =>
      -- Goal: errorProb μ false x + errorProb μ true x = 1
      have := errorProb_true_add_false_eq_one μ x hμx
      linarith
  | true =>
    cases h2 : universalPrediction ξ x with
    | false =>
      -- Goal: errorProb μ true x + errorProb μ false x = 1
      have := errorProb_true_add_false_eq_one μ x hμx
      linarith
    | true =>
      rw [h1, h2] at h_disagree
      exact absurd rfl h_disagree

/-- Helper: Error difference when predictions disagree -/
lemma error_diff_eq_abs_two_p_minus_one (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (hμx : μ x ≠ 0) (h_disagree : universalPrediction ξ x ≠ optimalPrediction μ x) :
    |universalErrorProb μ ξ x - optimalErrorProb μ x| =
    |2 * FiniteHorizon.condProb μ.toSemimeasure x true - 1| := by
  set p := FiniteHorizon.condProb μ.toSemimeasure x true
  have hsum := Convergence.condProb_sum_eq_one μ x hμx
  have hpf : FiniteHorizon.condProb μ.toSemimeasure x false = 1 - p := by linarith
  -- When predictions disagree, exactly one predicts true and one predicts false
  -- This means the error probabilities are errorProb μ true x and errorProb μ false x
  -- Their sum is 1, and their difference is |2p - 1|
  unfold universalErrorProb optimalErrorProb errorProb
  cases h1 : optimalPrediction μ x with
  | false =>
    cases h2 : universalPrediction ξ x with
    | false =>
      rw [h1, h2] at h_disagree
      exact absurd rfl h_disagree
    | true =>
      -- optimal predicts false, universal predicts true
      -- universalErrorProb = 1 - condProb true = 1 - p
      -- optimalErrorProb = 1 - condProb false = 1 - (1 - p) = p
      -- difference = (1 - p) - p = 1 - 2p
      rw [hpf]
      have hdiff : (1 - p) - (1 - (1 - p)) = 1 - 2 * p := by ring
      rw [hdiff]
      exact abs_sub_comm (1 : ℝ) (2 * p)
  | true =>
    cases h2 : universalPrediction ξ x with
    | false =>
      -- optimal predicts true, universal predicts false
      -- universalErrorProb = 1 - condProb false = 1 - (1 - p) = p
      -- optimalErrorProb = 1 - condProb true = 1 - p
      -- difference = p - (1 - p) = 2p - 1
      rw [hpf]
      have hdiff : (1 - (1 - p)) - (1 - p) = 2 * p - 1 := by ring
      rw [hdiff]
    | true =>
      rw [h1, h2] at h_disagree
      exact absurd rfl h_disagree

/-- Helper: When predictions disagree, sqDistStep ≥ (2p-1)²/2.
    This is the key connection between prediction error and squared distance.

    When μ predicts true (p ≥ 1/2) and ξ predicts false (q < 1/2):
    |p - q| = (p - q) ≥ (p - 1/2), so sqDistStep = 2(p-q)² ≥ 2(p-1/2)² = (2p-1)²/2.

    Similarly for the symmetric case. -/
lemma sqDistStep_ge_error_diff_sq (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (h_disagree : universalPrediction ξ x ≠ optimalPrediction μ x) :
    sqDistStep μ ξ x ≥ (2 * FiniteHorizon.condProb μ.toSemimeasure x true - 1) ^ 2 / 2 := by
  unfold sqDistStep
  rw [Entropy.sqDistBinary_eq_two_mul]
  -- sqDistStep = 2 * (p - q)² where p = condProb μ, q = condProb ξ
  set p := FiniteHorizon.condProb μ.toSemimeasure x true
  set q := FiniteHorizon.condProb ξ x true
  -- We need: 2 * (p - q)² ≥ (2p - 1)² / 2
  -- When predictions disagree: one of p,q ≥ 1/2 and the other < 1/2
  -- So |p - q| ≥ |p - 1/2|
  have key : |p - q| ≥ |p - 1/2| := by
    -- Analyze based on actual Bool predictions
    cases h1 : optimalPrediction μ x with
    | false =>
      cases h2 : universalPrediction ξ x with
      | false =>
        rw [h1, h2] at h_disagree
        exact absurd rfl h_disagree
      | true =>
        -- μ predicts false (p < 1/2), ξ predicts true (q ≥ 1/2)
        unfold optimalPrediction at h1
        unfold universalPrediction at h2
        simp only [decide_eq_false_iff_not, not_le] at h1
        simp only [decide_eq_true_iff] at h2
        have h1' : p < 1/2 := h1
        have h2' : q ≥ 1/2 := h2
        have hpq_pos : q - p > 0 := by linarith
        have hphalf_pos : 1/2 - p > 0 := by linarith
        rw [abs_sub_comm p q, abs_of_pos hpq_pos]
        rw [abs_sub_comm p (1/2 : ℝ), abs_of_pos hphalf_pos]
        linarith
    | true =>
      cases h2 : universalPrediction ξ x with
      | false =>
        -- μ predicts true (p ≥ 1/2), ξ predicts false (q < 1/2)
        unfold optimalPrediction at h1
        unfold universalPrediction at h2
        simp only [decide_eq_true_iff] at h1
        simp only [decide_eq_false_iff_not, not_le] at h2
        have h1' : p ≥ 1/2 := h1
        have h2' : q < 1/2 := h2
        have hpq_pos : p - q > 0 := by linarith
        have hphalf_nonneg : p - 1/2 ≥ 0 := by linarith
        rw [abs_of_pos hpq_pos, abs_of_nonneg hphalf_nonneg]
        linarith
      | true =>
        rw [h1, h2] at h_disagree
        exact absurd rfl h_disagree
  -- Now from |p - q| ≥ |p - 1/2|, get (p - q)² ≥ (p - 1/2)²
  -- |a| ≥ |b| implies a² = |a|² ≥ |b|² = b²
  have hsq : (p - q) ^ 2 ≥ (p - 1/2) ^ 2 := by
    have h1 : (p - q) ^ 2 = |p - q| ^ 2 := (sq_abs (p - q)).symm
    have h2 : (p - 1/2) ^ 2 = |p - 1/2| ^ 2 := (sq_abs (p - 1/2)).symm
    rw [h1, h2]
    apply sq_le_sq'
    · calc -|p - q| ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
        _ ≤ |p - 1/2| := abs_nonneg _
    · exact key
  -- And 2(p-q)² ≥ 2(p-1/2)² = (2p-1)²/2
  have h2pq : 2 * (p - q) ^ 2 ≥ 2 * (p - 1/2) ^ 2 := by linarith
  have hrw : 2 * (p - 1/2) ^ 2 = (2 * p - 1) ^ 2 / 2 := by ring
  linarith

/-- Per-step error difference bound.
    e^ξ_t - e^μ_t ≤ A(e^μ_t + e^ξ_t) + B·s_t for suitable A, B > 0.

    From the proof: 2AB ≥ 1 is required.

    **Proof (Hutter 3.37-3.42)**:
    - When predictions agree: difference = 0 ≤ RHS
    - When predictions disagree: error sum = 1, and sqDistStep provides
      the leverage via AM-GM (am_gm_error_bound lemma) -/
theorem errorDiff_le_sqDist (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (A B : ℝ) (hAB : 2 * A * B ≥ 1) (hA : A > 0) (hB : B > 0) :
    universalErrorProb μ ξ x - optimalErrorProb μ x ≤
    A * (optimalErrorProb μ x + universalErrorProb μ ξ x) + B * sqDistStep μ ξ x := by
  -- First, establish that the RHS is non-negative regardless of predictions
  have hRHS_nonneg : 0 ≤ A * (optimalErrorProb μ x + universalErrorProb μ ξ x) + B * sqDistStep μ ξ x := by
    apply add_nonneg
    · apply mul_nonneg (le_of_lt hA)
      apply add_nonneg <;> exact errorProb_nonneg μ _ x
    · exact mul_nonneg (le_of_lt hB) (sqDistStep_nonneg μ ξ x)
  -- Case split: do predictions agree?
  by_cases h_agree : universalPrediction ξ x = optimalPrediction μ x
  · -- Predictions agree: difference = 0, RHS is non-negative
    have heq := error_eq_when_predictions_agree μ ξ x h_agree
    rw [heq]
    have hLHS : optimalErrorProb μ x - optimalErrorProb μ x = 0 := sub_self _
    rw [hLHS]
    -- Need to show 0 ≤ A * (optimalErrorProb + optimalErrorProb) + B * sqDistStep
    apply add_nonneg
    · apply mul_nonneg (le_of_lt hA)
      apply add_nonneg <;> exact errorProb_nonneg μ _ x
    · exact mul_nonneg (le_of_lt hB) (sqDistStep_nonneg μ ξ x)
  · -- Predictions disagree: need the AM-GM argument
    -- Handle μ x = 0 case separately
    by_cases hμx : μ x = 0
    · -- When μ x = 0, both condProb values are 0, so both error probs are 1
      -- Hence universalErrorProb = optimalErrorProb = 1, difference = 0
      have hpt0 : FiniteHorizon.condProb μ.toSemimeasure x true = 0 := by
        simp only [FiniteHorizon.condProb, conditionalENN]; simp [hμx]
      have hpf0 : FiniteHorizon.condProb μ.toSemimeasure x false = 0 := by
        simp only [FiniteHorizon.condProb, conditionalENN]; simp [hμx]
      have h_eμ : optimalErrorProb μ x = 1 := by
        unfold optimalErrorProb optimalPrediction errorProb
        have : (decide (FiniteHorizon.condProb μ.toSemimeasure x true ≥ 1/2)) = false := by
          simp only [decide_eq_false_iff_not, not_le]; simp [hpt0]
        rw [this, hpf0]; norm_num
      have h_eξ : universalErrorProb μ ξ x = 1 := by
        unfold universalErrorProb errorProb
        cases huniv : universalPrediction ξ x with
        | false => rw [hpf0]; norm_num
        | true => rw [hpt0]; norm_num
      rw [h_eμ, h_eξ, sub_self]
      -- Goal: 0 ≤ A * (1 + 1) + B * sqDistStep μ ξ x
      apply add_nonneg
      · apply mul_nonneg (le_of_lt hA)
        linarith
      · exact mul_nonneg (le_of_lt hB) (sqDistStep_nonneg μ ξ x)
    · -- When μ x ≠ 0, use the AM-GM argument
      -- Key facts:
      -- 1. error_sum = 1 (from error_sum_eq_one_when_disagree)
      -- 2. error_diff = |2p - 1| (from error_diff_eq_abs_two_p_minus_one)
      -- 3. sqDistStep ≥ (2p-1)²/2 (from sqDistStep_ge_error_diff_sq)
      have h_sum : optimalErrorProb μ x + universalErrorProb μ ξ x = 1 :=
        error_sum_eq_one_when_disagree μ ξ x hμx h_agree
      -- Get the error difference bound
      set p := FiniteHorizon.condProb μ.toSemimeasure x true
      set u := universalErrorProb μ ξ x - optimalErrorProb μ x
      -- From error_sum = 1, we have universalErrorProb = 1 - optimalErrorProb
      -- So u = (1 - optimalErrorProb) - optimalErrorProb = 1 - 2*optimalErrorProb
      -- And |u| = |2p - 1| (this comes from the error_diff lemma)
      -- First, show u ≤ 1 and |u| ≤ 1
      have hu_le_1 : u ≤ 1 := by
        have he1 : universalErrorProb μ ξ x ≤ 1 := by
          unfold universalErrorProb errorProb
          have hle := condProb_le_one' μ.toSemimeasure x (universalPrediction ξ x)
          have hge : 0 ≤ FiniteHorizon.condProb μ.toSemimeasure x (universalPrediction ξ x) := by
            unfold FiniteHorizon.condProb conditionalENN
            exact ENNReal.toReal_nonneg
          linarith
        have he2 : 0 ≤ optimalErrorProb μ x := errorProb_nonneg μ _ x
        linarith
      -- Show u ≥ 0 when predictions disagree in the "bad" direction
      -- Actually u could be positive or negative depending on which predictor is worse
      -- But we only need to bound u from above, so if u ≤ 0, we're done
      by_cases hu_neg : u ≤ 0
      · calc u ≤ 0 := hu_neg
          _ ≤ A * (optimalErrorProb μ x + universalErrorProb μ ξ x) + B * sqDistStep μ ξ x :=
            hRHS_nonneg
      · -- u > 0: need the full argument
        push Not at hu_neg
        -- u > 0 and error_sum = 1, so u = |2p - 1| by the error_diff lemma
        have hu_abs : u = |2 * p - 1| := by
          -- From the error_diff_eq_abs_two_p_minus_one lemma, |u| = |2p - 1|
          -- Since u > 0, u = |u|
          have h_abs := error_diff_eq_abs_two_p_minus_one μ ξ x hμx h_agree
          have hu_pos : 0 < u := hu_neg
          rw [abs_of_pos hu_pos] at h_abs
          exact h_abs
        -- u = |2p - 1|, which is in [0, 1]
        have hu_01 : 0 ≤ |2 * p - 1| ∧ |2 * p - 1| ≤ 1 := by
          constructor
          · exact abs_nonneg _
          · have hp_le_1 := condProb_le_one' μ.toSemimeasure x true
            have hp_ge_0 : 0 ≤ p := by
              show 0 ≤ FiniteHorizon.condProb μ.toSemimeasure x true
              unfold FiniteHorizon.condProb conditionalENN
              exact ENNReal.toReal_nonneg
            rw [abs_le]
            constructor <;> linarith
        rw [hu_abs]
        -- Now use am_gm_error_bound with the error value
        have hsqDist_ge := sqDistStep_ge_error_diff_sq μ ξ x h_agree
        -- sqDistStep ≥ (2p - 1)² / 2 = |2p - 1|² / 2
        -- Since (a)² = |a|², we have (2p - 1)² / 2 = |2p - 1|² / 2
        have hsqDist_ge' : sqDistStep μ ξ x ≥ |2 * p - 1| ^ 2 / 2 := by
          have heq : (2 * p - 1) ^ 2 = |2 * p - 1| ^ 2 := (sq_abs _).symm
          calc sqDistStep μ ξ x ≥ (2 * p - 1) ^ 2 / 2 := hsqDist_ge
            _ = |2 * p - 1| ^ 2 / 2 := by rw [heq]
        -- By am_gm_error_bound: |2p-1| ≤ A + B * |2p-1|² / 2
        have ham_gm := am_gm_error_bound hAB hA hB hu_01.1 hu_01.2
        -- ham_gm has form |2p-1| ≤ A + B * |2p-1|² / 2, need to add parentheses
        have hAB_form : |2 * p - 1| ≤ A + B * (|2 * p - 1| ^ 2 / 2) := by
          have heq : B * |2 * p - 1| ^ 2 / 2 = B * (|2 * p - 1| ^ 2 / 2) := by ring
          rw [← heq]
          exact ham_gm
        -- Since sqDistStep ≥ |2p-1|²/2, we have B * sqDistStep ≥ B * |2p-1|²/2
        have hBsq : B * sqDistStep μ ξ x ≥ B * (|2 * p - 1| ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_left hsqDist_ge' (le_of_lt hB)
        -- Combine with error_sum = 1: A * error_sum = A
        calc |2 * p - 1|
            ≤ A + B * (|2 * p - 1| ^ 2 / 2) := hAB_form
          _ ≤ A + B * sqDistStep μ ξ x := by linarith
          _ = A * 1 + B * sqDistStep μ ξ x := by ring
          _ = A * (optimalErrorProb μ x + universalErrorProb μ ξ x) + B * sqDistStep μ ξ x := by
              rw [h_sum]

/-- Helper: For any A, B > 0 with 2AB ≥ 1, the aggregated error bound holds.
    E^ξ - E^μ ≤ A*(E^μ + E^ξ) + B*S_n

    **Proof sketch**: Sum the per-step bounds from `errorDiff_le_sqDist` using
    linearity of expectation. The algebraic manipulation uses:
    - Finset.sum_le_sum to aggregate pointwise bounds
    - Finset.sum_add_distrib and Finset.mul_sum for distribution -/
lemma error_bound_AB (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ)
    (A B : ℝ) (hAB : 2 * A * B ≥ 1) (hA : A > 0) (hB : B > 0) :
    expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≤
    A * (expectedOptimalErrors μ n + expectedUniversalErrors μ ξ n) +
    B * totalSqDist μ ξ n := by
  -- The proof aggregates the per-step bounds from errorDiff_le_sqDist
  -- using linearity of expectation and sum distribution.
  unfold expectedUniversalErrors expectedOptimalErrors totalSqDist
  -- E^ξ - E^μ = Σ_k E_μ[e^ξ_k - e^μ_k] (difference of sums = sum of differences)
  rw [← Finset.sum_sub_distrib]
  -- For the RHS, distribute A and B into the sums using calc
  calc ∑ k ∈ Finset.range n, (expectPrefix μ k (universalErrorProb μ ξ) -
                               expectPrefix μ k (optimalErrorProb μ))
      ≤ ∑ k ∈ Finset.range n, (A * expectPrefix μ k (optimalErrorProb μ) +
                               A * expectPrefix μ k (universalErrorProb μ ξ) +
                               B * expectPrefix μ k (sqDistStep μ ξ)) := by
        apply Finset.sum_le_sum
        intro k _hk
        unfold expectPrefix
        rw [← Finset.sum_sub_distrib]
        have hrhs2 : A * ∑ x : Fin k → Bool, (prefixPMF μ k x).toReal * optimalErrorProb μ (List.ofFn x) +
                     A * ∑ x : Fin k → Bool, (prefixPMF μ k x).toReal * universalErrorProb μ ξ (List.ofFn x) +
                     B * ∑ x : Fin k → Bool, (prefixPMF μ k x).toReal * sqDistStep μ ξ (List.ofFn x) =
                     ∑ x : Fin k → Bool, (A * ((prefixPMF μ k x).toReal * optimalErrorProb μ (List.ofFn x)) +
                                          A * ((prefixPMF μ k x).toReal * universalErrorProb μ ξ (List.ofFn x)) +
                                          B * ((prefixPMF μ k x).toReal * sqDistStep μ ξ (List.ofFn x))) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        rw [hrhs2]
        apply Finset.sum_le_sum
        intro f _hf
        have hstep := errorDiff_le_sqDist μ ξ (List.ofFn f) A B hAB hA hB
        have hμ_nonneg : 0 ≤ (prefixPMF μ k f).toReal := ENNReal.toReal_nonneg
        calc (prefixPMF μ k f).toReal * universalErrorProb μ ξ (List.ofFn f) -
               (prefixPMF μ k f).toReal * optimalErrorProb μ (List.ofFn f)
            = (prefixPMF μ k f).toReal * (universalErrorProb μ ξ (List.ofFn f) - optimalErrorProb μ (List.ofFn f)) := by ring
          _ ≤ (prefixPMF μ k f).toReal *
              (A * (optimalErrorProb μ (List.ofFn f) + universalErrorProb μ ξ (List.ofFn f)) +
               B * sqDistStep μ ξ (List.ofFn f)) := by
              apply mul_le_mul_of_nonneg_left hstep hμ_nonneg
          _ = A * ((prefixPMF μ k f).toReal * optimalErrorProb μ (List.ofFn f)) +
              A * ((prefixPMF μ k f).toReal * universalErrorProb μ ξ (List.ofFn f)) +
              B * ((prefixPMF μ k f).toReal * sqDistStep μ ξ (List.ofFn f)) := by ring
    _ = A * (∑ k ∈ Finset.range n, expectPrefix μ k (optimalErrorProb μ) +
             ∑ k ∈ Finset.range n, expectPrefix μ k (universalErrorProb μ ξ)) +
        B * ∑ k ∈ Finset.range n, expectPrefix μ k (sqDistStep μ ξ) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

/-- Helper: Expected errors are non-negative -/
lemma expectedOptimalErrors_nonneg (μ : PrefixMeasure) (n : ℕ) :
    0 ≤ expectedOptimalErrors μ n := by
  unfold expectedOptimalErrors expectPrefix
  apply Finset.sum_nonneg; intro k _; apply Finset.sum_nonneg; intro f _
  apply mul_nonneg ENNReal.toReal_nonneg; exact errorProb_nonneg μ _ _

lemma expectedUniversalErrors_nonneg (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) :
    0 ≤ expectedUniversalErrors μ ξ n := by
  unfold expectedUniversalErrors expectPrefix
  apply Finset.sum_nonneg; intro k _; apply Finset.sum_nonneg; intro f _
  apply mul_nonneg ENNReal.toReal_nonneg; exact errorProb_nonneg μ _ _

lemma totalSqDist_nonneg (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) :
    0 ≤ totalSqDist μ ξ n := by
  unfold totalSqDist expectPrefix
  apply Finset.sum_nonneg; intro k _; apply Finset.sum_nonneg; intro f _
  apply mul_nonneg ENNReal.toReal_nonneg; exact sqDistStep_nonneg μ ξ _

/-- Main bound from Theorem 3.36 (first form):
    E^ξ - E^μ ≤ √(2(E^μ + E^ξ)·S_n)

    Proof: Apply error_bound_AB with optimal A, B:
    - A = √(S_n / (2*(E^μ + E^ξ))), B = √((E^μ + E^ξ) / (2*S_n))
    - Then 2AB = 1 and A*X + B*S = √(2*X*S) where X = E^μ + E^ξ

    **Note**: This theorem aggregates the per-step error bounds from `errorDiff_le_sqDist`.
    The algebraic optimization proof is straightforward but tedious in Lean. -/
theorem error_bound_sqrt (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) :
    expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≤
    Real.sqrt (2 * (expectedOptimalErrors μ n + expectedUniversalErrors μ ξ n) *
      totalSqDist μ ξ n) := by
  apply Mettapedia.DecisionTheory.le_sqrt_of_linear_tradeoff
    (expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n)
    (expectedOptimalErrors μ n + expectedUniversalErrors μ ξ n) (totalSqDist μ ξ n)
    (add_nonneg (expectedOptimalErrors_nonneg μ n) (expectedUniversalErrors_nonneg μ ξ n))
    (totalSqDist_nonneg μ ξ n)
  intro a ha
  have reciprocal : 0 < 1 / (2 * a) := by positivity
  have bound := error_bound_AB μ ξ n a (1 / (2 * a)) (by field_simp; norm_num) ha reciprocal
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using bound

/-- The sharp zero/one regret bound in terms of cumulative squared distance. -/
theorem error_bound_sharp (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) :
    expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≤
      totalSqDist μ ξ n + Real.sqrt (4 * expectedOptimalErrors μ n * totalSqDist μ ξ n +
        (totalSqDist μ ξ n) ^ 2) := by
  have gap : 0 ≤ expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n :=
    sub_nonneg.mpr (expectedOptimalErrors_le_universal μ ξ n)
  have ho := expectedOptimalErrors_nonneg μ n
  have hu := expectedUniversalErrors_nonneg μ ξ n
  have hs := totalSqDist_nonneg μ ξ n
  have base := error_bound_sqrt μ ξ n
  have square := (sq_le_sq₀ gap (Real.sqrt_nonneg _)).mpr base
  rw [Real.sq_sqrt (by positivity : 0 ≤ 2 *
    (expectedOptimalErrors μ n + expectedUniversalErrors μ ξ n) * totalSqDist μ ξ n)] at square
  exact Mettapedia.DecisionTheory.sharp_of_quadratic
    (expectedUniversalErrors μ ξ n) (expectedOptimalErrors μ n) (totalSqDist μ ξ n)
    ho hs (by simpa only [add_comm] using square)

/-- The quadratic regret comparison gives the familiar simpler error bound. -/
theorem error_bound_main (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) :
    expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≤
    Real.sqrt (4 * expectedOptimalErrors μ n * totalSqDist μ ξ n) +
    2 * totalSqDist μ ξ n := by
  have sharp := error_bound_sharp μ ξ n
  have simple := Mettapedia.DecisionTheory.sharp_le_simple _ _
    (expectedOptimalErrors_nonneg μ n) (totalSqDist_nonneg μ ξ n)
  have root : Real.sqrt (4 * expectedOptimalErrors μ n * totalSqDist μ ξ n) =
      2 * Real.sqrt (expectedOptimalErrors μ n * totalSqDist μ ξ n) := by
    rw [show 4 * expectedOptimalErrors μ n * totalSqDist μ ξ n =
      4 * (expectedOptimalErrors μ n * totalSqDist μ ξ n) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [root]
  linarith

/-- Corollary: Under dominance, error regret is bounded by log(1/c).
    E^ξ - E^μ ≤ √(4·E^μ·log(1/c)) + 2·log(1/c) -/
theorem error_bound_dominance (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0) (n : ℕ)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false) :
    expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n ≤
    Real.sqrt (4 * expectedOptimalErrors μ n * Real.log (1 / c.toReal)) +
    2 * Real.log (1 / c.toReal) := by
  have hSn := convergence_bound μ ξ hdom hc0 n h_cond_true h_cond_false
  have hMain := error_bound_main μ ξ n
  have hEμ_nonneg : 0 ≤ expectedOptimalErrors μ n := by
    unfold expectedOptimalErrors expectPrefix
    apply Finset.sum_nonneg
    intro k _
    apply Finset.sum_nonneg
    intro f _
    apply mul_nonneg ENNReal.toReal_nonneg
    exact errorProb_nonneg μ _ _
  calc expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n
      ≤ Real.sqrt (4 * expectedOptimalErrors μ n * totalSqDist μ ξ n) +
        2 * totalSqDist μ ξ n := hMain
    _ ≤ Real.sqrt (4 * expectedOptimalErrors μ n * Real.log (1 / c.toReal)) +
        2 * Real.log (1 / c.toReal) := by
      apply add_le_add
      · apply Real.sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_left hSn
        apply mul_nonneg (by linarith) hEμ_nonneg
      · apply mul_le_mul_of_nonneg_left hSn (by norm_num : (0:ℝ) ≤ 2)

/-- For deterministic environments, the universal predictor makes only finitely many errors.

    **Hypothesis**: The environment μ is deterministic, i.e., expectedOptimalErrors μ n = 0 for all n.
    This means at each step, μ assigns probability 1 to the true outcome.

    Under this condition: E^ξ ≤ 2·log(1/c) for all n.

    The proof:
    1. From error_bound_dominance: E^ξ - E^μ ≤ √(4·E^μ·log(1/c)) + 2·log(1/c)
    2. With E^μ = 0: E^ξ ≤ √(0) + 2·log(1/c) = 2·log(1/c)
    3. Therefore E^ξ is uniformly bounded by 2·log(1/c). -/
theorem finite_errors_deterministic (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0)
    (h_cond_true : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (h_cond_false : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false)
    (h_deterministic : ∀ n, expectedOptimalErrors μ n = 0) :
    ∃ B : ℝ, ∀ n, expectedUniversalErrors μ ξ n ≤ B := by
  use 2 * Real.log (1 / c.toReal) + 1
  intro n
  have hbound := error_bound_dominance μ ξ hdom hc0 n h_cond_true h_cond_false
  rw [h_deterministic n] at hbound
  -- Simplify: √(4 * 0 * log(1/c)) = √0 = 0
  have hsimpl : Real.sqrt (4 * 0 * Real.log (1 / c.toReal)) = 0 := by
    simp only [mul_zero, zero_mul, Real.sqrt_zero]
  rw [hsimpl] at hbound
  simp only [zero_add, sub_zero] at hbound
  calc expectedUniversalErrors μ ξ n
      ≤ 2 * Real.log (1 / c.toReal) := hbound
    _ ≤ 2 * Real.log (1 / c.toReal) + 1 := by linarith

/-- Instantaneous threshold-error regret; null histories are excluded explicitly. -/
theorem instantaneous_error_bound (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString)
    (hx : μ x ≠ 0) :
    |universalErrorProb μ ξ x - optimalErrorProb μ x| ≤ 2 * Real.sqrt (sqDistStep μ ξ x) := by
  by_cases agrees : universalPrediction ξ x = optimalPrediction μ x
  · rw [error_eq_when_predictions_agree μ ξ x agrees, sub_self, abs_zero]
    positivity
  · rw [error_diff_eq_abs_two_p_minus_one μ ξ x hx agrees]
    have bound := sqDistStep_ge_error_diff_sq μ ξ x agrees
    have square := Real.sq_sqrt (sqDistStep_nonneg μ ξ x)
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    nlinarith [sq_abs (2 * condProb μ.toSemimeasure x true - 1)]

theorem expectedOptimalErrors_le_horizon (μ : PrefixMeasure) (n : ℕ) : expectedOptimalErrors μ n ≤ n := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
      apply (expectPrefix_mono μ k (g := fun _ => 1) ?_).trans_eq (expectPrefix_const μ k 1)
      intro x
      exact sub_le_self 1 (show 0 ≤ FiniteHorizon.condProb μ.toSemimeasure x (optimalPrediction μ x) from
        ENNReal.toReal_nonneg)
    _ = _ := by simp

/-- The historical threshold-error predictor retains its vanishing average regret. -/
theorem average_error_regret_vanishes (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (dominates : Dominates ξ μ c) (hc : c ≠ 0)
    (positiveTrue : ∀ (k : ℕ) (x : BinString), x.length = k →
      FiniteHorizon.condProb ξ x true ∈ Set.Ioo (0 : ℝ) 1)
    (positiveFalse : ∀ (k : ℕ) (x : BinString), x.length = k →
      0 < FiniteHorizon.condProb ξ x false) :
    Filter.Tendsto (fun n => (expectedUniversalErrors μ ξ n - expectedOptimalErrors μ n) / n)
      Filter.atTop (nhds 0) := by
  have hd : 0 ≤ Real.log (1 / c.toReal) := (relEntropy_zero_nonneg μ ξ dominates hc).trans
    (relEntropy_le_log_inv_of_dominates μ ξ dominates hc 0)
  apply Mettapedia.DecisionTheory.average_of_root_bound _ _ hd
    (fun n => sub_nonneg.mpr (expectedOptimalErrors_le_universal μ ξ n))
  intro n
  have bound := error_bound_dominance μ ξ dominates hc n positiveTrue positiveFalse
  have root : Real.sqrt (4 * expectedOptimalErrors μ n * Real.log (1 / c.toReal)) ≤
      2 * Real.sqrt ((n : ℝ) * Real.log (1 / c.toReal)) := by
    calc
      _ ≤ Real.sqrt (4 * (n : ℝ) * Real.log (1 / c.toReal)) := Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (expectedOptimalErrors_le_horizon μ n) (by norm_num : (0 : ℝ) ≤ 4)) hd)
      _ = _ := by
        rw [show 4 * (n : ℝ) * Real.log (1 / c.toReal) =
          4 * ((n : ℝ) * Real.log (1 / c.toReal)) by ring,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
          show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

end ErrorBounds

end Mettapedia.UniversalAI.UniversalPrediction
