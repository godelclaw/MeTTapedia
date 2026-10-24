import Mettapedia.UniversalAI.UniversalPrediction.ErrorBounds

/-!
# Loss-specific decisions and sharp cumulative regret

For normalized binary forecasts, a half-probability threshold minimizes
zero/one loss. A general bounded loss requires minimizing that loss under
the model's own forecast.
The actual environment supplies the evaluation weights. Conditional rows on
its positive-mass histories are normalized explicitly; null histories have
zero expectation weight and retain their separate threshold behavior.

The finite analytic certificate yields Hutter's general loss bound
`R ≤ D + sqrt (4 L D + D²)`, with `L` the optimal cumulative loss. Prefix
entropy includes its root term: the chain rule sums to `Dₙ - D₀`.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction.LossBounds

open Mettapedia.DecisionTheory
open Mettapedia.InformationTheory.FiniteRV
open FiniteHorizon Convergence ErrorBounds
open scoped Classical BigOperators

abbrev BinaryLoss := BoundedLoss Bool Bool

/-- Zero/one classification loss, distinct from an arbitrary unit-interval loss. -/
def zeroOneLoss : BinaryLoss where
  toFun a x := if a = x then 0 else 1
  nonneg := by intro a x; split_ifs <;> norm_num
  le_one := by intro a x; split_ifs <;> norm_num

def weights (ρ : Semimeasure) (x : BinString) : Bool → ℝ := fun b => condProb ρ x b

def stepRisk (ρ : Semimeasure) (loss : BinaryLoss) (a : Bool) (x : BinString) : ℝ :=
  expectedRisk (weights ρ x) loss a

def bayesAction (ρ : Semimeasure) (loss : BinaryLoss) (x : BinString) : Bool :=
  bayesBool (weights ρ x) loss

def oracleRisk (μ : PrefixMeasure) (loss : BinaryLoss) (x : BinString) : ℝ :=
  stepRisk μ.toSemimeasure loss (bayesAction μ.toSemimeasure loss x) x

def decisionRisk (μ : PrefixMeasure) (ρ : Semimeasure) (loss : BinaryLoss) (x : BinString) : ℝ :=
  stepRisk μ.toSemimeasure loss (bayesAction ρ loss x) x

/-- Evaluation of the historical half-probability threshold policy. -/
def thresholdRisk (μ : PrefixMeasure) (ρ : Semimeasure) (loss : BinaryLoss) (x : BinString) : ℝ :=
  stepRisk μ.toSemimeasure loss (universalPrediction ρ x) x

@[simp] theorem stepRisk_eq (ρ : Semimeasure) (loss : BinaryLoss) (a : Bool) (x : BinString) :
    stepRisk ρ loss a x = condProb ρ x true * loss a true + condProb ρ x false * loss a false := by
  simp [stepRisk, expectedRisk, weights, add_comm]

theorem bayesAction_best (ρ : Semimeasure) (loss : BinaryLoss) (x : BinString) (a : Bool) :
    stepRisk ρ loss (bayesAction ρ loss x) x ≤ stepRisk ρ loss a x :=
  bayesBool_best (weights ρ x) loss a

theorem oracleRisk_eq_min (μ : PrefixMeasure) (loss : BinaryLoss) (x : BinString) :
    oracleRisk μ loss x = min (stepRisk μ.toSemimeasure loss true x)
      (stepRisk μ.toSemimeasure loss false x) := by
  apply le_antisymm
  · exact le_min (bayesAction_best _ _ _ true) (bayesAction_best _ _ _ false)
  · unfold oracleRisk
    cases bayesAction μ.toSemimeasure loss x
    · exact min_le_right _ _
    · exact min_le_left _ _

theorem stepRisk_nonneg (ρ : Semimeasure) (loss : BinaryLoss) (a : Bool) (x : BinString) :
    0 ≤ stepRisk ρ loss a x := expectedRisk_nonneg _ (fun _ => ENNReal.toReal_nonneg) loss a

theorem stepRisk_le_one (ρ : Semimeasure) (loss : BinaryLoss) (a : Bool) (x : BinString) :
    stepRisk ρ loss a x ≤ 1 := by
  have bound := expectedRisk_le_mass (weights ρ x) (fun _ => ENNReal.toReal_nonneg) loss a
  exact bound.trans (by simpa [weights, add_comm] using condProb_sum_le_one ρ x)

theorem regret_nonneg (μ : PrefixMeasure) (ρ : Semimeasure) (loss : BinaryLoss) (x : BinString) :
    0 ≤ decisionRisk μ ρ loss x - oracleRisk μ loss x :=
  sub_nonneg.mpr (bayesAction_best μ.toSemimeasure loss x _)

/-- The finite ℓ¹ comparison specializes to normalized binary squared distance. -/
theorem decision_regret_le_sqDist (μ : PrefixMeasure) (ρ : Semimeasure)
    (loss : BinaryLoss) (x : BinString) (hx : μ x ≠ 0)
    (normalized : condProb ρ x true + condProb ρ x false = 1) :
    |decisionRisk μ ρ loss x - oracleRisk μ loss x| ≤ 2 * Real.sqrt (sqDistStep μ ρ x) := by
  rw [abs_of_nonneg (regret_nonneg μ ρ loss x)]
  have bound := risk_regret_le_l1 (weights μ.toSemimeasure x) (weights ρ x) loss
    (bayesAction ρ loss x) (bayesAction μ.toSemimeasure loss x) (bayesAction_best ρ loss x _)
  simp only [weights, Fintype.sum_bool] at bound
  apply bound.trans
  have actual := condProb_sum_eq_one μ x hx
  have complement : condProb μ.toSemimeasure x false - condProb ρ x false =
      -(condProb μ.toSemimeasure x true - condProb ρ x true) := by linarith
  rw [complement, abs_neg]
  have square := Real.sq_sqrt (sqDistStep_nonneg μ ρ x)
  have distance : sqDistStep μ ρ x = 2 * (condProb μ.toSemimeasure x true - condProb ρ x true) ^ 2 :=
    Entropy.sqDistBinary_eq_two_mul _ _
  apply (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)).mp
  nlinarith [sq_abs (condProb μ.toSemimeasure x true - condProb ρ x true), distance]

/-- Normalization is required only where the actual environment has positive mass. -/
def NormalizedOnSupport (μ : PrefixMeasure) (ρ : Semimeasure) : Prop :=
  ∀ x, μ x ≠ 0 → condProb ρ x true + condProb ρ x false = 1

theorem conditional_support (μ : PrefixMeasure) (ρ : Semimeasure) {c : ENNReal}
    (dominates : Dominates ρ μ c) (hc : c ≠ 0) (x : BinString) (hx : μ x ≠ 0)
    (b : Bool) (positive : 0 < weights μ.toSemimeasure x b) : 0 < weights ρ x b := by
  have parent : ρ x ≠ 0 := fun zero => hx (Dominates.eq_zero_of_eq_zero (h := dominates) hc x zero)
  have actualChild : μ (x ++ [b]) ≠ 0 := by
    intro zero
    simp [weights, condProb, conditionalENN, zero] at positive
  have child : ρ (x ++ [b]) ≠ 0 := fun zero =>
    actualChild (Dominates.eq_zero_of_eq_zero (h := dominates) hc (x ++ [b]) zero)
  exact ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨child, semimeasure_ne_top ρ x⟩)
    (ENNReal.div_ne_top (semimeasure_ne_top ρ (x ++ [b])) parent)

theorem step_kl_tradeoff (μ : PrefixMeasure) (ρ : Semimeasure) {c : ENNReal}
    (dominates : Dominates ρ μ c) (hc : c ≠ 0) (normalized : NormalizedOnSupport μ ρ)
    (loss : BinaryLoss) (x : BinString) (hx : μ x ≠ 0) (a : ℝ) (ha : 0 < a) :
    decisionRisk μ ρ loss x ≤ (1 + a) * oracleRisk μ loss x +
      ((a + 2) ^ 2 / (4 * a)) * stepRelEntropy μ ρ x := by
  have bound := risk_kl_tradeoff (weights μ.toSemimeasure x) (weights ρ x)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (by simpa [weights, add_comm] using condProb_sum_eq_one μ x hx)
    (by simpa [weights, add_comm] using (normalized x hx).le)
    (conditional_support μ ρ dominates hc x hx) loss
    (bayesAction ρ loss x) (bayesAction μ.toSemimeasure loss x)
    (bayesAction_best ρ loss x _) a ha
  simpa only [decisionRisk, oracleRisk, stepRisk, klSum_eq_sum, weights,
    Fintype.sum_bool, stepRelEntropy, add_comm] using bound

def cumulativeDecisionLoss (μ : PrefixMeasure) (ρ : Semimeasure) (loss : BinaryLoss) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, expectPrefix μ k (decisionRisk μ ρ loss)

def cumulativeOracleLoss (μ : PrefixMeasure) (loss : BinaryLoss) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, expectPrefix μ k (oracleRisk μ loss)

theorem cumulativeOracleLoss_nonneg (μ : PrefixMeasure) (loss : BinaryLoss) (n : ℕ) :
    0 ≤ cumulativeOracleLoss μ loss n := by
  apply Finset.sum_nonneg
  intro k _
  rw [← expectPrefix_const μ k 0]
  exact expectPrefix_mono μ k
    (fun x => stepRisk_nonneg μ.toSemimeasure loss (bayesAction μ.toSemimeasure loss x) x)

theorem cumulative_regret_nonneg (μ : PrefixMeasure) (ρ : Semimeasure) (loss : BinaryLoss) (n : ℕ) :
    0 ≤ cumulativeDecisionLoss μ ρ loss n - cumulativeOracleLoss μ loss n := by
  apply sub_nonneg.mpr
  apply Finset.sum_le_sum
  intro k _
  exact expectPrefix_mono μ k fun x => sub_nonneg.mp (regret_nonneg μ ρ loss x)

theorem cumulativeOracleLoss_le_horizon (μ : PrefixMeasure) (loss : BinaryLoss) (n : ℕ) :
    cumulativeOracleLoss μ loss n ≤ n := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun k _ =>
      (expectPrefix_mono μ k fun x => stepRisk_le_one _ loss _ x).trans_eq (expectPrefix_const μ k 1)
    _ = _ := by simp

theorem cumulative_kl_tradeoff (μ : PrefixMeasure) (ρ : Semimeasure) {c : ENNReal}
    (dominates : Dominates ρ μ c) (hc : c ≠ 0) (normalized : NormalizedOnSupport μ ρ)
    (loss : BinaryLoss) (n : ℕ) (a : ℝ) (ha : 0 < a) :
    cumulativeDecisionLoss μ ρ loss n ≤ (1 + a) * cumulativeOracleLoss μ loss n +
      ((a + 2) ^ 2 / (4 * a)) * relEntropy μ ρ n := by
  have step (k : ℕ) : expectPrefix μ k (decisionRisk μ ρ loss) ≤
      (1 + a) * expectPrefix μ k (oracleRisk μ loss) +
        ((a + 2) ^ 2 / (4 * a)) * expectPrefix μ k (stepRelEntropy μ ρ) := by
    rw [← expectPrefix_affine]
    unfold expectPrefix
    apply Finset.sum_le_sum
    intro f _
    by_cases zero : μ (List.ofFn f) = 0
    · simp [prefixPMF_apply, zero]
    · exact mul_le_mul_of_nonneg_left (step_kl_tradeoff μ ρ dominates hc normalized loss _ zero a ha)
        ENNReal.toReal_nonneg
  calc
    _ ≤ ∑ k ∈ Finset.range n, ((1 + a) * expectPrefix μ k (oracleRisk μ loss) +
        ((a + 2) ^ 2 / (4 * a)) * expectPrefix μ k (stepRelEntropy μ ρ)) :=
      Finset.sum_le_sum fun k _ => step k
    _ = (1 + a) * cumulativeOracleLoss μ loss n +
        ((a + 2) ^ 2 / (4 * a)) * totalStepEntropy μ ρ n := by
      simp only [cumulativeOracleLoss, totalStepEntropy, Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := by
      rw [← relEntropy_diff_eq_sum_step μ ρ dominates hc n]
      have root := relEntropy_zero_nonneg μ ρ dominates hc
      have coefficient : 0 ≤ (a + 2) ^ 2 / (4 * a) := by positivity
      nlinarith

theorem stepEntropy_nonneg (μ : PrefixMeasure) (ρ : Semimeasure) {c : ENNReal}
    (dominates : Dominates ρ μ c) (hc : c ≠ 0) (x : BinString) : 0 ≤ stepRelEntropy μ ρ x := by
  by_cases zero : μ x = 0
  · simp [stepRelEntropy, condProb, conditionalENN, zero]
  · have bound := klSumOn_nonneg Finset.univ (weights μ.toSemimeasure x) (weights ρ x)
      (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
      (fun b _ => conditional_support μ ρ dominates hc x zero b)
      (by
        simp only [weights, Fintype.sum_bool]
        have actual := condProb_sum_eq_one μ x zero
        have model := condProb_sum_le_one ρ x
        linarith)
    simpa [klSumOn, weights, stepRelEntropy, add_comm] using bound

theorem prefixEntropy_nonneg (μ : PrefixMeasure) (ρ : Semimeasure) {c : ENNReal}
    (dominates : Dominates ρ μ c) (hc : c ≠ 0) (n : ℕ) : 0 ≤ relEntropy μ ρ n := by
  have steps : 0 ≤ totalStepEntropy μ ρ n := Finset.sum_nonneg fun k _ => by
    simpa using expectPrefix_mono μ k (fun x => stepEntropy_nonneg μ ρ dominates hc x)
  have root := relEntropy_zero_nonneg μ ρ dominates hc
  have chain := relEntropy_diff_eq_sum_step μ ρ dominates hc n
  linarith

/-- Hutter's sharp bounded-loss theorem, with an explicit prefix-entropy budget. -/
theorem cumulative_regret_le_kl (μ : PrefixMeasure) (ρ : Semimeasure) {c : ENNReal}
    (dominates : Dominates ρ μ c) (hc : c ≠ 0) (normalized : NormalizedOnSupport μ ρ)
    (loss : BinaryLoss) (n : ℕ) :
    cumulativeDecisionLoss μ ρ loss n - cumulativeOracleLoss μ loss n ≤
      relEntropy μ ρ n + Real.sqrt (4 * cumulativeOracleLoss μ loss n * relEntropy μ ρ n +
        (relEntropy μ ρ n) ^ 2) :=
  sharp_of_tradeoff _ _ _ (cumulativeOracleLoss_nonneg μ loss n)
    (prefixEntropy_nonneg μ ρ dominates hc n)
    (cumulative_kl_tradeoff μ ρ dominates hc normalized loss n)

/-- The dominance constant fixes a single entropy budget for every horizon. -/
theorem cumulative_regret_le_dominance (μ : PrefixMeasure) (ρ : Semimeasure) {c : ENNReal}
    (dominates : Dominates ρ μ c) (hc : c ≠ 0) (normalized : NormalizedOnSupport μ ρ)
    (loss : BinaryLoss) (n : ℕ) :
    cumulativeDecisionLoss μ ρ loss n - cumulativeOracleLoss μ loss n ≤
      Real.log (1 / c.toReal) + Real.sqrt (4 * cumulativeOracleLoss μ loss n *
        Real.log (1 / c.toReal) + Real.log (1 / c.toReal) ^ 2) := by
  have hd : 0 ≤ Real.log (1 / c.toReal) :=
    (prefixEntropy_nonneg μ ρ dominates hc 0).trans (relEntropy_le_log_inv_of_dominates μ ρ dominates hc 0)
  apply sharp_of_tradeoff _ _ _ (cumulativeOracleLoss_nonneg μ loss n) hd
  intro a ha
  have bound := cumulative_kl_tradeoff μ ρ dominates hc normalized loss n a ha
  have entropy := mul_le_mul_of_nonneg_left (relEntropy_le_log_inv_of_dominates μ ρ dominates hc n)
    (show 0 ≤ (a + 2) ^ 2 / (4 * a) by positivity)
  linarith

theorem cumulative_regret_le_root_horizon (μ : PrefixMeasure) (ρ : Semimeasure) {c : ENNReal}
    (dominates : Dominates ρ μ c) (hc : c ≠ 0) (normalized : NormalizedOnSupport μ ρ)
    (loss : BinaryLoss) (n : ℕ) :
    cumulativeDecisionLoss μ ρ loss n - cumulativeOracleLoss μ loss n ≤
      2 * Real.log (1 / c.toReal) + 2 * Real.sqrt ((n : ℝ) * Real.log (1 / c.toReal)) := by
  have hd : 0 ≤ Real.log (1 / c.toReal) :=
    (prefixEntropy_nonneg μ ρ dominates hc 0).trans (relEntropy_le_log_inv_of_dominates μ ρ dominates hc 0)
  have simple := (cumulative_regret_le_dominance μ ρ dominates hc normalized loss n).trans
    (sharp_le_simple _ _ (cumulativeOracleLoss_nonneg μ loss n) hd)
  exact simple.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (cumulativeOracleLoss_le_horizon μ loss n) hd))
    (by norm_num : (0 : ℝ) ≤ 2)))

theorem average_decision_regret_vanishes (μ : PrefixMeasure) (ρ : Semimeasure) {c : ENNReal}
    (dominates : Dominates ρ μ c) (hc : c ≠ 0) (normalized : NormalizedOnSupport μ ρ)
    (loss : BinaryLoss) : Filter.Tendsto
      (fun n => (cumulativeDecisionLoss μ ρ loss n - cumulativeOracleLoss μ loss n) / n)
      Filter.atTop (nhds 0) :=
  average_of_root_bound _ _
    ((prefixEntropy_nonneg μ ρ dominates hc 0).trans (relEntropy_le_log_inv_of_dominates μ ρ dominates hc 0))
    (cumulative_regret_nonneg μ ρ loss) (cumulative_regret_le_root_horizon μ ρ dominates hc normalized loss)

theorem loss_bound_of_oracle_zero (μ : PrefixMeasure) (ρ : Semimeasure) {c : ENNReal}
    (dominates : Dominates ρ μ c) (hc : c ≠ 0) (normalized : NormalizedOnSupport μ ρ)
    (loss : BinaryLoss) (n : ℕ) (zero : cumulativeOracleLoss μ loss n = 0) :
    cumulativeDecisionLoss μ ρ loss n ≤ 2 * Real.log (1 / c.toReal) := by
  have sharp := (cumulative_regret_le_dominance μ ρ dominates hc normalized loss n).trans
    (sharp_le_simple _ _ (cumulativeOracleLoss_nonneg μ loss n)
      ((prefixEntropy_nonneg μ ρ dominates hc 0).trans (relEntropy_le_log_inv_of_dominates μ ρ dominates hc 0)))
  simpa only [zero, sub_zero, zero_mul, Real.sqrt_zero, mul_zero, add_zero] using sharp

/-- A threshold policy has only the unconditional horizon bound for arbitrary losses. -/
theorem threshold_regret_le_horizon (μ : PrefixMeasure) (ρ : Semimeasure) (loss : BinaryLoss) (n : ℕ) :
    (∑ k ∈ Finset.range n, expectPrefix μ k (fun x => thresholdRisk μ ρ loss x - oracleRisk μ loss x)) ≤ n := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
      apply (expectPrefix_mono μ k (g := fun _ => 1) ?_).trans_eq (expectPrefix_const μ k 1)
      intro x
      have upper := stepRisk_le_one μ.toSemimeasure loss (universalPrediction ρ x) x
      have lower := stepRisk_nonneg μ.toSemimeasure loss (bayesAction μ.toSemimeasure loss x) x
      change stepRisk μ.toSemimeasure loss (universalPrediction ρ x) x -
        stepRisk μ.toSemimeasure loss (bayesAction μ.toSemimeasure loss x) x ≤ 1
      linarith
    _ = _ := by simp

theorem bayesAction_zeroOne_eq_threshold (ρ : Semimeasure) (x : BinString)
    (normalized : condProb ρ x true + condProb ρ x false = 1) :
    bayesAction ρ zeroOneLoss x = universalPrediction ρ x := by
  simp only [bayesAction, bayesBool, expectedRisk, weights, Fintype.sum_bool, zeroOneLoss,
    Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
    mul_zero, zero_add, mul_one, add_zero, universalPrediction]
  congr 1
  apply propext
  constructor <;> intro h <;> linarith

theorem stepRisk_zeroOne_eq_error (μ : PrefixMeasure) (x : BinString) (hx : μ x ≠ 0) (b : Bool) :
    stepRisk μ.toSemimeasure zeroOneLoss b x = errorProb μ b x := by
  have total := condProb_sum_eq_one μ x hx
  cases b <;> simp [stepRisk_eq, zeroOneLoss, errorProb] <;> linarith

theorem oracleRisk_zeroOne_eq_error (μ : PrefixMeasure) (x : BinString) (hx : μ x ≠ 0) :
    oracleRisk μ zeroOneLoss x = optimalErrorProb μ x := by
  unfold oracleRisk
  rw [bayesAction_zeroOne_eq_threshold _ _ (condProb_sum_eq_one μ x hx), stepRisk_zeroOne_eq_error μ x hx]
  rfl

theorem cumulative_zeroOne_eq_errors (μ : PrefixMeasure) (ρ : Semimeasure)
    (normalized : NormalizedOnSupport μ ρ) (n : ℕ) :
    cumulativeDecisionLoss μ ρ zeroOneLoss n = expectedUniversalErrors μ ρ n := by
  apply Finset.sum_congr rfl
  intro k _
  apply expectPrefix_congr_on_support μ k
  intro x hx
  unfold decisionRisk
  rw [bayesAction_zeroOne_eq_threshold ρ x (normalized x hx), stepRisk_zeroOne_eq_error μ x hx]
  rfl

theorem cumulativeOracle_zeroOne_eq_errors (μ : PrefixMeasure) (n : ℕ) :
    cumulativeOracleLoss μ zeroOneLoss n = expectedOptimalErrors μ n := by
  apply Finset.sum_congr rfl
  intro k _
  exact expectPrefix_congr_on_support μ k (oracleRisk_zeroOne_eq_error μ)

/-- The zero/one specialization retains the stronger existing squared-distance error route. -/
theorem zeroOne_loss_bound (μ : PrefixMeasure) (ρ : Semimeasure) {c : ENNReal}
    (dominates : Dominates ρ μ c) (hc : c ≠ 0) (normalized : NormalizedOnSupport μ ρ)
    (positiveTrue : ∀ (k : ℕ) (x : BinString), x.length = k → condProb ρ x true ∈ Set.Ioo (0 : ℝ) 1)
    (positiveFalse : ∀ (k : ℕ) (x : BinString), x.length = k → 0 < condProb ρ x false) (n : ℕ) :
    cumulativeDecisionLoss μ ρ zeroOneLoss n - cumulativeOracleLoss μ zeroOneLoss n ≤
      Real.sqrt (4 * expectedOptimalErrors μ n * Real.log (1 / c.toReal)) +
        2 * Real.log (1 / c.toReal) := by
  rw [cumulative_zeroOne_eq_errors μ ρ normalized, cumulativeOracle_zeroOne_eq_errors]
  exact error_bound_dominance μ ρ dominates hc n positiveTrue positiveFalse

/-! ## Separating controls -/

def asymmetricLoss : BinaryLoss where
  toFun pred actual :=
    match pred, actual with
    | true, true => 0
    | true, false => 1
    | false, true => 0.01
    | false, false => 0
  nonneg := by intro p a; cases p <;> cases a <;> norm_num
  le_one := by intro p a; cases p <;> cases a <;> norm_num

/-- Count true values in a boolean list -/
def countTrue (x : BinString) : ℕ := (x.filter (· = true)).length

/-- Count false values in a boolean list -/
def countFalse (x : BinString) : ℕ := (x.filter (· = false)).length

@[simp] lemma countTrue_nil : countTrue [] = 0 := rfl
@[simp] lemma countFalse_nil : countFalse [] = 0 := rfl
@[simp] lemma countTrue_cons_true (x : BinString) : countTrue (true :: x) = countTrue x + 1 := by
  simp [countTrue, List.filter]
@[simp] lemma countTrue_cons_false (x : BinString) : countTrue (false :: x) = countTrue x := by
  simp [countTrue, List.filter]
@[simp] lemma countFalse_cons_true (x : BinString) : countFalse (true :: x) = countFalse x := by
  simp [countFalse, List.filter]
@[simp] lemma countFalse_cons_false (x : BinString) : countFalse (false :: x) = countFalse x + 1 := by
  simp [countFalse, List.filter]
@[simp] lemma countTrue_append (x y : BinString) : countTrue (x ++ y) = countTrue x + countTrue y := by
  simp [countTrue]
@[simp] lemma countFalse_append (x y : BinString) : countFalse (x ++ y) = countFalse x + countFalse y := by
  simp [countFalse]

/-- Count lemmas for singleton lists -/
@[simp] lemma countTrue_singleton_true : countTrue [true] = 1 := rfl
@[simp] lemma countTrue_singleton_false : countTrue [false] = 0 := rfl
@[simp] lemma countFalse_singleton_true : countFalse [true] = 0 := rfl
@[simp] lemma countFalse_singleton_false : countFalse [false] = 1 := rfl

/-- A biased coin measure: at each step, P(true) = p, P(false) = 1-p.
    For 0 < p < 1, this is a valid prefix measure. -/
noncomputable def biasedCoinMeasure (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : PrefixMeasure where
  toFun := fun x => ENNReal.ofReal (p ^ countTrue x * (1 - p) ^ countFalse x)
  root_eq_one' := by simp
  additive' := fun x => by
    have hp_nn : 0 ≤ p := le_of_lt hp0
    have h1mp_nn : 0 ≤ 1 - p := by linarith
    simp only [countTrue_append, countFalse_append, countTrue_singleton_true,
               countFalse_singleton_true, countTrue_singleton_false, countFalse_singleton_false,
               add_zero]
    have h1 : 0 ≤ p ^ countTrue x * (1 - p) ^ (countFalse x + 1) := by positivity
    have h2 : 0 ≤ p ^ (countTrue x + 1) * (1 - p) ^ countFalse x := by positivity
    rw [← ENNReal.ofReal_add h1 h2]
    congr 1
    rw [pow_succ, pow_succ]; ring

/-- The conditional probability under a biased coin measure is exactly p for true. -/
lemma biasedCoinMeasure_condProb_true (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (x : BinString) :
    FiniteHorizon.condProb (biasedCoinMeasure p hp0 hp1).toSemimeasure x true = p := by
  unfold FiniteHorizon.condProb conditionalENN
  simp only [PrefixMeasure.toSemimeasure_apply, biasedCoinMeasure]
  have hp_nn : 0 ≤ p := le_of_lt hp0
  have h1mp_pos : 0 < 1 - p := by linarith
  have hdenom_pos : 0 < p ^ countTrue x * (1 - p) ^ countFalse x := by positivity
  have hdenom_ne : ENNReal.ofReal (p ^ countTrue x * (1 - p) ^ countFalse x) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hdenom_pos
  simp only [countTrue_append, countFalse_append, countTrue_singleton_true,
             countFalse_singleton_true, add_zero]
  rw [pow_succ]
  have hnum : p ^ countTrue x * p * (1 - p) ^ countFalse x =
              p ^ countTrue x * (1 - p) ^ countFalse x * p := by ring
  rw [hnum, ENNReal.ofReal_mul (le_of_lt hdenom_pos)]
  rw [mul_comm (ENNReal.ofReal (p ^ countTrue x * (1 - p) ^ countFalse x)) (ENNReal.ofReal p)]
  rw [mul_div_assoc, ENNReal.div_self hdenom_ne ENNReal.ofReal_ne_top, mul_one]
  simp only [ENNReal.toReal_ofReal hp_nn]

/-- The conditional probability under a biased coin measure is 1-p for false. -/
lemma biasedCoinMeasure_condProb_false (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (x : BinString) :
    FiniteHorizon.condProb (biasedCoinMeasure p hp0 hp1).toSemimeasure x false = 1 - p := by
  unfold FiniteHorizon.condProb conditionalENN
  simp only [PrefixMeasure.toSemimeasure_apply, biasedCoinMeasure]
  have h1mp_pos : 0 < 1 - p := by linarith
  have h1mp_nn : 0 ≤ 1 - p := le_of_lt h1mp_pos
  have hdenom_pos : 0 < p ^ countTrue x * (1 - p) ^ countFalse x := by positivity
  have hdenom_ne : ENNReal.ofReal (p ^ countTrue x * (1 - p) ^ countFalse x) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hdenom_pos
  simp only [countTrue_append, countFalse_append, countTrue_singleton_false,
             countFalse_singleton_false, add_zero]
  rw [pow_succ]
  have hnum : p ^ countTrue x * ((1 - p) ^ countFalse x * (1 - p)) =
              p ^ countTrue x * (1 - p) ^ countFalse x * (1 - p) := by ring
  rw [hnum, ENNReal.ofReal_mul (le_of_lt hdenom_pos)]
  rw [mul_comm (ENNReal.ofReal (p ^ countTrue x * (1 - p) ^ countFalse x)) (ENNReal.ofReal (1 - p))]
  rw [mul_div_assoc, ENNReal.div_self hdenom_ne ENNReal.ofReal_ne_top, mul_one]
  simp only [ENNReal.toReal_ofReal h1mp_nn]


/-- Identical forecasts do not rescue a loss-insensitive threshold policy. -/
theorem threshold_fails_for_asymmetric_loss :
    ∃ (μ : PrefixMeasure) (ρ : Semimeasure) (x : BinString) (loss : BinaryLoss),
      |thresholdRisk μ ρ loss x - oracleRisk μ loss x| > 2 * Real.sqrt (sqDistStep μ ρ x) := by
  let μ := biasedCoinMeasure 0.6 (by norm_num) (by norm_num)
  have truth : condProb μ.toSemimeasure [] true = 0.6 := biasedCoinMeasure_condProb_true _ _ _ _
  have falsity : condProb μ.toSemimeasure [] false = 0.4 := by
    rw [biasedCoinMeasure_condProb_false]; norm_num
  have chosen : universalPrediction μ.toSemimeasure [] = true := by
    norm_num [universalPrediction, truth]
  have high : stepRisk μ.toSemimeasure asymmetricLoss true [] = 0.4 := by
    rw [stepRisk_eq, truth, falsity]; norm_num [asymmetricLoss]
  have low : stepRisk μ.toSemimeasure asymmetricLoss false [] = 0.006 := by
    rw [stepRisk_eq, truth, falsity]; norm_num [asymmetricLoss]
  have optimal : oracleRisk μ asymmetricLoss [] = 0.006 := by
    rw [oracleRisk_eq_min, high, low]; norm_num
  refine ⟨μ, μ.toSemimeasure, [], asymmetricLoss, ?_⟩
  have same : sqDistStep μ μ.toSemimeasure [] = 0 := by
    simp [sqDistStep, Entropy.sqDistBinary_eq_two_mul]
  rw [same, Real.sqrt_zero, mul_zero, optimal]
  unfold thresholdRisk
  rw [chosen, high]
  norm_num

/-- Rare mistakes distinguish the KL loss bound from an invalid squared-distance substitution. -/
def rareLoss : BinaryLoss where
  toFun action outcome := if action = outcome then 0 else if action then 1 / 8 else 1
  nonneg := by intro a x; cases a <;> cases x <;> norm_num
  le_one := by intro a x; cases a <;> cases x <;> norm_num

theorem squared_distance_fails_for_bayes_loss :
    let p : Bool → ℝ := fun b => if b then 0 else 1
    let q : Bool → ℝ := fun b => if b then 1 / 8 else 7 / 8
    let optimal := expectedRisk p rareLoss (bayesBool p rareLoss)
    let distance := Entropy.sqDistBinary (p true) (q true)
    expectedRisk p rareLoss (bayesBool q rareLoss) - optimal >
      2 * distance + 2 * Real.sqrt (optimal * distance) := by
  norm_num [expectedRisk, bayesBool, rareLoss, Entropy.sqDistBinary_eq_two_mul]

/-- A constant observation cannot retain risks that distinguish the two outcomes. -/
theorem constant_view_loses_zeroOne_risk :
    ¬ ∃ target : BoundedLoss Bool Unit, ∀ weights : Bool → ℝ, ∀ action,
      expectedRisk (pushforward weights (fun _ => ())) target action =
        expectedRisk weights zeroOneLoss action := by
  rintro ⟨target, preserved⟩
  have factor := (risk_pushforward_iff (fun _ : Bool => ()) zeroOneLoss target).mp preserved
  have first := factor true true
  have second := factor true false
  norm_num [zeroOneLoss] at first second
  linarith

end Mettapedia.UniversalAI.UniversalPrediction.LossBounds
