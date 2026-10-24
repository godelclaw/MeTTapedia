import Mathlib.Tactic

/-!
# Finite multiclass Brier value of information

For finite contexts `X`, signals `Z`, and labels `Y`, the unresolved forecast
averages the declared posterior `P(Y | X, Z)` over `Z`. Resolving `Z` reduces
calibrated Brier risk by exactly the weighted squared posterior movement.
Every context-only forecast has an additional excess risk: its squared distance
from that mixture. Optimality and zero-information equalities constrain only
positive-mass cells. These laws concern the declared model; uncalibrated advice
can increase risk, and different posteriors on null cells need not carry information.
-/

namespace Mettapedia.InformationTheory.FiniteBrierInformation

open scoped BigOperators

noncomputable section

universe u v w

variable {Y : Type u} [Fintype Y] [DecidableEq Y]

/-- One-hot coordinate of a realized finite outcome. -/
def outcomeCoordinate (outcome coordinate : Y) : ℝ :=
  if coordinate = outcome then 1 else 0

/-- Multiclass Brier loss of a forecast at one realized outcome. -/
def brierLoss (forecast : Y → ℝ) (outcome : Y) : ℝ :=
  ∑ coordinate, (forecast coordinate - outcomeCoordinate outcome coordinate) ^ 2

/-- Expected Brier loss under a declared finite label distribution. -/
def expectedBrier (truth forecast : Y → ℝ) : ℝ :=
  ∑ outcome, truth outcome * brierLoss forecast outcome

/-- Squared Euclidean distance between two finite forecasts. -/
def forecastSquaredDistance (left right : Y → ℝ) : ℝ :=
  ∑ coordinate, (left coordinate - right coordinate) ^ 2

/-- A nonnegative weighted sum vanishes exactly on its positive-weight support. -/
theorem sum_weighted_eq_zero_iff {ι : Type*} [Fintype ι] (weight value : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hv : ∀ i, 0 ≤ value i) :
    (∑ i, weight i * value i) = 0 ↔ ∀ i, 0 < weight i → value i = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hw i) (hv i))]
  simp only [Finset.mem_univ, forall_const, mul_eq_zero]
  apply forall_congr'
  intro i
  by_cases h : weight i = 0
  · simp [h]
  · simp [h, lt_of_le_of_ne (hw i) (Ne.symm h)]

omit [DecidableEq Y] in
theorem forecastSquaredDistance_nonneg (left right : Y → ℝ) :
    0 ≤ forecastSquaredDistance left right := Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq Y] in
@[simp] theorem forecastSquaredDistance_eq_zero_iff (left right : Y → ℝ) :
    forecastSquaredDistance left right = 0 ↔ left = right := by
  rw [forecastSquaredDistance, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, sq_eq_zero_iff, sub_eq_zero, funext_iff]

/-- Expansion of one realized multiclass Brier loss. -/
theorem brierLoss_eq_sum_sq_sub (forecast : Y → ℝ) (outcome : Y) :
    brierLoss forecast outcome =
      (∑ coordinate, (forecast coordinate) ^ 2) -
        2 * forecast outcome + 1 := by
  simp [brierLoss, outcomeCoordinate, sub_sq, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_ite]

/-- Expansion of expected Brier loss for a normalized truth distribution. -/
theorem expectedBrier_eq_sum_sq_sub_inner_add_one (truth forecast : Y → ℝ)
    (truth_sum : ∑ outcome, truth outcome = 1) :
    expectedBrier truth forecast =
      (∑ coordinate, (forecast coordinate) ^ 2) -
        2 * (∑ coordinate, truth coordinate * forecast coordinate) + 1 := by
  simp only [expectedBrier, brierLoss_eq_sum_sq_sub, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    truth_sum, one_mul]
  simp_rw [mul_left_comm _ (2 : ℝ), ← Finset.mul_sum]

omit [DecidableEq Y] in
/-- Expansion of finite squared forecast distance. -/
theorem forecastSquaredDistance_eq (left right : Y → ℝ) :
    forecastSquaredDistance left right =
      (∑ coordinate, (left coordinate) ^ 2) -
        2 * (∑ coordinate, right coordinate * left coordinate) +
        ∑ coordinate, (right coordinate) ^ 2 := by
  simp only [forecastSquaredDistance, sub_sq, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

/-- **Strict propriety of finite multiclass Brier score.**  Excess expected
risk over the calibrated forecast is exactly squared forecast distance. -/
theorem expectedBrier_decomposition (truth forecast : Y → ℝ)
    (truth_sum : ∑ outcome, truth outcome = 1) :
    expectedBrier truth forecast =
      expectedBrier truth truth + forecastSquaredDistance forecast truth := by
  rw [expectedBrier_eq_sum_sq_sub_inner_add_one truth forecast truth_sum,
    expectedBrier_eq_sum_sq_sub_inner_add_one truth truth truth_sum,
    forecastSquaredDistance_eq]
  ring_nf

/-- Brier excess risk is nonnegative. -/
theorem expectedBrier_truth_le (truth forecast : Y → ℝ)
    (truth_sum : ∑ outcome, truth outcome = 1) :
    expectedBrier truth truth ≤ expectedBrier truth forecast := by
  rw [expectedBrier_decomposition truth forecast truth_sum]
  exact le_add_of_nonneg_right (forecastSquaredDistance_nonneg _ _)

/-- Exact equality in the proper-score theorem means coordinatewise equality. -/
theorem expectedBrier_eq_truth_iff (truth forecast : Y → ℝ)
    (truth_sum : ∑ outcome, truth outcome = 1) :
    expectedBrier truth forecast = expectedBrier truth truth ↔ forecast = truth := by
  rw [expectedBrier_decomposition truth forecast truth_sum]
  simp

/-- Expected loss is linear in the truth weights, without normalization premises. -/
theorem expectedBrier_mixture {ι : Type*} [Fintype ι] (weight : ι → ℝ)
    (truth : ι → Y → ℝ) (forecast : Y → ℝ) :
    expectedBrier (fun y => ∑ i, weight i * truth i y) forecast =
      ∑ i, weight i * expectedBrier (truth i) forecast := by
  simp only [expectedBrier, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-! ## A finite conditional-information model -/

/-- Calibrated finite conditional distributions over contexts, schema signals,
and labels. -/
structure ConditionalLabelModel (X : Type v) (Z : Type w) (Y : Type u)
    [Fintype X] [Fintype Z] [Fintype Y] where
  contextWeight : X → ℝ
  schemaWeight : X → Z → ℝ
  labelPosterior : X → Z → Y → ℝ
  contextWeight_nonneg : ∀ context, 0 ≤ contextWeight context
  contextWeight_sum : ∑ context, contextWeight context = 1
  schemaWeight_nonneg : ∀ context schema, 0 ≤ schemaWeight context schema
  schemaWeight_sum : ∀ context, ∑ schema, schemaWeight context schema = 1
  labelPosterior_nonneg : ∀ context schema label, 0 ≤ labelPosterior context schema label
  labelPosterior_sum : ∀ context schema, ∑ label, labelPosterior context schema label = 1

variable {X : Type v} {Z : Type w}
variable [Fintype X] [Fintype Z]

/-- Label posterior before the schema signal is resolved. -/
def ConditionalLabelModel.coarsePosterior
    (model : ConditionalLabelModel X Z Y) (context : X) (label : Y) : ℝ :=
  ∑ schema, model.schemaWeight context schema * model.labelPosterior context schema label

omit [DecidableEq Y] in
/-- The unresolved posterior is normalized. -/
theorem ConditionalLabelModel.coarsePosterior_sum (model : ConditionalLabelModel X Z Y) (context : X) :
    ∑ label, model.coarsePosterior context label = 1 := by
  unfold ConditionalLabelModel.coarsePosterior
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, model.labelPosterior_sum, mul_one]
  exact model.schemaWeight_sum context

/-- Risk of an arbitrary forecast allowed to observe both context and schema. -/
def conditionalBrierRisk (model : ConditionalLabelModel X Z Y)
    (forecast : X → Z → Y → ℝ) : ℝ :=
  ∑ context, model.contextWeight context *
    ∑ schema, model.schemaWeight context schema *
      expectedBrier (model.labelPosterior context schema)
        (forecast context schema)

/-- Risk of the calibrated schema-resolved posterior. -/
def resolvedBrierRisk (model : ConditionalLabelModel X Z Y) : ℝ :=
  conditionalBrierRisk model model.labelPosterior

/-- Risk of using only the context-level mixture, without resolved schema. -/
def unresolvedBrierRisk (model : ConditionalLabelModel X Z Y) : ℝ :=
  conditionalBrierRisk model
    (fun context _schema => model.coarsePosterior context)

/-- Weighted squared posterior movement supplied by resolving the schema. -/
def brierInformationValue (model : ConditionalLabelModel X Z Y) : ℝ :=
  ∑ context, model.contextWeight context *
    ∑ schema, model.schemaWeight context schema *
      forecastSquaredDistance (model.coarsePosterior context)
        (model.labelPosterior context schema)

/-- Risk decomposition for any schema-aware forecast. -/
theorem conditionalBrierRisk_decomposition (model : ConditionalLabelModel X Z Y)
    (forecast : X → Z → Y → ℝ) :
    conditionalBrierRisk model forecast =
      resolvedBrierRisk model +
        ∑ context, model.contextWeight context *
          ∑ schema, model.schemaWeight context schema *
            forecastSquaredDistance (forecast context schema)
              (model.labelPosterior context schema) := by
  simp only [resolvedBrierRisk, conditionalBrierRisk]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro context _
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro schema _
  rw [← mul_add, expectedBrier_decomposition _ _ (model.labelPosterior_sum context schema)]

/-- **Finite multiclass value of schema information.**  The reduction in
Brier risk from resolving the schema is exactly the expected squared movement
of the calibrated posterior. -/
theorem unresolved_sub_resolved_eq_brierInformationValue (model : ConditionalLabelModel X Z Y) :
    unresolvedBrierRisk model - resolvedBrierRisk model =
      brierInformationValue model := by
  rw [sub_eq_iff_eq_add]
  simpa only [unresolvedBrierRisk, brierInformationValue, add_comm] using
    conditionalBrierRisk_decomposition model (fun context _ => model.coarsePosterior context)

omit [DecidableEq Y] in
/-- Calibrated schema information cannot increase Brier risk. -/
theorem brierInformationValue_nonneg (model : ConditionalLabelModel X Z Y) :
    0 ≤ brierInformationValue model := by
  unfold brierInformationValue
  exact Finset.sum_nonneg fun context _ =>
    mul_nonneg (model.contextWeight_nonneg context)
      (Finset.sum_nonneg fun schema _ =>
        mul_nonneg (model.schemaWeight_nonneg context schema)
          (Finset.sum_nonneg fun label _ => sq_nonneg _))

omit [DecidableEq Y] in
/-- Exact zero-information boundary: every posterior coordinate agrees on
every context/schema cell carrying positive joint mass. -/
theorem brierInformationValue_eq_zero_iff (model : ConditionalLabelModel X Z Y) :
    brierInformationValue model = 0 ↔
      ∀ context schema label,
        0 < model.contextWeight context * model.schemaWeight context schema →
        model.labelPosterior context schema label =
          model.coarsePosterior context label := by
  unfold brierInformationValue
  rw [sum_weighted_eq_zero_iff _ _ model.contextWeight_nonneg
    (fun context => Finset.sum_nonneg fun schema _ =>
      mul_nonneg (model.schemaWeight_nonneg context schema) (forecastSquaredDistance_nonneg _ _))]
  simp_rw [sum_weighted_eq_zero_iff _ _ (model.schemaWeight_nonneg _)
    (fun _ => forecastSquaredDistance_nonneg _ _), forecastSquaredDistance_eq_zero_iff, funext_iff]
  constructor
  · intro equal context schema label positive
    exact (equal context (pos_of_mul_pos_left positive (model.schemaWeight_nonneg context schema))
      schema (pos_of_mul_pos_right positive (model.contextWeight_nonneg context)) label).symm
  · intro equal context contextPos schema schemaPos label
    exact (equal context schema label (mul_pos contextPos schemaPos)).symm

omit [DecidableEq Y] in
/-- Any positive-mass posterior-coordinate change gives strictly positive
schema information value. -/
theorem brierInformationValue_pos_of_exists (model : ConditionalLabelModel X Z Y)
    (context : X) (schema : Z) (label : Y)
    (joint_pos : 0 <
      model.contextWeight context * model.schemaWeight context schema)
    (different : model.labelPosterior context schema label ≠
      model.coarsePosterior context label) :
    0 < brierInformationValue model := by
  have nonneg := brierInformationValue_nonneg model
  exact lt_of_le_of_ne nonneg (fun zero =>
    different ((brierInformationValue_eq_zero_iff model).1 zero.symm
      context schema label joint_pos))

/-- Giving a static learner the resolved binding restores risk parity with the
calibrated resolved predictor. -/
theorem resolved_binding_restores_brier_parity (model : ConditionalLabelModel X Z Y) :
    conditionalBrierRisk model model.labelPosterior = resolvedBrierRisk model := rfl

/-! ## Optimal prediction from the retained context -/

/-- A context-only forecast sees the mixture law even when risk is evaluated finely. -/
theorem contextOnlyRisk_eq (model : ConditionalLabelModel X Z Y) (forecast : X → Y → ℝ) :
    conditionalBrierRisk model (fun x _ => forecast x) =
      ∑ x, model.contextWeight x * expectedBrier (model.coarsePosterior x) (forecast x) := by
  exact Finset.sum_congr rfl fun x _ => congrArg (model.contextWeight x * ·)
    (expectedBrier_mixture (model.schemaWeight x) (model.labelPosterior x) (forecast x)).symm

/-- Context-only excess risk is precisely departure from the coarse posterior. -/
theorem contextOnlyRisk_decomposition (model : ConditionalLabelModel X Z Y)
    (forecast : X → Y → ℝ) :
    conditionalBrierRisk model (fun x _ => forecast x) = unresolvedBrierRisk model +
      ∑ x, model.contextWeight x * forecastSquaredDistance (forecast x) (model.coarsePosterior x) := by
  rw [contextOnlyRisk_eq, unresolvedBrierRisk, contextOnlyRisk_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_add, expectedBrier_decomposition _ _ (model.coarsePosterior_sum x)]

/-- Total excess separates omitted information from an inaccurate context-only forecast. -/
theorem contextOnlyRisk_excess (model : ConditionalLabelModel X Z Y) (forecast : X → Y → ℝ) :
    conditionalBrierRisk model (fun x _ => forecast x) - resolvedBrierRisk model =
      brierInformationValue model +
        ∑ x, model.contextWeight x * forecastSquaredDistance (forecast x) (model.coarsePosterior x) := by
  rw [contextOnlyRisk_decomposition, add_sub_right_comm,
    unresolved_sub_resolved_eq_brierInformationValue]

theorem contextOnlyRisk_min (model : ConditionalLabelModel X Z Y) (forecast : X → Y → ℝ) :
    unresolvedBrierRisk model ≤ conditionalBrierRisk model (fun x _ => forecast x) := by
  rw [contextOnlyRisk_decomposition]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun x _ =>
    mul_nonneg (model.contextWeight_nonneg x) (forecastSquaredDistance_nonneg _ _))

/-- Optimal forecasts are unique only on positive-weight contexts. -/
theorem contextOnlyRisk_eq_min_iff (model : ConditionalLabelModel X Z Y) (forecast : X → Y → ℝ) :
    conditionalBrierRisk model (fun x _ => forecast x) = unresolvedBrierRisk model ↔
      ∀ x, 0 < model.contextWeight x → forecast x = model.coarsePosterior x := by
  rw [contextOnlyRisk_decomposition]
  simp only [add_eq_left, sum_weighted_eq_zero_iff _ _ model.contextWeight_nonneg
    (fun _ => forecastSquaredDistance_nonneg _ _), forecastSquaredDistance_eq_zero_iff]

/-! ## Informative, irrelevant, and misleading controls -/

def twoModeModel : ConditionalLabelModel Unit Bool Bool where
  contextWeight _ := 1
  schemaWeight _ _ := 1 / 2
  labelPosterior _ schema label := if label = schema then 1 else 0
  contextWeight_nonneg := by intro; norm_num
  contextWeight_sum := by simp
  schemaWeight_nonneg := by intros; norm_num
  schemaWeight_sum := by intro; norm_num
  labelPosterior_nonneg := by intros; split <;> norm_num
  labelPosterior_sum := by intro context schema; cases schema <;> norm_num

/-- Resolving two equally likely deterministic modes reduces Brier risk by
exactly one half. -/
theorem twoMode_brierInformationValue_eq_half :
    brierInformationValue twoModeModel = 1 / 2 := by
  norm_num [brierInformationValue, forecastSquaredDistance,
    ConditionalLabelModel.coarsePosterior, twoModeModel]

def irrelevantSchemaModel : ConditionalLabelModel Unit Bool Bool where
  contextWeight _ := 1
  schemaWeight _ _ := 1 / 2
  labelPosterior _ _ label := if label then 3 / 4 else 1 / 4
  contextWeight_nonneg := by intro; norm_num
  contextWeight_sum := by simp
  schemaWeight_nonneg := by intros; norm_num
  schemaWeight_sum := by intro; norm_num
  labelPosterior_nonneg := by intros; split <;> norm_num
  labelPosterior_sum := by intros; norm_num

/-- A schema that leaves the calibrated label posterior unchanged has exactly
zero value. -/
theorem irrelevantSchema_has_zero_brierInformationValue :
    brierInformationValue irrelevantSchemaModel = 0 := by
  norm_num [brierInformationValue, forecastSquaredDistance,
    ConditionalLabelModel.coarsePosterior, irrelevantSchemaModel]

def fairTruth : Bool → ℝ
  | false => 1 / 2
  | true => 1 / 2

def misleadingForecast : Bool → ℝ
  | false => 0
  | true => 1

/-- Uncalibrated schema advice can be harmful: on a fair binary outcome, a
confident one-sided forecast doubles Bayes Brier risk from `1/2` to `1`. -/
theorem misleading_uncalibrated_schema_increases_brierRisk :
    expectedBrier fairTruth fairTruth = 1 / 2 ∧
      expectedBrier fairTruth misleadingForecast = 1 ∧
      expectedBrier fairTruth fairTruth <
        expectedBrier fairTruth misleadingForecast := by
  norm_num [expectedBrier, brierLoss, outcomeCoordinate,
    fairTruth, misleadingForecast]

/-- The absent signal may have a different declared posterior without carrying information. -/
def nullSchemaModel : ConditionalLabelModel Unit Bool Bool where
  contextWeight _ := 1
  schemaWeight _ signal := if signal then 0 else 1
  labelPosterior _ signal label := if signal then (if label then 1 else 0) else 1 / 2
  contextWeight_nonneg := by intro; norm_num
  contextWeight_sum := by simp
  schemaWeight_nonneg := by intros; split <;> norm_num
  schemaWeight_sum := by intro; norm_num
  labelPosterior_nonneg := by intro context signal label; cases signal <;> cases label <;> norm_num
  labelPosterior_sum := by intro context signal; cases signal <;> norm_num

theorem nullSchema_information_boundary : brierInformationValue nullSchemaModel = 0 ∧
    nullSchemaModel.labelPosterior () true true ≠ nullSchemaModel.coarsePosterior () true := by
  norm_num [brierInformationValue, forecastSquaredDistance,
    ConditionalLabelModel.coarsePosterior, nullSchemaModel]

/-- Half of the total excess is omitted information, and half is forecast error. -/
theorem biased_context_risk_split :
    conditionalBrierRisk twoModeModel (fun _ _ => misleadingForecast) = 1 ∧
      brierInformationValue twoModeModel = 1 / 2 ∧
      forecastSquaredDistance misleadingForecast (twoModeModel.coarsePosterior ()) = 1 / 2 := by
  norm_num [conditionalBrierRisk, expectedBrier, brierLoss, outcomeCoordinate, brierInformationValue,
    forecastSquaredDistance, ConditionalLabelModel.coarsePosterior, twoModeModel, misleadingForecast]

end

end Mettapedia.InformationTheory.FiniteBrierInformation
