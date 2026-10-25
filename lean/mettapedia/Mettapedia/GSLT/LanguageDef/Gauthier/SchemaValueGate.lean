import Mettapedia.GSLT.LanguageDef.Gauthier.SchemaActionEvidence
import Mettapedia.GSLT.Core.PolicyFamilySufficiency
import Mettapedia.InformationTheory.FiniteBrierInformation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ConditionalCreditAdvantage
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.PairedDesignEstimands

/-!
# Work-normalized value gates for schema information

Zero Brier information is exactly posterior-query sufficiency of the context
readout on positive-mass cells. The net-value gate adds the certified PC-over-BP
progress advantage and subtracts priced work; positive work normalization
preserves its sign. The two-by-two schema/rule contrast removes shared static
benefits and identifies any additional PC-specific surplus.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierSchemaValueGate

open Mettapedia.InformationTheory.FiniteBrierInformation
open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ConditionalCreditAdvantage
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
open Mettapedia.GSLT.Core

/-! ## Posterior observations on positive-mass cells -/

section PosteriorReadout
variable {X Z Y : Type*} [Fintype X] [Fintype Z] [Fintype Y]
variable (model : ConditionalLabelModel X Z Y)

/-- Impossible context/signal cells are outside the statistical observation domain. -/
abbrev SupportedCell := {cell : X × Z // 0 < model.contextWeight cell.1 * model.schemaWeight cell.1 cell.2}

/-- Each label requests its actual posterior probability, before any compression. -/
def posteriorFamily : PolicyFamily (SupportedCell model) where
  Policy := Y
  Result := fun _ => ℝ
  decide := fun label cell => model.labelPosterior cell.val.1 cell.val.2 label

/-- The zero-information witness uses the independently defined mixture posterior. -/
noncomputable def zeroInformationRealization (zero : brierInformationValue model = 0) :
    (posteriorFamily model).ReadoutRealization (fun cell => cell.val.1) where
  run := fun label context => model.coarsePosterior context label
  agrees := fun label cell =>
    ((brierInformationValue_eq_zero_iff model).1 zero _ _ label cell.property).symm

theorem contextSupports_iff :
    (posteriorFamily model).SupportsReadout (fun cell => cell.val.1) ↔ brierInformationValue model = 0 := by
  constructor
  · rintro ⟨realization⟩
    let run : Y → X → ℝ := realization.run
    rw [brierInformationValue_eq_zero_iff]
    intro context schema label positive
    have contextPos := pos_of_mul_pos_left positive (model.schemaWeight_nonneg context schema)
    calc
      model.labelPosterior context schema label = run label context :=
        (realization.agrees label ⟨(context, schema), positive⟩).symm
      _ = ∑ signal, model.schemaWeight context signal * run label context := by
        rw [← Finset.sum_mul, model.schemaWeight_sum, one_mul]
      _ = model.coarsePosterior context label := by
        apply Finset.sum_congr rfl
        intro signal _
        by_cases zero : model.schemaWeight context signal = 0
        · simp [zero]
        · exact congrArg (model.schemaWeight context signal * ·)
            (realization.agrees label ⟨(context, signal),
              mul_pos contextPos (lt_of_le_of_ne (model.schemaWeight_nonneg context signal) (Ne.symm zero))⟩)
  · exact fun zero => ⟨zeroInformationRealization model zero⟩

/-- Every sufficient readout recovers the complete posterior vector. -/
theorem posteriorVector_isLeastSufficient :
    (posteriorFamily model).SupportsReadout (posteriorFamily model).vector ∧
      ∀ (Readout : Type*) (readout : SupportedCell model → Readout),
        (posteriorFamily model).SupportsReadout readout →
          NonFactorization.Factors readout (posteriorFamily model).vector :=
  (posteriorFamily model).vector_isLeastSufficient

theorem informative_context_insufficient :
    ¬ (posteriorFamily twoModeModel).SupportsReadout (fun cell => cell.val.1) := by
  rw [contextSupports_iff, twoMode_brierInformationValue_eq_half]
  norm_num

theorem irrelevant_context_sufficient :
    (posteriorFamily irrelevantSchemaModel).SupportsReadout (fun cell => cell.val.1) :=
  (contextSupports_iff _).2 irrelevantSchema_has_zero_brierInformationValue

end PosteriorReadout

/-! ## Exact net-value gate -/

/-- Net schema value in common utility units.  `informationValue` is the
proper-score risk reduction, the two guarantees price learning progress, and
`workPrice * extraWork` charges the additional computation. -/
def netSchemaValue (informationValue pcGuarantee bpGuarantee extraWork workPrice : ℝ) : ℝ :=
  informationValue + (pcGuarantee - bpGuarantee) - workPrice * extraWork

/-- Net schema value per unit of declared matched work. -/
noncomputable def workNormalizedNetSchemaValue (informationValue pcGuarantee bpGuarantee extraWork workPrice
      totalWork : ℝ) : ℝ :=
  netSchemaValue informationValue pcGuarantee bpGuarantee extraWork workPrice /
    totalWork

/-- **Exact work-normalized schema gate.**  For positive declared work, the
schema is admitted exactly when information plus certified PC progress pays
for the priced extra work. -/
theorem workNormalizedNetSchemaValue_pos_iff (informationValue pcGuarantee bpGuarantee extraWork workPrice
      totalWork : ℝ)
    (totalWork_pos : 0 < totalWork) :
    0 < workNormalizedNetSchemaValue informationValue pcGuarantee bpGuarantee
        extraWork workPrice totalWork ↔
      workPrice * extraWork <
        informationValue + (pcGuarantee - bpGuarantee) := by
  rw [workNormalizedNetSchemaValue, div_pos_iff_of_pos_right totalWork_pos,
    netSchemaValue, sub_pos]

/-- Instantiate the gate with the calibrated finite Brier information value. -/
def calibratedSchemaNetValue
    {X Z Y : Type*} [Fintype X] [Fintype Z] [Fintype Y] [DecidableEq Y]
    (model : ConditionalLabelModel X Z Y)
    (pcGuarantee bpGuarantee extraWork workPrice : ℝ) : ℝ :=
  netSchemaValue (brierInformationValue model) pcGuarantee bpGuarantee
    extraWork workPrice

/-- The calibrated gate can be read entirely as observable risk reduction
plus the certified progress contrast. -/
theorem workNormalized_calibrated_gate_iff
    {X Z Y : Type*} [Fintype X] [Fintype Z] [Fintype Y] [DecidableEq Y]
    (model : ConditionalLabelModel X Z Y)
    (pcGuarantee bpGuarantee extraWork workPrice totalWork : ℝ)
    (totalWork_pos : 0 < totalWork) :
    0 < workNormalizedNetSchemaValue (brierInformationValue model)
        pcGuarantee bpGuarantee extraWork workPrice totalWork ↔
      workPrice * extraWork <
        (unresolvedBrierRisk model - resolvedBrierRisk model) +
          (pcGuarantee - bpGuarantee) := by
  rw [workNormalizedNetSchemaValue_pos_iff _ _ _ _ _ _ totalWork_pos,
    unresolved_sub_resolved_eq_brierInformationValue]

/-- Direct bridge to the already-certified work-normalized credit guarantees. -/
noncomputable def calibratedNetValueFromCreditGuarantees
    {X Z Y : Type*} [Fintype X] [Fintype Z] [Fintype Y] [DecidableEq Y]
    (model : ConditionalLabelModel X Z Y)
    (workBudget pcFixed pcSweep pcDepth bpFixed bpSweep bpDepth : ℕ)
    (step pcAlignment pcCurvature bpAlignment bpCurvature
      extraWork workPrice : ℝ) : ℝ :=
  calibratedSchemaNetValue model
    (workNormalizedGuarantee workBudget pcFixed pcSweep pcDepth
      step pcAlignment pcCurvature)
    (workNormalizedGuarantee workBudget bpFixed bpSweep bpDepth
      step bpAlignment bpCurvature)
    extraWork workPrice

/-- If the schema carries no label information, PC has no certified progress
advantage, and extra work has nonnegative price, its net value is nonpositive. -/
theorem netSchemaValue_nonpos_of_closed_channels (pcGuarantee bpGuarantee extraWork workPrice : ℝ)
    (pc_le_bp : pcGuarantee ≤ bpGuarantee)
    (extraWork_nonneg : 0 ≤ extraWork)
    (workPrice_nonneg : 0 ≤ workPrice) :
    netSchemaValue 0 pcGuarantee bpGuarantee extraWork workPrice ≤ 0 := by
  unfold netSchemaValue
  nlinarith [mul_nonneg workPrice_nonneg extraWork_nonneg]

/-- A positive information/progress margin can pay for work. -/
theorem positive_margin_pays_for_work :
    0 < workNormalizedNetSchemaValue 2 3 2 2 1 5 := by
  norm_num [workNormalizedNetSchemaValue, netSchemaValue]

/-- Excess work can erase the same gross advantage. -/
theorem excess_work_rejects_schema :
    workNormalizedNetSchemaValue 2 3 2 4 1 5 < 0 := by
  norm_num [workNormalizedNetSchemaValue, netSchemaValue]

/-! ## Schema-by-rule interaction -/

/-- Difference in schema effects: `(PC,on - PC,off) - (BP,on - BP,off)`. -/
def schemaRuleInteraction (bpOff bpOn pcOff pcOn : ℝ) : ℝ :=
  (pcOn - pcOff) - (bpOn - bpOff)

/-- The real-valued schema/rule interaction agrees with the existing
count-valued paired-design interaction after casting. -/
theorem schemaRuleInteraction_natCast_eq_architectureUpdateInteraction (bpOff bpOn pcOff pcOn : ℕ) :
    schemaRuleInteraction (bpOff : ℝ) (bpOn : ℝ) (pcOff : ℝ) (pcOn : ℝ) =
      (architectureUpdateInteraction bpOff bpOn pcOff pcOn : ℝ) := by
  unfold schemaRuleInteraction architectureUpdateInteraction
  push_cast
  ring

/-- Interaction is zero exactly when the schema contrast is the same under
both learning rules. -/
theorem schemaRuleInteraction_eq_zero_iff (bpOff bpOn pcOff pcOn : ℝ) :
    schemaRuleInteraction bpOff bpOn pcOff pcOn = 0 ↔
      pcOn - pcOff = bpOn - bpOff := sub_eq_zero

/-- Shared static schema evidence is an additive main effect and has zero
schema-by-rule interaction. -/
theorem additive_static_schema_effect_has_zero_interaction (baseline ruleEffect staticSchemaEffect : ℝ) :
    schemaRuleInteraction
      baseline (baseline + staticSchemaEffect)
      (baseline + ruleEffect)
      (baseline + ruleEffect + staticSchemaEffect) = 0 := by
  unfold schemaRuleInteraction
  ring

/-- If PC extracts an additional dynamic benefit from the same schema, the
four-cell interaction identifies exactly that surplus. -/
theorem schemaRuleInteraction_eq_dynamic_surplus
    (baseline ruleEffect staticSchemaEffect dynamicSurplus : ℝ) :
    schemaRuleInteraction
      baseline (baseline + staticSchemaEffect)
      (baseline + ruleEffect)
      (baseline + ruleEffect + staticSchemaEffect + dynamicSurplus) =
        dynamicSurplus := by
  unfold schemaRuleInteraction
  ring

/-- Three cells never identify the schema-by-rule interaction: two possible
values of the missing PC/schema-on cell preserve every observation but give
different contrasts. -/
theorem three_cells_do_not_identify_schemaRuleInteraction (bpOff bpOn pcOff : ℝ) :
    ∃ firstCompletion secondCompletion : ℝ,
      schemaRuleInteraction bpOff bpOn pcOff firstCompletion ≠
        schemaRuleInteraction bpOff bpOn pcOff secondCompletion := by
  refine ⟨0, 1, ?_⟩
  unfold schemaRuleInteraction
  linarith

/-- Concrete positive interaction: static evidence helps both rules by one,
and PC obtains two further units dynamically. -/
theorem schemaRuleInteraction_positive_example :
    schemaRuleInteraction 10 11 10 13 = 2 := by
  norm_num [schemaRuleInteraction]

/-- Concrete no-interaction control. -/
theorem schemaRuleInteraction_zero_example :
    schemaRuleInteraction 10 11 12 13 = 0 := by
  norm_num [schemaRuleInteraction]

end Mettapedia.GSLT.LanguageDef.GauthierSchemaValueGate
