import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef

/-!
# Combining independently interpreted semantic settings

A shared numerical carrier does not identify the meanings of judgments.
Classifying judgment heads makes the setting of each schema explicit. This
module checks schema homogeneity and combines independently proved schema
interpretations. Instantiated rule applications additionally require their
interpretation to commute with substitution; schema soundness alone does not
assert that further result.
-/

namespace Mettapedia.GSLT.LanguageDef.SemanticSettings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceExtension

variable {Setting : Type*} [DecidableEq Setting]

/-- Every premise and the conclusion belong to one declared semantic setting. -/
def homogeneous? (classify : Pattern → Option Setting) (rule : RuleSchema) : Bool :=
  match classify rule.conclusion with
  | none => false
  | some setting => rule.premises.all fun premise => decide (classify premise = some setting)

theorem homogeneous_iff (classify : Pattern → Option Setting) (rule : RuleSchema) :
    homogeneous? classify rule = true ↔
      ∃ setting, classify rule.conclusion = some setting ∧
        ∀ premise ∈ rule.premises, classify premise = some setting := by
  unfold homogeneous?
  cases found : classify rule.conclusion with
  | none => simp
  | some setting => simp [List.all_eq_true]

/-- Models for different settings need not share any carrier. -/
def combinedHolds {Model : Setting → Type*}
    (classify : Pattern → Option Setting)
    (reading : ∀ setting, Model setting → Pattern → Prop)
    (models : ∀ setting, Model setting) (judgment : Pattern) : Prop :=
  match classify judgment with
  | none => False
  | some setting => reading setting (models setting) judgment

omit [DecidableEq Setting] in
theorem combinedHolds_of_setting {Model : Setting → Type*}
    (classify : Pattern → Option Setting)
    (reading : ∀ setting, Model setting → Pattern → Prop)
    (models : ∀ setting, Model setting) {judgment : Pattern} {setting : Setting}
    (declared : classify judgment = some setting) :
    combinedHolds classify reading models judgment ↔ reading setting (models setting) judgment := by
  simp only [combinedHolds, declared]

/-- Local schema semantics, independent of structural admission. -/
def SchemaSound {Model : Type*} (reading : Model → Pattern → Prop) (rule : RuleSchema) : Prop :=
  ∀ model, (∀ premise ∈ rule.premises, reading model premise) → reading model rule.conclusion

/-- A homogeneous schema is sound in the combined model when its independent
interpretation is sound in its declared setting. -/
theorem combine_schema_sound {Model : Setting → Type*}
    (classify : Pattern → Option Setting)
    (reading : ∀ setting, Model setting → Pattern → Prop)
    (rule : RuleSchema) (homogeneous : homogeneous? classify rule = true)
    (localSound : ∀ setting, classify rule.conclusion = some setting →
      SchemaSound (reading setting) rule) :
    SchemaSound (combinedHolds classify reading) rule := by
  intro models premises
  obtain ⟨setting, conclusionSetting, premiseSettings⟩ := (homogeneous_iff classify rule).mp homogeneous
  apply (combinedHolds_of_setting classify reading models conclusionSetting).mpr
  apply localSound setting conclusionSetting (models setting)
  intro premise member
  exact (combinedHolds_of_setting classify reading models (premiseSettings premise member)).mp
    (premises premise member)

end Mettapedia.GSLT.LanguageDef.SemanticSettings
