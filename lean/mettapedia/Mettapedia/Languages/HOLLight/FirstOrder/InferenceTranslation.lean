import Mettapedia.Languages.MM0.Translation.CalculusSimulation
import Mettapedia.Logic.HOL.Embedding.InferenceRuleInstances

/-!
# Admitted first-order calculi as inference rule packages

The finite schema fragment used by the MM0 translation also supplies the
existing named first-order inference rules. The conversion preserves each
ordered rule row, formal vector and premise list, and reconstructs the
original schemas exactly. Consequently the established checker bridge applies
to every admitted calculus, without another definition of source derivability.

The schemas contain only constructors and depth-zero metavariables. Arguments
are the checker's canonical closed patterns and may themselves contain binders;
they remain opaque substitution values rather than being encoded as schemas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Mettapedia.Logic.HOL.Embedding.InferenceRules

/-- Read a schema's first-order fields in their original order. -/
def inferenceRule (rule : RuleSchema) : FORule where
  id := rule.id.value
  vars := ruleNames rule
  premises := rule.premises
  conclusion := rule.conclusion

/-- The ordered rule family of the original calculus. -/
def inferenceRules (definition : CalculusLanguageDef) : List FORule :=
  definition.rules.map inferenceRule

/-- Zero-depth formals are reconstructed without changing their coordinates. -/
theorem inferenceRule_formals {rule : RuleSchema}
    (arities : ∀ formal ∈ rule.metavariables, formal.2 = 0) :
    (inferenceRule rule).formals = rule.metavariables := by
  simp only [inferenceRule, FORule.formals, ruleNames, List.map_map]
  trans rule.metavariables.map id
  · apply List.map_congr_left
    intro formal member
    exact Prod.ext rfl (arities formal member).symm
  · exact List.map_id _

/-- Reconstruction is exact on the admitted schema fragment, including the
absence of side conditions. -/
theorem inferenceRule_toSchema {rule : RuleSchema}
    (arities : ∀ formal ∈ rule.metavariables, formal.2 = 0)
    (sideConditions : rule.sideConditions = []) :
    (inferenceRule rule).toSchema = rule := by
  have formals := inferenceRule_formals arities
  cases rule with
  | mk id metavariables premises conclusion conditions =>
      cases id
      simp only [inferenceRule, FORule.toSchema] at formals ⊢
      change conditions = [] at sideConditions
      rw [formals, sideConditions]

mutual
  /-- An ordinary named schema satisfies the existing instantiation bridge. -/
  theorem schema_bindingFragment {names : List String} {pattern : Pattern}
      (schema : Schema names pattern) :
      BindingSchemaFragment (names.map fun name => (name, 0)) pattern := by
    cases schema with
    | metavariable member =>
        exact .fvar (List.mem_map.mpr ⟨_, member, rfl⟩)
    | constructor arguments => exact .apply (schemas_bindingFragment arguments)
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  /-- Ordered premise schemas retain their structural admissions. -/
  theorem schemas_bindingFragment {names : List String} {patterns : List Pattern}
      (schemas : Schemas names patterns) :
      BindingSchemasFragment (names.map fun name => (name, 0)) patterns := by
    cases schemas with
    | nil => exact .nil
    | cons head tail =>
        exact .cons (schema_bindingFragment head) (schemas_bindingFragment tail)
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- All rule rows meet the source-binding bridge's admission conditions. -/
theorem inferenceRules_package {definition : CalculusLanguageDef}
    (firstOrder : FirstOrderCalculus definition) :
    FOPackage (inferenceRules definition) where
  nodup := by
    intro rule member
    obtain ⟨schema, schemaMember, rfl⟩ := List.mem_map.mp member
    exact firstOrder.distinctNames schema schemaMember
  premisesFragment := by
    intro rule member
    obtain ⟨schema, schemaMember, rfl⟩ := List.mem_map.mp member
    exact schemas_bindingFragment (firstOrder.premiseSchemas schema schemaMember)
  conclusionFragment := by
    intro rule member
    obtain ⟨schema, schemaMember, rfl⟩ := List.mem_map.mp member
    exact schema_bindingFragment (firstOrder.conclusionSchema schema schemaMember)

/-- The same unchanged source schemas admit the finite schematic HOL theory. -/
theorem inferenceRules_schemaPackage {definition : CalculusLanguageDef}
    (firstOrder : FirstOrderCalculus definition) :
    SchemaPackage (inferenceRules definition) where
  nodup := by
    intro rule member
    obtain ⟨schema, schemaMember, rfl⟩ := List.mem_map.mp member
    exact firstOrder.distinctNames schema schemaMember
  premises := by
    intro rule member
    obtain ⟨schema, schemaMember, rfl⟩ := List.mem_map.mp member
    exact firstOrder.premiseSchemas schema schemaMember
  conclusion := by
    intro rule member
    obtain ⟨schema, schemaMember, rfl⟩ := List.mem_map.mp member
    exact firstOrder.conclusionSchema schema schemaMember

/-- The converted rules reconstruct the original calculus rows exactly. -/
theorem inferenceRules_schemas {definition : CalculusLanguageDef}
    (firstOrder : FirstOrderCalculus definition) :
    (inferenceRules definition).map FORule.toSchema = definition.rules := by
  simp only [inferenceRules, List.map_map]
  trans definition.rules.map id
  · apply List.map_congr_left
    intro rule member
    exact inferenceRule_toSchema (firstOrder.arities rule member)
      (firstOrder.noSideConditions rule member)
  · exact List.map_id _

/-- The original validated calculus presents this rule family, with its own
declarations and lookup cache. No replacement calculus is constructed. -/
theorem presents (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) :
    Presents definition (inferenceRules definition.1) where
  package := inferenceRules_package firstOrder
  rules_eq := (inferenceRules_schemas firstOrder).symm

/-- Each source rule application checks exact arity and every canonical ground
argument before using the original ordered substitution. -/
theorem ruleApplication_iff (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) {rule : RuleSchema}
    (member : rule ∈ definition.1.rules)
    (arguments premises : List Pattern) (conclusion : Pattern) :
    RuleApplication definition ⟨rule.id, arguments⟩ premises conclusion ↔
      arguments.length = (ruleNames rule).length ∧
      (∀ argument ∈ arguments, argumentValidAt 0 argument = true) ∧
      premises = rule.premises.map (applyBindings ((ruleNames rule).zip arguments)) ∧
      conclusion = applyBindings ((ruleNames rule).zip arguments) rule.conclusion := by
  have admitted := presents definition firstOrder
  have convertedMember : inferenceRule rule ∈ inferenceRules definition.1 :=
    List.mem_map.mpr ⟨rule, member, rfl⟩
  exact FirstOrderRules.ruleApplication_iff definition _ admitted.package
    (inferenceRule rule) convertedMember (admitted.lookup convertedMember)
    arguments premises conclusion

/-- A fixed finite rule family's complete premise and conclusion payload. -/
def schemaPayloadFactor (definition : CalculusLanguageDef) : Nat :=
  1 + (definition.rules.map (fun rule =>
    Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight rule.premises +
      Mettapedia.OSLF.MeTTaIL.PatternTokens.weight rule.conclusion)).sum

/-- Successful original instantiation is linear in the complete argument
payload for each fixed finite rule family. Constructor names, ordered
premise occurrences and copied metavariables are all included. -/
theorem instantiateRule_payload (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (instantiated : instantiateRule? definition ruleInstance = some (premises, conclusion)) :
    Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight premises +
        Mettapedia.OSLF.MeTTaIL.PatternTokens.weight conclusion ≤
      schemaPayloadFactor definition.1 *
        (Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight ruleInstance.arguments + 1) := by
  have application := instantiateRule?_eq_some_iff_application.mp instantiated
  cases application with
  | intro rule found valid sideConditions instantiated concluded =>
      have member : rule ∈ definition.1.rules := List.mem_of_find?_eq_some found
      have idSame : rule.id = ruleInstance.ruleId := by
        simpa [CalculusLanguageDef.lookupRule?] using List.find?_some found
      have applied : RuleApplication definition ⟨rule.id, ruleInstance.arguments⟩ premises conclusion := by
        simpa only [idSame] using (RuleApplication.intro rule found valid sideConditions instantiated concluded)
      have shapes := (ruleApplication_iff definition firstOrder member _ _ _).mp applied
      have converted : inferenceRule rule ∈ inferenceRules definition.1 := List.mem_map.mpr ⟨rule, member, rfl⟩
      have package := inferenceRules_package firstOrder
      have p := FORule.instPremises_weight (inferenceRule rule) ruleInstance.arguments
        (package.premisesFragment _ converted)
      have c := FORule.instConclusion_weight (inferenceRule rule) ruleInstance.arguments
        (package.conclusionFragment _ converted)
      have ps : premises = (inferenceRule rule).instPremises ruleInstance.arguments := shapes.2.2.1
      have cs : conclusion = (inferenceRule rule).instConclusion ruleInstance.arguments := shapes.2.2.2
      rw [← ps] at p
      rw [← cs] at c
      have row := List.le_sum_of_mem (List.mem_map.mpr ⟨rule, member, rfl⟩ :
        Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight rule.premises +
          Mettapedia.OSLF.MeTTaIL.PatternTokens.weight rule.conclusion ∈
            definition.1.rules.map (fun candidate =>
              Mettapedia.OSLF.MeTTaIL.PatternTokens.listWeight candidate.premises +
                Mettapedia.OSLF.MeTTaIL.PatternTokens.weight candidate.conclusion))
      simp only [inferenceRule] at p c
      unfold schemaPayloadFactor
      nlinarith

/-- Source derivations and first-order rule derivations coincide. -/
theorem derivation_iff (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern) :
    Nonempty (Derivation definition goal) ↔
      FODerivable (inferenceRules definition.1) goal :=
  derivation_iff_foDerivable (presents definition firstOrder) goal

/-- The supplied generic checker accepts some certificate exactly for the
derivable judgments of the converted source rules. -/
theorem checker_iff (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (goal : Pattern) :
    (∃ proof, checkRaw definition goal proof = true) ↔
      FODerivable (inferenceRules definition.1) goal :=
  checkRaw_exists_iff_foDerivable (presents definition firstOrder) goal

/-- The original generic checker and the finite generated HOL theory derive
exactly the same canonical ground claims. Each source row contributes one
universally quantified rule axiom; reflection covers arbitrary HOL proofs. -/
theorem checker_iff_holProvable (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) {goal : Pattern}
    (valid : argumentValidAt 0 goal = true) :
    (∃ proof, checkRaw definition goal proof = true) ↔
      (theory (inferenceRules definition.1)).Provable (judgment goal) :=
  (checker_iff definition firstOrder goal).trans
    (provable_iff (inferenceRules_schemaPackage firstOrder) valid).symm

namespace Controls

open Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation

/-- A first-order schema can carry arbitrary canonical closed data as its
argument; the binder structure belongs to the data rather than the schema. -/
def dataRule : RuleSchema where
  id := ⟨"data"⟩
  metavariables := [("value", 0)]
  premises := []
  conclusion := judgmentP (.fvar "value")

def dataCalculus : ValidatedCalculusLanguageDef :=
  ⟨modusPonens [dataRule], by decide +kernel⟩

theorem dataCalculus_firstOrder : FirstOrderCalculus dataCalculus.1 :=
  firstOrderCheck_sound (by decide +kernel)

def binderValue : Pattern := .lambda none (.bvar 0)

def dataProof (arguments : List Pattern) : RawProof :=
  .node ⟨dataRule.id, arguments⟩ []

/-- The canonical binder-bearing value is retained exactly by substitution. -/
theorem binder_substitution_exact :
    (inferenceRule dataRule).instConclusion [binderValue] =
      judgmentP binderValue := by decide +kernel

/-- The original generic checker accepts that same, unencoded binder value. -/
theorem binder_accepted :
    checkRaw dataCalculus (judgmentP binderValue) (dataProof [binderValue]) = true := by
  decide +kernel

/-- The adapter transports the actual checker receipt to source derivability. -/
theorem binder_derivable :
    FODerivable (inferenceRules dataCalculus.1) (judgmentP binderValue) :=
  (checker_iff dataCalculus dataCalculus_firstOrder _).mp ⟨_, binder_accepted⟩

/-- The finite HOL theory proves the unchanged binder-bearing source claim. -/
theorem binder_holProvable :
    (theory (inferenceRules dataCalculus.1)).Provable (judgment (judgmentP binderValue)) :=
  preserves (inferenceRules_schemaPackage dataCalculus_firstOrder) binder_derivable

/-- An escaping de Bruijn index is refused at the argument boundary. -/
theorem escaping_binder_refused :
    checkRaw dataCalculus (judgmentP (.lambda none (.bvar 1)))
      (dataProof [.lambda none (.bvar 1)]) = false := by
  decide +kernel

/-- Noncanonical binder names are refused, even when the index is closed. -/
theorem named_binder_refused :
    checkRaw dataCalculus (judgmentP (.lambda (some "x") (.bvar 0)))
      (dataProof [.lambda (some "x") (.bvar 0)]) = false := by
  decide +kernel

/-- Neither missing arguments nor surplus arguments can instantiate the row. -/
theorem arity_refused :
    checkRaw dataCalculus (judgmentP binderValue) (dataProof []) = false ∧
    checkRaw dataCalculus (judgmentP binderValue)
      (dataProof [binderValue, binderValue]) = false := by
  decide +kernel

/-- A well-formed certificate still has to establish the requested judgment. -/
theorem different_goal_refused :
    checkRaw dataCalculus (judgmentP formulaA) (dataProof [binderValue]) = false := by
  decide +kernel

end Controls

end Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation
