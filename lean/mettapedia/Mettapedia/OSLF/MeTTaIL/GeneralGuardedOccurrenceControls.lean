import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

/-!
# Actual guarded occurrence execution beneath nested typed binders

Two declarations with equal source and target patterns and duplicate provider rows remain distinct
origins. Every receipt below comes from the general occurrence frontier;
source checking and site generation follow the actual grammar and the chosen
operational permissions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralGuardedOccurrenceControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralExecutionAdmission GeneralTypedSites

def term : TypeExpr := .base "Term"
def name : TypeExpr := .base "Name"
def zero : Pattern := .apply "Zero" []

def guarded : RewriteRule where
  name := "consume-guarded"
  typeContext := [("X", term)]
  left := .apply "Guarded" [.fvar "X"]
  right := .apply "Accept" [.fvar "X"]
  premises := [.relationQuery "gate" [.fvar "X"]]

def language : LanguageDef where
  name := "guarded-nested-occurrences"
  types := ["Term", "Name"]
  terms := [
    {label := "Zero", category := "Term", params := [], syntaxPattern := []},
    {label := "Guarded", category := "Term", params := [.simple "x" term], syntaxPattern := []},
    {label := "Accept", category := "Term", params := [.simple "x" term], syntaxPattern := []},
    {label := "Binder", category := "Term", params := [.abstraction "body" (.arrow name term)], syntaxPattern := []}]
  equations := []
  rewrites := [guarded, {guarded with name := "consume-guarded-again"}]

def snapshot (rows : List Pattern) : Snapshot where
  language := language
  freeTypes := []
  provider := ⟨[⟨"gate", [term], [.input]⟩], rows.map fun value => ⟨"gate", [value]⟩⟩

def permissions (sites : OperationalPermissions) : Permissions where
  sites := sites
  equationIndices := some []
  includeDerivedEquations := false

def plan (rows : List Pattern) (sites : OperationalPermissions := .all) : Plan :=
  compile (snapshot rows) (permissions sites)

def declaration (index : Nat) : RulePlan where
  declarationIndex := index
  authored := if index = 0 then guarded else {guarded with name := "consume-guarded-again"}
  binding := ⟨GeneralRuleBindingInference.inferredSpec guarded, .inferredRootInputs⟩

theorem bindings_compiled :
    GeneralRuleBindingInference.compile? language guarded = some (declaration 0).binding ∧
      GeneralRuleBindingInference.compile? language {guarded with name := "consume-guarded-again"} =
        some (declaration 1).binding := by
  decide +kernel

theorem premises_admitted (rows : List Pattern) :
    GeneralPremise.rulePremisesAdmitted language (snapshot rows).provider guarded
        (declaration 0).binding.spec = true ∧
      GeneralPremise.rulePremisesAdmitted language (snapshot rows).provider
        {guarded with name := "consume-guarded-again"} (declaration 1).binding.spec = true := by
  simp [GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow,
    GeneralPremise.premiseFlow, GeneralPremise.queryInputNames, GeneralPremise.queryOutputNames,
    GeneralPremise.schemaValuesChecked, GeneralPremise.lookupRuleType?,
    GeneralPremise.SchemaTyping.checkSchemaType, GeneralPremise.namesAvailable,
    GeneralPremise.signature?, snapshot, guarded, declaration, term, Pattern.freeFvarNames]

theorem canonical_templates :
    GeneralEquationCanonicalTemplates.checkRule guarded = true ∧
      GeneralEquationCanonicalTemplates.checkRule
        {guarded with name := "consume-guarded-again"} = true ∧
      GeneralEquationCanonicalTemplates.checkBinding (declaration 0).binding.spec = true ∧
      GeneralEquationCanonicalTemplates.checkBinding (declaration 1).binding.spec = true := by
  decide +kernel

theorem compiled_rules (rows : List Pattern) (sites : OperationalPermissions) :
    (plan rows sites).rules = [declaration 0, declaration 1] := by
  have selectedRules : selectedRules (snapshot rows) (permissions sites) =
      [(guarded, 0), ({guarded with name := "consume-guarded-again"}, 1)] := rfl
  unfold plan compile rules
  rw [selectedRules]
  simp only [List.filterMap_cons, List.filterMap_nil, rulePlan?, Option.bind_eq_bind,
    show (snapshot rows).language = language from rfl, bindings_compiled.1,
    bindings_compiled.2, Option.bind_some, (premises_admitted rows).1,
    (premises_admitted rows).2, canonical_templates.1, canonical_templates.2.1,
    canonical_templates.2.2.1, canonical_templates.2.2.2, Bool.and_self, ↓reduceIte]
  rfl

theorem compilation_complete (sites : OperationalPermissions) :
    (plan [zero, zero] sites).complete = true := by
  have validated : language.validate = [] := by
    simp [LanguageDef.validate, LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premisePatterns, LanguageDef.premiseForAllParams,
      language, guarded, Pattern.freeFvarNames]
    all_goals decide +kernel
  have reflected : Reflection.validate language (permissions sites).reflection = [] := rfl
  have providerChecked : GeneralPremise.checkProviderClosed language (snapshot [zero, zero]).free
      (snapshot [zero, zero]).provider = true := by decide +kernel
  have strata : GeneralPremise.checkStepStratification
      (executionLanguage (snapshot [zero, zero]) (permissions sites)) = true := by
    change GeneralPremise.checkStepStratification
      {language with rewrites := (plan [zero, zero] sites).rules.map RulePlan.rule} = true
    rw [compiled_rules]
    rfl
  have ruleChecks : (selectedRules (snapshot [zero, zero]) (permissions sites)).flatMap
      (fun (rule, index) => ruleObligations (snapshot [zero, zero]) index rule) = [] := by
    have selectedRules : selectedRules (snapshot [zero, zero]) (permissions sites) =
        [(guarded, 0), ({guarded with name := "consume-guarded-again"}, 1)] := rfl
    rw [selectedRules]
    simp only [List.flatMap_cons, List.flatMap_nil, ruleObligations,
      show (snapshot [zero, zero]).language = language from rfl,
      bindings_compiled.1, bindings_compiled.2, (premises_admitted [zero, zero]).1,
      (premises_admitted [zero, zero]).2, canonical_templates.1, canonical_templates.2.1,
      canonical_templates.2.2.1, canonical_templates.2.2.2, Bool.and_self, ↓reduceIte,
      List.nil_append]
  apply List.isEmpty_iff.mpr
  change (compile (snapshot [zero, zero]) (permissions sites)).obligations = []
  dsimp only [compile]
  rw [show (snapshot [zero, zero]).language.validate = [] from validated,
    show checkFreeContext (snapshot [zero, zero]) = true from rfl,
    show GeneralPremise.checkProviderClosed (snapshot [zero, zero]).language
      (snapshot [zero, zero]).free (snapshot [zero, zero]).provider = true from providerChecked,
    show Reflection.validate (snapshot [zero, zero]).language (permissions sites).reflection = [] from reflected,
    ruleChecks, strata]
  rfl

def runtimePlan (sites : OperationalPermissions) : Plan where
  snapshot := snapshot [zero, zero]
  permissions := permissions sites
  rules := [declaration 0, declaration 1]
  equations := []
  obligations := []

theorem runtime_plan_actual (sites : OperationalPermissions) :
    plan [zero, zero] sites = runtimePlan sites := by
  have rules := compiled_rules [zero, zero] sites
  have obligations := List.isEmpty_iff.mp (compilation_complete sites)
  unfold plan compile at rules obligations ⊢
  simp only at rules obligations
  rw [rules, obligations]
  rfl

def bind (body : Pattern) : Pattern := .apply "Binder" [.lambda none body]
def source : Pattern := bind (bind (.apply "Guarded" [zero]))
def target : Pattern := bind (bind (.apply "Accept" [zero]))

def request (rows : List Pattern) (sites : OperationalPermissions := .all) : GeneralOccurrenceFrontier.Request :=
  ⟨plan rows sites, [], term, source⟩

def paused (fuel : Nat) (rows : List Pattern) (sites : OperationalPermissions := .all) :=
  GeneralOccurrenceFrontier.run (request rows sites) fuel (GeneralOccurrenceFrontier.start (request rows sites))

def queryRows (events : List GeneralPremise.Event) : List Nat :=
  events.filterMap fun event => match event with
    | .query _ _ row _ => some row
    | _ => none

def readout (rows : List Pattern) (sites : OperationalPermissions := .all)
    (answer : GeneralOccurrenceFrontier.Answer (request rows sites)) :
    Nat × List Nat × List TypeExpr × List Nat × Pattern :=
  (answer.val.firing.job.declaration.declarationIndex, answer.val.firing.job.site.address,
    answer.val.firing.job.site.focusBound, queryRows answer.val.firing.premiseHistory, answer.val.target)

def rawReadout (receipt : GeneralOccurrenceSemantics.Receipt) :
    Nat × List Nat × List TypeExpr × List Nat × Pattern :=
  (receipt.firing.job.declaration.declarationIndex, receipt.firing.job.site.address,
    receipt.firing.job.site.focusBound, queryRows receipt.firing.premiseHistory, receipt.target)

def readouts (query : GeneralOccurrenceFrontier.Request) (fuel : Nat) :=
  ((GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)).answers.map Subtype.val).map rawReadout

theorem source_erasure : source.eraseBinderMetadata = source := by
  simp [source, bind, zero, Pattern.eraseBinderMetadata]

theorem actual_start (sites : OperationalPermissions) :
    GeneralOccurrenceFrontier.start ⟨runtimePlan sites, [], term, source⟩ =
      { agenda := [.visit ⟨source, [], by
            rw [show (GeneralOccurrenceFrontier.Request.mk (runtimePlan sites) [] term source).root = source
              from source_erasure]
            exact .nil source⟩, .universe] } := by
  simp only [GeneralOccurrenceFrontier.start, GeneralOccurrenceFrontier.Request.root, source_erasure]
  rfl

theorem admitted_compilation : (plan [zero, zero]).complete = true := compilation_complete .all

theorem all_real_typed_sites :
    (generate language (snapshot [zero, zero]).free .all [] term source).map
      (fun site => (site.address, site.focusBound)) =
      [([], []), ([0], []), ([0, 0], [name]), ([0, 0, 0], [name]),
        ([0, 0, 0, 0], [name, name]), ([0, 0, 0, 0, 0], [name, name])] := by decide +kernel

theorem actual_nested_duplicate_receipts :
    (paused 115 [zero, zero]).answers.map (readout [zero, zero]) =
      [(0, [0, 0, 0, 0], [name, name], [0], target),
        (0, [0, 0, 0, 0], [name, name], [1], target),
        (1, [0, 0, 0, 0], [name, name], [0], target),
        (1, [0, 0, 0, 0], [name, name], [1], target)] := by
  have observed : readouts (request [zero, zero]) 115 =
      [(0, [0, 0, 0, 0], [name, name], [0], target),
        (0, [0, 0, 0, 0], [name, name], [1], target),
        (1, [0, 0, 0, 0], [name, name], [0], target),
        (1, [0, 0, 0, 0], [name, name], [1], target)] := by
    unfold request
    rw [runtime_plan_actual]
    unfold readouts
    rw [actual_start]
    decide +kernel
  change (GeneralOccurrenceFrontier.run (request [zero, zero]) 115
    (GeneralOccurrenceFrontier.start (request [zero, zero]))).answers.map
      (fun answer => rawReadout answer.val) = _
  simpa only [readouts, List.map_map, Function.comp_def] using observed

theorem actual_pause_retains_work :
    (paused 25 [zero, zero]).answers = [] ∧
      GeneralOccurrenceFrontier.complete (request [zero, zero]) (paused 25 [zero, zero]) = false := by
  unfold paused request
  rw [runtime_plan_actual]
  rw [actual_start]
  decide +kernel

theorem actual_resume :
    GeneralOccurrenceFrontier.run (request [zero, zero]) 90 (paused 25 [zero, zero]) = paused 115 [zero, zero] :=
  (GeneralOccurrenceFrontier.run_add _ 25 90 _).symm

theorem root_only_changes_actual_sites :
    (GeneralRuleJobs.jobs (plan [zero, zero] .rootOnly) [] term source).map
      (fun job => job.site.address) = [[], []] := by
  rw [runtime_plan_actual]
  decide +kernel

theorem root_only_prefix_has_no_receipts : (paused 5 [zero, zero] .rootOnly).answers = [] := by
  unfold paused request
  rw [runtime_plan_actual]
  rw [actual_start]
  decide +kernel

#print axioms actual_nested_duplicate_receipts
#print axioms actual_resume

end Mettapedia.OSLF.MeTTaIL.GeneralGuardedOccurrenceControls
