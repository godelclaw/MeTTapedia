import Mettapedia.OSLF.NativeTypes.Generation.BindingControls
import Mettapedia.OSLF.NativeTypes.Generation.ConstructorOrigins
import Mettapedia.OSLF.MeTTaIL.StructuralDescentSourceReadout

/-!
# Public scoped execution with queries, repeated captures and selected contexts

The control presentation extends the original lambda source with ordinary
ordered constructors and explicitly scoped declarations. Its provider family
has fixed signatures and arbitrary finite rows. Operational contexts still
come from the authored congruence rules, including queries called below a
binder. Equal answers retain different rule and row origins.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingOperationalControls

open Mettapedia.OSLF.MeTTaIL Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralPremise GeneralExecutionAdmission
open BindingPipeline

private def term : TypeExpr := .base "Term"

def identity : Pattern := .apply "Lam" [.lambda none (.bvar 0)]
def constantIdentity : Pattern := .apply "Lam" [.lambda none identity]

def probe (body : Pattern) : Pattern := .apply "Probe" [body]
def shield (body : Pattern) : Pattern := .apply "Shield" [body]
def closedBinder (body : Pattern) : Pattern := .apply "Seal" [.lambda none body]
def equalPair (left right : Pattern) : Pattern := .apply "EqualPair" [left, right]

def probeRule (name : String) : RewriteRule where
  «name» := name
  typeContext := [("X", term)]
  left := probe (.fvar "X")
  right := .fvar "X"
  premises := [.relationQuery "seen" [.fvar "X"], .relationQuery "confirm" [.fvar "X"]]
  bindings := some {dependencies := [("X", [])], occurrences := []}

def equalRule : RewriteRule where
  «name» := "EqualPairMatch"
  typeContext := [("X", term)]
  left := equalPair (.fvar "X") (.fvar "X")
  right := .fvar "X"
  premises := []
  bindings := some {dependencies := [("X", [])], occurrences := []}

/-- This declaration intentionally admits only a body independent of the
binder. The empty dependency list is an operational capture constraint. -/
def sealRule : RewriteRule where
  «name» := "OpenClosedSeal"
  typeContext := [("X", term)]
  left := closedBinder (.fvar "X")
  right := .fvar "X"
  premises := []
  bindings := some {dependencies := [("X", [])], occurrences := []}

def language : LanguageDef :=
  {BindingPipeline.Controls.originalLambda with
    name := "ScopedOperationalControls"
    terms := BindingPipeline.Controls.originalLambda.terms ++
      [{label := "Probe", category := "Term", params := [.simple "body" term], syntaxPattern := []},
       {label := "Shield", category := "Term", params := [.simple "body" term], syntaxPattern := []},
       {label := "Seal", category := "Term", params := [.abstraction "body" (.arrow term term)], syntaxPattern := []},
       {label := "EqualPair", category := "Term",
         params := [.simple "left" term, .simple "right" term], syntaxPattern := []}]
    rewrites := BindingPipeline.Controls.originalLambda.rewrites ++
      [probeRule "SeenFirst", probeRule "SeenSecond", equalRule, sealRule]}

def provider (rows : List ProviderRow) : ProviderSnapshot where
  signatures := [⟨"seen", [term], [.input]⟩, ⟨"confirm", [term], [.input]⟩]
  rows := rows

def snapshot (rows : List ProviderRow) (freeTypes : List (String × TypeExpr) := []) : Snapshot :=
  ⟨language, freeTypes, provider rows⟩

def chosen : LanguageFragment := BindingPipeline.Controls.fragment

def install (rows : List ProviderRow) (freeTypes : List (String × TypeExpr) := [])
    (fragment : LanguageFragment := chosen) : Except GenerationIssue Installed :=
  BindingPipeline.generate (snapshot rows freeTypes) fragment BindingPipeline.Controls.fullLogic
    (fun _ => .star, fun _ => .star)

def generated (rows : List ProviderRow) (freeTypes : List (String × TypeExpr)) : Generated :=
  Generation.generate (snapshot rows freeTypes) chosen BindingPipeline.Controls.fullLogic.observations
    (fun _ => .star, fun _ => .star)

/-- The comparison environment reads the original authored declarations and
binding annotations directly. It is independent of the execution plan. -/
def originalEnvironment (rows : List ProviderRow) (freeTypes : List (String × TypeExpr)) : Environment where
  language := language
  free := (snapshot rows freeTypes).free
  provider := provider rows
  specifications := language.rewrites.zipIdx.filterMap fun (rule, index) =>
    rule.bindings.map fun spec => (index, spec)

private theorem flow_rows (authored : RewriteRule) (spec : RuleBindingSpec)
    (rows : List ProviderRow) (available : List String) (premise : Premise) :
    premiseFlow language (provider rows) authored spec available premise =
      premiseFlow language (provider []) authored spec available premise := by
  induction premise generalizing available with
  | relationQuery relation arguments => rfl
  | freshness condition => rfl
  | congruence source target => rfl
  | scopedStep step => rfl
  | forAll collection parameter body ih => simp only [premiseFlow, ih]

private theorem flows_rows (authored : RewriteRule) (spec : RuleBindingSpec)
    (rows : List ProviderRow) (available : List String) (premises : List Premise) :
    premisesFlow language (provider rows) authored spec available premises =
      premisesFlow language (provider []) authored spec available premises := by
  induction premises generalizing available with
  | nil => rfl
  | cons premise premises ih => simp only [premisesFlow, flow_rows, ih]

private theorem premise_admission_rows (authored : RewriteRule) (spec : RuleBindingSpec)
    (rows : List ProviderRow) :
    rulePremisesAdmitted language (provider rows) authored spec =
      rulePremisesAdmitted language (provider []) authored spec := by
  simp only [rulePremisesAdmitted, flows_rows]

private theorem rule_plan_rows (rows : List ProviderRow) (freeTypes : List (String × TypeExpr))
    (index : Nat) (authored : RewriteRule) :
    rulePlan? (snapshot rows freeTypes) index authored =
      rulePlan? (snapshot [] []) index authored := by
  simp only [rulePlan?, snapshot, premise_admission_rows]
  rfl

private theorem rule_plans_rows (rows : List ProviderRow) (freeTypes : List (String × TypeExpr)) :
    GeneralExecutionAdmission.rules (snapshot rows freeTypes) chosen.operational =
      GeneralExecutionAdmission.rules (snapshot [] []) chosen.operational := by
  unfold GeneralExecutionAdmission.rules
  rw [show selectedRules (snapshot rows freeTypes) chosen.operational =
    selectedRules (snapshot [] []) chosen.operational from rfl]
  simp only [rule_plan_rows]

private theorem environment_eq {first second : Environment}
    (language : first.language = second.language) (free : first.free = second.free)
    (provider : first.provider = second.provider)
    (specifications : first.specifications = second.specifications)
    (reflection : first.reflection = second.reflection) (dynamic : first.dynamic = second.dynamic) :
    first = second := by
  cases first
  cases second
  cases language
  cases free
  cases provider
  cases specifications
  cases reflection
  cases dynamic
  rfl

/-- Elaboration preserves the complete original scoped environment for all
finite rows and all free-name contexts, including original declaration order. -/
theorem family_environment_original (rows : List ProviderRow) (freeTypes : List (String × TypeExpr)) :
    BindingPipeline.environment (generated rows freeTypes) = originalEnvironment rows freeTypes := by
  change GeneralPlanEnvironment.environment
    (StructuralDescent.Plan.refine (GeneralExecutionAdmission.compile
      (selectedSnapshot (snapshot rows freeTypes) chosen) chosen.operational)) = _
  rw [StructuralDescent.Plan.refinement_environment]
  have selected : selectedSnapshot (snapshot rows freeTypes) chosen = snapshot rows freeTypes := by
    simp only [selectedSnapshot, chosen, BindingPipeline.Controls.fragment,
      unrestricted_signature]
  rw [selected]
  apply environment_eq
  · change {language with rewrites :=
      (GeneralExecutionAdmission.rules (snapshot rows freeTypes) chosen.operational).map RulePlan.rule} = language
    rw [rule_plans_rows]
    have rewrites : (GeneralExecutionAdmission.rules (snapshot [] []) chosen.operational).map
        RulePlan.rule = language.rewrites := by
      simp +decide [GeneralExecutionAdmission.rules, selectedRules, GeneralExecutionAdmission.selected,
        chosen, BindingPipeline.Controls.fragment, snapshot, provider, List.zipIdx,
        rulePlan?, GeneralRuleBindingInference.compile?, GeneralRuleBindingInference.BindingPlan.elaborate,
        GeneralRuleBindingInference.BindingPlan.implicitTypes, RulePlan.rule,
        language, BindingPipeline.Controls.originalLambda,
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language,
        Mettapedia.GSLT.Examples.ScopedLamCongExecution.language,
        Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule,
        Mettapedia.GSLT.Examples.ScopedLamCongExecution.lamCongRule,
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLRule,
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRRule,
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLSpec,
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRSpec,
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLStep,
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRStep,
        probeRule, equalRule, sealRule, probe, equalPair, closedBinder, term,
        GeneralEquationCanonicalTemplates.checkRule, GeneralEquationCanonicalTemplates.checkBinding,
        Pattern.freeFvarNames, GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow,
        GeneralPremise.premiseFlow, GeneralPremise.schemaValuesChecked, GeneralPremise.signature?,
        GeneralPremise.queryInputNames, GeneralPremise.queryOutputNames, GeneralPremise.namesAvailable]
    rw [rewrites]
  · rfl
  · rfl
  · change (GeneralExecutionAdmission.rules (snapshot rows freeTypes) chosen.operational).zipIdx.map
      (fun (rule, index) => (index, rule.binding.spec)) =
        language.rewrites.zipIdx.filterMap (fun (rule, index) => rule.bindings.map (fun spec => (index, spec)))
    rw [rule_plans_rows]
    simp +decide [GeneralExecutionAdmission.rules, selectedRules, GeneralExecutionAdmission.selected,
      chosen, BindingPipeline.Controls.fragment, snapshot, provider, List.zipIdx,
      rulePlan?, GeneralRuleBindingInference.compile?, GeneralRuleBindingInference.BindingPlan.elaborate,
      GeneralRuleBindingInference.BindingPlan.implicitTypes,
      language, BindingPipeline.Controls.originalLambda,
      Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language,
      Mettapedia.GSLT.Examples.ScopedLamCongExecution.language,
      Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule,
      Mettapedia.GSLT.Examples.ScopedLamCongExecution.lamCongRule,
      Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLRule,
      Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRRule,
      Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLSpec,
      Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRSpec,
      Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLStep,
      Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRStep,
      probeRule, equalRule, sealRule, probe, equalPair, closedBinder, term,
      GeneralEquationCanonicalTemplates.checkRule, GeneralEquationCanonicalTemplates.checkBinding,
      Pattern.freeFvarNames, GeneralPremise.rulePremisesAdmitted, GeneralPremise.premisesFlow,
      GeneralPremise.premiseFlow, GeneralPremise.schemaValuesChecked, GeneralPremise.signature?,
      GeneralPremise.queryInputNames, GeneralPremise.queryOutputNames, GeneralPremise.namesAvailable]
  · rfl
  · rfl

theorem family_structural_admission (rows : List ProviderRow) (freeTypes : List (String × TypeExpr)) :
    StructuralDescent.checkEnvironment (BindingPipeline.environment (generated rows freeTypes)) = true := by
  rw [family_environment_original]
  change StructuralDescent.checkEnvironment (originalEnvironment [] []) = true
  simp [StructuralDescent.checkEnvironment, originalEnvironment, List.zipIdx,
    language, BindingPipeline.Controls.originalLambda,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.language,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.lamCongRule,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLRule,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRRule,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLSpec,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRSpec,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongLStep,
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.appCongRStep,
    probeRule, equalRule, sealRule, probe, equalPair, closedBinder,
    specification?, StructuralDescent.checkRule, StructuralDescent.checkPremises,
    StructuralDescent.checkPremise, StructuralDescent.checkSource,
    StructuralDescent.checkDescent, StructuralDescent.fvarCount, StructuralDescent.fvarCountList, GeneralEquationAdmission.restCount, GeneralEquationAdmission.restCountList,
    GeneralEquationMeasures.constantContribution,
    GeneralEquationMeasures.evaluate, GeneralEquationMeasures.evaluateList,
    Pattern.freeFvarNames, GeneralEquationAdmission.checkSide,
    GeneralEquationAdmission.checkArguments]
  decide +kernel

/-- Every occurrence field, not merely the target, is equivalent to the
independent scoped authored firing relation throughout this provider family. -/
theorem family_occurrences (rows : List ProviderRow) (freeTypes : List (String × TypeExpr))
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List Event) (target : Pattern) :
    (∃ answer ∈ StructuralDescent.Scheduled.receipts (StructuralDescent.Scheduled.finishSource
        (BindingPipeline.environment (generated rows freeTypes)) bound type source),
      answer.index = index ∧ answer.trace = trace ∧ answer.captured = captured ∧
      answer.completed = completed ∧ answer.history = history ∧ answer.target = target) ↔
    RootFiring (originalEnvironment rows freeTypes) bound type source
      index trace captured completed history target := by
  rw [StructuralDescent.Scheduled.finishSource_occurrences _ (family_structural_admission rows freeTypes),
    family_environment_original]

/-- Successful public installation keeps the exact authored/provider snapshot,
so its execution readout has the same independently specified semantics. -/
theorem installed_environment_original (rows : List ProviderRow)
    (freeTypes : List (String × TypeExpr)) (installed : Installed)
    (accepted : install rows freeTypes = .ok installed) :
    installed.Environment = originalEnvironment rows freeTypes := by
  have same : installed.generated = generated rows freeTypes :=
    (installGenerated_retains language (generated rows freeTypes)
      BindingPipeline.Controls.fullLogic.native installed accepted).2.1
  change BindingPipeline.environment installed.generated = _
  rw [same, family_environment_original]

theorem installed_occurrences (rows : List ProviderRow) (freeTypes : List (String × TypeExpr))
    (installed : Installed) (accepted : install rows freeTypes = .ok installed)
    (source : Installed.Source) (index : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List Event) (target : Pattern) :
    (∃ answer ∈ installed.receipts (installed.finish source),
      answer.index = index ∧ answer.trace = trace ∧ answer.captured = captured ∧
      answer.completed = completed ∧ answer.history = history ∧ answer.target = target) ↔
    RootFiring (originalEnvironment rows freeTypes) source.bound source.type source.term
      index trace captured completed history target := by
  change (∃ answer ∈ StructuralDescent.Scheduled.receipts (StructuralDescent.Scheduled.finishSource
      installed.Environment source.bound source.type source.term), _) ↔ _
  rw [StructuralDescent.Scheduled.finishSource_occurrences _ installed.structural]
  change RootFiring installed.Environment _ _ _ _ _ _ _ _ _ ↔ _
  rw [installed_environment_original rows freeTypes installed accepted]

/-- Complete public readout of actual retained work. The extra fields let the
controls distinguish duplicated origins from deduplicated endpoints. -/
structure Readout where
  targets : List Pattern
  roots : List Nat
  childOrigins : List (List Nat)
  queryOrigins : List (List (Nat × Nat × Nat))
  complete : Bool
  possibility : Installed.Answer
  outgoingAll : Installed.Answer
  deriving DecidableEq, Repr

mutual
def queryOrigins : Event → List (Nat × Nat × Nat)
  | .query premise quantifier row _ => [(premise, quantifier, row)]
  | .child _ _ _ _ _ _ _ _ _ _ history => queryOriginsList history
  | .quantified _ _ _ entries => queryElementOrigins entries
  | _ => []
termination_by event => sizeOf event

def queryOriginsList : List Event → List (Nat × Nat × Nat)
  | [] => []
  | head :: tail => queryOrigins head ++ queryOriginsList tail
termination_by events => sizeOf events

def queryElementOrigins : List (Nat × Pattern × List Event) → List (Nat × Nat × Nat)
  | [] => []
  | (_, _, history) :: tail => queryOriginsList history ++ queryElementOrigins tail
termination_by entries => sizeOf entries
end

def read (installed : Installed) (source : Installed.Source) (state : installed.ExecutionState source) : Readout :=
  {targets := (installed.receipts state).map (·.target)
   roots := (installed.receipts state).map (·.index)
   childOrigins := (installed.receipts state).map fun receipt =>
     receipt.history.flatMap StructuralDescent.Controls.childIndices
   queryOrigins := (installed.receipts state).map fun receipt => queryOriginsList receipt.history
   complete := Scheduler.complete state
   possibility := installed.possibility source (fun _ => true) state
   outgoingAll := installed.outgoingAll source (fun _ => true) state}

def run (rows : List ProviderRow) (source : Installed.Source) (budget : Nat)
    (freeTypes : List (String × TypeExpr) := []) (fragment : LanguageFragment := chosen) : Option Readout :=
  match install rows freeTypes fragment with
  | .error _ => none
  | .ok installed => some (read installed source (installed.resume source budget (installed.begin source)))

def rows : List ProviderRow :=
  [⟨"seen", [identity]⟩, ⟨"seen", [identity]⟩, ⟨"confirm", [identity]⟩]

def rootProbe : Installed.Source := ⟨[], term, probe identity⟩
def binderProbe : Installed.Source := ⟨[], term, .apply "Lam" [.lambda none (probe identity)]⟩
def failedProbe : Installed.Source := ⟨[], term, probe constantIdentity⟩
def equalSuccess : Installed.Source := ⟨[], term, equalPair identity identity⟩
def equalFailure : Installed.Source := ⟨[], term, equalPair identity constantIdentity⟩
def captureFailure : Installed.Source := ⟨[], term, closedBinder (.bvar 0)⟩
def captureSuccess : Installed.Source := ⟨[], term, closedBinder identity⟩
def shieldedProbe : Installed.Source := ⟨[], term, shield (probe identity)⟩
def freeProbe : Installed.Source := ⟨[], term, .apply "Lam" [.lambda none (probe (.fvar "a"))]⟩

#guard (install rows).isOk

#guard run rows rootProbe 600 == some
  {targets := List.replicate 4 identity, roots := [4, 4, 5, 5], childOrigins := [[], [], [], []],
   queryOrigins := [[(0, 0, 0), (1, 0, 2)], [(0, 0, 1), (1, 0, 2)],
     [(0, 0, 0), (1, 0, 2)], [(0, 0, 1), (1, 0, 2)]],
   complete := true, possibility := .proved, outgoingAll := .proved}

#guard run rows binderProbe 1200 == some
  {targets := List.replicate 4 constantIdentity, roots := [1, 1, 1, 1],
   childOrigins := [[4], [4], [5], [5]],
   queryOrigins := [[(0, 0, 0), (1, 0, 2)], [(0, 0, 1), (1, 0, 2)],
     [(0, 0, 0), (1, 0, 2)], [(0, 0, 1), (1, 0, 2)]],
   complete := true, possibility := .proved, outgoingAll := .proved}

def noSuccessor : Readout :=
  ⟨[], [], [], [], true, .refuted, .proved⟩

#guard run rows failedProbe 600 == some noSuccessor
#guard run rows equalSuccess 600 == some
  {targets := [identity], roots := [6], childOrigins := [[]], queryOrigins := [[]],
   complete := true, possibility := .proved, outgoingAll := .proved}
#guard run rows equalFailure 600 == some noSuccessor
#guard run rows captureFailure 600 == some noSuccessor
#guard run rows captureSuccess 600 == some
  {targets := [identity], roots := [7], childOrigins := [[]], queryOrigins := [[]],
   complete := true, possibility := .proved, outgoingAll := .proved}
#guard run rows shieldedProbe 600 == some noSuccessor

#guard run [⟨"seen", [.fvar "a"]⟩, ⟨"confirm", [.fvar "a"]⟩] freeProbe 1200 [("a", term)] == some
  {targets := [.apply "Lam" [.lambda none (.fvar "a")], .apply "Lam" [.lambda none (.fvar "a")]],
   roots := [1, 1], childOrigins := [[4], [5]],
   queryOrigins := [[(0, 0, 0), (1, 0, 1)], [(0, 0, 0), (1, 0, 1)]],
   complete := true, possibility := .proved, outgoingAll := .proved}

def noBinderCongruence : LanguageFragment :=
  {chosen with operational := {chosen.operational with ruleIndices := some [0, 2, 3, 4, 5, 6, 7]}}

#guard run rows binderProbe 600 [] noBinderCongruence == some noSuccessor
#guard (run rows rootProbe 600 [] noBinderCongruence).map (·.targets) == some (List.replicate 4 identity)

#guard run rows binderProbe 0 == some ⟨[], [], [], [], false, .unknown, .unknown⟩
#guard run rows binderProbe 1 == some ⟨[], [], [], [], false, .unknown, .unknown⟩

def resumed (rows : List ProviderRow) (source : Installed.Source) (first second : Nat) : Option Readout :=
  match install rows with
  | .error _ => none
  | .ok installed =>
      some (read installed source (installed.resume source second
        (installed.resume source first (installed.begin source))))

#guard resumed rows binderProbe 1 1199 == run rows binderProbe 1200
#guard resumed rows binderProbe 523 677 == run rows binderProbe 1200

private def closedSpec : RuleBindingSpec := {dependencies := [("X", [])], occurrences := []}

theorem actual_capture_rejected :
    ScopedRuleMatching.matchRuleAt sealRule closedSpec 0 captureFailure.term = [] := by
  decide +kernel

theorem repeated_capture_conflict_rejected :
    ScopedRuleMatching.matchRuleAt equalRule closedSpec 0 equalFailure.term = [] := by
  decide +kernel

theorem repeated_capture_equal_retained :
    ScopedRuleMatching.matchRuleAt equalRule closedSpec 0 equalSuccess.term =
      [[("X", ⟨[], 0, identity⟩)]] := by
  decide +kernel


/-- A finite table with an ambient bound variable does not pass the closed-row
provider contract, even though the same variable is typed inside a binder. -/
theorem ambient_bound_rows_rejected :
    checkProviderClosed language (fun _ => none) (provider [⟨"seen", [.bvar 0]⟩]) = false := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.Generation.BindingOperationalControls
