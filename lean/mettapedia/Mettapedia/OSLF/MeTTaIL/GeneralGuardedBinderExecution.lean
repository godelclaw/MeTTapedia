import Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceArchiveCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProjectionTotality

/-!
# Execution contracts for the original guarded binder language

The complete original grammar, both extrusion orientations and both consume
declarations use the general typed occurrence executor. Contextual captures
of the process body retain their Name dependency. The guard capture remains
independent of that local binder and is projected at its actual query site.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderExecution

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open EquationFrontierBinderProfile GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted

def plan (allowed : List Token) : Plan :=
  compile (GeneralGuardedBinderAdmission.snapshot allowed) GeneralGuardedBinderAdmission.permissions

def request (allowed : List Token) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) :
    GeneralOccurrenceFrontier.Request :=
  GeneralOccurrenceFrontier.Request.fromSnapshot (GeneralGuardedBinderAdmission.snapshot allowed)
    GeneralGuardedBinderAdmission.permissions bound expected source

theorem arbitrary_source_admitted {allowed : List Token} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (typed : HasType language FreeTypeContext.empty bound source expected)
    (object : isObjectPattern source = true) (safe : source.isWellScopedAt bound.length = true) :
    GeneralOccurrenceFrontier.Admitted (request allowed bound expected source) :=
  GeneralOccurrenceFrontier.fromSnapshot_admitted (GeneralGuardedBinderAdmission.admission_complete allowed)
    typed object safe

theorem arbitrary_source_settles {allowed : List Token} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (typed : HasType language FreeTypeContext.empty bound source expected)
    (object : isObjectPattern source = true) (safe : source.isWellScopedAt bound.length = true) :
    ∃ fuel, GeneralOccurrenceFrontier.settled (request allowed bound expected source)
      (GeneralOccurrenceFrontier.run (request allowed bound expected source) fuel
        (GeneralOccurrenceFrontier.start (request allowed bound expected source))) = true :=
  GeneralOccurrenceFrontier.finite_saturation _ (arbitrary_source_admitted typed object safe)

def consumeSpec : RuleBindingSpec := consumeRule.bindings.getD {dependencies := []}
def extrusionSpec : RuleBindingSpec := extrusionEquation.bindings.getD {dependencies := []}

def consumePlan (index : Nat) : RulePlan where
  declarationIndex := index
  authored := if index = 0 then consumeRule else {consumeRule with name := "consume-guard-again"}
  binding := ⟨consumeSpec, .authored⟩

def extrusionPlan (direction : ScopedEquationExecution.Orientation) : EquationPlan where
  declarationIndex := 0
  authored := extrusionEquation
  direction := direction
  binding := ⟨if direction = .forward then extrusionSpec else ScopedEquationExecution.exchangeBindings extrusionSpec, .authored⟩
  coverageReady := true

theorem compiled_rules (allowed : List Token) : (plan allowed).rules = [consumePlan 0, consumePlan 1] := by cbv

theorem compiled_equations (allowed : List Token) :
    (plan allowed).equations = [extrusionPlan .forward, extrusionPlan .reverse] := by cbv

def runtimePlan (allowed : List Token) : Plan where
  snapshot := GeneralGuardedBinderAdmission.snapshot allowed
  permissions := GeneralGuardedBinderAdmission.permissions
  rules := [consumePlan 0, consumePlan 1]
  equations := [extrusionPlan .forward, extrusionPlan .reverse]
  obligations := []

theorem runtime_plan_actual (allowed : List Token) : plan allowed = runtimePlan allowed := by
  have rules := compiled_rules allowed
  have equations := compiled_equations allowed
  have obligations := List.isEmpty_iff.mp (GeneralGuardedBinderAdmission.admission_complete allowed)
  unfold plan compile at rules equations ⊢
  simp only at rules equations
  dsimp only [compile] at obligations
  rw [rules, equations, obligations]
  rfl

inductive Choice where
  | consume
  | consumeAgain
  | forward
  | reverse
  deriving Repr, DecidableEq

def Choice.rule : Choice → RewriteRule
  | .consume => consumeRule
  | .consumeAgain => {consumeRule with name := "consume-guard-again"}
  | .forward => ScopedEquationExecution.orientedRule extrusionEquation .forward
  | .reverse => ScopedEquationExecution.orientedRule extrusionEquation .reverse

def Choice.spec (choice : Choice) : RuleBindingSpec := choice.rule.bindings.getD {dependencies := []}

def Choice.context (choice : Choice) (bound : List TypeExpr) : GeneralPremise.Context where
  ruleIndex := match choice with | .consume => 0 | .consumeAgain => 1 | _ => 2
  rule := choice.rule
  spec := choice.spec
  bound := bound
  premiseIndex := 0
  quantifierDepth := 0

def Choice.pPath : Choice → List Nat
  | .consume | .consumeAgain => [0, 0, 0, 0]
  | .forward | .reverse => [0, 0, 0]

def Choice.qPath : Choice → List Nat
  | .consume | .consumeAgain => [0, 0, 0, 1]
  | .forward => [1]
  | .reverse => [0, 0, 1]

def Choice.qDepth : Choice → Nat
  | .forward => 0
  | _ => 1

theorem Choice.dependenciesP (choice : Choice) : dependencies? choice.spec "P" = some [.name] := by
  cases choice <;> decide +kernel

theorem Choice.dependenciesQ (choice : Choice) : dependencies? choice.spec "Q" = some [] := by
  cases choice <;> decide +kernel

theorem Choice.query_arguments (choice : Choice) :
    arguments? choice.rule choice.spec "Q" (.premise 0 0 0) [] = some [] := by
  cases choice <;> decide +kernel

theorem Choice.output_argumentsP (choice : Choice) :
    arguments? choice.rule choice.spec "P" .right choice.pPath = some [.bvar 0] := by
  cases choice <;> decide +kernel

theorem Choice.output_argumentsQ (choice : Choice) :
    arguments? choice.rule choice.spec "Q" .right choice.qPath = some [] := by
  cases choice <;> decide +kernel

theorem Choice.premises (choice : Choice) : choice.rule.premises = [.relationQuery "allow" [.fvar "Q"]] := by
  cases choice <;> rfl

theorem Choice.left_names (choice : Choice) : choice.rule.left.freeFvarNames = ["P", "Q"] := by
  cases choice <;> simp [Choice.rule, consumeRule, extrusionEquation,
    ScopedEquationControls.extrusionEquation, ScopedEquationExecution.orientedRule,
    pair, nu, Pattern.freeFvarNames]

theorem matching_names {choice : Choice} {bound : List TypeExpr} {source : Pattern}
    {assignment : Assignment}
    (matching : GeneralScopedMatch.Matches choice.rule choice.spec bound.length .left [] 0 []
      choice.rule.left source assignment) : GeneralPremise.BoundNames assignment ["P", "Q"] := by
  simpa only [choice.left_names] using GeneralPremise.matching_bound_names matching

def pValue (ambient : Nat) (body : Pattern) : ContextualValue := ⟨[.name], ambient, body⟩
def qValue (ambient : Nat) (body : Pattern) : ContextualValue := ⟨[], ambient, body⟩

private theorem full_spine_identity : occurrenceAssignment 1 1 [.bvar 0] = Pattern.bvar := by
  funext index
  by_cases localIndex : index < 1
  · have zero : index = 0 := by omega
    subst index
    rfl
  · simp only [occurrenceAssignment, localIndex, ↓reduceIte]
    congr 1
    omega

theorem p_projection {ambient : Nat} {body : Pattern}
    (safe : body.isWellScopedAt (1 + ambient) = true) :
    instantiateValue? (pValue ambient body) ambient 1 [.bvar 0] = some body := by
  simp [instantiateValue?, pValue, full_spine_identity, ContextSubstitution.substitute_id,
    safe, Pattern.isWellScopedAt]

def qProjected (depth : Nat) (body : Pattern) : Pattern :=
  ContextSubstitution.substitute (occurrenceAssignment 0 depth []) body

theorem q_projection {ambient : Nat} {body : Pattern}
    (safe : body.isWellScopedAt ambient = true) (depth : Nat) :
    instantiateValue? (qValue ambient body) ambient depth [] = some (qProjected depth body) := by
  have assignmentSafe : ContextSubstitution.WellScopedAssignment ambient (depth + ambient)
      (occurrenceAssignment 0 depth []) := by
    intro index within
    simp only [occurrenceAssignment, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, Pattern.isWellScopedAt]
    exact decide_eq_true (by omega)
  have resultSafe := ContextSubstitution.substitute_wellScoped assignmentSafe safe
  simp [instantiateValue?, qValue, qProjected, safe, resultSafe]

theorem typed_captureP {environment : GeneralPremise.Environment} {choice : Choice}
    {bound : List TypeExpr} {assignment : Assignment} {value : ContextualValue}
    (typed : GeneralPremise.TypedAssignment environment (choice.context bound) assignment)
    (found : lookup assignment "P" = some value) :
    value = pValue bound.length value.body ∧ value.body.isWellScopedAt (1 + bound.length) = true := by
  obtain ⟨dependencies, expected, declared, _, metadata, ambient, sorted⟩ :=
    typed.1 "P" value (ConditionalEquationExecution.lookup_assignment_member _ _ _ found)
  change dependencies? choice.spec "P" = some dependencies at declared
  have deps : dependencies = [.name] := Option.some.inj (declared.symm.trans choice.dependenciesP)
  have scopeProof := sorted.isWellScopedAt
  simp only [deps, List.length_append, List.length_cons, List.length_nil] at scopeProof
  have sameDeps : value.dependencies = [.name] := metadata.trans deps
  have same : value = pValue bound.length value.body := by
    cases value with
    | mk actual caller body =>
        simp only at sameDeps ambient
        subst actual
        subst caller
        rfl
  exact ⟨same, scopeProof⟩

theorem typed_captureQ {environment : GeneralPremise.Environment} {choice : Choice}
    {bound : List TypeExpr} {assignment : Assignment} {value : ContextualValue}
    (typed : GeneralPremise.TypedAssignment environment (choice.context bound) assignment)
    (found : lookup assignment "Q" = some value) :
    value = qValue bound.length value.body ∧ value.body.isWellScopedAt bound.length = true := by
  obtain ⟨dependencies, expected, declared, _, metadata, ambient, sorted⟩ :=
    typed.1 "Q" value (ConditionalEquationExecution.lookup_assignment_member _ _ _ found)
  change dependencies? choice.spec "Q" = some dependencies at declared
  have deps : dependencies = [] := Option.some.inj (declared.symm.trans choice.dependenciesQ)
  have scopeProof := sorted.isWellScopedAt
  simp only [deps, List.nil_append] at scopeProof
  have sameDeps : value.dependencies = [] := metadata.trans deps
  have same : value = qValue bound.length value.body := by
    cases value with
    | mk actual caller body =>
        simp only at sameDeps ambient
        subst actual
        subst caller
        rfl
  exact ⟨same, scopeProof⟩

theorem query_projection_total {environment : GeneralPremise.Environment} {choice : Choice}
    {bound : List TypeExpr} {assignment : Assignment}
    (typed : GeneralPremise.TypedAssignment environment (choice.context bound) assignment)
    (names : GeneralPremise.BoundNames assignment ["P", "Q"]) :
    ∃ target, instantiateAt? choice.rule choice.spec bound.length (.premise 0 0 0) [] 0
      assignment (.fvar "Q") = some target := by
  obtain ⟨value, found⟩ := names "Q" (by simp)
  obtain ⟨same, safe⟩ := typed_captureQ typed found
  have projected := q_projection safe 0
  refine ⟨qProjected 0 value.body, ?_⟩
  simp only [instantiateAt?, instantiateWith?, found, Option.bind_eq_bind, Option.bind_some,
    choice.query_arguments]
  rw [same]
  exact projected

def Choice.schemaRight : Choice → Pattern
  | .consume | .consumeAgain => nu (done (pair (.fvar "P") (.fvar "Q")))
  | .forward => pair (nu (.fvar "P")) (.fvar "Q")
  | .reverse => nu (pair (.fvar "P") (.fvar "Q"))

theorem Choice.right_schema (choice : Choice) : choice.rule.right = choice.schemaRight := by
  cases choice <;> rfl

def Choice.result : Choice → Pattern → Pattern → Pattern
  | .consume, body, guardBody => nu (done (pair body (qProjected 1 guardBody)))
  | .consumeAgain, body, guardBody => nu (done (pair body (qProjected 1 guardBody)))
  | .forward, body, guardBody => pair (nu body) (qProjected 0 guardBody)
  | .reverse, body, guardBody => nu (pair body (qProjected 1 guardBody))

theorem reduct_total {environment : GeneralPremise.Environment} {choice : Choice}
    {bound : List TypeExpr} {assignment : Assignment}
    (typed : GeneralPremise.TypedAssignment environment (choice.context bound) assignment)
    (names : GeneralPremise.BoundNames assignment ["P", "Q"])
    (operation : Pattern → Pattern → Pattern) :
    ∃ target, reductWith? operation choice.rule choice.spec bound.length assignment = some target := by
  obtain ⟨processValue, processFound⟩ := names "P" (by simp)
  obtain ⟨guardValue, guardFound⟩ := names "Q" (by simp)
  obtain ⟨processSame, processScope⟩ := typed_captureP typed processFound
  obtain ⟨guardSame, guardScope⟩ := typed_captureQ typed guardFound
  have processRead : instantiateValue? processValue bound.length 1 [.bvar 0] = some processValue.body := by
    rw [processSame]
    exact p_projection processScope
  have guardRead0 : instantiateValue? guardValue bound.length 0 [] = some (qProjected 0 guardValue.body) := by
    rw [guardSame]
    exact q_projection guardScope 0
  have guardRead1 : instantiateValue? guardValue bound.length 1 [] = some (qProjected 1 guardValue.body) := by
    rw [guardSame]
    exact q_projection guardScope 1
  have processOccurrence := choice.output_argumentsP
  have guardOccurrence := choice.output_argumentsQ
  refine ⟨choice.result processValue.body guardValue.body, ?_⟩
  unfold reductWith?
  rw [choice.right_schema]
  cases choice <;>
    simp only [Choice.pPath, Choice.qPath] at processOccurrence guardOccurrence <;>
    simp only [Choice.schemaRight, Choice.result, pair, nu, done,
      instantiateWith?, instantiateArgsWith?, List.nil_append,
      List.cons_append, Nat.zero_add, processFound, guardFound, processOccurrence, guardOccurrence,
      processRead, guardRead0, guardRead1, Option.bind_eq_bind, Option.bind_some]

#print axioms reduct_total

#print axioms arbitrary_source_settles
#print axioms query_projection_total

end Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderExecution
