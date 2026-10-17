import Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderFrontierComparison
import Mathlib.Tactic.FinCases

/-!
# Actual frontier controls for the original guarded binder language

The full original snapshot includes both guarded extrusion orientations and
both consume declarations. These controls read actual equation evidence and
primitive firing origins separately. Every source uses the original grammar
and the general occurrence generator.

The completed-run controls obtain finite fuel from the proved termination and
certificate coverage of the actual scheduler. Their origin families are
specified witnesses; they do not assert the lengths of the complete answer
lists. Equation evidence remains separate from primitive firing origins. The
two-tick control checks an actual suspended matcher before universe scanning.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderFrontierControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open EquationFrontierBinderProfile GeneralGuardedBinderExecution
open RuleBinding ScopedRuleMatching GeneralTypedSites GeneralScopedMatchMachine
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

def source : Pattern := nu (pair (cell 0) (guard .permit))
def exposed : Pattern := pair (nu (cell 0)) (guard .permit)
def target : Pattern := nu (done (pair (cell 0) (guard .permit)))
def nestedSource : Pattern := nu (nu (pair (nu (cell 2)) (guard .permit)))
def nestedTarget : Pattern := nu (nu (nu (done (pair (cell 2) (guard .permit)))))
def multipleSource : Pattern := nu (pair (pair (nu (cell 1)) (guard .permit))
  (pair (nu (cell 0)) (guard .permit)))

def actualRequest (allowed : List Token) (pattern : Pattern) : GeneralOccurrenceFrontier.Request :=
  request allowed [] .proc pattern

def literalRequest (allowed : List Token) (pattern : Pattern) : GeneralOccurrenceFrontier.Request :=
  ⟨runtimePlan allowed, [], .proc, pattern⟩

theorem actual_request (allowed : List Token) (pattern : Pattern) :
    actualRequest allowed pattern = literalRequest allowed pattern := by
  unfold actualRequest request GeneralOccurrenceFrontier.Request.fromSnapshot
  change (⟨plan allowed, [], .proc, pattern⟩ : GeneralOccurrenceFrontier.Request) =
    literalRequest allowed pattern
  rw [runtime_plan_actual]
  rfl

theorem source_erasure : source.eraseBinderMetadata = source := by
  simp [source, nu, pair, cell, EquationFrontierBinderProfile.guard, Token.pattern,
    Pattern.eraseBinderMetadata]

theorem literal_start {allowed : List Token} {pattern : Pattern}
    (erased : pattern.eraseBinderMetadata = pattern)
    (checked : checkOpenPatternWellSorted EquationFrontierBinderProfile.language
      FreeTypeContext.empty [] .proc pattern = true) :
    GeneralOccurrenceFrontier.start (literalRequest allowed pattern) =
      { agenda := [.visit ⟨pattern, [], by
          rw [show (literalRequest allowed pattern).root = pattern from erased]
          exact .nil pattern⟩, .universe] } := by
  simp only [GeneralOccurrenceFrontier.start, GeneralOccurrenceFrontier.Request.root, literalRequest, erased]
  change (if checkOpenPatternWellSorted EquationFrontierBinderProfile.language
    FreeTypeContext.empty [] .proc pattern then _ else _) = _
  rw [checked]
  rfl

def paused (allowed : List Token) (pattern : Pattern) (fuel : Nat) :=
  GeneralOccurrenceFrontier.run (actualRequest allowed pattern) fuel
    (GeneralOccurrenceFrontier.start (actualRequest allowed pattern))

def queryRows (events : List GeneralPremise.Event) : List Nat :=
  events.filterMap fun event => match event with | .query _ _ row _ => some row | _ => none

def conversionRows : GeneralOccurrenceSemantics.Conversion → List Nat
  | .forward receipt | .reverse receipt => queryRows receipt.premiseHistory

def conversionAddress : GeneralOccurrenceSemantics.Conversion → List Nat
  | .forward receipt | .reverse receipt => receipt.job.site.address

structure Readout where
  declarationIndex : Nat
  address : List Nat
  binders : List TypeExpr
  providerRows : List Nat
  conversionRows : List (List Nat)
  conversionAddresses : List (List Nat)
  target : Pattern
  deriving Repr, DecidableEq

def rawReadout (receipt : GeneralOccurrenceSemantics.Receipt) : Readout :=
  ⟨receipt.firing.job.declaration.declarationIndex, receipt.firing.job.site.address,
    receipt.firing.job.site.focusBound, queryRows receipt.firing.premiseHistory,
    receipt.conversions.map conversionRows, receipt.conversions.map conversionAddress, receipt.target⟩

def readouts (query : GeneralOccurrenceFrontier.Request) (fuel : Nat) :=
  ((GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)).answers.map Subtype.val).map rawReadout

def phase {query : GeneralOccurrenceFrontier.Request} : GeneralOccurrenceFrontier.Task query → String
  | .visit _ => "visit"
  | .incoming _ _ => "incoming"
  | .universe => "universe"
  | .scanUniverse _ => "scan-universe"
  | .rule _ => "rule"
  | .equation _ => "equation"

def allowed : List Token := [.permit, .permit]
abbrev executionPlan := plan allowed
abbrev environment := GeneralPlanEnvironment.environment executionPlan

def captures (ambient : Nat) (body : Pattern) : Assignment :=
  [("Q", qValue ambient (EquationFrontierBinderProfile.guard .permit)),
    ("P", pValue ambient body)]

def exampleSource (choice : Choice) (body : Pattern) : Pattern :=
  match choice with
  | .forward => nu (pair body (EquationFrontierBinderProfile.guard .permit))
  | _ => pair (nu body) (EquationFrontierBinderProfile.guard .permit)

def exampleTarget (choice : Choice) (body : Pattern) : Pattern :=
  match choice with
  | .consume | .consumeAgain => nu (done (pair body (EquationFrontierBinderProfile.guard .permit)))
  | .forward => pair (nu body) (EquationFrontierBinderProfile.guard .permit)
  | .reverse => nu (pair body (EquationFrontierBinderProfile.guard .permit))

private theorem recovery_identity (ambient : Nat) :
    recoveryAssignment 1 1 ambient [0] = Pattern.bvar := by
  funext index
  by_cases small : index < 1
  · have zero : index = 0 := by omega
    subst index
    rfl
  · simp only [recoveryAssignment, small, ↓reduceIte]
    congr 1
    omega

private theorem occurrence_identity : occurrenceAssignment 1 1 [.bvar 0] = Pattern.bvar := by
  funext index
  by_cases small : index < 1
  · have zero : index = 0 := by omega
    subst index
    rfl
  · simp only [occurrenceAssignment, small, ↓reduceIte]
    congr 1
    omega

private theorem recover_p {ambient : Nat} {body : Pattern}
    (safe : body.isWellScopedAt (1 + ambient) = true) :
    recoverValue? [.name] ambient 1 [.bvar 0] body = some (pValue ambient body) := by
  simp [recoverValue?, safe, variableSpine?, recovery_identity,
    ContextSubstitution.substitute_id, pValue, instantiateValue?, occurrence_identity,
    Pattern.isWellScopedAt]

private theorem p_capture {choice : Choice} {ambient : Nat} {body : Pattern}
    (safe : body.isWellScopedAt (1 + ambient) = true) :
    capture? choice.rule choice.spec ambient 1 .left [0, 0, 0] [] "P" body =
      some [("P", pValue ambient body)] := by
  have arguments : arguments? choice.rule choice.spec "P" .left [0, 0, 0] = some [.bvar 0] := by
    cases choice <;> decide +kernel
  simp only [capture?, choice.dependenciesP, arguments, Option.bind_eq_bind, Option.bind_some,
    recover_p safe]
  rfl

private theorem recover_guard (ambient depth : Nat) :
    recoverValue? [] ambient depth [] (EquationFrontierBinderProfile.guard .permit) =
      some (qValue ambient (EquationFrontierBinderProfile.guard .permit)) := by
  simp [recoverValue?, instantiateValue?, variableSpine?,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    ContextSubstitution.substitute, ContextSubstitution.substituteList,
    qValue, EquationFrontierBinderProfile.guard, Token.pattern, Token.label]

private theorem q_capture (choice : Choice) (ambient : Nat) (body : Pattern) :
    capture? choice.rule choice.spec ambient (if choice = .forward then 1 else 0) .left
      (if choice = .forward then [0, 0, 1] else [1]) [("P", pValue ambient body)] "Q"
      (EquationFrontierBinderProfile.guard .permit) = some (captures ambient body) := by
  have arguments : arguments? choice.rule choice.spec "Q" .left
      (if choice = .forward then [0, 0, 1] else [1]) = some [] := by
    cases choice <;> decide +kernel
  simp [capture?, choice.dependenciesQ, arguments, recover_guard, captures, assign, lookup]

private theorem example_matching {choice : Choice} {ambient : Nat} {body : Pattern}
    (safe : body.isWellScopedAt (1 + ambient) = true) :
    TracedMatches choice.rule choice.spec ambient .left [] 0 [] choice.rule.left
      (exampleSource choice body) [] (captures ambient body) := by
  cases choice with
  | consume =>
      exact .constructor (.cons (.constructor (.cons (.binder (.capture (p_capture (choice := .consume) safe))) .nil))
        (.cons (.capture (q_capture .consume ambient body)) .nil))
  | consumeAgain =>
      exact .constructor (.cons (.constructor (.cons (.binder (.capture (p_capture (choice := .consumeAgain) safe))) .nil))
        (.cons (.capture (q_capture .consumeAgain ambient body)) .nil))
  | forward =>
      exact .constructor (.cons (.binder (.constructor (.cons (.capture (p_capture (choice := .forward) safe))
        (.cons (.capture (q_capture .forward ambient body)) .nil)))) .nil)
  | reverse =>
      exact .constructor (.cons (.constructor (.cons (.binder (.capture (p_capture (choice := .reverse) safe))) .nil))
        (.cons (.capture (q_capture .reverse ambient body)) .nil))

private theorem guard_open (bound : List TypeExpr) :
    OpenPatternWellSorted environment.language environment.free bound .proc
      (EquationFrontierBinderProfile.guard .permit) := by
  apply (GeneralPlanEnvironment.typing_iff executionPlan _ _ _).mpr
  exact ⟨guard_typed .permit bound, by decide +kernel, by decide +kernel,
    (guard_typed .permit bound).isWellScopedAt⟩

private theorem captures_typed {choice : Choice} {bound : List TypeExpr} {body : Pattern}
    (typed : OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty
      (.name :: bound) .proc body) :
    GeneralPremise.TypedAssignment environment (choice.context bound) (captures bound.length body) := by
  constructor
  · intro name value present
    simp only [captures, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with same | same
    · cases same
      refine ⟨[], .proc, choice.dependenciesQ, ?_, rfl, rfl, (guard_open bound).1⟩
      cases choice <;> rfl
    · cases same
      refine ⟨[.name], .proc, choice.dependenciesP, ?_, rfl, rfl, ?_⟩
      · cases choice <;> rfl
      · exact GeneralLanguageTyping.type_transport (GeneralPlanEnvironment.grammar executionPlan).symm typed.1
  · intro name value present
    simp only [captures, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with same | same
    · cases same
      exact (guard_open bound).2.2.1
    · cases same
      exact typed.2.2.1

private theorem input_projection (choice : Choice) (bound : List TypeExpr) (body : Pattern) :
    instantiateAt? choice.rule choice.spec bound.length (.premise 0 0 0) [] 0
      (captures bound.length body) (.fvar "Q") =
      some (EquationFrontierBinderProfile.guard .permit) := by
  have projected := q_projection (ambient := bound.length) (body := EquationFrontierBinderProfile.guard .permit)
    ((guard_open bound).2.2.2) 0
  simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, choice.query_arguments,
    show lookup (captures bound.length body) "Q" =
      some (qValue bound.length (EquationFrontierBinderProfile.guard .permit)) from rfl,
    Option.bind_some]
  simpa [qProjected, EquationFrontierBinderProfile.guard, Token.pattern, Token.label,
    ContextSubstitution.substitute, ContextSubstitution.substituteList] using projected

private theorem example_premises {choice : Choice} {bound : List TypeExpr} {body : Pattern}
    (typed : OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty
      (.name :: bound) .proc body) (row : Fin 2) :
    GeneralPremise.PremisesHold environment (choice.context bound) choice.rule.premises
      (captures bound.length body) (captures bound.length body)
      [.query 0 0 row.val [(0, [])]] := by
  rw [choice.premises]
  apply GeneralPremise.PremisesHold.cons (.query ?_) .nil
  apply GeneralPremise.TracedQuery.row
    (row := ⟨"allow", [EquationFrontierBinderProfile.guard .permit]⟩)
    (signature := ⟨"allow", [.proc], [.input]⟩)
  · fin_cases row <;> cbv
  · cbv
  · exact ⟨rfl, .cons (guard_open bound) .nil⟩
  · exact .input (input_projection choice bound body) .nil
  · exact captures_typed typed

private theorem example_reduct {choice : Choice} {bound : List TypeExpr} {body : Pattern}
    (safe : body.isWellScopedAt (1 + bound.length) = true) (operation : Pattern → Pattern → Pattern) :
    reductWith? operation choice.rule choice.spec bound.length (captures bound.length body) =
      some (exampleTarget choice body) := by
  have pRead := p_projection safe
  have qRead0 := q_projection (ambient := bound.length) (body := EquationFrontierBinderProfile.guard .permit)
    ((guard_open bound).2.2.2) 0
  have qRead1 := q_projection (ambient := bound.length) (body := EquationFrontierBinderProfile.guard .permit)
    ((guard_open bound).2.2.2) 1
  have pArguments := choice.output_argumentsP
  have qArguments := choice.output_argumentsQ
  unfold reductWith?
  rw [choice.right_schema]
  cases choice <;>
    simp only [Choice.pPath, Choice.qPath] at pArguments qArguments <;>
    simp only [Choice.schemaRight, exampleTarget, pair, nu, done, instantiateWith?, instantiateArgsWith?,
      List.nil_append, List.cons_append, Nat.zero_add, Option.bind_eq_bind,
      show lookup (captures bound.length body) "P" = some (pValue bound.length body) from rfl,
      show lookup (captures bound.length body) "Q" =
        some (qValue bound.length (EquationFrontierBinderProfile.guard .permit)) from rfl,
      pArguments, qArguments, pRead, qRead0, qRead1, Option.bind_some] <;>
    simp [qProjected, EquationFrontierBinderProfile.guard, Token.pattern, Token.label,
      ContextSubstitution.substitute, ContextSubstitution.substituteList]

private theorem example_source_type {choice : Choice} {bound : List TypeExpr} {body : Pattern}
    (typed : HasType EquationFrontierBinderProfile.language FreeTypeContext.empty
      (.name :: bound) body .proc) :
    HasType EquationFrontierBinderProfile.language FreeTypeContext.empty bound
      (exampleSource choice body) .proc := by
  cases choice with
  | consume => exact pair_typed _ _ _ (nu_typed _ _ typed) (guard_typed .permit _)
  | consumeAgain => exact pair_typed _ _ _ (nu_typed _ _ typed) (guard_typed .permit _)
  | forward => exact nu_typed _ _ (pair_typed _ _ _ typed (guard_typed .permit _))
  | reverse => exact pair_typed _ _ _ (nu_typed _ _ typed) (guard_typed .permit _)

private theorem example_target_type {choice : Choice} {bound : List TypeExpr} {body : Pattern}
    (typed : HasType EquationFrontierBinderProfile.language FreeTypeContext.empty
      (.name :: bound) body .proc) :
    HasType EquationFrontierBinderProfile.language FreeTypeContext.empty bound
      (exampleTarget choice body) .proc := by
  cases choice with
  | consume => exact nu_typed _ _ (done_typed _ _ (pair_typed _ _ _ typed (guard_typed .permit _)))
  | consumeAgain => exact nu_typed _ _ (done_typed _ _ (pair_typed _ _ _ typed (guard_typed .permit _)))
  | forward => exact pair_typed _ _ _ (nu_typed _ _ typed) (guard_typed .permit _)
  | reverse => exact nu_typed _ _ (pair_typed _ _ _ typed (guard_typed .permit _))

private theorem example_sources_open {choice : Choice} {bound : List TypeExpr} {body : Pattern}
    (typed : OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty
      (.name :: bound) .proc body) :
    OpenPatternWellSorted environment.language environment.free bound .proc (exampleSource choice body) ∧
      OpenPatternWellSorted environment.language environment.free bound .proc (exampleTarget choice body) := by
  constructor
  · apply (GeneralPlanEnvironment.typing_iff executionPlan _ _ _).mpr
    refine ⟨example_source_type typed.1, ?_, ?_, (example_source_type typed.1).isWellScopedAt⟩
    · cases choice <;> simp only [exampleSource, pair, nu, EquationFrontierBinderProfile.guard,
        Token.pattern, Token.label, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, Option.isNone_none,
        Bool.and_true, typed.2.1]
    · cases choice <;> simp only [exampleSource, pair, nu, EquationFrontierBinderProfile.guard,
        Token.pattern, Token.label, isObjectPattern, isObjectPatternList,
        Bool.and_true, typed.2.2.1]
  · apply (GeneralPlanEnvironment.typing_iff executionPlan _ _ _).mpr
    refine ⟨example_target_type typed.1, ?_, ?_, (example_target_type typed.1).isWellScopedAt⟩
    · cases choice <;> simp only [exampleTarget, pair, nu, done, EquationFrontierBinderProfile.guard,
        Token.pattern, Token.label, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, Option.isNone_none,
        Bool.and_true, typed.2.1]
    · cases choice <;> simp only [exampleTarget, pair, nu, done, EquationFrontierBinderProfile.guard,
        Token.pattern, Token.label, isObjectPattern, isObjectPatternList,
        Bool.and_true, typed.2.2.1]

def consumeChoice (declaration : Fin 2) : Choice :=
  if declaration.val = 0 then .consume else .consumeAgain

def rootReceipt (declaration row : Fin 2) (bound : List TypeExpr) (body : Pattern) :
    GeneralRuleJobs.Receipt where
  job := ⟨declaration.val, consumePlan declaration.val,
    .here bound .proc (exampleSource (consumeChoice declaration) body)⟩
  matcherTrace := []
  captured := captures bound.length body
  completed := captures bound.length body
  premiseHistory := [.query 0 0 row.val [(0, [])]]
  localTarget := exampleTarget (consumeChoice declaration) body
  target := exampleTarget (consumeChoice declaration) body

private theorem root_firing {bound : List TypeExpr} {body : Pattern}
    (typed : OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty
      (.name :: bound) .proc body) (declaration row : Fin 2) :
    GeneralPremise.RootFiring environment bound .proc (exampleSource (consumeChoice declaration) body)
      declaration.val [] (captures bound.length body) (captures bound.length body)
      [.query 0 0 row.val [(0, [])]] (exampleTarget (consumeChoice declaration) body) := by
  have position : executionPlan.rules[declaration.val]? = some (consumePlan declaration.val) := by
    rw [compiled_rules]
    fin_cases declaration <;> rfl
  have ruleSame : (consumePlan declaration.val).rule = (consumeChoice declaration).rule := by
    fin_cases declaration <;> rfl
  have specSame : (consumePlan declaration.val).binding.spec = (consumeChoice declaration).spec := by
    fin_cases declaration <;> rfl
  have selected := GeneralPlanEnvironment.selected_rule executionPlan position
  have specification := GeneralPlanEnvironment.selected_specification executionPlan position
  rw [ruleSame] at selected
  rw [specSame] at specification
  have contextSame : (⟨declaration.val, (consumeChoice declaration).rule,
      (consumeChoice declaration).spec, bound, 0, 0⟩ : GeneralPremise.Context) =
      (consumeChoice declaration).context bound := by fin_cases declaration <;> rfl
  have safe : body.isWellScopedAt (1 + bound.length) = true := by
    simpa only [ScopeSafeAt, List.length_cons, Nat.add_comm] using typed.2.2.2
  refine .fire selected specification ?_ (example_sources_open typed).1 (example_matching safe) ?_ ?_
    (example_reduct safe _) (example_sources_open typed).2
  · fin_cases declaration <;> decide +kernel
  · rw [contextSame]
    exact captures_typed typed
  · rw [contextSame]
    exact example_premises typed row

theorem root_receipt_valid {bound : List TypeExpr} {body : Pattern}
    (typed : OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty
      (.name :: bound) .proc body) (declaration row : Fin 2) :
    (rootReceipt declaration row bound body).Valid executionPlan bound .proc
      (exampleSource (consumeChoice declaration) body) := by
  have sourceTyped := (example_sources_open (choice := consumeChoice declaration) typed).1
  have targetTyped := (example_sources_open (choice := consumeChoice declaration) typed).2
  refine ⟨⟨?_, .here rfl sourceTyped.2.2.1 sourceTyped.1⟩,
    root_firing typed declaration row, rfl, rfl, targetTyped⟩
  change (consumePlan declaration.val, declaration.val) ∈ executionPlan.rules.zipIdx
  rw [compiled_rules]
  fin_cases declaration <;> simp

def extrusionChoice : ScopedEquationExecution.Orientation → Choice
  | .forward => .forward
  | .reverse => .reverse

def extrusionPosition : ScopedEquationExecution.Orientation → Nat
  | .forward => 0
  | .reverse => 1

def equationReceipt (direction : ScopedEquationExecution.Orientation) (row : Fin 2)
    (bound : List TypeExpr) (body : Pattern) : GeneralEquationJobs.Receipt where
  job := ⟨extrusionPosition direction, extrusionPlan direction,
    .here bound .proc (exampleSource (extrusionChoice direction) body)⟩
  matcherTrace := []
  captured := captures bound.length body
  completed := captures bound.length body
  premiseHistory := [.query 0 0 row.val [(0, [])]]
  rawReduct := exampleTarget (extrusionChoice direction) body
  target := exampleTarget (extrusionChoice direction) body

theorem equation_receipt_valid {bound : List TypeExpr} {body : Pattern}
    (typed : OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty
      (.name :: bound) .proc body) (direction : ScopedEquationExecution.Orientation) (row : Fin 2) :
    GeneralEquationJobs.Completion executionPlan bound .proc
      (exampleSource (extrusionChoice direction) body) (equationReceipt direction row bound body) := by
  have sourceTyped := (example_sources_open (choice := extrusionChoice direction) typed).1
  have targetTyped := (example_sources_open (choice := extrusionChoice direction) typed).2
  have ruleSame : (extrusionPlan direction).rule = (extrusionChoice direction).rule := by
    cases direction <;> rfl
  have specSame : (extrusionPlan direction).binding.spec = (extrusionChoice direction).spec := by
    cases direction <;> rfl
  have contextSame : (equationReceipt direction row bound body).job.context executionPlan =
      (extrusionChoice direction).context bound := by
    unfold GeneralEquationJobs.Job.context
    rw [compiled_rules]
    cases direction <;> rfl
  have sourceErasure := Pattern.eraseBinderMetadata_eq_self_of_canonical sourceTyped.2.1
  have targetErasure := Pattern.eraseBinderMetadata_eq_self_of_canonical targetTyped.2.1
  have safe : body.isWellScopedAt (1 + bound.length) = true := by
    simpa only [ScopeSafeAt, List.length_cons, Nat.add_comm] using typed.2.2.2
  refine ⟨⟨?_, .here rfl sourceTyped.2.2.1 sourceTyped.1⟩, sourceTyped, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (extrusionPlan direction, extrusionPosition direction) ∈ executionPlan.equations.zipIdx
    rw [compiled_equations]
    cases direction <;> simp [extrusionPosition]
  · change TracedMatches (extrusionPlan direction).rule (extrusionPlan direction).binding.spec
      bound.length .left [] 0 [] (extrusionPlan direction).rule.left
      (exampleSource (extrusionChoice direction) body).eraseBinderMetadata [] (captures bound.length body)
    rw [ruleSame, specSame, sourceErasure]
    exact example_matching safe
  · rw [contextSame]
    exact captures_typed typed
  · rw [contextSame]
    change GeneralPremise.PremisesHold environment ((extrusionChoice direction).context bound)
      (extrusionPlan direction).rule.premises _ _ _
    rw [ruleSame]
    exact example_premises typed row
  · rw [contextSame]
    exact captures_typed typed
  · change reduct? (extrusionPlan direction).rule (extrusionPlan direction).binding.spec
      bound.length (captures bound.length body) = some (exampleTarget (extrusionChoice direction) body)
    rw [ruleSame, specSame]
    exact example_reduct safe _
  · change GeneralEquationJobs.Acceptable executionPlan bound .proc
      (equationReceipt direction row bound body).job (exampleTarget (extrusionChoice direction) body)
    unfold GeneralEquationJobs.Acceptable
    rw [targetErasure]
    refine ⟨rfl, targetTyped, ?_⟩
    change OpenPatternWellSorted environment.language environment.free bound .proc
      (exampleTarget (extrusionChoice direction) body).eraseBinderMetadata
    rw [targetErasure]
    exact targetTyped
  · change exampleTarget (extrusionChoice direction) body =
      (exampleTarget (extrusionChoice direction) body).eraseBinderMetadata.eraseBinderMetadata
    simp only [targetErasure]

#print axioms root_receipt_valid
#print axioms equation_receipt_valid

def underNu (body : Pattern) (inner : SiteData) : SiteData :=
  (inner.wrapLambda none .name).wrapApplication 6 "Nu" [.lambda none body] 0

private theorem underNu_licensed {bound : List TypeExpr} {body : Pattern} {inner : SiteData}
    (licensed : Licensed environment.language environment.free executionPlan.permissions.sites
      (.name :: bound) .proc body inner) :
    Licensed environment.language environment.free executionPlan.permissions.sites bound .proc
      (nu body) (underNu body inner) := by
  apply Licensed.application (rule := nuRule) (parameter := .abstraction "body" (.arrow .name .proc))
    (parameterType := .arrow .name .proc)
  · change (nuRule, 6) ∈ EquationFrontierBinderProfile.language.terms.zipIdx
    decide +kernel
  · simp [UsesBareCollection, nuRule]
  · exact .cons trivial rfl (.lambda licensed.source_typed) .nil
  · simpa only [isObjectPatternList, isObjectPattern, Bool.and_true] using licensed.source_object
  · rfl
  · rfl
  · rfl
  · exact .inl rfl
  · exact .lambda rfl licensed

def nuReceipt (body : Pattern) (inner : GeneralRuleJobs.Receipt) : GeneralRuleJobs.Receipt :=
  { inner with job := {inner.job with site := underNu body inner.job.site}, target := nu inner.target }

private theorem nu_receipt_valid {bound : List TypeExpr} {body : Pattern} {inner : GeneralRuleJobs.Receipt}
    (valid : inner.Valid executionPlan (.name :: bound) .proc body) :
    (nuReceipt body inner).Valid executionPlan bound .proc (nu body) := by
  have original := (GeneralPlanEnvironment.typing_iff executionPlan _ _ _).mp valid.2.2.2.2
  have targetTyped := nu_typed bound inner.target original.1
  have represented : (nuReceipt body inner).job.site.acceptsReplacementRepresentation
      environment.language inner.localTarget = true := by
    change inner.job.site.acceptsReplacementRepresentation environment.language inner.localTarget = true
    exact valid.2.2.1
  refine ⟨⟨valid.1.1, underNu_licensed valid.1.2⟩, valid.2.1, represented, ?_, ?_⟩
  · change nu inner.target = nu (inner.job.site.context.fill inner.localTarget)
    rw [valid.2.2.2.1]
  · apply (GeneralPlanEnvironment.typing_iff executionPlan _ _ _).mpr
    refine ⟨targetTyped, ?_, ?_, targetTyped.isWellScopedAt⟩
    · change (nu inner.target).hasCanonicalBinderMetadata = true
      simp only [nu, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
        Option.isNone_none, original.2.1, Bool.and_self]
    · change isObjectPattern (nu inner.target) = true
      simp only [nu, isObjectPattern, isObjectPatternList, original.2.2.1, Bool.and_self]

def nestedReceipt (declaration row : Fin 2) : GeneralRuleJobs.Receipt :=
  let root := rootReceipt declaration row [.name, .name] (cell 2)
  nuReceipt (nu root.job.site.focus) (nuReceipt root.job.site.focus root)

private theorem cell_open (ambient : Nat) (index : Fin (ambient + 1)) :
    OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty
      (.name :: ambientContext ambient) .proc (cell index.val) :=
  ⟨cell_typed ambient index, by simp [cell, Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList], by simp [cell, isObjectPattern, isObjectPatternList],
    (cell_typed ambient index).isWellScopedAt⟩

theorem nested_receipt_valid (declaration row : Fin 2) :
    (nestedReceipt declaration row).Valid executionPlan [] .proc nestedSource := by
  have body : OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty
      [.name, .name, .name] .proc (cell 2) := cell_open 2 ⟨2, by decide⟩
  have root := root_receipt_valid body declaration row
  have nested := nu_receipt_valid (nu_receipt_valid root)
  fin_cases declaration <;> exact nested

def underPair (left right : Pattern) (side : Fin 2) (inner : SiteData) : SiteData :=
  inner.wrapApplication 5 "Pair" [left, right] side.val

private theorem underPair_licensed {bound : List TypeExpr} {left right focus : Pattern}
    {side : Fin 2} {inner : SiteData}
    (leftTyped : OpenPatternWellSorted environment.language environment.free bound .proc left)
    (rightTyped : OpenPatternWellSorted environment.language environment.free bound .proc right)
    (selected : [left, right][side.val]? = some focus)
    (licensed : Licensed environment.language environment.free executionPlan.permissions.sites
      bound .proc focus inner) :
    Licensed environment.language environment.free executionPlan.permissions.sites bound .proc
      (pair left right) (underPair left right side inner) := by
  apply Licensed.application (rule := pairRule)
    (parameter := .simple (if side.val = 0 then "left" else "right") .proc)
    (parameterType := .proc)
  · change (pairRule, 5) ∈ EquationFrontierBinderProfile.language.terms.zipIdx
    decide +kernel
  · simp [UsesBareCollection, pairRule]
  · exact .cons trivial rfl leftTyped.1 (.cons trivial rfl rightTyped.1 .nil)
  · simp only [isObjectPatternList, leftTyped.2.2.1, rightTyped.2.2.1, Bool.and_self]
  · exact selected
  · fin_cases side <;> rfl
  · rfl
  · exact .inl rfl
  · exact licensed

def multipleBody (side : Fin 2) : Pattern := cell (if side.val = 0 then 1 else 0)
def multipleLeft : Pattern := exampleSource .consume (cell 1)
def multipleRight : Pattern := exampleSource .consume (cell 0)

def multipleReceipt (declaration row side : Fin 2) : GeneralRuleJobs.Receipt :=
  let root := rootReceipt declaration row [.name] (multipleBody side)
  let atPair := underPair multipleLeft multipleRight side root.job.site
  let site := underNu (pair multipleLeft multipleRight) atPair
  { root with job := {root.job with site := site}, target := site.context.fill root.localTarget }

theorem multiple_receipt_valid (declaration row side : Fin 2) :
    (multipleReceipt declaration row side).Valid executionPlan [] .proc multipleSource := by
  have body : OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty
      [.name, .name] .proc (multipleBody side) := by
    fin_cases side
    · exact cell_open 1 ⟨1, by decide⟩
    · exact cell_open 1 ⟨0, by decide⟩
  have root := root_receipt_valid body declaration row
  have leftOpen : OpenPatternWellSorted environment.language environment.free [.name] .proc multipleLeft :=
    (example_sources_open (choice := .consume) (cell_open 1 ⟨1, by decide⟩)).1
  have rightOpen : OpenPatternWellSorted environment.language environment.free [.name] .proc multipleRight :=
    (example_sources_open (choice := .consume) (cell_open 1 ⟨0, by decide⟩)).1
  have selected : [multipleLeft, multipleRight][side.val]? =
      some (exampleSource (consumeChoice declaration) (multipleBody side)) := by
    fin_cases declaration <;> fin_cases side <;> rfl
  have licensed := underNu_licensed (underPair_licensed leftOpen rightOpen selected root.1.2)
  have represented : (multipleReceipt declaration row side).job.site.acceptsReplacementRepresentation
      environment.language (multipleReceipt declaration row side).localTarget = true := by
    fin_cases side <;> rfl
  have targetTyped := licensed.replace_checked (multipleReceipt declaration row side).localTarget represented
    root.2.2.2.2.1
  refine ⟨⟨root.1.1, licensed⟩, root.2.1, represented, rfl, targetTyped, ?_, ?_, targetTyped.isWellScopedAt⟩
  · fin_cases declaration <;> fin_cases side <;> fin_cases row <;> decide +kernel
  · fin_cases declaration <;> fin_cases side <;> fin_cases row <;> decide +kernel

#print axioms nested_receipt_valid
#print axioms multiple_receipt_valid

structure PhysicalReadout where
  declarationIndex : Nat
  address : List Nat
  binders : List TypeExpr
  matcherTrace : List BagChoice
  providerRows : List Nat
  target : Pattern
  deriving Repr, DecidableEq

def firingReadout (receipt : GeneralRuleJobs.Receipt) : PhysicalReadout :=
  ⟨receipt.job.declaration.declarationIndex, receipt.job.site.address, receipt.job.site.focusBound,
    receipt.matcherTrace, queryRows receipt.premiseHistory, receipt.target⟩

def physicalReadouts (query : GeneralOccurrenceFrontier.Request)
    (state : GeneralOccurrenceFrontier.State query) : List (Pattern × PhysicalReadout) :=
  state.answers.map fun answer => (answer.val.representative, firingReadout answer.val.firing)

structure EquationReadout where
  direction : ScopedEquationExecution.Orientation
  address : List Nat
  binders : List TypeExpr
  providerRows : List Nat
  target : Pattern
  deriving Repr, DecidableEq

def equationReadout (receipt : GeneralEquationJobs.Receipt) : EquationReadout :=
  ⟨receipt.job.equation.direction, receipt.job.site.address, receipt.job.site.focusBound,
    queryRows receipt.premiseHistory, receipt.target⟩

def equationReadouts (query : GeneralOccurrenceFrontier.Request)
    (state : GeneralOccurrenceFrontier.State query) : List (Pattern × EquationReadout) :=
  state.edges.map fun edge => (edge.source, equationReadout edge.receipt)

/-- One actual finite run covers every independent occurrence simultaneously. -/
private theorem actual_run_covers {pattern : Pattern}
    (typed : OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty
      [] .proc pattern) :
    ∃ fuel,
      GeneralOccurrenceFrontier.complete (actualRequest allowed pattern) (paused allowed pattern fuel) = true ∧
      GeneralOccurrenceFrontier.checkCertificate (actualRequest allowed pattern) (paused allowed pattern fuel) = true ∧
      (∀ representative,
        Relation.EqvGen (GeneralOccurrenceSemantics.Equation executionPlan [] .proc)
          pattern.eraseBinderMetadata representative →
        ∀ receipt : GeneralRuleJobs.Receipt, receipt.Valid executionPlan [] .proc representative →
          ∃ answer ∈ (paused allowed pattern fuel).answers,
            answer.val.representative = representative ∧ answer.val.firing = receipt) ∧
      (∀ source ∈ (actualRequest allowed pattern).universe,
        ∀ receipt : GeneralEquationJobs.Receipt,
          GeneralEquationJobs.Completion executionPlan [] .proc source receipt →
          ∃ edge ∈ (paused allowed pattern fuel).edges, edge.source = source ∧ edge.receipt = receipt) := by
  let admitted := GeneralGuardedBinderFrontierComparison.actual_source_admitted (allowed := allowed)
    typed.1 typed.2.2.1
  obtain ⟨fuel, actual⟩ := GeneralOccurrenceFrontier.finish_actual_run (actualRequest allowed pattern) admitted
  have certificate := GeneralGuardedBinderFrontierComparison.whole_original_frontier_certificate
    (allowed := allowed) typed.1 typed.2.2.1
  refine ⟨fuel, ?_, ?_, ?_, ?_⟩
  · change GeneralOccurrenceFrontier.complete _ (GeneralOccurrenceFrontier.run _ fuel _) = true
    rw [actual]
    exact GeneralGuardedBinderFrontierComparison.whole_original_frontier_complete
      (allowed := allowed) typed.1 typed.2.2.1
  · change GeneralOccurrenceFrontier.checkCertificate _ (GeneralOccurrenceFrontier.run _ fuel _) = true
    rw [actual]
    exact certificate
  · intro representative related receipt valid
    change ∃ answer ∈ (GeneralOccurrenceFrontier.run _ fuel _).answers, _
    rw [actual]
    exact GeneralOccurrenceFrontier.certified_physical_occurrence admitted certificate representative related receipt valid
  · intro source within receipt valid
    change ∃ edge ∈ (GeneralOccurrenceFrontier.run _ fuel _).edges, _
    rw [actual]
    exact GeneralOccurrenceFrontier.certified_equation_occurrence admitted certificate source within receipt valid

private theorem physical_readout_present {query : GeneralOccurrenceFrontier.Request}
    {state : GeneralOccurrenceFrontier.State query} {representative : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (present : ∃ answer ∈ state.answers,
      answer.val.representative = representative ∧ answer.val.firing = receipt) :
    (representative, firingReadout receipt) ∈ physicalReadouts query state := by
  obtain ⟨answer, member, sourceEq, firingEq⟩ := present
  exact List.mem_map.mpr ⟨answer, member, by simp only [sourceEq, firingEq]⟩

private theorem equation_readout_present {query : GeneralOccurrenceFrontier.Request}
    {state : GeneralOccurrenceFrontier.State query} {source : Pattern} {receipt : GeneralEquationJobs.Receipt}
    (present : ∃ edge ∈ state.edges, edge.source = source ∧ edge.receipt = receipt) :
    (source, equationReadout receipt) ∈ equationReadouts query state := by
  obtain ⟨edge, member, sourceEq, receiptEq⟩ := present
  exact List.mem_map.mpr ⟨edge, member, by simp only [sourceEq, receiptEq]⟩

private theorem source_sorted :
    OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty [] .proc source :=
  (GeneralPlanEnvironment.typing_iff executionPlan _ _ _).mp
    (example_sources_open (choice := .forward) (cell_open 0 ⟨0, by decide⟩)).1

private theorem nested_sorted :
    OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty [] .proc nestedSource :=
  checkOpenPatternWellSorted_sound (by decide +kernel)

private theorem multiple_sorted :
    OpenPatternWellSorted EquationFrontierBinderProfile.language FreeTypeContext.empty [] .proc multipleSource :=
  checkOpenPatternWellSorted_sound (by decide +kernel)

private theorem source_exposed_equivalent :
    Relation.EqvGen (GeneralOccurrenceSemantics.Equation executionPlan [] .proc)
      source.eraseBinderMetadata exposed := by
  rw [source_erasure]
  exact .rel source exposed ⟨equationReceipt .forward ⟨0, by decide⟩ [] (cell 0),
    equation_receipt_valid (cell_open 0 ⟨0, by decide⟩) .forward ⟨0, by decide⟩, rfl⟩

/-- The tucked presentation needs actual equation conversion before a root
consume event is available. The four origins distinguish both declarations
and both original provider rows. Conversion proofs are separate evidence. -/
theorem equation_enabled_four_actual_origins :
    ∃ fuel,
      GeneralOccurrenceFrontier.complete (actualRequest allowed source) (paused allowed source fuel) = true ∧
      GeneralOccurrenceFrontier.checkCertificate (actualRequest allowed source) (paused allowed source fuel) = true ∧
      ∀ declaration row : Fin 2,
        (exposed, ⟨declaration.val, [], [], [], [row.val], target⟩) ∈
          physicalReadouts (actualRequest allowed source) (paused allowed source fuel) := by
  obtain ⟨fuel, complete, certificate, physical, _⟩ := actual_run_covers source_sorted
  refine ⟨fuel, complete, certificate, ?_⟩
  intro declaration row
  have present := physical_readout_present (physical exposed source_exposed_equivalent
    (rootReceipt declaration row [] (cell 0))
    (by fin_cases declaration <;> exact root_receipt_valid (cell_open 0 ⟨0, by decide⟩) _ row))
  fin_cases declaration <;> exact present

theorem nested_actual_origins :
    ∃ fuel,
      GeneralOccurrenceFrontier.complete (actualRequest allowed nestedSource) (paused allowed nestedSource fuel) = true ∧
      GeneralOccurrenceFrontier.checkCertificate (actualRequest allowed nestedSource) (paused allowed nestedSource fuel) = true ∧
      ∀ declaration row : Fin 2,
        (nestedSource, ⟨declaration.val, [0, 0, 0, 0], [.name, .name], [], [row.val], nestedTarget⟩) ∈
          physicalReadouts (actualRequest allowed nestedSource) (paused allowed nestedSource fuel) := by
  obtain ⟨fuel, complete, certificate, physical, _⟩ := actual_run_covers nested_sorted
  refine ⟨fuel, complete, certificate, ?_⟩
  intro declaration row
  have related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation executionPlan [] .proc)
      nestedSource.eraseBinderMetadata nestedSource := by
    rw [Pattern.eraseBinderMetadata_eq_self_of_canonical nested_sorted.2.1]
    exact .refl _
  have present := physical_readout_present
    (physical nestedSource related (nestedReceipt declaration row) (nested_receipt_valid declaration row))
  fin_cases declaration <;> exact present

def multipleTarget (side : Fin 2) : Pattern :=
  if side.val = 0 then
    nu (pair (nu (done (pair (cell 1) (EquationFrontierBinderProfile.guard .permit)))) multipleRight)
  else
    nu (pair multipleLeft (nu (done (pair (cell 0) (EquationFrontierBinderProfile.guard .permit)))))

theorem multiple_actual_origins :
    ∃ fuel,
      GeneralOccurrenceFrontier.complete (actualRequest allowed multipleSource) (paused allowed multipleSource fuel) = true ∧
      GeneralOccurrenceFrontier.checkCertificate (actualRequest allowed multipleSource) (paused allowed multipleSource fuel) = true ∧
      ∀ declaration row side : Fin 2,
        (multipleSource, ⟨declaration.val, [0, 0, side.val], [.name], [], [row.val], multipleTarget side⟩) ∈
          physicalReadouts (actualRequest allowed multipleSource) (paused allowed multipleSource fuel) := by
  obtain ⟨fuel, complete, certificate, physical, _⟩ := actual_run_covers multiple_sorted
  refine ⟨fuel, complete, certificate, ?_⟩
  intro declaration row side
  have related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation executionPlan [] .proc)
      multipleSource.eraseBinderMetadata multipleSource := by
    rw [Pattern.eraseBinderMetadata_eq_self_of_canonical multiple_sorted.2.1]
    exact .refl _
  have present := physical_readout_present
    (physical multipleSource related (multipleReceipt declaration row side) (multiple_receipt_valid declaration row side))
  fin_cases declaration <;> fin_cases side <;> exact present

private theorem extrusion_source_within (direction : ScopedEquationExecution.Orientation) :
    exampleSource (extrusionChoice direction) (cell 0) ∈ (actualRequest allowed source).universe := by
  let admitted := GeneralGuardedBinderFrontierComparison.actual_source_admitted (allowed := allowed)
    source_sorted.1 source_sorted.2.2.1
  cases direction with
  | forward =>
      change source ∈ (actualRequest allowed source).universe
      have within := (actualRequest allowed source).root_in_universe source_sorted.1 source_sorted.2.2.1
        (show source.isWellScopedAt 0 = true from source_sorted.2.2.2)
      simpa only [actualRequest, request, GeneralOccurrenceFrontier.Request.fromSnapshot,
        GeneralOccurrenceFrontier.Request.root, source_erasure] using within
  | reverse =>
      let representative : GeneralOccurrenceFrontier.Representative (actualRequest allowed source) :=
        ⟨exposed, [.forward (equationReceipt .forward ⟨0, by decide⟩ [] (cell 0))], by
          change GeneralOccurrenceSemantics.ConversionPath executionPlan [] .proc source.eraseBinderMetadata exposed _
          rw [source_erasure]
          exact .cons (equation_receipt_valid (cell_open 0 ⟨0, by decide⟩) .forward ⟨0, by decide⟩) rfl (.nil exposed)⟩
      exact admitted.representative_within representative

theorem both_extrusion_orientations_and_provider_rows :
    ∃ fuel,
      GeneralOccurrenceFrontier.complete (actualRequest allowed source) (paused allowed source fuel) = true ∧
      GeneralOccurrenceFrontier.checkCertificate (actualRequest allowed source) (paused allowed source fuel) = true ∧
      ∀ direction : ScopedEquationExecution.Orientation, ∀ row : Fin 2,
        (exampleSource (extrusionChoice direction) (cell 0),
          ⟨direction, [], [], [row.val], exampleTarget (extrusionChoice direction) (cell 0)⟩) ∈
          equationReadouts (actualRequest allowed source) (paused allowed source fuel) := by
  obtain ⟨fuel, complete, certificate, _, equations⟩ := actual_run_covers source_sorted
  refine ⟨fuel, complete, certificate, ?_⟩
  intro direction row
  have present := equation_readout_present
    (equations _ (extrusion_source_within direction) (equationReceipt direction row [] (cell 0))
      (equation_receipt_valid (cell_open 0 ⟨0, by decide⟩) direction row))
  exact present

/-- Repeated equation justifications do not change this primitive origin key. -/
theorem duplicate_primitive_origins_distinct {first second firstRow secondRow : Fin 2}
    (same : firingReadout (rootReceipt first firstRow [] (cell 0)) =
      firingReadout (rootReceipt second secondRow [] (cell 0))) :
    first = second ∧ firstRow = secondRow := by
  constructor
  · apply Fin.ext
    exact congrArg PhysicalReadout.declarationIndex same
  · apply Fin.ext
    have rows := congrArg PhysicalReadout.providerRows same
    change [firstRow.val] = [secondRow.val] at rows
    exact (List.cons.inj rows).1

theorem multiple_sites_distinct {declaration row first second : Fin 2}
    (same : firingReadout (multipleReceipt declaration row first) =
      firingReadout (multipleReceipt declaration row second)) : first = second := by
  apply Fin.ext
  have addresses := congrArg PhysicalReadout.address same
  change [0, 0, first.val] = [0, 0, second.val] at addresses
  exact (List.cons.inj (List.cons.inj (List.cons.inj addresses).2).2).1

private theorem root_match_empty (declaration : Fin 2) :
    matchAt (consumePlan declaration.val).rule consumeSpec 0 .left [] 0 []
      (consumePlan declaration.val).rule.left source = [] := by
  fin_cases declaration <;> cbv

theorem tucked_root_requires_equation (declaration : Fin 2) (trace : List BagChoice) (assignment : Assignment) :
    ¬ TracedMatches (consumePlan declaration.val).rule consumeSpec 0 .left [] 0 []
      (consumePlan declaration.val).rule.left source trace assignment := by
  intro matching
  have present := GeneralScopedMatch.matchAt_iff.mpr matching.matching
  rw [root_match_empty declaration] at present
  exact List.not_mem_nil present

theorem disabled_provider_has_no_query (choice : Choice) (bound : List TypeExpr)
    (initial final : Assignment) (row : Nat) (origins : List (Nat × List BagChoice)) :
    ¬ GeneralPremise.TracedQuery (GeneralPlanEnvironment.environment (plan [])) (choice.context bound)
      "allow" [.fvar "Q"] initial row final origins := by
  intro matching
  cases matching with
  | row selected _ _ _ _ =>
      change ([] : List GeneralPremise.ProviderRow)[row]? = some _ at selected
      simp at selected
  | dynamicRow dynamic _ _ _ _ _ _ _ => exact absurd dynamic (by decide +kernel)

def pendingMatcher {query : GeneralOccurrenceFrontier.Request} : GeneralOccurrenceFrontier.Task query → Bool
  | .rule frame => frame.state.agenda.any fun
      | .root root => root.state.agenda.any fun
          | .rootMatch matching => !matching.state.agenda.isEmpty
          | _ => false
  | _ => false

def pauseReadout (query : GeneralOccurrenceFrontier.Request) (fuel : Nat) :
    Nat × Bool × Option Bool × Bool × Bool :=
  let state := GeneralOccurrenceFrontier.run query fuel (GeneralOccurrenceFrontier.start query)
  (state.work, state.answers.isEmpty, state.agenda.head?.map pendingMatcher,
    GeneralOccurrenceFrontier.complete query state, state.universeScanned)

/-- Two actual frontier ticks leave the successful exposed-root match suspended
before its structural task is processed. No query rows or firings are emitted. -/
theorem pauses_inside_original_matcher :
    pauseReadout (actualRequest allowed exposed) 2 = (2, true, some true, false, false) := by
  rw [actual_request]
  cbv

/-- Pause and resume preserve the complete actual machine state. -/
theorem whole_state_resume (pattern : Pattern) (first second : Nat) :
    GeneralOccurrenceFrontier.run (actualRequest allowed pattern) second (paused allowed pattern first) =
      paused allowed pattern (first + second) :=
  (GeneralOccurrenceFrontier.run_add _ first second _).symm

#print axioms equation_enabled_four_actual_origins
#print axioms nested_actual_origins
#print axioms multiple_actual_origins
#print axioms both_extrusion_orientations_and_provider_rows
#print axioms tucked_root_requires_equation
#print axioms pauses_inside_original_matcher
#print axioms whole_state_resume

end Mettapedia.OSLF.MeTTaIL.GeneralGuardedBinderFrontierControls
