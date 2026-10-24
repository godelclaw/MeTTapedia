import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseEnvironmentExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedRuleInstantiationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseSchedulerExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryCorrectness

/-! Native source realization of the finite-provider general-premise query
frames. Registered native services have their separate execution contract. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Effects (State)
open SpaceSemantics (Program)
open Eval
open scoped ProgramQuotation

private def matcherEraseSource : Program := RuleExecutionProgram.matcherEraseProgram

private def instantiationSource : Program := RuleExecutionProgram.scopedInstantiationProgram

private def matcherSource : Program := RuleExecutionProgram.scopedMatcherProgram

private def querySource : Program := RuleExecutionProgram.premiseQueryProgram

private def extension : Program :=
  ((matcherEraseSource.append instantiationSource).append matcherSource).append querySource

def queryRuntimeProgram : Program := premiseRuntimeProgram.append extension

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem prior_agreement :
    ProgramAgreementOn premiseExecutionHeads premiseRuntimeProgram queryRuntimeProgram := by
  apply appended_program_agreement
  · intro equation member
    have checked : extension.equations.all (fun equation => !premiseExecutionHeads equation.head) = true := by
      rfl
    have row := List.all_eq_true.mp checked equation member
    cases selected : premiseExecutionHeads equation.head with
    | false => rfl
    | true => simp [selected] at row
  · intro name types member
    have checked : extension.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !premiseExecutionHeads head
        | _ => true) = true := by rfl
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases selected : premiseExecutionHeads name with
    | false => rfl
    | true => simp [selected] at row

theorem prior_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin premiseExecutionHeads code = true)
    (returned : PureReturns premiseRuntimeProgram caller state code state answer) :
    PureReturns queryRuntimeProgram caller state code state answer :=
  premise_returns_in_extension queryRuntimeProgram prior_agreement supported returned

def queryExpansionTerm {environment : Environment} {request : Query.Request}
    (expansion : Scheduler.Expansion (Query.Task environment request) (Query.Answer environment request) Query.Obligation) : Term :=
  PremiseSchedulerExecution.schedulerExpansionTerm queryTaskTerm queryAnswerTerm queryObligationTerm expansion

theorem query_state_wire_eq_scheduler {environment : Environment} {request : Query.Request}
    (state : Query.State environment request) :
    queryStateTerm state =
      PremiseSchedulerExecution.schedulerStateTerm queryTaskTerm queryAnswerTerm queryObligationTerm state := rfl

theorem query_source_no_initializers : querySource.initializers = [] := by decide +kernel

theorem query_source_equation_heads_unique : (querySource.equations.map (·.head)).Nodup := by decide +kernel


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Effects (State)
open SpaceSemantics (Program)
open Eval

private def baseHeads (head : String) : Bool :=
  premiseExecutionHeads head && !(["gslt:premise:check-assignment", "gslt:premise:check-row", "gslt:premise:check-values", "gslt:premise:constructor-declarations", "gslt:premise:context-next", "gslt:premise:context-quantified", "gslt:premise:ground-at", "gslt:premise:ground-list-at", "gslt:premise:machine-deliver", "gslt:premise:machine-evaluate", "gslt:premise:machine-expand", "gslt:premise:presentation-named", "gslt:premise:reflective-presentations", "gslt:premise:reflective-rules", "gslt:premise:signature", "gslt:premise:signature-candidates", "gslt:premise:source-type", "gslt:premise:specification", "gslt:premise:substitution-presentation", "gslt:premise:type-context-lookup"].contains head)

private def baseExtension : Program where
  equations := queryRuntimeProgram.equations.drop RuleExecutionProgram.program.equations.length
  declarations := queryRuntimeProgram.declarations.drop RuleExecutionProgram.program.declarations.length
  initializers := queryRuntimeProgram.initializers.drop RuleExecutionProgram.program.initializers.length
  facts := queryRuntimeProgram.facts.drop RuleExecutionProgram.program.facts.length
  layout := queryRuntimeProgram.layout.drop RuleExecutionProgram.program.layout.length

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem base_append : queryRuntimeProgram = RuleExecutionProgram.program.append baseExtension := by
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem base_closed : ProgramClosed baseHeads RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : RuleExecutionProgram.program.equations.all (fun equation =>
        !baseHeads equation.head || codeWithin baseHeads equation.body) = true := by rfl
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem base_agreement : ProgramAgreementOn baseHeads RuleExecutionProgram.program queryRuntimeProgram := by
  rw [base_append]
  apply appended_program_agreement
  · intro equation member
    have checked : baseExtension.equations.all (fun equation => !baseHeads equation.head) = true := by
      rfl
    have row := List.all_eq_true.mp checked equation member
    cases selected : baseHeads equation.head with
    | false => rfl
    | true => simp [selected] at row
  · intro name types member
    have checked : baseExtension.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => !baseHeads head
        | _ => true) = true := by rfl
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases selected : baseHeads name with
    | false => rfl
    | true => simp [selected] at row

theorem base_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin baseHeads code = true)
    (returned : PureReturns RuleExecutionProgram.program caller state code state answer) :
    PureReturns queryRuntimeProgram caller state code state answer :=
  path_of_closed_agreement base_closed base_agreement ⟨supported, rfl⟩ returned


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

abbrev runtime : Program := queryRuntimeProgram
abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
abbrev v (name : String) : Atom := .var name
abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
abbrev number (value : Nat) : Atom := encoded (.natural value)
abbrev stringValue (value : String) : Atom := encoded (.string value)
abbrev boundValue (bound : List TypeExpr) : Atom := encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound)
abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)
abbrev ruleValue (rule : RewriteRule) : Atom := encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule)
abbrev assignmentValue (assignment : Assignment) : Atom := encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment)
abbrev contextValue (context : Context) : Atom := encoded (contextTerm context)
abbrev queryValue (request : Query.Request) : Atom := encoded (queryRequestTerm request)
abbrev taskValue {env : Environment} {request : Query.Request} (task : Query.Task env request) : Atom := encoded (queryTaskTerm task)
abbrev expansionValue {env : Environment} {request : Query.Request}
    (expansion : Scheduler.Expansion (Query.Task env request) (Query.Answer env request) Query.Obligation) : Atom :=
  encoded (encodeOption queryExpansionTerm (some expansion))

def caseData (expression : Atom) (rows : SpaceSemantics.Cases) : Atom :=
  a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]

inductive Helper where | site | matchingRequest | expand

def Helper.head : Helper → String
  | .site => "gslt:premise:query-site"
  | .matchingRequest => "gslt:premise:query-matching-request"
  | .expand => "gslt:premise:query-expand-in"

def Helper.names : Helper → List String
  | .site => ["context", "argument"]
  | .matchingRequest => ["context", "index", "assignment", "schema", "value"]
  | .expand => ["environment", "request", "task"]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
def queryEquation (helper : Helper) : SpaceSemantics.Equation :=
  (runtime.equations.filter (fun equation => equation.head == helper.head))[0]'(by cases helper <;> decide +kernel)

def callee (helper : Helper) (values : List Atom) : Subst := (helper.names.zip values).reverse

theorem captured_closed (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem query_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses runtime helper.head values = [.evaluate (callee helper values) (queryEquation helper).body] :=
  PureData.named_equation_clause runtime helper.head (queryEquation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem query_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw runtime helper.head index = true := by
  cases helper <;> simp only [Helper.names, List.length_cons, List.length_nil] at bounded
  all_goals
    have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
    rcases small with rfl | rfl | rfl | rfl | rfl <;> first | omega | decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem query_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime (callee helper values) state (queryEquation helper).body state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return runtime caller (callee helper values) state state
    helper.head arguments (queryEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel)
  · intro index bounded
    apply query_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact query_clause helper values length
  · exact returned

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem query_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime [] state (a helper.head values) state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns runtime [] caller state state helper.head values arguments answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact query_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

theorem branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns runtime caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns runtime selected state body state answer) :
    PureReturns runtime caller state (caseData expression rows) state answer :=
  case_returns runtime caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns runtime caller state condition state (Effects.boolean value))
    (returned : PureReturns runtime caller state (if value then yes else no) state answer) :
    PureReturns runtime caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns runtime caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (computed : PureReturns runtime caller state expression state value)
    (continued : PureReturns runtime ((name, value) :: caller) state body state answer) :
    PureReturns runtime caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns runtime caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

def dataHeads : List String :=
  ["Some", "LCons", "RulePremise", "ScopedMatcherRequest", "PremiseExpansion", "PremiseSignatureUnavailable",
    "PremiseInputUnavailable", "PremiseArgumentShape", "PremiseQueryRows", "PremiseQueryArguments",
    "PremiseQueryAnswer", "PremiseQueryMatcher", "ArgumentOrigin"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem data_template (head : String) (arguments : List Atom)
    (supported : head ∈ dataHeads)
    (children : ∀ child ∈ arguments, PureData.Template runtime child) :
    PureData.Template runtime (a head arguments) := by
  have checked : dataHeads.all (fun name => decide
      ((ioHead name || StdLib.known name || runtime.equations.any (·.head == name)) = false ∧
        name ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])) = true := by
    rfl
  have row := List.all_eq_true.mp checked head supported
  rw [decide_eq_true_eq] at row
  exact .constructor head arguments row.1 row.2 children

def sourceCases (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [.symbol "case", _, .expression rows] => (readCases rows).getD []
  | _ => []

def siteCases : SpaceSemantics.Cases := sourceCases (queryEquation .site).body

def matchingRequestCases : SpaceSemantics.Cases := sourceCases (queryEquation .matchingRequest).body

def environmentCases : SpaceSemantics.Cases := sourceCases (queryEquation .expand).body

def requestCases : SpaceSemantics.Cases := sourceCases ((environmentCases.head!).2)

def taskCases : SpaceSemantics.Cases := sourceCases ((requestCases.head!).2)

def taskBody (index : Nat) : Atom := ((taskCases[index]?).getD (.symbol "unreachable", .symbol "None")).2

theorem site_shape : (queryEquation .site).body = caseData (v "context") siteCases := by decide +kernel

theorem matching_request_shape : (queryEquation .matchingRequest).body = caseData (v "context") matchingRequestCases := by decide +kernel

theorem expand_shape : (queryEquation .expand).body = caseData (v "environment") environmentCases := by decide +kernel

theorem environment_case_shape : (environmentCases.head!).2 = caseData (v "request") requestCases := by decide +kernel

theorem request_case_shape : (requestCases.head!).2 = caseData (v "task") taskCases := by decide +kernel

def contextCaller (context : Context) (caller : Subst) : Subst :=
  [("quantifiers", number context.quantifierDepth), ("premise", number context.premiseIndex),
    ("bound", boundValue context.bound), ("spec", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm context.spec)),
    ("rule", ruleValue context.rule), ("ruleIndex", number context.ruleIndex)] ++ caller

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue

theorem length_returns {α : Type} (encoder : α → Term) (caller : Subst) (state : State)
    (values : List α) (input : String)
    (captured : applySubst caller (v input) = encoded (encodeList encoder values)) :
    PureReturns runtime caller state (a "gslt:automata:length" [v input]) state (number values.length) := by
  have returned := MatchAutomataSourceExecution.length_captured_returns caller state
    (values.map encoder) (v input) (by
      simpa only [MatchAutomataSourceExecution.listValue, CettaWire.encodeList_map, Function.id_comp] using captured)
  have transferred := base_returns (by simp [codeWithin, expressionHeadWithin]; decide +kernel)
    (RuleExecutionProgram.automata_captured_returns
      (by simp [codeWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead]) returned)
  simpa only [List.length_map] using transferred


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def querySiteCasesSyntax : SpaceSemantics.Cases :=
  [(a "PremiseContext" [v "ruleIndex", v "rule", v "spec", v "bound", v "premise", v "quantifiers"], a "RulePremise" [v "premise", v "quantifiers", v "argument"]),
    (v "bad", .symbol "None")]

def queryMatchingCasesSyntax : SpaceSemantics.Cases :=
  [(a "PremiseContext" [v "ruleIndex", v "rule", v "spec", v "bound", v "premise", v "quantifiers"], a "let*" [.expression [.expression [v "ambient", a "gslt:automata:length" [v "bound"]], .expression [v "site", a "gslt:premise:query-site" [v "context", v "index"]]], a "ScopedMatcherRequest" [v "rule", v "spec", v "ambient", v "site", .symbol "LNil", number 0, v "assignment", v "schema", v "value"]]),
    (v "bad", .symbol "None")]

theorem site_cases_syntax : siteCases = querySiteCasesSyntax := by decide +kernel

theorem matching_cases_syntax : matchingRequestCases = queryMatchingCasesSyntax := by decide +kernel

theorem environment_cases_syntax : environmentCases =
  [(a "PremiseEnvironment" [v "declarations", v "rewrites", v "specifications", a "PremiseProvider" [v "signatures", v "rows"], v "reflection", v "free"], caseData (v "request") requestCases),
    (v "badEnvironment", .symbol "None")] := by decide +kernel

theorem request_cases_syntax : requestCases =
  [(a "PremiseQueryRequest" [a "PremiseContext" [v "ruleIndex", v "rule", v "spec", v "bound", v "premise", v "quantifiers"], v "relation", v "arguments", v "initial"], caseData (v "task") taskCases),
    (v "badRequest", .symbol "None")] := by decide +kernel

theorem task_cases_syntax : taskCases =
  [(.symbol "PremiseQueryStart", taskBody 0),
    (a "PremiseQueryRows" [v "signature", v "cursor"], taskBody 1),
    (a "PremiseQueryArguments" [v "rowIndex", v "index", v "assignment", .symbol "LNil", .symbol "LNil", .symbol "LNil", v "origins"], taskBody 2),
    (a "PremiseQueryArguments" [v "rowIndex", v "index", v "assignment", a "LCons" [v "schema", v "schemas"], a "LCons" [v "value", v "values"], a "LCons" [.symbol "RelationInput", v "modes"], v "origins"], taskBody 3),
    (a "PremiseQueryArguments" [v "rowIndex", v "index", v "assignment", a "LCons" [v "schema", v "schemas"], a "LCons" [v "value", v "values"], a "LCons" [.symbol "RelationOutput", v "modes"], v "origins"], taskBody 4),
    (a "PremiseQueryArguments" [v "rowIndex", v "index", v "assignment", v "schemas", v "values", v "modes", v "origins"], taskBody 5),
    (a "PremiseQueryMatcher" [v "rowIndex", v "argument", v "schemas", v "values", v "modes", v "origins", v "query", v "state", v "cursor"], taskBody 6),
    (v "badTask", taskBody 7)] := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval

local macro "query_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue

theorem query_site_returns (state : State) (context : Context) (index : Nat) :
    PureReturns runtime [] state
      (a "gslt:premise:query-site" [contextValue context, number index]) state
      (encoded (InferenceCettaWire.AuthoredRule.siteTerm (context.site index))) := by
  let caller := callee .site [contextValue context, number index]
  let selected := contextCaller context caller
  apply query_call .site [] state _ _ _ rfl (captured_closed _)
  rw [site_shape]
  apply branch_returns caller selected state _ (contextValue context) siteCases
    (a "RulePremise" [v "premise", v "quantifiers", v "argument"]) _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns runtime caller state "context"
  · simp [site_cases_syntax, querySiteCasesSyntax, contextTerm, selected, contextCaller, caller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · have templated : PureData.Template runtime (a "RulePremise" [v "premise", v "quantifiers", v "argument"]) := by
      query_template
    simpa [GeneralPremise.Context.site, InferenceCettaWire.AuthoredRule.siteTerm,
      selected, contextCaller, caller, callee, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
      CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      PureData.template_return runtime selected state _ templated

theorem query_site_captured_returns (caller : Subst) (state : State) (context : Context) (index : Nat)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [contextValue context, number index]) :
    PureReturns runtime caller state (a "gslt:premise:query-site" [one, two]) state
      (encoded (InferenceCettaWire.AuthoredRule.siteTerm (context.site index))) :=
  query_capture .site caller state _ _ _ rfl captured (query_site_returns state context index)

private def matchingRequestData : Atom :=
  a "ScopedMatcherRequest" [v "rule", v "spec", v "ambient", v "site", .symbol "LNil", number 0,
    v "assignment", v "schema", v "value"]

private def matchingRequestBody : Atom :=
  a "let*" [.expression [.expression [v "ambient", a "gslt:automata:length" [v "bound"]],
    .expression [v "site", a "gslt:premise:query-site" [v "context", v "index"]]], matchingRequestData]

private theorem matching_request_case_body : (matchingRequestCases.head!).2 = matchingRequestBody := by decide +kernel

theorem query_matching_request_returns (state : State) (request : Query.Request) (index : Nat)
    (assignment : Assignment) (schema value : Pattern) :
    PureReturns runtime [] state
      (a "gslt:premise:query-matching-request" [contextValue request.context, number index,
        assignmentValue assignment, patternValue schema, patternValue value]) state
      (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        (Query.matchingRequest request index assignment schema value))) := by
  let caller := callee .matchingRequest [contextValue request.context, number index,
    assignmentValue assignment, patternValue schema, patternValue value]
  let selected := contextCaller request.context caller
  let ambient := ("ambient", number request.context.bound.length) :: selected
  let final := ("site", encoded (InferenceCettaWire.AuthoredRule.siteTerm (request.context.site index))) :: ambient
  apply query_call .matchingRequest [] state _ _ _ rfl (captured_closed _)
  rw [matching_request_shape]
  apply branch_returns caller selected state _ (contextValue request.context) matchingRequestCases matchingRequestBody _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns runtime caller state "context"
  · simp [matching_cases_syntax, queryMatchingCasesSyntax, matchingRequestBody, matchingRequestData,
      contextTerm, selected, contextCaller, caller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · unfold matchingRequestBody
    apply PureData.let_bindings_return (pairs := [
      (v "ambient", a "gslt:automata:length" [v "bound"]),
      (v "site", a "gslt:premise:query-site" [v "context", v "index"])])
      (final := final) (middle := state) _ state matchingRequestData _ _
    · apply PureData.BindingsReturn.cons (bound := ambient) (middle := state)
        (value := number request.context.bound.length)
      · exact length_returns InferenceCettaWire.AuthoredRule.typeTerm selected state request.context.bound "bound"
          (by simp [selected, contextCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
          ambient, selected, contextCaller, caller, callee, Helper.names, Subst.lookup]
      · apply PureData.BindingsReturn.cons (bound := final) (middle := state)
          (value := encoded (InferenceCettaWire.AuthoredRule.siteTerm (request.context.site index)))
        · exact query_site_captured_returns ambient state request.context index (v "context") (v "index")
            (by simp [ambient, selected, contextCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
            final, ambient, selected, contextCaller, caller, callee, Helper.names, Subst.lookup]
        · exact .nil final state
    · have templated : PureData.Template runtime matchingRequestData := by unfold matchingRequestData; query_template
      simpa [matchingRequestData, Query.matchingRequest,
        RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
        final, ambient, selected, contextCaller, caller, callee, Helper.names,
        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return runtime final state _ templated

theorem query_matching_request_captured_returns (caller : Subst) (state : State)
    (request : Query.Request) (index : Nat) (assignment : Assignment) (schema value : Pattern)
    (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [contextValue request.context, number index, assignmentValue assignment, patternValue schema, patternValue value]) :
    PureReturns runtime caller state (a "gslt:premise:query-matching-request" [one, two, three, four, five]) state
      (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        (Query.matchingRequest request index assignment schema value))) :=
  query_capture .matchingRequest caller state _ _ _ rfl captured
    (query_matching_request_returns state request index assignment schema value)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval

local macro "query_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue queryValue taskValue

abbrev environmentValue (environment : Environment) (free : List (String × TypeExpr)) : Atom :=
  encoded (environmentTerm environment free)

def environmentCaller (environment : Environment) (free : List (String × TypeExpr)) (caller : Subst) : Subst :=
  [("free", encoded (DeclarationTyping.freeContextTerm free)),
    ("reflection", encoded (reflectionTerm environment.reflection)),
    ("rows", encoded (encodeList providerRowTerm environment.provider.rows)),
    ("signatures", encoded (encodeList signatureTerm environment.provider.signatures)),
    ("specifications", encoded (encodeList specificationTerm environment.specifications)),
    ("rewrites", encoded (encodeList InferenceCettaWire.AuthoredRule.rewriteTerm environment.language.rewrites)),
    ("declarations", encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm environment.language.terms))] ++ caller

def requestCaller (request : Query.Request) (caller : Subst) : Subst :=
  [("initial", assignmentValue request.initial), ("arguments", patternsValue request.arguments),
    ("relation", stringValue request.relation)] ++ contextCaller request.context caller

def frameCaller (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request) (free : List (String × TypeExpr)) : Subst :=
  requestCaller request (environmentCaller environment free
    (callee .expand [environmentValue environment free, queryValue request, taskValue task]))

theorem expand_branch_returns (state : State) (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request) (free : List (String × TypeExpr))
    (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase (frameCaller environment request task free) (taskValue task)
      taskCases = some (selected, body))
    (continued : PureReturns runtime selected state body state answer) :
    PureReturns runtime [] state
      (a "gslt:premise:query-expand-in" [environmentValue environment free, queryValue request, taskValue task])
      state answer := by
  let caller := callee .expand [environmentValue environment free, queryValue request, taskValue task]
  let envCaller := environmentCaller environment free caller
  let reqCaller := requestCaller request envCaller
  apply query_call .expand [] state _ _ _ rfl (captured_closed _)
  rw [expand_shape]
  apply branch_returns caller envCaller state _ (environmentValue environment free)
    environmentCases (environmentCases.head!).2 _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns runtime caller state "environment"
  · simp [environment_cases_syntax, environmentValue, environmentTerm,
      providerTerm, envCaller, environmentCaller, caller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [environment_case_shape]
    apply branch_returns envCaller reqCaller state _ (queryValue request) requestCases (requestCases.head!).2 _
    · simpa [envCaller, environmentCaller, caller, callee, Helper.names, applySubst, Subst.lookup] using
        variable_returns runtime envCaller state "request"
    · simp [request_cases_syntax, queryRequestTerm,
        contextTerm, reqCaller, requestCaller, contextCaller, envCaller, environmentCaller, caller, callee, Helper.names,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    · rw [request_case_shape]
      apply branch_returns reqCaller selected state _ (taskValue task) taskCases body _
      · simpa [reqCaller, requestCaller, contextCaller, envCaller, environmentCaller,
          caller, callee, Helper.names, applySubst, Subst.lookup] using
          variable_returns runtime reqCaller state "task"
      · exact matched
      · exact continued

private def startUnavailableData : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
    a "LCons" [a "PremiseSignatureUnavailable" [v "relation", v "arity"], .symbol "LNil"]]]

private def startRowsData : Atom :=
  a "Some" [a "PremiseExpansion" [a "LCons" [a "PremiseQueryRows" [v "signature", number 0], .symbol "LNil"],
    .symbol "LNil", .symbol "LNil"]]

private def startSignatureCases : SpaceSemantics.Cases :=
  [(.symbol "None", startUnavailableData), (a "Some" [v "signature"], startRowsData), (v "badSignature", .symbol "None")]

private def startSignatureBody : Atom :=
  caseData (a "gslt:premise:signature" [v "relation", v "arity", a "PremiseProvider" [v "signatures", v "rows"]]) startSignatureCases

private def startBody : Atom :=
  a "let" [v "arity", a "gslt:automata:length" [v "arguments"], startSignatureBody]

private theorem start_shape : taskBody 0 = startBody := by decide +kernel

theorem query_expand_start_returns (state : State) (environment : Environment) (request : Query.Request)
    (free : List (String × TypeExpr))
    (unregistered : request.relation ∉ environment.provider.dynamicRelations) :
    PureReturns runtime [] state
      (a "gslt:premise:query-expand-in" [environmentValue environment free, queryValue request,
        taskValue (Query.Task.start (environment := environment) (request := request))]) state
      (expansionValue (Query.expand environment request .start)) := by
  let caller := frameCaller environment request .start free
  let counted := ("arity", number request.arguments.length) :: caller
  apply expand_branch_returns state environment request .start free caller startBody _
  · simp [task_cases_syntax, start_shape,
      startBody, startSignatureBody, startSignatureCases, startUnavailableData, startRowsData,
      queryTaskTerm, caller, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, CettaWireAtom.encode]
  · unfold startBody
    apply named_let_returns caller state "arity" _ (number request.arguments.length) startSignatureBody _
    · simp [caller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
    · exact length_returns InferenceCettaWire.encodePattern caller state request.arguments "arguments"
        (by simp [caller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
          InferenceCettaWire.encodePatterns_eq_encodeList, applySubst, Subst.lookup])
    · have queried := GeneralExecution.signature_captured_returns counted state environment.provider request.relation request.arguments.length
        (v "relation") (v "arity") (a "PremiseProvider" [v "signatures", v "rows"])
        (by
          change [v "relation", v "arity", a "PremiseProvider" [v "signatures", v "rows"]].map (applySubst counted) =
            [stringValue request.relation, number request.arguments.length, encoded (providerTerm environment.provider)]
          simp [counted, caller, frameCaller, requestCaller, contextCaller, environmentCaller,
            callee, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, providerTerm])
      change PureReturns _ counted state
        (a "gslt:premise:signature" [v "relation", v "arity", a "PremiseProvider" [v "signatures", v "rows"]]) state
        (encoded (encodeOption signatureTerm (signature? environment.provider request.relation request.arguments.length))) at queried
      have computed := prior_returns (by simp [codeWithin, expressionHeadWithin, atomsWithin, premiseExecutionHeads])
        (premise_previous_returns (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) queried)
      cases found : signature? environment.provider request.relation request.arguments.length with
      | none =>
          have original : Query.expand (matcher := GeneralPremise.MatchingExecution.ordinary) environment request .start =
              { unresolved := [.signatureUnavailable request.relation request.arguments.length] } := by
            simp only [Query.expand]
            split <;> simp_all
          rw [original]
          unfold startSignatureBody
          apply branch_returns counted counted state _ (.symbol "None") startSignatureCases startUnavailableData _
          · simpa [found, encodeOption, CettaWireAtom.encode] using computed
          · simp [startSignatureCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
          · have templated : PureData.Template runtime startUnavailableData := by unfold startUnavailableData; query_template
            simpa [expansionValue, queryExpansionTerm,
              PremiseSchedulerExecution.schedulerExpansionTerm, queryObligationTerm, encodeOption,
              encodeList, startUnavailableData, counted, caller, frameCaller, requestCaller, contextCaller,
              environmentCaller, callee, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return runtime counted state _ templated
      | some signature =>
          have original : Query.expand (matcher := GeneralPremise.MatchingExecution.ordinary) environment request .start =
              { tasks := [.rows ⟨signature, found, 0⟩] } := by
            simp only [Query.expand]
            split
            · rename_i impossible
              rw [found] at impossible
              cases impossible
            · rename_i actual selected
              have same : actual = signature := Option.some.inj (selected.symm.trans found)
              subst actual
              simp only [dif_neg unregistered]
          rw [original]
          let selected := ("signature", encoded (signatureTerm signature)) :: counted
          unfold startSignatureBody
          apply branch_returns counted selected state _ (encoded (encodeOption signatureTerm (some signature))) startSignatureCases startRowsData _
          · simpa only [found] using computed
          · simp [startSignatureCases, selected, counted, caller, frameCaller, requestCaller, contextCaller,
              environmentCaller, callee, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
          · have templated : PureData.Template runtime startRowsData := by unfold startRowsData; query_template
            simpa [expansionValue, queryExpansionTerm,
              PremiseSchedulerExecution.schedulerExpansionTerm, queryTaskTerm, encodeOption,
              encodeList, startRowsData, selected, counted, caller, frameCaller, requestCaller, contextCaller,
              environmentCaller, callee, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return runtime selected state _ templated


theorem row_at_returns {α : Type} (encoder : α → Term) (caller : Subst) (state : State)
    (index : Nat) (values : List α) (one two : String)
    (captured : [v one, v two].map (applySubst caller) = [number index, encoded (encodeList encoder values)]) :
    PureReturns runtime caller state (a "gslt:rule:row-at" [v one, v two]) state
      (encoded (encodeOption encoder values[index]?)) := by
  have returned := RuleInstantiationExecution.RowLookup.row_at_captured_returns caller state index
    (values.map encoder) (v one) (v two) (by
      simpa only [CettaWire.encodeList_map, Function.id_comp] using captured)
  have transferred := base_returns (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) returned
  cases found : values[index]? <;>
    simpa [List.getElem?_map, found, MatchAutomataBindingExecution.payloadOptionTerm, encodeOption] using transferred

theorem successor_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns runtime caller state (a "+" [v name, number 1]) state (number (value + 1)) := by
  apply native_binary_call_returns runtime caller state state state state "+"
    (v name) (number 1) (number value) (number 1) (number (value + 1))
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  · simpa only [captured] using variable_returns runtime caller state name
  · exact grounded_returns runtime caller state (.int 1)
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one] using
      StdLib.integer_addition state (value : Int) 1
  · decide

private def rowsEmptyData : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]

private def rowsTailData : Atom :=
  a "PremiseQueryRows" [v "signature", v "next"]

private def rowsAcceptedData : Atom :=
  a "Some" [a "PremiseExpansion" [
    a "LCons" [a "PremiseQueryArguments" [v "cursor", number 0, v "initial", v "arguments", v "values", v "modes", .symbol "LNil"],
      a "LCons" [rowsTailData, .symbol "LNil"]], .symbol "LNil", .symbol "LNil"]]

private def rowsRejectedData : Atom :=
  a "Some" [a "PremiseExpansion" [a "LCons" [rowsTailData, .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def rowsCheckedBody : Atom := a "if" [v "checked", rowsAcceptedData, rowsRejectedData]

private def rowsConsBody : Atom :=
  a "let*" [.expression [.expression [v "next", a "+" [v "cursor", number 1]],
    .expression [v "checked", a "gslt:premise:check-row" [v "declarations", v "free", v "bound", v "signature",
      a "PremiseProviderRow" [v "rowRelation", v "values"]]]], rowsCheckedBody]

private def rowsSignatureCases : SpaceSemantics.Cases :=
  [(a "PremiseSignature" [v "signatureRelation", v "types", v "modes"], rowsConsBody),
    (v "badSignature", .symbol "None")]

private def rowsSignatureBody : Atom := caseData (v "signature") rowsSignatureCases

private def rowsCases : SpaceSemantics.Cases :=
  [(.symbol "None", rowsEmptyData),
    (a "Some" [a "PremiseProviderRow" [v "rowRelation", v "values"]], rowsSignatureBody),
    (v "badRow", .symbol "None")]

private def rowsBody : Atom := caseData (a "gslt:rule:row-at" [v "cursor", v "rows"]) rowsCases

private theorem rows_shape : taskBody 1 = rowsBody := by decide +kernel

def rowsCaller (environment : Environment) (request : Query.Request)
    (frame : Query.RowsFrame environment request) (free : List (String × TypeExpr)) : Subst :=
  [("cursor", number frame.cursor), ("signature", encoded (signatureTerm frame.signature))] ++
    frameCaller environment request (.rows frame) free

private def rowFoundCaller (row : ProviderRow) (caller : Subst) : Subst :=
  [("values", patternsValue row.values), ("rowRelation", stringValue row.relation)] ++ caller

private def rowSignatureCaller (signature : Signature) (caller : Subst) : Subst :=
  [("modes", encoded (encodeList modeTerm signature.modes)),
    ("types", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm signature.argumentTypes)),
    ("signatureRelation", stringValue signature.relation)] ++ caller

private def rowsAcceptedValue (environment : Environment) (request : Query.Request)
    (frame : Query.RowsFrame environment request) (row : ProviderRow) : Atom :=
  encoded (.application "Some" [.application "PremiseExpansion" [
    .application "LCons" [.application "PremiseQueryArguments" [.natural frame.cursor, .natural 0,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm request.initial,
      InferenceCettaWire.encodePatterns request.arguments, InferenceCettaWire.encodePatterns row.values,
      encodeList modeTerm frame.signature.modes, .symbol "LNil"],
      .application "LCons" [.application "PremiseQueryRows" [signatureTerm frame.signature, .natural (frame.cursor + 1)], .symbol "LNil"]],
    .symbol "LNil", .symbol "LNil"]])

private def rowsRejectedValue (environment : Environment) (request : Query.Request)
    (frame : Query.RowsFrame environment request) : Atom :=
  encoded (.application "Some" [.application "PremiseExpansion" [
    .application "LCons" [.application "PremiseQueryRows" [signatureTerm frame.signature, .natural (frame.cursor + 1)], .symbol "LNil"],
    .symbol "LNil", .symbol "LNil"]])

private theorem rowsExpansion_none (environment : Environment) (request : Query.Request)
    (frame : Query.RowsFrame environment request) (missing : environment.provider.rows[frame.cursor]? = none) :
    expansionValue (Query.expand environment request (.rows frame)) =
      encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]) := by
  simp only [Query.expand]
  split
  · rfl
  · rename_i row found
    simp [missing] at found

private theorem rowsExpansion_some (environment : Environment) (request : Query.Request)
    (frame : Query.RowsFrame environment request) (row : ProviderRow)
    (found : environment.provider.rows[frame.cursor]? = some row) :
    expansionValue (Query.expand environment request (.rows frame)) =
      if checkRow environment.language environment.free request.context.bound frame.signature row then
        rowsAcceptedValue environment request frame row else rowsRejectedValue environment request frame := by
  simp only [Query.expand]
  split
  · rename_i missing
    simp [found] at missing
  · rename_i selected selectedFound
    have same : selected = row := Option.some.inj (selectedFound.symm.trans found)
    subst selected
    split <;> rename_i checked <;>
      simp [expansionValue, queryExpansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm,
        queryTaskTerm, originsTerm, encodeOption, encodeList, rowsAcceptedValue, rowsRejectedValue,
        CettaWireAtom.encode, CettaWireAtom.encodeMany]

theorem query_expand_rows_returns (state : State) (environment : Environment) (request : Query.Request)
    (frame : Query.RowsFrame environment request) (footprint : List String)
    (covers : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint) :
    PureReturns runtime [] state
      (a "gslt:premise:query-expand-in" [environmentValue environment (environment.free.entriesOn footprint), queryValue request,
        taskValue (.rows frame)]) state (expansionValue (Query.expand environment request (.rows frame))) := by
  let free := environment.free.entriesOn footprint
  let caller := rowsCaller environment request frame free
  apply expand_branch_returns state environment request (.rows frame) free caller rowsBody _
  · simp [task_cases_syntax, rows_shape, queryTaskTerm, caller, rowsCaller, frameCaller, requestCaller, contextCaller,
      environmentCaller, callee, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · have lookup := row_at_returns providerRowTerm caller state frame.cursor environment.provider.rows "cursor" "rows"
      (by simp [caller, rowsCaller, frameCaller, requestCaller, contextCaller, environmentCaller,
        callee, Helper.names, applySubst, Subst.lookup])
    cases found : environment.provider.rows[frame.cursor]? with
    | none =>
        rw [rowsExpansion_none environment request frame found]
        unfold rowsBody
        apply branch_returns caller caller state _ (.symbol "None") rowsCases rowsEmptyData _
        · simpa [found, encodeOption, CettaWireAtom.encode] using lookup
        · simp [rowsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · have templated : PureData.Template runtime rowsEmptyData := by unfold rowsEmptyData; query_template
          exact PureData.template_return runtime caller state _ templated
    | some row =>
        rw [rowsExpansion_some environment request frame row found]
        let selected := rowFoundCaller row caller
        let typed := rowSignatureCaller frame.signature selected
        let next := ("next", number (frame.cursor + 1)) :: typed
        let final := ("checked", Effects.boolean (checkRow environment.language environment.free request.context.bound frame.signature row)) :: next
        unfold rowsBody
        apply branch_returns caller selected state _ (encoded (encodeOption providerRowTerm (some row))) rowsCases rowsSignatureBody _
        · simpa only [found] using lookup
        · simp [rowsCases, selected, rowFoundCaller, caller, rowsCaller, frameCaller, requestCaller, contextCaller,
            environmentCaller, callee, Helper.names, providerRowTerm, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
        · unfold rowsSignatureBody
          apply branch_returns selected typed state _ (encoded (signatureTerm frame.signature)) rowsSignatureCases rowsConsBody _
          · simpa [selected, rowFoundCaller, caller, rowsCaller, frameCaller, requestCaller, contextCaller,
              environmentCaller, callee, Helper.names, applySubst, Subst.lookup] using
              variable_returns runtime selected state "signature"
          · simp [rowsSignatureCases, typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
              requestCaller, contextCaller, environmentCaller, callee, Helper.names, signatureTerm,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
          · unfold rowsConsBody
            apply PureData.let_bindings_return (pairs := [
              (v "next", a "+" [v "cursor", number 1]),
              (v "checked", a "gslt:premise:check-row" [v "declarations", v "free", v "bound", v "signature",
                a "PremiseProviderRow" [v "rowRelation", v "values"]])])
              (final := final) (middle := state) _ state rowsCheckedBody _ _
            · apply PureData.BindingsReturn.cons (bound := next) (middle := state) (value := number (frame.cursor + 1))
              · exact successor_returns typed state frame.cursor "cursor" (by
                  simp [typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
                    requestCaller, contextCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                  next, typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
                  requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
              · apply PureData.BindingsReturn.cons (bound := final) (middle := state)
                  (value := Effects.boolean (checkRow environment.language environment.free request.context.bound frame.signature row))
                · have checked := GeneralExecution.check_row_captured_returns next state environment.language free request.context.bound
                    frame.signature row (v "declarations") (v "free") (v "bound") (v "signature")
                    (a "PremiseProviderRow" [v "rowRelation", v "values"]) (by
                      change [v "declarations", v "free", v "bound", v "signature", a "PremiseProviderRow" [v "rowRelation", v "values"]].map (applySubst next) =
                        [encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm environment.language.terms),
                          encoded (DeclarationTyping.freeContextTerm free), boundValue request.context.bound,
                          encoded (signatureTerm frame.signature), encoded (providerRowTerm row)]
                      simp [next, typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
                        requestCaller, contextCaller, environmentCaller, callee, Helper.names, providerRowTerm,
                        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany])
                  have transported := prior_returns (by simp [codeWithin, expressionHeadWithin, atomsWithin, premiseExecutionHeads])
                    (premise_previous_returns (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) checked)
                  simpa only [free, check_row_snapshot environment.language environment.free request.context.bound
                    environment.provider frame.signature row (List.mem_of_getElem? found) footprint covers] using transported
                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                    final, next, typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
                    requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
                · exact .nil final state
            · unfold rowsCheckedBody
              apply bool_if_returns final state (v "checked")
                (checkRow environment.language environment.free request.context.bound frame.signature row)
                rowsAcceptedData rowsRejectedData _
              · simpa [final, applySubst, Subst.lookup] using variable_returns runtime final state "checked"
              · cases checked : checkRow environment.language environment.free request.context.bound frame.signature row with
                | false =>
                    have templated : PureData.Template runtime rowsRejectedData := by unfold rowsRejectedData rowsTailData; query_template
                    simpa [checked, rowsRejectedData, rowsTailData, rowsRejectedValue,
                      final, next, typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
                      requestCaller, contextCaller, environmentCaller, callee, Helper.names,
                      applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                      PureData.template_return runtime final state _ templated
                | true =>
                    have templated : PureData.Template runtime rowsAcceptedData := by unfold rowsAcceptedData rowsTailData; query_template
                    simpa [checked, rowsAcceptedData, rowsTailData, rowsAcceptedValue,
                      final, next, typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
                      requestCaller, contextCaller, environmentCaller, callee, Helper.names,
                      applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                      PureData.template_return runtime final state _ templated


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue queryValue taskValue

local macro "query_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

private def argumentsEmptyData : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]

private def argumentsAcceptedData : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil",
    a "LCons" [a "PremiseQueryAnswer" [v "rowIndex", v "assignment", v "origins"], .symbol "LNil"],
    .symbol "LNil"]]

private def argumentsDoneBody : Atom :=
  a "if" [a "gslt:premise:check-assignment"
    [v "declarations", v "free", v "bound", v "rule", v "spec", v "assignment"],
    argumentsAcceptedData, argumentsEmptyData]

private theorem arguments_done_shape : taskBody 2 = argumentsDoneBody := by decide +kernel

theorem query_arguments_wire (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) :
    queryTaskTerm (.arguments frame) = .application "PremiseQueryArguments"
      [.natural frame.rowIndex, .natural frame.index,
        RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.assignment,
        InferenceCettaWire.encodePatterns frame.schemas, InferenceCettaWire.encodePatterns frame.values,
        encodeList modeTerm frame.modes, originsTerm frame.origins] := rfl

def argumentsDoneCaller (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (free : List (String × TypeExpr)) : Subst :=
  [("origins", encoded (originsTerm frame.origins)), ("assignment", assignmentValue frame.assignment),
    ("index", number frame.index), ("rowIndex", number frame.rowIndex)] ++
    frameCaller environment request (.arguments frame) free

private def argumentsAcceptedValue (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) : Atom :=
  encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil",
    .application "LCons" [.application "PremiseQueryAnswer" [.natural frame.rowIndex,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.assignment,
      originsTerm frame.origins], .symbol "LNil"], .symbol "LNil"]])

private theorem arguments_done_expansion (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request)
    (schemas : frame.schemas = []) (values : frame.values = []) (modes : frame.modes = []) :
    expansionValue (Query.expand environment request (.arguments frame)) =
      if checkTypedAssignment environment request.context frame.assignment then
        argumentsAcceptedValue environment request frame else
        encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]) := by
  rcases frame with ⟨rowIndex, index, assignment, schemas', values', modes', origins, finish⟩
  change schemas' = [] at schemas
  change values' = [] at values
  change modes' = [] at modes
  subst schemas'
  subst values'
  subst modes'
  dsimp only [Query.expand, Query.expandArguments]
  split <;>
    simp [expansionValue, queryExpansionTerm, queryAnswerTerm,
      PremiseSchedulerExecution.schedulerExpansionTerm, argumentsAcceptedValue, encodeOption, encodeList]

theorem query_expand_arguments_done_returns (state : State) (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request)
    (schemas : frame.schemas = []) (values : frame.values = []) (modes : frame.modes = [])
    (footprint : List String)
    (covers : ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint) :
    PureReturns runtime [] state
      (a "gslt:premise:query-expand-in" [environmentValue environment (environment.free.entriesOn footprint),
        queryValue request, taskValue (.arguments frame)]) state
      (expansionValue (Query.expand environment request (.arguments frame))) := by
  let caller := argumentsDoneCaller environment request frame (environment.free.entriesOn footprint)
  apply expand_branch_returns state environment request (.arguments frame) (environment.free.entriesOn footprint)
    caller argumentsDoneBody _
  · simp [task_cases_syntax, arguments_done_shape, query_arguments_wire, schemas, values, modes,
      InferenceCettaWire.encodePatterns,
      caller, argumentsDoneCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · have checked := GeneralExecution.check_assignment_captured_returns caller state environment.language
      (environment.free.entriesOn footprint) request.context.bound request.context.rule request.context.spec frame.assignment
      (v "declarations") (v "free") (v "bound") (v "rule") (v "spec") (v "assignment") (by
        change [v "declarations", v "free", v "bound", v "rule", v "spec", v "assignment"].map (applySubst caller) =
          [encoded (DeclarationTyping.declarationsTerm environment.language.terms),
            encoded (DeclarationTyping.freeContextTerm (environment.free.entriesOn footprint)),
            boundValue request.context.bound, ruleValue request.context.rule,
            encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.context.spec), assignmentValue frame.assignment]
        simp [caller, argumentsDoneCaller, frameCaller, requestCaller, contextCaller, environmentCaller,
          callee, Helper.names, applySubst, Subst.lookup, DeclarationTyping.declarationsTerm])
    have transferred := prior_returns (by simp [codeWithin, expressionHeadWithin, atomsWithin, premiseExecutionHeads])
      (premise_previous_returns (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) checked)
    rw [ConditionalEquationExecution.checkAssignment_snapshot environment.language environment.free request.context.bound request.context.rule request.context.spec frame.assignment footprint covers] at transferred
    rw [arguments_done_expansion environment request frame schemas values modes]
    unfold argumentsDoneBody
    apply bool_if_returns caller state _ (checkTypedAssignment environment request.context frame.assignment)
      argumentsAcceptedData argumentsEmptyData _ transferred
    cases checkedValue : checkTypedAssignment environment request.context frame.assignment with
    | false =>
        have templated : PureData.Template runtime argumentsEmptyData := by unfold argumentsEmptyData; query_template
        simpa [checkedValue, argumentsEmptyData, applySubst, applySubst.applySubstList, CettaWireAtom.encode,
          CettaWireAtom.encodeMany] using PureData.template_return runtime caller state _ templated
    | true =>
        have templated : PureData.Template runtime argumentsAcceptedData := by unfold argumentsAcceptedData; query_template
        simpa [checkedValue, argumentsAcceptedData, argumentsAcceptedValue,
          caller, argumentsDoneCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
          applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return runtime caller state _ templated


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue queryValue taskValue

def ownedHeads (head : String) : Bool :=
  ([Helper.site.head, Helper.matchingRequest.head, Helper.expand.head, "+", "=="] ++ dataHeads).contains head

theorem helper_supported (helper : Helper) : ownedHeads helper.head = true := by cases helper <;> decide

theorem helper_clause (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (helper : Helper) (values : List Atom) (length : values.length = helper.names.length) :
    clauses program helper.head values = [.evaluate (callee helper values) (queryEquation helper).body] := by
  rw [← agreement.bodies helper.head values (helper_supported helper)]
  exact query_clause helper values length

theorem helper_raw (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw program helper.head index = true := by
  rw [← agreement.demand helper.head index (helper_supported helper)]
  exact query_raw helper index bounded

theorem helper_call (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (helper : Helper) (caller : Subst) (state : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length) (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (callee helper values) state (queryEquation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (callee helper values) state state
    helper.head arguments (queryEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide) _ _ _ returned
  · rw [← agreement.dispatch helper.head (helper_supported helper)]
    cases helper <;> decide +kernel
  · intro index bounded
    apply helper_raw program agreement helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause program agreement helper values length

theorem helper_capture (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (helper : Helper) (caller : Subst) (state : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length) (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] state (a helper.head values) state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head values arguments answer
    _ _ (by cases helper <;> decide) _ returned
  · rw [← agreement.dispatch helper.head (helper_supported helper)]
    cases helper <;> decide +kernel
  · intro index bounded
    exact helper_raw program agreement helper index (by omega)
  · simpa only [captured_closed] using captured.symm

theorem data_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (head : String) (arguments : List Atom) (member : head ∈ dataHeads)
    (children : ∀ argument ∈ arguments, PureData.Template program argument) :
    PureData.Template program (a head arguments) := by
  apply PureData.Template.constructor head arguments _ _ children
  · have supported : ownedHeads head = true := by simp [ownedHeads, member]
    rw [← agreement.dispatch head supported]
    have checked : dataHeads.all (fun name => decide
        ((ioHead name || StdLib.known name || runtime.equations.any (·.head == name)) = false ∧
          name ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])) = true := by
      rfl
    have row := List.all_eq_true.mp checked head member
    rw [decide_eq_true_eq] at row
    exact row.1
  · simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem branch_returns (program : Program) (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns program caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns program selected state body state answer) :
    PureReturns program caller state (caseData expression rows) state answer :=
  case_returns program caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

theorem bool_if_returns (program : Program) (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller state condition state (Effects.boolean value))
    (returned : PureReturns program caller state (if value then yes else no) state answer) :
    PureReturns program caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns program caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

theorem named_let_returns (program : Program) (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (computed : PureReturns program caller state expression state value)
    (continued : PureReturns program ((name, value) :: caller) state body state answer) :
    PureReturns program caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns program caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

theorem add_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (caller : Subst) (state : State) (left right : Nat) (one two : Atom)
    (first : PureReturns program caller state one state (number left))
    (second : PureReturns program caller state two state (number right)) :
    PureReturns program caller state (a "+" [one, two]) state (number (left + right)) := by
  have supported : ownedHeads "+" = true := by decide
  apply native_binary_call_returns program caller state state state state "+"
    one two (number left) (number right) (number (left + right))
    (by decide) (by decide) _ _ first second _ (by decide)
  · rw [← agreement.demand "+" 0 supported]; decide +kernel
  · rw [← agreement.demand "+" 1 supported]; decide +kernel
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add] using
      StdLib.integer_addition state (left : Int) (right : Int)

theorem expand_branch_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request) (free : List (String × TypeExpr))
    (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase (frameCaller environment request task free) (taskValue task)
      taskCases = some (selected, body))
    (continued : PureReturns program selected state body state answer) :
    PureReturns program [] state
      (a "gslt:premise:query-expand-in" [environmentValue environment free, queryValue request, taskValue task])
      state answer := by
  let caller := callee .expand [environmentValue environment free, queryValue request, taskValue task]
  let envCaller := environmentCaller environment free caller
  let reqCaller := requestCaller request envCaller
  apply helper_call program agreement .expand [] state _ _ _ rfl (captured_closed _)
  rw [expand_shape]
  apply branch_returns program caller envCaller state _ (environmentValue environment free)
    environmentCases (environmentCases.head!).2 _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "environment"
  · simp [environment_cases_syntax, environmentValue, environmentTerm,
      providerTerm, envCaller, environmentCaller, caller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [environment_case_shape]
    apply branch_returns program envCaller reqCaller state _ (queryValue request) requestCases (requestCases.head!).2 _
    · simpa [envCaller, environmentCaller, caller, callee, Helper.names, applySubst, Subst.lookup] using
        variable_returns program envCaller state "request"
    · simp [request_cases_syntax, queryRequestTerm, contextTerm, reqCaller, requestCaller, contextCaller,
        envCaller, environmentCaller, caller, callee, Helper.names, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    · rw [request_case_shape]
      apply branch_returns program reqCaller selected state _ (taskValue task) taskCases body _
      · simpa [reqCaller, requestCaller, contextCaller, envCaller, environmentCaller, caller, callee,
          Helper.names, applySubst, Subst.lookup] using variable_returns program reqCaller state "task"
      · exact matched
      · exact continued

structure LowerOperations (program : Program) : Prop where
  row : ∀ (caller : Subst) (state : State) (index : Nat) (values : List Term) (one two : Atom),
    [one, two].map (applySubst caller) = [number index, encoded (encodeList id values)] →
    PureReturns program caller state (a "gslt:rule:row-at" [one, two]) state
      (encoded (encodeOption id values[index]?))
  length : ∀ (caller : Subst) (state : State) (values : List Term) (input : Atom),
    applySubst caller input = encoded (encodeList id values) →
    PureReturns program caller state (a "gslt:automata:length" [input]) state (number values.length)
  append : ∀ (caller : Subst) (state : State) (left right : List Term) (one two : Atom),
    [one, two].map (applySubst caller) = [encoded (encodeList id left), encoded (encodeList id right)] →
    PureReturns program caller state (a "gslt:automata:append" [one, two]) state (encoded (encodeList id (left ++ right)))
  signature : ∀ (caller : Subst) (state : State) (provider : ProviderSnapshot) (relation : String) (arity : Nat)
    (one two three : Atom),
    [one, two, three].map (applySubst caller) = [stringValue relation, number arity, encoded (providerTerm provider)] →
    PureReturns program caller state (a "gslt:premise:signature" [one, two, three]) state
      (encoded (encodeOption signatureTerm (signature? provider relation arity)))
  rowTyped : ∀ (caller : Subst) (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (signature : Signature) (row : ProviderRow) (one two three four five : Atom),
    [one, two, three, four, five].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm language.terms), encoded (DeclarationTyping.freeContextTerm free),
        boundValue bound, encoded (signatureTerm signature), encoded (providerRowTerm row)] →
    PureReturns program caller state (a "gslt:premise:check-row" [one, two, three, four, five]) state
      (Effects.boolean (checkRow language (FreeTypeContext.ofList free) bound signature row))
  assignment : ∀ (caller : Subst) (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (rule : RewriteRule) (spec : RuleBindingSpec) (assignment : Assignment)
    (one two three four five six : Atom),
    [one, two, three, four, five, six].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm language.terms), encoded (DeclarationTyping.freeContextTerm free),
        boundValue bound, ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), assignmentValue assignment] →
    PureReturns program caller state (a "gslt:premise:check-assignment" [one, two, three, four, five, six]) state
      (Effects.boolean (ConditionalEquationExecution.checkAssignment language (FreeTypeContext.ofList free) bound rule spec assignment))
  start : ∀ (caller : Subst) (state : State) (request : GeneralScopedMatchMachine.Request) (input : Atom),
    applySubst caller input = encoded (matcherRequestTerm request) →
    PureReturns program caller state (a "gslt:rule:scope-matcher-start" [input]) state
      (encoded (matcherStateTerm (GeneralScopedMatchMachine.start request)))
  tick : ∀ (caller : Subst) (state : State) (request : GeneralScopedMatchMachine.Request)
    (machine : GeneralScopedMatchMachine.State) (one two : Atom),
    [one, two].map (applySubst caller) = [encoded (matcherRequestTerm request), encoded (matcherStateTerm machine)] →
    PureReturns program caller state (a "gslt:rule:scope-matcher-tick" [one, two]) state
      (encoded (matcherStateTerm (GeneralScopedMatchMachine.tick request machine)))
  complete : ∀ (caller : Subst) (state : State) (machine : GeneralScopedMatchMachine.State) (input : Atom),
    applySubst caller input = encoded (matcherStateTerm machine) →
    PureReturns program caller state (a "gslt:rule:scope-matcher-complete" [input]) state
      (Effects.boolean (GeneralScopedMatchMachine.complete machine))
  instantiate : ∀ (caller : Subst) (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat) (assignment : Assignment)
    (pattern : Pattern) (one two three four five six seven eight nine : Atom),
    [one, two, three, four, five, six, seven, eight, nine].map (applySubst caller) =
      [.symbol "None", ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec),
        number ambient, encoded (InferenceCettaWire.AuthoredRule.siteTerm site), encoded (encodeList Term.natural path),
        number depth, assignmentValue assignment, patternValue pattern] →
    PureReturns program caller state (a "gslt:rule:scope-instantiate-at" [one, two, three, four, five, six, seven, eight, nine]) state
      (encoded (encodeOption InferenceCettaWire.encodePattern (instantiateAt? rule spec ambient site path depth assignment pattern)))


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

theorem length_encoded_returns {α : Type} (program : Program) (lower : LowerOperations program)
    (encoder : α → Term) (caller : Subst) (state : State) (values : List α) (input : String)
    (captured : applySubst caller (v input) = encoded (encodeList encoder values)) :
    PureReturns program caller state (a "gslt:automata:length" [v input]) state (number values.length) := by
  simpa only [List.length_map] using lower.length caller state (values.map encoder) (v input)
    (by simpa only [encodeList_map, Function.id_comp] using captured)

theorem append_encoded_returns {α : Type} (program : Program) (lower : LowerOperations program)
    (encoder : α → Term) (caller : Subst) (state : State) (left right : List α) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [encoded (encodeList encoder left), encoded (encodeList encoder right)]) :
    PureReturns program caller state (a "gslt:automata:append" [one, two]) state
      (encoded (encodeList encoder (left ++ right))) := by
  simpa only [← List.map_append, encodeList_map, Function.id_comp] using
    lower.append caller state (left.map encoder) (right.map encoder) one two
      (by simpa only [encodeList_map, Function.id_comp] using captured)

theorem row_encoded_returns {α : Type} (program : Program) (lower : LowerOperations program)
    (encoder : α → Term) (caller : Subst) (state : State) (index : Nat) (values : List α) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [number index, encoded (encodeList encoder values)]) :
    PureReturns program caller state (a "gslt:rule:row-at" [one, two]) state
      (encoded (encodeOption encoder values[index]?)) := by
  have returned := lower.row caller state index (values.map encoder) one two
    (by simpa only [encodeList_map, Function.id_comp] using captured)
  cases found : values[index]? <;> simpa [List.getElem?_map, found, encodeOption] using returned

local macro "query_template" "(" p:term ")" "(" g:term ")" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template $p $g _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue

theorem query_site_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) (state : State) (context : Context) (index : Nat) :
    PureReturns program [] state
      (a "gslt:premise:query-site" [contextValue context, number index]) state
      (encoded (InferenceCettaWire.AuthoredRule.siteTerm (context.site index))) := by
  let caller := callee .site [contextValue context, number index]
  let selected := contextCaller context caller
  apply helper_call program agreement .site [] state _ _ _ rfl (captured_closed _)
  rw [site_shape]
  apply branch_returns program caller selected state _ (contextValue context) siteCases
    (a "RulePremise" [v "premise", v "quantifiers", v "argument"]) _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "context"
  · simp [site_cases_syntax, querySiteCasesSyntax, contextTerm, selected, contextCaller, caller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · have templated : PureData.Template program (a "RulePremise" [v "premise", v "quantifiers", v "argument"]) := by
      query_template (program) (agreement)
    simpa [GeneralPremise.Context.site, InferenceCettaWire.AuthoredRule.siteTerm,
      selected, contextCaller, caller, callee, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
      CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      PureData.template_return program selected state _ templated

theorem query_site_captured_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) (caller : Subst) (state : State) (context : Context) (index : Nat)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [contextValue context, number index]) :
    PureReturns program caller state (a "gslt:premise:query-site" [one, two]) state
      (encoded (InferenceCettaWire.AuthoredRule.siteTerm (context.site index))) :=
  helper_capture program agreement .site caller state _ _ _ rfl captured (query_site_returns program agreement state context index)

private def matchingRequestData : Atom :=
  a "ScopedMatcherRequest" [v "rule", v "spec", v "ambient", v "site", .symbol "LNil", number 0,
    v "assignment", v "schema", v "value"]

private def matchingRequestBody : Atom :=
  a "let*" [.expression [.expression [v "ambient", a "gslt:automata:length" [v "bound"]],
    .expression [v "site", a "gslt:premise:query-site" [v "context", v "index"]]], matchingRequestData]

private theorem matching_request_case_body : (matchingRequestCases.head!).2 = matchingRequestBody := by decide +kernel

theorem query_matching_request_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program) (state : State) (request : Query.Request) (index : Nat)
    (assignment : Assignment) (schema value : Pattern) :
    PureReturns program [] state
      (a "gslt:premise:query-matching-request" [contextValue request.context, number index,
        assignmentValue assignment, patternValue schema, patternValue value]) state
      (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        (Query.matchingRequest request index assignment schema value))) := by
  let caller := callee .matchingRequest [contextValue request.context, number index,
    assignmentValue assignment, patternValue schema, patternValue value]
  let selected := contextCaller request.context caller
  let ambient := ("ambient", number request.context.bound.length) :: selected
  let final := ("site", encoded (InferenceCettaWire.AuthoredRule.siteTerm (request.context.site index))) :: ambient
  apply helper_call program agreement .matchingRequest [] state _ _ _ rfl (captured_closed _)
  rw [matching_request_shape]
  apply branch_returns program caller selected state _ (contextValue request.context) matchingRequestCases matchingRequestBody _
  · simpa [caller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "context"
  · simp [matching_cases_syntax, queryMatchingCasesSyntax, matchingRequestBody, matchingRequestData,
      contextTerm, selected, contextCaller, caller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · unfold matchingRequestBody
    apply PureData.let_bindings_return (pairs := [
      (v "ambient", a "gslt:automata:length" [v "bound"]),
      (v "site", a "gslt:premise:query-site" [v "context", v "index"])])
      (final := final) (middle := state) _ state matchingRequestData _ _
    · apply PureData.BindingsReturn.cons (bound := ambient) (middle := state)
        (value := number request.context.bound.length)
      · exact length_encoded_returns program lower InferenceCettaWire.AuthoredRule.typeTerm selected state request.context.bound "bound"
          (by simp [selected, contextCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
          ambient, selected, contextCaller, caller, callee, Helper.names, Subst.lookup]
      · apply PureData.BindingsReturn.cons (bound := final) (middle := state)
          (value := encoded (InferenceCettaWire.AuthoredRule.siteTerm (request.context.site index)))
        · exact query_site_captured_returns program agreement ambient state request.context index (v "context") (v "index")
            (by simp [ambient, selected, contextCaller, caller, callee, Helper.names, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
            final, ambient, selected, contextCaller, caller, callee, Helper.names, Subst.lookup]
        · exact .nil final state
    · have templated : PureData.Template program matchingRequestData := by unfold matchingRequestData; query_template (program) (agreement)
      simpa [matchingRequestData, Query.matchingRequest,
        RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
        final, ambient, selected, contextCaller, caller, callee, Helper.names,
        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return program final state _ templated

theorem query_matching_request_captured_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program) (caller : Subst) (state : State)
    (request : Query.Request) (index : Nat) (assignment : Assignment) (schema value : Pattern)
    (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [contextValue request.context, number index, assignmentValue assignment, patternValue schema, patternValue value]) :
    PureReturns program caller state (a "gslt:premise:query-matching-request" [one, two, three, four, five]) state
      (encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm
        (Query.matchingRequest request index assignment schema value))) :=
  helper_capture program agreement .matchingRequest caller state _ _ _ rfl captured
    (query_matching_request_returns program agreement lower state request index assignment schema value)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom)

theorem symbol_constructor_mismatch (caller : Subst) (symbol head : String) (values : List Atom) :
    SpaceSemantics.matchValue caller (.symbol symbol) (a head values) = none := by
  simp [a, SpaceSemantics.matchValue, matchAtom]

theorem constructor_head_mismatch (caller : Subst) (left right : String) (patterns values : List Atom)
    (ordinary : left ≠ "cons") (different : left ≠ right) :
    SpaceSemantics.matchValue caller (a left patterns) (a right values) = none := by
  rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by
    intro first rest equal
    exact ordinary (Atom.symbol.inj (List.cons.inj equal).1))]
  rw [SpaceSemantics.matchValue.matchValues]
  simp only [SpaceSemantics.matchValue, matchAtom, beq_iff_eq,
    if_neg different, Option.bind_eq_bind]
  rfl

theorem select_skip_constructor (caller : Subst) (left right : String) (patterns values : List Atom)
    (body : Atom) (rest : SpaceSemantics.Cases) (ordinary : left ≠ "cons") (different : left ≠ right) :
    SpaceSemantics.selectCase caller (a right values) ((a left patterns, body) :: rest) =
      SpaceSemantics.selectCase caller (a right values) rest := by
  rw [SpaceSemantics.selectCase, constructor_head_mismatch caller left right patterns values ordinary different]


theorem constructor_variables_match (caller : Subst) (head : String) (names : List String) (values : List Atom)
    (ordinary : head ≠ "cons") (distinct : names.Nodup) (length : values.length = names.length)
    (fresh : ∀ name ∈ names, Subst.lookup caller name = none) :
    SpaceSemantics.matchValue caller (a head (names.map v)) (a head values) =
      some ((names.zip values).reverse ++ caller) := by
  rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by
    intro first rest equal
    exact ordinary (Atom.symbol.inj (List.cons.inj equal).1))]
  simp only [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue, matchAtom,
    beq_self_eq_true, Option.bind_eq_bind]
  exact PureData.match_variable_values names values caller distinct length fresh


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

local macro "query_template" "(" p:term ")" "(" g:term ")" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template $p $g _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue queryValue taskValue

private def startUnavailableData : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
    a "LCons" [a "PremiseSignatureUnavailable" [v "relation", v "arity"], .symbol "LNil"]]]

private def startRowsData : Atom :=
  a "Some" [a "PremiseExpansion" [a "LCons" [a "PremiseQueryRows" [v "signature", number 0], .symbol "LNil"],
    .symbol "LNil", .symbol "LNil"]]

private def startSignatureCases : SpaceSemantics.Cases :=
  [(.symbol "None", startUnavailableData), (a "Some" [v "signature"], startRowsData), (v "badSignature", .symbol "None")]

private def startSignatureBody : Atom :=
  caseData (a "gslt:premise:signature" [v "relation", v "arity", a "PremiseProvider" [v "signatures", v "rows"]]) startSignatureCases

private def startBody : Atom :=
  a "let" [v "arity", a "gslt:automata:length" [v "arguments"], startSignatureBody]

private theorem start_shape : taskBody 0 = startBody := by decide +kernel

theorem query_expand_start_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program) (state : State) (environment : Environment) (request : Query.Request)
    (free : List (String × TypeExpr))
    (unregistered : request.relation ∉ environment.provider.dynamicRelations) :
    PureReturns program [] state
      (a "gslt:premise:query-expand-in" [environmentValue environment free, queryValue request,
        taskValue (Query.Task.start (environment := environment) (request := request))]) state
      (expansionValue (Query.expand environment request .start)) := by
  let caller := frameCaller environment request .start free
  let counted := ("arity", number request.arguments.length) :: caller
  apply expand_branch_returns program agreement state environment request .start free caller startBody _
  · simp [task_cases_syntax, start_shape,
      startBody, startSignatureBody, startSignatureCases, startUnavailableData, startRowsData,
      queryTaskTerm, caller, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, CettaWireAtom.encode]
  · unfold startBody
    apply named_let_returns program caller state "arity" _ (number request.arguments.length) startSignatureBody _
    · simp [caller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
    · exact length_encoded_returns program lower InferenceCettaWire.encodePattern caller state request.arguments "arguments"
        (by simp [caller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
          InferenceCettaWire.encodePatterns_eq_encodeList, applySubst, Subst.lookup])
    · have queried := lower.signature counted state environment.provider request.relation request.arguments.length
        (v "relation") (v "arity") (a "PremiseProvider" [v "signatures", v "rows"])
        (by
          simp [counted, caller, frameCaller, requestCaller, contextCaller, environmentCaller,
            callee, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, providerTerm])
      change PureReturns _ counted state
        (a "gslt:premise:signature" [v "relation", v "arity", a "PremiseProvider" [v "signatures", v "rows"]]) state
        (encoded (encodeOption signatureTerm (signature? environment.provider request.relation request.arguments.length))) at queried
      have computed := queried
      cases found : signature? environment.provider request.relation request.arguments.length with
      | none =>
          have original : Query.expand (matcher := GeneralPremise.MatchingExecution.ordinary) environment request .start =
              { unresolved := [.signatureUnavailable request.relation request.arguments.length] } := by
            simp only [Query.expand]
            split <;> simp_all
          rw [original]
          unfold startSignatureBody
          apply branch_returns program counted counted state _ (.symbol "None") startSignatureCases startUnavailableData _
          · simpa [found, encodeOption, CettaWireAtom.encode] using computed
          · simp [startSignatureCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
          · have templated : PureData.Template program startUnavailableData := by unfold startUnavailableData; query_template (program) (agreement)
            simpa [expansionValue, queryExpansionTerm,
              PremiseSchedulerExecution.schedulerExpansionTerm, queryObligationTerm, encodeOption,
              encodeList, startUnavailableData, counted, caller, frameCaller, requestCaller, contextCaller,
              environmentCaller, callee, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return program counted state _ templated
      | some signature =>
          have original : Query.expand (matcher := GeneralPremise.MatchingExecution.ordinary) environment request .start =
              { tasks := [.rows ⟨signature, found, 0⟩] } := by
            simp only [Query.expand]
            split
            · rename_i impossible
              rw [found] at impossible
              cases impossible
            · rename_i actual selected
              have same : actual = signature := Option.some.inj (selected.symm.trans found)
              subst actual
              simp only [dif_neg unregistered]
          rw [original]
          let selected := ("signature", encoded (signatureTerm signature)) :: counted
          unfold startSignatureBody
          apply branch_returns program counted selected state _ (encoded (encodeOption signatureTerm (some signature))) startSignatureCases startRowsData _
          · simpa only [found] using computed
          · simp [startSignatureCases, selected, counted, caller, frameCaller, requestCaller, contextCaller,
              environmentCaller, callee, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
          · have templated : PureData.Template program startRowsData := by unfold startRowsData; query_template (program) (agreement)
            simpa [expansionValue, queryExpansionTerm,
              PremiseSchedulerExecution.schedulerExpansionTerm, queryTaskTerm, encodeOption,
              encodeList, startRowsData, selected, counted, caller, frameCaller, requestCaller, contextCaller,
              environmentCaller, callee, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return program selected state _ templated


theorem successor_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "+" [v name, number 1]) state (number (value + 1)) := by
  apply add_returns program agreement caller state value 1 (v name) (number 1)
  · simpa only [captured] using variable_returns program caller state name
  · exact grounded_returns program caller state (.int 1)

private def rowsEmptyData : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]

private def rowsTailData : Atom :=
  a "PremiseQueryRows" [v "signature", v "next"]

private def rowsAcceptedData : Atom :=
  a "Some" [a "PremiseExpansion" [
    a "LCons" [a "PremiseQueryArguments" [v "cursor", number 0, v "initial", v "arguments", v "values", v "modes", .symbol "LNil"],
      a "LCons" [rowsTailData, .symbol "LNil"]], .symbol "LNil", .symbol "LNil"]]

private def rowsRejectedData : Atom :=
  a "Some" [a "PremiseExpansion" [a "LCons" [rowsTailData, .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def rowsCheckedBody : Atom := a "if" [v "checked", rowsAcceptedData, rowsRejectedData]

private def rowsConsBody : Atom :=
  a "let*" [.expression [.expression [v "next", a "+" [v "cursor", number 1]],
    .expression [v "checked", a "gslt:premise:check-row" [v "declarations", v "free", v "bound", v "signature",
      a "PremiseProviderRow" [v "rowRelation", v "values"]]]], rowsCheckedBody]

private def rowsSignatureCases : SpaceSemantics.Cases :=
  [(a "PremiseSignature" [v "signatureRelation", v "types", v "modes"], rowsConsBody),
    (v "badSignature", .symbol "None")]

private def rowsSignatureBody : Atom := caseData (v "signature") rowsSignatureCases

private def rowsCases : SpaceSemantics.Cases :=
  [(.symbol "None", rowsEmptyData),
    (a "Some" [a "PremiseProviderRow" [v "rowRelation", v "values"]], rowsSignatureBody),
    (v "badRow", .symbol "None")]

private def rowsBody : Atom := caseData (a "gslt:rule:row-at" [v "cursor", v "rows"]) rowsCases

private theorem rows_shape : taskBody 1 = rowsBody := by decide +kernel

def rowsCaller (environment : Environment) (request : Query.Request)
    (frame : Query.RowsFrame environment request) (free : List (String × TypeExpr)) : Subst :=
  [("cursor", number frame.cursor), ("signature", encoded (signatureTerm frame.signature))] ++
    frameCaller environment request (.rows frame) free

private def rowFoundCaller (row : ProviderRow) (caller : Subst) : Subst :=
  [("values", patternsValue row.values), ("rowRelation", stringValue row.relation)] ++ caller

private def rowSignatureCaller (signature : Signature) (caller : Subst) : Subst :=
  [("modes", encoded (encodeList modeTerm signature.modes)),
    ("types", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm signature.argumentTypes)),
    ("signatureRelation", stringValue signature.relation)] ++ caller

private def rowsAcceptedValue (environment : Environment) (request : Query.Request)
    (frame : Query.RowsFrame environment request) (row : ProviderRow) : Atom :=
  encoded (.application "Some" [.application "PremiseExpansion" [
    .application "LCons" [.application "PremiseQueryArguments" [.natural frame.cursor, .natural 0,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm request.initial,
      InferenceCettaWire.encodePatterns request.arguments, InferenceCettaWire.encodePatterns row.values,
      encodeList modeTerm frame.signature.modes, .symbol "LNil"],
      .application "LCons" [.application "PremiseQueryRows" [signatureTerm frame.signature, .natural (frame.cursor + 1)], .symbol "LNil"]],
    .symbol "LNil", .symbol "LNil"]])

private def rowsRejectedValue (environment : Environment) (request : Query.Request)
    (frame : Query.RowsFrame environment request) : Atom :=
  encoded (.application "Some" [.application "PremiseExpansion" [
    .application "LCons" [.application "PremiseQueryRows" [signatureTerm frame.signature, .natural (frame.cursor + 1)], .symbol "LNil"],
    .symbol "LNil", .symbol "LNil"]])

private theorem rowsExpansion_none (environment : Environment) (request : Query.Request)
    (frame : Query.RowsFrame environment request) (missing : environment.provider.rows[frame.cursor]? = none) :
    expansionValue (Query.expand environment request (.rows frame)) =
      encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]) := by
  simp only [Query.expand]
  split
  · rfl
  · rename_i row found
    simp [missing] at found

private theorem rowsExpansion_some (environment : Environment) (request : Query.Request)
    (frame : Query.RowsFrame environment request) (row : ProviderRow)
    (found : environment.provider.rows[frame.cursor]? = some row) :
    expansionValue (Query.expand environment request (.rows frame)) =
      if checkRow environment.language environment.free request.context.bound frame.signature row then
        rowsAcceptedValue environment request frame row else rowsRejectedValue environment request frame := by
  simp only [Query.expand]
  split
  · rename_i missing
    simp [found] at missing
  · rename_i selected selectedFound
    have same : selected = row := Option.some.inj (selectedFound.symm.trans found)
    subst selected
    split <;> rename_i checked <;>
      simp [expansionValue, queryExpansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm,
        queryTaskTerm, originsTerm, encodeOption, encodeList, rowsAcceptedValue, rowsRejectedValue,
        CettaWireAtom.encode, CettaWireAtom.encodeMany]

theorem query_expand_rows_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program) (state : State) (environment : Environment) (request : Query.Request)
    (frame : Query.RowsFrame environment request) (footprint : List String)
    (covers : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint) :
    PureReturns program [] state
      (a "gslt:premise:query-expand-in" [environmentValue environment (environment.free.entriesOn footprint), queryValue request,
        taskValue (.rows frame)]) state (expansionValue (Query.expand environment request (.rows frame))) := by
  let free := environment.free.entriesOn footprint
  let caller := rowsCaller environment request frame free
  apply expand_branch_returns program agreement state environment request (.rows frame) free caller rowsBody _
  · simp [task_cases_syntax, rows_shape, queryTaskTerm, caller, rowsCaller, frameCaller, requestCaller, contextCaller,
      environmentCaller, callee, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · have lookup := row_encoded_returns program lower providerRowTerm caller state frame.cursor environment.provider.rows (v "cursor") (v "rows")
      (by simp [caller, rowsCaller, frameCaller, requestCaller, contextCaller, environmentCaller,
        callee, Helper.names, applySubst, Subst.lookup])
    cases found : environment.provider.rows[frame.cursor]? with
    | none =>
        rw [rowsExpansion_none environment request frame found]
        unfold rowsBody
        apply branch_returns program caller caller state _ (.symbol "None") rowsCases rowsEmptyData _
        · simpa [found, encodeOption, CettaWireAtom.encode] using lookup
        · simp [rowsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · have templated : PureData.Template program rowsEmptyData := by unfold rowsEmptyData; query_template (program) (agreement)
          exact PureData.template_return program caller state _ templated
    | some row =>
        rw [rowsExpansion_some environment request frame row found]
        let selected := rowFoundCaller row caller
        let typed := rowSignatureCaller frame.signature selected
        let next := ("next", number (frame.cursor + 1)) :: typed
        let final := ("checked", Effects.boolean (checkRow environment.language environment.free request.context.bound frame.signature row)) :: next
        unfold rowsBody
        apply branch_returns program caller selected state _ (encoded (encodeOption providerRowTerm (some row))) rowsCases rowsSignatureBody _
        · simpa only [found] using lookup
        · simp [rowsCases, selected, rowFoundCaller, caller, rowsCaller, frameCaller, requestCaller, contextCaller,
            environmentCaller, callee, Helper.names, providerRowTerm, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
        · unfold rowsSignatureBody
          apply branch_returns program selected typed state _ (encoded (signatureTerm frame.signature)) rowsSignatureCases rowsConsBody _
          · simpa [selected, rowFoundCaller, caller, rowsCaller, frameCaller, requestCaller, contextCaller,
              environmentCaller, callee, Helper.names, applySubst, Subst.lookup] using
              variable_returns program selected state "signature"
          · simp [rowsSignatureCases, typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
              requestCaller, contextCaller, environmentCaller, callee, Helper.names, signatureTerm,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
          · unfold rowsConsBody
            apply PureData.let_bindings_return (pairs := [
              (v "next", a "+" [v "cursor", number 1]),
              (v "checked", a "gslt:premise:check-row" [v "declarations", v "free", v "bound", v "signature",
                a "PremiseProviderRow" [v "rowRelation", v "values"]])])
              (final := final) (middle := state) _ state rowsCheckedBody _ _
            · apply PureData.BindingsReturn.cons (bound := next) (middle := state) (value := number (frame.cursor + 1))
              · exact successor_returns program agreement typed state frame.cursor "cursor" (by
                  simp [typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
                    requestCaller, contextCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                  next, typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
                  requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
              · apply PureData.BindingsReturn.cons (bound := final) (middle := state)
                  (value := Effects.boolean (checkRow environment.language environment.free request.context.bound frame.signature row))
                · have checked := lower.rowTyped next state environment.language free request.context.bound
                    frame.signature row (v "declarations") (v "free") (v "bound") (v "signature")
                    (a "PremiseProviderRow" [v "rowRelation", v "values"]) (by
                      change [v "declarations", v "free", v "bound", v "signature", a "PremiseProviderRow" [v "rowRelation", v "values"]].map (applySubst next) =
                        [encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm environment.language.terms),
                          encoded (DeclarationTyping.freeContextTerm free), boundValue request.context.bound,
                          encoded (signatureTerm frame.signature), encoded (providerRowTerm row)]
                      simp [next, typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
                        requestCaller, contextCaller, environmentCaller, callee, Helper.names, providerRowTerm,
                        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany])
                  simpa only [free, check_row_snapshot environment.language environment.free request.context.bound
                    environment.provider frame.signature row (List.mem_of_getElem? found) footprint covers] using checked
                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
                    final, next, typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
                    requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
                · exact .nil final state
            · unfold rowsCheckedBody
              apply bool_if_returns program final state (v "checked")
                (checkRow environment.language environment.free request.context.bound frame.signature row)
                rowsAcceptedData rowsRejectedData _
              · simpa [final, applySubst, Subst.lookup] using variable_returns program final state "checked"
              · cases checked : checkRow environment.language environment.free request.context.bound frame.signature row with
                | false =>
                    have templated : PureData.Template program rowsRejectedData := by unfold rowsRejectedData rowsTailData; query_template (program) (agreement)
                    simpa [checked, rowsRejectedData, rowsTailData, rowsRejectedValue,
                      final, next, typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
                      requestCaller, contextCaller, environmentCaller, callee, Helper.names,
                      applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                      PureData.template_return program final state _ templated
                | true =>
                    have templated : PureData.Template program rowsAcceptedData := by unfold rowsAcceptedData rowsTailData; query_template (program) (agreement)
                    simpa [checked, rowsAcceptedData, rowsTailData, rowsAcceptedValue,
                      final, next, typed, rowSignatureCaller, selected, rowFoundCaller, caller, rowsCaller, frameCaller,
                      requestCaller, contextCaller, environmentCaller, callee, Helper.names,
                      applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                      PureData.template_return program final state _ templated


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue queryValue taskValue

local macro "query_template" "(" p:term ")" "(" g:term ")" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template $p $g _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

private def outputData : Atom :=
  a "Some" [a "PremiseExpansion" [a "LCons" [
    a "PremiseQueryMatcher" [v "rowIndex", v "index", v "schemas", v "values", v "modes", v "origins", v "query", v "started", number 0],
    .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def outputContextData : Atom :=
  a "PremiseContext" [v "ruleIndex", v "rule", v "spec", v "bound", v "premise", v "quantifiers"]

private def outputBody : Atom :=
  a "let*" [.expression [
    .expression [v "query", a "gslt:premise:query-matching-request"
      [outputContextData, v "index", v "assignment", v "schema", v "value"]],
    .expression [v "started", a "gslt:rule:scope-matcher-start" [v "query"]]], outputData]

private theorem output_shape : taskBody 4 = outputBody := by decide +kernel

def argumentsConsCaller (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (free : List (String × TypeExpr))
    (schema : Pattern) (schemas : List Pattern) (value : Pattern) (values : List Pattern)
    (modes : List RelationArgMode) : Subst :=
  [("origins", encoded (originsTerm frame.origins)), ("modes", encoded (encodeList modeTerm modes)),
    ("values", patternsValue values), ("value", patternValue value), ("schemas", patternsValue schemas),
    ("schema", patternValue schema), ("assignment", assignmentValue frame.assignment),
    ("index", number frame.index), ("rowIndex", number frame.rowIndex)] ++
    frameCaller environment request (.arguments frame) free

private def outputValue (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (schema : Pattern) (schemas : List Pattern)
    (value : Pattern) (values : List Pattern) (modes : List RelationArgMode) : Atom :=
  let query := Query.matchingRequest request frame.index frame.assignment schema value
  encoded (.application "Some" [.application "PremiseExpansion" [.application "LCons" [
    .application "PremiseQueryMatcher" [.natural frame.rowIndex, .natural frame.index,
      InferenceCettaWire.encodePatterns schemas, InferenceCettaWire.encodePatterns values,
      encodeList modeTerm modes, originsTerm frame.origins, matcherRequestTerm query,
      matcherStateTerm (GeneralScopedMatchMachine.start query), .natural 0], .symbol "LNil"],
    .symbol "LNil", .symbol "LNil"]])

private theorem output_expansion (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (schema : Pattern) (schemas : List Pattern)
    (value : Pattern) (values : List Pattern) (modes : List RelationArgMode)
    (schemasFound : frame.schemas = schema :: schemas) (valuesFound : frame.values = value :: values)
    (modesFound : frame.modes = .output :: modes) :
    expansionValue (Query.expand environment request (.arguments frame)) =
      outputValue environment request frame schema schemas value values modes := by
  rcases frame with ⟨rowIndex, index, assignment, schemas', values', modes', origins, finish⟩
  change schemas' = _ at schemasFound
  change values' = _ at valuesFound
  change modes' = _ at modesFound
  subst schemas'
  subst values'
  subst modes'
  rfl

theorem query_expand_arguments_output_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program)
    (state : State) (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (free : List (String × TypeExpr))
    (schema : Pattern) (schemas : List Pattern) (value : Pattern) (values : List Pattern)
    (modes : List RelationArgMode)
    (schemasFound : frame.schemas = schema :: schemas) (valuesFound : frame.values = value :: values)
    (modesFound : frame.modes = .output :: modes) :
    PureReturns program [] state (a "gslt:premise:query-expand-in"
      [environmentValue environment free, queryValue request, taskValue (.arguments frame)]) state
      (expansionValue (Query.expand environment request (.arguments frame))) := by
  let query := Query.matchingRequest request frame.index frame.assignment schema value
  let caller := argumentsConsCaller environment request frame free schema schemas value values modes
  let matched := ("query", encoded (matcherRequestTerm query)) :: caller
  let started := ("started", encoded (matcherStateTerm (GeneralScopedMatchMachine.start query))) :: matched
  rw [output_expansion environment request frame schema schemas value values modes schemasFound valuesFound modesFound]
  apply expand_branch_returns program agreement state environment request (.arguments frame) free caller outputBody _
  · simp [task_cases_syntax, output_shape, query_arguments_wire, schemasFound, valuesFound, modesFound,
      modeTerm, InferenceCettaWire.encodePatterns, encodeList, caller, argumentsConsCaller,
      frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · unfold outputBody
    apply PureData.let_bindings_return (pairs := [
      (v "query", a "gslt:premise:query-matching-request" [outputContextData, v "index", v "assignment", v "schema", v "value"]),
      (v "started", a "gslt:rule:scope-matcher-start" [v "query"])])
      (final := started) (middle := state) _ state outputData _ _
    · apply PureData.BindingsReturn.cons (bound := matched) (middle := state) (value := encoded (matcherRequestTerm query))
      · exact query_matching_request_captured_returns program agreement lower caller state request frame.index frame.assignment schema value
          outputContextData (v "index") (v "assignment") (v "schema") (v "value") (by
            simp [outputContextData, contextTerm, caller, argumentsConsCaller, frameCaller, requestCaller,
              contextCaller, environmentCaller, callee, Helper.names, applySubst, applySubst.applySubstList,
              Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany])
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, matched, caller,
          argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
      · apply PureData.BindingsReturn.cons (bound := started) (middle := state)
          (value := encoded (matcherStateTerm (GeneralScopedMatchMachine.start query)))
        · exact lower.start matched state query (v "query") (by simp [matched, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, started, matched, caller,
            argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
        · exact .nil _ _
    · have templated : PureData.Template program outputData := by unfold outputData; query_template (program) (agreement)
      simpa [outputData, outputValue, query, started, matched, caller, argumentsConsCaller, frameCaller,
        requestCaller, contextCaller, environmentCaller, callee, Helper.names, applySubst, applySubst.applySubstList,
        Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return program started state _ templated


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue queryValue taskValue

local macro "query_template" "(" p:term ")" "(" g:term ")" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template $p $g _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

private def inputEmptyData : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]

private def unavailableData : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
    a "LCons" [a "PremiseInputUnavailable" [v "rowIndex", v "index"], .symbol "LNil"]]]

private def acceptedData : Atom :=
  a "Some" [a "PremiseExpansion" [a "LCons" [
    a "PremiseQueryArguments" [v "rowIndex", v "next", v "assignment", v "schemas", v "values", v "modes", v "extended"],
    .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def advanceBody : Atom :=
  a "let*" [.expression [
    .expression [v "next", a "+" [v "index", number 1]],
    .expression [v "extended", a "gslt:automata:append" [v "origins",
      a "LCons" [a "ArgumentOrigin" [v "index", .symbol "LNil"], .symbol "LNil"]]]], acceptedData]

private def actualBody : Atom := a "if" [a "==" [v "actual", v "value"], advanceBody, inputEmptyData]

private def instantiateCases : SpaceSemantics.Cases :=
  [(.symbol "None", unavailableData), (a "Some" [v "actual"], actualBody), (v "badInstantiation", .symbol "None")]

private def instantiateBody : Atom :=
  caseData (a "gslt:rule:scope-instantiate-at" [.symbol "None", v "rule", v "spec", v "ambient", v "site",
    .symbol "LNil", number 0, v "assignment", v "schema"]) instantiateCases

private def inputSiteData : Atom := a "RulePremise" [v "premise", v "quantifiers", v "index"]

private def inputBody : Atom :=
  a "let*" [.expression [
    .expression [v "ambient", a "gslt:automata:length" [v "bound"]],
    .expression [v "site", inputSiteData]], instantiateBody]

private theorem input_shape : taskBody 3 = inputBody := by decide +kernel

private def acceptedValue (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (schemas values : List Pattern) (modes : List RelationArgMode) : Atom :=
  encoded (.application "Some" [.application "PremiseExpansion" [.application "LCons" [
    .application "PremiseQueryArguments" [.natural frame.rowIndex, .natural (frame.index + 1),
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.assignment,
      InferenceCettaWire.encodePatterns schemas, InferenceCettaWire.encodePatterns values,
      encodeList modeTerm modes, originsTerm (frame.origins ++ [(frame.index, [])])], .symbol "LNil"],
    .symbol "LNil", .symbol "LNil"]])

private def inputValue (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (schema : Pattern) (schemas : List Pattern)
    (value : Pattern) (values : List Pattern) (modes : List RelationArgMode) : Atom :=
  match instantiateAt? request.context.rule request.context.spec request.context.bound.length
      (request.context.site frame.index) [] 0 frame.assignment schema with
  | none => encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
      .application "LCons" [.application "PremiseInputUnavailable" [.natural frame.rowIndex, .natural frame.index], .symbol "LNil"]]])
  | some actual => if actual == value then acceptedValue environment request frame schemas values modes else
      encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]])

private theorem input_expansion (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (schema : Pattern) (schemas : List Pattern)
    (value : Pattern) (values : List Pattern) (modes : List RelationArgMode)
    (schemasFound : frame.schemas = schema :: schemas) (valuesFound : frame.values = value :: values)
    (modesFound : frame.modes = .input :: modes) :
    expansionValue (Query.expand environment request (.arguments frame)) =
      inputValue environment request frame schema schemas value values modes := by
  rcases frame with ⟨rowIndex, index, assignment, schemas', values', modes', origins, finish⟩
  change schemas' = _ at schemasFound
  change values' = _ at valuesFound
  change modes' = _ at modesFound
  subst schemas'
  subst values'
  subst modes'
  dsimp only [Query.expand, Query.expandArguments]
  split
  · rename_i found
    simp only [inputValue, found]
    rfl
  · rename_i actual found
    simp only [inputValue, found]
    split
    · rename_i same
      have literal : actual = value := by
        apply beq_iff_eq.mp
        change (actual == value) = true at same
        exact same
      subst actual
      simp [expansionValue, queryExpansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm,
        acceptedValue, query_arguments_wire, encodeOption, encodeList]
    · rename_i different
      have literal : actual ≠ value := by
        intro equal
        apply different
        change (actual == value) = true
        exact beq_iff_eq.mpr equal
      simp [literal, expansionValue, queryExpansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm,
        encodeOption, encodeList]

theorem query_expand_arguments_input_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program)
    (state : State) (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (free : List (String × TypeExpr))
    (schema : Pattern) (schemas : List Pattern) (value : Pattern) (values : List Pattern)
    (modes : List RelationArgMode)
    (schemasFound : frame.schemas = schema :: schemas) (valuesFound : frame.values = value :: values)
    (modesFound : frame.modes = .input :: modes) :
    PureReturns program [] state (a "gslt:premise:query-expand-in"
      [environmentValue environment free, queryValue request, taskValue (.arguments frame)]) state
      (expansionValue (Query.expand environment request (.arguments frame))) := by
  let caller := argumentsConsCaller environment request frame free schema schemas value values modes
  let ambient := ("ambient", number request.context.bound.length) :: caller
  let site := ("site", encoded (InferenceCettaWire.AuthoredRule.siteTerm (request.context.site frame.index))) :: ambient
  rw [input_expansion environment request frame schema schemas value values modes schemasFound valuesFound modesFound]
  apply expand_branch_returns program agreement state environment request (.arguments frame) free caller inputBody _
  · simp [task_cases_syntax, input_shape, query_arguments_wire, schemasFound, valuesFound, modesFound,
      modeTerm, InferenceCettaWire.encodePatterns, encodeList, caller, argumentsConsCaller,
      frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · unfold inputBody
    apply PureData.let_bindings_return (pairs := [
      (v "ambient", a "gslt:automata:length" [v "bound"]), (v "site", inputSiteData)])
      (final := site) (middle := state) _ state instantiateBody _ _
    · apply PureData.BindingsReturn.cons (bound := ambient) (middle := state) (value := number request.context.bound.length)
      · exact length_encoded_returns program lower InferenceCettaWire.AuthoredRule.typeTerm caller state request.context.bound "bound"
          (by simp [caller, argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
            applySubst, Subst.lookup])
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, ambient, caller,
          argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
      · apply PureData.BindingsReturn.cons (bound := site) (middle := state)
          (value := encoded (InferenceCettaWire.AuthoredRule.siteTerm (request.context.site frame.index)))
        · have templated : PureData.Template program inputSiteData := by unfold inputSiteData; query_template (program) (agreement)
          simpa [inputSiteData, GeneralPremise.Context.site, InferenceCettaWire.AuthoredRule.siteTerm,
            ambient, caller, argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
            applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program ambient state _ templated
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, site, ambient, caller,
            argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
        · exact .nil _ _
    · have instantiated := lower.instantiate site state request.context.rule request.context.spec request.context.bound.length
        (request.context.site frame.index) [] 0 frame.assignment schema
        (.symbol "None") (v "rule") (v "spec") (v "ambient") (v "site") (.symbol "LNil") (number 0) (v "assignment") (v "schema") (by
          simp [site, ambient, caller, argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller,
            callee, Helper.names, applySubst, Subst.lookup, encodeList, CettaWireAtom.encode])
      unfold instantiateBody
      cases found : instantiateAt? request.context.rule request.context.spec request.context.bound.length
          (request.context.site frame.index) [] 0 frame.assignment schema with
      | none =>
          apply branch_returns program site site state _ (.symbol "None") instantiateCases unavailableData _
          · simpa [found, encodeOption, CettaWireAtom.encode] using instantiated
          · simp [instantiateCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
          · have templated : PureData.Template program unavailableData := by unfold unavailableData; query_template (program) (agreement)
            simpa [inputValue, found, unavailableData, site, ambient, caller, argumentsConsCaller,
              frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
              applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return program site state _ templated
      | some actual =>
          let selected := ("actual", patternValue actual) :: site
          apply branch_returns program site selected state _ (encoded (encodeOption InferenceCettaWire.encodePattern (some actual)))
            instantiateCases actualBody _
          · simpa only [found] using instantiated
          · simp [instantiateCases, selected, site, ambient, caller, argumentsConsCaller, frameCaller,
              requestCaller, contextCaller, environmentCaller, callee, Helper.names, encodeOption,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
          · have compared := CettaWireAtom.equality_captured_returns program selected state
              (InferenceCettaWire.encodePattern actual) (InferenceCettaWire.encodePattern value) "actual" "value"
              (by simp [selected, applySubst, Subst.lookup])
              (by simp [selected, site, ambient, caller, argumentsConsCaller, frameCaller, requestCaller, contextCaller,
                environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
            have tested : PureReturns program selected state (a "==" [v "actual", v "value"]) state
                (Effects.boolean (actual == value)) := by
              simpa only [InferenceCettaWire.encodePattern_injective.eq_iff, beq_eq_decide] using compared
            unfold actualBody
            apply bool_if_returns program selected state _ (actual == value) advanceBody inputEmptyData _ tested
            cases checked : actual == value with
            | false =>
                have templated : PureData.Template program inputEmptyData := by unfold inputEmptyData; query_template (program) (agreement)
                simpa [inputValue, found, checked, inputEmptyData, applySubst, applySubst.applySubstList,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany] using PureData.template_return program selected state _ templated
            | true =>
                let next := ("next", number (frame.index + 1)) :: selected
                let extended := ("extended", encoded (originsTerm (frame.origins ++ [(frame.index, [])]))) :: next
                simp only [↓reduceIte]
                unfold advanceBody
                apply PureData.let_bindings_return (pairs := [
                  (v "next", a "+" [v "index", number 1]),
                  (v "extended", a "gslt:automata:append" [v "origins", a "LCons" [a "ArgumentOrigin" [v "index", .symbol "LNil"], .symbol "LNil"]])])
                  (final := extended) (middle := state) _ state acceptedData _ _
                · apply PureData.BindingsReturn.cons (bound := next) (middle := state) (value := number (frame.index + 1))
                  · apply add_returns program agreement selected state frame.index 1 (v "index") (number 1)
                    · simpa [selected, site, ambient, caller, argumentsConsCaller, frameCaller, requestCaller, contextCaller,
                        environmentCaller, callee, Helper.names, applySubst, Subst.lookup] using variable_returns program selected state "index"
                    · exact grounded_returns program selected state (.int 1)
                  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, next, selected, site, ambient, caller,
                      argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
                  · apply PureData.BindingsReturn.cons (bound := extended) (middle := state)
                      (value := encoded (originsTerm (frame.origins ++ [(frame.index, [])])))
                    · exact append_encoded_returns program lower
                        (fun origin : Nat × List GeneralScopedMatchMachine.BagChoice => .application "ArgumentOrigin" [.natural origin.1, traceTerm origin.2])
                        next state frame.origins [(frame.index, [])] (v "origins")
                        (a "LCons" [a "ArgumentOrigin" [v "index", .symbol "LNil"], .symbol "LNil"]) (by
                          simp [originsTerm, traceTerm, RuleInstantiationExecution.GeneralExecution.traceTerm,
                            next, selected, site, ambient, caller, argumentsConsCaller, frameCaller, requestCaller, contextCaller,
                            environmentCaller, callee, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
                            encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany])
                    · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, extended, next, selected, site, ambient, caller,
                        argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
                    · exact .nil _ _
                · have templated : PureData.Template program acceptedData := by unfold acceptedData; query_template (program) (agreement)
                  simpa [inputValue, found, checked, acceptedValue, acceptedData, extended, next, selected, site, ambient, caller,
                    argumentsConsCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
                    applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                    PureData.template_return program extended state _ templated


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue queryValue taskValue

local macro "query_template" "(" p:term ")" "(" g:term ")" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template $p $g _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

private def argumentsEmptyData : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]

private def argumentsAcceptedData : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil",
    a "LCons" [a "PremiseQueryAnswer" [v "rowIndex", v "assignment", v "origins"], .symbol "LNil"],
    .symbol "LNil"]]

private def argumentsDoneBody : Atom :=
  a "if" [a "gslt:premise:check-assignment"
    [v "declarations", v "free", v "bound", v "rule", v "spec", v "assignment"],
    argumentsAcceptedData, argumentsEmptyData]

private theorem arguments_done_shape : taskBody 2 = argumentsDoneBody := by decide +kernel

def argumentsDoneCaller (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (free : List (String × TypeExpr)) : Subst :=
  [("origins", encoded (originsTerm frame.origins)), ("assignment", assignmentValue frame.assignment),
    ("index", number frame.index), ("rowIndex", number frame.rowIndex)] ++
    frameCaller environment request (.arguments frame) free

private def argumentsAcceptedValue (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) : Atom :=
  encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil",
    .application "LCons" [.application "PremiseQueryAnswer" [.natural frame.rowIndex,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm frame.assignment,
      originsTerm frame.origins], .symbol "LNil"], .symbol "LNil"]])

private theorem arguments_done_expansion (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request)
    (schemas : frame.schemas = []) (values : frame.values = []) (modes : frame.modes = []) :
    expansionValue (Query.expand environment request (.arguments frame)) =
      if checkTypedAssignment environment request.context frame.assignment then
        argumentsAcceptedValue environment request frame else
        encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]) := by
  rcases frame with ⟨rowIndex, index, assignment, schemas', values', modes', origins, finish⟩
  change schemas' = [] at schemas
  change values' = [] at values
  change modes' = [] at modes
  subst schemas'
  subst values'
  subst modes'
  dsimp only [Query.expand, Query.expandArguments]
  split <;>
    simp [expansionValue, queryExpansionTerm, queryAnswerTerm,
      PremiseSchedulerExecution.schedulerExpansionTerm, argumentsAcceptedValue, encodeOption, encodeList]

theorem query_expand_arguments_done_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program) (state : State) (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request)
    (schemas : frame.schemas = []) (values : frame.values = []) (modes : frame.modes = [])
    (footprint : List String)
    (covers : ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint) :
    PureReturns program [] state
      (a "gslt:premise:query-expand-in" [environmentValue environment (environment.free.entriesOn footprint),
        queryValue request, taskValue (.arguments frame)]) state
      (expansionValue (Query.expand environment request (.arguments frame))) := by
  let caller := argumentsDoneCaller environment request frame (environment.free.entriesOn footprint)
  apply expand_branch_returns program agreement state environment request (.arguments frame) (environment.free.entriesOn footprint)
    caller argumentsDoneBody _
  · simp [task_cases_syntax, arguments_done_shape, query_arguments_wire, schemas, values, modes,
      InferenceCettaWire.encodePatterns,
      caller, argumentsDoneCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · have checked := lower.assignment caller state environment.language
      (environment.free.entriesOn footprint) request.context.bound request.context.rule request.context.spec frame.assignment
      (v "declarations") (v "free") (v "bound") (v "rule") (v "spec") (v "assignment") (by
        simp [caller, argumentsDoneCaller, frameCaller, requestCaller, contextCaller, environmentCaller,
          callee, Helper.names, applySubst, Subst.lookup, DeclarationTyping.declarationsTerm])
    rw [ConditionalEquationExecution.checkAssignment_snapshot environment.language environment.free request.context.bound request.context.rule request.context.spec frame.assignment footprint covers] at checked
    rw [arguments_done_expansion environment request frame schemas values modes]
    unfold argumentsDoneBody
    apply bool_if_returns program caller state _ (checkTypedAssignment environment request.context frame.assignment)
      argumentsAcceptedData argumentsEmptyData _ checked
    cases checkedValue : checkTypedAssignment environment request.context frame.assignment with
    | false =>
        have templated : PureData.Template program argumentsEmptyData := by unfold argumentsEmptyData; query_template (program) (agreement)
        simpa [checkedValue, argumentsEmptyData, applySubst, applySubst.applySubstList, CettaWireAtom.encode,
          CettaWireAtom.encodeMany] using PureData.template_return program caller state _ templated
    | true =>
        have templated : PureData.Template program argumentsAcceptedData := by unfold argumentsAcceptedData; query_template (program) (agreement)
        simpa [checkedValue, argumentsAcceptedData, argumentsAcceptedValue,
          caller, argumentsDoneCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
          applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return program caller state _ templated


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue queryValue taskValue

private def shapeData : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
    a "LCons" [a "PremiseArgumentShape" [v "rowIndex", v "index"], .symbol "LNil"]]]

private theorem shape_body : taskBody 5 = shapeData := by decide +kernel

private def shapeCaller (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (free : List (String × TypeExpr)) : Subst :=
  [("origins", encoded (originsTerm frame.origins)), ("modes", encoded (encodeList modeTerm frame.modes)),
    ("values", patternsValue frame.values), ("schemas", patternsValue frame.schemas),
    ("assignment", assignmentValue frame.assignment), ("index", number frame.index), ("rowIndex", number frame.rowIndex)] ++
    frameCaller environment request (.arguments frame) free

theorem query_expand_arguments_shape_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (free : List (String × TypeExpr))
    (shape : ¬ (frame.schemas.isEmpty = frame.values.isEmpty ∧ frame.values.isEmpty = frame.modes.isEmpty)) :
    PureReturns program [] state (a "gslt:premise:query-expand-in"
      [environmentValue environment free, queryValue request, taskValue (.arguments frame)]) state
      (expansionValue (Query.expand environment request (.arguments frame))) := by
  let caller := shapeCaller environment request frame free
  have original : expansionValue (Query.expand environment request (.arguments frame)) =
      encoded (.application "Some" [.application "PremiseExpansion" [.symbol "LNil", .symbol "LNil",
        .application "LCons" [.application "PremiseArgumentShape" [.natural frame.rowIndex, .natural frame.index], .symbol "LNil"]]]) := by
    simp only [Query.expand, Query.expandArguments]
    split
    · rename_i schemasFound valuesFound modesFound
      exact False.elim (shape (by simp [schemasFound, valuesFound, modesFound]))
    · rename_i schema schemas value values mode modes schemasFound valuesFound modesFound
      exact False.elim (shape (by simp [schemasFound, valuesFound, modesFound]))
    · rfl
  rw [original]
  apply expand_branch_returns program agreement state environment request (.arguments frame) free caller shapeData _
  · cases schemasFound : frame.schemas <;> cases valuesFound : frame.values <;> cases modesFound : frame.modes
    case nil.nil.nil => exact False.elim (shape (by simp [schemasFound, valuesFound, modesFound]))
    case cons.cons.cons => exact False.elim (shape (by simp [schemasFound, valuesFound, modesFound]))
    case nil.nil.cons mode modes =>
      cases mode <;>
        simp [task_cases_syntax, shape_body, query_arguments_wire, schemasFound, valuesFound, modesFound,
          InferenceCettaWire.encodePatterns, encodeList, modeTerm, caller, shapeCaller,
          frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    case nil.cons.cons value values mode modes =>
      cases mode <;>
        simp [task_cases_syntax, shape_body, query_arguments_wire, schemasFound, valuesFound, modesFound,
          InferenceCettaWire.encodePatterns, encodeList, modeTerm, caller, shapeCaller,
          frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    case cons.nil.cons schema schemas mode modes =>
      cases mode <;>
        simp [task_cases_syntax, shape_body, query_arguments_wire, schemasFound, valuesFound, modesFound,
          InferenceCettaWire.encodePatterns, encodeList, modeTerm, caller, shapeCaller,
          frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    all_goals
      simp [task_cases_syntax, shape_body, query_arguments_wire, schemasFound, valuesFound, modesFound,
        InferenceCettaWire.encodePatterns, encodeList, caller, shapeCaller,
        frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · have templated : PureData.Template program shapeData := by
      unfold shapeData
      apply data_template program agreement "Some" _ (by decide)
      intro child member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst child
      apply data_template program agreement "PremiseExpansion" _ (by decide)
      intro child member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact .symbol _
      · exact .symbol _
      · apply data_template program agreement "LCons" _ (by decide)
        intro child member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · apply data_template program agreement "PremiseArgumentShape" _ (by decide)
          intro child member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> exact .captured _
        · exact .symbol _
    simpa [shapeData, caller, shapeCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
      applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
      PureData.template_return program caller state _ templated

theorem query_expand_arguments_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program)
    (state : State) (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request) (footprint : List String)
    (covers : ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint) :
    PureReturns program [] state (a "gslt:premise:query-expand-in"
      [environmentValue environment (environment.free.entriesOn footprint), queryValue request, taskValue (.arguments frame)]) state
      (expansionValue (Query.expand environment request (.arguments frame))) := by
  cases schemasFound : frame.schemas <;> cases valuesFound : frame.values <;> cases modesFound : frame.modes
  case nil.nil.nil =>
    exact query_expand_arguments_done_returns program agreement lower state environment request frame
      schemasFound valuesFound modesFound footprint covers
  case cons.cons.cons schema schemas value values mode modes =>
    cases mode with
    | input =>
        exact query_expand_arguments_input_returns program agreement lower state environment request frame
          (environment.free.entriesOn footprint) schema schemas value values modes schemasFound valuesFound modesFound
    | output =>
        exact query_expand_arguments_output_returns program agreement lower state environment request frame
          (environment.free.entriesOn footprint) schema schemas value values modes schemasFound valuesFound modesFound
  all_goals
    exact query_expand_arguments_shape_returns program agreement state environment request frame
      (environment.free.entriesOn footprint) (by simp [schemasFound, valuesFound, modesFound])


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

attribute [local simp] a v encoded number boundValue patternValue patternsValue ruleValue assignmentValue contextValue queryValue taskValue

local macro "query_template" "(" p:term ")" "(" g:term ")" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template $p $g _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

abbrev matcherAnswerWire := RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm
abbrev matcherWorkWire := RuleInstantiationExecution.GeneralExecution.matcherWorkTerm

theorem query_matcher_wire (environment : Environment) (request : Query.Request)
    (frame : Query.MatcherFrame environment request) :
    queryTaskTerm (.matcher frame) = .application "PremiseQueryMatcher"
      [.natural frame.rowIndex, .natural frame.argumentIndex, InferenceCettaWire.encodePatterns frame.schemas,
        InferenceCettaWire.encodePatterns frame.values, encodeList modeTerm frame.modes, originsTerm frame.origins,
        matcherRequestTerm frame.query, matcherStateTerm frame.state, .natural frame.cursor] := rfl

private def emptyData : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", .symbol "LNil"]]

private def answerData : Atom :=
  a "Some" [a "PremiseExpansion" [a "LCons" [
    a "PremiseQueryArguments" [v "rowIndex", v "nextArgument", v "assignment", v "schemas", v "values", v "modes", v "extended"],
    a "LCons" [a "PremiseQueryMatcher" [v "rowIndex", v "argument", v "schemas", v "values", v "modes", v "origins",
      v "query", v "state", v "nextCursor"], .symbol "LNil"]], .symbol "LNil", .symbol "LNil"]]

private def answerBody : Atom :=
  a "let*" [.expression [
    .expression [v "nextArgument", a "+" [v "argument", number 1]],
    .expression [v "nextCursor", a "+" [v "cursor", number 1]],
    .expression [v "extended", a "gslt:automata:append" [v "origins",
      a "LCons" [a "ArgumentOrigin" [v "argument", v "trace"], .symbol "LNil"]]]], answerData]

private def steppedData : Atom :=
  a "Some" [a "PremiseExpansion" [a "LCons" [
    a "PremiseQueryMatcher" [v "rowIndex", v "argument", v "schemas", v "values", v "modes", v "origins", v "query", v "stepped", v "cursor"],
    .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]

private def stopBody : Atom :=
  a "if" [a "gslt:rule:scope-matcher-complete" [v "state"], emptyData,
    a "let" [v "stepped", a "gslt:rule:scope-matcher-tick" [v "query", v "state"], steppedData]]

private def answerCases : SpaceSemantics.Cases :=
  [(a "Some" [a "ScopedMatcherAnswer" [v "assignment", v "trace"]], answerBody),
    (.symbol "None", stopBody), (v "badAnswer", .symbol "None")]

private def stateBody : Atom := caseData (a "gslt:rule:row-at" [v "cursor", v "answers"]) answerCases

private def stateCases : SpaceSemantics.Cases :=
  [(a "ScopedMatcherState" [v "agenda", v "answers"], stateBody), (v "badState", .symbol "None")]

private def matcherBody : Atom := caseData (v "state") stateCases

private theorem matcher_shape : taskBody 6 = matcherBody := by decide +kernel

def matcherCaller (environment : Environment) (request : Query.Request)
    (frame : Query.MatcherFrame environment request) (free : List (String × TypeExpr)) : Subst :=
  [("cursor", number frame.cursor), ("state", encoded (matcherStateTerm frame.state)),
    ("query", encoded (matcherRequestTerm frame.query)), ("origins", encoded (originsTerm frame.origins)),
    ("modes", encoded (encodeList modeTerm frame.modes)), ("values", patternsValue frame.values),
    ("schemas", patternsValue frame.schemas), ("argument", number frame.argumentIndex), ("rowIndex", number frame.rowIndex)] ++
    frameCaller environment request (.matcher frame) free

theorem query_expand_matcher_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program)
    (state : State) (environment : Environment) (request : Query.Request)
    (frame : Query.MatcherFrame environment request) (free : List (String × TypeExpr)) :
    PureReturns program [] state (a "gslt:premise:query-expand-in"
      [environmentValue environment free, queryValue request, taskValue (.matcher frame)]) state
      (expansionValue (Query.expand environment request (.matcher frame))) := by
  let caller := matcherCaller environment request frame free
  let machine := [("answers", encoded (encodeList matcherAnswerWire frame.state.answers)),
    ("agenda", encoded (encodeList matcherWorkWire frame.state.agenda))] ++ caller
  let selected (answer : GeneralScopedMatchMachine.Answer) :=
    ("trace", encoded (traceTerm answer.trace)) :: ("assignment", assignmentValue answer.assignment) :: machine
  let nextArgument (answer : GeneralScopedMatchMachine.Answer) :=
    ("nextArgument", number (frame.argumentIndex + 1)) :: selected answer
  let nextCursor (answer : GeneralScopedMatchMachine.Answer) :=
    ("nextCursor", number (frame.cursor + 1)) :: nextArgument answer
  let extended (answer : GeneralScopedMatchMachine.Answer) :=
    ("extended", encoded (originsTerm (frame.origins ++ [(frame.argumentIndex, answer.trace)]))) :: nextCursor answer
  let stepped := ("stepped", encoded (matcherStateTerm (GeneralScopedMatchMachine.tick frame.query frame.state))) :: machine
  have wire : expansionValue (Query.expand environment request (.matcher frame)) =
      match frame.state.answers[frame.cursor]? with
      | some answer => applySubst (extended answer) answerData
      | none => if GeneralScopedMatchMachine.complete frame.state then applySubst machine emptyData
          else applySubst stepped steppedData := by
    simp only [Query.expand, Query.expandMatcher]
    split
    · rename_i answer found
      simp only [found]
      simp [answerData, extended, nextCursor, nextArgument, selected, machine, caller, matcherCaller,
        frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
        applySubst, applySubst.applySubstList, Subst.lookup, expansionValue, queryExpansionTerm,
        PremiseSchedulerExecution.schedulerExpansionTerm, query_arguments_wire, query_matcher_wire,
        encodeOption, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
    · rename_i found
      simp only [found]
      split_ifs with finished
      · simp [emptyData, applySubst, applySubst.applySubstList, expansionValue, queryExpansionTerm,
          PremiseSchedulerExecution.schedulerExpansionTerm, encodeOption, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · simp [steppedData, stepped, machine, caller, matcherCaller, frameCaller, requestCaller, contextCaller,
          environmentCaller, callee, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup,
          expansionValue, queryExpansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm,
          query_matcher_wire, encodeOption, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  rw [wire]
  apply expand_branch_returns program agreement state environment request (.matcher frame) free caller matcherBody _
  · let values : List Atom := [number frame.rowIndex, number frame.argumentIndex,
      patternsValue frame.schemas, patternsValue frame.values, encoded (encodeList modeTerm frame.modes),
      encoded (originsTerm frame.origins), encoded (matcherRequestTerm frame.query),
      encoded (matcherStateTerm frame.state), number frame.cursor]
    have taskWire : taskValue (.matcher frame) = a "PremiseQueryMatcher" values := by
      change encoded (queryTaskTerm (.matcher frame)) = _
      rw [query_matcher_wire]
      rfl
    rw [task_cases_syntax, matcher_shape, taskWire]
    rw [SpaceSemantics.selectCase, symbol_constructor_mismatch]
    rw [select_skip_constructor _ "PremiseQueryRows" "PremiseQueryMatcher" _ _ _ _ (by decide) (by decide)]
    iterate 4 rw [select_skip_constructor _ "PremiseQueryArguments" "PremiseQueryMatcher" _ _ _ _ (by decide) (by decide)]
    rw [SpaceSemantics.selectCase]
    have matched := constructor_variables_match (frameCaller environment request (.matcher frame) free)
      "PremiseQueryMatcher" ["rowIndex", "argument", "schemas", "values", "modes", "origins", "query", "state", "cursor"]
      values (by decide) (by decide) (by rfl) (by
        intro name member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup])
    have fields : SpaceSemantics.matchValue (frameCaller environment request (.matcher frame) free)
        (a "PremiseQueryMatcher" [v "rowIndex", v "argument", v "schemas", v "values", v "modes", v "origins", v "query", v "state", v "cursor"])
        (a "PremiseQueryMatcher" values) = some caller := by
      simpa [values, caller, matcherCaller] using matched
    rw [fields]
  · unfold matcherBody
    apply branch_returns program caller machine state _ (encoded (matcherStateTerm frame.state)) stateCases stateBody _
    · simpa [caller, matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
        applySubst, Subst.lookup] using variable_returns program caller state "state"
    · simp [stateCases, matcherStateTerm, RuleInstantiationExecution.GeneralExecution.matcherStateTerm, machine,
        caller, matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
        matcherAnswerWire, matcherWorkWire, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    · have row := row_encoded_returns program lower matcherAnswerWire machine state frame.cursor frame.state.answers
        (v "cursor") (v "answers") (by simp [machine, caller, matcherCaller, frameCaller, requestCaller, contextCaller,
          environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
      unfold stateBody
      cases found : frame.state.answers[frame.cursor]? with
      | some answer =>
          apply branch_returns program machine (selected answer) state _ (encoded (encodeOption matcherAnswerWire (some answer)))
            answerCases answerBody _
          · simpa only [found] using row
          · simp [answerCases, matcherAnswerWire, RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
              selected, machine, caller, matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
          · unfold answerBody
            apply PureData.let_bindings_return (pairs := [
              (v "nextArgument", a "+" [v "argument", number 1]), (v "nextCursor", a "+" [v "cursor", number 1]),
              (v "extended", a "gslt:automata:append" [v "origins", a "LCons" [a "ArgumentOrigin" [v "argument", v "trace"], .symbol "LNil"]])])
              (final := extended answer) (middle := state) _ state answerData _ _
            · apply PureData.BindingsReturn.cons (bound := nextArgument answer) (middle := state)
                (value := number (frame.argumentIndex + 1))
              · apply add_returns program agreement (selected answer) state frame.argumentIndex 1 (v "argument") (number 1)
                · simpa [selected, machine, caller, matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller,
                    callee, Helper.names, applySubst, Subst.lookup] using variable_returns program (selected answer) state "argument"
                · exact grounded_returns program (selected answer) state (.int 1)
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, nextArgument, selected, machine,
                  caller, matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
              · apply PureData.BindingsReturn.cons (bound := nextCursor answer) (middle := state) (value := number (frame.cursor + 1))
                · apply add_returns program agreement (nextArgument answer) state frame.cursor 1 (v "cursor") (number 1)
                  · simpa [nextArgument, selected, machine, caller, matcherCaller, frameCaller, requestCaller, contextCaller,
                      environmentCaller, callee, Helper.names, applySubst, Subst.lookup] using
                      variable_returns program (nextArgument answer) state "cursor"
                  · exact grounded_returns program (nextArgument answer) state (.int 1)
                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, nextCursor, nextArgument, selected, machine,
                    caller, matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
                · apply PureData.BindingsReturn.cons (bound := extended answer) (middle := state)
                    (value := encoded (originsTerm (frame.origins ++ [(frame.argumentIndex, answer.trace)])))
                  · exact append_encoded_returns program lower
                      (fun origin : Nat × List GeneralScopedMatchMachine.BagChoice => .application "ArgumentOrigin" [.natural origin.1, traceTerm origin.2])
                      (nextCursor answer) state frame.origins [(frame.argumentIndex, answer.trace)] (v "origins")
                      (a "LCons" [a "ArgumentOrigin" [v "argument", v "trace"], .symbol "LNil"]) (by
                        simp [originsTerm, nextCursor, nextArgument, selected, machine, caller, matcherCaller, frameCaller,
                          requestCaller, contextCaller, environmentCaller, callee, Helper.names, applySubst, applySubst.applySubstList,
                          Subst.lookup, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany])
                  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, extended, nextCursor, nextArgument, selected, machine,
                      caller, matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
                  · exact .nil _ _
            · have templated : PureData.Template program answerData := by unfold answerData; query_template (program) (agreement)
              simpa only [found] using PureData.template_return program (extended answer) state _ templated
      | none =>
          apply branch_returns program machine machine state _ (.symbol "None") answerCases stopBody _
          · simpa [found, encodeOption, CettaWireAtom.encode] using row
          · simp [answerCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
          · have tested := lower.complete machine state frame.state (v "state") (by
              simp [machine, caller, matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
                applySubst, Subst.lookup])
            unfold stopBody
            apply bool_if_returns program machine state _ (GeneralScopedMatchMachine.complete frame.state) emptyData _ _ tested
            cases finished : GeneralScopedMatchMachine.complete frame.state with
            | true =>
                have templated : PureData.Template program emptyData := by unfold emptyData; query_template (program) (agreement)
                simpa only [found, finished, ↓reduceIte] using PureData.template_return program machine state _ templated
            | false =>
                apply named_let_returns program machine state "stepped" _ _ _ _
                · simp [machine, caller, matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names, Subst.lookup]
                · exact lower.tick machine state frame.query frame.state (v "query") (v "state") (by
                    simp [machine, caller, matcherCaller, frameCaller, requestCaller, contextCaller, environmentCaller, callee, Helper.names,
                      applySubst, Subst.lookup])
                · have templated : PureData.Template program steppedData := by unfold steppedData; query_template (program) (agreement)
                  simpa only [found, finished, Bool.false_eq_true, ↓reduceIte] using PureData.template_return program stepped state _ templated


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open SpaceSemantics (Program)
open Eval

theorem query_expand_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program)
    (state : State) (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations)
    (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (captures : ∀ frame : Query.ArgumentsFrame environment request, task = .arguments frame →
      ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint) :
    PureReturns program [] state (a "gslt:premise:query-expand-in"
      [environmentValue environment (environment.free.entriesOn footprint), queryValue request, taskValue task]) state
      (expansionValue (Query.expand environment request task)) := by
  cases task with
  | start =>
      exact query_expand_start_returns program agreement lower state environment request
        (environment.free.entriesOn footprint) unregistered
  | rows frame => exact query_expand_rows_returns program agreement lower state environment request frame footprint provider
  | arguments frame =>
      exact query_expand_arguments_returns program agreement lower state environment request frame footprint
        (captures frame rfl)
  | matcher frame =>
      exact query_expand_matcher_returns program agreement lower state environment request frame
        (environment.free.entriesOn footprint)
  | dynamicInputs frame => exact False.elim (unregistered frame.registered)
  | dynamicRows frame => exact False.elim (unregistered frame.registered)


theorem query_expand_captured_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program)
    (caller : Subst) (state : State) (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations)
    (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (captures : ∀ frame : Query.ArgumentsFrame environment request, task = .arguments frame →
      ∀ name ∈ ConditionalEquationExecution.assignmentFreeNames frame.assignment, name ∈ footprint)
    (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [environmentValue environment (environment.free.entriesOn footprint), queryValue request, taskValue task]) :
    PureReturns program caller state (a "gslt:premise:query-expand-in" [one, two, three]) state
      (expansionValue (Query.expand environment request task)) :=
  helper_capture program agreement .expand caller state _ _ _ rfl captured
    (query_expand_returns program agreement lower state environment request task unregistered footprint provider captures)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open SpaceSemantics (Program)
open Eval

namespace Trajectory

open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

theorem query_expand_within_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program)
    (state : State) (environment : Environment) (request : Query.Request)
    (task : Query.Task environment request)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations)
    (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Query.taskFreeWithin footprint task) :
    PureReturns program [] state (a "gslt:premise:query-expand-in"
      [environmentValue environment (environment.free.entriesOn footprint), queryValue request, taskValue task]) state
      (expansionValue (Query.expand environment request task)) := by
  apply query_expand_returns program agreement lower state environment request task unregistered footprint provider
  intro frame same
  subst task
  exact Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution.assignment_free_names_covered _ _ covered.1

theorem query_expand_prefix_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program) (lower : LowerOperations program)
    (state : State) (environment : Environment) (request : Query.Request)
    (finiteProvider : environment.provider.dynamicRelations = [])
    (fuel : Nat) (task : Query.Task environment request)
    (member : task ∈ (Query.run environment request fuel (Query.start environment request)).agenda) :
    PureReturns program [] state (a "gslt:premise:query-expand-in"
      [environmentValue environment (environment.free.entriesOn
        (ConditionalEquationExecution.assignmentFreeNames request.initial ++ providerFreeNames environment.provider)),
        queryValue request, taskValue task]) state
      (expansionValue (Query.expand environment request task)) :=
  query_expand_within_returns program agreement lower state environment request task
    (by simp only [finiteProvider, List.not_mem_nil, not_false_eq_true]) _
    (fun _ occurs => List.mem_append_right _ occurs)
    ((Query.run_finite_free_within environment request
      (Query.DynamicOutputsFreeWithin.of_unregistered _ _ finiteProvider) fuel).1 _ member)


end Trajectory

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryExecution.Parameterized


set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryLower

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval
open QueryExecution (a v encoded number stringValue boundValue patternValue ruleValue assignmentValue)

private def operationArities : List (String × Nat) :=
  [("gslt:premise:signature", 3), ("gslt:premise:check-row", 5), ("gslt:rule:scope-instantiate-at", 9), ("gslt:premise:check-assignment", 6)]

private theorem raw_at (head : String) (arity index : Nat)
    (member : (head, arity) ∈ operationArities) (bound : index < arity) :
    argumentIsRaw RuleExecutionProgram.scopedMachineProgram head index = true := by
  have checked : operationArities.all (fun operation =>
      (List.range operation.2).all (argumentIsRaw RuleExecutionProgram.scopedMachineProgram operation.1)) = true := by rfl
  exact List.all_eq_true.mp (List.all_eq_true.mp checked (head, arity) member) index (List.mem_range.mpr bound)

private theorem raw_arguments (head : String) (arity : Nat)
    (member : (head, arity) ∈ operationArities) (arguments : List Atom) (length : arguments.length = arity) :
    ∀ index argument, arguments[index]? = some argument →
      argumentIsRaw RuleExecutionProgram.scopedMachineProgram head index = true ∨ passiveArgument argument = true := by
  intro index argument picked
  exact Or.inl (raw_at head arity index member (by
    have bound := (List.getElem?_eq_some_iff.mp picked).1
    simpa only [length] using bound))

private theorem ordinary_dispatch (head : String) (arity : Nat)
    (member : (head, arity) ∈ operationArities) :
    (ioHead head || StdLib.known head || RuleExecutionProgram.scopedMachineProgram.equations.any (·.head == head)) = true := by
  have checked : operationArities.all (fun operation =>
      ioHead operation.1 || StdLib.known operation.1 ||
        RuleExecutionProgram.scopedMachineProgram.equations.any (·.head == operation.1)) = true := by rfl
  exact List.all_eq_true.mp checked (head, arity) member

private theorem pattern_option_representation (result : Option Pattern) :
    encoded (MatchAutomataBindingExecution.patternOptionTerm result) =
      encoded (encodeOption InferenceCettaWire.encodePattern result) := by
  cases result <;> rfl

theorem signature_returns (caller : Subst) (state : State) (provider : ProviderSnapshot) (relation : String) (arity : Nat)
    (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) = [stringValue relation, number arity, encoded (providerTerm provider)]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:signature" [one, two, three]) state (encoded (encodeOption signatureTerm (signature? provider relation arity))) := by
  let capturedCaller : Subst := [("one", stringValue relation), ("two", number arity), ("three", encoded (providerTerm provider))]
  have capturedNames : [v "one", v "two", v "three"].map (applySubst capturedCaller) = [stringValue relation, number arity, encoded (providerTerm provider)] := by
    simp [capturedCaller, applySubst, Subst.lookup]
  have source := signature_captured_returns capturedCaller state provider relation arity (v "one") (v "two") (v "three") capturedNames
  have prepared := premise_previous_returns
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) source
  have actual := premise_returns_in_extension RuleExecutionProgram.scopedMachineProgram AssembledLower.premise_agreement
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) prepared
  exact captured_call_returns RuleExecutionProgram.scopedMachineProgram capturedCaller caller state state "gslt:premise:signature"
    [v "one", v "two", v "three"] [one, two, three] _
    (ordinary_dispatch _ 3 (by simp [operationArities])) (by decide)
    (raw_arguments _ 3 (by simp [operationArities]) _ rfl)
    (raw_arguments _ 3 (by simp [operationArities]) _ rfl)
    (capturedNames.trans captured.symm) actual

theorem row_typed_returns (caller : Subst) (state : State) (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (signature : Signature) (row : ProviderRow)
    (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) = [encoded (DeclarationTyping.declarationsTerm language.terms), encoded (DeclarationTyping.freeContextTerm free), boundValue bound, encoded (signatureTerm signature), encoded (providerRowTerm row)]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:premise:check-row" [one, two, three, four, five]) state (Effects.boolean (checkRow language (FreeTypeContext.ofList free) bound signature row)) := by
  let capturedCaller : Subst := [("one", encoded (DeclarationTyping.declarationsTerm language.terms)), ("two", encoded (DeclarationTyping.freeContextTerm free)), ("three", boundValue bound), ("four", encoded (signatureTerm signature)), ("five", encoded (providerRowTerm row))]
  have capturedNames : [v "one", v "two", v "three", v "four", v "five"].map (applySubst capturedCaller) = [encoded (DeclarationTyping.declarationsTerm language.terms), encoded (DeclarationTyping.freeContextTerm free), boundValue bound, encoded (signatureTerm signature), encoded (providerRowTerm row)] := by
    simp [capturedCaller, applySubst, Subst.lookup]
  have source := check_row_captured_returns capturedCaller state language free bound signature row (v "one") (v "two") (v "three") (v "four") (v "five") capturedNames
  have prepared := premise_previous_returns
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) source
  have actual := premise_returns_in_extension RuleExecutionProgram.scopedMachineProgram AssembledLower.premise_agreement
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) prepared
  exact captured_call_returns RuleExecutionProgram.scopedMachineProgram capturedCaller caller state state "gslt:premise:check-row"
    [v "one", v "two", v "three", v "four", v "five"] [one, two, three, four, five] _
    (ordinary_dispatch _ 5 (by simp [operationArities])) (by decide)
    (raw_arguments _ 5 (by simp [operationArities]) _ rfl)
    (raw_arguments _ 5 (by simp [operationArities]) _ rfl)
    (capturedNames.trans captured.symm) actual

theorem instantiate_returns (caller : Subst) (state : State) (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (assignment : Assignment) (pattern : Pattern)
    (one two three four five six seven eight nine : Atom)
    (captured : [one, two, three, four, five, six, seven, eight, nine].map (applySubst caller) = [.symbol "None", ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient, encoded (InferenceCettaWire.AuthoredRule.siteTerm site), encoded (encodeList Term.natural path), number depth, assignmentValue assignment, patternValue pattern]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state (a "gslt:rule:scope-instantiate-at" [one, two, three, four, five, six, seven, eight, nine]) state (encoded (encodeOption InferenceCettaWire.encodePattern (instantiateAt? rule spec ambient site path depth assignment pattern))) := by
  let capturedCaller : Subst := [("one", .symbol "None"), ("two", ruleValue rule), ("three", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)), ("four", number ambient), ("five", encoded (InferenceCettaWire.AuthoredRule.siteTerm site)), ("six", encoded (encodeList Term.natural path)), ("seven", number depth), ("eight", assignmentValue assignment), ("nine", patternValue pattern)]
  have capturedNames : [v "one", v "two", v "three", v "four", v "five", v "six", v "seven", v "eight", v "nine"].map (applySubst capturedCaller) = [.symbol "None", ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient, encoded (InferenceCettaWire.AuthoredRule.siteTerm site), encoded (encodeList Term.natural path), number depth, assignmentValue assignment, patternValue pattern] := by
    simp [capturedCaller, applySubst, Subst.lookup]
  have source := ScopedInstantiationExecution.instantiate_ordinary_captured_returns capturedCaller state
    rule spec ambient site path depth assignment pattern [v "one", v "two", v "three", v "four", v "five", v "six", v "seven", v "eight", v "nine"]
    (by simpa only [ScopedInstantiationExecution.instantiationValues] using capturedNames)
  have actual := path_of_closed_agreement ScopedInstantiationExecution.runtime_closed ScopedInstantiationExecution.scoped_machine_agreement
    ⟨by change codeWithin ScopedInstantiationExecution.executionHeads (a "gslt:rule:scope-instantiate-at" [v "one", v "two", v "three", v "four", v "five", v "six", v "seven", v "eight", v "nine"]) = true
        decide +kernel, rfl⟩ source
  exact captured_call_returns RuleExecutionProgram.scopedMachineProgram capturedCaller caller state state "gslt:rule:scope-instantiate-at"
    [v "one", v "two", v "three", v "four", v "five", v "six", v "seven", v "eight", v "nine"] [one, two, three, four, five, six, seven, eight, nine] _
    (ordinary_dispatch _ 9 (by simp [operationArities])) (by decide)
    (raw_arguments _ 9 (by simp [operationArities]) _ rfl)
    (raw_arguments _ 9 (by simp [operationArities]) _ rfl)
    (capturedNames.trans captured.symm) (by simpa only [pattern_option_representation] using actual)

theorem assignment_returns (caller : Subst) (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (rule : RewriteRule)
    (spec : RuleBindingSpec) (assignment : Assignment) (one two three four five six : Atom)
    (captured : [one, two, three, four, five, six].map (applySubst caller) =
      [encoded (DeclarationTyping.declarationsTerm language.terms), encoded (DeclarationTyping.freeContextTerm free), boundValue bound, ruleValue rule,
        encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), assignmentValue assignment]) :
    PureReturns RuleExecutionProgram.scopedMachineProgram caller state
      (a "gslt:premise:check-assignment" [one, two, three, four, five, six]) state
      (Effects.boolean (ConditionalEquationExecution.checkAssignment language
        (FreeTypeContext.ofList free) bound rule spec assignment)) := by
  let capturedCaller : Subst :=
    [("one", encoded (DeclarationTyping.declarationsTerm language.terms)), ("two", encoded (DeclarationTyping.freeContextTerm free)), ("three", boundValue bound),
      ("four", ruleValue rule), ("five", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)), ("six", assignmentValue assignment)]
  have capturedNames : [v "one", v "two", v "three", v "four", v "five", v "six"].map
      (applySubst capturedCaller) =
      [encoded (DeclarationTyping.declarationsTerm language.terms), encoded (DeclarationTyping.freeContextTerm free), boundValue bound, ruleValue rule,
        encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), assignmentValue assignment] := by
    simp [capturedCaller, applySubst, Subst.lookup]
  have source := check_assignment_captured_returns capturedCaller state language free bound rule spec
    assignment (v "one") (v "two") (v "three") (v "four") (v "five") (v "six") capturedNames
  have prepared := premise_previous_returns
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) source
  have actual := premise_returns_in_extension RuleExecutionProgram.scopedMachineProgram AssembledLower.premise_agreement
    (by simp [codeWithin, expressionHeadWithin, atomsWithin]; decide +kernel) prepared
  exact captured_call_returns RuleExecutionProgram.scopedMachineProgram capturedCaller caller state state
    "gslt:premise:check-assignment" [v "one", v "two", v "three", v "four", v "five", v "six"]
    [one, two, three, four, five, six] _
    (ordinary_dispatch _ 6 (by simp [operationArities])) (by decide)
    (raw_arguments _ 6 (by simp [operationArities]) _ rfl)
    (raw_arguments _ 6 (by simp [operationArities]) _ rfl)
    (capturedNames.trans captured.symm) actual


theorem operations : QueryExecution.Parameterized.LowerOperations RuleExecutionProgram.scopedMachineProgram where
  row := RuleInstantiationExecution.GeneralExecution.Mechanical.row_returns
  length := RuleInstantiationExecution.GeneralExecution.Mechanical.length_returns
  append := RuleInstantiationExecution.GeneralExecution.Mechanical.append_returns
  signature := signature_returns
  rowTyped := row_typed_returns
  assignment := assignment_returns
  start := RuleInstantiationExecution.GeneralExecution.Mechanical.start_returns
  tick := RuleInstantiationExecution.GeneralExecution.Mechanical.tick_returns
  complete := RuleInstantiationExecution.GeneralExecution.Mechanical.complete_returns
  instantiate := instantiate_returns


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.QueryLower


set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.ControlAssembly

open Eval

theorem query_retained_equations :
    QueryExecution.runtime.equations.filter (fun equation => QueryExecution.Parameterized.ownedHeads equation.head) =
    RuleExecutionProgram.scopedMachineProgram.equations.filter (fun equation => QueryExecution.Parameterized.ownedHeads equation.head) := by rfl

theorem query_retained_declarations :
    QueryExecution.runtime.declarations.filter (retainedCallDeclaration QueryExecution.Parameterized.ownedHeads) =
    RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration QueryExecution.Parameterized.ownedHeads) := by rfl

theorem query_agreement : ProgramAgreementOn QueryExecution.Parameterized.ownedHeads QueryExecution.runtime RuleExecutionProgram.scopedMachineProgram :=
  Eval.programAgreementOn_of_retained_rows _ _ _ query_retained_equations query_retained_declarations


theorem scheduler_retained_equations :
    PremiseSchedulerExecution.runtime.equations.filter (fun equation => PremiseSchedulerExecution.executionHeads equation.head) =
    RuleExecutionProgram.scopedMachineProgram.equations.filter (fun equation => PremiseSchedulerExecution.executionHeads equation.head) := by rfl

theorem scheduler_retained_declarations :
    PremiseSchedulerExecution.runtime.declarations.filter (retainedCallDeclaration PremiseSchedulerExecution.executionHeads) =
    RuleExecutionProgram.scopedMachineProgram.declarations.filter (retainedCallDeclaration PremiseSchedulerExecution.executionHeads) := by rfl

theorem scheduler_agreement : ProgramAgreementOn PremiseSchedulerExecution.executionHeads PremiseSchedulerExecution.runtime RuleExecutionProgram.scopedMachineProgram :=
  Eval.programAgreementOn_of_retained_rows _ _ _ scheduler_retained_equations scheduler_retained_declarations


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.ControlAssembly


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

def queryRequestCases : SpaceSemantics.Cases := sourceCases (taskBody 2)
def queryRequestBody : Atom := (queryRequestCases.head!).2
def queryContextCases : SpaceSemantics.Cases := sourceCases queryRequestBody
def queryContextBody : Atom := (queryContextCases.head!).2
def queryStateCases : SpaceSemantics.Cases := sourceCases queryContextBody
def queryStateBody : Atom := (queryStateCases.head!).2
def queryAnswerCases : SpaceSemantics.Cases := sourceCases queryStateBody
def queryAnswerBody : Atom := (queryAnswerCases.head!).2
def queryAgendaCases : SpaceSemantics.Cases := sourceCases ((queryAnswerCases[1]!).2)
def queryEmptyBody : Atom := (queryAgendaCases.head!).2
def queryProgressBody : Atom := ((queryAgendaCases[1]!).2)

theorem query_task_shape : taskBody 2 = caseData (v "request") queryRequestCases := by decide +kernel
theorem query_request_shape : queryRequestBody = caseData (v "context") queryContextCases := by decide +kernel
theorem query_context_shape : queryContextBody = caseData (v "queryState") queryStateCases := by decide +kernel
theorem query_state_shape : queryStateBody =
    caseData (a "gslt:rule:row-at" [v "cursor", v "answers"]) queryAnswerCases := by decide +kernel
theorem query_none_shape : (queryAnswerCases[1]!).2 = caseData (v "agenda") queryAgendaCases := by decide +kernel

theorem query_request_cases_syntax : queryRequestCases =
    [(a "PremiseQueryRequest" [v "context", v "relation", v "arguments", v "initial"], queryRequestBody),
      (v "badRequest", .symbol "None")] := by decide +kernel
theorem query_context_cases_syntax : queryContextCases =
    [(a "PremiseContext" [v "ruleIndex", v "rule", v "spec", v "bound", v "premiseIndex", v "quantifiers"], queryContextBody),
      (v "badContext", .symbol "None")] := by decide +kernel
theorem query_state_cases_syntax : queryStateCases =
    [(a "PremiseState" [v "agenda", v "answers", v "unresolved", v "work"], queryStateBody),
      (v "badState", .symbol "None")] := by decide +kernel
theorem query_answer_cases_syntax : queryAnswerCases =
    [(a "Some" [a "PremiseQueryAnswer" [v "rowIndex", v "assignment", v "origins"]], queryAnswerBody),
      (.symbol "None", caseData (v "agenda") queryAgendaCases),
      (v "badAnswer", .symbol "None")] := by decide +kernel
theorem query_agenda_cases_syntax : queryAgendaCases =
    [(.symbol "LNil", queryEmptyBody),
      (a "LCons" [v "queryTask", v "queryRest"], queryProgressBody),
      (v "badAgenda", .symbol "None")] := by decide +kernel

def queryTaskCaller (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("continuation", continuationValue tail), ("cursor", number cursor),
    ("queryState", encoded (queryStateTerm machine)), ("request", QueryExecution.queryValue request)] ++
    taskCaller environment (.query request machine cursor tail) free

def queryRequestCaller (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("initial", assignmentValue request.initial), ("arguments", patternsValue request.arguments),
    ("relation", stringValue request.relation), ("context", contextValue request.context)] ++
    queryTaskCaller environment outer request machine cursor tail free

def queryContextCaller (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("quantifiers", number request.context.quantifierDepth), ("premiseIndex", number request.context.premiseIndex),
    ("bound", boundValue request.context.bound), ("spec", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.context.spec)),
    ("rule", ruleValue request.context.rule), ("ruleIndex", number request.context.ruleIndex)] ++
    queryRequestCaller environment outer request machine cursor tail free

def queryMachineCaller (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) : Subst :=
  [("work", number machine.work), ("unresolved", encoded (encodeList queryObligationTerm machine.unresolved)),
    ("answers", encoded (encodeList QueryExecution.queryAnswerTerm machine.answers)),
    ("agenda", encoded (encodeList queryTaskTerm machine.agenda))] ++
    queryContextCaller environment outer request machine cursor tail free

theorem query_task_selected (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) :
    SpaceSemantics.selectCase (taskCaller environment (.query request machine cursor tail) free)
      (taskValue (.query request machine cursor tail)) taskCases =
      some (queryTaskCaller environment outer request machine cursor tail free, taskBody 2) := by
  simp [task_cases_syntax, taskValue, taskTerm, queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]

theorem expand_query_body_returns (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) (answer : Atom)
    (returned : PureReturns program (queryMachineCaller environment outer request machine cursor tail free)
      state queryStateBody state answer) :
    PureReturns program [] state (a Helper.expand.head
      [environmentValue environment free, taskValue (.query request machine cursor tail)]) state answer := by
  apply expand_branch_returns program agreement state environment outer (.query request machine cursor tail) free
    (queryTaskCaller environment outer request machine cursor tail free) (taskBody 2) answer
    (query_task_selected environment outer request machine cursor tail free)
  rw [query_task_shape]
  apply branch_returns program (queryTaskCaller environment outer request machine cursor tail free)
    (queryRequestCaller environment outer request machine cursor tail free) state _ (QueryExecution.queryValue request)
    queryRequestCases queryRequestBody answer
  · simpa [queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup] using
      variable_returns program (queryTaskCaller environment outer request machine cursor tail free) state "request"
  · simp [query_request_cases_syntax, QueryExecution.queryValue, queryRequestTerm,
      queryRequestCaller, queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [query_request_shape]
    apply branch_returns program (queryRequestCaller environment outer request machine cursor tail free)
      (queryContextCaller environment outer request machine cursor tail free) state _ (contextValue request.context)
      queryContextCases queryContextBody answer
    · simpa [queryRequestCaller, queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
        applySubst, Subst.lookup] using
        variable_returns program (queryRequestCaller environment outer request machine cursor tail free) state "context"
    · simp [query_context_cases_syntax, contextValue, contextTerm,
        queryContextCaller, queryRequestCaller, queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    · rw [query_context_shape]
      apply branch_returns program (queryContextCaller environment outer request machine cursor tail free)
        (queryMachineCaller environment outer request machine cursor tail free) state _ (encoded (queryStateTerm machine))
        queryStateCases queryStateBody answer
      · simpa [queryContextCaller, queryRequestCaller, queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
          applySubst, Subst.lookup] using
          variable_returns program (queryContextCaller environment outer request machine cursor tail free) state "queryState"
      · simp [query_state_cases_syntax, queryStateTerm, PremiseSchedulerExecution.schedulerStateTerm, queryMachineCaller, queryContextCaller, queryRequestCaller,
          queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · exact returned


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open SpaceSemantics (Program)
open Eval

theorem query_commit_in_extension_returns (program : Program)
    (agreement : ProgramAgreementOn PremiseSchedulerExecution.executionHeads PremiseSchedulerExecution.runtime program)
    (caller : Subst) (state : State) (environment : Environment) (request : Query.Request)
    (machine : Query.State environment request) (current : Query.Task environment request)
    (rest : List (Query.Task environment request)) (agenda : machine.agenda = current :: rest)
    (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [QueryExecution.encoded (queryStateTerm machine),
        QueryExecution.encoded (encodeOption QueryExecution.queryExpansionTerm
          (some (Query.expand environment request current)))]) :
    PureReturns program caller state (QueryExecution.a "gslt:premise:machine-commit" arguments) state
      (QueryExecution.encoded (encodeOption queryStateTerm (some (Query.tick environment request machine)))) := by
  let values := [QueryExecution.encoded (queryStateTerm machine),
    QueryExecution.encoded (encodeOption QueryExecution.queryExpansionTerm
      (some (Query.expand environment request current)))]
  let aliases : Subst := [("queryState", values[0]!), ("queryExpansion", values[1]!)]
  have sourceCaptured : arguments.map (applySubst caller) =
      [CettaWireAtom.encode (PremiseSchedulerExecution.schedulerStateTerm
        queryTaskTerm QueryExecution.queryAnswerTerm queryObligationTerm machine),
       CettaWireAtom.encode (encodeOption (PremiseSchedulerExecution.schedulerExpansionTerm
         queryTaskTerm QueryExecution.queryAnswerTerm queryObligationTerm)
         (machine.agenda.head?.map (Query.expand environment request)))] := by
    simp only [agenda, List.head?_cons, Option.map_some]
    exact captured
  have returned := PremiseSchedulerExecution.commit_captured_returns caller state queryTaskTerm
    QueryExecution.queryAnswerTerm queryObligationTerm (Query.expand environment request) machine arguments sourceCaptured
  have transported := captured_call_in_extension PremiseSchedulerExecution.runtime_closed agreement
    caller aliases state state "gslt:premise:machine-commit" arguments ["queryState", "queryExpansion"] _
    (by decide) (by decide) (by decide +kernel) (by decide) (by
      intro offset argument selected
      have bounded : offset < arguments.length := (List.getElem?_eq_some_iff.mp selected).1
      have length : arguments.length = 2 := by
        have same := congrArg List.length captured
        simpa only [List.length_map, List.length_cons, List.length_nil] using same
      have small : offset = 0 ∨ offset = 1 := by omega
      rcases small with rfl | rfl <;> exact Or.inl (by decide +kernel)) (by
      simpa [aliases, values, applySubst, Subst.lookup] using captured) returned
  exact transported


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution


set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program)
open Eval

namespace QueryFrame

def answeredData : Atom := a "Some" [a "PremiseExpansion" [
  a "LCons" [a "PremiseDeliver" [a "PremiseResult" [
    a "PremiseGoal" [v "context", a "RelationQuery" [v "relation", v "arguments"], v "initial"],
    a "PremiseAnswer" [v "assignment", a "PremiseQueryEvent" [v "premiseIndex", v "quantifiers", v "rowIndex", v "origins"]]],
    v "continuation"], a "LCons" [a "PremiseQuery" [v "request", v "queryState", v "next", v "continuation"], .symbol "LNil"]],
  .symbol "LNil", .symbol "LNil"]]
def emptyData : Atom := a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", v "reasons"]]
def pendingData : Atom := a "Some" [a "PremiseExpansion" [a "LCons" [
  a "PremiseQuery" [v "request", v "nextState", v "cursor", v "continuation"], .symbol "LNil"], .symbol "LNil", .symbol "LNil"]]
def commitCases : SpaceSemantics.Cases :=
  [(a "Some" [v "nextState"], pendingData), (v "badCommit", .symbol "None")]
def commitBody : Atom := caseData (a "gslt:premise:machine-commit" [v "queryState", v "expanded"]) commitCases

theorem answered_shape : queryAnswerBody = a "let" [v "next", a "+" [v "cursor", number 1], answeredData] := by decide +kernel
theorem empty_shape : queryEmptyBody =
    a "let" [v "reasons", a Helper.queryObligations.head [v "unresolved"], emptyData] := by decide +kernel
theorem progress_shape : queryProgressBody = a "let" [v "expanded",
    a "gslt:premise:query-expand-in" [v "environment", v "request", v "queryTask"], commitBody] := by decide +kernel

local macro "environment_template" "(" p:term ")" "(" g:term ")" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply data_template $p $g _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

theorem answered_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) :
    PureData.Template program answeredData := by unfold answeredData; environment_template (program) (agreement)
theorem empty_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) :
    PureData.Template program emptyData := by unfold emptyData; environment_template (program) (agreement)
theorem pending_template (program : Program) (agreement : ProgramAgreementOn ownedHeads runtime program) :
    PureData.Template program pendingData := by unfold pendingData; environment_template (program) (agreement)

theorem expand_query_answer_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (queryAgreement : ProgramAgreementOn QueryExecution.Parameterized.ownedHeads QueryExecution.runtime program)
    (lower : QueryExecution.Parameterized.LowerOperations program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) (answer : Query.Answer environment request)
    (found : machine.answers[cursor]? = some answer) :
    PureReturns program [] state (a Helper.expand.head
      [environmentValue environment free, taskValue (.query request machine cursor tail)]) state
      (expansionValue (Execution.expandQuery environment outer request machine cursor tail)) := by
  let caller := queryMachineCaller environment outer request machine cursor tail free
  let selected := [("origins", encoded (originsTerm answer.origins)), ("assignment", assignmentValue answer.assignment),
    ("rowIndex", number answer.rowIndex)] ++ caller
  let final := ("next", number (cursor + 1)) :: selected
  apply expand_query_body_returns program agreement state environment outer request machine cursor tail free
  rw [query_state_shape]
  apply branch_returns program caller selected state _ (encoded (encodeOption QueryExecution.queryAnswerTerm (some answer)))
    queryAnswerCases queryAnswerBody _
  · have returned := QueryExecution.Parameterized.row_encoded_returns program lower QueryExecution.queryAnswerTerm
      caller state cursor machine.answers (v "cursor") (v "answers") (by
        simp [caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
    simpa only [found] using returned
  · simp [query_answer_cases_syntax, selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller,
      queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names, QueryExecution.queryAnswerTerm,
      assignmentValue, encodeOption,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
  · rw [answered_shape]
    apply named_let_returns program selected state "next" _ (number (cursor + 1)) answeredData _
    · simp [selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
        taskCaller, environmentCaller, callee, Helper.names, Subst.lookup]
    · apply QueryExecution.Parameterized.add_returns program queryAgreement selected state cursor 1
        (v "cursor") (number 1)
      · simpa [selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup] using
          variable_returns program selected state "cursor"
      · exact grounded_returns program selected state (.int 1)
    · unfold expansionValue Execution.expandQuery
      rw [found]
      exact (by
        simpa [answeredData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, taskTerm, resultTerm, goalTerm, eventTerm,
          InferenceCettaWire.AuthoredRule.premiseTerm, final, selected, caller,
          queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, assignmentValue, QueryExecution.assignmentValue,
          QueryExecution.queryValue, queryRequestTerm, contextValue, QueryExecution.contextValue,
          stringValue, patternsValue, QueryExecution.patternsValue, number, encodeOption, encodeList,
          applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return program final state answeredData (answered_template program agreement))

theorem expand_query_empty_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (lower : QueryExecution.Parameterized.LowerOperations program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (free : List (String × TypeExpr)) (missing : machine.answers[cursor]? = none)
    (empty : machine.agenda = []) :
    PureReturns program [] state (a Helper.expand.head
      [environmentValue environment free, taskValue (.query request machine cursor tail)]) state
      (expansionValue (Execution.expandQuery environment outer request machine cursor tail)) := by
  let caller := queryMachineCaller environment outer request machine cursor tail free
  let final := ("reasons", encoded (encodeList obligationTerm (machine.unresolved.map Execution.Obligation.query))) :: caller
  apply expand_query_body_returns program agreement state environment outer request machine cursor tail free
  rw [query_state_shape]
  apply branch_returns program caller caller state _ (.symbol "None") queryAnswerCases
    (caseData (v "agenda") queryAgendaCases) _
  · have returned := QueryExecution.Parameterized.row_encoded_returns program lower QueryExecution.queryAnswerTerm
      caller state cursor machine.answers (v "cursor") (v "answers") (by
        simp [caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
    simpa [missing, encodeOption, CettaWireAtom.encode] using returned
  · simp [query_answer_cases_syntax, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · apply branch_returns program caller caller state _ (.symbol "LNil") queryAgendaCases queryEmptyBody _
    · simpa [caller, queryMachineCaller, empty, encodeList, applySubst, Subst.lookup, CettaWireAtom.encode] using
        variable_returns program caller state "agenda"
    · simp [query_agenda_cases_syntax, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · rw [empty_shape]
      apply named_let_returns program caller state "reasons" _
        (encoded (encodeList obligationTerm (machine.unresolved.map Execution.Obligation.query))) emptyData _
      · simp [caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, Subst.lookup]
      · exact query_obligations_captured_returns program agreement caller state machine.unresolved (v "unresolved")
          (by simp [caller, queryMachineCaller, applySubst, Subst.lookup])
      · unfold expansionValue Execution.expandQuery
        rw [missing]
        simp only [empty, List.isEmpty_nil, ↓reduceIte]
        exact (by
          simpa [emptyData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, final, caller, encodeOption, encodeList,
            applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program final state emptyData (empty_template program agreement))


theorem expand_query_progress_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (queryAgreement : ProgramAgreementOn QueryExecution.Parameterized.ownedHeads QueryExecution.runtime program)
    (schedulerAgreement : ProgramAgreementOn PremiseSchedulerExecution.executionHeads PremiseSchedulerExecution.runtime program)
    (lower : QueryExecution.Parameterized.LowerOperations program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations)
    (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.stateFreeWithin
      footprint environment request machine)
    (missing : machine.answers[cursor]? = none)
    (current : Query.Task environment request) (rest : List (Query.Task environment request))
    (agenda : machine.agenda = current :: rest) :
    PureReturns program [] state (a Helper.expand.head
      [environmentValue environment (environment.free.entriesOn footprint), taskValue (.query request machine cursor tail)]) state
      (expansionValue (Execution.expandQuery environment outer request machine cursor tail)) := by
  let free := environment.free.entriesOn footprint
  let caller := queryMachineCaller environment outer request machine cursor tail free
  let selected := [("queryRest", encoded (encodeList queryTaskTerm rest)), ("queryTask", encoded (queryTaskTerm current))] ++ caller
  let expanded := ("expanded", QueryExecution.expansionValue (Query.expand environment request current)) :: selected
  let final := ("nextState", encoded (queryStateTerm (Query.tick environment request machine))) :: expanded
  apply expand_query_body_returns program agreement state environment outer request machine cursor tail free
  rw [query_state_shape]
  apply branch_returns program caller caller state _ (.symbol "None") queryAnswerCases
    (caseData (v "agenda") queryAgendaCases) _
  · have returned := QueryExecution.Parameterized.row_encoded_returns program lower QueryExecution.queryAnswerTerm
      caller state cursor machine.answers (v "cursor") (v "answers") (by
        simp [caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, applySubst, Subst.lookup])
    simpa [missing, encodeOption, CettaWireAtom.encode] using returned
  · simp [query_answer_cases_syntax, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · apply branch_returns program caller selected state _ (encoded (encodeList queryTaskTerm (current :: rest)))
      queryAgendaCases queryProgressBody _
    · simpa [caller, queryMachineCaller, agenda, applySubst, Subst.lookup] using
        variable_returns program caller state "agenda"
    · simp [query_agenda_cases_syntax, selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller,
        queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names, encodeList,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
    · rw [progress_shape]
      apply named_let_returns program selected state "expanded" _
        (QueryExecution.expansionValue (Query.expand environment request current)) commitBody _
      · simp [selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
          taskCaller, environmentCaller, callee, Helper.names, Subst.lookup]
      · apply QueryExecution.Parameterized.helper_capture program queryAgreement .expand selected state
          [v "environment", v "request", v "queryTask"]
          [environmentValue environment free, QueryExecution.queryValue request, QueryExecution.taskValue current] _ rfl
        · simp [selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
            taskCaller, environmentCaller, callee, Helper.names, QueryExecution.taskValue, applySubst, Subst.lookup]
        · exact QueryExecution.Parameterized.Trajectory.query_expand_within_returns program queryAgreement lower
            state environment request current unregistered footprint provider (covered.1 current (by simp [agenda]))
      · unfold commitBody
        apply branch_returns program expanded final state _
          (encoded (encodeOption queryStateTerm (some (Query.tick environment request machine)))) commitCases pendingData _
        · exact query_commit_in_extension_returns program schedulerAgreement expanded state environment request machine current rest agenda
            [v "queryState", v "expanded"] (by
              simp [expanded, selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller, queryTaskCaller,
                taskCaller, environmentCaller, callee, Helper.names, QueryExecution.expansionValue,
                applySubst, Subst.lookup])
        · simp [commitCases, final, expanded, selected, caller, queryMachineCaller, queryContextCaller, queryRequestCaller,
            queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names, encodeOption,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
        · unfold expansionValue Execution.expandQuery
          rw [missing]
          simp only [agenda, List.isEmpty_cons]
          exact (by
            simpa [pendingData, expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, taskTerm, final, expanded, selected, caller, queryMachineCaller,
              queryContextCaller, queryRequestCaller, queryTaskCaller, taskCaller, environmentCaller, callee, Helper.names,
              QueryExecution.queryValue, queryRequestTerm, number, encodeOption, encodeList,
              applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return program final state pendingData (pending_template program agreement))

theorem expand_query_within_returns (program : Program)
    (agreement : ProgramAgreementOn ownedHeads runtime program)
    (queryAgreement : ProgramAgreementOn QueryExecution.Parameterized.ownedHeads QueryExecution.runtime program)
    (schedulerAgreement : ProgramAgreementOn PremiseSchedulerExecution.executionHeads PremiseSchedulerExecution.runtime program)
    (lower : QueryExecution.Parameterized.LowerOperations program)
    (state : State) (environment : Environment) (outer : Execution.Goal) (request : Query.Request)
    (machine : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (unregistered : request.relation ∉ environment.provider.dynamicRelations)
    (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (covered : Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.stateFreeWithin
      footprint environment request machine) :
    PureReturns program [] state (a Helper.expand.head
      [environmentValue environment (environment.free.entriesOn footprint), taskValue (.query request machine cursor tail)]) state
      (expansionValue (Execution.expand environment outer (.query request machine cursor tail))) := by
  cases found : machine.answers[cursor]? with
  | some answer => exact expand_query_answer_returns program agreement queryAgreement lower state environment outer request machine cursor tail _ answer found
  | none =>
      cases agenda : machine.agenda with
      | nil => exact expand_query_empty_returns program agreement lower state environment outer request machine cursor tail _ found agenda
      | cons current rest =>
          exact expand_query_progress_returns program agreement queryAgreement schedulerAgreement lower
            state environment outer request machine cursor tail unregistered footprint provider covered found current rest agenda


end QueryFrame

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution.EnvironmentExecution
