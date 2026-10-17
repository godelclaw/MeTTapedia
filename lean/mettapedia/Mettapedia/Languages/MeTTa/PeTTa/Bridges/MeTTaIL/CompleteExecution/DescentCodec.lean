import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledTermination
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseMachineExecution.Core

/-!
# The scheduled descent machine as MeTTa data

Goals, results, continuations, tasks, obligations and states of
`StructuralDescent.Scheduled`, encoded as `gslt_descent_execution.metta` represents them. Every goal,
continuation and frame carries its recursion depth; proof fields are not encoded. Contexts, events,
step calls, query states and matcher states use the ordered premise machine's codecs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentCodec

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open StructuralDescent.Scheduled
open PremiseOperationsExecution.GeneralExecution (contextTerm eventTerm eventsTerm quantifiedEventsTerm
  stepCallTerm queryRequestTerm queryStateTerm queryObligationTerm matcherStateTerm traceTerm)

abbrev assignmentTerm (assignment : Assignment) : Term :=
  RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment
abbrev typesTerm (types : List TypeExpr) : Term := encodeList InferenceCettaWire.AuthoredRule.typeTerm types
abbrev typeTerm (type : TypeExpr) : Term := InferenceCettaWire.AuthoredRule.typeTerm type
abbrev patternTerm (pattern : Pattern) : Term := InferenceCettaWire.encodePattern pattern
abbrev patternsTerm (patterns : List Pattern) : Term := InferenceCettaWire.encodePatterns patterns
abbrev premiseTerm (premise : Premise) : Term := InferenceCettaWire.AuthoredRule.premiseTerm premise

def goalTerm : Goal → Term
  | .premise depth context premise initial => .application "DescentPremiseGoal"
      [.natural depth, contextTerm context, premiseTerm premise, assignmentTerm initial]
  | .premises depth context premises initial => .application "DescentPremisesGoal"
      [.natural depth, contextTerm context, encodeList premiseTerm premises, assignmentTerm initial]
  | .quantified depth context parameter body index elements initial => .application "DescentQuantifiedGoal"
      [.natural depth, contextTerm context, .string parameter, premiseTerm body, .natural index,
        patternsTerm elements, assignmentTerm initial]
  | .root depth bound type source index => .application "DescentRootGoal"
      [.natural depth, typesTerm bound, typeTerm type, patternTerm source, .natural index]
  | .steps depth bound type source limit => .application "DescentStepsGoal"
      [.natural depth, typesTerm bound, typeTerm type, patternTerm source, .natural limit]

def answerTerm {environment : Environment} {goal : Goal} : Result environment goal → Term
  | .premise assignment event _ => .application "PremiseAnswer" [assignmentTerm assignment, eventTerm event]
  | .premises assignment events _ => .application "PremisesAnswer" [assignmentTerm assignment, eventsTerm events]
  | .quantified assignment events _ =>
      .application "QuantifiedAnswer" [assignmentTerm assignment, quantifiedEventsTerm events]
  | .root trace captured completed events target _ => .application "RootAnswer"
      [traceTerm trace, assignmentTerm captured, assignmentTerm completed, eventsTerm events, patternTerm target]
  | .steps index trace captured completed events target _ _ => .application "StepsAnswer"
      [.natural index, traceTerm trace, assignmentTerm captured, assignmentTerm completed, eventsTerm events,
        patternTerm target]

def resultTerm {environment : Environment} {goal : Goal} (result : Result environment goal) : Term :=
  .application "PremiseResult" [goalTerm goal, answerTerm result]

def continuationTerm {environment : Environment} {goal outer : Goal} :
    Continuation environment goal outer → Term
  | .done goal => .application "DescentDone" [goalTerm goal]
  | .nextPremise depth context premise premises initial tail => .application "DescentNext"
      [.natural depth, contextTerm context, premiseTerm premise, encodeList premiseTerm premises,
        assignmentTerm initial, continuationTerm tail]
  | .prepend depth context premise premises initial middle event _ tail => .application "DescentPrepend"
      [.natural depth, contextTerm context, premiseTerm premise, encodeList premiseTerm premises,
        assignmentTerm initial, assignmentTerm middle, eventTerm event, continuationTerm tail]
  | .quantifier depth context collection parameter body initial kind elements _ tail =>
      .application "DescentQuantifier" [.natural depth, contextTerm context, .string collection,
        .string parameter, premiseTerm body, assignmentTerm initial, InferenceCettaWire.encodeCollectionType kind,
        patternsTerm elements, continuationTerm tail]
  | .element depth context parameter body index element elements initial _ tail => .application "DescentElement"
      [.natural depth, contextTerm context, .string parameter, premiseTerm body, .natural index,
        patternTerm element, patternsTerm elements, assignmentTerm initial, continuationTerm tail]
  | .prependElement depth context parameter body index element elements initial middle event _ _ tail =>
      .application "DescentPrependElement" [.natural depth, contextTerm context, .string parameter,
        premiseTerm body, .natural index, patternTerm element, patternsTerm elements, assignmentTerm initial,
        assignmentTerm middle, eventTerm event, continuationTerm tail]
  | .rootBody depth bound type source index rule spec _ _ _ _ trace captured _ _ tail =>
      .application "DescentRootBody" [.natural depth, typesTerm bound, typeTerm type, patternTerm source,
        .natural index, InferenceCettaWire.AuthoredRule.rewriteTerm rule,
        InferenceCettaWire.AuthoredRule.bindingSpecTerm spec, traceTerm trace, assignmentTerm captured,
        continuationTerm tail]
  | .searchedRoot depth bound type source index limit _ tail => .application "DescentSearchedRoot"
      [.natural depth, typesTerm bound, typeTerm type, patternTerm source, .natural index, .natural limit,
        continuationTerm tail]
  | .stepped depth call tail => .application "DescentStepped" [.natural depth, stepCallTerm call, continuationTerm tail]

def taskTerm {environment : Environment} {outer : Goal} : Task environment outer → Term
  | .evaluate goal tail => .application "DescentEvaluate" [goalTerm goal, continuationTerm tail]
  | .deliver result tail => .application "DescentDeliver" [resultTerm result, continuationTerm tail]
  | .query depth request state cursor tail => .application "DescentQuery"
      [.natural depth, queryRequestTerm request, queryStateTerm state, .natural cursor, continuationTerm tail]
  | .rootMatch frame => .application "DescentRootMatch"
      [.natural frame.depth, typesTerm frame.bound, typeTerm frame.type, patternTerm frame.source,
        .natural frame.index, InferenceCettaWire.AuthoredRule.rewriteTerm frame.rule,
        InferenceCettaWire.AuthoredRule.bindingSpecTerm frame.spec, matcherStateTerm frame.state,
        .natural frame.cursor, continuationTerm frame.tail]
  | .targetMatch frame => .application "DescentTargetMatch"
      [.natural frame.depth, stepCallTerm frame.call, .natural frame.index, traceTerm frame.trace,
        assignmentTerm frame.captured, assignmentTerm frame.completed, eventsTerm frame.history,
        patternTerm frame.target, matcherStateTerm frame.state, .natural frame.cursor, continuationTerm frame.tail]
  | .scanChildren depth bound type source limit cursor tail => .application "DescentScanChildren"
      [.natural depth, typesTerm bound, typeTerm type, patternTerm source, .natural limit, .natural cursor,
        continuationTerm tail]

def obligationTerm : Obligation → Term
  | .query reason => .application "PremiseQueryObligation" [queryObligationTerm reason]
  | .freshnessProjection index quantifiers =>
      .application "PremiseFreshnessProjection" [.natural index, .natural quantifiers]
  | .collectionProjection index quantifiers collection => .application "PremiseCollectionProjection"
      [.natural index, .natural quantifiers, .string collection]
  | .quantifiedAssignment index quantifiers element => .application "PremiseQuantifiedAssignment"
      [.natural index, .natural quantifiers, .natural element]
  | .stepProjection index quantifiers => .application "PremiseStepProjection" [.natural index, .natural quantifiers]
  | .stepSort index quantifiers => .application "PremiseStepSort" [.natural index, .natural quantifiers]
  | .ruleUnavailable index => .application "PremiseRuleUnavailable" [.natural index]
  | .bindingUnavailable index => .application "PremiseBindingUnavailable" [.natural index]
  | .bindingRejected index => .application "PremiseBindingRejected" [.natural index]
  | .sourceRejected index => .application "PremiseSourceRejected" [.natural index]
  | .targetProjection index => .application "PremiseTargetProjection" [.natural index]
  | .depthExhausted index => .application "DescentDepthExhausted" [.natural index]

def expansionTerm {environment : Environment} {outer : Goal}
    (expansion : Scheduler.Expansion (Task environment outer) (Result environment outer) Obligation) : Term :=
  PremiseSchedulerExecution.schedulerExpansionTerm taskTerm resultTerm obligationTerm expansion

def stateTerm {environment : Environment} {outer : Goal} (state : State environment outer) : Term :=
  PremiseSchedulerExecution.schedulerStateTerm taskTerm resultTerm obligationTerm state

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentCodec
