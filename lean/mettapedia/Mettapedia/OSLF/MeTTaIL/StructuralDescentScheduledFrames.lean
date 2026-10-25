import Mettapedia.OSLF.MeTTaIL.StructuralDescentCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryFrames

/-!
# Suspended scoped execution with structural recursion depth

All authored declaration indices are searched at every recursive call.
A root at depth `d+1` runs its premise calls at depth `d`; the structural
admission theorem earns the sufficient initial depth from the actual source.
Frames retain matcher states, provider states, assignments and continuations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled

open Syntax RuleBinding ScopedRuleMatching GeneralPremise

abbrev StepCall (environment : Environment)
    (matcher : MatchingExecution := MatchingExecution.ordinary) :=
  GeneralPremise.Execution.StepCall environment matcher
inductive Obligation where
  | query (reason : Query.Obligation)
  | freshnessProjection (premiseIndex quantifierDepth : Nat)
  | collectionProjection (premiseIndex quantifierDepth : Nat) (collection : String)
  | quantifiedAssignment (premiseIndex quantifierDepth elementIndex : Nat)
  | stepProjection (premiseIndex quantifierDepth : Nat)
  | stepSort (premiseIndex quantifierDepth : Nat)
  | ruleUnavailable (index : Nat)
  | bindingUnavailable (index : Nat)
  | bindingRejected (index : Nat)
  | sourceRejected (index : Nat)
  | targetProjection (index : Nat)
  | depthExhausted (index : Nat)
  deriving Repr, DecidableEq
open Mettapedia.GSLT.LanguageDef.WellSorted

inductive Goal where
  | premise (depth : Nat) (context : Context) (premise : Premise) (initial : Assignment)
  | premises (depth : Nat) (context : Context) (premises : List Premise) (initial : Assignment)
  | quantified (depth : Nat) (context : Context) (parameter : String) (body : Premise)
      (index : Nat) (elements : List Pattern) (initial : Assignment)
  | root (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
  | steps (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (limit : Nat)
  deriving Repr

namespace Interpreted

inductive Result (matcher : MatchingExecution) (environment : Environment) : Goal → Type where
  | premise {depth : Nat} {context : Context} {premise : Premise} {initial : Assignment}
      (assignment : Assignment) (event : Event matcher.Choice)
      (valid : GeneralPremise.Interpreted.PremiseHolds matcher.meaning environment context premise initial assignment event) :
      Result matcher environment (.premise depth context premise initial)
  | premises {depth : Nat} {context : Context} {premises : List Premise} {initial : Assignment}
      (assignment : Assignment) (events : List (Event matcher.Choice))
      (valid : GeneralPremise.Interpreted.PremisesHold matcher.meaning environment context premises initial assignment events) :
      Result matcher environment (.premises depth context premises initial)
  | quantified {depth : Nat} {context : Context} {parameter : String} {body : Premise} {index : Nat}
      {elements : List Pattern} {initial : Assignment}
      (assignment : Assignment) (events : List (Nat × Pattern × List (Event matcher.Choice)))
      (valid : GeneralPremise.Interpreted.QuantifiedElements matcher.meaning environment context parameter body index elements
        initial assignment events) :
      Result matcher environment (.quantified depth context parameter body index elements initial)
  | root {depth : Nat} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {index : Nat}
      (trace : List matcher.Choice) (captured completed : Assignment)
      (events : List (Event matcher.Choice)) (target : Pattern)
      (valid : GeneralPremise.Interpreted.RootFiring matcher.meaning environment bound type source index trace captured completed events target) :
      Result matcher environment (.root depth bound type source index)
  | steps {depth : Nat} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {limit : Nat}
      (index : Nat) (trace : List matcher.Choice)
      (captured completed : Assignment) (events : List (Event matcher.Choice)) (target : Pattern)
      (earlier : index < limit)
      (valid : GeneralPremise.Interpreted.RootFiring matcher.meaning environment bound type source index trace captured completed events target) :
      Result matcher environment (.steps depth bound type source limit)

inductive Continuation (matcher : MatchingExecution) (environment : Environment) : Goal → Goal → Type where
  | done (goal : Goal) : Continuation matcher environment goal goal
  | nextPremise {outer : Goal} (depth : Nat) (context : Context) (premise : Premise)
      (premises : List Premise) (initial : Assignment)
      (tail : Continuation matcher environment (.premises depth context (premise :: premises) initial) outer) :
      Continuation matcher environment (.premise depth context premise initial) outer
  | prepend {outer : Goal} (depth : Nat) (context : Context) (premise : Premise)
      (premises : List Premise) (initial middle : Assignment) (event : Event matcher.Choice)
      (head : GeneralPremise.Interpreted.PremiseHolds matcher.meaning environment context premise initial middle event)
      (tail : Continuation matcher environment (.premises depth context (premise :: premises) initial) outer) :
      Continuation matcher environment (.premises depth context.next premises middle) outer
  | quantifier {outer : Goal} (depth : Nat) (context : Context) (collection parameter : String)
      (body : Premise) (initial : Assignment) (kind : CollType) (elements : List Pattern)
      (read : finiteCollection? context.bound.length initial collection = some (kind, elements))
      (tail : Continuation matcher environment (.premise depth context (.forAll collection parameter body) initial) outer) :
      Continuation matcher environment (.quantified depth context parameter body 0 elements initial) outer
  | element {outer : Goal} (depth : Nat) (context : Context) (parameter : String) (body : Premise)
      (index : Nat) (element : Pattern) (elements : List Pattern) (initial : Assignment)
      (localTyped : TypedAssignment environment context.quantified
        (bindParameter parameter (localValue context.bound element) initial))
      (tail : Continuation matcher environment
        (.quantified depth context parameter body index (element :: elements) initial) outer) :
      Continuation matcher environment
        (.premise depth context.quantified body
          (bindParameter parameter (localValue context.bound element) initial)) outer
  | prependElement {outer : Goal} (depth : Nat) (context : Context) (parameter : String) (body : Premise)
      (index : Nat) (element : Pattern) (elements : List Pattern) (initial middle : Assignment)
      (event : Event matcher.Choice)
      (localTyped : TypedAssignment environment context.quantified
        (bindParameter parameter (localValue context.bound element) initial))
      (head : GeneralPremise.Interpreted.PremiseHolds matcher.meaning environment context.quantified body
        (bindParameter parameter (localValue context.bound element) initial) middle event)
      (tail : Continuation matcher environment
        (.quantified depth context parameter body index (element :: elements) initial) outer) :
      Continuation matcher environment
        (.quantified depth context parameter body (index + 1) elements
          initial) outer
  | rootBody {outer : Goal} (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
      (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
      (declared : environment.language.rewrites[index]? = some rule)
      (specified : specification? environment index = some spec)
      (admitted : admittedFor rule spec = true)
      (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
      (trace : List matcher.Choice) (captured : Assignment)
      (matched : matcher.meaning.Matches ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
        trace captured)
      (capturedTyped : TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured)
      (tail : Continuation matcher environment (.root (depth + 1) bound type source index) outer) :
      Continuation matcher environment
        (.premises depth ⟨index, rule, spec, bound, 0, 0⟩ rule.premises captured) outer
  | searchedRoot {outer : Goal} (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
      (index limit : Nat) (earlier : index < limit)
      (tail : Continuation matcher environment (.steps depth bound type source limit) outer) :
      Continuation matcher environment (.root depth bound type source index) outer
  | stepped {outer : Goal} (depth : Nat) (call : StepCall environment matcher)
      (tail : Continuation matcher environment (.premise depth call.context call.premise call.initial) outer) :
      Continuation matcher environment (.steps depth (call.binders ++ call.context.bound) call.type call.source
        environment.language.rewrites.length) outer

end Interpreted

/-- The class backend is the ordinary specialization of the shared frames. -/
abbrev Result (environment : Environment) := Interpreted.Result MatchingExecution.ordinary environment
namespace Result
export Interpreted.Result (premise premises quantified root steps)
end Result

abbrev Continuation (environment : Environment) :=
  Interpreted.Continuation MatchingExecution.ordinary environment
namespace Continuation
export Interpreted.Continuation (done nextPremise prepend quantifier element prependElement rootBody searchedRoot stepped)
end Continuation

structure RootMatchFrame (environment : Environment) (outer : Goal)
    (matcher : MatchingExecution := MatchingExecution.ordinary) where
  depth : Nat
  bound : List TypeExpr
  type : TypeExpr
  source : Pattern
  index : Nat
  rule : RewriteRule
  spec : RuleBindingSpec
  declared : environment.language.rewrites[index]? = some rule
  specified : specification? environment index = some spec
  admitted : admittedFor rule spec = true
  sorted : OpenPatternWellSorted environment.language environment.free bound type source
  state : matcher.State
  reachable : matcher.Reachable
    ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩ state
  cursor : Nat
  tail : Interpreted.Continuation matcher environment (.root (depth + 1) bound type source index) outer

structure TargetMatchFrame (environment : Environment) (outer : Goal)
    (matcher : MatchingExecution := MatchingExecution.ordinary) where
  depth : Nat
  call : StepCall environment matcher
  index : Nat
  trace : List matcher.Choice
  captured : Assignment
  completed : Assignment
  history : List (Event matcher.Choice)
  target : Pattern
  valid : GeneralPremise.Interpreted.RootFiring matcher.meaning environment (call.binders ++ call.context.bound) call.type call.source index
    trace captured completed history target
  state : matcher.State
  reachable : matcher.Reachable
    ⟨call.context.rule, call.context.spec, call.context.bound.length, call.context.site 1,
      [], call.binders.length, call.initial, call.targetSchema, target⟩ state
  cursor : Nat
  tail : Interpreted.Continuation matcher environment (.premise depth call.context call.premise call.initial) outer

namespace Interpreted

inductive Task (matcher : MatchingExecution) (environment : Environment) (outer : Goal) where
  | evaluate (goal : Goal) (tail : Continuation matcher environment goal outer)
  | deliver {goal : Goal} (result : Result matcher environment goal)
      (tail : Continuation matcher environment goal outer)
  | query (depth : Nat) (request : Query.Request) (state : Query.State environment request matcher) (cursor : Nat)
      (tail : Continuation matcher environment
        (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer)
  | rootMatch (frame : RootMatchFrame environment outer matcher)
  | targetMatch (frame : TargetMatchFrame environment outer matcher)
  | scanChildren (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
      (limit cursor : Nat) (tail : Continuation matcher environment (.steps depth bound type source limit) outer)

end Interpreted

abbrev Task (environment : Environment) (outer : Goal) :=
  Interpreted.Task MatchingExecution.ordinary environment outer
namespace Task
export Interpreted.Task (evaluate deliver query rootMatch targetMatch scanChildren)
end Task

abbrev State (environment : Environment) (goal : Goal)
    (matcher : MatchingExecution := MatchingExecution.ordinary) :=
  Scheduler.State (Interpreted.Task matcher environment goal)
    (Interpreted.Result matcher environment goal) Obligation

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
