import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryFrames

/-!
# Typed continuation frames for authored premise execution

Each suspended frame retains the exact caller, assignment and authored
occurrence. Child searches are restricted by the caller's actual declaration
index and reuse the same root-firing machinery. Certificates record the
independent semantics of results, rather than a separate unproved oracle.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

inductive Goal where
  | premise (context : Context) (premise : Premise) (initial : Assignment)
  | premises (context : Context) (premises : List Premise) (initial : Assignment)
  | quantified (context : Context) (parameter : String) (body : Premise)
      (index : Nat) (elements : List Pattern) (initial : Assignment)
  | root (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
  | steps (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (limit : Nat)
  deriving Repr

inductive Result (environment : Environment) : Goal → Type where
  | premise {context : Context} {premise : Premise} {initial : Assignment}
      (assignment : Assignment) (event : Event)
      (valid : PremiseHolds environment context premise initial assignment event) :
      Result environment (.premise context premise initial)
  | premises {context : Context} {premises : List Premise} {initial : Assignment}
      (assignment : Assignment) (events : List Event)
      (valid : PremisesHold environment context premises initial assignment events) :
      Result environment (.premises context premises initial)
  | quantified {context : Context} {parameter : String} {body : Premise} {index : Nat}
      {elements : List Pattern} {initial : Assignment}
      (assignment : Assignment) (events : List (Nat × Pattern × List Event))
      (valid : QuantifiedElements environment context parameter body index elements
        initial assignment events) :
      Result environment (.quantified context parameter body index elements initial)
  | root {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {index : Nat}
      (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
      (events : List Event) (target : Pattern)
      (valid : RootFiring environment bound type source index trace captured completed events target) :
      Result environment (.root bound type source index)
  | steps {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {limit : Nat}
      (index : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
      (captured completed : Assignment) (events : List Event) (target : Pattern)
      (earlier : index < limit)
      (valid : RootFiring environment bound type source index trace captured completed events target) :
      Result environment (.steps bound type source limit)

structure StepCall (environment : Environment)
    (matcher : MatchingExecution := MatchingExecution.ordinary) where
  context : Context
  premise : Premise
  initial : Assignment
  binders : List TypeExpr
  type : TypeExpr
  source : Pattern
  targetSchema : Pattern
  conclude : ∀ index trace captured completed history target final targetTrace,
    Interpreted.RootFiring matcher.meaning environment (binders ++ context.bound) type source index trace captured completed
      history target →
    matcher.meaning.Matches ⟨context.rule, context.spec, context.bound.length,
      context.site 1, [], binders.length, initial, targetSchema, target⟩ targetTrace final →
    TypedAssignment environment context final →
    Interpreted.PremiseHolds matcher.meaning environment context premise initial final
      (.child context.premiseIndex context.quantifierDepth index (binders ++ context.bound)
        source target trace targetTrace captured completed history)

inductive Continuation (environment : Environment) : Goal → Goal → Type where
  | done (goal : Goal) : Continuation environment goal goal
  | nextPremise {outer : Goal} (context : Context) (premise : Premise)
      (premises : List Premise) (initial : Assignment)
      (tail : Continuation environment (.premises context (premise :: premises) initial) outer) :
      Continuation environment (.premise context premise initial) outer
  | prepend {outer : Goal} (context : Context) (premise : Premise)
      (premises : List Premise) (initial middle : Assignment) (event : Event)
      (head : PremiseHolds environment context premise initial middle event)
      (tail : Continuation environment (.premises context (premise :: premises) initial) outer) :
      Continuation environment (.premises context.next premises middle) outer
  | quantifier {outer : Goal} (context : Context) (collection parameter : String)
      (body : Premise) (initial : Assignment) (kind : CollType) (elements : List Pattern)
      (read : finiteCollection? context.bound.length initial collection = some (kind, elements))
      (tail : Continuation environment (.premise context (.forAll collection parameter body) initial) outer) :
      Continuation environment (.quantified context parameter body 0 elements initial) outer
  | element {outer : Goal} (context : Context) (parameter : String) (body : Premise)
      (index : Nat) (element : Pattern) (elements : List Pattern) (initial : Assignment)
      (localTyped : TypedAssignment environment context.quantified
        (bindParameter parameter (localValue context.bound element) initial))
      (tail : Continuation environment
        (.quantified context parameter body index (element :: elements) initial) outer) :
      Continuation environment
        (.premise context.quantified body
          (bindParameter parameter (localValue context.bound element) initial)) outer
  | prependElement {outer : Goal} (context : Context) (parameter : String) (body : Premise)
      (index : Nat) (element : Pattern) (elements : List Pattern) (initial middle : Assignment)
      (event : Event)
      (localTyped : TypedAssignment environment context.quantified
        (bindParameter parameter (localValue context.bound element) initial))
      (head : PremiseHolds environment context.quantified body
        (bindParameter parameter (localValue context.bound element) initial) middle event)
      (tail : Continuation environment
        (.quantified context parameter body index (element :: elements) initial) outer) :
      Continuation environment
        (.quantified context parameter body (index + 1) elements
          initial) outer
  | rootBody {outer : Goal} (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
      (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
      (declared : environment.language.rewrites[index]? = some rule)
      (specified : specification? environment index = some spec)
      (admitted : admittedFor rule spec = true)
      (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
      (trace : List GeneralScopedMatchMachine.BagChoice) (captured : Assignment)
      (matched : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 []
        rule.left source trace captured)
      (capturedTyped : TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured)
      (tail : Continuation environment (.root bound type source index) outer) :
      Continuation environment
        (.premises ⟨index, rule, spec, bound, 0, 0⟩ rule.premises captured) outer
  | searchedRoot {outer : Goal} (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
      (index limit : Nat) (earlier : index < limit)
      (tail : Continuation environment (.steps bound type source limit) outer) :
      Continuation environment (.root bound type source index) outer
  | stepped {outer : Goal} (call : StepCall environment)
      (tail : Continuation environment (.premise call.context call.premise call.initial) outer) :
      Continuation environment (.steps (call.binders ++ call.context.bound) call.type call.source
        call.context.ruleIndex) outer

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
  deriving Repr, DecidableEq

structure RootMatchFrame (environment : Environment) (outer : Goal) where
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
  state : GeneralScopedMatchMachine.State
  reachable : GeneralScopedMatchMachine.Reachable
    ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩ state
  cursor : Nat
  tail : Continuation environment (.root bound type source index) outer

structure TargetMatchFrame (environment : Environment) (outer : Goal) where
  call : StepCall environment
  index : Nat
  trace : List GeneralScopedMatchMachine.BagChoice
  captured : Assignment
  completed : Assignment
  history : List Event
  target : Pattern
  valid : RootFiring environment (call.binders ++ call.context.bound) call.type call.source index
    trace captured completed history target
  state : GeneralScopedMatchMachine.State
  reachable : GeneralScopedMatchMachine.Reachable
    ⟨call.context.rule, call.context.spec, call.context.bound.length, call.context.site 1,
      [], call.binders.length, call.initial, call.targetSchema, target⟩ state
  cursor : Nat
  tail : Continuation environment (.premise call.context call.premise call.initial) outer

inductive Task (environment : Environment) (outer : Goal) where
  | evaluate (goal : Goal) (tail : Continuation environment goal outer)
  | deliver {goal : Goal} (result : Result environment goal)
      (tail : Continuation environment goal outer)
  | query (request : Query.Request) (state : Query.State environment request) (cursor : Nat)
      (tail : Continuation environment
        (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
  | rootMatch (frame : RootMatchFrame environment outer)
  | targetMatch (frame : TargetMatchFrame environment outer)
  | scanChildren (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
      (limit cursor : Nat) (tail : Continuation environment (.steps bound type source limit) outer)

abbrev State (environment : Environment) (goal : Goal) :=
  Scheduler.State (Task environment goal) (Result environment goal) Obligation

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution
