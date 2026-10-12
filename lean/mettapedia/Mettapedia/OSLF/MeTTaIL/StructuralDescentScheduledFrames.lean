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

abbrev StepCall := GeneralPremise.Execution.StepCall
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

inductive Result (environment : Environment) : Goal → Type where
  | premise {depth : Nat} {context : Context} {premise : Premise} {initial : Assignment}
      (assignment : Assignment) (event : Event)
      (valid : PremiseHolds environment context premise initial assignment event) :
      Result environment (.premise depth context premise initial)
  | premises {depth : Nat} {context : Context} {premises : List Premise} {initial : Assignment}
      (assignment : Assignment) (events : List Event)
      (valid : PremisesHold environment context premises initial assignment events) :
      Result environment (.premises depth context premises initial)
  | quantified {depth : Nat} {context : Context} {parameter : String} {body : Premise} {index : Nat}
      {elements : List Pattern} {initial : Assignment}
      (assignment : Assignment) (events : List (Nat × Pattern × List Event))
      (valid : QuantifiedElements environment context parameter body index elements
        initial assignment events) :
      Result environment (.quantified depth context parameter body index elements initial)
  | root {depth : Nat} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {index : Nat}
      (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
      (events : List Event) (target : Pattern)
      (valid : RootFiring environment bound type source index trace captured completed events target) :
      Result environment (.root depth bound type source index)
  | steps {depth : Nat} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {limit : Nat}
      (index : Nat) (trace : List GeneralScopedMatchMachine.BagChoice)
      (captured completed : Assignment) (events : List Event) (target : Pattern)
      (earlier : index < limit)
      (valid : RootFiring environment bound type source index trace captured completed events target) :
      Result environment (.steps depth bound type source limit)

inductive Continuation (environment : Environment) : Goal → Goal → Type where
  | done (goal : Goal) : Continuation environment goal goal
  | nextPremise {outer : Goal} (depth : Nat) (context : Context) (premise : Premise)
      (premises : List Premise) (initial : Assignment)
      (tail : Continuation environment (.premises depth context (premise :: premises) initial) outer) :
      Continuation environment (.premise depth context premise initial) outer
  | prepend {outer : Goal} (depth : Nat) (context : Context) (premise : Premise)
      (premises : List Premise) (initial middle : Assignment) (event : Event)
      (head : PremiseHolds environment context premise initial middle event)
      (tail : Continuation environment (.premises depth context (premise :: premises) initial) outer) :
      Continuation environment (.premises depth context.next premises middle) outer
  | quantifier {outer : Goal} (depth : Nat) (context : Context) (collection parameter : String)
      (body : Premise) (initial : Assignment) (kind : CollType) (elements : List Pattern)
      (read : finiteCollection? context.bound.length initial collection = some (kind, elements))
      (tail : Continuation environment (.premise depth context (.forAll collection parameter body) initial) outer) :
      Continuation environment (.quantified depth context parameter body 0 elements initial) outer
  | element {outer : Goal} (depth : Nat) (context : Context) (parameter : String) (body : Premise)
      (index : Nat) (element : Pattern) (elements : List Pattern) (initial : Assignment)
      (localTyped : TypedAssignment environment context.quantified
        (bindParameter parameter (localValue context.bound element) initial))
      (tail : Continuation environment
        (.quantified depth context parameter body index (element :: elements) initial) outer) :
      Continuation environment
        (.premise depth context.quantified body
          (bindParameter parameter (localValue context.bound element) initial)) outer
  | prependElement {outer : Goal} (depth : Nat) (context : Context) (parameter : String) (body : Premise)
      (index : Nat) (element : Pattern) (elements : List Pattern) (initial middle : Assignment)
      (event : Event)
      (localTyped : TypedAssignment environment context.quantified
        (bindParameter parameter (localValue context.bound element) initial))
      (head : PremiseHolds environment context.quantified body
        (bindParameter parameter (localValue context.bound element) initial) middle event)
      (tail : Continuation environment
        (.quantified depth context parameter body index (element :: elements) initial) outer) :
      Continuation environment
        (.quantified depth context parameter body (index + 1) elements
          (restoreParameter parameter initial middle)) outer
  | rootBody {outer : Goal} (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
      (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
      (declared : environment.language.rewrites[index]? = some rule)
      (specified : specification? environment index = some spec)
      (admitted : admittedFor rule spec = true)
      (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
      (trace : List GeneralScopedMatchMachine.BagChoice) (captured : Assignment)
      (matched : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 []
        rule.left source trace captured)
      (capturedTyped : TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured)
      (tail : Continuation environment (.root (depth + 1) bound type source index) outer) :
      Continuation environment
        (.premises depth ⟨index, rule, spec, bound, 0, 0⟩ rule.premises captured) outer
  | searchedRoot {outer : Goal} (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
      (index limit : Nat) (earlier : index < limit)
      (tail : Continuation environment (.steps depth bound type source limit) outer) :
      Continuation environment (.root depth bound type source index) outer
  | stepped {outer : Goal} (depth : Nat) (call : StepCall environment)
      (tail : Continuation environment (.premise depth call.context call.premise call.initial) outer) :
      Continuation environment (.steps depth (call.binders ++ call.context.bound) call.type call.source
        environment.language.rewrites.length) outer

structure RootMatchFrame (environment : Environment) (outer : Goal) where
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
  state : GeneralScopedMatchMachine.State
  reachable : GeneralScopedMatchMachine.Reachable
    ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩ state
  cursor : Nat
  tail : Continuation environment (.root (depth + 1) bound type source index) outer

structure TargetMatchFrame (environment : Environment) (outer : Goal) where
  depth : Nat
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
  tail : Continuation environment (.premise depth call.context call.premise call.initial) outer

inductive Task (environment : Environment) (outer : Goal) where
  | evaluate (goal : Goal) (tail : Continuation environment goal outer)
  | deliver {goal : Goal} (result : Result environment goal)
      (tail : Continuation environment goal outer)
  | query (depth : Nat) (request : Query.Request) (state : Query.State environment request) (cursor : Nat)
      (tail : Continuation environment
        (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer)
  | rootMatch (frame : RootMatchFrame environment outer)
  | targetMatch (frame : TargetMatchFrame environment outer)
  | scanChildren (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
      (limit cursor : Nat) (tail : Continuation environment (.steps depth bound type source limit) outer)

abbrev State (environment : Environment) (goal : Goal) :=
  Scheduler.State (Task environment goal) (Result environment goal) Obligation

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
