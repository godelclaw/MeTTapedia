import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledExecution

/-!
# Equations of the scheduled descent machine's delivery

`delivered` matches on its continuation and then on its result. The inner match is on a result of
an indexed family, which `simp` does not reduce; these equations state each case directly, by
definition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {environment : Environment} {outer : Goal}

@[simp] theorem delivered_done {goal : Goal} (result : Result environment goal) :
    delivered environment goal result (.done goal) = { answers := [result] } := rfl

@[simp] theorem delivered_nextPremise {depth : Nat} {context : Context} {premise : Premise}
    {premises : List Premise} {initial assignment : Assignment} {event : Event}
    (valid : PremiseHolds environment context premise initial assignment event)
    (tail : Continuation environment (.premises depth context (premise :: premises) initial) outer) :
    delivered environment outer (.premise assignment event valid) (.nextPremise depth context premise premises initial tail) =
      { tasks := [.evaluate (.premises depth context.next premises assignment)
          (.prepend depth context premise premises initial assignment event valid tail)] } := rfl

@[simp] theorem delivered_prepend {depth : Nat} {context : Context} {premise : Premise}
    {premises : List Premise} {initial middle assignment : Assignment} {event : Event} {events : List Event}
    (head : PremiseHolds environment context premise initial middle event)
    (valid : PremisesHold environment context.next premises middle assignment events)
    (tail : Continuation environment (.premises depth context (premise :: premises) initial) outer) :
    delivered environment outer (.premises assignment events valid)
        (.prepend depth context premise premises initial middle event head tail) =
      { tasks := [.deliver (.premises assignment (event :: events) (.cons head valid)) tail] } := rfl

@[simp] theorem delivered_quantifier {depth : Nat} {context : Context} {collection parameter : String}
    {body : Premise} {initial assignment : Assignment} {kind : CollType} {elements : List Pattern}
    {events : List (Nat × Pattern × List Event)}
    (read : finiteCollection? context.bound.length initial collection = some (kind, elements))
    (valid : QuantifiedElements environment context parameter body 0 elements initial assignment events)
    (tail : Continuation environment (.premise depth context (.forAll collection parameter body) initial) outer) :
    delivered environment outer (.quantified assignment events valid)
        (.quantifier depth context collection parameter body initial kind elements read tail) =
      { tasks := [.deliver (.premise assignment
          (.quantified context.premiseIndex context.quantifierDepth kind events) (.quantified read valid)) tail] } := rfl

@[simp] theorem delivered_element {depth : Nat} {context : Context} {parameter : String} {body : Premise}
    {index : Nat} {element : Pattern} {elements : List Pattern} {initial assignment : Assignment} {event : Event}
    (localTyped : TypedAssignment environment context.quantified
      (bindParameter parameter (localValue context.bound element) initial))
    (valid : PremiseHolds environment context.quantified body
      (bindParameter parameter (localValue context.bound element) initial) assignment event)
    (tail : Continuation environment (.quantified depth context parameter body index (element :: elements) initial) outer) :
    delivered environment outer (.premise assignment event valid)
        (.element depth context parameter body index element elements initial localTyped tail) =
      { tasks := [.evaluate
          (.quantified depth context parameter body (index + 1) elements (restoreParameter parameter initial assignment))
          (.prependElement depth context parameter body index element elements initial assignment
            event localTyped valid tail)] } := rfl

@[simp] theorem delivered_prependElement {depth : Nat} {context : Context} {parameter : String} {body : Premise}
    {index : Nat} {element : Pattern} {elements : List Pattern} {initial middle assignment : Assignment}
    {event : Event} {events : List (Nat × Pattern × List Event)}
    (localTyped : TypedAssignment environment context.quantified
      (bindParameter parameter (localValue context.bound element) initial))
    (head : PremiseHolds environment context.quantified body
      (bindParameter parameter (localValue context.bound element) initial) middle event)
    (valid : QuantifiedElements environment context parameter body (index + 1) elements
      (restoreParameter parameter initial middle) assignment events)
    (tail : Continuation environment (.quantified depth context parameter body index (element :: elements) initial) outer) :
    delivered environment outer (.quantified assignment events valid)
        (.prependElement depth context parameter body index element elements initial middle event localTyped head tail) =
      { tasks := [.deliver (.quantified assignment ((index, element, [event]) :: events)
          (.cons localTyped head valid)) tail] } := rfl

@[simp] theorem delivered_searchedRoot {depth : Nat} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    {index limit : Nat} {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {events : List Event} {target : Pattern} (earlier : index < limit)
    (valid : RootFiring environment bound type source index trace captured completed events target)
    (tail : Continuation environment (.steps depth bound type source limit) outer) :
    delivered environment outer (.root trace captured completed events target valid)
        (.searchedRoot depth bound type source index limit earlier tail) =
      { tasks := [.deliver (.steps index trace captured completed events target earlier valid) tail] } := rfl

@[simp] theorem delivered_stepped {depth : Nat} {call : StepCall environment} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment} {events : List Event}
    {target : Pattern} (earlier : index < environment.language.rewrites.length)
    (valid : RootFiring environment (call.binders ++ call.context.bound) call.type call.source index trace captured
      completed events target)
    (tail : Continuation environment (.premise depth call.context call.premise call.initial) outer) :
    delivered environment outer (.steps index trace captured completed events target earlier valid) (.stepped depth call tail) =
      { tasks := [.targetMatch {
          depth := depth, call := call, index := index, trace := trace, captured := captured, completed := completed,
          history := events, target := target, valid := valid
          state := GeneralScopedMatchMachine.start ⟨call.context.rule, call.context.spec, call.context.bound.length,
            call.context.site 1, [], call.binders.length, call.initial, call.targetSchema, target⟩
          reachable := .start, cursor := 0, tail := tail }] } := rfl

section RootBody

variable {depth : Nat} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern} {index : Nat}
  {rule : RewriteRule} {spec : RuleBindingSpec} (declared : environment.language.rewrites[index]? = some rule)
  (specified : specification? environment index = some spec) (admitted : admittedFor rule spec = true)
  (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
  {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment} {events : List Event}
  (matched : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 [] rule.left source trace captured)
  (capturedTyped : TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured)
  (valid : PremisesHold environment ⟨index, rule, spec, bound, 0, 0⟩ rule.premises captured completed events)
  (tail : Continuation environment (.root (depth + 1) bound type source index) outer)

theorem delivered_rootBody_none
    (none : reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule) rule spec bound.length
      completed = none) :
    delivered environment outer (.premises completed events valid)
      (.rootBody depth bound type source index rule spec declared specified admitted sorted trace captured matched
        capturedTyped tail) = { unresolved := [.targetProjection index] } := by
  simp only [delivered]
  split
  · rfl
  · rename_i found
    rw [none] at found
    cases found

theorem delivered_rootBody_sorted {target : Pattern}
    (converted : reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule) rule spec
      bound.length completed = some target)
    (checked : checkOpenPatternWellSorted environment.language environment.free bound type target = true) :
    delivered environment outer (.premises completed events valid)
      (.rootBody depth bound type source index rule spec declared specified admitted sorted trace captured matched
        capturedTyped tail) =
      { tasks := [.deliver (.root trace captured completed events target
          (.fire declared specified admitted sorted matched capturedTyped valid converted
            (checkOpenPatternWellSorted_sound checked))) tail] } := by
  simp only [delivered]
  split
  · rename_i found
    rw [converted] at found
    cases found
  · rename_i other found
    rw [converted] at found
    cases found
    simp [checked]

theorem delivered_rootBody_unsorted {target : Pattern}
    (converted : reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule) rule spec
      bound.length completed = some target)
    (unchecked : checkOpenPatternWellSorted environment.language environment.free bound type target = false) :
    delivered environment outer (.premises completed events valid)
      (.rootBody depth bound type source index rule spec declared specified admitted sorted trace captured matched
        capturedTyped tail) = {} := by
  simp only [delivered]
  split
  · rename_i found
    rw [converted] at found
    cases found
  · rename_i other found
    rw [converted] at found
    cases found
    simp [unchecked]

end RootBody

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
