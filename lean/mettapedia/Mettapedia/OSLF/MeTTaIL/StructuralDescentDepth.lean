import Mettapedia.OSLF.MeTTaIL.StructuralDescentExecution

/-!
# Readable depth of actual recursive firing certificates

Depth counts nested authored rule firings, including child firings below
binders. Provider rows, freshness checks, and equation administration do not
create additional directed firings. Ordered history remains separate from
this maximum-depth readout.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent

open Syntax RuleBinding ScopedRuleMatching GeneralPremise

mutual
def eventDepth {Choice : Type} : Event Choice → Nat
  | .query _ _ _ _ | .freshness _ _ _ _ => 0
  | .child _ _ _ _ _ _ _ _ _ _ history => 1 + eventsDepth history
  | .quantified _ _ _ elements => elementsDepth elements
termination_by event => sizeOf event

def eventsDepth {Choice : Type} : List (Event Choice) → Nat
  | [] => 0
  | event :: events => max (eventDepth event) (eventsDepth events)
termination_by events => sizeOf events

def elementsDepth {Choice : Type} : List (Nat × Pattern × List (Event Choice)) → Nat
  | [] => 0
  | (_, _, history) :: elements => max (eventsDepth history) (elementsDepth elements)
termination_by elements => sizeOf elements
end

namespace Execution

def RootAnswer.requiredDepth {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern} (answer : RootAnswer environment bound type source) : Nat :=
  1 + eventsDepth answer.history

def OracleCompleteAt (environment : Environment) (oracle : Oracle environment) (depth : Nat) : Prop :=
  ∀ bound type source (answer : RootAnswer environment bound type source),
    answer.requiredDepth ≤ depth → answer ∈ oracle bound type source

theorem premiseAnswer_eq {environment : Environment} {context : Context} {premise : Premise}
    {initial : Assignment} {first second : PremiseAnswer environment context premise initial}
    (assignment : first.assignment = second.assignment) (event : first.event = second.event) :
    first = second := by
  cases first
  cases second
  cases assignment
  cases event
  rfl

theorem premisesAnswer_eq {environment : Environment} {context : Context} {premises : List Premise}
    {initial : Assignment} {first second : PremisesAnswer environment context premises initial}
    (assignment : first.assignment = second.assignment) (history : first.history = second.history) :
    first = second := by
  cases first
  cases second
  cases assignment
  cases history
  rfl

theorem elementsAnswer_eq {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial : Assignment} {first second : ElementsAnswer environment context parameter body index elements initial}
    (assignment : first.assignment = second.assignment) (history : first.history = second.history) :
    first = second := by
  cases first
  cases second
  cases assignment
  cases history
  rfl

theorem rootAnswer_eq {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {first second : RootAnswer environment bound type source}
    (index : first.index = second.index) (trace : first.trace = second.trace)
    (captured : first.captured = second.captured) (completed : first.completed = second.completed)
    (history : first.history = second.history) (target : first.target = second.target) :
    first = second := by
  cases first
  cases second
  cases index
  cases trace
  cases captured
  cases completed
  cases history
  cases target
  rfl

theorem runStep_selected {environment : Environment} {oracle : Oracle environment}
    (call : GeneralPremise.Execution.StepCall environment)
    (child : RootAnswer environment (call.binders ++ call.context.bound) call.type call.source)
    (listed : child ∈ oracle (call.binders ++ call.context.bound) call.type call.source)
    (assignment : Assignment) (targetTrace : List GeneralScopedMatchMachine.BagChoice)
    (matched : GeneralScopedMatchMachine.TracedMatches call.context.rule call.context.spec
      call.context.bound.length (call.context.site 1) [] call.binders.length call.initial
      call.targetSchema child.target targetTrace assignment)
    (typed : TypedAssignment environment call.context assignment) :
    ∃ answer ∈ runStep environment oracle call,
      answer.assignment = assignment ∧ answer.event =
        .child call.context.premiseIndex call.context.quantifierDepth child.index
          (call.binders ++ call.context.bound) call.source child.target child.trace targetTrace
          child.captured child.completed child.history := by
  let request : GeneralScopedMatchMachine.Request :=
    ⟨call.context.rule, call.context.spec, call.context.bound.length, call.context.site 1,
      [], call.binders.length, call.initial, call.targetSchema, child.target⟩
  let wanted : GeneralScopedMatchMachine.Answer := ⟨assignment, targetTrace⟩
  have valid : wanted.Valid request := matched
  obtain ⟨found, member, same⟩ := FiniteServices.Matcher.answers_complete request wanted valid
  have checked := checkTypedAssignment_complete typed
  refine ⟨⟨assignment, _, call.conclude _ _ _ _ _ _ _ _ child.valid matched typed⟩,
    ?_, rfl, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨child, listed, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨found, member, ?_⟩
  simp only [same, wanted, checked, ↓reduceDIte]

end Execution
end Mettapedia.OSLF.MeTTaIL.StructuralDescent
