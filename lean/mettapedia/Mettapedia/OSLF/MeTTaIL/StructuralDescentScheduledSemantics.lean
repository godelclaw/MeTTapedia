import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledExecution

/-!
# Independent semantics of structurally bounded continuations

Suspended work denotes the original relational derivations, restricted only
by the retained recursion depth. Continuations retain independent premise,
quantifier, matcher, typing and reduct witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The declaration order is unrestricted. The bound measures the nesting
of actual child-event certificates, not declaration indices. -/
def Interpreted.Result.ordered {matcher : MatchingExecution} {environment : Environment} {goal : Goal}
    (result : Interpreted.Result matcher environment goal) : Bool :=
  match goal, result with
  | .premise depth _ _ _, .premise _ event _ => decide (eventDepth event ≤ depth)
  | .premises depth _ _ _, .premises _ events _ => decide (eventsDepth events ≤ depth)
  | .quantified depth _ _ _ _ _ _, .quantified _ events _ => decide (elementsDepth events ≤ depth)
  | .root depth _ _ _ _, .root _ _ _ events _ _ => decide (1 + eventsDepth events ≤ depth)
  | .steps depth _ _ _ _, .steps _ _ _ _ events _ _ _ => decide (1 + eventsDepth events ≤ depth)

def Concludes {matcher : MatchingExecution} {environment : Environment} {goal outer : Goal}
    (tail : Interpreted.Continuation matcher environment goal outer) (result : Interpreted.Result matcher environment goal)
    (wanted : Interpreted.Result matcher environment outer) : Prop :=
  match tail with
  | .done _ => result = wanted
  | .nextPremise depth context premise premises initial tail =>
      match result with
      | .premise middle event head =>
          ∃ (final : Assignment) (events : List (Event matcher.Choice)) (rest : GeneralPremise.Interpreted.PremisesHold matcher.meaning environment context.next premises middle final events),
            eventsDepth events ≤ depth ∧
            Concludes tail (.premises final (event :: events) (.cons head rest)) wanted
  | .prepend depth _ _ _ _ _ event head tail =>
      match result with
      | .premises final events rest =>
          Concludes tail (.premises final (event :: events) (.cons head rest)) wanted
  | .quantifier depth context _ _ _ _ kind _ read tail =>
      match result with
      | .quantified final events held =>
          Concludes tail (.premise final
            (.quantified context.premiseIndex context.quantifierDepth kind events)
            (.quantified read held)) wanted
  | .element depth context parameter body index element elements initial localTyped tail =>
      match result with
      | .premise _middle event head =>
          ∃ (final : Assignment) (events : List (Nat × Pattern × List (Event matcher.Choice))) (rest : GeneralPremise.Interpreted.QuantifiedElements matcher.meaning environment context parameter body
              (index + 1) elements initial final events),
            elementsDepth events ≤ depth ∧
            Concludes tail (.quantified final ((index, element, [event]) :: events)
              (.cons localTyped head rest)) wanted
  | .prependElement depth _ _ _ index element _ _ _ event localTyped head tail =>
      match result with
      | .quantified final events rest =>
          Concludes tail (.quantified final ((index, element, [event]) :: events)
            (.cons localTyped head rest)) wanted
  | .rootBody depth bound type _ index rule spec declared specified admitted sorted trace captured
      matched capturedTyped tail =>
      match result with
      | .premises completed events held =>
          ∃ (target : Pattern) (converted : reductWith? (ScopedReflectiveExecution.binderOperation
              environment.reflection rule) rule spec bound.length completed = some target)
              (typed : OpenPatternWellSorted environment.language environment.free bound type target),
            Concludes tail (.root trace captured completed events target
              (.fire declared specified admitted sorted matched capturedTyped held converted typed)) wanted
  | .searchedRoot depth _ _ _ index _ earlier tail =>
      match result with
      | .root trace captured completed events target held =>
          Concludes tail (.steps index trace captured completed events target earlier held) wanted
  | .stepped depth call tail =>
      match result with
      | .steps index trace captured completed events target _ held =>
          ∃ (final : Assignment) (targetTrace : List matcher.Choice)
              (matched : matcher.meaning.Matches ⟨call.context.rule, call.context.spec,
                call.context.bound.length, call.context.site 1, [], call.binders.length,
                call.initial, call.targetSchema, target⟩ targetTrace final)
              (typed : TypedAssignment environment call.context final),
            Concludes tail (.premise final
              (.child call.context.premiseIndex call.context.quantifierDepth index
                (call.binders ++ call.context.bound) call.source target trace targetTrace
                captured completed events)
              (call.conclude _ _ _ _ _ _ _ _ held matched typed)) wanted

/-- Pending evaluations denote actual independent semantic results, together
with the meaning of the retained continuation. -/
def EvaluatesTo {matcher : MatchingExecution} {environment : Environment} {goal outer : Goal}
    (tail : Interpreted.Continuation matcher environment goal outer) (wanted : Interpreted.Result matcher environment outer) : Prop :=
  ∃ result : Interpreted.Result matcher environment goal, result.ordered = true ∧ Concludes tail result wanted

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
