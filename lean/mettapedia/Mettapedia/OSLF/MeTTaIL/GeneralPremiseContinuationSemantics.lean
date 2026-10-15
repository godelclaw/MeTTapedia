import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseOrder

/-!
# Independent meaning of suspended premise continuations

A continuation completes the semantic result already obtained by its caller.
Remaining premise and quantified branches use the independent relational
judgments. Their declaration-order condition is stated explicitly; it is
separate from the executable scheduling policy.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

def Concludes {environment : Environment} {goal outer : Goal}
    (tail : Continuation environment goal outer) (result : Result environment goal)
    (wanted : Result environment outer) : Prop :=
  match tail with
  | .done _ => result = wanted
  | .nextPremise context premise premises initial tail =>
      match result with
      | .premise middle event head =>
          ∃ (final : Assignment) (events : List Event) (rest : PremisesHold environment context.next premises middle final events),
            eventsOrdered context.ruleIndex events = true ∧
            Concludes tail (.premises final (event :: events) (.cons head rest)) wanted
  | .prepend _ _ _ _ _ event head tail =>
      match result with
      | .premises final events rest =>
          Concludes tail (.premises final (event :: events) (.cons head rest)) wanted
  | .quantifier context _ _ _ _ kind _ read tail =>
      match result with
      | .quantified final events held =>
          Concludes tail (.premise final
            (.quantified context.premiseIndex context.quantifierDepth kind events)
            (.quantified read held)) wanted
  | .element context parameter body index element elements initial localTyped tail =>
      match result with
      | .premise middle event head =>
          ∃ (final : Assignment) (events : List (Nat × Pattern × List Event)) (rest : QuantifiedElements environment context parameter body
              (index + 1) elements (restoreParameter parameter initial middle) final events),
            quantifiedOrdered context.ruleIndex events = true ∧
            Concludes tail (.quantified final ((index, element, [event]) :: events)
              (.cons localTyped head rest)) wanted
  | .prependElement _ _ _ index element _ _ _ event localTyped head tail =>
      match result with
      | .quantified final events rest =>
          Concludes tail (.quantified final ((index, element, [event]) :: events)
            (.cons localTyped head rest)) wanted
  | .rootBody bound type _ index rule spec declared specified admitted sorted trace captured
      matched capturedTyped tail =>
      match result with
      | .premises completed events held =>
          ∃ (target : Pattern) (converted : reductWith? (ScopedReflectiveExecution.binderOperation
              environment.reflection rule) rule spec bound.length completed = some target)
              (typed : OpenPatternWellSorted environment.language environment.free bound type target),
            Concludes tail (.root trace captured completed events target
              (.fire declared specified admitted sorted matched capturedTyped held converted typed)) wanted
  | .searchedRoot _ _ _ index _ earlier tail =>
      match result with
      | .root trace captured completed events target held =>
          Concludes tail (.steps index trace captured completed events target earlier held) wanted
  | .stepped call tail =>
      match result with
      | .steps index trace captured completed events target _ held =>
          ∃ (final : Assignment) (targetTrace : List GeneralScopedMatchMachine.BagChoice)
              (matched : GeneralScopedMatchMachine.TracedMatches call.context.rule call.context.spec
                call.context.bound.length (call.context.site 1) [] call.binders.length
                call.initial call.targetSchema target targetTrace final)
              (typed : TypedAssignment environment call.context final),
            Concludes tail (.premise final
              (.child call.context.premiseIndex call.context.quantifierDepth index
                (call.binders ++ call.context.bound) call.source target trace targetTrace
                captured completed events)
              (call.conclude _ _ _ _ _ _ _ _ held matched typed)) wanted

/-- Pending evaluations denote actual independent semantic results, together
with the meaning of the retained continuation. -/
def EvaluatesTo {environment : Environment} {goal outer : Goal}
    (tail : Continuation environment goal outer) (wanted : Result environment outer) : Prop :=
  ∃ result : Result environment goal, result.ordered = true ∧ Concludes tail result wanted

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution
