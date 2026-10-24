import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticContracts
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseResolvedTrees

/-!
# Complete resolution of statically admitted authored work

Static syntax and provider refinements construct a clean tree containing all
actual continuation branches. Child searches use every earlier authored
declaration and retain the full typed local context. Tree uniqueness then
establishes resolution of the ordinary executor for arbitrary admitted inputs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open Execution

def resolvedEvaluate (environment : Environment) (language : checkLanguage environment = true)
    (services : DynamicAvailability environment)
    (outer goal : Goal) (admitted : GoalAdmitted environment goal)
    (tail : Continuation environment goal outer) (continued : ResolvedContinued environment outer goal tail) :
    ResolvedTree environment outer (.evaluate goal tail) := by
  apply ResolvedTree.branch
  · exact checkGoalReady_sound environment outer goal tail (admitted.ready language)
  · cases goal with
    | premises context premises initial =>
      cases admitted with
      | premises refinement facts zero depth supported stratum =>
        cases premises with
        | nil => exact .cons (continued (.premises initial [] .nil)) (.nil _ _)
        | cons premise premises =>
          simp only [premisesFlow, Bool.and_eq_true] at supported
          have headChecked : (premiseFlow environment.language environment.provider context.rule context.spec
              context.premiseIndex context.quantifierDepth refinement premise).supported = true := by
            simpa only [depth] using supported.1
          refine .cons (resolvedEvaluate environment language services outer (.premise context premise initial)
            (.premise refinement facts zero headChecked stratum) _ ?_) (.nil _ _)
          intro result
          cases result with
          | premise middle event head =>
            apply ResolvedTree.branch rfl
            have after := facts.afterPremise head
            rw [depth] at after
            refine .cons (resolvedEvaluate environment language services outer
              (.premises context.next premises middle)
              (.premises _ ⟨after.typed, after.canonical, after.represented⟩
                zero rfl supported.2 stratum) _ ?_) (.nil _ _)
            intro result
            cases result with
            | premises final history rest =>
              exact .branch rfl (.cons (continued _) (.nil _ _))
    | quantified context parameter body index elements initial =>
      cases admitted with
      | quantified refinement elementType facts zero parameterType parameterDependencies
          elementsTyped elementsObjects elementsCanonical supported stratum =>
        cases elements with
        | nil => exact .cons (continued (.quantified initial [] .nil)) (.nil _ _)
        | cons element elements =>
          have elementTyped : HasType environment.language environment.free context.bound element elementType := by
            cases elementsTyped with
            | cons head _ => exact head
          have tailTyped : ElementsHaveType environment.language environment.free context.bound elements elementType := by
            cases elementsTyped with
            | cons _ tail => exact tail
          simp only [isObjectPatternList, Bool.and_eq_true] at elementsObjects
          simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at elementsCanonical
          have localTyped := facts.typed.bindParameter parameterType parameterDependencies
            elementTyped elementsObjects.1
          have localChecked := checkTypedAssignment_complete localTyped
          simp only [expand, evaluate, localChecked, ↓reduceDIte]
          have localFacts : InputFacts environment context.quantified
              (localRefinement refinement parameter)
              (bindParameter parameter (localValue context.bound element) initial) :=
            ⟨localTyped, facts.canonical.bindParameter parameter elementsCanonical.1,
              facts.represented.bindParameter parameter _⟩
          refine .cons (resolvedEvaluate environment language services outer
            (.premise context.quantified body
              (bindParameter parameter (localValue context.bound element) initial))
            (.premise _ localFacts zero supported stratum) _ ?_) (.nil _ _)
          intro result
          cases result with
          | premise middle event head =>
            apply ResolvedTree.branch rfl
            refine .cons (resolvedEvaluate environment language services outer
              (.quantified context parameter body (index + 1) elements
                initial)
              (.quantified refinement elementType facts zero parameterType parameterDependencies
                tailTyped elementsObjects.2 elementsCanonical.2 supported stratum) _ ?_) (.nil _ _)
            intro result
            cases result with
            | quantified final history rest =>
              exact .branch rfl (.cons (continued _) (.nil _ _))
    | premise context premise initial =>
      cases admitted with
      | premise refinement facts zero supported stratum =>
        cases premise with
        | relationQuery relation arguments =>
          cases found : signature? environment.provider relation arguments.length with
          | none => simp [premiseFlow, found] at supported
          | some signature =>
            have checked : checkQueryInputs context.rule context.spec context.premiseIndex
                context.quantifierDepth refinement.available 0 arguments signature.modes = true := by
              simpa only [premiseFlow, found] using supported
            let request : Query.Request := ⟨context, relation, arguments, initial⟩
            let admission : Query.InputAdmission environment request :=
              ⟨refinement.available, signature, found, zero, checked,
                facts.typed.rootValues zero, facts.represented.1,
                fun registered resolved inputs =>
                  services.query request signature registered found facts.typed resolved inputs⟩
            exact .cons (resolvedQuery environment outer request admission
              (Query.start environment request) (Query.start_ready admission) 0 tail continued) (.nil _ _)
        | freshness condition =>
          simp only [expand, evaluate, evaluatePremise]
          split
          · rename_i missing
            exact False.elim (by
              obtain ⟨atom, subject, read⟩ := freshness_total facts.typed zero facts.represented supported
              rw [missing] at read
              contradiction)
          · split
            · exact .cons (continued _) (.nil _ _)
            · exact .nil _ _
        | forAll collection parameter body =>
          simp only [expand, evaluate, evaluatePremise]
          split
          · rename_i missing
            exact False.elim (by
              obtain ⟨kind, elements, read⟩ := forAll_total facts.typed zero facts.represented supported
              rw [missing] at read
              contradiction)
          · rename_i kind elements read
            refine .cons (resolvedEvaluate environment language services outer
              (.quantified context parameter body 0 elements initial)
              (GoalAdmitted.quantifiedFromRead facts zero supported stratum read) _ ?_) (.nil _ _)
            intro result
            cases result with
            | quantified final history valid =>
              exact .branch rfl (.cons (continued _) (.nil _ _))
        | congruence source target =>
          simp only [expand, evaluate, evaluatePremise]
          split
          · rename_i unavailable
            simp [premiseFlow, unavailable] at supported
          · split
            · rename_i type typeFound unavailable
              have ready := premise_ready facts.typed zero facts.represented supported
              simp only [checkGoalReady, typeFound, unavailable, Option.isSome_some,
                Option.isSome_none, Bool.true_and, Bool.false_eq_true] at ready
            · rename_i type typeFound actualSource interpreted
              have sorted := step_source_typed facts zero supported typeFound interpreted
              refine .cons (resolvedEvaluate environment language services outer
                (.steps context.bound type actualSource context.ruleIndex)
                (.steps sorted stratum) _ ?_) (.nil _ _)
              intro result
              cases result with
              | steps index trace captured completed history actualTarget earlier valid =>
                exact .branch rfl (.cons (resolvedTarget environment outer _ continued) (.nil _ _))
        | scopedStep step =>
          simp only [expand, evaluate, evaluatePremise]
          split
          · rename_i unavailable
            have ready := premise_ready facts.typed zero facts.represented supported
            simp only [checkGoalReady, unavailable, Option.isSome_none, Bool.false_eq_true] at ready
          · rename_i actualSource interpreted
            have sorted := scoped_source_typed facts zero supported interpreted
            refine .cons (resolvedEvaluate environment language services outer
              (.steps (step.binders ++ context.bound) step.resultType actualSource context.ruleIndex)
              (.steps sorted stratum) _ ?_) (.nil _ _)
            intro result
            cases result with
            | steps index trace captured completed history actualTarget earlier valid =>
              exact .branch rfl (.cons (resolvedTarget environment outer _ continued) (.nil _ _))
    | root bound type source index =>
      cases admitted with
      | root sourceTyped within =>
        simp only [expand, evaluate, evaluateRoot]
        split
        · rename_i missing
          have declared := List.getElem?_eq_getElem within
          rw [missing] at declared
          contradiction
        · rename_i rule declared
          split
          · rename_i missing
            exact False.elim (by
              obtain ⟨selectedSpec, specification, _, _⟩ := checkLanguage_rule language declared
              rw [missing] at specification
              contradiction)
          · rename_i spec specified
            have selected : admittedFor rule spec = true ∧
                checkRule environment.language environment.provider rule spec = true := by
              obtain ⟨selectedSpec, specification, accepted, checked⟩ := checkLanguage_rule language declared
              have same := Option.some.inj (specified.symm.trans specification)
              subst selectedSpec
              exact ⟨accepted, checked⟩
            split
            · split
              · refine .cons (resolvedRootMatch environment outer _ ?_) (.nil _ _)
                intro answer valid typed
                have initialFacts : InputFacts environment
                    ⟨index, rule, spec, bound, 0, 0⟩ (initialRefinement rule) answer.assignment :=
                  ⟨typed, matching_canonicalValues CanonicalValues.empty sourceTyped.2.1 valid.matching,
                    initialRefinement_holds valid.matching⟩
                have contract := selected.2
                simp only [checkRule, Bool.and_eq_true] at contract
                refine resolvedEvaluate environment language services outer
                  (.premises ⟨index, rule, spec, bound, 0, 0⟩ rule.premises answer.assignment)
                  (.premises _ initialFacts contract.1.1.1 rfl contract.1.1.2 (Nat.le_of_lt within)) _ ?_
                intro result
                cases result with
                | premises completed history held =>
                  have finalFacts := initialFacts.afterPremises rfl held
                  have names : BoundNames completed rule.right.freeFvarNames := by
                    intro name member
                    exact finalFacts.represented.1 name
                      (namesAvailable_sound _ _ contract.2 name member)
                  have projected := checkRootProjectionSchema_sound
                    (operation := ScopedReflectiveExecution.binderOperation environment.reflection rule)
                    (depth := 0) contract.1.2 (finalFacts.typed.rootValues contract.1.1.1) names
                  apply ResolvedTree.branch
                  · simp only [expand, delivered]
                    split
                    · rename_i missing
                      exact False.elim (by
                        obtain ⟨target, read⟩ := projected
                        change reductWith? _ rule spec bound.length completed = none at missing
                        change reductWith? _ rule spec bound.length completed = some target at read
                        rw [missing] at read
                        contradiction)
                    · split <;> rfl
                  · simp only [expand, delivered]
                    split
                    · rename_i missing
                      exact False.elim (by
                        obtain ⟨target, read⟩ := projected
                        change reductWith? _ rule spec bound.length completed = none at missing
                        change reductWith? _ rule spec bound.length completed = some target at read
                        rw [missing] at read
                        contradiction)
                    · split
                      · exact .cons (continued _) (.nil _ _)
                      · exact .nil _ _
              · rename_i sourceRejected
                have canonicalCheck := checkOpenPatternWellSorted_complete sourceTyped
                contradiction
            · rename_i specRejected
              exact False.elim (specRejected selected.1)
    | steps bound type source limit =>
      cases admitted with
      | steps sourceTyped stratum =>
        refine .cons (resolvedScan environment outer bound type source limit 0 tail continued ?_) (.nil _ _)
        intro index earlier childTail childContinued
        have within := Nat.lt_of_lt_of_le earlier stratum
        exact resolvedEvaluate environment language services outer (.root bound type source index)
          (.root sourceTyped within) childTail childContinued
termination_by goal.rank
decreasing_by
  all_goals subst_vars
  all_goals dsimp only [Goal.rank, premiseWorkWeight, Context.next, Context.quantified]
  all_goals simp only [Prod.lex_def]
  all_goals simp
  all_goals omega

theorem finish_resolved {environment : Environment} {goal : Goal}
    (language : checkLanguage environment = true)
    (services : DynamicAvailability environment) (admitted : GoalAdmitted environment goal) :
    (finish environment goal).unresolved = [] :=
  finish_resolved_of_tree environment goal
    (resolvedEvaluate environment language services goal goal admitted (.done goal) (resolvedDone environment goal))

theorem root_resolved {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {index : Nat} {rule : RewriteRule}
    (language : checkLanguage environment = true)
    (services : DynamicAvailability environment)
    (declared : environment.language.rewrites[index]? = some rule)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source) :
    (finish environment (.root bound type source index)).unresolved = [] :=
  finish_resolved language services (.root sourceTyped (List.getElem?_eq_some_iff.mp declared).1)

theorem premises_resolved {environment : Environment} {context : Context} {source : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured : Assignment}
    (language : checkLanguage environment = true)
    (services : DynamicAvailability environment)
    (ruleChecked : checkRule environment.language environment.provider context.rule context.spec = true)
    (stratum : context.ruleIndex ≤ environment.language.rewrites.length)
    (initialIndex : context.premiseIndex = 0) (initialDepth : context.quantifierDepth = 0)
    (sourceCanonical : source.hasCanonicalBinderMetadata = true)
    (matched : GeneralScopedMatchMachine.TracedMatches context.rule context.spec context.bound.length
      .left [] 0 [] context.rule.left source trace captured)
    (typed : TypedAssignment environment context captured) :
    (finish environment (.premises context context.rule.premises captured)).unresolved = [] := by
  have facts : InputFacts environment context (initialRefinement context.rule) captured :=
    ⟨typed, matching_canonicalValues CanonicalValues.empty sourceCanonical matched.matching,
      initialRefinement_holds matched.matching⟩
  simp only [checkRule, Bool.and_eq_true] at ruleChecked
  apply finish_resolved language services
  refine .premises _ facts ruleChecked.1.1.1 initialDepth ?_ stratum
  simpa only [initialIndex] using ruleChecked.1.1.2

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static
