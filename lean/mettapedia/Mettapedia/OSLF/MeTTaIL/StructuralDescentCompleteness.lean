import Mettapedia.OSLF.MeTTaIL.StructuralDescentDepth

/-!
# Certificate-depth completeness of generic authored execution

The comparison uses the independent typed premise and root-firing judgments.
Every finite valid receipt is found at a depth computed from its actual
recursive history. No declaration-order restriction or supplied child
completeness field is part of the executable construction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Execution

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem runElements_complete (environment : Environment) (context : Context)
    (parameter : String) (body : Premise)
    (executeBody : ∀ initial, List (PremiseAnswer environment context.quantified body initial))
    (budget : Nat)
    (bodyComplete : ∀ initial (answer : PremiseAnswer environment context.quantified body initial),
      eventDepth answer.event ≤ budget → answer ∈ executeBody initial)
    (index : Nat) (elements : List Pattern) (initial : Assignment)
    (answer : ElementsAnswer environment context parameter body index elements initial)
    (bounded : elementsDepth answer.history ≤ budget) :
    answer ∈ runElements environment context parameter body executeBody index elements initial := by
  cases answer with
  | mk final history held =>
    cases held with
    | nil => simp only [runElements, List.mem_singleton]
    | @cons _ _ _ _ element elements initial middle final event events localTyped head tail =>
      have checked := checkTypedAssignment_complete localTyped
      simp only [runElements, checked, ↓reduceDIte]
      simp only [elementsDepth, eventsDepth, Nat.max_zero, Nat.max_le] at bounded
      apply List.mem_flatMap.mpr
      refine ⟨⟨middle, event, head⟩, bodyComplete _ _ bounded.1, ?_⟩
      apply List.mem_map.mpr
      refine ⟨⟨final, events, tail⟩,
        runElements_complete environment context parameter body executeBody budget bodyComplete
          (index + 1) elements (restoreParameter parameter initial middle) _ bounded.2, rfl⟩
termination_by elements.length

theorem runPremise_complete (environment : Environment) (oracle : Oracle environment)
    (budget : Nat) (complete : OracleCompleteAt environment oracle budget)
    (context : Context) (premise : Premise) (initial : Assignment)
    (answer : PremiseAnswer environment context premise initial)
    (bounded : eventDepth answer.event ≤ budget) :
    answer ∈ runPremise environment oracle context premise initial := by
  cases answer with
  | mk final event held =>
    cases held with
    | @query _ relation arguments initial final rowIndex origins valid =>
      have listed := FiniteServices.Provider.answers_complete environment
        ⟨context, relation, arguments, initial⟩ ⟨rowIndex, final, origins, valid⟩
      rw [runPremise]
      exact List.mem_map.mpr ⟨_, listed, rfl⟩
    | freshness read fresh =>
      have checked := (syntactic_freshness_iff _ _).mpr fresh
      rw [runPremise]
      split
      · rename_i failed
        rw [read] at failed
        contradiction
      · rename_i atom subject observed
        have same := Option.some.inj (observed.symm.trans read)
        rcases Prod.mk.inj same with ⟨rfl, rfl⟩
        rw [dif_pos checked]
        exact List.mem_singleton.mpr rfl
    | @step _ source target actualSource actualTarget type initial final captured completed
        childIndex trace targetTrace history typed interpreted child matched finalTyped =>
      let call : GeneralPremise.Execution.StepCall environment := {
        context := context, premise := .congruence source target,
        initial := initial, binders := [], type := type, source := actualSource,
        targetSchema := target,
        conclude := fun _ _ _ _ _ _ _ _ valid targetMatched targetTyped =>
          .step typed interpreted valid targetMatched targetTyped }
      let receipt : RootAnswer environment context.bound type actualSource :=
        ⟨childIndex, trace, captured, completed, history, actualTarget, child⟩
      have within : receipt.requiredDepth ≤ budget := by
        simpa only [RootAnswer.requiredDepth, eventDepth] using bounded
      have listed := complete _ _ _ receipt within
      obtain ⟨found, member, assignment, event⟩ :=
        runStep_selected call receipt listed final targetTrace matched finalTyped
      have same : found = ⟨final, _, .step typed interpreted child matched finalTyped⟩ :=
        premiseAnswer_eq assignment event
      rw [runPremise]
      split
      · rename_i failed
        rw [typed] at failed
        contradiction
      · rename_i foundType observed
        cases Option.some.inj (observed.symm.trans typed)
        split
        · rename_i failed
          rw [interpreted] at failed
          contradiction
        · rename_i foundSource observed
          cases Option.some.inj (observed.symm.trans interpreted)
          exact same ▸ member
    | @scopedStep _ step actualSource actualTarget initial final captured completed
        childIndex trace targetTrace history interpreted child matched finalTyped =>
      let call : GeneralPremise.Execution.StepCall environment := {
        context := context, premise := .scopedStep step,
        initial := initial, binders := step.binders, type := step.resultType,
        source := actualSource, targetSchema := step.target,
        conclude := fun _ _ _ _ _ _ _ _ valid targetMatched targetTyped =>
          .scopedStep interpreted valid targetMatched targetTyped }
      let receipt : RootAnswer environment (step.binders ++ context.bound) step.resultType actualSource :=
        ⟨childIndex, trace, captured, completed, history, actualTarget, child⟩
      have within : receipt.requiredDepth ≤ budget := by
        simpa only [RootAnswer.requiredDepth, eventDepth] using bounded
      have listed := complete _ _ _ receipt within
      obtain ⟨found, member, assignment, event⟩ :=
        runStep_selected call receipt listed final targetTrace matched finalTyped
      have same : found = ⟨final, _, .scopedStep interpreted child matched finalTyped⟩ :=
        premiseAnswer_eq assignment event
      rw [runPremise]
      split
      · rename_i failed
        rw [interpreted] at failed
        contradiction
      · rename_i foundSource observed
        cases Option.some.inj (observed.symm.trans interpreted)
        exact same ▸ member
    | @quantified _ collection parameter body initial final kind elements history read held =>
      rw [runPremise]
      split
      · rename_i failed
        rw [read] at failed
        contradiction
      · rename_i foundKind foundElements observed
        have same := Option.some.inj (observed.symm.trans read)
        rcases Prod.mk.inj same with ⟨rfl, rfl⟩
        apply List.mem_map.mpr
        refine ⟨⟨final, history, held⟩, ?_, rfl⟩
        exact runElements_complete environment context parameter body _ budget
          (fun localAssignment wanted within =>
            runPremise_complete environment oracle budget complete context.quantified body
              localAssignment wanted within) 0 foundElements initial _
                (by simpa only [eventDepth] using bounded)
termination_by sizeOf premise

theorem runPremises_complete (environment : Environment) (oracle : Oracle environment)
    (budget : Nat) (complete : OracleCompleteAt environment oracle budget)
    (context : Context) (premises : List Premise) (initial : Assignment)
    (answer : PremisesAnswer environment context premises initial)
    (bounded : eventsDepth answer.history ≤ budget) :
    answer ∈ runPremises environment oracle context premises initial := by
  cases answer with
  | mk final history held =>
    cases held with
    | nil => simp only [runPremises, List.mem_singleton]
    | @cons _ premise premises initial middle final event events head tail =>
      simp only [eventsDepth, Nat.max_le] at bounded
      apply List.mem_flatMap.mpr
      refine ⟨⟨middle, event, head⟩,
        runPremise_complete environment oracle budget complete context premise initial _ bounded.1, ?_⟩
      apply List.mem_map.mpr
      refine ⟨⟨final, events, tail⟩,
        runPremises_complete environment oracle budget complete context.next premises middle _ bounded.2, rfl⟩
termination_by premises.length

theorem runRoot_complete (environment : Environment) (oracle : Oracle environment)
    (budget : Nat) (complete : OracleCompleteAt environment oracle budget)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (answer : RootAnswer environment bound type source)
    (bounded : eventsDepth answer.history ≤ budget) :
    answer ∈ runRoot environment oracle bound type source answer.index := by
  cases answer with
  | mk index trace captured completed history target held =>
    cases held with
    | @fire _ _ _ _ _ rule spec _ _ _ _ declared specified admitted sorted matched
        capturedTyped premises converted targetTyped =>
      have sourceCheck := checkOpenPatternWellSorted_complete sorted
      have captureCheck := checkTypedAssignment_complete capturedTyped
      have targetCheck := checkOpenPatternWellSorted_complete targetTyped
      let request : GeneralScopedMatchMachine.Request :=
        ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
      let wanted : GeneralScopedMatchMachine.Answer := ⟨captured, trace⟩
      obtain ⟨found, member, same⟩ := FiniteServices.Matcher.answers_complete request wanted matched
      rcases found with ⟨foundValue, foundValid⟩
      dsimp only at same
      cases same
      have premiseMember := runPremises_complete environment oracle budget complete
        ⟨index, rule, spec, bound, 0, 0⟩ rule.premises captured
        ⟨completed, history, premises⟩ bounded
      rw [runRoot]
      split
      · rename_i failed
        rw [declared] at failed
        contradiction
      · rename_i foundRule observed
        cases Option.some.inj (observed.symm.trans declared)
        split
        · rename_i failed
          rw [specified] at failed
          contradiction
        · rename_i foundSpec observed
          cases Option.some.inj (observed.symm.trans specified)
          rw [dif_pos admitted, dif_pos sourceCheck]
          apply List.mem_flatMap.mpr
          refine ⟨⟨wanted, foundValid⟩, member, ?_⟩
          simp only [wanted, captureCheck, ↓reduceDIte]
          apply List.mem_filterMap.mpr
          refine ⟨⟨completed, history, premises⟩, premiseMember, ?_⟩
          split
          · rename_i failed
            rw [converted] at failed
            contradiction
          · rename_i foundTarget observed
            cases Option.some.inj (observed.symm.trans converted)
            rw [dif_pos targetCheck]

/-- Depth completeness is earned over the original authored declaration
catalogue for every language, context and finite provider snapshot. -/
theorem roots_complete_at_depth (environment : Environment) (depth : Nat) :
    OracleCompleteAt environment (roots environment depth) depth := by
  induction depth with
  | zero =>
      intro bound type source answer bounded
      simp only [RootAnswer.requiredDepth] at bounded
      omega
  | succ depth ih =>
      intro bound type source answer bounded
      have declaredIndex : answer.index < environment.language.rewrites.length := by
        cases answer.valid with
        | fire declared _ _ _ _ _ _ _ _ =>
          exact (List.getElem?_eq_some_iff.mp declared).1
      apply List.mem_flatMap.mpr
      refine ⟨answer.index, List.mem_range.mpr declaredIndex, ?_⟩
      apply runRoot_complete environment (roots environment depth) depth ih
      simp only [RootAnswer.requiredDepth] at bounded
      omega

theorem every_certificate_discovered (environment : Environment)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (answer : RootAnswer environment bound type source) :
    answer ∈ roots environment answer.requiredDepth bound type source :=
  roots_complete_at_depth environment answer.requiredDepth bound type source answer (Nat.le_refl _)

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Execution
