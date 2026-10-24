import Mettapedia.OSLF.MeTTaIL.StructuralDescentCompleteness

/-!
# Earned exhaustive depth for structurally admitted authored languages

This comparison is quantified over every independently valid firing receipt.
Each recursive source is smaller than its actual matched caller. The caller's
node count therefore bounds the whole nested firing depth, and the generic
finite-depth executor covers every occurrence, not merely every endpoint.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent

open Syntax RuleBinding ScopedRuleMatching GeneralPremise PatternTreeSize
open GeneralEquationAdmission GeneralScopedMatch

theorem elements_depth_zero (environment : Environment) (context : Context)
    (parameter : String) (body : Premise) (index : Nat) (elements : List Pattern)
    (initial final : Assignment) (history : List (Nat × Pattern × List Event))
    (held : QuantifiedElements environment context parameter body index elements initial final history)
    (bodyZero : ∀ first last event,
      PremiseHolds environment context.quantified body first last event → eventDepth event = 0) :
    elementsDepth history = 0 := by
  induction elements generalizing index initial final history with
  | nil => cases held; simp only [elementsDepth]
  | cons element elements ih =>
      cases held with
      | cons _ head tail =>
          have rest := ih _ _ _ _ tail
          simp only [elementsDepth, eventsDepth, bodyZero _ _ _ head, Nat.max_self, rest]

theorem premise_depth_zero {environment : Environment} {context : Context}
    {premise : Premise} {initial final : Assignment} {event : Event}
    (held : PremiseHolds environment context premise initial final event)
    (noSteps : stepSources premise = []) : eventDepth event = 0 := by
  cases held with
  | query _ => simp only [eventDepth]
  | freshness _ _ => simp only [eventDepth]
  | step _ _ _ _ _ => simp only [stepSources, List.cons_ne_nil] at noSteps
  | scopedStep _ _ _ _ => simp only [stepSources, List.cons_ne_nil] at noSteps
  | quantified _ elements =>
      simpa only [eventDepth] using elements_depth_zero environment context _ _ _ _ _ _ _ elements
        (fun _ _ _ body => premise_depth_zero body noSteps)
termination_by sizeOf premise

/-- This local comparison is used inside well-founded source induction.
Its child contract is discharged by that induction, not admitted as an
unproved execution-completeness field. -/
def ChildrenBounded (environment : Environment) (parent : Pattern) : Prop :=
  ∀ bound type child (answer : Execution.RootAnswer environment bound type child),
    Smaller child parent → answer.requiredDepth ≤ nodes child

theorem premise_depth_lt {environment : Environment} {context : Context}
    {premise : Premise} {captured initial final : Assignment} {parent : Pattern} {event : Event}
    (held : PremiseHolds environment context premise initial final event)
    (checked : checkPremise context.rule context.spec context.premiseIndex 0 premise = true)
    (rootDepth : context.quantifierDepth = 0)
    (matching : Matches context.rule context.spec context.bound.length .left [] 0 []
      context.rule.left parent captured)
    (extension : Extends captured initial)
    (children : ChildrenBounded environment parent) : eventDepth event < nodes parent := by
  cases held with
  | query _ => simpa only [eventDepth] using nodes_positive parent
  | freshness _ _ => simpa only [eventDepth] using nodes_positive parent
  | @step _ source target actualSource actualTarget type initial final childCaptured completed
      childIndex trace targetTrace history typed interpreted child matched finalTyped =>
      have sourceChecked : checkSource context.rule context.spec context.premiseIndex
          context.quantifierDepth 0 source = true := by
        simpa only [checkPremise, rootDepth] using checked
      have smaller := actual_source_decreases sourceChecked matching extension interpreted
      have bounded := children context.bound type actualSource
        ⟨childIndex, trace, childCaptured, completed, history, actualTarget, child⟩ smaller
      simp only [eventDepth]
      exact lt_of_le_of_lt bounded smaller
  | @scopedStep _ step actualSource actualTarget initial final childCaptured completed
      childIndex trace targetTrace history interpreted child matched finalTyped =>
      have sourceChecked : checkSource context.rule context.spec context.premiseIndex
          context.quantifierDepth step.binders.length step.source = true := by
        simpa only [checkPremise, rootDepth] using checked
      have smaller := actual_source_decreases sourceChecked matching extension interpreted
      have bounded := children (step.binders ++ context.bound) step.resultType actualSource
        ⟨childIndex, trace, childCaptured, completed, history, actualTarget, child⟩ smaller
      simp only [eventDepth]
      exact lt_of_le_of_lt bounded smaller
  | @quantified _ collection parameter body initial final kind elements history read held =>
      have empty : stepSources body = [] := by
        exact List.isEmpty_iff.mp checked
      have zero := elements_depth_zero environment context parameter body _ _ _ _ _ held
        (fun _ _ _ bodyHeld => premise_depth_zero bodyHeld empty)
      simpa only [eventDepth, zero] using nodes_positive parent

theorem premises_depth_lt {environment : Environment} {context : Context}
    {premises : List Premise} {captured initial final : Assignment} {parent : Pattern}
    {history : List Event}
    (held : PremisesHold environment context premises initial final history)
    (checked : checkPremises context.rule context.spec context.premiseIndex premises = true)
    (rootDepth : context.quantifierDepth = 0)
    (matching : Matches context.rule context.spec context.bound.length .left [] 0 []
      context.rule.left parent captured)
    (extension : Extends captured initial)
    (children : ChildrenBounded environment parent) : eventsDepth history < nodes parent := by
  cases held with
  | nil => simpa only [eventsDepth] using nodes_positive parent
  | cons head tail =>
      simp only [checkPremises, Bool.and_eq_true] at checked
      have headBound := premise_depth_lt head checked.1 rootDepth matching extension children
      have tailBound := premises_depth_lt tail checked.2 rfl matching
        (extension.trans head.extension) children
      simpa only [eventsDepth] using max_lt headBound tailBound
termination_by premises.length

theorem firing_depth_bound (environment : Environment)
    (checked : checkEnvironment environment = true) (parent : Pattern) :
    ∀ bound type (answer : Execution.RootAnswer environment bound type parent),
      answer.requiredDepth ≤ nodes parent := by
  induction parent using smaller_wellFounded.induction with
  | h parent ih =>
      intro bound type answer
      have children : ChildrenBounded environment parent :=
        fun childBound childType child receipt smaller => ih child smaller childBound childType receipt
      cases answer with
      | mk index trace captured completed history target held =>
        cases held with
        | @fire _ _ _ _ _ rule spec _ _ _ _ declared specified admitted sorted matched
            capturedTyped premises converted targetTyped =>
          obtain ⟨foundSpec, found, ruleChecked⟩ := checkEnvironment_rule checked declared
          have same := Option.some.inj (found.symm.trans specified)
          cases same
          simp only [StructuralDescent.checkRule, Bool.and_eq_true] at ruleChecked
          have smaller := premises_depth_lt premises ruleChecked.2 rfl matched.matching
            (Extends.refl _) children
          change eventsDepth history < nodes parent at smaller
          change 1 + eventsDepth history ≤ nodes parent
          omega

namespace Execution

def exhaustive (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) : List (RootAnswer environment bound type source) :=
  roots environment (nodes source) bound type source

theorem exhaustive_complete (environment : Environment)
    (checked : checkEnvironment environment = true) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (answer : RootAnswer environment bound type source) :
    answer ∈ exhaustive environment bound type source :=
  roots_complete_at_depth environment (nodes source) bound type source answer
    (firing_depth_bound environment checked source bound type answer)

/-- Complete receipt occurrence coverage, retaining declaration and matcher
origins even when multiple receipts have the same target. -/
theorem exhaustive_occurrences (environment : Environment)
    (checked : checkEnvironment environment = true) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (index : Nat)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment)
    (history : List Event) (target : Pattern) :
    (∃ answer ∈ exhaustive environment bound type source,
      answer.index = index ∧ answer.trace = trace ∧ answer.captured = captured ∧
      answer.completed = completed ∧ answer.history = history ∧ answer.target = target) ↔
    RootFiring environment bound type source index trace captured completed history target := by
  constructor
  · rintro ⟨answer, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact answer.valid
  · intro valid
    exact ⟨⟨index, trace, captured, completed, history, target, valid⟩,
      exhaustive_complete environment checked bound type source _,
      rfl, rfl, rfl, rfl, rfl, rfl⟩

end Execution
end Mettapedia.OSLF.MeTTaIL.StructuralDescent
