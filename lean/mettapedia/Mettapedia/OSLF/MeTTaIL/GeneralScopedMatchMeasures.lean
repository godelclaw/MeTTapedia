import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch
import Mettapedia.OSLF.MeTTaIL.GeneralEquationAdmission

/-!
# Structural measures of independently specified scoped matches

Balanced equation admission needs the weight of the actual matched source,
including every occurrence of a captured value. The proof follows the match
judgment and remains valid after premise evaluation extends its assignment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMeasures

open Syntax RuleBinding ScopedRuleMatching PatternTreeSize GeneralScopedMatch
open GeneralEquationMeasures GeneralEquationAdmission

theorem listNodes_selected (targets : List Pattern) (selected : Nat)
    (within : selected < targets.length) :
    listNodes targets = nodes targets[selected] + listNodes (targets.eraseIdx selected) := by
  induction targets generalizing selected with
  | nil => simp at within
  | cons target targets ih =>
      cases selected with
      | zero => simp only [listNodes, List.getElem_cons_zero, List.eraseIdx_zero, List.tail_cons]
      | succ selected =>
          have tailWithin : selected < targets.length := by simpa using within
          have tailCount := ih selected tailWithin
          simp only [List.eraseIdx_cons_succ, listNodes, List.getElem_cons_succ]
          omega

mutual
  theorem matched_nodes {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat}
      {initial final complete : Assignment} {pattern target : Pattern}
      (matched : Matches rule spec ambient site path depth initial pattern target final)
      (supported : checkSide rule spec site path depth pattern = true)
      (extension : Extends final complete) :
      nodes target = evaluate (capturedWeight complete) pattern := by
    cases matched with
    | capture captured =>
        obtain ⟨dependencies, arguments, value, _, occurrence, _, retained, interpreted, _⟩ :=
          capture_interpretation captured
        simp only [checkSide, occurrence, Bool.and_eq_true] at supported
        have count := instantiateValue_nodes value ambient depth arguments target supported.1 interpreted
        have finalLookup := extension _ _ retained
        simpa only [evaluate, capturedWeight, finalLookup, Option.map_some, Option.getD_some] using count
    | bound => rfl
    | constructor arguments =>
        simp only [checkSide] at supported
        have count := matchedArguments_nodes arguments supported extension
        simp only [nodes, evaluate, count]
    | binder body =>
        simp only [checkSide] at supported
        have count := matched_nodes body supported extension
        simp only [nodes, evaluate, count]
    | binders body =>
        simp only [checkSide] at supported
        have count := matched_nodes body supported extension
        simp only [nodes, evaluate, count]
    | substitution _ _ => simp only [checkSide, Bool.false_eq_true] at supported
    | bag _notVector bag =>
        rename_i kind patterns rest targets
        simp only [checkSide, Bool.and_eq_true] at supported
        have noRest : rest = none := Option.isNone_iff_eq_none.mp supported.1
        subst rest
        have count := matchedBag_nodes bag supported.2 extension
        simp only [nodes, evaluate, Option.toList_none, List.map_nil, List.sum_nil, Nat.add_zero, count]
    | vector arguments =>
        simp only [checkSide, Option.isNone_none, Bool.true_and] at supported
        have count := matchedArguments_nodes arguments supported extension
        simp only [nodes, evaluate, Option.toList_none, List.map_nil, List.sum_nil, Nat.add_zero, count]
    | vectorRest _ _ => simp only [checkSide, Option.isNone_some, Bool.false_and, Bool.false_eq_true] at supported
  termination_by sizeOf pattern

  theorem matchedArguments_nodes {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final complete : Assignment} {patterns targets : List Pattern}
      (matched : Arguments rule spec ambient site path depth initial index patterns targets final)
      (supported : checkArguments rule spec site path depth index patterns = true)
      (extension : Extends final complete) :
      listNodes targets = evaluateList (capturedWeight complete) patterns := by
    cases matched with
    | nil => rfl
    | cons head tail =>
        simp only [checkArguments, Bool.and_eq_true] at supported
        have headCount := matched_nodes head supported.1 (tail.extends.trans extension)
        have tailCount := matchedArguments_nodes tail supported.2 extension
        simp only [listNodes, evaluateList, headCount, tailCount]
  termination_by sizeOf patterns

  theorem matchedBag_nodes {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final complete : Assignment} {patterns targets : List Pattern} {kind : CollType}
      (matched : Bag rule spec ambient site path depth initial index patterns none kind targets final)
      (supported : checkArguments rule spec site path depth index patterns = true)
      (extension : Extends final complete) :
      listNodes targets = evaluateList (capturedWeight complete) patterns := by
    cases matched with
    | nil => rfl
    | cons selected within head tail =>
        simp only [checkArguments, Bool.and_eq_true] at supported
        have headCount := matched_nodes head supported.1 (tail.extends.trans extension)
        have tailCount := matchedBag_nodes tail supported.2 extension
        rw [listNodes_selected targets selected within, headCount, tailCount]
        rfl
  termination_by sizeOf patterns
end

theorem matchRule_nodes {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {source : Pattern} {captured completed : Assignment}
    (supported : checkSide rule spec .left [] 0 rule.left = true)
    (matched : captured ∈ matchRuleAt rule spec ambient source)
    (extension : Extends captured completed) :
    nodes source = evaluate (capturedWeight completed) rule.left :=
  matched_nodes (matchRuleAt_iff.mp matched) supported extension

theorem matched_reduct_preserves_nodes {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {source target : Pattern} {captured completed : Assignment}
    (accepted : checkRule rule spec = true)
    (matched : captured ∈ matchRuleAt rule spec ambient source)
    (extension : Extends captured completed)
    (reduct : reduct? rule spec ambient completed = some target) : nodes source = nodes target := by
  have ready := checkRule_sides rule spec accepted
  rw [matchRule_nodes ready.2.1 matched extension,
    instantiate_nodes rule spec ambient .right [] 0 completed rule.right target ready.2.2.1 reduct]
  exact balanced_evaluate rule.left rule.right ready.2.2.2 (capturedWeight completed)

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMeasures
