import Mettapedia.OSLF.NativeTypes.Modal.NativeCaptureSubstitution
import Mathlib.Data.List.InsertIdx

/-!
# Ambient substitution of complete scoped matcher witnesses

The action preserves every authored occurrence path, original bag-choice
index, ordered assignment and duplicate target occurrence. Schemas are read
in their independently scoped local binder prefix. Collection rest capture
uses the same proved dependent recovery action as ordinary metavariables.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeTracedMatchSubstitution

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralScopedMatchMachine

mutual
theorem matched_substitutes {rule : RewriteRule} {spec : RuleBindingSpec}
    {source target depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {schema actual : Pattern} {trace : List BagChoice}
    (matched : TracedMatches rule spec source site path depth initial schema actual trace final)
    (localScope : schema.isWellScopedAt depth = true)
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    TracedMatches rule spec target site path depth
      (NativeContextualSubstitution.assignment target substitution initial) schema
      (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution) actual) trace
      (NativeContextualSubstitution.assignment target substitution final) := by
  cases matched with
  | capture captured => exact .capture (NativeCaptureSubstitution.capture_substitutes captured substitution boundScoped)
  | bound =>
      have within := of_decide_eq_true localScope
      simpa only [ContextSubstitution.substitute, ContextSubstitution.lift, within, ite_true] using
        (TracedMatches.bound (rule := rule) (spec := spec) (ambient := target)
          (initial := NativeContextualSubstitution.assignment target substitution initial))
  | constructor arguments =>
      simpa only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map] using
        (TracedMatches.constructor (arguments_substitute arguments localScope substitution boundScoped))
  | binder body =>
      simpa only [ContextSubstitution.substitute, ContextSubstitution.lift_lift] using
        (TracedMatches.binder (matched_substitutes body localScope substitution boundScoped))
  | binders body =>
      simpa only [ContextSubstitution.substitute, ContextSubstitution.lift_lift] using
        (TracedMatches.binders (matched_substitutes body localScope substitution boundScoped))
  | substitution body replacement =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at localScope
      simpa only [ContextSubstitution.substitute, ContextSubstitution.lift_lift] using
        (TracedMatches.substitution
          (matched_substitutes body localScope.1 substitution boundScoped)
          (matched_substitutes replacement localScope.2 substitution boundScoped))
  | bag kind bag =>
      simpa only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map] using
        (TracedMatches.bag kind (bag_substitutes bag localScope substitution boundScoped))
  | vector arguments =>
      simpa only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map] using
        (TracedMatches.vector (arguments_substitute arguments localScope substitution boundScoped))
  | vectorRest arguments captured =>
      have front := arguments_substitute arguments localScope substitution boundScoped
      have rest := NativeCaptureSubstitution.captureRest_substitutes captured substitution boundScoped
      simp only [List.map_take] at front
      simp only [List.map_drop] at rest
      simpa only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map] using
        (TracedMatches.vectorRest front rest)
termination_by sizeOf schema

theorem arguments_substitute {rule : RewriteRule} {spec : RuleBindingSpec}
    {source target depth index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {schemas actuals : List Pattern} {trace : List BagChoice}
    (matched : TracedArguments rule spec source site path depth initial index schemas actuals trace final)
    (localScope : Pattern.isWellScopedListAt depth schemas = true)
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    TracedArguments rule spec target site path depth
      (NativeContextualSubstitution.assignment target substitution initial) index schemas
      (actuals.map (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution))) trace
      (NativeContextualSubstitution.assignment target substitution final) := by
  cases matched with
  | nil => exact .nil
  | cons head tail =>
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at localScope
      exact .cons (matched_substitutes head localScope.1 substitution boundScoped)
        (arguments_substitute tail localScope.2 substitution boundScoped)
termination_by sizeOf schemas

theorem bag_substitutes {rule : RewriteRule} {spec : RuleBindingSpec}
    {source target depth index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {schemas actuals : List Pattern} {trace : List BagChoice}
    {rest : Option String} {kind : CollType}
    (matched : TracedBag rule spec source site path depth initial index schemas rest kind actuals trace final)
    (localScope : Pattern.isWellScopedListAt depth schemas = true)
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    TracedBag rule spec target site path depth
      (NativeContextualSubstitution.assignment target substitution initial) index schemas rest kind
      (actuals.map (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution))) trace
      (NativeContextualSubstitution.assignment target substitution final) := by
  cases matched with
  | nil => exact .nil
  | rest captured => exact .rest (NativeCaptureSubstitution.captureRest_substitutes captured substitution boundScoped)
  | cons selected within head tail =>
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at localScope
      have transformedHead := matched_substitutes head localScope.1 substitution boundScoped
      have transformedTail := bag_substitutes tail localScope.2 substitution boundScoped
      have withinMapped : selected <
          (actuals.map (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution))).length := by
        simpa only [List.length_map] using within
      apply TracedBag.cons selected withinMapped
      · simpa only [List.getElem_map] using transformedHead
      · simpa only [List.eraseIdx_map] using transformedTail
termination_by sizeOf schemas
end

end Mettapedia.OSLF.NativeTypes.Modal.NativeTracedMatchSubstitution
