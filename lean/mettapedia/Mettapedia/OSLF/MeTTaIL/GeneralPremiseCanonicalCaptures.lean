import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCanonicalProjection

/-!
# Canonical captured values from actual matcher derivations

Captures are recovered from the supplied target with a variable-only inverse
context map. Canonical target metadata therefore gives canonical stored bodies.
The property survives ordered and permutation matching, including collection
rest captures and restoration of a lexical quantifier parameter.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching

theorem recoverValue?_canonical {dependencies : List TypeExpr} {ambient depth : Nat}
    {arguments : List Pattern} {target : Pattern} {value : ContextualValue}
    (canonical : target.hasCanonicalBinderMetadata = true)
    (recovered : recoverValue? dependencies ambient depth arguments target = some value) :
    value.body.hasCanonicalBinderMetadata = true := by
  unfold recoverValue? at recovered
  split at recovered <;> try contradiction
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at recovered
  obtain ⟨indices, _, recovered⟩ := recovered
  split at recovered <;> try contradiction
  split at recovered <;> try contradiction
  cases Option.some.inj recovered
  apply contextSubstitute_canonical canonical
  intro index
  simp only [recoveryAssignment]
  split
  · split <;> rfl
  · rfl

theorem assign_canonicalValues {initial final : Assignment} {name : String} {value : ContextualValue}
    (before : CanonicalValues initial) (canonical : value.body.hasCanonicalBinderMetadata = true)
    (assigned : assign initial name value = some final) : CanonicalValues final := by
  unfold assign at assigned
  cases previous : lookup initial name with
  | none =>
      rw [previous] at assigned
      cases Option.some.inj assigned
      intro queried foundValue found
      by_cases same : queried = name
      · subst queried
        simp only [lookup_cons, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at found
        subst foundValue
        exact canonical
      · apply before queried foundValue
        simpa only [lookup_cons, show (name == queried) = false from by simp [Ne.symm same],
          Bool.false_eq_true, ↓reduceIte] using found
  | some previousValue =>
      simp only [previous] at assigned
      split at assigned
      · cases Option.some.inj assigned
        exact before
      · contradiction

theorem capture_canonicalValues {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : Assignment}
    {name : String} {target : Pattern}
    (before : CanonicalValues initial) (canonical : target.hasCanonicalBinderMetadata = true)
    (captured : capture? rule spec ambient depth site path initial name target = some final) :
    CanonicalValues final := by
  simp only [capture?, Option.bind_eq_bind, Option.bind_eq_some_iff] at captured
  obtain ⟨dependencies, _, arguments, _, value, recovered, assigned⟩ := captured
  exact assign_canonicalValues before (recoverValue?_canonical canonical recovered) assigned

theorem canonicalList_take {targets : List Pattern} (count : Nat)
    (canonical : Pattern.hasCanonicalBinderMetadataList targets = true) :
    Pattern.hasCanonicalBinderMetadataList (targets.take count) = true :=
  (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mpr fun target member =>
    (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp canonical target (List.mem_of_mem_take member)

theorem canonicalList_drop {targets : List Pattern} (count : Nat)
    (canonical : Pattern.hasCanonicalBinderMetadataList targets = true) :
    Pattern.hasCanonicalBinderMetadataList (targets.drop count) = true :=
  (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mpr fun target member =>
    (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp canonical target (List.mem_of_mem_drop member)

mutual
  theorem matching_canonicalValues {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
      {site : RulePatternSite} {path : List Nat} {initial final : Assignment} {schema target : Pattern}
      (before : CanonicalValues initial) (canonical : target.hasCanonicalBinderMetadata = true)
      (matching : GeneralScopedMatch.Matches rule spec ambient site path depth initial schema target final) :
      CanonicalValues final := by
    cases matching with
    | capture captured => exact capture_canonicalValues before canonical captured
    | bound => exact before
    | constructor arguments => exact matchingArguments_canonicalValues before canonical arguments
    | binder body =>
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        exact matching_canonicalValues before canonical.2 body
    | binders body =>
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        exact matching_canonicalValues before canonical.2 body
    | substitution body replacement =>
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        exact matching_canonicalValues (matching_canonicalValues before canonical.1 body) canonical.2 replacement
    | bag _ bag => exact matchingBag_canonicalValues before canonical bag
    | vector arguments => exact matchingArguments_canonicalValues before canonical arguments
    | vectorRest arguments captured =>
        have matched := matchingArguments_canonicalValues before (canonicalList_take _ canonical) arguments
        have capturedAsTree := captured
        unfold captureRest? at capturedAsTree
        apply capture_canonicalValues (captured := capturedAsTree) matched
        exact canonicalList_drop _ canonical

  theorem matchingArguments_canonicalValues {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
      {initial final : Assignment} {schemas targets : List Pattern}
      (before : CanonicalValues initial)
      (canonical : Pattern.hasCanonicalBinderMetadataList targets = true)
      (matching : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas targets final) :
      CanonicalValues final := by
    cases matching with
    | nil => exact before
    | cons head tail =>
        simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at canonical
        exact matchingArguments_canonicalValues (matching_canonicalValues before canonical.1 head) canonical.2 tail

  theorem matchingBag_canonicalValues {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
      {initial final : Assignment} {schemas targets : List Pattern}
      {rest : Option String} {kind : CollType}
      (before : CanonicalValues initial)
      (canonical : Pattern.hasCanonicalBinderMetadataList targets = true)
      (matching : GeneralScopedMatch.Bag rule spec ambient site path depth initial index schemas rest kind targets final) :
      CanonicalValues final := by
    cases matching with
    | nil => exact before
    | rest captured =>
        have capturedAsTree := captured
        unfold captureRest? at capturedAsTree
        apply capture_canonicalValues (captured := capturedAsTree) before
        exact canonical
    | cons selected within head tail =>
        have canonicalTargets : ∀ target ∈ targets, target.hasCanonicalBinderMetadata = true :=
          (Pattern.hasCanonicalBinderMetadataList_eq_true_iff targets).mp canonical
        have selectedCanonical := canonicalTargets targets[selected] (List.getElem_mem within)
        have remaining : Pattern.hasCanonicalBinderMetadataList (targets.eraseIdx selected) = true :=
          (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mpr
            (fun target member => canonicalTargets target (List.mem_of_mem_eraseIdx member))
        exact matchingBag_canonicalValues (matching_canonicalValues before selectedCanonical head) remaining tail
end

theorem CanonicalValues.restoreParameter {initial final : Assignment}
    (before : CanonicalValues initial) (after : CanonicalValues final) (parameter : String) :
    CanonicalValues (restoreParameter parameter initial final) := by
  intro name value found
  by_cases same : name = parameter
  · subst name
    exact before parameter value (by simpa only [lookup_restore_parameter] using found)
  · exact after name value (by simpa only [lookup_restore_other initial final parameter name same] using found)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
