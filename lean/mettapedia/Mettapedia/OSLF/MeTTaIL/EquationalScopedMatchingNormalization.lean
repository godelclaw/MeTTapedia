import Mettapedia.OSLF.MeTTaIL.EquationalScopedMatchingPresentation
import Mettapedia.OSLF.MeTTaIL.CanonicalMatching

/-!
# Recursive collection coverage at canonical subjects

Every ordinary source match transports to the recursive collection matcher
at the canonical subject. Nested set schemas are included: duplicated source
elements may become reuse and overlap choices. The same increasing-spine
condition as the existing capture-normalization theorem is retained.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching

open Syntax RuleBinding ScopedRuleMatching CanonicalBags CollectionSelection
open CollectionMatcherCompatibility

mutual
theorem ordinary_canonical {rule : RewriteRule} {spec : RuleBindingSpec}
    (increasing : IncreasingSpines rule spec)
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial final : Assignment} {schema target : Pattern}
    (matched : GeneralScopedMatch.Matches rule spec ambient site path depth initial schema target final) :
    Meaning literalBodyComparison rule spec ambient site path depth
      (canonAssignment initial) schema (canon target) (canonAssignment final) := by
  cases matched with
  | capture captured =>
    simpa only [Meaning, captureWith?_literal] using capture?_canon increasing captured
  | bound => simp [Meaning, canon]
  | constructor rows =>
    simpa only [canon_apply, Meaning, true_and] using ordinary_arguments_canonical increasing rows
  | binder body =>
    simpa only [canon, Meaning] using ordinary_canonical increasing body
  | binders body =>
    simpa only [canon, Meaning, true_and] using ordinary_canonical increasing body
  | substitution head tail =>
    simp only [canon, Meaning]
    exact ⟨_, ordinary_canonical increasing head, ordinary_canonical increasing tail⟩
  | bag unordered rows =>
    simpa only [canon_collection, Meaning.eq_def, true_and, unordered, ↓reduceIte, Nat.zero_add] using
      ordinary_bag_canonical increasing unordered rows
  | vector rows =>
    simpa only [canon_collection, arrange_vec, Meaning.eq_def, true_and, ↓reduceIte] using
      ordinary_arguments_canonical increasing rows
  | vectorRest rows captured =>
    have front := ordinary_arguments_canonical increasing rows
    have rest := captureRest?_canon increasing captured
    rw [arrange_vec, List.map_drop] at rest
    rw [List.map_take] at front
    simp only [canon_collection, arrange_vec, Meaning.eq_def, true_and, ↓reduceIte,
      captureRestWith?_literal]
    exact ⟨_, front, rest⟩
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

theorem ordinary_arguments_canonical {rule : RewriteRule} {spec : RuleBindingSpec}
    (increasing : IncreasingSpines rule spec)
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
    {initial final : Assignment} {schemas targets : List Pattern}
    (matched : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas targets final) :
    ArgumentsMeaning literalBodyComparison rule spec ambient site path depth
      (canonAssignment initial) index schemas (targets.map canon) (canonAssignment final) := by
  cases matched with
  | nil => simp [ArgumentsMeaning]
  | cons head tail =>
    simp only [List.map_cons, ArgumentsMeaning]
    exact ⟨_, ordinary_canonical increasing head, ordinary_arguments_canonical increasing tail⟩
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec

theorem ordinary_bag_canonical {rule : RewriteRule} {spec : RuleBindingSpec}
    (increasing : IncreasingSpines rule spec)
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
    {initial final : Assignment} {schemas targets : List Pattern} {rest : Option String} {kind : CollType}
    (unordered : kind ≠ .vec)
    (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial index schemas rest kind targets final) :
    ∃ values residual middle,
      Presents kind (arrange kind (targets.map canon)) (values ++ residual) ∧
      ArgumentsMeaning literalBodyComparison rule spec ambient site path depth
        (canonAssignment initial) index schemas values middle ∧
      Finished literalBodyComparison rule spec ambient site path depth (index + schemas.length)
        rest kind middle (arrange kind residual) (canonAssignment final) := by
  cases matched with
  | nil =>
    have empty : arrange kind [] = [] := by cases kind <;> rfl
    refine ⟨[], [], canonAssignment initial, ?_, by simp [ArgumentsMeaning], ?_⟩
    · simpa only [List.map_nil, List.nil_append, empty] using Presents.refl kind []
    · simp [Finished, empty]
  | @rest _ _ _ _ _ _ targets _ captured =>
    refine ⟨[], targets.map canon, canonAssignment initial, ?_, by simp [ArgumentsMeaning], ?_⟩
    · exact presents_of_arrange_eq (arrange_eq_of_presents (presents_arrange kind _)).symm
    · simpa only [Finished, captureRestWith?_literal, List.length_nil, Nat.add_zero] using
        captureRest?_canon increasing captured
  | cons selected within head tail =>
    obtain ⟨chosen, residual, middle, presents, arguments, finished⟩ :=
      ordinary_bag_canonical increasing unordered tail
    refine ⟨canon targets[selected] :: chosen, residual, middle, ?_, ?_, ?_⟩
    · have split : Presents kind (targets.map canon)
          (canon targets[selected] :: (targets.eraseIdx selected).map canon) := by
        have permuted := (List.getElem_cons_eraseIdx_perm within).map canon
        cases kind with
        | vec => exact False.elim (unordered rfl)
        | hashBag => simpa only [Presents, List.map_cons] using permuted.symm
        | hashSet => intro item; simpa only [List.map_cons] using permuted.mem_iff.symm
      have tailPresents := presents_trans (presents_arrange kind _) presents
      have before : Presents kind (arrange kind (targets.map canon)) (targets.map canon) :=
        presents_of_arrange_eq (arrange_eq_of_presents (presents_arrange kind _)).symm
      have after := presents_cons tailPresents (canon targets[selected])
      exact presents_trans before (presents_trans split
        (by simpa only [List.cons_append] using after))
    · simp only [ArgumentsMeaning]
      exact ⟨_, ordinary_canonical increasing head, arguments⟩
    · convert finished using 1
      simp only [List.length_cons]
      omega
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

/-- The actual recursive executor covers an ordinary match from any equivalent
presentation. Canonicalization acts on captures as well as the subject. -/
theorem runAt_covers_presentation {rule : RewriteRule} {spec : RuleBindingSpec}
    (increasing : IncreasingSpines rule spec)
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial final : Assignment} {schema target presented : Pattern}
    (same : Same target presented)
    (matched : GeneralScopedMatch.Matches rule spec ambient site path depth initial schema presented final) :
    canonAssignment final ∈ runAt literalBodyComparison rule spec ambient site path depth
      (canonAssignment initial) schema (canon target) := by
  apply (runAt_exact _ _ _ _ _ _ _ _ _ _ _).mpr
  rw [same]
  exact ordinary_canonical increasing matched

private theorem assignment_canon_idempotent (assignment : Assignment) :
    canonAssignment (canonAssignment assignment) = canonAssignment assignment := by
  simp only [canonAssignment, List.map_map, Function.comp_def, canonValue, canon_idempotent]

/-- Exact answer membership modulo collection equality. The explicit output
normalization is an observation of captures; it neither identifies allocation
origins nor asserts equality of derivation multiplicities. -/
theorem runAt_canonical_observation_iff {rule : RewriteRule} {spec : RuleBindingSpec}
    (increasing : IncreasingSpines rule spec)
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial observed : Assignment} {schema target : Pattern}
    (initialCanonical : canonAssignment initial = initial) :
    observed ∈ (runAt literalBodyComparison rule spec ambient site path depth
      initial schema (canon target)).map canonAssignment ↔
      ∃ presented captured, Same target presented ∧
        GeneralScopedMatch.Matches rule spec ambient site path depth initial schema presented captured ∧
        observed = canonAssignment captured := by
  constructor
  · intro member
    obtain ⟨captured, capturedMember, observedEq⟩ := List.mem_map.mp member
    obtain ⟨presented, same, matched⟩ := meaning_has_ordinary_presentation
      ((runAt_exact _ _ _ _ _ _ _ _ _ _ _).mp capturedMember)
    exact ⟨presented, captured, by simpa only [Same, canon_idempotent] using same,
      matched, observedEq.symm⟩
  · rintro ⟨presented, captured, same, matched, rfl⟩
    have found := runAt_covers_presentation increasing same matched
    rw [initialCanonical] at found
    exact List.mem_map.mpr ⟨canonAssignment captured, found, assignment_canon_idempotent captured⟩

end Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching
