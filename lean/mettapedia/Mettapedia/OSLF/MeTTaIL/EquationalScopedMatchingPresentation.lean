import Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherCompatibility
import Mathlib.Data.List.Forall2

/-!
# Ordinary source witnesses for recursive collection matches

Nested bag/set decompositions reconstruct a concrete ordinary presentation
of the source. The captured assignment and the authored occurrence paths are
unchanged. This reuses the original scoped matching judgment; no additional
meaning of a rule firing is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching

open Syntax RuleBinding ScopedRuleMatching CanonicalBags CollectionSelection
open CollectionMatcherCompatibility

private theorem finished_literal {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
    {rest : Option String} {kind : CollType} {initial final : Assignment} {targets : List Pattern}
    (finished : Finished literalBodyComparison rule spec ambient site path depth index rest kind
      initial targets final) :
    ScopedCollectionMatching.Finished rule spec ambient site path depth index kind rest
      initial targets final := by
  cases rest with
  | none =>
    obtain ⟨rfl, rfl⟩ := finished
    exact .empty
  | some name =>
    exact .captured (by simpa only [Finished, captureRestWith?_literal] using finished)

mutual
theorem meaning_has_ordinary_presentation {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial final : Assignment} {schema target : Pattern}
    (matched : Meaning literalBodyComparison rule spec ambient site path depth initial schema target final) :
    ∃ presented, Same target presented ∧
      GeneralScopedMatch.Matches rule spec ambient site path depth initial schema presented final := by
  cases schema with
  | fvar name =>
    exact ⟨target, rfl, .capture (by simpa only [Meaning, captureWith?_literal] using matched)⟩
  | bvar index =>
    cases target <;> simp only [Meaning] at matched
    obtain ⟨rfl, rfl⟩ := matched
    exact ⟨_, rfl, .bound⟩
  | apply label schemas =>
    cases target <;> simp only [Meaning] at matched
    rename_i actual targets
    obtain ⟨rfl, rows⟩ := matched
    obtain ⟨presented, same, ordinary⟩ := arguments_has_ordinary_presentation rows
    exact ⟨.apply label presented, same_apply_congr _ same, .constructor ordinary⟩
  | lambda display body =>
    cases target <;> simp only [Meaning] at matched
    rename_i targetDisplay targetBody
    obtain ⟨presented, same, ordinary⟩ := meaning_has_ordinary_presentation matched
    exact ⟨.lambda targetDisplay presented, same_lambda_congr _ same, .binder ordinary⟩
  | multiLambda arity display body =>
    cases target <;> simp only [Meaning] at matched
    rename_i actualArity targetDisplay targetBody
    obtain ⟨rfl, matched⟩ := matched
    obtain ⟨presented, same, ordinary⟩ := meaning_has_ordinary_presentation matched
    exact ⟨.multiLambda arity targetDisplay presented,
      same_multiLambda_congr _ _ same, .binders ordinary⟩
  | subst body replacement =>
    cases target <;> simp only [Meaning] at matched
    obtain ⟨middle, head, tail⟩ := matched
    obtain ⟨body', sameBody, ordinaryBody⟩ := meaning_has_ordinary_presentation head
    obtain ⟨replacement', sameReplacement, ordinaryReplacement⟩ := meaning_has_ordinary_presentation tail
    exact ⟨.subst body' replacement', same_subst_congr sameBody sameReplacement,
      .substitution ordinaryBody ordinaryReplacement⟩
  | collection kind schemas rest =>
    cases target <;> simp only [Meaning.eq_def] at matched
    rename_i actual targets actualRest
    obtain ⟨sameKind, restNone, matched⟩ := matched
    subst actual
    subst actualRest
    by_cases vector : kind = .vec
    · subst kind
      simp only [↓reduceIte] at matched
      cases rest with
      | none =>
        obtain ⟨presented, same, ordinary⟩ := arguments_has_ordinary_presentation matched
        exact ⟨.collection .vec presented none, same_collection_congr _ _ same, .vector ordinary⟩
      | some name =>
        obtain ⟨middle, rows, captured⟩ := matched
        obtain ⟨presented, same, ordinary⟩ := arguments_has_ordinary_presentation rows
        have length : presented.length = schemas.length :=
          same.length_eq.symm.trans (arguments_length rows).symm
        have sourceSame : Same (.collection .vec targets none)
            (.collection .vec (presented ++ targets.drop schemas.length) none) := by
          apply same_collection_congr
          simpa only [List.take_append_drop] using
            List.rel_append same (forall₂_same_of_map
              (targets := targets.drop schemas.length) rfl)
        refine ⟨_, sourceSame, .vectorRest (middle := middle) ?_ ?_⟩
        · simpa only [← length, List.take_left] using ordinary
        · simpa only [← length, List.drop_left, captureRestWith?_literal] using captured
    · simp only [vector, ↓reduceIte] at matched
      obtain ⟨values, residual, middle, presents, rows, finished⟩ := matched
      obtain ⟨presented, same, ordinary⟩ := arguments_has_ordinary_presentation rows
      have sourceSame : Same (.collection kind targets none)
          (.collection kind (values ++ arrange kind residual) none) :=
        (same_iff _ _).mpr
          (collection_equivalent_of_presents vector (presents_append_arrange presents))
      have valuesSame : Same (.collection kind (values ++ arrange kind residual) none)
          (.collection kind (presented ++ arrange kind residual) none) :=
        same_collection_congr _ _ (List.rel_append same (forall₂_same_of_map rfl))
      refine ⟨_, sourceSame.trans valuesSame, .bag vector ?_⟩
      exact bag_of_arguments_finished ordinary (by
        simpa only [Nat.zero_add] using finished_literal finished)
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

theorem arguments_has_ordinary_presentation {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
    {initial final : Assignment} {schemas targets : List Pattern}
    (matched : ArgumentsMeaning literalBodyComparison rule spec ambient site path depth
      initial index schemas targets final) :
    ∃ presented, List.Forall₂ Same targets presented ∧
      GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas presented final := by
  cases schemas with
  | nil =>
    cases targets <;> simp only [ArgumentsMeaning] at matched
    subst final
    exact ⟨[], .nil, .nil⟩
  | cons schema schemas =>
    cases targets <;> simp only [ArgumentsMeaning] at matched
    obtain ⟨middle, head, tail⟩ := matched
    obtain ⟨first, firstSame, firstOrdinary⟩ := meaning_has_ordinary_presentation head
    obtain ⟨rest, restSame, restOrdinary⟩ := arguments_has_ordinary_presentation tail
    exact ⟨first :: rest, .cons firstSame restSame, .cons firstOrdinary restOrdinary⟩
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

/-- Every recursive executable answer has an ordinary source-matching
witness at an equivalent presentation, including all nested set choices. -/
theorem runAt_has_ordinary_presentation {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial final : Assignment} {schema target : Pattern}
    (member : final ∈ runAt literalBodyComparison rule spec ambient site path depth initial schema target) :
    ∃ presented trace, Same target presented ∧
      GeneralScopedMatchMachine.TracedMatches rule spec ambient site path depth initial
        schema presented trace final := by
  obtain ⟨presented, same, ordinary⟩ := meaning_has_ordinary_presentation
    ((runAt_exact literalBodyComparison rule spec ambient site path depth initial schema target final).mp member)
  obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.matches_trace ordinary
  exact ⟨presented, trace, same, traced⟩

end Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching
