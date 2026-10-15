import Mettapedia.OSLF.MeTTaIL.GeneralPremiseAdmission

/-!
# Source-head coverage for declaration-derived step strata

Scoped instantiation does not change an authored constructor head. Independent
matching can match that head only with the same constructor or a metavariable.
Thus the conservative child classifier covers every actual child firing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleMatchingHeads

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch GeneralPremise

theorem instantiate_constructor_head {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat} {assignment : Assignment}
    {label : String} {arguments : List Pattern} {result : Pattern}
    (interpreted : instantiateAt? rule spec ambient site path depth assignment
      (.apply label arguments) = some result) :
    ∃ results, result = .apply label results := by
  simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at interpreted
  obtain ⟨results, _, equality⟩ := interpreted
  exact ⟨results, (Option.some.inj equality).symm⟩

theorem matches_constructor_head {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {pattern : Pattern} {label : String} {targets : List Pattern}
    (matched : Matches rule spec ambient site path depth initial pattern (.apply label targets) final) :
    (∃ name, pattern = .fvar name) ∨ (∃ arguments, pattern = .apply label arguments) := by
  cases matched with
  | capture => exact Or.inl ⟨_, rfl⟩
  | constructor => exact Or.inr ⟨_, rfl⟩

theorem potentialChild_actual {parent child : RewriteRule} {parentSpec childSpec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {assignment captured : Assignment} {schema source : Pattern}
    (interpreted : instantiateAt? parent parentSpec ambient site path depth assignment schema = some source)
    (matched : Matches child childSpec (depth + ambient) .left [] 0 [] child.left source captured) :
    potentialChild schema child = true := by
  cases schema with
  | apply label arguments =>
      obtain ⟨results, same⟩ := instantiate_constructor_head interpreted
      subst source
      rcases matches_constructor_head matched with ⟨name, same⟩ | ⟨arguments, same⟩ <;>
        simp only [potentialChild, same, beq_self_eq_true]
  | bvar _ | fvar _ | lambda _ _ | multiLambda _ _ _ | subst _ _ | collection _ _ _ =>
      simp only [potentialChild]

theorem actual_child_stratum {language : LanguageDef}
    (checked : checkStepStratification language = true)
    {parent child : RewriteRule} {parentSpec childSpec : RuleBindingSpec}
    {parentIndex childIndex ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {assignment captured : Assignment} {schema source : Pattern}
    (parentAuthored : (parent, parentIndex) ∈ language.rewrites.zipIdx)
    (childAuthored : (child, childIndex) ∈ language.rewrites.zipIdx)
    (called : schema ∈ parent.premises.flatMap stepSources)
    (interpreted : instantiateAt? parent parentSpec ambient site path depth assignment schema = some source)
    (matched : Matches child childSpec (depth + ambient) .left [] 0 [] child.left source captured) :
    childIndex < parentIndex :=
  checkStepStratification_child language checked parent child parentIndex childIndex
    parentAuthored childAuthored schema called (potentialChild_actual interpreted matched)

end Mettapedia.OSLF.MeTTaIL.GeneralRuleMatchingHeads
