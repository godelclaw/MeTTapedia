import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaInstantiationObjects

/-!
# Canonical metadata survives contextual projection

Binder displays are preserved by context reindexing. Executing a substitution
preserves canonical metadata when its two operands are canonical. These laws
apply to actual captured values and ordinary premise instantiation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching Substitution
open Mettapedia.GSLT.LanguageDef.WellSorted

def CanonicalValues (assignment : Assignment) : Prop :=
  ∀ name value, lookup assignment name = some value → value.body.hasCanonicalBinderMetadata = true

theorem contextSubstitute_canonical {body : Pattern} {assignment : ContextSubstitution.Assignment}
    (canonical : body.hasCanonicalBinderMetadata = true)
    (images : ∀ index, (assignment index).hasCanonicalBinderMetadata = true) :
    (ContextSubstitution.substitute assignment body).hasCanonicalBinderMetadata = true := by
  induction body using Pattern.inductionOn generalizing assignment with
  | hbvar index => exact images index
  | hfvar name => rfl
  | happly constructor arguments ih =>
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
        Pattern.hasCanonicalBinderMetadata] at canonical ⊢
      apply (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mpr
      intro actual member
      rcases List.mem_map.mp member with ⟨argument, argumentMember, rfl⟩
      exact ih argument argumentMember
        ((Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp canonical argument argumentMember) images
  | hlambda binder body ih =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      simp only [ContextSubstitution.substitute, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true]
      refine ⟨canonical.1, ih canonical.2 ?_⟩
      intro index
      simp only [ContextSubstitution.lift]
      split
      · rfl
      · simpa only [hasCanonicalBinderMetadata_liftBVars] using images (index - 1)
  | hmultiLambda arity binders body ih =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      simp only [ContextSubstitution.substitute, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true]
      refine ⟨canonical.1, ih canonical.2 ?_⟩
      intro index
      simp only [ContextSubstitution.lift]
      split
      · rfl
      · simpa only [hasCanonicalBinderMetadata_liftBVars] using images (index - arity)
  | hsubst body replacement bodyIH replacementIH =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      simp only [ContextSubstitution.substitute, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true]
      refine ⟨bodyIH canonical.1 ?_, replacementIH canonical.2 images⟩
      intro index
      simp only [ContextSubstitution.lift]
      split
      · rfl
      · simpa only [hasCanonicalBinderMetadata_liftBVars] using images (index - 1)
  | hcollection kind elements rest ih =>
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
        Pattern.hasCanonicalBinderMetadata] at canonical ⊢
      apply (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mpr
      intro actual member
      rcases List.mem_map.mp member with ⟨element, elementMember, rfl⟩
      exact ih element elementMember
        ((Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp canonical element elementMember) images

theorem instantiateBVarAt_canonical {body replacement : Pattern} (depth : Nat)
    (bodyCanonical : body.hasCanonicalBinderMetadata = true)
    (replacementCanonical : replacement.hasCanonicalBinderMetadata = true) :
    (instantiateBVarAt depth replacement body).hasCanonicalBinderMetadata = true := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      simp only [instantiateBVarAt]
      split
      · rfl
      · split
        · simpa only [hasCanonicalBinderMetadata_liftBVars] using replacementCanonical
        · rfl
  | hfvar name => simp only [instantiateBVarAt, Pattern.hasCanonicalBinderMetadata]
  | happly constructor arguments ih =>
      simp only [Pattern.hasCanonicalBinderMetadata] at bodyCanonical
      simp only [instantiateBVarAt, Pattern.hasCanonicalBinderMetadata]
      apply (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mpr
      intro actual member
      rcases List.mem_map.mp member with ⟨argument, argumentMember, rfl⟩
      exact ih argument argumentMember depth
        ((Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp bodyCanonical argument argumentMember)
  | hlambda binder body ih =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at bodyCanonical
      simp only [instantiateBVarAt, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true]
      exact ⟨bodyCanonical.1, ih (depth + 1) bodyCanonical.2⟩
  | hmultiLambda arity binders body ih =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at bodyCanonical
      simp only [instantiateBVarAt, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true]
      exact ⟨bodyCanonical.1, ih (depth + arity) bodyCanonical.2⟩
  | hsubst body replacement bodyIH replacementIH =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at bodyCanonical
      simp only [instantiateBVarAt, Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true]
      exact ⟨bodyIH (depth + 1) bodyCanonical.1, replacementIH depth bodyCanonical.2⟩
  | hcollection kind elements rest ih =>
      simp only [Pattern.hasCanonicalBinderMetadata] at bodyCanonical
      simp only [instantiateBVarAt, Pattern.hasCanonicalBinderMetadata]
      apply (Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mpr
      intro actual member
      rcases List.mem_map.mp member with ⟨element, elementMember, rfl⟩
      exact ih element elementMember depth
        ((Pattern.hasCanonicalBinderMetadataList_eq_true_iff _).mp bodyCanonical element elementMember)

theorem instantiateValue?_canonical {value : ContextualValue} {ambient depth : Nat}
    {actual : Pattern} (canonical : value.body.hasCanonicalBinderMetadata = true)
    (projected : instantiateValue? value ambient depth [] = some actual) :
    actual.hasCanonicalBinderMetadata = true := by
  unfold instantiateValue? at projected
  split at projected <;> try contradiction
  split at projected <;> try contradiction
  split at projected <;> try contradiction
  split at projected <;> try contradiction
  dsimp only at projected
  split at projected <;> try contradiction
  rw [← Option.some.inj projected]
  apply contextSubstitute_canonical canonical
  intro index
  simp only [occurrenceAssignment]
  split
  · simp [List.getD, Pattern.hasCanonicalBinderMetadata]
  · rfl

mutual
  theorem instantiateAt?_canonical
      {context : Context} {assignment : Assignment} {depth : Nat}
      {site : RulePatternSite} {path : List Nat} {schema actual : Pattern}
      (values : CanonicalValues assignment)
      (canonical : schema.hasCanonicalBinderMetadata = true)
      (checked : checkRootProjectionSchema context.rule context.spec site path schema = true)
      (projected : instantiateAt? context.rule context.spec context.bound.length site path
        depth assignment schema = some actual) : actual.hasCanonicalBinderMetadata = true := by
    cases schema with
    | bvar index =>
        simp only [instantiateAt?, instantiateWith?, Option.some.injEq] at projected
        subst actual
        rfl
    | fvar name =>
        have arguments : arguments? context.rule context.spec name site path = some [] := beq_iff_eq.mp checked
        simp only [instantiateAt?, instantiateWith?, arguments, Option.bind_eq_bind,
          Option.bind_some, Option.bind_eq_some_iff] at projected
        obtain ⟨value, found, projected⟩ := projected
        exact instantiateValue?_canonical (values name value found) projected
    | apply constructor arguments =>
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualArguments, read, same⟩ := projected
        subst actual
        exact instantiateArgsAt?_canonical values canonical checked read
    | lambda binder body =>
        have bodyChecked : checkRootProjectionSchema context.rule context.spec site (path ++ [0]) body = true := checked
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualBody, read, same⟩ := projected
        subst actual
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true]
        exact ⟨canonical.1, instantiateAt?_canonical values canonical.2 bodyChecked read⟩
    | multiLambda arity binders body =>
        have bodyChecked : checkRootProjectionSchema context.rule context.spec site (path ++ [0]) body = true := checked
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualBody, read, same⟩ := projected
        subst actual
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true]
        exact ⟨canonical.1, instantiateAt?_canonical values canonical.2 bodyChecked read⟩
    | subst body replacement =>
        simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
        simp only [checkRootProjectionSchema, Bool.and_eq_true] at checked
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualBody, bodyRead, actualReplacement, replacementRead, same⟩ := projected
        subst actual
        exact instantiateBVarAt_canonical 0
          (instantiateAt?_canonical values canonical.1 checked.1 bodyRead)
          (instantiateAt?_canonical values canonical.2 checked.2 replacementRead)
    | collection kind elements rest =>
        simp only [checkRootProjectionSchema, Bool.and_eq_true, Option.isNone_iff_eq_none] at checked
        rcases checked with ⟨restNone, checked⟩
        subst restNone
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualElements, read, same⟩ := projected
        subst actual
        exact instantiateArgsAt?_canonical values canonical checked read
  termination_by sizeOf schema
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem instantiateArgsAt?_canonical
      {context : Context} {assignment : Assignment} {depth index : Nat}
      {site : RulePatternSite} {path : List Nat} {schemas actuals : List Pattern}
      (values : CanonicalValues assignment)
      (canonical : Pattern.hasCanonicalBinderMetadataList schemas = true)
      (checked : checkRootProjectionArguments context.rule context.spec site path index schemas = true)
      (projected : instantiateArgsWith? instantiateBVar context.rule context.spec context.bound.length
        site path depth assignment index schemas = some actuals) :
      Pattern.hasCanonicalBinderMetadataList actuals = true := by
    cases schemas with
    | nil => simp only [instantiateArgsWith?, Option.some.injEq] at projected; subst actuals; rfl
    | cons head tail =>
        simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at canonical
        simp only [checkRootProjectionArguments, Bool.and_eq_true] at checked
        simp only [instantiateArgsWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualHead, headRead, actualTail, tailRead, same⟩ := projected
        subst actuals
        simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
        exact ⟨instantiateAt?_canonical values canonical.1 checked.1 headRead,
          instantiateArgsAt?_canonical values canonical.2 checked.2 tailRead⟩
  termination_by sizeOf schemas
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega
end

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
