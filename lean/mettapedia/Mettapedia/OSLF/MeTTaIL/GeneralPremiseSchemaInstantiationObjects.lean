import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaInstantiationTyping
import Mettapedia.GSLT.LanguageDef.ContextSupport

/-!
# Object terms survive structural premise interpretation

Occurrence projection reindexes captured object terms. Explicit substitution
is executed, rather than left as an object-language node. The result therefore
has neither pending substitutions nor symbolic collection tails.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching Substitution
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem objectList_iff (patterns : List Pattern) :
    isObjectPatternList patterns = true ↔ ∀ pattern ∈ patterns, isObjectPattern pattern = true := by
  induction patterns with
  | nil => simp [isObjectPatternList]
  | cons head tail ih => simp [isObjectPatternList, ih]

theorem instantiateBVarAt_objects {body replacement : Pattern} (depth : Nat)
    (bodyObject : isObjectPattern body = true)
    (replacementObject : isObjectPattern replacement = true) :
    isObjectPattern (instantiateBVarAt depth replacement body) = true := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      simp only [instantiateBVarAt]
      split
      · rfl
      · split
        · simpa only [isObjectPattern_liftBVars] using replacementObject
        · rfl
  | hfvar name => simp only [instantiateBVarAt, isObjectPattern]
  | happly constructor arguments ih =>
      simp only [isObjectPattern] at bodyObject
      simp only [instantiateBVarAt, isObjectPattern]
      apply (objectList_iff _).mpr
      intro actual member
      rcases List.mem_map.mp member with ⟨argument, argumentMember, rfl⟩
      exact ih argument argumentMember depth ((objectList_iff _).mp bodyObject argument argumentMember)
  | hlambda binder body ih => simpa only [instantiateBVarAt, isObjectPattern] using ih (depth + 1) bodyObject
  | hmultiLambda arity binders body ih => simpa only [instantiateBVarAt, isObjectPattern] using ih (depth + arity) bodyObject
  | hsubst body replacement _ _ => simp [isObjectPattern] at bodyObject
  | hcollection kind elements rest ih =>
      simp only [isObjectPattern, Bool.and_eq_true] at bodyObject
      simp only [instantiateBVarAt, isObjectPattern, Bool.and_eq_true]
      refine ⟨bodyObject.1, (objectList_iff _).mpr ?_⟩
      intro actual member
      rcases List.mem_map.mp member with ⟨element, elementMember, rfl⟩
      exact ih element elementMember depth ((objectList_iff _).mp bodyObject.2 element elementMember)

theorem contextSubstitute_objects {body : Pattern} {assignment : ContextSubstitution.Assignment}
    (bodyObject : isObjectPattern body = true)
    (images : ∀ index, isObjectPattern (assignment index) = true) :
    isObjectPattern (ContextSubstitution.substitute assignment body) = true := by
  induction body using Pattern.inductionOn generalizing assignment with
  | hbvar index => exact images index
  | hfvar name => rfl
  | happly constructor arguments ih =>
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
        isObjectPattern] at bodyObject ⊢
      apply (objectList_iff _).mpr
      intro actual member
      rcases List.mem_map.mp member with ⟨argument, argumentMember, rfl⟩
      exact ih argument argumentMember ((objectList_iff _).mp bodyObject argument argumentMember) images
  | hlambda binder body ih =>
      apply ih bodyObject
      intro index
      simp only [ContextSubstitution.lift]
      split
      · rfl
      · simpa only [isObjectPattern_liftBVars] using images (index - 1)
  | hmultiLambda arity binders body ih =>
      apply ih bodyObject
      intro index
      simp only [ContextSubstitution.lift]
      split
      · rfl
      · simpa only [isObjectPattern_liftBVars] using images (index - arity)
  | hsubst body replacement _ _ => simp [isObjectPattern] at bodyObject
  | hcollection kind elements rest ih =>
      simp only [isObjectPattern, Bool.and_eq_true] at bodyObject
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
        isObjectPattern, Bool.and_eq_true]
      refine ⟨bodyObject.1, (objectList_iff _).mpr ?_⟩
      intro actual member
      rcases List.mem_map.mp member with ⟨element, elementMember, rfl⟩
      exact ih element elementMember ((objectList_iff _).mp bodyObject.2 element elementMember) images

/-- Successful inverse occurrence substitution retains objecthood of
the supplied target. The inverse maps indices to indices and introduces
neither pending substitutions nor symbolic collection tails. -/
theorem recoverValue?_objects {dependencies : List TypeExpr} {ambient depth : Nat}
    {arguments : List Pattern} {target : Pattern} {value : ContextualValue}
    (object : isObjectPattern target = true)
    (recovered : recoverValue? dependencies ambient depth arguments target = some value) :
    isObjectPattern value.body = true := by
  unfold recoverValue? at recovered
  split at recovered <;> try contradiction
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at recovered
  obtain ⟨indices, _, recovered⟩ := recovered
  split at recovered <;> try contradiction
  split at recovered <;> try contradiction
  cases Option.some.inj recovered
  apply contextSubstitute_objects object
  intro index
  simp only [recoveryAssignment]
  split
  · split <;> rfl
  · rfl

#print axioms recoverValue?_objects

theorem instantiateValue?_objects {value : ContextualValue} {ambient depth : Nat}
    {actual : Pattern} (object : isObjectPattern value.body = true)
    (projected : instantiateValue? value ambient depth [] = some actual) :
    isObjectPattern actual = true := by
  unfold instantiateValue? at projected
  split at projected <;> try contradiction
  split at projected <;> try contradiction
  split at projected <;> try contradiction
  split at projected <;> try contradiction
  dsimp only at projected
  split at projected <;> try contradiction
  have same := Option.some.inj projected
  rw [← same]
  apply contextSubstitute_objects object
  intro index
  simp only [occurrenceAssignment]
  split
  · simp [List.getD, isObjectPattern]
  · rfl

mutual
  theorem instantiateAt?_objects
      {context : Context} {assignment : Assignment} {depth : Nat}
      {site : RulePatternSite} {path : List Nat} {schema actual : Pattern}
      (objects : ConditionalEquationExecution.AssignmentObjects assignment)
      (checked : checkRootProjectionSchema context.rule context.spec site path schema = true)
      (projected : instantiateAt? context.rule context.spec context.bound.length site path
        depth assignment schema = some actual) : isObjectPattern actual = true := by
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
        exact instantiateValue?_objects (objects name value
          (ConditionalEquationExecution.lookup_assignment_member _ _ _ found)) projected
    | apply constructor arguments =>
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualArguments, read, same⟩ := projected
        subst actual
        exact instantiateArgsAt?_objects objects checked read
    | lambda binder body =>
        have bodyChecked : checkRootProjectionSchema context.rule context.spec site (path ++ [0]) body = true := checked
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualBody, read, same⟩ := projected
        subst actual
        change isObjectPattern actualBody = true
        exact instantiateAt?_objects objects bodyChecked read
    | multiLambda arity binders body =>
        have bodyChecked : checkRootProjectionSchema context.rule context.spec site (path ++ [0]) body = true := checked
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualBody, read, same⟩ := projected
        subst actual
        change isObjectPattern actualBody = true
        exact instantiateAt?_objects objects bodyChecked read
    | subst body replacement =>
        simp only [checkRootProjectionSchema, Bool.and_eq_true] at checked
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualBody, bodyRead, actualReplacement, replacementRead, same⟩ := projected
        subst actual
        exact instantiateBVarAt_objects 0
          (instantiateAt?_objects objects checked.1 bodyRead)
          (instantiateAt?_objects objects checked.2 replacementRead)
    | collection kind elements rest =>
        simp only [checkRootProjectionSchema, Bool.and_eq_true, Option.isNone_iff_eq_none] at checked
        rcases checked with ⟨restNone, checked⟩
        subst restNone
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualElements, read, same⟩ := projected
        subst actual
        simp only [isObjectPattern, Option.isNone_none, Bool.true_and]
        exact instantiateArgsAt?_objects objects checked read
  termination_by sizeOf schema
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem instantiateArgsAt?_objects
      {context : Context} {assignment : Assignment} {depth index : Nat}
      {site : RulePatternSite} {path : List Nat} {schemas actuals : List Pattern}
      (objects : ConditionalEquationExecution.AssignmentObjects assignment)
      (checked : checkRootProjectionArguments context.rule context.spec site path index schemas = true)
      (projected : instantiateArgsWith? instantiateBVar context.rule context.spec context.bound.length
        site path depth assignment index schemas = some actuals) : isObjectPatternList actuals = true := by
    cases schemas with
    | nil => simp only [instantiateArgsWith?, Option.some.injEq] at projected; subst actuals; rfl
    | cons head tail =>
        simp only [checkRootProjectionArguments, Bool.and_eq_true] at checked
        simp only [instantiateArgsWith?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.some.injEq] at projected
        obtain ⟨actualHead, headRead, actualTail, tailRead, same⟩ := projected
        subst actuals
        simp only [isObjectPatternList, Bool.and_eq_true]
        exact ⟨instantiateAt?_objects objects checked.1 headRead,
          instantiateArgsAt?_objects objects checked.2 tailRead⟩
  termination_by sizeOf schemas
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega
end

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
