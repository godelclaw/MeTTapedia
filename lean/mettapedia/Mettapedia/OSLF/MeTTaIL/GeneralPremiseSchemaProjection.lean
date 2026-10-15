import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProjectionTotality

/-!
# Static checks for total structural occurrence interpretation

The check reads the actual occurrence substitution at every schema variable.
An empty dependency spine permits total projection under any binder prefix.
Constructor, binder and explicit-substitution nodes are interpreted by the
existing scoped traversal. Symbolic collection tails require an additional
representation check and are kept outside this admission class.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching

mutual
  def checkRootProjectionSchema (rule : RewriteRule) (spec : RuleBindingSpec)
      (site : RulePatternSite) (path : List Nat) : Pattern → Bool
    | .fvar name => arguments? rule spec name site path == some []
    | .bvar _ => true
    | .apply _ arguments => checkRootProjectionArguments rule spec site path 0 arguments
    | .lambda _ body | .multiLambda _ _ body =>
        checkRootProjectionSchema rule spec site (path ++ [0]) body
    | .subst body replacement =>
        checkRootProjectionSchema rule spec site (path ++ [0]) body &&
          checkRootProjectionSchema rule spec site (path ++ [1]) replacement
    | .collection _ elements rest =>
        rest.isNone && checkRootProjectionArguments rule spec site path 0 elements

  def checkRootProjectionArguments (rule : RewriteRule) (spec : RuleBindingSpec)
      (site : RulePatternSite) (path : List Nat) (index : Nat) : List Pattern → Bool
    | [] => true
    | pattern :: patterns =>
        checkRootProjectionSchema rule spec site (path ++ [index]) pattern &&
          checkRootProjectionArguments rule spec site path (index + 1) patterns
end

mutual
  theorem checkRootProjectionSchema_sound (operation : Pattern → Pattern → Pattern)
      {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
      {site : RulePatternSite} {path : List Nat} {assignment : Assignment} {schema : Pattern}
      (checked : checkRootProjectionSchema rule spec site path schema = true)
      (values : RootValues ambient assignment) (bound : BoundNames assignment schema.freeFvarNames) :
      ∃ result, instantiateWith? operation rule spec ambient site path depth assignment schema = some result :=
    match schema with
    | .fvar name => by
        have declared : arguments? rule spec name site path = some [] := beq_iff_eq.mp checked
        obtain ⟨value, found⟩ := bound name (by simp [Pattern.freeFvarNames])
        obtain ⟨actual, read⟩ := (values name value found).project depth
        exact ⟨actual, by simp only [instantiateWith?, Option.bind_eq_bind, found, declared, read, Option.bind_some]⟩
    | .bvar index => ⟨.bvar index, by simp only [instantiateWith?]⟩
    | .apply constructor arguments => by
        obtain ⟨actual, read⟩ := checkRootProjectionArguments_sound operation (depth := depth)
          (by simpa only [checkRootProjectionSchema] using checked) values
          (by simpa only [Pattern.freeFvarNames] using bound)
        exact ⟨.apply constructor actual, by simp only [instantiateWith?, Option.bind_eq_bind, read, Option.bind_some]⟩
    | .lambda binder body => by
        obtain ⟨actual, read⟩ := checkRootProjectionSchema_sound operation (schema := body) (depth := depth + 1)
          (by simpa only [checkRootProjectionSchema] using checked) values
          (by simpa only [Pattern.freeFvarNames] using bound)
        exact ⟨.lambda binder actual, by simp only [instantiateWith?, Option.bind_eq_bind, read, Option.bind_some]⟩
    | .multiLambda arity binders body => by
        obtain ⟨actual, read⟩ := checkRootProjectionSchema_sound operation (schema := body) (depth := depth + arity)
          (by simpa only [checkRootProjectionSchema] using checked) values
          (by simpa only [Pattern.freeFvarNames] using bound)
        exact ⟨.multiLambda arity binders actual, by simp only [instantiateWith?, Option.bind_eq_bind, read, Option.bind_some]⟩
    | .subst body replacement => by
        simp only [checkRootProjectionSchema, Bool.and_eq_true] at checked
        have bodyBound : BoundNames assignment body.freeFvarNames := by
          intro name member
          exact bound name (by simpa only [Pattern.freeFvarNames] using
            List.mem_append.mpr (Or.inl member))
        have replacementBound : BoundNames assignment replacement.freeFvarNames := by
          intro name member
          exact bound name (by simpa only [Pattern.freeFvarNames] using
            List.mem_append.mpr (Or.inr member))
        obtain ⟨actualBody, bodyRead⟩ := checkRootProjectionSchema_sound operation (depth := depth + 1) checked.1 values bodyBound
        obtain ⟨actualReplacement, replacementRead⟩ :=
          checkRootProjectionSchema_sound operation (depth := depth) checked.2 values replacementBound
        exact ⟨operation actualReplacement actualBody, by
          simp only [instantiateWith?, Option.bind_eq_bind, bodyRead, replacementRead, Option.bind_some]⟩
    | .collection kind elements rest => by
        simp only [checkRootProjectionSchema, Bool.and_eq_true, Option.isNone_iff_eq_none] at checked
        obtain ⟨actual, read⟩ := checkRootProjectionArguments_sound operation (depth := depth) checked.2 values
          (by simpa only [Pattern.freeFvarNames, checked.1, Option.toList_none, List.append_nil] using bound)
        exact ⟨.collection kind actual none, by
          simp only [instantiateWith?, Option.bind_eq_bind, checked.1, read, Option.bind_some]⟩

  theorem checkRootProjectionArguments_sound (operation : Pattern → Pattern → Pattern)
      {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth index : Nat}
      {site : RulePatternSite} {path : List Nat} {assignment : Assignment} {schemas : List Pattern}
      (checked : checkRootProjectionArguments rule spec site path index schemas = true)
      (values : RootValues ambient assignment)
      (bound : BoundNames assignment (schemas.flatMap Pattern.freeFvarNames)) :
      ∃ results, instantiateArgsWith? operation rule spec ambient site path depth assignment index schemas = some results :=
    match schemas with
    | [] => ⟨[], by simp only [instantiateArgsWith?]⟩
    | schema :: schemas => by
        simp only [checkRootProjectionArguments, Bool.and_eq_true] at checked
        have headBound : BoundNames assignment schema.freeFvarNames := by
          intro name member
          exact bound name (by simp only [List.flatMap_cons]; exact List.mem_append.mpr (Or.inl member))
        have tailBound : BoundNames assignment (schemas.flatMap Pattern.freeFvarNames) := by
          intro name member
          exact bound name (by simp only [List.flatMap_cons]; exact List.mem_append.mpr (Or.inr member))
        obtain ⟨head, headRead⟩ := checkRootProjectionSchema_sound operation (depth := depth) checked.1 values headBound
        obtain ⟨tail, tailRead⟩ := checkRootProjectionArguments_sound operation (depth := depth) checked.2 values tailBound
        exact ⟨head :: tail, by simp only [instantiateArgsWith?, Option.bind_eq_bind, headRead, tailRead, Option.bind_some]⟩
end

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
