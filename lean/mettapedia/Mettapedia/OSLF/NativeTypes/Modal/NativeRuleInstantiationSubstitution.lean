import Mettapedia.OSLF.NativeTypes.Modal.NativeBinderOperationSubstitution

/-!
# Substitution of actual authored rule instantiation

The comparison uses each occurrence's depth from the authored declaration,
its checked dependency arguments and the original scoped assignment. It
covers binders, explicit substitution and ordered residual collection
expansion. Ordinary binder elimination has a proved substitution square.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeRuleInstantiationSubstitution

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching

mutual
theorem successful_substitutes {rule : RewriteRule} {spec : RuleBindingSpec}
    {source target depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial : Assignment} {schema actual : Pattern}
    (accepted : instantiateWith? Substitution.instantiateBVar rule spec source site path depth initial schema = some actual)
    (admitted : admittedFor rule spec = true)
    (coherent : DepthCoherent rule site path depth schema)
    (localScope : schema.isWellScopedAt depth = true)
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    instantiateWith? Substitution.instantiateBVar rule spec target site path depth
      (NativeContextualSubstitution.assignment target substitution initial) schema =
      some (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution) actual) := by
  cases schema with
  | fvar name =>
      simp only [instantiateWith?, Option.bind_eq_bind] at accepted ⊢
      cases stored : lookup initial name with
      | none => simp only [stored, Option.bind_none] at accepted; contradiction
      | some value =>
          simp only [stored, Option.bind_some] at accepted
          cases decoded : arguments? rule spec name site path with
          | none => simp only [decoded, Option.bind_none] at accepted; contradiction
          | some arguments =>
              simp only [decoded, Option.bind_some] at accepted
              rw [NativeContextualSubstitution.lookup_assignment, stored]
              simp only [Option.map_some, Option.bind_some]
              exact NativeValueInstantiationSubstitution.successful_instantiation_substitutes accepted
                (NativeRuleOccurrenceScope.decoded_scopes admitted coherent.fvar decoded) substitution boundScoped
  | bvar index =>
      simp only [instantiateWith?] at accepted
      have within := of_decide_eq_true localScope
      have same := Option.some.inj accepted
      cases same
      simp only [instantiateWith?, ContextSubstitution.substitute, ContextSubstitution.lift,
        within, ite_true]
  | apply constructor arguments =>
      simp only [instantiateWith?, Option.bind_eq_bind] at accepted ⊢
      cases interpreted : instantiateArgsWith? Substitution.instantiateBVar rule spec source site path depth initial 0 arguments with
      | none => simp only [interpreted, Option.bind_none] at accepted; contradiction
      | some values =>
          simp only [interpreted, Option.bind_some] at accepted
          have same := Option.some.inj accepted
          cases same
          rw [arguments_substitute interpreted admitted coherent.constructorArguments localScope substitution boundScoped]
          simp only [Option.bind_some, ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
  | lambda binder body =>
      simp only [instantiateWith?, Option.bind_eq_bind] at accepted ⊢
      cases interpreted : instantiateWith? Substitution.instantiateBVar rule spec source site (path ++ [0]) (depth + 1) initial body with
      | none => simp only [interpreted, Option.bind_none] at accepted; contradiction
      | some value =>
          simp only [interpreted, Option.bind_some] at accepted
          have same := Option.some.inj accepted
          cases same
          rw [successful_substitutes interpreted admitted coherent.lambda localScope substitution boundScoped]
          simp only [Option.bind_some, ContextSubstitution.substitute, ContextSubstitution.lift_lift]
  | multiLambda arity binders body =>
      simp only [instantiateWith?, Option.bind_eq_bind] at accepted ⊢
      cases interpreted : instantiateWith? Substitution.instantiateBVar rule spec source site (path ++ [0]) (depth + arity) initial body with
      | none => simp only [interpreted, Option.bind_none] at accepted; contradiction
      | some value =>
          simp only [interpreted, Option.bind_some] at accepted
          have same := Option.some.inj accepted
          cases same
          rw [successful_substitutes interpreted admitted coherent.multiLambda localScope substitution boundScoped]
          simp only [Option.bind_some, ContextSubstitution.substitute, ContextSubstitution.lift_lift]
  | subst body replacement =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at localScope
      simp only [instantiateWith?, Option.bind_eq_bind] at accepted ⊢
      cases interpretedBody : instantiateWith? Substitution.instantiateBVar rule spec source site (path ++ [0]) (depth + 1) initial body with
      | none => simp only [interpretedBody, Option.bind_none] at accepted; contradiction
      | some bodyValue =>
          simp only [interpretedBody, Option.bind_some] at accepted
          cases interpretedReplacement : instantiateWith? Substitution.instantiateBVar rule spec source site (path ++ [1]) depth initial replacement with
          | none => simp only [interpretedReplacement, Option.bind_none] at accepted; contradiction
          | some replacementValue =>
              simp only [interpretedReplacement, Option.bind_some] at accepted
              have same := Option.some.inj accepted
              cases same
              rw [successful_substitutes interpretedBody admitted coherent.substitutionBody localScope.1 substitution boundScoped]
              simp only [Option.bind_some]
              rw [successful_substitutes interpretedReplacement admitted coherent.substitutionReplacement localScope.2 substitution boundScoped]
              simp only [Option.bind_some]
              rw [NativeBinderOperationSubstitution.ordinary, ContextSubstitution.lift_lift]
  | collection kind elements rest =>
      simp only [instantiateWith?, Option.bind_eq_bind] at accepted ⊢
      cases interpreted : instantiateArgsWith? Substitution.instantiateBVar rule spec source site path depth initial 0 elements with
      | none => simp only [interpreted, Option.bind_none] at accepted; contradiction
      | some values =>
          simp only [interpreted, Option.bind_some] at accepted
          rw [arguments_substitute interpreted admitted coherent.collectionArguments localScope substitution boundScoped]
          simp only [Option.bind_some]
          cases rest with
          | none =>
              have same := Option.some.inj accepted
              cases same
              simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
          | some name =>
              dsimp only at ⊢
              cases stored : lookup initial name with
              | none => simp only [stored, Option.bind_none] at accepted; contradiction
              | some value =>
                  simp only [stored, Option.bind_some] at accepted
                  cases decoded : arguments? rule spec name site (path ++ [elements.length]) with
                  | none => simp only [decoded, Option.bind_none] at accepted; contradiction
                  | some arguments =>
                      simp only [decoded, Option.bind_some] at accepted
                      cases instantiated : instantiateValue? value source depth arguments with
                      | none => simp only [instantiated, Option.bind_none] at accepted; contradiction
                      | some residual =>
                          simp only [instantiated, Option.bind_some] at accepted
                          rw [NativeContextualSubstitution.lookup_assignment, stored]
                          simp only [Option.map_some, Option.bind_some]
                          rw [NativeValueInstantiationSubstitution.successful_instantiation_substitutes instantiated
                            (NativeRuleOccurrenceScope.decoded_scopes admitted coherent.collectionRest decoded) substitution boundScoped]
                          simp only [Option.bind_some]
                          cases residual with
                          | collection actualKind remaining residualRest =>
                              cases residualRest with
                              | none =>
                                  dsimp only at accepted
                                  split at accepted <;> try contradiction
                                  rename_i sameKind
                                  have same := Option.some.inj accepted
                                  cases same
                                  simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
                                    sameKind, ite_true, List.map_append]
                              | some residualName => contradiction
                          | _ => contradiction
termination_by sizeOf schema

theorem arguments_substitute {rule : RewriteRule} {spec : RuleBindingSpec}
    {source target depth index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial : Assignment} {schemas actuals : List Pattern}
    (accepted : instantiateArgsWith? Substitution.instantiateBVar rule spec source site path depth initial index schemas = some actuals)
    (admitted : admittedFor rule spec = true)
    (coherent : ArgumentsDepthCoherent rule site path depth index schemas)
    (localScope : Pattern.isWellScopedListAt depth schemas = true)
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    instantiateArgsWith? Substitution.instantiateBVar rule spec target site path depth
      (NativeContextualSubstitution.assignment target substitution initial) index schemas =
      some (actuals.map (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution))) := by
  cases schemas with
  | nil =>
      simp only [instantiateArgsWith?] at accepted
      have same := Option.some.inj accepted
      cases same
      simp only [instantiateArgsWith?, List.map_nil]
  | cons schema schemas =>
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at localScope
      simp only [instantiateArgsWith?, Option.bind_eq_bind] at accepted ⊢
      cases interpretedHead : instantiateWith? Substitution.instantiateBVar rule spec source site (path ++ [index]) depth initial schema with
      | none => simp only [interpretedHead, Option.bind_none] at accepted; contradiction
      | some head =>
          simp only [interpretedHead, Option.bind_some] at accepted
          cases interpretedTail : instantiateArgsWith? Substitution.instantiateBVar rule spec source site path depth initial (index + 1) schemas with
          | none => simp only [interpretedTail, Option.bind_none] at accepted; contradiction
          | some tail =>
              simp only [interpretedTail, Option.bind_some] at accepted
              have same := Option.some.inj accepted
              cases same
              rw [successful_substitutes interpretedHead admitted coherent.head localScope.1 substitution boundScoped]
              simp only [Option.bind_some]
              rw [arguments_substitute interpretedTail admitted coherent.tail localScope.2 substitution boundScoped]
              rfl
termination_by sizeOf schemas
end

theorem instantiateAt_substitutes {rule : RewriteRule} {spec : RuleBindingSpec}
    {source target depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial : Assignment} {schema actual : Pattern}
    (accepted : instantiateAt? rule spec source site path depth initial schema = some actual)
    (admitted : admittedFor rule spec = true)
    (coherent : DepthCoherent rule site path depth schema)
    (localScope : schema.isWellScopedAt depth = true)
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    instantiateAt? rule spec target site path depth
      (NativeContextualSubstitution.assignment target substitution initial) schema =
      some (ContextSubstitution.substitute (ContextSubstitution.lift depth substitution) actual) :=
  successful_substitutes accepted admitted coherent localScope substitution boundScoped

theorem reduct_substitutes {rule : RewriteRule} {spec : RuleBindingSpec}
    {source target : Nat} {initial : Assignment} {actual : Pattern}
    (accepted : reduct? rule spec source initial = some actual)
    (admitted : admittedFor rule spec = true)
    (localScope : rule.right.isWellScopedAt 0 = true)
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    reduct? rule spec target (NativeContextualSubstitution.assignment target substitution initial) =
      some (ContextSubstitution.substitute substitution actual) := by
  simpa only [reduct?, ContextSubstitution.lift_zero] using
    instantiateAt_substitutes accepted admitted (depthCoherent_right rule) localScope substitution boundScoped

end Mettapedia.OSLF.NativeTypes.Modal.NativeRuleInstantiationSubstitution
