import Mettapedia.OSLF.NativeTypes.Modal.NativePremiseSubstitutionBase

/-!
# Forward substitution of actual positive query receipts

Both input evaluation and output matching preserve their original argument
indices, bag-choice traces, row index and ordered assignment. Closed provider
rows are reused unchanged. This is forward preservation; substitution may
create a previously unmatched query, so reflection is not asserted.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeQuerySubstitution

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open NativePremiseSubstitutionBase

def ArgumentsLocated (context : Context) (index : Nat) (schemas : List Pattern) : Prop :=
  ∀ offset schema, schemas[offset]? = some schema →
    DepthCoherent context.rule (context.site (index + offset)) [] 0 schema

theorem ArgumentsLocated.head {context : Context} {index : Nat} {schema : Pattern} {schemas : List Pattern}
    (located : ArgumentsLocated context index (schema :: schemas)) :
    DepthCoherent context.rule (context.site index) [] 0 schema := by
  simpa only [Nat.add_zero] using located 0 schema rfl

theorem ArgumentsLocated.tail {context : Context} {index : Nat} {schema : Pattern} {schemas : List Pattern}
    (located : ArgumentsLocated context index (schema :: schemas)) :
    ArgumentsLocated context (index + 1) schemas := by
  intro offset pattern selected
  have found := located (offset + 1) pattern (by simpa using selected)
  simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found

theorem query_arguments_located {context : Context} {relation : String} {arguments : List Pattern}
    (located : NativePremisePosition.Located context (.relationQuery relation arguments)) :
    ArgumentsLocated context 0 arguments := by
  intro index schema selected
  simpa only [Nat.zero_add] using NativePremisePosition.query_coherent located selected

theorem arguments_substitute {context : Context} {index : Nat}
    {initial final : ScopedRuleMatching.Assignment} {schemas values : List Pattern}
    {modes : List RelationArgMode} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : TracedArgumentsHold context index initial schemas values modes final origins)
    (admitted : admittedFor context.rule context.spec = true)
    (located : ArgumentsLocated context index schemas)
    (scopes : ∀ schema ∈ schemas, schema.isWellScopedAt 0 = true)
    (target : List TypeExpr) (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment context.bound.length target.length substitution) :
    TracedArgumentsHold (NativePremiseSubstitutionBase.context target context) index
      (NativeContextualSubstitution.assignment target.length substitution initial) schemas
      (values.map (ContextSubstitution.substitute substitution)) modes
      (NativeContextualSubstitution.assignment target.length substitution final) origins := by
  induction held with
  | nil => exact .nil
  | input interpreted rest ih =>
      have headScope := scopes _ (List.mem_cons_self)
      have head := NativeRuleInstantiationSubstitution.instantiateAt_substitutes
        interpreted admitted located.head headScope substitution boundScoped
      exact .input (by simpa only [NativePremiseSubstitutionBase.context, Context.site, ContextSubstitution.lift_zero] using head)
        (ih located.tail (fun schema member => scopes schema (List.mem_cons_of_mem _ member)))
  | output matched rest ih =>
      have headScope := scopes _ (List.mem_cons_self)
      have head := NativeTracedMatchSubstitution.matched_substitutes matched headScope substitution boundScoped
      exact .output (by simpa only [NativePremiseSubstitutionBase.context, Context.site, ContextSubstitution.lift_zero] using head)
        (ih located.tail (fun schema member => scopes schema (List.mem_cons_of_mem _ member)))

theorem query_substitutes {environment : Environment} {original : Context} {relation : String}
    {arguments : List Pattern} {initial final : ScopedRuleMatching.Assignment}
    {rowIndex : Nat} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : TracedQuery environment original relation arguments initial rowIndex final origins)
    (admitted : admittedFor original.rule original.spec = true)
    (located : NativePremisePosition.Located original (.relationQuery relation arguments))
    (scopes : ∀ schema ∈ arguments, schema.isWellScopedAt 0 = true)
    (closed : NativeOperationalAdmission.ClosedProvider environment.language environment.free environment.provider)
    {target : List TypeExpr}
    (substitution : TypedBoundAssignment environment.language environment.free original.bound target)
    (objects : ∀ index, isObjectPattern (substitution.assignment index) = true) :
    TracedQuery environment (NativePremiseSubstitutionBase.context target original) relation arguments
      (NativeContextualSubstitution.assignment target.length substitution.assignment initial) rowIndex
      (NativeContextualSubstitution.assignment target.length substitution.assignment final) origins := by
  cases held with
  | row selected declared typed argumentsHeld finalTyped =>
      have present := List.mem_of_getElem? selected
      obtain ⟨closedSignature, closedSelected, closedTyped⟩ := closed.rows _ present
      have signatureData := signature?_readout _ _ _ _ declared
      have sameRelation := typed.1.trans signatureData.2.1
      have sameArity := typed.2.length.trans signatureData.2.2.1
      rw [sameRelation, sameArity] at closedSelected
      have sameSignature := Option.some.inj (closedSelected.symm.trans declared)
      subst closedSignature
      have argumentsMapped := arguments_substitute argumentsHeld admitted
        (query_arguments_located located) scopes target substitution.assignment substitution.wellScoped
      rw [NativeProviderSubstitution.closed_values_fixed closedTyped.2 substitution.assignment] at argumentsMapped
      exact .row selected declared (closed_row_in_bound closedTyped target) argumentsMapped
        (typed_assignment substitution objects finalTyped)

end Mettapedia.OSLF.NativeTypes.Modal.NativeQuerySubstitution
