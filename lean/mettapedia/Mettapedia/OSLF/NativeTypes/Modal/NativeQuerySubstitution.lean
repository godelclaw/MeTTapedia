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
    (finiteProvider : environment.provider.dynamicRelations = [])
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
  | dynamicRow registered _ _ _ _ _ _ _ =>
      rw [finiteProvider] at registered
      exact False.elim (List.not_mem_nil registered)


/-- Resolving native input positions commutes with the original scoped
substitution. Output positions remain their original closed schemas. -/
theorem dynamic_inputs_substitute {original : Context} {index : Nat}
    {initial : ScopedRuleMatching.Assignment} {schemas resolved : List Pattern}
    {modes : List RelationArgMode}
    (inputs : DynamicInputs original index initial schemas modes resolved)
    (admitted : admittedFor original.rule original.spec = true)
    (located : ArgumentsLocated original index schemas)
    (scopes : ∀ schema ∈ schemas, schema.isWellScopedAt 0 = true)
    (target : List TypeExpr) (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment original.bound.length target.length substitution) :
    DynamicInputs (NativePremiseSubstitutionBase.context target original) index
      (NativeContextualSubstitution.assignment target.length substitution initial)
      schemas modes (resolved.map (ContextSubstitution.substitute substitution)) := by
  induction inputs with
  | nil => exact .nil
  | input interpreted rest ih =>
      have head := NativeRuleInstantiationSubstitution.instantiateAt_substitutes
        interpreted admitted located.head (scopes _ (List.mem_cons_self)) substitution boundScoped
      exact .input
        (by simpa only [NativePremiseSubstitutionBase.context, Context.site,
          ContextSubstitution.lift_zero] using head)
        (ih located.tail (fun schema member => scopes schema (List.mem_cons_of_mem _ member)))
  | output rest ih =>
      simp only [List.map_cons]
      rw [NativeProviderSubstitution.substitute_closed (scopes _ (List.mem_cons_self)) substitution]
      exact .output
        (ih located.tail (fun schema member => scopes schema (List.mem_cons_of_mem _ member)))

/-- The native source call is reused unchanged when its resolved request and
returned row are closed. The result retains the exact native occurrence and
all original argument-match traces; no naturality of arbitrary services is
assumed. Closedness is checked on these actual inputs and row. -/
theorem dynamic_query_substitutes {environment : Environment} {original : Context}
    {relation : String} {arguments : List Pattern}
    {initial final : ScopedRuleMatching.Assignment}
    {signature : Signature} {resolved : List Pattern} {rows : List (List Pattern)}
    {values : List Pattern} {nativeIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (registered : relation ∈ environment.provider.dynamicRelations)
    (declared : signature? environment.provider relation arguments.length = some signature)
    (inputs : DynamicInputs original 0 initial arguments signature.modes resolved)
    (source : environment.dynamic.Source relation resolved rows)
    (selected : rows[nativeIndex]? = some values)
    (rowClosed : RowTyped environment.language environment.free [] signature ⟨relation, values⟩)
    (argumentsHeld : TracedArgumentsHold original 0 initial arguments values signature.modes final origins)
    (finalTyped : TypedAssignment environment original final)
    (inputsClosed : ∀ value ∈ resolved, value.isWellScopedAt 0 = true)
    (admitted : admittedFor original.rule original.spec = true)
    (located : NativePremisePosition.Located original (.relationQuery relation arguments))
    (scopes : ∀ schema ∈ arguments, schema.isWellScopedAt 0 = true)
    {target : List TypeExpr}
    (substitution : TypedBoundAssignment environment.language environment.free original.bound target)
    (objects : ∀ index, isObjectPattern (substitution.assignment index) = true) :
    TracedQuery environment (NativePremiseSubstitutionBase.context target original) relation arguments
      (NativeContextualSubstitution.assignment target.length substitution.assignment initial)
      (environment.provider.rows.length + nativeIndex)
      (NativeContextualSubstitution.assignment target.length substitution.assignment final) origins := by
  have fixedInputs : resolved.map (ContextSubstitution.substitute substitution.assignment) = resolved := by
    calc
      _ = resolved.map _root_.id := List.map_congr_left fun value member =>
        NativeProviderSubstitution.substitute_closed (inputsClosed value member) substitution.assignment
      _ = resolved := List.map_id resolved
  have mappedInputs := dynamic_inputs_substitute inputs admitted
    (query_arguments_located located) scopes target substitution.assignment substitution.wellScoped
  rw [fixedInputs] at mappedInputs
  have mappedArguments := arguments_substitute argumentsHeld admitted
    (query_arguments_located located) scopes target substitution.assignment substitution.wellScoped
  rw [NativeProviderSubstitution.closed_values_fixed rowClosed.2 substitution.assignment] at mappedArguments
  exact .dynamicRow registered declared mappedInputs source selected
    (closed_row_in_bound rowClosed target) mappedArguments (typed_assignment substitution objects finalTyped)


/-- Primitive closure of the actual native request and selected source row.
This asks about service data, not about transport of a completed query. -/
def NativeCallClosed (environment : Environment) (original : Context)
    (relation : String) (arguments : List Pattern) (initial : ScopedRuleMatching.Assignment) : Prop :=
  ∀ (signature : Signature) (resolved : List Pattern) (rows : List (List Pattern))
    (nativeIndex : Nat) (values : List Pattern),
    relation ∈ environment.provider.dynamicRelations →
    signature? environment.provider relation arguments.length = some signature →
    DynamicInputs original 0 initial arguments signature.modes resolved →
    environment.dynamic.Source relation resolved rows →
    rows[nativeIndex]? = some values →
    (∀ value ∈ resolved, value.isWellScopedAt 0 = true) ∧
      RowTyped environment.language environment.free [] signature ⟨relation, values⟩

/-- Closed finite rows and independently closed native calls give forward
substitution for the complete query receipt, including its original origin
indices. This does not infer reflection or absence of later answers. -/
theorem query_substitutes_of_native_closed {environment : Environment} {original : Context}
    {relation : String} {arguments : List Pattern}
    {initial final : ScopedRuleMatching.Assignment}
    {rowIndex : Nat} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : TracedQuery environment original relation arguments initial rowIndex final origins)
    (admitted : admittedFor original.rule original.spec = true)
    (located : NativePremisePosition.Located original (.relationQuery relation arguments))
    (scopes : ∀ schema ∈ arguments, schema.isWellScopedAt 0 = true)
    (closed : NativeOperationalAdmission.ClosedProvider environment.language environment.free environment.provider)
    (nativeClosed : NativeCallClosed environment original relation arguments initial)
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
  | dynamicRow registered declared inputs source selected _ argumentsHeld finalTyped =>
      obtain ⟨inputsClosed, rowClosed⟩ := nativeClosed _ _ _ _ _ registered declared inputs source selected
      exact dynamic_query_substitutes registered declared inputs source selected rowClosed
        argumentsHeld finalTyped inputsClosed admitted located scopes substitution objects

end Mettapedia.OSLF.NativeTypes.Modal.NativeQuerySubstitution
