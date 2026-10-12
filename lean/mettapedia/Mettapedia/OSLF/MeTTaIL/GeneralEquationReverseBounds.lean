import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobs

/-!
# Reverse finite bounds for conditional equation instances

An equation instance retains the same metavariable multiplicities on both
sides. Variable-spine substitution preserves each captured body's symbols,
so bounded support of the target also bounds the source. This proves finite
undirected equation closure without assuming that rerunning a conditional
guard in the reverse orientation succeeds.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationReverseBounds

open Syntax RuleBinding ScopedRuleMatching DerivedContexts PatternTreeSize
open GeneralEquationMeasures GeneralEquationAdmission GeneralEquationSupport
open GeneralEquationCaptureDomain GeneralEquationCanonical GeneralEquationContexts GeneralScopedMatch
open GeneralScopedMatchMeasures GeneralEquationJobs GeneralExecutionAdmission
open Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem supported_of_erase {symbols : Alphabet} {pattern : Pattern}
    (supported : Supported symbols pattern.eraseBinderMetadata) : Supported symbols pattern := by
  have same := erase_support pattern
  simpa only [Supported, same.1, same.2.1, same.2.2] using supported

theorem instantiateValue_support_iff (symbols : Alphabet) (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) (result : Pattern)
    (onlyVariables : arguments.all variableArgument = true)
    (instantiated : instantiateValue? value ambient depth arguments = some result) :
    Supported symbols result ↔ Supported symbols value.body := by
  unfold instantiateValue? at instantiated
  split at instantiated <;> try cases instantiated
  split at instantiated <;> try cases instantiated
  split at instantiated <;> try cases instantiated
  split at instantiated <;> try cases instantiated
  dsimp only at instantiated
  split at instantiated <;> try cases instantiated
  have same := support_substitute_variables
    (occurrenceAssignment value.dependencies.length depth arguments)
    (occurrenceAssignment_variables value.dependencies.length depth arguments onlyVariables) value.body
  simp only [Supported, same.1, same.2.1, same.2.2]

/-- Only captures occurring in the specified schema are relevant. -/
def RelevantSupport (symbols : Alphabet) (assignment : Assignment) (names : List String) : Prop :=
  ∀ name ∈ names, ∀ value, lookup assignment name = some value → Supported symbols value.body

mutual
  theorem instantiate_relevant_support (symbols : Alphabet) (rule : RewriteRule) (spec : RuleBindingSpec)
      (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (assignment : Assignment) (pattern result : Pattern)
      (ready : checkSide rule spec site path depth pattern = true)
      (supported : Supported symbols result)
      (instantiated : instantiateAt? rule spec ambient site path depth assignment pattern = some result) :
      RelevantSupport symbols assignment pattern.freeFvarNames := by
    cases pattern with
    | fvar name =>
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨value, found, arguments, occurrence, interpreted⟩ := instantiated
        simp only [checkSide, occurrence, Bool.and_eq_true] at ready
        have bodySupported := (instantiateValue_support_iff symbols value ambient depth arguments result ready.1 interpreted).mp supported
        intro actual occurs other otherFound
        have same : actual = name := by simpa only [Pattern.freeFvarNames, List.mem_singleton] using occurs
        subst actual
        have sameValue : other = value := Option.some.inj (otherFound.symm.trans found)
        subst other
        exact bodySupported
    | bvar index => simp [RelevantSupport, Pattern.freeFvarNames]
    | apply label arguments =>
        simp only [checkSide] at ready
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨results, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        simpa only [Pattern.freeFvarNames] using
          instantiateArguments_relevant_support symbols rule spec ambient site path depth assignment 0
            arguments results ready (supported_argument symbols label results supported) interpreted
    | lambda display body =>
        simp only [checkSide] at ready
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨bodyResult, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        simpa only [Pattern.freeFvarNames] using
          instantiate_relevant_support symbols rule spec ambient site (path ++ [0]) (depth + 1)
            assignment body bodyResult ready (supported_binder_body supported) interpreted
    | multiLambda arity display body =>
        simp only [checkSide] at ready
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨bodyResult, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        simpa only [Pattern.freeFvarNames] using
          instantiate_relevant_support symbols rule spec ambient site (path ++ [0]) (depth + arity)
            assignment body bodyResult ready (supported_binders_body supported) interpreted
    | subst body replacement => simp only [checkSide, Bool.false_eq_true] at ready
    | collection kind elements rest =>
        cases rest with
        | some name => simp only [checkSide, Option.isNone_some, Bool.false_and, Bool.false_eq_true] at ready
        | none =>
            simp only [checkSide, Option.isNone_none, Bool.true_and] at ready
            simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
            obtain ⟨results, interpreted, equal⟩ := instantiated
            cases Option.some.inj equal
            simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using
              instantiateArguments_relevant_support symbols rule spec ambient site path depth assignment 0
                elements results ready (supported_element symbols kind results none supported) interpreted
  termination_by sizeOf pattern

  theorem instantiateArguments_relevant_support (symbols : Alphabet) (rule : RewriteRule) (spec : RuleBindingSpec)
      (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (assignment : Assignment) (index : Nat) (patterns results : List Pattern)
      (ready : checkArguments rule spec site path depth index patterns = true)
      (supported : ∀ result ∈ results, Supported symbols result)
      (instantiated : instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth
        assignment index patterns = some results) :
      RelevantSupport symbols assignment (patterns.flatMap Pattern.freeFvarNames) := by
    cases patterns with
    | nil => simp [RelevantSupport]
    | cons first rest =>
        simp only [checkArguments, Bool.and_eq_true] at ready
        simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨firstResult, firstInterpreted, restResults, restInterpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        have head := instantiate_relevant_support symbols rule spec ambient site (path ++ [index]) depth
          assignment first firstResult ready.1 (supported firstResult (by simp)) firstInterpreted
        have tail := instantiateArguments_relevant_support symbols rule spec ambient site path depth assignment (index + 1)
          rest restResults ready.2 (by intro result member; exact supported result (by simp [member])) restInterpreted
        intro name member
        simp only [List.flatMap_cons, List.mem_append] at member
        exact member.elim (head name) (tail name)
  termination_by sizeOf patterns
end

/-- Erasing one list occurrence leaves every other value in the list. Equal
duplicates may take either branch, so no multiplicity identification occurs. -/
theorem selected_or_erased (patterns : List Pattern) (index : Nat) (within : index < patterns.length)
    (pattern : Pattern) (member : pattern ∈ patterns) :
    pattern = patterns[index] ∨ pattern ∈ patterns.eraseIdx index := by
  induction patterns generalizing index with
  | nil => simp at within
  | cons first rest ih =>
      cases index with
      | zero =>
          simpa only [List.getElem_cons_zero, List.eraseIdx_zero, List.tail_cons, List.mem_cons] using member
      | succ index =>
          have restWithin : index < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within
          rcases List.mem_cons.mp member with rfl | later
          · exact Or.inr (by rw [List.eraseIdx_cons_succ]; exact List.Mem.head _)
          · simpa only [List.getElem_cons_succ, List.eraseIdx_cons_succ, List.mem_cons] using
              (ih index restWithin later).elim Or.inl (fun retained => Or.inr (Or.inr retained))

mutual
  theorem matched_target_supported {symbols : Alphabet} {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat}
      {initial final completed : Assignment} {pattern target : Pattern}
      (matched : Matches rule spec ambient site path depth initial pattern target final)
      (ready : checkSide rule spec site path depth pattern = true)
      (template : Supported symbols pattern)
      (bodies : RelevantSupport symbols completed pattern.freeFvarNames)
      (extension : Extends final completed) : Supported symbols target := by
    cases matched with
    | capture captured =>
        obtain ⟨dependencies, arguments, value, _, occurrence, _, retained, interpreted, _⟩ := capture_interpretation captured
        simp only [checkSide, occurrence, Bool.and_eq_true] at ready
        exact instantiateValue_supported symbols value ambient depth arguments target ready.1
          (bodies _ (by simp [Pattern.freeFvarNames]) value (extension _ _ retained)) interpreted
    | bound => simp [Supported, constructors, Pattern.freeFvarNames, arities]
    | constructor arguments =>
        simp only [checkSide] at ready
        exact supported_apply symbols _ _ (template.1 _ (by simp [constructors]))
          (matchedArguments_target_supported arguments ready (supported_argument _ _ _ template)
            (by simpa only [Pattern.freeFvarNames] using bodies) extension)
    | binder body =>
        simp only [checkSide] at ready
        have support := matched_target_supported body ready (supported_binder_body template)
          (by simpa only [Pattern.freeFvarNames] using bodies) extension
        simpa only [Supported, constructors, Pattern.freeFvarNames, arities] using support
    | binders body =>
        rename_i arity display actualDisplay bodyPattern targetBody
        simp only [checkSide] at ready
        have support := matched_target_supported body ready (supported_binders_body template)
          (by simpa only [Pattern.freeFvarNames] using bodies) extension
        refine ⟨by simpa only [constructors] using support.1,
          by simpa only [Pattern.freeFvarNames] using support.2.1, ?_⟩
        intro actual member
        simp only [arities, List.mem_cons] at member
        exact member.elim (fun same => same ▸ template.2.2 arity (by simp [arities])) (support.2.2 actual)
    | substitution _ _ => simp only [checkSide, Bool.false_eq_true] at ready
    | bag _notVector bag =>
        rename_i kind patterns rest targets
        simp only [checkSide, Bool.and_eq_true] at ready
        have noRest : rest = none := Option.isNone_iff_eq_none.mp ready.1
        subst rest
        exact supported_collection symbols kind targets
          (matchedBag_target_supported bag ready.2 (supported_element _ _ _ none template)
            (by simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using bodies) extension)
    | vector arguments =>
        simp only [checkSide, Option.isNone_none, Bool.true_and] at ready
        exact supported_collection symbols .vec _
          (matchedArguments_target_supported arguments ready (supported_element _ _ _ none template)
            (by simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using bodies) extension)
    | vectorRest _ _ => simp only [checkSide, Option.isNone_some, Bool.false_and, Bool.false_eq_true] at ready
  termination_by sizeOf pattern

  theorem matchedArguments_target_supported {symbols : Alphabet} {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final completed : Assignment} {patterns targets : List Pattern}
      (matched : Arguments rule spec ambient site path depth initial index patterns targets final)
      (ready : checkArguments rule spec site path depth index patterns = true)
      (templates : ∀ pattern ∈ patterns, Supported symbols pattern)
      (bodies : RelevantSupport symbols completed (patterns.flatMap Pattern.freeFvarNames))
      (extension : Extends final completed) : ∀ target ∈ targets, Supported symbols target := by
    cases matched with
    | nil => simp
    | cons head tail =>
        simp only [checkArguments, Bool.and_eq_true] at ready
        have first := matched_target_supported head ready.1 (templates _ (by simp))
          (by intro name member; exact bodies name (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inl member))
          (tail.extends.trans extension)
        have rest := matchedArguments_target_supported tail ready.2 (by intro pattern member; exact templates pattern (by simp [member]))
          (by intro name member; exact bodies name (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr member)) extension
        intro target member
        rcases List.mem_cons.mp member with rfl | later
        · exact first
        · exact rest target later
  termination_by sizeOf patterns

  theorem matchedBag_target_supported {symbols : Alphabet} {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final completed : Assignment} {patterns targets : List Pattern} {kind : CollType}
      (matched : Bag rule spec ambient site path depth initial index patterns none kind targets final)
      (ready : checkArguments rule spec site path depth index patterns = true)
      (templates : ∀ pattern ∈ patterns, Supported symbols pattern)
      (bodies : RelevantSupport symbols completed (patterns.flatMap Pattern.freeFvarNames))
      (extension : Extends final completed) : ∀ target ∈ targets, Supported symbols target := by
    cases matched with
    | nil => simp
    | cons selected within head tail =>
        simp only [checkArguments, Bool.and_eq_true] at ready
        have first := matched_target_supported head ready.1 (templates _ (by simp))
          (by intro name member; exact bodies name (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inl member))
          (tail.extends.trans extension)
        have rest := matchedBag_target_supported tail ready.2 (by intro pattern member; exact templates pattern (by simp [member]))
          (by intro name member; exact bodies name (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr member)) extension
        intro target member
        rcases selected_or_erased targets selected within target member with equal | later
        · exact equal ▸ first
        · exact rest target later
  termination_by sizeOf patterns
end

theorem completion_nodes {plan : Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {receipt : Receipt}
    (complete : Completion plan bound type source receipt)
    (accepted : checkRule receipt.job.equation.rule receipt.job.equation.binding.spec = true) :
    nodes receipt.target = nodes source := by
  have selected := complete.job.2.source_eq
  have focusCanonical := canonical_redex receipt.job.site.context receipt.job.site.focus
    (selected.symm ▸ complete.sourceTyped.2.1)
  have matching : receipt.captured ∈ matchRuleAt receipt.job.equation.rule receipt.job.equation.binding.spec
      receipt.job.site.focusBound.length receipt.job.site.focus := by
    apply matchRuleAt_iff.mpr
    simpa only [Pattern.eraseBinderMetadata_eq_self_of_canonical focusCanonical] using complete.matched.matching
  have extension : Extends receipt.captured receipt.completed := complete.premises.extension
  have same := matched_reduct_preserves_nodes accepted matching extension complete.reduct
  rw [complete.endpoint, eraseBinderMetadata_nodes]
  have localSame : nodes receipt.job.site.focus = nodes receipt.rawReduct.eraseBinderMetadata :=
    same.trans (eraseBinderMetadata_nodes receipt.rawReduct).symm
  rw [← fill_preserves_nodes receipt.job.site.context receipt.job.site.focus receipt.rawReduct.eraseBinderMetadata localSame, selected]

/-- Target support reflects through every balanced equation instance, even
when its conditional guard has no operational reverse execution. -/
theorem completion_reverse_supported {plan : Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {receipt : Receipt} {symbols : Alphabet}
    (complete : Completion plan bound type source receipt)
    (accepted : checkRule receipt.job.equation.rule receipt.job.equation.binding.spec = true)
    (template : Supported symbols receipt.job.equation.rule.left)
    (supported : Supported symbols receipt.target) : Supported symbols source := by
  have selected := complete.job.2.source_eq
  have focusCanonical := canonical_redex receipt.job.site.context receipt.job.site.focus
    (selected.symm ▸ complete.sourceTyped.2.1)
  have matching : receipt.captured ∈ matchRuleAt receipt.job.equation.rule receipt.job.equation.binding.spec
      receipt.job.site.focusBound.length receipt.job.site.focus := by
    apply matchRuleAt_iff.mpr
    simpa only [Pattern.eraseBinderMetadata_eq_self_of_canonical focusCanonical] using complete.matched.matching
  have extension : Extends receipt.captured receipt.completed := complete.premises.extension
  have filledSupport : Supported symbols (receipt.job.site.context.fill receipt.rawReduct.eraseBinderMetadata) := by
    apply supported_of_erase
    rw [← complete.endpoint]
    exact supported
  have rawSupport : Supported symbols receipt.rawReduct := supported_of_erase (supported_redex filledSupport)
  have ready := checkRule_sides _ _ accepted
  have rightBodies := instantiate_relevant_support symbols receipt.job.equation.rule receipt.job.equation.binding.spec
    receipt.job.site.focusBound.length .right [] 0 receipt.completed receipt.job.equation.rule.right receipt.rawReduct
    ready.2.2.1 rawSupport complete.reduct
  have balance : constantContribution receipt.job.equation.rule.left = constantContribution receipt.job.equation.rule.right ∧
      receipt.job.equation.rule.left.freeFvarNames.Perm receipt.job.equation.rule.right.freeFvarNames := by
    simpa only [balanced, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using ready.2.2.2
  have leftBodies : RelevantSupport symbols receipt.completed receipt.job.equation.rule.left.freeFvarNames := by
    intro name member
    exact rightBodies name (balance.2.mem_iff.mp member)
  have focusSupport := matched_target_supported (matchRuleAt_iff.mp matching) ready.2.1 template leftBodies extension
  have sourceSupport := fill_preserves_support receipt.job.site.context receipt.rawReduct.eraseBinderMetadata
    receipt.job.site.focus filledSupport focusSupport
  simpa only [selected] using sourceSupport

theorem compiled_left_template {snapshot : Snapshot} {permissions : Permissions} {equationPlan : EquationPlan}
    (member : equationPlan ∈ (compile snapshot permissions).equations) (root : Pattern) (providerTerms : List Pattern) :
    Supported (alphabet snapshot.language root providerTerms) equationPlan.rule.left := by
  obtain ⟨equation, index, direction, authored, _, _, compiled⟩ := compiled_equation_origin member
  have readout := equationPlan_readout compiled
  have declared : equation ∈ snapshot.language.equations := List.fst_mem_of_mem_zipIdx authored
  rw [EquationPlan.rule, readout.2.1, readout.2.2.1]
  have endpoints : ∀ endpoint ∈ [equation.left, equation.right],
      Supported (alphabet snapshot.language root providerTerms) endpoint := by
    intro endpoint occurs
    apply supported_fromPatterns _ endpoint
    simp only [List.mem_cons, List.mem_append, languagePatterns, List.mem_flatMap]
    exact Or.inr (Or.inl (Or.inl ⟨equation, declared, by simpa only [List.mem_cons] using occurs⟩))
  cases direction with
  | forward => exact endpoints equation.left (by simp)
  | reverse => exact endpoints equation.right (by simp)

/-- The reverse carrier bound follows from actual instance evidence; it does
not require a reverse-direction rule or a repeated conditional query. -/
theorem compiled_reverse_universe_closed {snapshot : Snapshot} {permissions : Permissions}
    {bound : List TypeExpr} {type : TypeExpr} {root source : Pattern}
    {providerTerms : List Pattern} {receipt : Receipt}
    (accepted : (compile snapshot permissions).complete = true)
    (complete : Completion (compile snapshot permissions) bound type source receipt)
    (member : receipt.target ∈ sourceUniverse snapshot.language snapshot.free bound type root providerTerms) :
    source ∈ sourceUniverse snapshot.language snapshot.free bound type root providerTerms := by
  have declared : receipt.job.equation ∈ (compile snapshot permissions).equations := List.fst_mem_of_mem_zipIdx complete.job.1
  have schema := compiled_equation_checked accepted declared
  have targetSmall := (typedUniverse_sound _ _ _ _ _ _ _ _ member).1
  have targetSupport := sourceUniverse_supported _ _ _ _ _ _ _ member
  have sourceSupport := completion_reverse_supported complete schema (compiled_left_template declared root providerTerms) targetSupport
  have same := completion_nodes complete schema
  have small : nodes source ≤ nodes root := same ▸ targetSmall
  have sourceTyped : OpenPatternWellSorted snapshot.language snapshot.free bound type source :=
    (GeneralPlanEnvironment.typing_iff _ bound type source).mp complete.sourceTyped
  apply typedUniverse_complete _ _ _ _ _ _ _ _ sourceTyped small sourceSupport
  exact scoped_indices _ _ bound.length (nodes root) small sourceTyped.2.2.2
    (fun arity occurs => arity_le_maximum _ arity (sourceSupport.2.2 arity occurs))

/-- Independently witnessed local equation instances generate the quotient
relation. Direction choice governs which instances are generators, while
their generated mathematical equivalence is explicitly symmetric. -/
def Equation (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (source target : Pattern) : Prop :=
  ∃ receipt, Completion plan bound type source receipt ∧ receipt.target = target

/-- Every equivalence generator and its inverse preserve the derived carrier.
This earns closure for arbitrary detours, rather than only outgoing walks. -/
theorem compiled_equivalence_universe_iff {snapshot : Snapshot} {permissions : Permissions}
    {bound : List TypeExpr} {type : TypeExpr} {root source target : Pattern} (providerTerms : List Pattern)
    (accepted : (compile snapshot permissions).complete = true)
    (related : Relation.EqvGen (Equation (compile snapshot permissions) bound type) source target) :
    source ∈ sourceUniverse snapshot.language snapshot.free bound type root providerTerms ↔
      target ∈ sourceUniverse snapshot.language snapshot.free bound type root providerTerms := by
  induction related with
  | rel source target conversion =>
      obtain ⟨receipt, complete, equal⟩ := conversion
      subst target
      exact ⟨compiled_completion_universe_closed accepted complete, compiled_reverse_universe_closed accepted complete⟩
  | refl source => rfl
  | symm source target _ ih => exact ih.symm
  | trans source middle target _ _ first second => exact first.trans second

end Mettapedia.OSLF.MeTTaIL.GeneralEquationReverseBounds
