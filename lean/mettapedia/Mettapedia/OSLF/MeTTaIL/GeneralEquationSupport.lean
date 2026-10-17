import Mettapedia.OSLF.MeTTaIL.GeneralEquationAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch
import Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse

/-!
# Finite support of actual scoped equation instantiation

Variable-spine substitution changes only bound indices. Constructor labels,
object free names and multi-binder arities therefore remain in the support of
captured values and authored templates. Provider values can enlarge the fixed
snapshot alphabet, but no opaque provider function is assumed globally finite.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationSupport

open Syntax RuleBinding ScopedRuleMatching GeneralEquationMeasures GeneralEquationAdmission
open Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse

theorem flatMap_map_eq {Atom : Type} (function : Pattern → Pattern) (keys : Pattern → List Atom)
    (patterns : List Pattern) (same : ∀ pattern ∈ patterns, keys (function pattern) = keys pattern) :
    (patterns.map function).flatMap keys = patterns.flatMap keys := by
  induction patterns with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.map_cons, List.flatMap_cons, same first (by simp)]
    rw [ih (by intro pattern member; exact same pattern (by simp [member]))]

theorem support_substitute_variables (assignment : ContextSubstitution.Assignment)
    (onlyVariables : VariablesOnly assignment) (pattern : Pattern) :
    constructors (ContextSubstitution.substitute assignment pattern) = constructors pattern ∧
      (ContextSubstitution.substitute assignment pattern).freeFvarNames = pattern.freeFvarNames ∧
      arities (ContextSubstitution.substitute assignment pattern) = arities pattern := by
  induction pattern using Pattern.inductionOn generalizing assignment with
  | hbvar index =>
    obtain ⟨next, equal⟩ := onlyVariables index
    simp only [ContextSubstitution.substitute, equal, constructors, Pattern.freeFvarNames, arities]
    simp
  | hfvar name => simp only [ContextSubstitution.substitute]; simp
  | happly label arguments ih =>
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
      constructors, Pattern.freeFvarNames, arities]
    rw [flatMap_map_eq _ constructors arguments (by intro pattern member; exact (ih pattern member assignment onlyVariables).1),
      flatMap_map_eq _ Pattern.freeFvarNames arguments (by intro pattern member; exact (ih pattern member assignment onlyVariables).2.1),
      flatMap_map_eq _ arities arguments (by intro pattern member; exact (ih pattern member assignment onlyVariables).2.2)]
    simp
  | hlambda name body ih =>
    simpa only [ContextSubstitution.substitute, constructors, Pattern.freeFvarNames, arities] using
      ih _ (onlyVariables.lift 1)
  | hmultiLambda arity names body ih =>
    have bodyResult := ih _ (onlyVariables.lift arity)
    simp only [ContextSubstitution.substitute, constructors, Pattern.freeFvarNames, arities,
      bodyResult.1, bodyResult.2.1, bodyResult.2.2]
    simp
  | hsubst body replacement bodyIH replacementIH =>
    have before := bodyIH _ (onlyVariables.lift 1)
    have after := replacementIH _ onlyVariables
    simp only [ContextSubstitution.substitute, constructors, Pattern.freeFvarNames, arities,
      before.1, before.2.1, before.2.2, after.1, after.2.1, after.2.2]
    simp
  | hcollection kind elements rest ih =>
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
      constructors, Pattern.freeFvarNames, arities]
    rw [flatMap_map_eq _ constructors elements (by intro pattern member; exact (ih pattern member assignment onlyVariables).1),
      flatMap_map_eq _ Pattern.freeFvarNames elements (by intro pattern member; exact (ih pattern member assignment onlyVariables).2.1),
      flatMap_map_eq _ arities elements (by intro pattern member; exact (ih pattern member assignment onlyVariables).2.2)]
    simp

theorem instantiateValue_supported (alphabet : Alphabet) (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) (result : Pattern)
    (onlyVariables : arguments.all variableArgument = true)
    (support : Supported alphabet value.body)
    (instantiated : instantiateValue? value ambient depth arguments = some result) :
    Supported alphabet result := by
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
  simpa only [Supported, same.1, same.2.1, same.2.2] using support

def SupportedBodies (alphabet : Alphabet) (assignment : Assignment) : Prop :=
  ∀ name value, lookup assignment name = some value → Supported alphabet value.body

theorem supported_apply (alphabet : Alphabet) (label : String) (arguments : List Pattern)
    (declared : label ∈ alphabet.constructors)
    (children : ∀ child ∈ arguments, Supported alphabet child) :
    Supported alphabet (.apply label arguments) := by
  refine ⟨?_, ?_, ?_⟩
  · intro constructor occurs
    simp only [constructors] at occurs
    rcases List.mem_cons.mp occurs with same | childOccurrence
    · exact same ▸ declared
    · obtain ⟨child, member, contains⟩ := List.mem_flatMap.mp childOccurrence
      exact (children child member).1 constructor contains
  · intro name occurs
    simp only [Pattern.freeFvarNames] at occurs
    obtain ⟨child, member, contains⟩ := List.mem_flatMap.mp occurs
    exact (children child member).2.1 name contains
  · intro arity occurs
    simp only [arities] at occurs
    obtain ⟨child, member, contains⟩ := List.mem_flatMap.mp occurs
    exact (children child member).2.2 arity contains

theorem supported_collection (alphabet : Alphabet) (kind : CollType) (elements : List Pattern)
    (children : ∀ child ∈ elements, Supported alphabet child) :
    Supported alphabet (.collection kind elements none) := by
  refine ⟨?_, ?_, ?_⟩
  · intro constructor occurs
    simp only [constructors] at occurs
    obtain ⟨child, member, contains⟩ := List.mem_flatMap.mp occurs
    exact (children child member).1 constructor contains
  · intro name occurs
    simp only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] at occurs
    obtain ⟨child, member, contains⟩ := List.mem_flatMap.mp occurs
    exact (children child member).2.1 name contains
  · intro arity occurs
    simp only [arities] at occurs
    obtain ⟨child, member, contains⟩ := List.mem_flatMap.mp occurs
    exact (children child member).2.2 arity contains

theorem supported_argument (alphabet : Alphabet) (label : String) (arguments : List Pattern)
    (support : Supported alphabet (.apply label arguments)) (argument : Pattern)
    (member : argument ∈ arguments) : Supported alphabet argument := by
  refine ⟨?_, ?_, ?_⟩
  · intro constructor occurs
    exact support.1 constructor (by simp only [constructors, List.mem_cons, List.mem_flatMap]; exact Or.inr ⟨argument, member, occurs⟩)
  · intro name occurs
    exact support.2.1 name (by simp only [Pattern.freeFvarNames, List.mem_flatMap]; exact ⟨argument, member, occurs⟩)
  · intro arity occurs
    exact support.2.2 arity (by simp only [arities, List.mem_flatMap]; exact ⟨argument, member, occurs⟩)

theorem supported_element (alphabet : Alphabet) (kind : CollType) (elements : List Pattern)
    (rest : Option String) (support : Supported alphabet (.collection kind elements rest))
    (element : Pattern) (member : element ∈ elements) : Supported alphabet element := by
  refine ⟨?_, ?_, ?_⟩
  · intro constructor occurs
    exact support.1 constructor (by simp only [constructors, List.mem_flatMap]; exact ⟨element, member, occurs⟩)
  · intro name occurs
    exact support.2.1 name (by simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]; exact Or.inl ⟨element, member, occurs⟩)
  · intro arity occurs
    exact support.2.2 arity (by simp only [arities, List.mem_flatMap]; exact ⟨element, member, occurs⟩)

mutual
  theorem instantiate_supported (alphabet : Alphabet) (rule : RewriteRule) (spec : RuleBindingSpec)
      (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (assignment : Assignment) (pattern result : Pattern)
      (ready : checkSide rule spec site path depth pattern = true)
      (support : Supported alphabet pattern) (bodies : SupportedBodies alphabet assignment)
      (instantiated : instantiateAt? rule spec ambient site path depth assignment pattern = some result) :
      Supported alphabet result := by
    cases pattern with
    | fvar name =>
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨value, found, arguments, occurrence, interpreted⟩ := instantiated
        simp only [checkSide, occurrence, Bool.and_eq_true] at ready
        exact instantiateValue_supported alphabet value ambient depth arguments result ready.1
          (bodies name value found) interpreted
    | bvar index =>
        simp only [instantiateAt?, instantiateWith?, Option.some.injEq] at instantiated
        cases instantiated
        simp [Supported, constructors, Pattern.freeFvarNames, arities]
    | apply label arguments =>
        simp only [checkSide] at ready
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨results, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        exact supported_apply alphabet label results (support.1 label (by simp [constructors]))
          (instantiateArguments_supported alphabet rule spec ambient site path depth assignment 0
            arguments results ready (supported_argument alphabet label arguments support) bodies interpreted)
    | lambda binder body =>
        simp only [checkSide] at ready
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨bodyResult, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        have supported := instantiate_supported alphabet rule spec ambient site (path ++ [0]) (depth + 1)
          assignment body bodyResult ready
          (by simpa only [Supported, constructors, Pattern.freeFvarNames, arities] using support) bodies interpreted
        simpa only [Supported, constructors, Pattern.freeFvarNames, arities] using supported
    | multiLambda arity binders body =>
        simp only [checkSide] at ready
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨bodyResult, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        have bodySupport : Supported alphabet body := by
          refine ⟨by simpa only [constructors] using support.1,
            by simpa only [Pattern.freeFvarNames] using support.2.1, ?_⟩
          intro size member
          exact support.2.2 size (by simp [arities, member])
        have supported := instantiate_supported alphabet rule spec ambient site (path ++ [0]) (depth + arity)
          assignment body bodyResult ready bodySupport bodies interpreted
        refine ⟨by simpa only [constructors] using supported.1,
          by simpa only [Pattern.freeFvarNames] using supported.2.1, ?_⟩
        intro size member
        simp only [arities, List.mem_cons] at member
        rcases member with same | below
        · exact same ▸ support.2.2 arity (by simp [arities])
        · exact supported.2.2 size below
    | subst body replacement => simp only [checkSide, Bool.false_eq_true] at ready
    | collection kind elements rest =>
        simp only [checkSide, Bool.and_eq_true] at ready
        cases rest with
        | some name =>
            simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
            obtain ⟨explicit, interpreted, value, found, arguments, occurrence, residualValue, residual, spliced⟩ :=
              instantiated
            have spine := ready.1
            simp only [restSupported, occurrence, Bool.and_eq_true] at spine
            have explicitSupport := instantiateArguments_supported alphabet rule spec ambient site path depth
              assignment 0 elements explicit ready.2 (supported_element alphabet kind elements (some name) support)
              bodies interpreted
            have residualSupport := instantiateValue_supported alphabet value ambient depth arguments residualValue
              spine.1 (bodies name value found) residual
            split at spliced
            · rename_i actualKind items
              split at spliced
              · cases spliced
                apply supported_collection alphabet kind
                intro child member
                rcases List.mem_append.mp member with early | late
                · exact explicitSupport child early
                · exact supported_element alphabet actualKind items none residualSupport child late
              · cases spliced
            · cases spliced
        | none =>
            simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
            obtain ⟨results, interpreted, equal⟩ := instantiated
            cases Option.some.inj equal
            exact supported_collection alphabet kind results
              (instantiateArguments_supported alphabet rule spec ambient site path depth assignment 0
                elements results ready.2 (supported_element alphabet kind elements none support) bodies interpreted)
  termination_by sizeOf pattern

  theorem instantiateArguments_supported (alphabet : Alphabet) (rule : RewriteRule) (spec : RuleBindingSpec)
      (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (assignment : Assignment) (index : Nat) (patterns results : List Pattern)
      (ready : checkArguments rule spec site path depth index patterns = true)
      (support : ∀ pattern ∈ patterns, Supported alphabet pattern)
      (bodies : SupportedBodies alphabet assignment)
      (instantiated : instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth
        assignment index patterns = some results) : ∀ result ∈ results, Supported alphabet result := by
    cases patterns with
    | nil =>
        simp only [instantiateArgsWith?, Option.some.injEq] at instantiated
        cases instantiated
        simp
    | cons first rest =>
        simp only [checkArguments, Bool.and_eq_true] at ready
        simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨firstResult, firstInterpreted, restResults, restInterpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        intro result member
        rcases List.mem_cons.mp member with same | later
        · subst result
          exact instantiate_supported alphabet rule spec ambient site (path ++ [index]) depth assignment
            first firstResult ready.1 (support first (by simp)) bodies firstInterpreted
        · exact instantiateArguments_supported alphabet rule spec ambient site path depth assignment (index + 1)
            rest restResults ready.2 (by intro pattern member; exact support pattern (by simp [member]))
            bodies restInterpreted result later
  termination_by sizeOf patterns
end

open GeneralScopedMatch

theorem recoveryAssignment_variables (depth dependencies ambient : Nat) (indices : List Nat) :
    VariablesOnly (recoveryAssignment depth dependencies ambient indices) := by
  intro index
  unfold recoveryAssignment
  split
  · split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem recovered_supported (alphabet : Alphabet) (dependencies : List TypeExpr)
    (ambient depth : Nat) (arguments : List Pattern) (target : Pattern)
    (value : ContextualValue) (support : Supported alphabet target)
    (recovered : recoverValue? dependencies ambient depth arguments target = some value) :
    Supported alphabet value.body := by
  unfold recoverValue? at recovered
  split at recovered <;> try cases recovered
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at recovered
  obtain ⟨indices, _, recovered⟩ := recovered
  split at recovered <;> try cases recovered
  split at recovered <;> cases recovered
  have same := support_substitute_variables
    (recoveryAssignment depth dependencies.length ambient indices)
    (recoveryAssignment_variables depth dependencies.length ambient indices) target
  simpa only [Supported, same.1, same.2.1, same.2.2] using support

theorem assign_supported (alphabet : Alphabet) (initial final : ScopedRuleMatching.Assignment)
    (name : String) (value : ContextualValue) (bodies : SupportedBodies alphabet initial)
    (support : Supported alphabet value.body) (assigned : assign initial name value = some final) :
    SupportedBodies alphabet final := by
  unfold assign at assigned
  cases stored : lookup initial name with
  | none =>
      simp only [stored, Option.some.injEq] at assigned
      subst final
      intro previous previousValue found
      simp only [lookup, List.find?_cons] at found
      by_cases same : name = previous
      · subst previous
        simp only [beq_self_eq_true, Option.map_some, Option.some.injEq] at found
        subst previousValue
        exact support
      · simp only [beq_eq_false_iff_ne.mpr same] at found
        exact bodies previous previousValue found
  | some prior =>
      simp only [stored] at assigned
      split at assigned <;> try cases assigned
      exact bodies

theorem capture_supported {alphabet : Alphabet} {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : ScopedRuleMatching.Assignment} {name : String} {target : Pattern}
    (bodies : SupportedBodies alphabet initial) (support : Supported alphabet target)
    (captured : capture? rule spec ambient depth site path initial name target = some final) :
    SupportedBodies alphabet final := by
  simp only [capture?, Option.bind_eq_bind, Option.bind_eq_some_iff] at captured
  obtain ⟨dependencies, _, arguments, _, value, recovered, assigned⟩ := captured
  exact assign_supported alphabet initial final name value bodies
    (recovered_supported alphabet dependencies ambient depth arguments target value support recovered) assigned

theorem supported_binder_body {alphabet : Alphabet} {display : Option String} {body : Pattern}
    (support : Supported alphabet (.lambda display body)) : Supported alphabet body := by
  simpa only [Supported, constructors, Pattern.freeFvarNames, arities] using support

theorem supported_binders_body {alphabet : Alphabet} {arity : Nat} {display : List String} {body : Pattern}
    (support : Supported alphabet (.multiLambda arity display body)) : Supported alphabet body := by
  refine ⟨by simpa only [constructors] using support.1,
    by simpa only [Pattern.freeFvarNames] using support.2.1, ?_⟩
  intro count contains
  exact support.2.2 count (by simp only [arities, List.mem_cons]; exact Or.inr contains)

theorem supported_substitution_body {alphabet : Alphabet} {body replacement : Pattern}
    (support : Supported alphabet (.subst body replacement)) : Supported alphabet body := by
  refine ⟨?_, ?_, ?_⟩
  · intro label contains
    exact support.1 label (by simp only [constructors, List.mem_append]; exact Or.inl contains)
  · intro name contains
    exact support.2.1 name (by simp only [Pattern.freeFvarNames, List.mem_append]; exact Or.inl contains)
  · intro count contains
    exact support.2.2 count (by simp only [arities, List.mem_append]; exact Or.inl contains)

theorem supported_substitution_replacement {alphabet : Alphabet} {body replacement : Pattern}
    (support : Supported alphabet (.subst body replacement)) : Supported alphabet replacement := by
  refine ⟨?_, ?_, ?_⟩
  · intro label contains
    exact support.1 label (by simp only [constructors, List.mem_append]; exact Or.inr contains)
  · intro name contains
    exact support.2.1 name (by simp only [Pattern.freeFvarNames, List.mem_append]; exact Or.inr contains)
  · intro count contains
    exact support.2.2 count (by simp only [arities, List.mem_append]; exact Or.inr contains)

mutual
  theorem matched_supported {alphabet : Alphabet} {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
      {initial final : ScopedRuleMatching.Assignment} {pattern target : Pattern}
      (matched : Matches rule spec ambient site path depth initial pattern target final)
      (bodies : SupportedBodies alphabet initial) (support : Supported alphabet target) :
      SupportedBodies alphabet final := by
    cases matched with
    | capture captured => exact capture_supported bodies support captured
    | bound => exact bodies
    | constructor arguments =>
        exact matchedArguments_supported arguments bodies (supported_argument alphabet _ _ support)
    | binder body => exact matched_supported body bodies (supported_binder_body support)
    | binders body => exact matched_supported body bodies (supported_binders_body support)
    | substitution body replacement =>
        exact matched_supported replacement
          (matched_supported body bodies (supported_substitution_body support))
          (supported_substitution_replacement support)
    | bag _ bag => exact matchedBag_supported bag bodies (supported_element alphabet _ _ _ support)
    | vector arguments =>
        exact matchedArguments_supported arguments bodies (supported_element alphabet _ _ _ support)
    | vectorRest arguments captured =>
        have children := supported_element alphabet _ _ _ support
        have middle := matchedArguments_supported arguments bodies
          (by intro child member; exact children child (List.mem_of_mem_take member))
        exact capture_supported middle
          (supported_collection alphabet _ _ (by intro child member; exact children child (List.mem_of_mem_drop member))) captured
  termination_by sizeOf pattern

  theorem matchedArguments_supported {alphabet : Alphabet} {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final : ScopedRuleMatching.Assignment} {patterns targets : List Pattern}
      (matched : Arguments rule spec ambient site path depth initial index patterns targets final)
      (bodies : SupportedBodies alphabet initial) (support : ∀ target ∈ targets, Supported alphabet target) :
      SupportedBodies alphabet final := by
    cases matched with
    | nil => exact bodies
    | cons head tail =>
        exact matchedArguments_supported tail
          (matched_supported head bodies (support _ (by simp)))
          (by intro target member; exact support target (by simp [member]))
  termination_by sizeOf patterns

  theorem matchedBag_supported {alphabet : Alphabet} {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final : ScopedRuleMatching.Assignment} {patterns targets : List Pattern}
      {rest : Option String} {kind : CollType}
      (matched : Bag rule spec ambient site path depth initial index patterns rest kind targets final)
      (bodies : SupportedBodies alphabet initial) (support : ∀ target ∈ targets, Supported alphabet target) :
      SupportedBodies alphabet final := by
    cases matched with
    | nil => exact bodies
    | rest captured => exact capture_supported bodies (supported_collection alphabet _ _ support) captured
    | cons selected within head tail =>
        exact matchedBag_supported tail
          (matched_supported head bodies (support _ (List.getElem_mem within)))
          (by intro target member; exact support target (List.mem_of_mem_eraseIdx member))
  termination_by sizeOf patterns
end

theorem matchRule_supported {alphabet : Alphabet} {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {source : Pattern} {captured : ScopedRuleMatching.Assignment}
    (support : Supported alphabet source) (matched : captured ∈ matchRuleAt rule spec ambient source) :
    SupportedBodies alphabet captured :=
  matched_supported (matchRuleAt_iff.mp matched) (by simp [SupportedBodies, lookup]) support

end Mettapedia.OSLF.MeTTaIL.GeneralEquationSupport
