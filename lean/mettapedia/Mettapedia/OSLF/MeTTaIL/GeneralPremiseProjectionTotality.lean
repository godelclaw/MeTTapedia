import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFlow
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseTyping

/-!
# Total occurrence projections for dependency-free captures

Typing and matching derive the stored context and ordinary scope of captured
values. A dependency-free value can therefore be read under any additional
binder prefix. Structural matching preserves this invariant, including
provider outputs and collection-rest captures.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching ContextSubstitution
open Mettapedia.GSLT.LanguageDef.WellSorted

def RootValue (ambient : Nat) (value : ContextualValue) : Prop :=
  value.dependencies = [] ∧ value.ambient = ambient ∧
    value.body.isWellScopedAt ambient = true

def RootValues (ambient : Nat) (assignment : ScopedRuleMatching.Assignment) : Prop :=
  ∀ name value, lookup assignment name = some value → RootValue ambient value

def checkZeroDependencies (spec : RuleBindingSpec) : Bool :=
  spec.dependencies.all fun entry => entry.2.isEmpty

theorem checkZeroDependencies_sound (spec : RuleBindingSpec)
    (checked : checkZeroDependencies spec = true) (name : String) (dependencies : List TypeExpr)
    (found : dependencies? spec name = some dependencies) : dependencies = [] := by
  unfold dependencies? at found
  split at found
  · rename_i key actual selected
    have depsEqual : actual = dependencies := Option.some.inj found
    have actualMember : (key, actual) ∈
        spec.dependencies.filter (fun entry => entry.1 == name) := by
      rw [selected]
      exact List.mem_singleton_self _
    have empty := List.all_eq_true.mp checked (key, actual) (List.mem_filter.mp actualMember).1
    simpa only [depsEqual, List.isEmpty_iff] using empty
  · contradiction

theorem instantiateValue_body_scoped {value : ContextualValue} {ambient depth : Nat}
    {arguments : List Pattern} {target : Pattern}
    (read : instantiateValue? value ambient depth arguments = some target) :
    value.body.isWellScopedAt (value.dependencies.length + ambient) = true := by
  unfold instantiateValue? at read
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read
  · contradiction
  · rename_i bodyScope
    exact Bool.eq_true_of_not_eq_false (by simpa using bodyScope)

theorem RootValue.project {ambient : Nat} {value : ContextualValue}
    (stored : RootValue ambient value) (depth : Nat) :
    ∃ result, instantiateValue? value ambient depth [] = some result := by
  rcases stored with ⟨dependencies, caller, bodyScope⟩
  let assignment := occurrenceAssignment 0 depth []
  have assignmentScoped : WellScopedAssignment ambient (depth + ambient) assignment := by
    intro index within
    simp only [assignment, occurrenceAssignment, Nat.not_lt_zero, ↓reduceIte,
      Nat.sub_zero, Pattern.isWellScopedAt]
    exact decide_eq_true (by omega)
  have resultScoped := ContextSubstitution.substitute_wellScoped assignmentScoped bodyScope
  refine ⟨ContextSubstitution.substitute assignment value.body, ?_⟩
  simp [instantiateValue?, dependencies, caller, bodyScope, resultScoped, assignment]

theorem TypedAssignment.rootValues {environment : Environment} {context : Context}
    {assignment : ScopedRuleMatching.Assignment}
    (typed : TypedAssignment environment context assignment)
    (zero : checkZeroDependencies context.spec = true) :
    RootValues context.bound.length assignment := by
  intro name value found
  obtain ⟨dependencies, expected, declared, _, metadata, ambient, sorted⟩ :=
    typed.1 name value (ConditionalEquationExecution.lookup_assignment_member _ _ _ found)
  have noDependencies := checkZeroDependencies_sound context.spec zero name dependencies declared
  refine ⟨metadata.trans noDependencies, ambient, ?_⟩
  simpa only [noDependencies, List.nil_append] using sorted.isWellScopedAt

theorem recover_rootValue {spec : RuleBindingSpec} {name : String}
    {dependencies : List TypeExpr} {ambient depth : Nat} {arguments : List Pattern}
    {target : Pattern} {value : ContextualValue}
    (zero : checkZeroDependencies spec = true)
    (declared : dependencies? spec name = some dependencies)
    (recovered : recoverValue? dependencies ambient depth arguments target = some value) :
    RootValue ambient value := by
  have metadata := recoverValue?_context _ _ _ _ _ _ recovered
  have bodyScoped := instantiateValue_body_scoped
    (recoverValue?_forward _ _ _ _ _ _ recovered)
  have noDependencies := checkZeroDependencies_sound spec zero name dependencies declared
  refine ⟨metadata.1.trans noDependencies, metadata.2, ?_⟩
  simpa only [metadata.1, noDependencies, List.length_nil, Nat.zero_add] using bodyScoped

theorem assign_rootValues {ambient : Nat} {initial final : ScopedRuleMatching.Assignment}
    {name : String} {value : ContextualValue}
    (before : RootValues ambient initial) (stored : RootValue ambient value)
    (assigned : assign initial name value = some final) : RootValues ambient final := by
  unfold assign at assigned
  cases previous : lookup initial name with
  | none =>
      rw [previous] at assigned
      cases Option.some.inj assigned
      intro queried foundValue found
      by_cases same : queried = name
      · subst queried
        simp only [lookup_cons, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at found
        subst foundValue
        exact stored
      · apply before queried foundValue
        simpa only [lookup_cons, show (name == queried) = false from by simp [Ne.symm same],
          Bool.false_eq_true, ↓reduceIte] using found
  | some previousValue =>
      simp only [previous] at assigned
      split at assigned
      · cases Option.some.inj assigned
        exact before
      · contradiction

theorem capture_rootValues {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    {name : String} {target : Pattern}
    (zero : checkZeroDependencies spec = true) (before : RootValues ambient initial)
    (captured : capture? rule spec ambient depth site path initial name target = some final) :
    RootValues ambient final := by
  simp only [capture?, Option.bind_eq_bind, Option.bind_eq_some_iff] at captured
  obtain ⟨dependencies, declared, arguments, occurrence, value, recovered, assigned⟩ := captured
  exact assign_rootValues before (recover_rootValue zero declared recovered) assigned

mutual
  theorem matching_rootValues {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
      {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
      {schema target : Pattern}
      (zero : checkZeroDependencies spec = true) (before : RootValues ambient initial)
      (matching : GeneralScopedMatch.Matches rule spec ambient site path depth initial schema target final) :
      RootValues ambient final := by
    cases matching with
    | capture captured => exact capture_rootValues zero before captured
    | bound => exact before
    | constructor arguments => exact matchingArguments_rootValues zero before arguments
    | binder body => exact matching_rootValues zero before body
    | binders body => exact matching_rootValues zero before body
    | substitution body replacement =>
        exact matching_rootValues zero (matching_rootValues zero before body) replacement
    | bag _ bag => exact matchingBag_rootValues zero before bag
    | vector arguments => exact matchingArguments_rootValues zero before arguments
    | vectorRest arguments captured =>
        exact capture_rootValues zero (matchingArguments_rootValues zero before arguments)
          (by simpa only [captureRest?] using captured)

  theorem matchingArguments_rootValues {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
      {initial final : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
      (zero : checkZeroDependencies spec = true) (before : RootValues ambient initial)
      (matching : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas targets final) :
      RootValues ambient final := by
    cases matching with
    | nil => exact before
    | cons head tail =>
        exact matchingArguments_rootValues zero (matching_rootValues zero before head) tail

  theorem matchingBag_rootValues {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
      {initial final : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
      {rest : Option String} {kind : CollType}
      (zero : checkZeroDependencies spec = true) (before : RootValues ambient initial)
      (matching : GeneralScopedMatch.Bag rule spec ambient site path depth initial index schemas rest kind targets final) :
      RootValues ambient final := by
    cases matching with
    | nil => exact before
    | rest captured => exact capture_rootValues zero before (by simpa only [captureRest?] using captured)
    | cons _ _ head tail =>
        exact matchingBag_rootValues zero (matching_rootValues zero before head) tail
end

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
