import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticFlow
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaInstantiationTyping

/-!
# Typed finite quantifier representations

Actual finite collection reads preserve element typing and object syntax.
The checked collection and parameter declarations justify every local binding;
restoring the lexical parameter preserves the outer representation refinements.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem RootValue.project_zero {ambient : Nat} {value : ContextualValue}
    (stored : RootValue ambient value) :
    instantiateValue? value ambient 0 [] = some value.body := by
  rcases stored with ⟨dependencies, caller, bodyScope⟩
  have identity : occurrenceAssignment 0 0 [] = Pattern.bvar := by
    funext index
    simp [occurrenceAssignment]
  simp [instantiateValue?, dependencies, caller, bodyScope, identity]

theorem TypedAssignment.bindParameter {environment : Environment} {context : Context}
    {assignment : Assignment} (typed : TypedAssignment environment context assignment)
    {parameter : String} {elementType : TypeExpr} {element : Pattern}
    (declared : lookupRuleType? context.rule parameter = some elementType)
    (dependencies : dependencies? context.spec parameter = some [])
    (elementTyped : HasType environment.language environment.free context.bound element elementType)
    (elementObject : isObjectPattern element = true) :
    TypedAssignment environment context.quantified
      (bindParameter parameter (localValue context.bound element) assignment) := by
  have removed := typed.removeParameter parameter
  constructor
  · intro name value member
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact ⟨[], elementType, dependencies,
        by simpa only [lookupRuleType?_eq_lookup, Context.quantified] using declared,
        rfl, rfl, elementTyped⟩
    · exact removed.1 name value member
  · intro name value member
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact elementObject
    · exact removed.2 name value member

theorem finiteCollection_elements_typed {environment : Environment} {context : Context}
    {assignment : Assignment} {name : String} {kind : CollType} {elements : List Pattern}
    {declaredKind : CollType} {elementType : TypeExpr} (typed : TypedAssignment environment context assignment)
    (zero : checkZeroDependencies context.spec = true)
    (declared : lookupRuleType? context.rule name = some (.collection declaredKind elementType))
    (read : finiteCollection? context.bound.length assignment name = some (kind, elements)) :
    ElementsHaveType environment.language environment.free context.bound elements elementType ∧
      isObjectPatternList elements = true := by
  have values := typed.rootValues zero
  unfold finiteCollection? at read
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at read
  obtain ⟨value, found, actual, projected, read⟩ := read
  have same := Option.some.inj ((values name value found).project_zero.symm.trans projected)
  subst actual
  unfold concreteCollection? at read
  split at read <;> try contradiction
  rename_i actualKind actualElements shape
  cases Prod.mk.inj (Option.some.inj read) with
  | intro kindEqual elementsEqual =>
    subst actualKind
    subst actualElements
    have member := ConditionalEquationExecution.lookup_assignment_member assignment name value found
    obtain ⟨dependencies, expected, specified, sortFound, metadata, _, bodyTyped⟩ :=
      typed.1 name value member
    have empty := checkZeroDependencies_sound context.spec zero name dependencies specified
    have expectedEqual := Option.some.inj
      (sortFound.symm.trans (by simpa only [lookupRuleType?_eq_lookup] using declared))
    subst expected
    have elementTyping : ElementsHaveType environment.language environment.free context.bound
        elements elementType := by
      rw [empty, List.nil_append, shape] at bodyTyped
      cases bodyTyped with
      | collection sorted => exact sorted
    have objects := typed.2 name value member
    rw [shape] at objects
    exact ⟨elementTyping, by simpa only [isObjectPattern, Option.isNone_none, Bool.true_and] using objects⟩

namespace Static

theorem Refinement.Holds.bindParameter {assignment : Assignment} {refinement : Refinement}
    (before : refinement.Holds assignment) (parameter : String) (value : ContextualValue) :
    (Refinement.mk (parameter :: refinement.available)
      (refinement.finite.filter (· != parameter))
      (refinement.atomic.filter (· != parameter))).Holds
      (bindParameter parameter value assignment) := by
  constructor
  · intro name member
    rcases List.mem_cons.mp member with same | member
    · subst name
      exact ⟨value, lookup_bind_parameter assignment parameter value⟩
    · by_cases same : name = parameter
      · subst name
        exact ⟨value, lookup_bind_parameter assignment parameter value⟩
      · obtain ⟨stored, found⟩ := before.1 name member
        exact ⟨stored, by rw [lookup_bind_other _ _ _ _ same]; exact found⟩
  constructor
  · intro name member
    rcases List.mem_filter.mp member with ⟨member, different⟩
    have different : name ≠ parameter := by simpa only [bne_iff_ne] using different
    obtain ⟨stored, kind, elements, found, shape⟩ := before.2.1 name member
    exact ⟨stored, kind, elements, by rw [lookup_bind_other _ _ _ _ different]; exact found, shape⟩
  · intro name member
    rcases List.mem_filter.mp member with ⟨member, different⟩
    have different : name ≠ parameter := by simpa only [bne_iff_ne] using different
    obtain ⟨stored, atom, found, shape⟩ := before.2.2 name member
    exact ⟨stored, atom, by rw [lookup_bind_other _ _ _ _ different]; exact found, shape⟩

end Static
end Mettapedia.OSLF.MeTTaIL.GeneralPremise
