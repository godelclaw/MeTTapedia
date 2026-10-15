import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQuantifierTotality
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseTotalityReadiness

/-!
# Primitive readiness derived from static representation flow

All reads are justified by actual stored captures and the authored occurrence
checks. Literal freshness names are provably absent from typed assignments.
Finite quantification derives each local sort from its concrete collection.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem typed_lookup_none {environment : Environment} {context : Context}
    {assignment : Assignment} (typed : TypedAssignment environment context assignment)
    {name : String} (literal : lookupRuleType? context.rule name = none) :
    lookup assignment name = none := by
  cases found : lookup assignment name with
  | none => rfl
  | some value =>
    obtain ⟨_, _, _, declared, _, _, _⟩ := typed.1 name value
      (ConditionalEquationExecution.lookup_assignment_member assignment name value found)
    rw [lookupRuleType?_eq_lookup] at literal
    rw [literal] at declared
    contradiction

theorem freshness_total {environment : Environment} {context : Context}
    {assignment : Assignment} {refinement : Refinement} {condition : FreshnessCondition}
    (typed : TypedAssignment environment context assignment)
    (zero : checkZeroDependencies context.spec = true) (held : refinement.Holds assignment)
    (checked : (premiseFlow environment.language environment.provider context.rule context.spec
      context.premiseIndex context.quantifierDepth refinement (.freshness condition)).supported = true) :
    ∃ atom subject, freshnessSubject? context.rule context.spec context.bound context.premiseIndex
      context.quantifierDepth assignment condition = some (atom, subject) := by
  simp only [premiseFlow, Bool.and_eq_true] at checked
  have values := typed.rootValues zero
  have atomRead : ∃ atom, freshnessName? context.bound.length assignment condition.varName = some atom := by
    have alternative : refinement.atomic.contains condition.varName = true ∨
        (lookupRuleType? context.rule condition.varName).isNone = true := by
      simpa only [Bool.or_eq_true] using checked.1.1
    rcases alternative with atomic | literal
    · exact held.2.2.project values condition.varName (List.contains_iff_mem.mp atomic)
    · have missing : lookupRuleType? context.rule condition.varName = none :=
        Option.isNone_iff_eq_none.mp literal
      exact ⟨condition.varName, by simp only [freshnessName?, typed_lookup_none typed missing]⟩
  obtain ⟨atom, atomRead⟩ := atomRead
  have names : BoundNames assignment condition.term.freeFvarNames := by
    intro name member
    exact held.1 name (namesAvailable_sound _ _ checked.2 name member)
  obtain ⟨subject, subjectRead⟩ := checkRootProjectionSchema_sound
    (operation := Substitution.instantiateBVar) (depth := 0) checked.1.2 values names
  exact ⟨atom, subject, by
    simp only [freshnessSubject?, instantiateAt?, Option.bind_eq_bind, atomRead,
      subjectRead, Option.bind_some]⟩

theorem forAll_total {environment : Environment} {context : Context}
    {assignment : Assignment} {refinement : Refinement} {collection parameter : String}
    {body : Premise} (typed : TypedAssignment environment context assignment)
    (zero : checkZeroDependencies context.spec = true) (held : refinement.Holds assignment)
    (checked : (premiseFlow environment.language environment.provider context.rule context.spec
      context.premiseIndex context.quantifierDepth refinement
      (.forAll collection parameter body)).supported = true) :
    ∃ kind elements, finiteCollection? context.bound.length assignment collection = some (kind, elements) := by
  simp only [premiseFlow, Bool.and_eq_true] at checked
  exact held.2.1.project (typed.rootValues zero) collection
    (List.contains_iff_mem.mp checked.1.1)

theorem premise_ready {environment : Environment} {context : Context}
    {assignment : Assignment} {refinement : Refinement} {premise : Premise}
    (typed : TypedAssignment environment context assignment)
    (zero : checkZeroDependencies context.spec = true) (held : refinement.Holds assignment)
    (checked : (premiseFlow environment.language environment.provider context.rule context.spec
      context.premiseIndex context.quantifierDepth refinement premise).supported = true) :
    Execution.checkGoalReady environment (.premise context premise assignment) = true := by
  cases premise with
  | relationQuery => rfl
  | freshness condition =>
    obtain ⟨atom, subject, read⟩ := freshness_total typed zero held checked
    simp only [Execution.checkGoalReady, read, Option.isSome_some]
  | forAll collection parameter body =>
    obtain ⟨kind, elements, read⟩ := forAll_total typed zero held checked
    simp only [Execution.checkGoalReady, read, Option.isSome_some]
  | congruence source target =>
    simp only [premiseFlow, Bool.and_eq_true] at checked
    cases sourceType : sourceType? environment.language context.rule source with
    | none => simp [sourceType] at checked
    | some type =>
      have names : BoundNames assignment source.freeFvarNames := by
        intro name member
        exact held.1 name (namesAvailable_sound _ _ checked.2 name member)
      obtain ⟨actual, read⟩ := checkRootProjectionSchema_sound
        (operation := Substitution.instantiateBVar) (depth := 0) checked.1.2
          (typed.rootValues zero) names
      simp only [Execution.checkGoalReady, sourceType, instantiateAt?, Context.site,
        read, Option.isSome_some, Bool.and_self]
  | scopedStep step =>
    simp only [premiseFlow, Bool.and_eq_true] at checked
    have names : BoundNames assignment step.source.freeFvarNames := by
      intro name member
      exact held.1 name (namesAvailable_sound _ _ checked.2 name member)
    obtain ⟨actual, read⟩ := checkRootProjectionSchema_sound
      (operation := Substitution.instantiateBVar) (depth := step.binders.length) checked.1.2
        (typed.rootValues zero) names
    simp only [Execution.checkGoalReady, instantiateAt?, Context.site, read, Option.isSome_some]

theorem quantifier_element_typed {environment : Environment} {context : Context}
    {assignment : Assignment} {refinement : Refinement} {collection parameter : String}
    {body : Premise} {kind : CollType} {element : Pattern} {elements : List Pattern}
    (typed : TypedAssignment environment context assignment)
    (zero : checkZeroDependencies context.spec = true)
    (checked : (premiseFlow environment.language environment.provider context.rule context.spec
      context.premiseIndex context.quantifierDepth refinement
      (.forAll collection parameter body)).supported = true)
    (read : finiteCollection? context.bound.length assignment collection = some (kind, element :: elements)) :
    TypedAssignment environment context.quantified
      (bindParameter parameter (localValue context.bound element) assignment) := by
  simp only [premiseFlow, Bool.and_eq_true] at checked
  split at checked <;> try simp at checked
  rename_i collectionKind elementType parameterType collectionDeclared parameterDeclared
  have typeSame := checked.1.2.1
  subst parameterType
  obtain ⟨elementsTyped, objects⟩ := finiteCollection_elements_typed typed zero collectionDeclared read
  cases elementsTyped with
  | cons elementTyped tailTyped =>
    simp only [isObjectPatternList, Bool.and_eq_true] at objects
    exact typed.bindParameter parameterDeclared checked.1.2.2 elementTyped objects.1

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Static
