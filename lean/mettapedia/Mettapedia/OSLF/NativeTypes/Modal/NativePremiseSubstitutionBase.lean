import Mettapedia.OSLF.NativeTypes.Modal.NativePremisePosition
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCanonicalProjection

/-!
# Bound-context and lexical data of operational premise substitution

The action retains rule indices and exact argument sites. Quantifier shadowing,
restoration and ordered finite collections commute with the action. Authored
object typing is preserved using an actual typed bound assignment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativePremiseSubstitutionBase

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

def context (bound : List TypeExpr) (original : Context) : Context := {original with bound}

@[simp] theorem context_site (bound : List TypeExpr) (original : Context) (index : Nat) :
    (context bound original).site index = original.site index := rfl

@[simp] theorem context_next (bound : List TypeExpr) (original : Context) :
    context bound original.next = (context bound original).next := rfl

@[simp] theorem context_quantified (bound : List TypeExpr) (original : Context) :
    context bound original.quantified = (context bound original).quantified := rfl

theorem located_preserved (bound : List TypeExpr) {original : Context} {premise : Premise}
    (located : NativePremisePosition.Located original premise) :
    NativePremisePosition.Located (context bound original) premise := located

theorem typed_assignment {environment : Environment} {original : Context} {target : List TypeExpr}
    {stored : ScopedRuleMatching.Assignment}
    (substitution : TypedBoundAssignment environment.language environment.free original.bound target)
    (images : ∀ index, isObjectPattern (substitution.assignment index) = true)
    (typed : TypedAssignment environment original stored) :
    TypedAssignment environment (context target original)
      (NativeContextualSubstitution.assignment target.length substitution.assignment stored) :=
  ⟨NativeContextualSubstitution.assignment_typed substitution typed.1,
    NativeContextualSubstitution.assignment_objects typed.2 images⟩

theorem canonical_lift {substitution : ContextSubstitution.Assignment}
    (canonical : ∀ index, (substitution index).hasCanonicalBinderMetadata = true) (arity : Nat) :
    ∀ index, (ContextSubstitution.lift arity substitution index).hasCanonicalBinderMetadata = true := by
  intro index
  simp only [ContextSubstitution.lift]
  split
  · rfl
  · simpa only [hasCanonicalBinderMetadata_liftBVars] using canonical (index - arity)

theorem objects_lift {substitution : ContextSubstitution.Assignment}
    (objects : ∀ index, isObjectPattern (substitution index) = true) (arity : Nat) :
    ∀ index, isObjectPattern (ContextSubstitution.lift arity substitution index) = true := by
  intro index
  simp only [ContextSubstitution.lift]
  split
  · rfl
  · simpa only [isObjectPattern_liftBVars] using objects (index - arity)

theorem well_sorted {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr} {type : TypeExpr} {actual : Pattern}
    (substitution : TypedBoundAssignment language free source target)
    (canonical : ∀ index, (substitution.assignment index).hasCanonicalBinderMetadata = true)
    (objects : ∀ index, isObjectPattern (substitution.assignment index) = true)
    (sorted : OpenPatternWellSorted language free source type actual) :
    OpenPatternWellSorted language free target type
      (ContextSubstitution.substitute substitution.assignment actual) := by
  exact ⟨sorted.1.substituteBound substitution,
    contextSubstitute_canonical sorted.2.1 canonical,
    contextSubstitute_objects sorted.2.2.1 objects,
    ContextSubstitution.substitute_wellScoped substitution.wellScoped sorted.2.2.2⟩

theorem remove_parameter (target : Nat) (substitution : ContextSubstitution.Assignment)
    (parameter : String) (stored : ScopedRuleMatching.Assignment) :
    NativeContextualSubstitution.assignment target substitution (removeParameter parameter stored) =
      removeParameter parameter (NativeContextualSubstitution.assignment target substitution stored) := by
  induction stored with
  | nil => rfl
  | cons entry entries ih =>
      cases entry with
      | mk name value =>
          simp only [removeParameter, NativeContextualSubstitution.assignment, List.map_cons]
          split <;> simp_all only [NativeContextualSubstitution.assignment, List.map_cons]

theorem bind_parameter (target : Nat) (substitution : ContextSubstitution.Assignment)
    (parameter : String) (value : ContextualValue) (stored : ScopedRuleMatching.Assignment) :
    NativeContextualSubstitution.assignment target substitution (bindParameter parameter value stored) =
      bindParameter parameter (NativeContextualSubstitution.value target substitution value)
        (NativeContextualSubstitution.assignment target substitution stored) := by
  simp only [bindParameter, NativeContextualSubstitution.assignment, List.map_cons]
  exact congrArg (List.cons (parameter, NativeContextualSubstitution.value target substitution value))
    (remove_parameter target substitution parameter stored)

theorem local_value (source target : List TypeExpr) (substitution : ContextSubstitution.Assignment) (actual : Pattern) :
    NativeContextualSubstitution.value target.length substitution (localValue source actual) =
      localValue target (ContextSubstitution.substitute substitution actual) := by
  simp only [NativeContextualSubstitution.value, localValue, List.length_nil, ContextSubstitution.lift_zero]

theorem restore_parameter (target : Nat) (substitution : ContextSubstitution.Assignment)
    (parameter : String) (initial final : ScopedRuleMatching.Assignment) :
    NativeContextualSubstitution.assignment target substitution (restoreParameter parameter initial final) =
      restoreParameter parameter (NativeContextualSubstitution.assignment target substitution initial)
        (NativeContextualSubstitution.assignment target substitution final) := by
  simp only [restoreParameter, NativeContextualSubstitution.lookup_assignment]
  cases found : lookup initial parameter with
  | none => simp only [Option.map_none]; exact remove_parameter target substitution parameter final
  | some value =>
      simp only [Option.map_some, NativeContextualSubstitution.assignment, List.map_cons]
      exact congrArg (List.cons (parameter, NativeContextualSubstitution.value target substitution value))
        (remove_parameter target substitution parameter final)

theorem finite_collection {source target : Nat} {stored : ScopedRuleMatching.Assignment} {name : String}
    {kind : CollType} {elements : List Pattern}
    (accepted : finiteCollection? source stored name = some (kind, elements))
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    finiteCollection? target (NativeContextualSubstitution.assignment target substitution stored) name =
      some (kind, elements.map (ContextSubstitution.substitute substitution)) := by
  simp only [finiteCollection?, Option.bind_eq_bind] at accepted ⊢
  cases found : lookup stored name with
  | none => simp only [found, Option.bind_none] at accepted; contradiction
  | some value =>
      simp only [found, Option.bind_some] at accepted
      cases read : instantiateValue? value source 0 [] with
      | none => simp only [read, Option.bind_none] at accepted; contradiction
      | some actual =>
          simp only [read, Option.bind_some] at accepted
          rw [NativeContextualSubstitution.lookup_assignment, found]
          simp only [Option.map_some, Option.bind_some]
          rw [NativeValueInstantiationSubstitution.successful_instantiation_substitutes read
            (by intro item member; cases member) substitution boundScoped]
          simp only [Option.bind_some, ContextSubstitution.lift_zero]
          cases actual with
          | collection actualKind actualElements rest =>
              cases rest with
              | none =>
                  have same : (actualKind, actualElements) = (kind, elements) := Option.some.inj accepted
                  cases same
                  simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, concreteCollection?]
              | some rest => contradiction
          | _ => contradiction

end Mettapedia.OSLF.NativeTypes.Modal.NativePremiseSubstitutionBase
