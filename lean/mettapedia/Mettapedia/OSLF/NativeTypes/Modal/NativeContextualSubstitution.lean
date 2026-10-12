import Mettapedia.OSLF.NativeTypes.Modal.NativeEventParameters
import Mettapedia.GSLT.LanguageDef.TypedBoundSubstitution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaInstantiationObjects

/-!
# Substitution of complete authored contextual values

Ambient substitution acts below each retained dependency prefix. It keeps
the original names, list occurrences, dependency sorts and first-match
lookups. The action preserves independently authored typing and object
syntax. These laws concern retained values and assignments; they do not
assert that every authored firing is stable under substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeContextualSubstitution

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

def value (target : Nat) (substitution : ContextSubstitution.Assignment)
    (original : ContextualValue) : ContextualValue where
  dependencies := original.dependencies
  ambient := target
  body := ContextSubstitution.substitute
    (ContextSubstitution.lift original.dependencies.length substitution) original.body

@[simp] theorem value_dependencies (target : Nat) (substitution : ContextSubstitution.Assignment)
    (original : ContextualValue) :
    (value target substitution original).dependencies = original.dependencies := rfl

@[simp] theorem value_ambient (target : Nat) (substitution : ContextSubstitution.Assignment)
    (original : ContextualValue) : (value target substitution original).ambient = target := rfl

theorem value_typed {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr} {original : ContextualValue} {type : TypeExpr}
    (substitution : TypedBoundAssignment language free source target)
    (typed : HasType language free (original.dependencies ++ source) original.body type) :
    HasType language free (original.dependencies ++ target)
      (value target.length substitution.assignment original).body type :=
  typed.substituteBound (substitution.liftContext original.dependencies)

theorem value_object {target : Nat} {substitution : ContextSubstitution.Assignment}
    {original : ContextualValue} (object : isObjectPattern original.body = true)
    (images : ∀ index, isObjectPattern (substitution index) = true) :
    isObjectPattern (value target substitution original).body = true := by
  apply contextSubstitute_objects object
  intro index
  simp only [ContextSubstitution.lift]
  split
  · rfl
  · simpa only [isObjectPattern_liftBVars] using images (index - original.dependencies.length)

@[simp] theorem value_identity (original : ContextualValue) :
    value original.ambient Pattern.bvar original = original := by
  cases original
  simp [value]

theorem value_composition (middle target : Nat)
    (first second : ContextSubstitution.Assignment) (original : ContextualValue) :
    value target second (value middle first original) =
      value target (fun index => ContextSubstitution.substitute second (first index)) original := by
  cases original
  simp only [value, ContextSubstitution.substitute_comp, ContextSubstitution.lift_comp]

def assignment (target : Nat) (substitution : ContextSubstitution.Assignment)
    (original : ScopedRuleMatching.Assignment) : ScopedRuleMatching.Assignment :=
  original.map fun entry => (entry.1, value target substitution entry.2)

@[simp] theorem assignment_names (target : Nat) (substitution : ContextSubstitution.Assignment)
    (original : ScopedRuleMatching.Assignment) :
    (assignment target substitution original).map Prod.fst = original.map Prod.fst := by
  simp [assignment, List.map_map]

@[simp] theorem assignment_length (target : Nat) (substitution : ContextSubstitution.Assignment)
    (original : ScopedRuleMatching.Assignment) :
    (assignment target substitution original).length = original.length := by
  simp [assignment]

@[simp] theorem lookup_assignment (target : Nat) (substitution : ContextSubstitution.Assignment)
    (original : ScopedRuleMatching.Assignment) (name : String) :
    lookup (assignment target substitution original) name =
      (lookup original name).map (value target substitution) := by
  induction original with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | mk key item =>
          change lookup ((key, value target substitution item) :: assignment target substitution rest) name =
            (lookup ((key, item) :: rest) name).map (value target substitution)
          simp only [lookup_cons]
          split <;> simp_all

theorem assignment_typed {language : LanguageDef} {free : FreeTypeContext}
    {source target : List TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec}
    {original : ScopedRuleMatching.Assignment}
    (substitution : TypedBoundAssignment language free source target)
    (typed : ConditionalEquationExecution.AssignmentTyped language free source rule spec original) :
    ConditionalEquationExecution.AssignmentTyped language free target rule spec
      (assignment target.length substitution.assignment original) := by
  intro name transformed member
  obtain ⟨entry, present, same⟩ := List.mem_map.mp member
  cases entry with
  | mk oldName originalValue =>
      cases same
      obtain ⟨dependencies, expected, declared, sorted, metadata, ambient, bodyTyped⟩ :=
        typed oldName originalValue present
      refine ⟨dependencies, expected, declared, sorted, metadata, rfl, ?_⟩
      rw [← metadata] at bodyTyped ⊢
      exact value_typed substitution bodyTyped

theorem assignment_objects {target : Nat} {substitution : ContextSubstitution.Assignment}
    {original : ScopedRuleMatching.Assignment}
    (objects : ConditionalEquationExecution.AssignmentObjects original)
    (images : ∀ index, isObjectPattern (substitution index) = true) :
    ConditionalEquationExecution.AssignmentObjects (assignment target substitution original) := by
  intro name transformed member
  obtain ⟨entry, present, same⟩ := List.mem_map.mp member
  cases entry with
  | mk oldName originalValue =>
      cases same
      exact value_object (objects oldName originalValue present) images

theorem assignment_extension {target : Nat} {substitution : ContextSubstitution.Assignment}
    {initial final : ScopedRuleMatching.Assignment} (preserved : Extension initial final) :
    Extension (assignment target substitution initial) (assignment target substitution final) := by
  intro name transformed found
  rw [lookup_assignment] at found ⊢
  obtain ⟨original, selected, rfl⟩ := Option.map_eq_some_iff.mp found
  rw [preserved name original selected]
  rfl

theorem assignment_identity (original : ScopedRuleMatching.Assignment)
    (ambient : Nat) (contexts : ∀ name item, (name, item) ∈ original → item.ambient = ambient) :
    assignment ambient Pattern.bvar original = original := by
  induction original with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | mk name item =>
          change (name, value ambient Pattern.bvar item) :: assignment ambient Pattern.bvar rest =
            (name, item) :: rest
          have itemSame : value ambient Pattern.bvar item = item := by
            rw [← contexts name item (by simp), value_identity]
          rw [itemSame]
          rw [ih (by intro key stored member; exact contexts key stored (List.mem_cons_of_mem _ member))]

theorem assignment_composition (middle target : Nat)
    (first second : ContextSubstitution.Assignment) (original : ScopedRuleMatching.Assignment) :
    assignment target second (assignment middle first original) =
      assignment target (fun index => ContextSubstitution.substitute second (first index)) original := by
  simp only [assignment, List.map_map]
  apply List.map_congr_left
  rintro ⟨name, item⟩ _
  exact congrArg (Prod.mk name) (value_composition middle target first second item)

theorem actual_event_assignment_typed {plan : GeneralExecutionAdmission.Plan}
    {schema : Rules.Schema plan}
    (event : NativeEventFibre.Event schema)
    {target : List TypeExpr}
    (substitution : TypedBoundAssignment plan.snapshot.language plan.snapshot.free schema.bound target) :
    ConditionalEquationExecution.AssignmentTyped plan.snapshot.language plan.snapshot.free target
      schema.declaration.rule schema.declaration.binding.spec
        (assignment target.length substitution.assignment event.assignment) := by
  apply assignment_typed substitution
  intro name item member
  obtain ⟨dependencies, expected, declared, sorted, metadata, ambient, typed⟩ :=
    (NativeEventTyping.Event.assignment_typed event).1 name item member
  exact ⟨dependencies, expected, declared, sorted, metadata, ambient,
    GeneralLanguageTyping.type_transport (GeneralPlanEnvironment.grammar plan) typed⟩

end Mettapedia.OSLF.NativeTypes.Modal.NativeContextualSubstitution
