import Mettapedia.OSLF.NativeTypes.Modal.NativeEventFibre
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseTyping

/-!
# Sorted readouts of complete scoped operational events

Typing is recovered from the actual licensed firing and equation witnesses.
The resulting source, focus and target values inhabit the original authored
sorted carriers. Rely values and their scoped assignments remain part of the
event, together with the ordered execution evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeEventTyping

open _root_.CategoryTheory Opposite
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open NativeEventFibre

universe u
variable {plan : Plan} {schema : Schema plan}

private theorem equation_has_types {bound : List TypeExpr} {carrier : TypeExpr}
    {source target : Pattern}
    (equation : GeneralOccurrenceSemantics.Equation plan bound carrier source target) :
    HasType plan.snapshot.language plan.snapshot.free bound source carrier ∧
      HasType plan.snapshot.language plan.snapshot.free bound target carrier := by
  obtain ⟨receipt, complete, endpoint⟩ := equation
  have targetTyped := complete.accepted.2.2
  rw [← complete.endpoint, endpoint] at targetTyped
  exact ⟨((GeneralPlanEnvironment.typing_iff plan bound carrier source).mp complete.sourceTyped).1,
    ((GeneralPlanEnvironment.typing_iff plan bound carrier target).mp targetTyped).1⟩

theorem equation_conversion_preserves_typing {bound : List TypeExpr} {carrier : TypeExpr}
    {source target : Pattern}
    (conversion : Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation plan bound carrier) source target) :
    HasType plan.snapshot.language plan.snapshot.free bound source carrier ↔
      HasType plan.snapshot.language plan.snapshot.free bound target carrier := by
  induction conversion with
  | rel _ _ equation =>
      have sorts := equation_has_types equation
      exact ⟨fun _ => sorts.2, fun _ => sorts.1⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ leftIH rightIH => exact leftIH.trans rightIH

theorem Event.source_typed (event : Event schema) :
    HasType plan.snapshot.language plan.snapshot.free schema.bound event.source schema.programCarrier := by
  have representative := GeneralLanguageTyping.type_transport (GeneralPlanEnvironment.grammar plan)
    event.valid.2.1.2.source_typed
  exact (equation_conversion_preserves_typing event.valid.1.equivalent).mpr representative

theorem Event.target_typed (event : Event schema) :
    HasType plan.snapshot.language plan.snapshot.free schema.bound event.target schema.programCarrier :=
  (equation_conversion_preserves_typing event.conversion).mp
    (GeneralOccurrenceSemantics.Receipt.target_sorted plan schema.bound schema.programCarrier event.valid).1

/-- Authored program values use the exact declared free and bound contexts. -/
abbrev ProgramCarrier (schema : Schema plan) :=
  {term : Pattern | HasType plan.snapshot.language plan.snapshot.free schema.bound term schema.programCarrier}

abbrev FocusCarrier (schema : Schema plan) :=
  {term : Pattern | HasType plan.snapshot.language plan.snapshot.free schema.focusBound term schema.focusCarrier}

def Event.sortedSource (event : Event schema) : ProgramCarrier schema :=
  ⟨event.source, (Event.source_typed event)⟩

def Event.sortedTarget (event : Event schema) : ProgramCarrier schema :=
  ⟨event.target, (Event.target_typed event)⟩

def Event.sortedFocus (event : Event schema) : FocusCarrier schema :=
  ⟨event.focus, event.focusTyped⟩

theorem Event.sorted_readout (event : Event schema) :
    schema.fill? event.assignment (Event.sortedFocus event).val = some (Event.sortedSource event).val ∧
      schema.rhs? event.assignment = some (Event.sortedTarget event).val ∧
      (GeneralOccurrenceSemantics.gslt plan schema.bound schema.programCarrier).Step
        (Event.sortedSource event).val (Event.sortedTarget event).val :=
  ⟨event.filling, event.specified, event.semantic_step schema⟩

theorem Event.completed_typing (event : Event schema) :
    ∃ rule spec, (GeneralPlanEnvironment.environment plan).language.rewrites[event.receipt.firing.job.ordinal]? = some rule ∧
      GeneralPremise.specification? (GeneralPlanEnvironment.environment plan) event.receipt.firing.job.ordinal = some spec ∧
      GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan)
        ⟨event.receipt.firing.job.ordinal, rule, spec,
          event.receipt.firing.job.site.focusBound, 0, 0⟩ event.receipt.firing.completed :=
  GeneralPremise.Interpreted.RootFiring.completed_typed (event.root_firing schema)

/-- The actual rule and scoped specification are recovered from authored
declaration lookup. Local captures are typed in the same ambient context as
the schema; its nonroot focus has its separate binder-extended context. -/
theorem Event.assignment_typed (event : Event schema) :
    GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan)
      schema.context event.assignment := by
  obtain ⟨rule, spec, declared, specified, typed⟩ := Event.completed_typing event
  rw [event.ordinal] at declared specified
  have authored := GeneralPlanEnvironment.selected_rule plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  have bindingLookup := GeneralPlanEnvironment.selected_specification plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  have sameRule := Option.some.inj (declared.symm.trans authored)
  have sameSpec := Option.some.inj (specified.symm.trans bindingLookup)
  subst rule
  subst spec
  simpa only [Schema.context, event.ordinal, event.ambient, event.completed] using typed

section Presheaves

variable {W : Type u} [Category.{u} W]

abbrev programPresheaf (schema : Schema plan) : Wᵒᵖ ⥤ Type u :=
  (Functor.const Wᵒᵖ).obj (ULift.{u} (ProgramCarrier schema))

abbrev focusPresheaf (schema : Schema plan) : Wᵒᵖ ⥤ Type u :=
  (Functor.const Wᵒᵖ).obj (ULift.{u} (FocusCarrier schema))

/-- These maps land in the independently authored sorted carriers. They do
not introduce a second permissive raw-pattern operational semantics. -/
def sortedSource : eventPresheaf schema ⟶ programPresheaf (W := W) schema where
  app _ := TypeCat.ofHom fun event => ⟨(Event.sortedSource event.down)⟩
  naturality _ _ _ := rfl

def sortedTarget : eventPresheaf schema ⟶ programPresheaf (W := W) schema where
  app _ := TypeCat.ofHom fun event => ⟨(Event.sortedTarget event.down)⟩
  naturality _ _ _ := rfl

def sortedFocus : eventPresheaf schema ⟶ focusPresheaf (W := W) schema where
  app _ := TypeCat.ofHom fun event => ⟨(Event.sortedFocus event.down)⟩
  naturality _ _ _ := rfl

theorem complete_sorted_fibre_readout (world : W) (input : Input)
    (value : NativeFibre schema world input) :
    let event := (decode schema world input value).val
    HasType plan.snapshot.language plan.snapshot.free schema.bound event.source schema.programCarrier ∧
      HasType plan.snapshot.language plan.snapshot.free schema.bound event.target schema.programCarrier ∧
      schema.rhs? input.2 = some (Event.sortedTarget event).val := by
  exact ⟨(Event.source_typed (decode schema world input value).val),
    (Event.target_typed (decode schema world input value).val),
    (complete_event_readout schema world input value).2.1⟩

end Presheaves

end Mettapedia.OSLF.NativeTypes.Modal.NativeEventTyping
