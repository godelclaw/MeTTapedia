import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingScopedBodies
import Mettapedia.OSLF.NativeTypes.Modal.NativeAuthoredEventAction
import Mettapedia.OSLF.NativeTypes.Generation.NativeModalParameters
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCanonicalFlow

/-!
# Ordered authored captures over varying program contexts

An event is an actual original operational receipt at a fixed authored
declaration index. Its completed captures obtain scope, sorting, object
shape and canonical metadata from independent matching and premise proofs.
Reindexing keeps each slot name and origin, and transports its actual body.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaCaptures

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise GeneralExecutionAdmission
open RuleBinding ScopedRuleMatching
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open IntrinsicScopedConditionalPresheaf
open NativeBindingEventAction (bound)
open NativeAuthoredEventAction NativeEventParameters
open Mettapedia.OSLF.Framework.RedexPosition

variable {plan : Plan} (schema : Rules.Schema plan)

abbrev Selected (context : List String) (sort : String) :=
  {point : Point (GeneralPlanEnvironment.environment plan) plan.snapshot.language context sort |
    point.receipt.index = schema.ordinal}

def context (ambient : List String) : GeneralPremise.Context :=
  ⟨schema.ordinal, schema.declaration.rule, schema.declaration.binding.spec,
    bound ambient, 0, 0⟩

theorem completed_typed {ambient : List String} {sort : String}
    (point : Selected schema ambient sort) :
    TypedAssignment (GeneralPlanEnvironment.environment plan) (context schema ambient)
      point.val.receipt.completed := by
  obtain ⟨rule, spec, declared, specified, typed⟩ :=
    RootFiring.completed_typed point.val.receipt.valid
  rw [point.property] at declared specified
  have authored := GeneralPlanEnvironment.selected_rule plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  have bindingLookup := GeneralPlanEnvironment.selected_specification plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  cases Option.some.inj (declared.symm.trans authored)
  cases Option.some.inj (specified.symm.trans bindingLookup)
  exact typed

theorem completed_canonical {ambient : List String} {sort : String}
    (point : Selected schema ambient sort) : CanonicalValues point.val.receipt.completed := by
  cases point.val.receipt.valid with
  | fire _ _ _ sourceTyped matching _ premises _ _ =>
      exact premises.canonical
        (matching_canonicalValues CanonicalValues.empty sourceTyped.2.1 matching.matching)

theorem left_present {ambient : List String} {sort : String}
    (point : Selected schema ambient sort) :
    Present point.val.receipt.completed (fvarNames schema.declaration.rule.left) := by
  obtain ⟨rule, declared, present⟩ := firing_present point.val.receipt.valid
  rw [point.property] at declared
  have authored := GeneralPlanEnvironment.selected_rule plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  cases Option.some.inj (declared.symm.trans authored)
  exact present

theorem rely_present {ambient : List String} {sort : String}
    (point : Selected schema ambient sort) :
    Present point.val.receipt.completed schema.relyNames := by
  intro name member
  apply left_present schema point name
  apply context_names_subset
  exact (List.mem_filter.mp (List.mem_eraseDups.mp member)).1

theorem matched_present {ambient : List String} {sort : String}
    (point : Selected schema ambient sort) :
    Present point.val.receipt.completed schema.matchedNames := by
  intro name member
  apply left_present schema point name
  apply focus_names_subset _ schema.position
  unfold Rules.Schema.matchedNames at member
  unfold Mettapedia.OSLF.Framework.RedexPosition.focusFreeVars
  cases selected : Mettapedia.OSLF.Framework.RedexPosition.subtermAt
      schema.declaration.rule.left schema.position <;>
    simpa only [selected, Option.map_none, Option.map_some, Option.getD_none,
      Option.getD_some] using member

/-- Local contextual data retains its precise original authored slot. -/
abbrev SlotValue (slot : Slot schema) (ambient : List String) :=
  {value : ContextualValue | value.dependencies = slot.dependencies ∧
    value.ambient = ambient.length ∧
    HasType plan.snapshot.language plan.snapshot.free
      (slot.dependencies ++ bound ambient) value.body slot.expected ∧
    isObjectPattern value.body = true ∧ value.body.hasCanonicalBinderMetadata = true}

def readSlot {ambient : List String} {sort : String}
    (point : Selected schema ambient sort) (slot : Slot schema) : Option (SlotValue schema slot ambient) :=
  match found : lookup point.val.receipt.completed slot.name with
  | none => none
  | some value => some ⟨value, by
      have member := ConditionalEquationExecution.lookup_assignment_member _ _ _ found
      obtain ⟨dependencies, expected, declared, sorted, metadata, ambientLength, typed⟩ :=
        (completed_typed schema point).1 slot.name value member
      have sameDependencies := Option.some.inj (declared.symm.trans slot.declared)
      have sameExpected := Option.some.inj (sorted.symm.trans slot.sorted)
      rw [sameDependencies, sameExpected] at typed
      exact ⟨metadata.trans sameDependencies, by simpa only [context, bound,
        Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.length_map] using ambientLength,
        GeneralLanguageTyping.type_transport (GeneralPlanEnvironment.grammar plan) typed,
        (completed_typed schema point).2 slot.name value member,
        completed_canonical schema point slot.name value found⟩⟩

theorem readSlot_value {ambient : List String} {sort : String}
    (point : Selected schema ambient sort) (slot : Slot schema) {value : SlotValue schema slot ambient}
    (read : readSlot schema point slot = some value) :
    lookup point.val.receipt.completed slot.name = some value.val := by
  unfold readSlot at read
  split at read
  · cases read
  · rename_i actual found
    cases Option.some.inj read
    exact found

theorem readSlot_complete {ambient : List String} {sort : String}
    (point : Selected schema ambient sort) (slot : Slot schema)
    (present : ∃ value, lookup point.val.receipt.completed slot.name = some value) :
    ∃ value, readSlot schema point slot = some value := by
  obtain ⟨value, found⟩ := present
  unfold readSlot
  split
  · rename_i absent
    rw [found] at absent
    cases absent
  · exact ⟨_, rfl⟩

def action (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    {source target : List String}
    (substitution : Sub (signature plan.snapshot.language) source target) {sort : String}
    (point : Selected schema source sort) : Selected schema target sort :=
  ⟨NativeAuthoredEventAction.action (GeneralPlanEnvironment.grammar plan) freeEmpty ready substitution point.val,
    (congrArg NativeReceiptRechecking.Payload.index
      (NativeAuthoredEventAction.action_read (GeneralPlanEnvironment.grammar plan)
        freeEmpty ready substitution point.val)).trans point.property⟩

theorem action_source (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    {source target : List String}
    (substitution : Sub (signature plan.snapshot.language) source target) {sort : String}
    (point : Selected schema source sort) :
    (action schema freeEmpty ready substitution point).val.source =
      Binding.bind substitution point.val.source := rfl

theorem action_completed (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    {source target : List String}
    (substitution : Sub (signature plan.snapshot.language) source target) {sort : String}
    (point : Selected schema source sort) :
    (action schema freeEmpty ready substitution point).val.receipt.completed =
      NativeContextualSubstitution.assignment target.length
        (NativeBindingRendering.assignment substitution) point.val.receipt.completed := by
  simpa only [action, NativeReceiptRechecking.read, NativeOperationalReceiptTransport.payload,
    bound, Mettapedia.GSLT.Poly.BindingLanguage.typeContext, List.length_map] using
    (congrArg NativeReceiptRechecking.Payload.completed
      (NativeAuthoredEventAction.action_read (GeneralPlanEnvironment.grammar plan)
        freeEmpty ready substitution point.val))

theorem action_slot_read (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    {source target : List String}
    (substitution : Sub (signature plan.snapshot.language) source target) {sort : String}
    (point : Selected schema source sort) (slot : Slot schema)
    {value : SlotValue schema slot source} (read : readSlot schema point slot = some value) :
    lookup (action schema freeEmpty ready substitution point).val.receipt.completed slot.name =
      some (NativeContextualSubstitution.value target.length
        (NativeBindingRendering.assignment substitution) value.val) := by
  rw [action_completed, NativeContextualSubstitution.lookup_assignment,
    readSlot_value schema point slot read]
  rfl

theorem action_identity (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    {ambient : List String} {sort : String} (point : Selected schema ambient sort) :
    action schema freeEmpty ready (fun _ position => Term.var position) point = point := by
  apply Subtype.ext
  exact NativeAuthoredEventAction.action_identity (GeneralPlanEnvironment.grammar plan) freeEmpty ready point.val

theorem action_composition (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    {source middle target : List String}
    (first : Sub (signature plan.snapshot.language) source middle)
    (second : Sub (signature plan.snapshot.language) middle target) {sort : String}
    (point : Selected schema source sort) :
    action schema freeEmpty ready second (action schema freeEmpty ready first point) =
      action schema freeEmpty ready (fun sort position => Binding.bind second (first sort position)) point := by
  apply Subtype.ext
  exact NativeAuthoredEventAction.action_composition (GeneralPlanEnvironment.grammar plan)
    freeEmpty ready first second point.val

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaCaptures
