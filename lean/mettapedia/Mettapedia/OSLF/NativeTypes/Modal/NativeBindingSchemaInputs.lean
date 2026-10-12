import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaFocus
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingModalAdmission

/-!
# Independent schema inputs and their complete operational event fibres

Inputs retain an actual program, independently typed local focus and ordered
rely/matched parameter values. They do not contain a firing receipt. Actual
schema frames map to those inputs by reading their completed assignment;
ambient reindexing commutes with every readout.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaInputs

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise GeneralExecutionAdmission
open RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission IntrinsicScopedConditionalPresheaf
open NativeEventDeclarations NativeBindingSchemaCaptures NativeBindingSchemaFocus
open NativeBindingLocalValues

variable {plan : Plan}

structure Input (header : NativeModalHeaders.Header plan) (ambient : List String) (sort : String) where
  source : Term (signature plan.snapshot.language) ambient sort
  focus : Value (language := plan.snapshot.language)
    (schema plan header.origin).focusBound (schema plan header.origin).focusCarrier ambient
  rely : ∀ index : Fin header.rely.length, Value (language := plan.snapshot.language)
    header.rely[index].slot.dependencies header.rely[index].slot.expected ambient
  matched : ∀ index : Fin header.matched.length, Value (language := plan.snapshot.language)
    header.matched[index].slot.dependencies header.matched[index].slot.expected ambient

theorem input_ext {header : NativeModalHeaders.Header plan} {ambient : List String} {sort : String}
    {left right : Input header ambient sort} (source : left.source = right.source)
    (focus : left.focus = right.focus) (rely : left.rely = right.rely)
    (matched : left.matched = right.matched) : left = right := by
  cases left
  cases right
  dsimp only at source focus rely matched
  cases source
  cases focus
  cases rely
  cases matched
  rfl

def Input.action {header : NativeModalHeaders.Header plan} {source target : List String}
    (substitution : Sub (signature plan.snapshot.language) source target) {sort : String}
    (input : Input header source sort) : Input header target sort where
  source := Binding.bind substitution input.source
  focus := NativeBindingLocalValues.action substitution input.focus
  rely := fun index => NativeBindingLocalValues.action substitution (input.rely index)
  matched := fun index => NativeBindingLocalValues.action substitution (input.matched index)

theorem Input.action_identity {header : NativeModalHeaders.Header plan} {ambient : List String}
    {sort : String} (input : Input header ambient sort) :
    input.action (fun _ position => Term.var position) = input := by
  apply input_ext
  · exact Binding.bind_id input.source
  · exact NativeBindingLocalValues.action_identity input.focus
  · funext index
    exact NativeBindingLocalValues.action_identity (input.rely index)
  · funext index
    exact NativeBindingLocalValues.action_identity (input.matched index)

theorem Input.action_composition {header : NativeModalHeaders.Header plan}
    {source middle target : List String} (first : Sub (signature plan.snapshot.language) source middle)
    (second : Sub (signature plan.snapshot.language) middle target) {sort : String}
    (input : Input header source sort) :
    (input.action first).action second =
      input.action (fun sort position => Binding.bind second (first sort position)) := by
  apply input_ext
  · exact Binding.bind_comp first second input.source
  · exact NativeBindingLocalValues.action_composition first second input.focus
  · funext index
    exact NativeBindingLocalValues.action_composition first second (input.rely index)
  · funext index
    exact NativeBindingLocalValues.action_composition first second (input.matched index)

def inputs (header : NativeModalHeaders.Header plan) (sort : String) :
    Base (algebra plan.snapshot.language) ⥤ Type where
  obj X := Input header X.unop.context sort
  map morphism := TypeCat.ofHom (Input.action (NativeAuthoredEventPresheaf.morphismSub morphism))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro input
    change input.action (NativeAuthoredEventPresheaf.morphismSub (𝟙 X)) = input
    rw [NativeAuthoredEventPresheaf.morphismSub_identity]
    exact Input.action_identity input
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro input
    change input.action (NativeAuthoredEventPresheaf.morphismSub (first ≫ second)) =
      (input.action (NativeAuthoredEventPresheaf.morphismSub first)).action
        (NativeAuthoredEventPresheaf.morphismSub second)
    rw [NativeAuthoredEventPresheaf.morphismSub_composition]
    exact (Input.action_composition _ _ input).symm

def events (header : NativeModalHeaders.Header plan) (sort : String)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan)) :
    Base (algebra plan.snapshot.language) ⥤ Type where
  obj X := Frame (schema plan header.origin) X.unop.context sort
  map morphism := TypeCat.ofHom (NativeBindingSchemaFocus.action
    (schema plan header.origin) freeEmpty ready (NativeAuthoredEventPresheaf.morphismSub morphism))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro frame
    change NativeBindingSchemaFocus.action _ freeEmpty ready
      (NativeAuthoredEventPresheaf.morphismSub (𝟙 X)) frame = frame
    rw [NativeAuthoredEventPresheaf.morphismSub_identity]
    exact NativeBindingSchemaFocus.action_identity _ freeEmpty ready frame
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro frame
    change NativeBindingSchemaFocus.action _ freeEmpty ready
      (NativeAuthoredEventPresheaf.morphismSub (first ≫ second)) frame =
      NativeBindingSchemaFocus.action _ freeEmpty ready (NativeAuthoredEventPresheaf.morphismSub second)
        (NativeBindingSchemaFocus.action _ freeEmpty ready (NativeAuthoredEventPresheaf.morphismSub first) frame)
    rw [NativeAuthoredEventPresheaf.morphismSub_composition]
    exact (NativeBindingSchemaFocus.action_composition _ freeEmpty ready _ _ frame).symm

noncomputable def capture {authored : Rules.Schema plan} {ambient : List String} {sort : String}
    (point : Selected authored ambient sort) (slot : NativeEventParameters.Slot authored)
    (present : ∃ value, lookup point.val.receipt.completed slot.name = some value) :
    SlotValue authored slot ambient :=
  Classical.choose (readSlot_complete authored point slot present)

theorem capture_read {authored : Rules.Schema plan} {ambient : List String} {sort : String}
    (point : Selected authored ambient sort) (slot : NativeEventParameters.Slot authored)
    (present : ∃ value, lookup point.val.receipt.completed slot.name = some value) :
    lookup point.val.receipt.completed slot.name = some (capture point slot present).val :=
  readSlot_value authored point slot (Classical.choose_spec (readSlot_complete authored point slot present))

noncomputable def captureValue {authored : Rules.Schema plan} {ambient : List String} {sort : String}
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (point : Selected authored ambient sort) (slot : NativeEventParameters.Slot authored)
    (present : ∃ value, lookup point.val.receipt.completed slot.name = some value) :
    Value (language := plan.snapshot.language) slot.dependencies slot.expected ambient :=
  ⟨(capture point slot present).val.body,
    by simpa only [freeEmpty] using (capture point slot present).property.2.2.1,
    (capture point slot present).property.2.2.2⟩

theorem captureValue_action {authored : Rules.Schema plan} {source target : List String} {sort : String}
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    (substitution : Sub (signature plan.snapshot.language) source target)
    (point : Selected authored source sort) (slot : NativeEventParameters.Slot authored)
    (before : ∃ value, lookup point.val.receipt.completed slot.name = some value)
    (after : ∃ value, lookup
      (NativeBindingSchemaCaptures.action authored freeEmpty ready substitution point).val.receipt.completed
      slot.name = some value) :
    NativeBindingLocalValues.action substitution (captureValue freeEmpty point slot before) =
      captureValue freeEmpty (NativeBindingSchemaCaptures.action authored freeEmpty ready substitution point)
        slot after := by
  apply Subtype.ext
  have beforeRead := Classical.choose_spec (readSlot_complete authored point slot before)
  have transported := action_slot_read authored freeEmpty ready substitution point slot beforeRead
  have afterRead := capture_read
    (NativeBindingSchemaCaptures.action authored freeEmpty ready substitution point) slot after
  have same := Option.some.inj (afterRead.symm.trans transported)
  change (capture (NativeBindingSchemaCaptures.action authored freeEmpty ready substitution point) slot after).val =
    NativeContextualSubstitution.value target.length (NativeBindingRendering.assignment substitution)
      (capture point slot before).val at same
  change ContextSubstitution.substitute
    (ContextSubstitution.lift slot.dependencies.length (NativeBindingRendering.assignment substitution))
      (capture point slot before).val.body =
    (capture (NativeBindingSchemaCaptures.action authored freeEmpty ready substitution point) slot after).val.body
  rw [same]
  change ContextSubstitution.substitute
    (ContextSubstitution.lift slot.dependencies.length (NativeBindingRendering.assignment substitution))
      (capture point slot before).val.body = ContextSubstitution.substitute
    (ContextSubstitution.lift (capture point slot before).val.dependencies.length
      (NativeBindingRendering.assignment substitution)) (capture point slot before).val.body
  rw [(capture point slot before).property.1]

theorem relyPresent (header : NativeModalHeaders.Header plan)
    (decoded : NativeModalHeaders.decode? plan header.origin = some header)
    {ambient : List String} {sort : String} (frame : Frame (schema plan header.origin) ambient sort)
    (index : Fin header.rely.length) :
    ∃ value, lookup frame.point.val.receipt.completed header.rely[index].slot.name = some value := by
  apply rely_present _ frame.point
  rw [← (NativeModalHeaders.decode_parameters plan decoded).1]
  exact List.mem_map.mpr ⟨header.rely[index], List.getElem_mem index.isLt, rfl⟩

theorem matchedPresent (header : NativeModalHeaders.Header plan)
    (decoded : NativeModalHeaders.decode? plan header.origin = some header)
    {ambient : List String} {sort : String} (frame : Frame (schema plan header.origin) ambient sort)
    (index : Fin header.matched.length) :
    ∃ value, lookup frame.point.val.receipt.completed header.matched[index].slot.name = some value := by
  apply matched_present _ frame.point
  rw [← (NativeModalHeaders.decode_parameters plan decoded).2]
  exact List.mem_map.mpr ⟨header.matched[index], List.getElem_mem index.isLt, rfl⟩

noncomputable def observeValue (header : NativeModalHeaders.Header plan)
    (decoded : NativeModalHeaders.decode? plan header.origin = some header)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    {ambient : List String} {sort : String} (frame : Frame (schema plan header.origin) ambient sort) :
    Input header ambient sort where
  source := frame.point.val.source
  focus := ⟨frame.focus, by simpa only [freeEmpty] using frame.typed, frame.object, frame.canonical⟩
  rely := fun index => captureValue freeEmpty frame.point header.rely[index].slot
    (relyPresent header decoded frame index)
  matched := fun index => captureValue freeEmpty frame.point header.matched[index].slot
    (matchedPresent header decoded frame index)

theorem observeValue_action (header : NativeModalHeaders.Header plan)
    (decoded : NativeModalHeaders.decode? plan header.origin = some header)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    {source target : List String} (substitution : Sub (signature plan.snapshot.language) source target)
    {sort : String} (frame : Frame (schema plan header.origin) source sort) :
    (observeValue header decoded freeEmpty frame).action substitution =
      observeValue header decoded freeEmpty
        (NativeBindingSchemaFocus.action _ freeEmpty ready substitution frame) := by
  apply input_ext
  · rfl
  · apply Subtype.ext
    rfl
  · funext index
    exact captureValue_action freeEmpty ready substitution frame.point header.rely[index].slot _ _
  · funext index
    exact captureValue_action freeEmpty ready substitution frame.point header.matched[index].slot _ _

noncomputable def observe (header : NativeModalHeaders.Header plan)
    (decoded : NativeModalHeaders.decode? plan header.origin = some header)
    (sort : String) (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan)) :
    events header sort freeEmpty ready ⟶ inputs header sort where
  app _ := TypeCat.ofHom (observeValue header decoded freeEmpty)
  naturality X Y morphism := by
    apply ConcreteCategory.hom_ext
    intro frame
    exact (observeValue_action header decoded freeEmpty ready
      (NativeAuthoredEventPresheaf.morphismSub morphism) frame).symm

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaInputs
