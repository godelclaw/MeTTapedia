import Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl
import Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer
import Mettapedia.OSLF.NativeTypes.Modal.ProgramAdmission
import Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.Source

open Mettapedia.OSLF.Framework

/-!
# The original REST-bearing COMM schema through the generator

The original open remainder belongs to the authored schema and survives
typing descent. It is separate from the concrete object supplied to the
certified execution engine. The same generated system emits a native COMM
receipt and computes the input-continuation schema with its extra remainder
coordinate. The no-remainder three-slot communication presentation stays distinct.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.SchemaConsumer

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema)
open Mettapedia.GSLT.LanguageDef.WellSorted

def generated := Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.generated

def runtimePlan : Plan :=
  ⟨GeneralRho.snapshot, GeneralRho.permissions, [GeneralRho.declaration], [], []⟩

theorem runtime_plan_actual : generated.plan = runtimePlan := by
  rw [show generated.plan = GeneralRho.plan from Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.actual_plan]
  cbv

theorem original_rest_program_is_classified :
    Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.programCarrierStatus GeneralRho.language GeneralRho.comm =
      .classified [.base "Proc"] := by cbv

theorem original_rest_source_is_typed :
    HasType GeneralRho.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree GeneralRho.comm) []
      GeneralRho.comm.left (.base "Proc") := by
  have classified := Mettapedia.OSLF.NativeTypes.Modal.ProgramCarriers.program_status_sound original_rest_program_is_classified
  exact (classified.2.2.2 (.base "Proc") List.mem_cons_self).2

theorem original_rest_is_not_a_concrete_object : isObjectPattern GeneralRho.comm.left = false := by
  decide +kernel

def continuationSchema? : Option (Schema generated.plan) :=
  generated.modalCatalogue.find? fun schema =>
    schema.position == Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.restSite.position &&
      schema.programCarrier == .base "Proc"

def schemaReadout {plan : Plan} (schema : Schema plan) :=
  (schema.programCarrier, schema.focusCarrier, schema.bound, schema.focusBound,
    schema.declaration.declarationIndex, schema.position, schema.relyNames)

theorem computed_continuation_schema :
    continuationSchema?.map schemaReadout = some
      (.base "Proc", .arrow (.base "Name") (.base "Proc"), [], [], 0,
        Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.restSite.position, ["rest", "n", "q"]) := by
  change ((Mettapedia.OSLF.NativeTypes.Generation.schemas generated.plan).find? fun schema =>
    schema.position == Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.restSite.position &&
      schema.programCarrier == .base "Proc").map schemaReadout = _
  rw [runtime_plan_actual]
  cbv

theorem continuation_schema_is_present : continuationSchema?.isSome = true := by
  have present := congrArg Option.isSome computed_continuation_schema
  simpa using present

def continuationSchema : Schema generated.plan := continuationSchema?.get continuation_schema_is_present

theorem continuation_schema_computed : continuationSchema? = some continuationSchema :=
  (Option.some_get continuation_schema_is_present).symm

theorem continuation_schema_member : continuationSchema ∈ generated.modalCatalogue :=
  List.mem_of_find?_eq_some continuation_schema_computed

theorem continuation_schema_readout : schemaReadout continuationSchema =
    (.base "Proc", .arrow (.base "Name") (.base "Proc"), [], [], 0,
      Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.restSite.position, ["rest", "n", "q"]) := by
  have computed := computed_continuation_schema
  rw [continuation_schema_computed] at computed
  exact Option.some.inj computed

theorem continuation_parameters_are_computed :
    ∃ parameters, generated.modalParameters? continuationSchema = some parameters :=
  Mettapedia.OSLF.NativeTypes.Generation.generated_modal_parameters_complete GeneralRho.snapshot Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.fragment
    Mettapedia.OSLF.NativeTypes.Structural.heytingFragment Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.vertex continuationSchema
    continuation_schema_member

theorem continuation_schema_keeps_original_rule : continuationSchema.declaration.rule = GeneralRho.comm := by
  have original := continuationSchema.declared
  have rules : generated.plan.rules = [GeneralRho.declaration] := congrArg Plan.rules runtime_plan_actual
  rw [rules] at original
  have same : continuationSchema.declaration = GeneralRho.declaration :=
    List.mem_singleton.mp (List.fst_mem_of_mem_zipIdx original)
  rw [same]
  rfl

def typedContinuation? : Option SiteData :=
  (Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.generate GeneralRho.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree GeneralRho.comm)
    .all [] (.base "Proc") GeneralRho.comm.left).find? fun site =>
      site.address == Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.restSite.position

def siteReadout (site : SiteData) := (site.context, site.focus, site.focusBound, site.focusType)

theorem computed_typed_continuation_preserves_tail :
    typedContinuation?.map siteReadout = some
      (Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.restContext, .lambda none (.fvar "p"), [],
        .arrow (.base "Name") (.base "Proc")) := by cbv

theorem typed_continuation_is_present : typedContinuation?.isSome = true := by
  have present := congrArg Option.isSome computed_typed_continuation_preserves_tail
  simpa using present

def typedContinuation : SiteData := typedContinuation?.get typed_continuation_is_present

theorem typed_continuation_computed : typedContinuation? = some typedContinuation :=
  (Option.some_get typed_continuation_is_present).symm

theorem typed_continuation_is_independently_typed :
    Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.Licensed GeneralRho.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree GeneralRho.comm)
      .all [] (.base "Proc") GeneralRho.comm.left typedContinuation :=
  Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.generate_sound _ _ _ _ _ _ _
    (List.mem_of_find?_eq_some typed_continuation_computed)

theorem original_context_keeps_its_rest :
    typedContinuation.context = Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.restContext := by
  have computed := computed_typed_continuation_preserves_tail
  rw [typed_continuation_computed] at computed
  exact congrArg Prod.fst (Option.some.inj computed)

def authoredSite : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site :=
  {Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.restSite with rule := GeneralRho.comm}

def family := Mettapedia.OSLF.NativeTypes.SortProfiles.Slots.modalFamily GeneralRho.language authoredSite

theorem raw_source_inputs_are_computed :
    family.inputs = [("n", some (.base "Name")), ("q", some (.base "Proc")),
      ("rest", some (.collection .hashBag (.base "Proc")))] := by decide +kernel

theorem rest_schema_has_one_extra_slot :
    continuationSchema.relyNames.length + 1 = family.slotCount ∧
      family.slotCount = Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.family.slotCount + 1 := by
  have names := congrArg (fun readout => readout.2.2.2.2.2.2) continuation_schema_readout
  change continuationSchema.relyNames = ["rest", "n", "q"] at names
  rw [names]
  decide +kernel

/-- Both the schematic type and the native receipt are produced through the
same selected generator, with the original REST declaration retained. -/
theorem same_generator_types_and_executes_comm :
    continuationSchema ∈ generated.modalCatalogue ∧
      continuationSchema.declaration.rule.left = rhoCommRewrite.left ∧
      (generated.execute [] (.base "Proc") GeneralRho.FrontierControls.rootSource 40).answers.length = 1 := by
  refine ⟨continuation_schema_member, ?_, Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl.communication_emits_one_native_receipt⟩
  rw [continuation_schema_keeps_original_rule]
  exact GeneralRho.comm_original_source.2.1

end Mettapedia.OSLF.NativeTypes.Instances.Rho.SchemaConsumer
