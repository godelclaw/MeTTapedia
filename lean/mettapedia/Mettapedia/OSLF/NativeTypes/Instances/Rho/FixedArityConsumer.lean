import Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityBinding
import Mettapedia.OSLF.NativeTypes.Generation.ModalCoverage

open Mettapedia.OSLF.Framework

/-!
# Fixed-arity scoped communication through one executable generator

The source has two rely inputs and no collection remainder.
Its checked binding companion is executed with the authored reflective
substitution profile. Typed modal schemas and sort parameters come from the
same generator that emits the native operational receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityBinding
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema)
open Mettapedia.OSLF.NativeTypes.Modal.Formation (RelyIndex)
open ModalHypercube (HSort)

def fragment : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment := {operational := permissions}

def chosen := Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot fragment

theorem chosen_snapshot : chosen = snapshot := by
  change ({snapshot with language := Mettapedia.OSLF.NativeTypes.Generation.selectedLanguage language ⟨none, permissions⟩} : Snapshot) = _
  rw [Mettapedia.OSLF.NativeTypes.Generation.unrestricted_signature]
  rfl

def vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex chosen.language :=
  (fun _ => .star, fun _ => .star)

def generated := Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment
  Mettapedia.OSLF.NativeTypes.Structural.heytingFragment vertex

theorem all_generated_modal_schemas_licensed {schema : Schema generated.plan}
    (member : schema ∈ generated.modalCatalogue) :
    schema.bound = [] ∧
      schema.programCarrier ∈ Mettapedia.OSLF.NativeTypes.Generation.Occurrences.sourceCandidates generated.plan.snapshot.language
        schema.declaration.rule ∧
      ∃ site, Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.Licensed
        generated.plan.snapshot.language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree schema.declaration.rule)
        .all [] schema.programCarrier schema.declaration.rule.left site ∧
        schema.position = site.address ∧ schema.focusBound = site.focusBound ∧
        schema.focusCarrier = site.focusType := by
  change schema ∈ Mettapedia.OSLF.NativeTypes.Generation.schemas generated.plan at member
  exact Mettapedia.OSLF.NativeTypes.Generation.schemas_sound member

theorem all_generated_modal_coordinates_complete (schema : Schema generated.plan)
    (member : schema ∈ generated.modalCatalogue) :
    ∃ parameters, generated.modalParameters? schema = some parameters :=
  Mettapedia.OSLF.NativeTypes.Generation.generated_modal_parameters_complete snapshot fragment
    Mettapedia.OSLF.NativeTypes.Structural.heytingFragment vertex schema member

def runtimePlan : Plan := ⟨snapshot, permissions, [declaration], [], []⟩

theorem runtime_plan_actual : generated.plan = runtimePlan := by
  change compile chosen permissions = runtimePlan
  rw [chosen_snapshot]
  cbv

def zero : Pattern := .apply "PZero" []
def channel : Pattern := .apply "NQuote" [zero]
def receivedBody : Pattern := .apply "PDrop" [.bvar 0]
def communication : Pattern := source channel receivedBody zero
def result : Pattern := .collection .hashBag [zero] none

def request := generated.request [] (.base "Proc") communication
def execution := generated.execute [] (.base "Proc") communication 40

def literalRequest : GeneralOccurrenceFrontier.Request := ⟨runtimePlan, [], .base "Proc", communication⟩

theorem actual_request : request = literalRequest := by
  change (⟨generated.plan, [], .base "Proc", communication⟩ : GeneralOccurrenceFrontier.Request) = _
  rw [runtime_plan_actual]
  rfl

theorem literal_start : GeneralOccurrenceFrontier.start literalRequest =
    {agenda := [.visit ⟨communication, [], by
      rw [show literalRequest.root = communication from
        Pattern.eraseBinderMetadata_eq_self_of_canonical (by decide +kernel)]
      exact .nil communication⟩, .universe]} := by
  have canonical : communication.eraseBinderMetadata = communication :=
    Pattern.eraseBinderMetadata_eq_self_of_canonical (by decide +kernel)
  simp only [GeneralOccurrenceFrontier.start, GeneralOccurrenceFrontier.Request.root,
    literalRequest, runtimePlan, canonical, List.map_nil]
  change (if checkOpenPatternWellSorted language snapshot.free [] (.base "Proc") communication then _ else _) = _
  rw [show checkOpenPatternWellSorted language snapshot.free [] (.base "Proc") communication = true from
    by decide +kernel]
  rfl

structure Readout where
  declarationIndex : Nat
  address : List Nat
  body : Option RuleBinding.ContextualValue
  payload : Option RuleBinding.ContextualValue
  channel : Option RuleBinding.ContextualValue
  remainder : Option RuleBinding.ContextualValue
  right : Pattern
  target : Pattern
  administration : Nat
  deriving DecidableEq, Repr

def rawReadout (receipt : GeneralOccurrenceSemantics.Receipt) : Readout :=
  ⟨receipt.firing.job.declaration.declarationIndex, receipt.firing.job.site.address,
    ScopedRuleMatching.lookup receipt.firing.completed "p",
    ScopedRuleMatching.lookup receipt.firing.completed "q",
    ScopedRuleMatching.lookup receipt.firing.completed "n",
    ScopedRuleMatching.lookup receipt.firing.completed "rest",
    receipt.firing.job.declaration.rule.right, receipt.target, receipt.conversions.length⟩

def readouts (query : GeneralOccurrenceFrontier.Request) (budget : Nat) : List Readout :=
  (GeneralOccurrenceFrontier.run query budget (GeneralOccurrenceFrontier.start query)).answers.map
    fun receipt => rawReadout receipt.val

def expectedReadout : Readout :=
  ⟨0, [], some ⟨[.base "Name"], 0, receivedBody⟩, some ⟨[], 0, zero⟩,
    some ⟨[], 0, channel⟩, none, GeneratedHypercubeInstances.rhoCommPaper.right, result, 0⟩

theorem actual_no_remainder_communication : readouts request 40 = [expectedReadout] := by
  rw [actual_request]
  unfold readouts
  rw [literal_start]
  decide +kernel

theorem one_actual_answer : execution.answers.length = 1 := by
  have count := congrArg List.length actual_no_remainder_communication
  simpa only [readouts, List.length_map, List.length_singleton, execution,
    Mettapedia.OSLF.NativeTypes.Generation.Generated.execute, request] using count

def receipt : GeneralOccurrenceFrontier.Answer request :=
  execution.answers[0]'(by rw [one_actual_answer]; decide)

theorem receipt_readout : rawReadout receipt.val = expectedReadout := by
  have member : receipt ∈ execution.answers := List.getElem_mem _
  have projected : rawReadout receipt.val ∈ readouts request 40 := List.mem_map.mpr ⟨receipt, member, rfl⟩
  rw [actual_no_remainder_communication] at projected
  exact List.mem_singleton.mp projected

theorem original_right_hand_side_and_target :
    receipt.val.firing.job.declaration.rule.right = GeneratedHypercubeInstances.rhoCommPaper.right ∧
      receipt.val.target = result :=
  ⟨congrArg Readout.right receipt_readout, congrArg Readout.target receipt_readout⟩

theorem received_body_dependency_and_no_remainder :
    ScopedRuleMatching.lookup receipt.val.firing.completed "p" =
      some ⟨[.base "Name"], 0, receivedBody⟩ ∧
      ScopedRuleMatching.lookup receipt.val.firing.completed "rest" = none :=
  ⟨congrArg Readout.body receipt_readout, congrArg Readout.remainder receipt_readout⟩

theorem native_target_is_typed : OpenPatternWellSorted generated.snapshot.language generated.snapshot.free
    [] (.base "Proc") result := by
  have typed := GeneralOccurrenceNativeReceipts.target_typed generated.plan [] (.base "Proc") receipt
  dsimp only [Mettapedia.OSLF.NativeTypes.Generation.Generated.plan, GeneralExecutionAdmission.compile] at typed
  simpa only [original_right_hand_side_and_target.2] using typed

theorem one_primitive_no_equation_administration :
    (GeneralOccurrenceNativeReceipts.history generated.plan [] (.base "Proc") receipt).length = 1 ∧
      GeneralOccurrenceNativeReceipts.administration generated.plan [] (.base "Proc") receipt = 0 :=
  ⟨GeneralOccurrenceNativeReceipts.primitive_count _ _ _ _,
    congrArg Readout.administration receipt_readout⟩

theorem actual_generated_semantic_communication :
    (GeneralOccurrenceSemantics.gslt generated.plan [] (.base "Proc")).Step communication result := by
  have step := GeneralOccurrenceSemantics.Receipt.semantic_step generated.plan [] (.base "Proc") receipt.property
  have root : request.root = communication :=
    Pattern.eraseBinderMetadata_eq_self_of_canonical (by decide +kernel)
  simpa only [root, original_right_hand_side_and_target.2] using step

def continuationSchema? : Option (Schema generated.plan) :=
  generated.modalCatalogue.find? fun schema =>
    schema.position == Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.continuationSite.position &&
      schema.programCarrier == .base "Proc"

def schemaReadout {plan : Plan} (schema : Schema plan) :=
  (schema.programCarrier, schema.focusCarrier, schema.bound, schema.focusBound,
    schema.declaration.declarationIndex, schema.position, schema.relyNames)

theorem computed_continuation_schema :
    continuationSchema?.map schemaReadout = some
      (.base "Proc", .arrow (.base "Name") (.base "Proc"), [], [], 0,
        Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.continuationSite.position, ["n", "q"]) := by
  change ((Mettapedia.OSLF.NativeTypes.Generation.schemas generated.plan).find? fun schema =>
    schema.position == Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.continuationSite.position &&
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
      Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.continuationSite.position, ["n", "q"]) := by
  have computed := computed_continuation_schema
  rw [continuation_schema_computed] at computed
  exact Option.some.inj computed

theorem continuation_parameters_are_computed :
    ∃ parameters, generated.modalParameters? continuationSchema = some parameters :=
  all_generated_modal_coordinates_complete continuationSchema continuation_schema_member

theorem actual_continuation_carriers_and_inputs :
    continuationSchema.programCarrier = .base "Proc" ∧
      continuationSchema.focusCarrier = .arrow (.base "Name") (.base "Proc") ∧
      continuationSchema.bound = [] ∧ continuationSchema.focusBound = [] ∧
      continuationSchema.declaration.declarationIndex = 0 ∧
      continuationSchema.position = Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.continuationSite.position ∧
      continuationSchema.relyNames = ["n", "q"] := by
  simpa only [schemaReadout, Prod.mk.injEq] using continuation_schema_readout

theorem executed_continuation_has_source_geometry :
    continuationSchema.relyNames = Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.continuationSite.relyNames ∧
      continuationSchema.relyNames.length + 1 = Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.family.slotCount := by
  obtain ⟨_, _, _, _, _, _, inputs⟩ := actual_continuation_carriers_and_inputs
  constructor
  · rw [inputs, Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.actual_rely_inputs]
  · rw [inputs, Mettapedia.OSLF.NativeTypes.Instances.Rho.CommunicationGeometry.computed_three_slots]
    rfl

theorem continuation_schema_keeps_original_rule : continuationSchema.declaration.rule = comm := by
  have original := continuationSchema.declared
  have rules : generated.plan.rules = [declaration] := congrArg Plan.rules runtime_plan_actual
  rw [rules] at original
  have same : continuationSchema.declaration = declaration :=
    List.mem_singleton.mp (List.fst_mem_of_mem_zipIdx original)
  rw [same]
  rfl

theorem actual_matched_body_name : continuationSchema.matchedNames = ["p"] := by
  obtain ⟨_, _, _, _, _, position, _⟩ := actual_continuation_carriers_and_inputs
  unfold Mettapedia.OSLF.NativeTypes.Modal.Rules.Schema.matchedNames
  rw [continuation_schema_keeps_original_rule, position]
  decide +kernel

private theorem every_assignment_reads_the_star_vertex (assignment : Mettapedia.OSLF.NativeTypes.Generation.Assignment)
    (member : assignment ∈ generated.sortAssignments) :
    assignment.inputs = List.replicate assignment.family.inputs.length HSort.star ∧
      assignment.output = HSort.star := by
  change assignment ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.assignments chosen.language vertex at member
  rcases List.mem_append.mp member with modal | structural
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp modal
    subst assignment
    simp [Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.modalAssignment, vertex, List.ofFn_const]
  · obtain ⟨entry, _, same⟩ := List.mem_map.mp structural
    subst assignment
    simp [Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.structuralAssignment, Mettapedia.OSLF.NativeTypes.SortProfiles.Slots.structuralFamily,
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.input, Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output, vertex, List.ofFn_const]

/-- Both actual rely names and the output coordinate read their sorts from
the generated vertex. The body name remains in the scoped receipt instead. -/
theorem actual_continuation_parameter_sorts
    {parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters continuationSchema}
    (computed : generated.modalParameters? continuationSchema = some parameters) :
    parameters.output = .star ∧ ∀ name : RelyIndex continuationSchema, parameters.inputs name = .star := by
  obtain ⟨assignment, member, _, output, lookup⟩ := Mettapedia.OSLF.NativeTypes.Generation.modal_parameters_origins computed
  have assigned := every_assignment_reads_the_star_vertex assignment member
  refine ⟨output.trans assigned.2, ?_⟩
  intro name
  obtain ⟨before, after, rows, _⟩ := List.lookup_eq_some_iff.mp (lookup name)
  have pairMember : (name.val, parameters.inputs name) ∈
      (assignment.family.inputs.map Prod.fst).zip assignment.inputs := by
    rw [rows]
    simp
  have valueMember := (List.of_mem_zip pairMember).2
  rw [assigned.1] at valueMember
  exact (List.mem_replicate.mp valueMember).2

theorem zero_budget_stays_silent : (generated.execute [] (.base "Proc") communication 0).answers = [] := by
  change (GeneralOccurrenceFrontier.start request).answers = []
  rw [actual_request, literal_start]

end Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer
