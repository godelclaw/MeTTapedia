import Mettapedia.OSLF.NativeTypes.Generation.SchemaAdmission

open Mettapedia.OSLF.Framework

/-!
# Modal codes at the generator's actual sort coordinates

Input sorts are looked up by the rely names of the typed authored schema.
Missing coordinates are refused; they never acquire a default universe.
The continuation and generated focus code have the same computed result
sort. The meaning is the single specified-contractum former, with complete
scoped assignments and dependent continuation evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.Modal.Formation
open ModalHypercube (HSort)

structure ModalParameters {plan : Plan} (schema : Schema plan) where
  inputs : RelyIndex schema → HSort
  output : HSort

def schemaAssignment? (generated : Generated) (schema : Schema generated.plan) : Option Assignment :=
  generated.sortAssignments.find? fun assignment =>
    assignment.family.origin == .modal schema.declaration.declarationIndex schema.position

def relySort? (assignment : Assignment) (name : String) : Option HSort :=
  (assignment.family.inputs.map Prod.fst |>.zip assignment.inputs).lookup name

def Generated.modalParameters? (generated : Generated) (schema : Schema generated.plan) :
    Option (ModalParameters schema) :=
  match schemaAssignment? generated schema with
  | none => none
  | some assignment =>
      if complete : schema.relyNames.all (fun name => (relySort? assignment name).isSome) = true then
        some {inputs := fun name => (relySort? assignment name.val).get (by
          exact (List.all_eq_true.mp complete) name.val name.property), output := assignment.output}
      else none

theorem modal_parameters_origins {generated : Generated} {schema : Schema generated.plan}
    {parameters : ModalParameters schema}
    (computed : generated.modalParameters? schema = some parameters) :
    ∃ assignment ∈ generated.sortAssignments,
      assignment.family.origin = .modal schema.declaration.declarationIndex schema.position ∧
      parameters.output = assignment.output ∧
      ∀ name, relySort? assignment name.val = some (parameters.inputs name) := by
  unfold Generated.modalParameters? at computed
  cases found : schemaAssignment? generated schema with
  | none => simp [found] at computed
  | some assignment =>
      simp only [found] at computed
      split at computed
      · rename_i complete
        rw [← Option.some.inj computed]
        have member := List.mem_of_find?_eq_some found
        have selected := List.find?_some found
        refine ⟨assignment, member, by simpa using selected, rfl, ?_⟩
        intro name
        exact (Option.some_get (by exact (List.all_eq_true.mp complete) name.val name.property)).symm
      · cases computed

/-- The input interface is derived from the computed coordinate, including
the universe indices of every rely code and of the continuation. -/
def ModalInputs {plan : Plan} (schema : Schema plan) : Option (ModalParameters schema) → Type
  | none => Unit
  | some parameters =>
      RelyCodes schema parameters.inputs ×
        (Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment →
          TypeCode plan schema.bound schema.programCarrier parameters.output)

/-- A failed coordinate computation has no semantic former. The successful
branch constructs the actual modal type code, rather than a catalogue label. -/
def Generated.modalFormer? (generated : Generated) (schema : Schema generated.plan)
    (inputs : ModalInputs schema (generated.modalParameters? schema)) :
    Option (Σ sort : HSort, TypeCode generated.plan schema.focusBound schema.focusCarrier sort) :=
  if generated.equationAdmission = some true ∧ generated.logicFragment.core.modal = true ∧
      generated.schemaAdmitted? schema = true then
    match parameters : generated.modalParameters? schema with
    | none => none
    | some profile =>
        let supplied : ModalInputs schema (some profile) := parameters ▸ inputs
        some ⟨profile.output,
          generatedFormer schema profile.inputs profile.output profile.output supplied.1 supplied.2⟩
  else none

/-- A successful generated former reads the output slot of its authored
occurrence; changing that coordinate changes its sort index. -/
theorem generated_modal_result_slot {generated : Generated} {schema : Schema generated.plan}
    (inputs : ModalInputs schema (generated.modalParameters? schema))
    {code : Σ sort : HSort, TypeCode generated.plan schema.focusBound schema.focusCarrier sort}
    (formed : generated.modalFormer? schema inputs = some code) :
    ∃ assignment ∈ generated.sortAssignments,
      assignment.family.origin = .modal schema.declaration.declarationIndex schema.position ∧
      code.1 = assignment.output := by
  unfold Generated.modalFormer? at formed
  split at formed
  · split at formed
    · cases formed
    · rename_i parameters computed
      cases formed
      obtain ⟨assignment, member, origin, result, _⟩ := modal_parameters_origins computed
      exact ⟨assignment, member, origin, result⟩
  · cases formed

theorem rejected_equation_profile_has_no_modal_code {generated : Generated}
    {schema : Schema generated.plan}
    (inputs : ModalInputs schema (generated.modalParameters? schema))
    (rejected : generated.equationAdmission = some false) :
    generated.modalFormer? schema inputs = none := by
  simp [Generated.modalFormer?, rejected]

theorem disabled_modal_fragment_has_no_code {generated : Generated}
    {schema : Schema generated.plan}
    (inputs : ModalInputs schema (generated.modalParameters? schema))
    (disabled : generated.logicFragment.core.modal = false) :
    generated.modalFormer? schema inputs = none := by
  simp [Generated.modalFormer?, disabled]

theorem unlisted_schema_has_no_modal_code {generated : Generated}
    {schema : Schema generated.plan}
    (inputs : ModalInputs schema (generated.modalParameters? schema))
    (absent : schema ∉ generated.modalCatalogue) :
    generated.modalFormer? schema inputs = none := by
  simp [Generated.modalFormer?, generated_schema_rejected absent]

theorem generated_modal_formation {generated : Generated} {schema : Schema generated.plan}
    (inputs : ModalInputs schema (generated.modalParameters? schema))
    {code : Σ sort : HSort, TypeCode generated.plan schema.focusBound schema.focusCarrier sort}
    (formed : generated.modalFormer? schema inputs = some code) {term : Pattern}
    (inhabited : code.2.meaning term) :
    (∃ assignment ∈ generated.sortAssignments,
      assignment.family.origin = .modal schema.declaration.declarationIndex schema.position ∧
      code.1 = assignment.output) ∧
    Mettapedia.GSLT.LanguageDef.WellSorted.HasType generated.snapshot.language generated.snapshot.free
      schema.focusBound term schema.focusCarrier := by
  exact ⟨generated_modal_result_slot inputs formed, code.2.bounded term inhabited⟩

end Mettapedia.OSLF.NativeTypes.Generation
