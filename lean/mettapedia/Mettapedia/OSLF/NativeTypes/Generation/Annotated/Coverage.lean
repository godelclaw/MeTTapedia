import Mettapedia.OSLF.NativeTypes.Generation.Annotated.Schemas
import Mettapedia.OSLF.NativeTypes.Generation.ModalCoverage

open Mettapedia.OSLF.Framework

/-!
# Complete native coordinates for annotated generated schemas

Annotations instantiate arbitrary source and focus carriers without changing
the authored redex origin. The native sort coordinates are already generated
for every raw authored site. The original declaration and checked one-hole
context therefore earn a complete profile at every annotated instance.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.SortProfiles.Slots (Origin)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Derived (CubeVertex modalAssignment assignments)
open ModalHypercube (HSort)

theorem annotated_source_authored_site {generated : Generated} (source : AnnotatedSource generated) :
    source.site ∈ Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate generated.snapshot.language := by
  apply (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate_spec _ _).mpr
  exact ⟨List.mk_mem_zipIdx_iff_getElem?.mpr source.authored, source.selected⟩

theorem generated_annotated_assignment_exists (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language)
    (checked : AnnotatedSchema (generate snapshot language logic vertex)) :
    ∃ assignment, schemaAssignment? (generate snapshot language logic vertex) checked.schema = some assignment := by
  let generated := generate snapshot language logic vertex
  obtain ⟨index, below, readback⟩ := List.getElem_of_mem (annotated_source_authored_site checked.source)
  let coordinate : Fin (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate generated.snapshot.language).length := ⟨index, below⟩
  let assignment := modalAssignment generated.snapshot.language vertex.1 coordinate
  have assignmentMember : assignment ∈ generated.sortAssignments := by
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨coordinate, rfl⟩
  have assignmentOrigin : assignment.family.origin =
      .modal checked.schema.declaration.declarationIndex checked.schema.position := by
    change Origin.modal (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate generated.snapshot.language)[index].declaration
      (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate generated.snapshot.language)[index].position = _
    rw [readback, checked.original_declaration]
    rfl
  have found : (schemaAssignment? generated checked.schema).isSome = true := by
    apply List.find?_isSome.mpr
    exact ⟨assignment, assignmentMember, by simpa using assignmentOrigin⟩
  exact Option.isSome_iff_exists.mp found

/-- Every independently annotated raw site of an actual generated output
has all its rely coordinates and its result coordinate, at arbitrary types. -/
theorem generated_annotated_parameters_complete (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language)
    (checked : AnnotatedSchema (generate snapshot language logic vertex)) :
    ∃ parameters, (generate snapshot language logic vertex).modalParameters? checked.schema = some parameters := by
  let generated := generate snapshot language logic vertex
  obtain ⟨assignment, found⟩ := generated_annotated_assignment_exists snapshot language logic vertex checked
  have member := List.mem_of_find?_eq_some found
  have origin : assignment.family.origin =
      .modal checked.schema.declaration.declarationIndex checked.schema.position := by
    simpa using List.find?_some found
  have original : (checked.schema.declaration.authored, checked.schema.declaration.declarationIndex) ∈
      generated.snapshot.language.rewrites.zipIdx := by
    rw [checked.original_declaration]
    rw [checked.original_authored]
    exact List.mk_mem_zipIdx_iff_getElem?.mpr checked.source.authored
  have complete : checked.schema.relyNames.all (fun name => (relySort? assignment name).isSome) = true := by
    apply List.all_eq_true.mpr
    intro name relies
    exact assignment_rely_sort_complete generated.snapshot.language vertex checked.schema.declaration
      original checked.schema.position assignment member origin name relies
  unfold Generated.modalParameters?
  rw [found]
  simp only [complete, dif_pos]
  exact ⟨_, rfl⟩

/-- M-FORM for every accepted annotated instance, before any modal inhabitant
is supplied. The finite concrete carrier catalogue is not a premise. -/
theorem generated_annotated_m_form (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language)
    (checked : AnnotatedSchema (generate snapshot language logic vertex))
    (equations : (generate snapshot language logic vertex).equationAdmission = some true)
    (enabled : logic.core.modal = true)
    (inputs : ModalInputs checked.schema ((generate snapshot language logic vertex).modalParameters? checked.schema)) :
    ∃ code, (generate snapshot language logic vertex).annotatedModalFormer? checked inputs = some code ∧
      ∃ assignment ∈ (generate snapshot language logic vertex).sortAssignments,
        assignment.family.origin = .modal checked.schema.declaration.declarationIndex checked.schema.position ∧
        code.1 = assignment.output := by
  obtain ⟨parameters, computed⟩ := generated_annotated_parameters_complete snapshot language logic vertex checked
  obtain ⟨code, formed, _⟩ := annotated_modal_formation_complete checked inputs equations enabled computed
  exact ⟨code, formed, annotated_modal_result_slot checked inputs formed⟩

end Mettapedia.OSLF.NativeTypes.Generation
