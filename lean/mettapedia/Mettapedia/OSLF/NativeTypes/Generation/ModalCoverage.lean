import Mettapedia.OSLF.NativeTypes.Generation.Occurrences.NameBridge
import Mettapedia.OSLF.NativeTypes.Generation.ModalCodes

open Mettapedia.OSLF.Framework

/-!
# Complete modal coordinates of authored typed schemas

The schema catalogue and the sort catalogue use independent occurrence
traversals. Original declaration indices and the earned context-name bridge
identify the matching computed coordinate. Every rely input is then obtained
from the actual vertex, including beneath binders and in collections with a
retained remainder. No missing input acquires a default sort.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.SortProfiles.Slots (Origin modalFamily)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Derived (CubeVertex modalAssignment assignments)
open ModalHypercube (HSort)

private theorem zip_lookup_complete (names : List String) (sorts : List HSort)
    (lengths : sorts.length = names.length) (name : String) (member : name ∈ names) :
    ((names.zip sorts).lookup name).isSome = true := by
  induction names generalizing sorts with
  | nil => simp at member
  | cons first names ih =>
      cases sorts with
      | nil => simp at lengths
      | cons sort sorts =>
          have tails : sorts.length = names.length := by simpa using lengths
          by_cases equal : name = first
          · subst name
            simp
          · have tailMember : name ∈ names := by simpa [equal] using member
            have different : (name == first) = false := by simpa using equal
            simpa only [List.zip_cons_cons, List.lookup_cons, different] using ih sorts tails tailMember

private theorem modal_assignment_member (language : LanguageDef) (vertex : CubeVertex language)
    (index : Fin (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language).length) :
    modalAssignment language vertex.1 index ∈ assignments language vertex := by
  apply List.mem_append_left
  exact List.mem_ofFn.mpr ⟨index, rfl⟩

/-- A matching computed coordinate covers the complete independently read
rely context, even when the two occurrence traversals order names differently. -/
theorem assignment_rely_sort_complete (language : LanguageDef) (vertex : CubeVertex language)
    (declaration : RulePlan)
    (declared : (declaration.authored, declaration.declarationIndex) ∈ language.rewrites.zipIdx)
    (position : RedexPosition.Position) (assignment : Assignment)
    (member : assignment ∈ assignments language vertex)
    (origin : assignment.family.origin = .modal declaration.declarationIndex position)
    (name : String) (rely : name ∈ RedexPosition.relyVars declaration.rule.left position) :
    (relySort? assignment name).isSome = true := by
  rcases List.mem_append.mp member with modal | structural
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp modal
    subst assignment
    let site := (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language)[index]
    have generated : site ∈ Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language := List.getElem_mem _
    have sameOrigin : site.declaration = declaration.declarationIndex ∧ site.position = position := by
      exact Origin.modal.inj origin
    have original := ((Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate_spec _ _).mp generated).1
    have source1 := List.mk_mem_zipIdx_iff_getElem?.mp original
    have source2 := List.mk_mem_zipIdx_iff_getElem?.mp declared
    rw [sameOrigin.1] at source1
    have sameRule : site.rule = declaration.authored := Option.some.inj (source1.symm.trans source2)
    have sourceRely : name ∈ RedexPosition.relyVars site.rule.left site.position := by
      simpa only [sameRule, sameOrigin.2, RulePlan.rule,
        Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference.BindingPlan.elaborate] using rely
    have siteRely := (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generated_rely_member generated name).mp sourceRely
    apply zip_lookup_complete
    · simpa only [List.length_map] using
        Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.modal_inputs_exact language vertex.1 index
    · simpa [modalAssignment, modalFamily, List.map_map, site] using siteRely
  · obtain ⟨entry, _, same⟩ := List.mem_map.mp structural
    subst assignment
    cases origin

private theorem schema_original_declaration {generated : Generated}
    (schema : Schema generated.plan) :
    (schema.declaration.authored, schema.declaration.declarationIndex) ∈
      generated.snapshot.language.rewrites.zipIdx := by
  have member : schema.declaration ∈ generated.plan.rules := by
    have projected : schema.declaration ∈ generated.plan.rules.zipIdx.map Prod.fst := List.mem_map.mpr
      ⟨(schema.declaration, schema.ordinal), schema.declared, rfl⟩
    simpa only [List.zipIdx_map_fst] using projected
  obtain ⟨rule, index, authored, _, compiled⟩ := compiled_rule_origin member
  have readout := rulePlan_readout compiled
  simpa only [readout.1, readout.2.1] using authored

/-- The lookup succeeds because the typed source descent produces an
independently specified authored site at the exact original rule index. -/
theorem generated_schema_assignment_exists (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language)
    (schema : Schema (generate snapshot language logic vertex).plan)
    (member : schema ∈ schemas (generate snapshot language logic vertex).plan) :
    ∃ assignment, schemaAssignment? (generate snapshot language logic vertex) schema = some assignment := by
  let generated := generate snapshot language logic vertex
  obtain ⟨_, _, data, licensed, position, _, _⟩ := schemas_sound member
  let site : Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Site :=
    {context := data.context, focus := data.focus,
      declaration := schema.declaration.declarationIndex, rule := schema.declaration.authored}
  have sourceSite : site ∈ Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate generated.snapshot.language := by
    apply (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate_spec _ _).mpr
    refine ⟨schema_original_declaration schema, ?_⟩
    simpa only [RulePlan.rule,
      Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference.BindingPlan.elaborate] using licensed.selects
  obtain ⟨index, below, readback⟩ := List.getElem_of_mem sourceSite
  let coordinate : Fin (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate generated.snapshot.language).length := ⟨index, below⟩
  let assignment := modalAssignment generated.snapshot.language vertex.1 coordinate
  have assignmentMember : assignment ∈ generated.sortAssignments :=
    modal_assignment_member _ _ coordinate
  have assignmentOrigin : assignment.family.origin =
      .modal schema.declaration.declarationIndex schema.position := by
    change Origin.modal (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate generated.snapshot.language)[index].declaration
      (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate generated.snapshot.language)[index].position = _
    rw [readback]
    change Origin.modal schema.declaration.declarationIndex
      (Mettapedia.OSLF.MeTTaIL.GeneralTypedSites.contextAddress data.context) = _
    rw [← licensed.address_eq, ← position]
  have found : (schemaAssignment? generated schema).isSome = true := by
    apply List.find?_isSome.mpr
    refine ⟨assignment, assignmentMember, ?_⟩
    simpa using assignmentOrigin
  exact Option.isSome_iff_exists.mp found

/-- Every typed schema of the actual generator receives all its computed
input sorts and its result sort. This is a whole-presentation theorem. -/
theorem generated_schema_parameters_complete (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language)
    (schema : Schema (generate snapshot language logic vertex).plan)
    (member : schema ∈ schemas (generate snapshot language logic vertex).plan) :
    ∃ parameters, (generate snapshot language logic vertex).modalParameters? schema = some parameters := by
  let generated := generate snapshot language logic vertex
  obtain ⟨assignment, found⟩ := generated_schema_assignment_exists snapshot language logic vertex schema member
  have assignmentMember := List.mem_of_find?_eq_some found
  have assignmentOrigin : assignment.family.origin =
      .modal schema.declaration.declarationIndex schema.position := by
    simpa using List.find?_some found
  have complete : schema.relyNames.all (fun name => (relySort? assignment name).isSome) = true := by
    apply List.all_eq_true.mpr
    intro name relies
    exact assignment_rely_sort_complete generated.snapshot.language vertex schema.declaration
      (schema_original_declaration schema) schema.position assignment assignmentMember assignmentOrigin name relies
  unfold Generated.modalParameters?
  rw [found]
  simp only [complete, dif_pos]
  exact ⟨_, rfl⟩

/-- Logical disabling or rejected equation admission can remove a catalogue;
every schema the generator actually admits has a complete computed former. -/
theorem generated_modal_parameters_complete (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language)
    (schema : Schema (generate snapshot language logic vertex).plan)
    (member : schema ∈ (generate snapshot language logic vertex).modalCatalogue) :
    ∃ parameters, (generate snapshot language logic vertex).modalParameters? schema = some parameters := by
  apply generated_schema_parameters_complete snapshot language logic vertex schema
  change schema ∈ (if _ then schemas _ else []) at member
  split at member
  · exact member
  · simp at member

end Mettapedia.OSLF.NativeTypes.Generation
