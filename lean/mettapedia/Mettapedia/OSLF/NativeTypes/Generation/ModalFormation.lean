import Mettapedia.OSLF.NativeTypes.Generation.ModalCoverage

open Mettapedia.OSLF.Framework

/-!+# Formation of every admitted generated modal former

Formation precedes any inhabitant judgment. Every schema in the computed
catalogue has all its named input coordinates and a result coordinate. Once
the equation profile is accepted and typed input codes are supplied, the
generator actually returns the modal code at that result coordinate.

The code's carrier bound is earned by its specified-contractum semantics;
formation does not require a program to inhabit it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

universe u v

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.SortProfiles.Derived (CubeVertex)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Slots (Origin)
open ModalHypercube (HSort)

private theorem transport_roundtrip {α : Sort u} (family : α → Sort v)
    {first second : α} (equal : first = second) (value : family second) :
    equal ▸ (equal.symm ▸ value) = value := by
  cases equal
  rfl

theorem generated_modal_catalogue_enabled (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language)
    (schema : Schema (generate snapshot language logic vertex).plan)
    (member : schema ∈ (generate snapshot language logic vertex).modalCatalogue) :
    logic.core.modal = true := by
  change schema ∈ (if _ then schemas _ else []) at member
  split at member
  · rename_i enabled
    simp only [Bool.and_eq_true] at enabled
    exact enabled.2
  · simp at member

/-- M-FORM is an actual successful generator result for every admitted
authored occurrence, without an assumed modal inhabitant. -/
theorem generated_m_form (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot language).language)
    (schema : Schema (generate snapshot language logic vertex).plan)
    (member : schema ∈ (generate snapshot language logic vertex).modalCatalogue)
    (accepted : (generate snapshot language logic vertex).equationAdmission = some true)
    (inputs : ModalInputs schema ((generate snapshot language logic vertex).modalParameters? schema)) :
    ∃ code : Σ sort : HSort,
      TypeCode (generate snapshot language logic vertex).plan schema.focusBound schema.focusCarrier sort,
      (generate snapshot language logic vertex).modalFormer? schema inputs = some code ∧
      ∃ assignment ∈ (generate snapshot language logic vertex).sortAssignments,
        assignment.family.origin = .modal schema.declaration.declarationIndex schema.position ∧
        code.1 = assignment.output := by
  have enabled := generated_modal_catalogue_enabled snapshot language logic vertex schema member
  change (generate snapshot language logic vertex).logicFragment.core.modal = true at enabled
  obtain ⟨parameters, computed⟩ :=
    generated_modal_parameters_complete snapshot language logic vertex schema member
  have formed : ((generate snapshot language logic vertex).modalFormer? schema inputs).isSome = true := by
    unfold Generated.modalFormer?
    rw [if_pos ⟨accepted, enabled,
      generated_schema_admitted member⟩]
    split
    · rename_i absent
      rw [computed] at absent
      cases absent
    · rfl
  obtain ⟨code, output⟩ := Option.isSome_iff_exists.mp formed
  exact ⟨code, output, generated_modal_result_slot inputs output⟩

/-- The universe of the continuation and of the formed modal predicate is
the computed output coordinate, not a separately supplied focus sort. -/
theorem generated_modal_same_output_sort {generated : Generated}
    {schema : Schema generated.plan}
    (member : schema ∈ generated.modalCatalogue)
    (accepted : generated.equationAdmission = some true)
    (enabled : generated.logicFragment.core.modal = true)
    (parameters : ModalParameters schema)
    (computed : generated.modalParameters? schema = some parameters)
    (inputs : ModalInputs schema (some parameters)) :
    generated.modalFormer? schema (computed.symm ▸ inputs) =
      some ⟨parameters.output,
        Mettapedia.OSLF.NativeTypes.Modal.Formation.generatedFormer schema parameters.inputs
          parameters.output parameters.output inputs.1 inputs.2⟩ := by
  unfold Generated.modalFormer?
  rw [if_pos ⟨accepted, enabled, generated_schema_admitted member⟩]
  split
  · rename_i absent
    rw [computed] at absent
    cases absent
  · rename_i profile actual
    have equal : profile = parameters := Option.some.inj (actual.symm.trans computed)
    subst profile
    rw [transport_roundtrip (ModalInputs schema) computed inputs]

end Mettapedia.OSLF.NativeTypes.Generation
