import Mettapedia.OSLF.NativeTypes.Semantics.Families
import Mettapedia.OSLF.NativeTypes.Semantics.Modal.Root
import Mettapedia.OSLF.NativeTypes.Generation.ModalFormation
import Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional

open Mettapedia.OSLF.Framework

/-!
# Native outputs of the actual generated formers

The modal compiler uses the computed rely coordinates and the original
formation check. A successful output retains those codes and their full
dependent native family. General focus membership is equation-class support;
the root-context theorem earns the comparison to the raw generated code.

Structural and propositional outputs use the independently checked primitive
equation interpretation of a native model. Their comparisons are theorems
about the existing generated codes, rather than fields supplied by a client.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Generated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Modal.Formation
open Mettapedia.OSLF.NativeTypes.Semantics.Families GSLTTypeSynthesis
open ModalHypercube (HSort)

structure ModalProduct {plan : GeneralExecutionAdmission.Plan} (schema : Schema plan) where
  parameters : ModalParameters schema
  supplied : ModalInputs schema (some parameters)

def ModalProduct.raw {plan : GeneralExecutionAdmission.Plan} {schema : Schema plan}
    (product : ModalProduct schema) :
    TypeCode plan schema.focusBound schema.focusCarrier product.parameters.output :=
  generatedFormer schema product.parameters.inputs product.parameters.output product.parameters.output
    product.supplied.1 product.supplied.2

def ModalProduct.output {plan : GeneralExecutionAdmission.Plan} {schema : Schema plan}
    (product : ModalProduct schema) : NativeOutput (Mettapedia.OSLF.NativeTypes.Semantics.Modal.focusTheory schema) :=
  modalOutput schema (relyMeaning product.supplied.1) (continuationMeaning product.supplied.2)

/-- The output family keeps the representative, actual equation path and
implementation of every typed rely request. -/
theorem modal_output_support {plan : GeneralExecutionAdmission.Plan} {schema : Schema plan}
    (product : ModalProduct schema) (term : Pattern) :
    product.output.predicate term ↔
      Nonempty (Mettapedia.OSLF.NativeTypes.Semantics.Modal.Family schema
        (relyMeaning product.supplied.1) (continuationMeaning product.supplied.2) term) :=
  (product.output.supportExact term).symm

/-- Away from a root context, the comparison is to equation-class support
of the raw generated code; it does not assert unproved context stability. -/
theorem modal_output_raw_comparison {plan : GeneralExecutionAdmission.Plan} {schema : Schema plan}
    (product : ModalProduct schema) (term : Pattern) :
    product.output.predicate term ↔
      ∃ representative, (Mettapedia.OSLF.NativeTypes.Semantics.Modal.focusTheory schema).Equiv term representative ∧
        product.raw.meaning representative := Iff.rfl

/-- Root context conversion acts on the complete program, so it constructs
the complete raw implementation at the requested representative. -/
theorem root_modal_output_raw_comparison {plan : GeneralExecutionAdmission.Plan} {schema : Schema plan}
    (product : ModalProduct schema) (term : Pattern)
    (root : schema.position = []) (bound : schema.focusBound = schema.bound)
    (carrier : schema.focusCarrier = schema.programCarrier) :
    product.output.predicate term ↔ product.raw.meaning term :=
  Mettapedia.OSLF.NativeTypes.Semantics.Modal.root_predicate_iff_inhabits root bound carrier

/-- Formation is performed by the original generator; a refused or
unresolved coordinate has no native modal output. -/
def _root_.Mettapedia.OSLF.NativeTypes.Generation.Generated.nativeModalFormer? (generated : Generated)
    (schema : Schema generated.plan)
    (inputs : ModalInputs schema (generated.modalParameters? schema)) : Option (ModalProduct schema) :=
  match parameters : generated.modalParameters? schema with
  | none => none
  | some profile =>
      if (generated.modalFormer? schema inputs).isSome then
        some ⟨profile, parameters ▸ inputs⟩
      else none

theorem native_modal_formation_exact {generated : Generated} {schema : Schema generated.plan}
    (inputs : ModalInputs schema (generated.modalParameters? schema)) :
    (generated.nativeModalFormer? schema inputs).isSome = (generated.modalFormer? schema inputs).isSome := by
  unfold Generated.nativeModalFormer?
  split
  · rename_i absent
    unfold Generated.modalFormer?
    split
    · split
      · rfl
      · rename_i profile present
        rw [absent] at present
        cases present
    · rfl
  · split <;> simp_all

theorem native_modal_refusal {generated : Generated} {schema : Schema generated.plan}
    (inputs : ModalInputs schema (generated.modalParameters? schema))
    (refused : generated.modalFormer? schema inputs = none) :
    generated.nativeModalFormer? schema inputs = none := by
  have empty := native_modal_formation_exact inputs
  rw [refused] at empty
  cases found : generated.nativeModalFormer? schema inputs with
  | none => rfl
  | some product => simp [found] at empty

/-- Every admitted catalogue entry forms through the native output compiler,
using the actual computed coordinates rather than a hand-supplied slot list. -/
theorem native_m_form (snapshot : GeneralExecutionAdmission.Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (selectedSnapshot snapshot language).language)
    (schema : Schema (generate snapshot language logic vertex).plan)
    (member : schema ∈ (generate snapshot language logic vertex).modalCatalogue)
    (accepted : (generate snapshot language logic vertex).equationAdmission = some true)
    (inputs : ModalInputs schema ((generate snapshot language logic vertex).modalParameters? schema)) :
    ∃ output, (generate snapshot language logic vertex).nativeModalFormer? schema inputs = some output := by
  obtain ⟨code, formed, _⟩ := generated_m_form snapshot language logic vertex schema member accepted inputs
  apply Option.isSome_iff_exists.mp
  rw [native_modal_formation_exact, formed]
  rfl

theorem native_modal_result_slot {generated : Generated} {schema : Schema generated.plan}
    (inputs : ModalInputs schema (generated.modalParameters? schema)) {product : ModalProduct schema}
    (formed : generated.nativeModalFormer? schema inputs = some product) :
    ∃ assignment ∈ generated.sortAssignments,
      assignment.family.origin = .modal schema.declaration.declarationIndex schema.position ∧
      product.parameters.output = assignment.output := by
  unfold Generated.nativeModalFormer? at formed
  split at formed
  · cases formed
  · rename_i parameters computed
    split at formed
    · cases formed
      obtain ⟨assignment, member, origin, result, _⟩ := modal_parameters_origins computed
      exact ⟨assignment, member, origin, result⟩
    · cases formed

/-- The retained input family builds exactly the raw former emitted by the
original generator, with its computed output coordinate. -/
theorem native_modal_retains_raw_former {generated : Generated} {schema : Schema generated.plan}
    (inputs : ModalInputs schema (generated.modalParameters? schema)) {product : ModalProduct schema}
    (formed : generated.nativeModalFormer? schema inputs = some product) :
    generated.modalFormer? schema inputs = some ⟨product.parameters.output, product.raw⟩ := by
  unfold Generated.nativeModalFormer? at formed
  split at formed
  · cases formed
  · rename_i parameters computed
    split at formed
    · rename_i present
      cases formed
      unfold Generated.modalFormer? at present ⊢
      split at present
      · rename_i admitted
        rw [if_pos admitted]
        split
        · rename_i absent
          rw [computed] at absent
          cases absent
        · rename_i actual found
          have equal : actual = parameters := Option.some.inj (found.symm.trans computed)
          subst actual
          rfl
      · cases present
    · cases formed

def structuralOutput {generated : Generated} (model : Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.Model generated)
    (bound : List TypeExpr) (index : Fin generated.snapshot.language.terms.length)
    (inputs : StructuralInputs generated bound index) :
    NativeOutput (Mettapedia.OSLF.NativeTypes.Semantics.Structural.theory generated bound
      (.base (structuralDeclaration generated index).category)) where
  predicate := Mettapedia.OSLF.NativeTypes.Semantics.Structural.predicate model bound index inputs
  Family := Mettapedia.OSLF.NativeTypes.Semantics.Structural.Family model bound index inputs
  supportExact := Mettapedia.OSLF.NativeTypes.Semantics.Structural.family_support model bound index inputs

theorem structural_output_generated_comparison {generated : Generated}
    (model : Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.Model generated)
    (equations : Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction.EquationsInterpreted model)
    (bound : List TypeExpr) (index : Fin generated.snapshot.language.terms.length)
    (inputs : StructuralInputs generated bound index) (term : Pattern) :
    (structuralOutput model bound index inputs).predicate term ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (model bound) index inputs).meaning term :=
  (Mettapedia.OSLF.NativeTypes.Semantics.Structural.generated_native_comparison model equations bound index inputs term).symm

def propositionalOutput {generated : Generated} {model : Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.Model generated}
    (equations : Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction.EquationsInterpreted model)
    {bound : List TypeExpr} {leaves : Mettapedia.OSLF.NativeTypes.SortProfiles.Source.LeafCodes generated bound}
    (leafEquations : Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.LeafEquationsInterpreted bound leaves)
    {carrier : TypeExpr} {sort : HSort}
    (compiled : Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.Output model bound leaves carrier sort) :
    NativeOutput (Mettapedia.OSLF.NativeTypes.Semantics.Structural.theory generated bound carrier) where
  predicate := compiled.predicate equations
  Family := Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.Family model bound leaves carrier sort
    compiled.classified.expression
  supportExact := Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.family_support equations leafEquations
    compiled.classified.formation

theorem propositional_output_generated_comparison {generated : Generated}
    {model : Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.Model generated}
    (equations : Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction.EquationsInterpreted model)
    {bound : List TypeExpr} {leaves : Mettapedia.OSLF.NativeTypes.SortProfiles.Source.LeafCodes generated bound}
    (leafEquations : Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.LeafEquationsInterpreted bound leaves)
    {carrier : TypeExpr} {sort : HSort}
    (compiled : Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.Output model bound leaves carrier sort)
    (term : Pattern) :
    (propositionalOutput equations leafEquations compiled).predicate term ↔
      compiled.classified.code.meaning term :=
  (Mettapedia.OSLF.NativeTypes.Semantics.Structural.Propositional.generated_native_comparison equations leafEquations compiled term).symm

end Mettapedia.OSLF.NativeTypes.Semantics.Generated
