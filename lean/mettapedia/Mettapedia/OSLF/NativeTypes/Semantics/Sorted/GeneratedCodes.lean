import Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes

open Mettapedia.OSLF.Framework

/-!
# Sort-relative interpretation of code-bearing generator results

The executable generator checks its actual authored schema and universe
coordinates before constructing the classified modal expression. Native input
codes are restricted to a chosen model's sort subobjects in their complete
dependency contexts. A classified output retains that expression, its kind
proof and the actual response family beside its sort-relative interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.NativeTypes.Generation (Generated ModalParameters ModalInputs)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema TypeCode Evidence TypedRequest)
open Mettapedia.OSLF.NativeTypes.Modal.Formation (relyMeaning continuationMeaning)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source (ClassifiedModalCode ClassifiedModalInputs nativeModalInputs)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes
open ModalHypercube (HSort)

def restrictInputs {generated : Generated} {schema : Schema generated.plan} (model : Model generated) :
    {parameters : Option (ModalParameters schema)} → ModalInputs schema parameters → ModalInputs schema parameters
  | none, _ => ()
  | some _, inputs => ⟨restrictRelyCodes model inputs.1, restrictContinuations model inputs.2⟩

theorem classified_inputs_transport {generated : Generated} {schema : Schema generated.plan}
    (model : Model generated) {first second : Option (ModalParameters schema)}
    (equal : first = second) (inputs : ModalInputs schema first) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Source.liftModalInputs (restrictInputs model (equal ▸ inputs)) =
      equal ▸ Mettapedia.OSLF.NativeTypes.SortProfiles.Source.liftModalInputs (restrictInputs model inputs) := by
  cases equal
  rfl

structure ModalOutput (generated : Generated) (model : Model generated)
    (schema : Schema generated.plan) (sort : HSort) where
  formed : ClassifiedModalCode generated schema sort
  code : TypeCode generated.plan schema.focusBound schema.focusCarrier sort
  readout : ∀ term, code.meaning term ↔
    (model schema.focusBound).sortDomain schema.focusCarrier sort term ∧ formed.code.meaning term
  continuationSorted : ∀ assignment target,
    ((nativeModalInputs formed.inputs).2 assignment).meaning target →
      (model schema.bound).sortDomain schema.programCarrier formed.parameters.output target

def form {generated : Generated} {schema : Schema generated.plan} (model : Model generated)
    (parameters : ModalParameters schema) (computed : generated.modalParameters? schema = some parameters)
    (inputs : ModalInputs schema (some parameters)) : ModalOutput generated model schema parameters.output where
  formed := Mettapedia.OSLF.NativeTypes.SortProfiles.Source.classifiedModalCode parameters computed
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.liftModalInputs (restrictInputs model inputs))
  code := restrictCode (model schema.focusBound)
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.classifiedModalCode parameters computed
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.liftModalInputs (restrictInputs model inputs))).code
  readout _ := Iff.rfl
  continuationSorted _ _ inhabited := inhabited.1

def compile (generated : Generated) (model : Model generated) (schema : Schema generated.plan)
    (inputs : ModalInputs schema (generated.modalParameters? schema)) :
    Option (Σ sort : HSort, ModalOutput generated model schema sort) :=
  if generated.equationAdmission = some true ∧ generated.logicFragment.core.modal = true ∧
      generated.schemaAdmitted? schema = true then
    match computed : generated.modalParameters? schema with
    | none => none
    | some parameters => some ⟨parameters.output, form model parameters computed (computed ▸ inputs)⟩
  else none

/-- The classified expression is formed from the original generated family;
it is retained rather than replaced by the chosen semantic subobject. -/
theorem compiled_output_retains_formed_code {generated : Generated} {model : Model generated}
    {schema : Schema generated.plan} (inputs : ModalInputs schema (generated.modalParameters? schema))
    {output : Σ sort : HSort, ModalOutput generated model schema sort}
    (compiled : compile generated model schema inputs = some output) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Source.compileEquationModalNativeCode generated schema
        (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.liftModalInputs (restrictInputs model inputs)) =
      some ⟨output.1, output.2.formed⟩ := by
  unfold compile at compiled
  split at compiled
  · rename_i enabled
    unfold Mettapedia.OSLF.NativeTypes.SortProfiles.Source.compileEquationModalNativeCode
    rw [if_pos enabled]
    split at compiled
    · cases compiled
    · rename_i parameters computed
      cases compiled
      split
      · rename_i missing
        rw [computed] at missing
        cases missing
      · rename_i actualParameters actual
        have agrees : actualParameters = parameters := Option.some.inj (actual.symm.trans computed)
        subst actualParameters
        change _ = some (⟨parameters.output, Mettapedia.OSLF.NativeTypes.SortProfiles.Source.classifiedModalCode parameters computed
          (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.liftModalInputs (restrictInputs model (computed ▸ inputs)))⟩ :
          Σ actualSort : HSort, ClassifiedModalCode generated schema actualSort)
        rw [classified_inputs_transport model computed inputs]
  · cases compiled

theorem generated_formation_complete
    (snapshot : GeneralExecutionAdmission.Snapshot) (fragment : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot fragment).language)
    (model : Model (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex))
    (schema : Schema (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex).plan)
    (member : schema ∈ (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex).modalCatalogue)
    (accepted : (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex).equationAdmission = some true)
    (inputs : ModalInputs schema ((Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex).modalParameters? schema)) :
    ∃ output, compile (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex) model schema inputs = some output ∧
      output.2.formed.expression ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Source.ModalUniverse
        (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex) schema output.1 := by
  have enabled := Mettapedia.OSLF.NativeTypes.Generation.generated_modal_catalogue_enabled snapshot fragment logic vertex schema member
  change (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex).logicFragment.core.modal = true at enabled
  obtain ⟨parameters, computed⟩ :=
    Mettapedia.OSLF.NativeTypes.Generation.generated_modal_parameters_complete snapshot fragment logic vertex schema member
  have present : (compile (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot fragment logic vertex) model schema inputs).isSome = true := by
    unfold compile
    rw [if_pos ⟨accepted, enabled, Mettapedia.OSLF.NativeTypes.Generation.generated_schema_admitted member⟩]
    split
    · rename_i missing
      rw [computed] at missing
      cases missing
    · rfl
  obtain ⟨output, compiled⟩ := Option.isSome_iff_exists.mp present
  exact ⟨output, compiled, output.2.formed.universeFormation⟩

theorem inhabitant_is_in_requested_subobject {generated : Generated} {model : Model generated}
    {schema : Schema generated.plan} {sort : HSort} (output : ModalOutput generated model schema sort)
    {term : Pattern} (inhabited : output.code.meaning term) :
    (model schema.focusBound).sortDomain schema.focusCarrier sort term :=
  ((output.readout term).mp inhabited).1

/-- M-STEP and M-ELIM for the actual interpreted output use the native
dependent family. The chosen model only restricts its certificates; it cannot
supply an execution or choose a different right-hand side. -/
theorem inhabitant_native_elimination {generated : Generated} {model : Model generated}
    {schema : Schema generated.plan} {sort : HSort} (output : ModalOutput generated model schema sort)
    {term : Pattern} (inhabited : output.code.meaning term) :
    ∃ implementation : Evidence schema (relyMeaning (nativeModalInputs output.formed.inputs).1)
        (continuationMeaning (nativeModalInputs output.formed.inputs).2) term,
      ∀ assignment (request : TypedRequest schema (relyMeaning (nativeModalInputs output.formed.inputs).1)
        implementation.anchor assignment),
        let result := Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.eliminate implementation assignment request
        schema.fill? assignment term = some result.source ∧
          schema.rhs? assignment = some result.native.2.1 ∧
          (GeneralOccurrenceSemantics.gslt generated.plan schema.bound schema.programCarrier).Step
            result.source result.native.2.1 ∧
          (model schema.bound).sortDomain schema.programCarrier sort result.native.2.1 ∧
          ((nativeModalInputs output.formed.inputs).2 assignment).meaning result.native.2.1 ∧
          result.native.1.val = (implementation.respond assignment request).receipt := by
  have raw := ((output.readout term).mp inhabited).2
  have supported := (output.formed.meaningComparison term).mp raw
  obtain ⟨implementation⟩ := supported
  refine ⟨implementation, ?_⟩
  intro assignment request
  let result := Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.eliminate implementation assignment request
  have contract := Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.elimination_contract result
  have certificate := result.native.2.2.2.down
  have sorted := output.continuationSorted assignment result.native.2.1 certificate
  have requestedSort : (model schema.bound).sortDomain schema.programCarrier sort result.native.2.1 :=
    (congrArg (fun actualSort =>
      (model schema.bound).sortDomain schema.programCarrier actualSort result.native.2.1)
      output.formed.resultSlot).mpr sorted
  exact ⟨contract.1, contract.2.1, contract.2.2.1, requestedSort, certificate, rfl⟩

end Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes
