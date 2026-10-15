import Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeHeaderRanks
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeExtension
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeCertificates

/-!
# Cube enrichment from actual installed native declarations

Every former is an installed constructor or an installed typed modal
occurrence. Carriers and ordered slots are read from those headers. A modal
slot assignment is transported from its authored occurrence by a checked
declaration/address/name comparison; a missing comparison refuses the join.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeCubeProfile

open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open BindingPipeline

deriving instance Encodable for NativeSignature.Carrier

variable (installed : BindingPipeline.Installed)

abbrev language := (plan installed.generated).snapshot.language

theorem language_preserved : language installed = installed.generated.snapshot.language := by
  unfold language plan
  rw [Mettapedia.OSLF.MeTTaIL.StructuralDescent.Plan.snapshot_preserved]
  rfl

def sourceVertex : SortProfiles.Derived.CubeVertex (language installed) :=
  cast (congrArg SortProfiles.Derived.CubeVertex (language_preserved installed).symm)
    installed.generated.vertex

abbrev Former := installed.declarations.Constructor ⊕ Fin installed.modal.length

abbrev signature : CubeEnrichment.Signature where
  Carrier := NativeSignature.Carrier (language installed)
  Former := Former installed
  arity := fun former => match former with
    | .inl constructor => (installed.declarations.parameters constructor).length
    | .inr index => installed.modal[index].rely.length
  input := fun former position => match former with
    | .inl constructor => (installed.declarations.parameters constructor)[position]
    | .inr index => installed.modal[index].rely[position].carrier
  output := fun former => match former with
    | .inl constructor => installed.declarations.result constructor
    | .inr index => installed.modal[index].program

theorem constructor_slots (constructor : installed.declarations.Constructor) :
    (signature installed).arity (.inl constructor) =
      (installed.declarations.parameters constructor).length := rfl

theorem modal_slots (index : Fin installed.modal.length) :
    (signature installed).arity (.inr index) = installed.modal[index].rely.length := rfl

def rawIndex? (index : Fin installed.modal.length) :
    Option (Fin (Occurrences.generate (language installed)).length) :=
  let schema := Modal.NativeEventDeclarations.schema (plan installed.generated) installed.modal[index].origin
  (List.finRange (Occurrences.generate (language installed)).length).find? fun position =>
    let site := (Occurrences.generate (language installed))[position]
    site.declaration == schema.declaration.declarationIndex && site.position == schema.position &&
      decide (site.relyNames.Perm
        (installed.modal[index].rely.map (fun parameter => parameter.slot.name)))

def MatchingOccurrence (index : Fin installed.modal.length)
    (position : Fin (Occurrences.generate (language installed)).length) : Prop :=
  let schema := Modal.NativeEventDeclarations.schema (plan installed.generated) installed.modal[index].origin
  let site := (Occurrences.generate (language installed))[position]
  site.declaration = schema.declaration.declarationIndex ∧ site.position = schema.position ∧
    site.relyNames.Perm (installed.modal[index].rely.map (fun parameter => parameter.slot.name))

theorem rawIndex?_sound {index : Fin installed.modal.length}
    {position : Fin (Occurrences.generate (language installed)).length}
    (found : rawIndex? installed index = some position) : MatchingOccurrence installed index position := by
  have selected := List.find?_some found
  simpa only [MatchingOccurrence, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc] using selected

/-- A rely input follows its authored name even when address traversal and
zipper traversal order the surrounding components differently. -/
def relyCoordinate (index : Fin installed.modal.length)
    (position : Fin (Occurrences.generate (language installed)).length)
    (matching : MatchingOccurrence installed index position)
    (input : Fin installed.modal[index].rely.length) :
    Fin (SortProfiles.Slots.modalFamily (language installed)
      (Occurrences.generate (language installed))[position]).inputs.length :=
  let names := (Occurrences.generate (language installed))[position].relyNames
  let name := installed.modal[index].rely[input].slot.name
  have member : name ∈ names := matching.2.2.mem_iff.mpr
    (List.mem_map.mpr ⟨installed.modal[index].rely[input], List.getElem_mem input.isLt, rfl⟩)
  ⟨names.idxOf name, by
    simpa only [SortProfiles.Slots.modalFamily, List.length_map] using
      List.idxOf_lt_length_iff.mpr member⟩

private theorem modalInput_name (source : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (site : Occurrences.Site)
    (coordinate : Fin (SortProfiles.Slots.modalFamily source site).inputs.length) :
    (SortProfiles.Slots.modalFamily source site).inputs[coordinate].1 =
      site.relyNames[coordinate.val]'(by
        simpa only [SortProfiles.Slots.modalFamily, List.length_map] using coordinate.isLt) := by
  exact congrArg Prod.fst (List.getElem_map ..)

theorem relyCoordinate_name (index : Fin installed.modal.length)
    (position : Fin (Occurrences.generate (language installed)).length)
    (matching : MatchingOccurrence installed index position)
    (input : Fin installed.modal[index].rely.length) :
    (SortProfiles.Slots.modalFamily (language installed)
      (Occurrences.generate (language installed))[position]).inputs[
        relyCoordinate installed index position matching input].1 =
      installed.modal[index].rely[input].slot.name := by
  rw [modalInput_name]
  dsimp only [relyCoordinate]
  exact List.getElem_idxOf _

def slots? : (former : Former installed) →
    Option (Fin ((signature installed).arity former + 1) → HSort)
  | .inl constructor =>
      let declaration := (language installed).terms[(installed.declarations.origin constructor).val]
      let operation := SortProfiles.Derived.constructorOperation (language installed) declaration
        (List.getElem_mem (installed.declarations.origin constructor).isLt)
      if lengths : (installed.declarations.parameters constructor).length = declaration.params.length then
        some (Fin.lastCases
          (SortProfiles.Coherence.output (sourceVertex installed).2 operation)
          (fun position => SortProfiles.Coherence.input (sourceVertex installed).2 operation
            ⟨position.val, by
              change position.val < declaration.params.length
              rw [← lengths]
              exact position.isLt⟩))
      else none
  | .inr index =>
      match found : rawIndex? installed index with
      | none => none
      | some position =>
          let family := SortProfiles.Slots.modalFamily (language installed)
            (Occurrences.generate (language installed))[position]
          some (Fin.lastCases
            ((sourceVertex installed).1 ⟨position, Fin.last family.inputs.length⟩)
            (fun input => (sourceVertex installed).1
              ⟨position, (relyCoordinate installed index position
                (rawIndex?_sound installed found) input).castSucc⟩))

theorem modal_input_read {index : Fin installed.modal.length}
    {position : Fin (Occurrences.generate (language installed)).length}
    (found : rawIndex? installed index = some position)
    {profile : Fin ((signature installed).arity (.inr index) + 1) → HSort}
    (decoded : slots? installed (.inr index) = some profile)
    (input : Fin installed.modal[index].rely.length) :
    profile input.castSucc = (sourceVertex installed).1
      ⟨position, (relyCoordinate installed index position
        (rawIndex?_sound installed found) input).castSucc⟩ := by
  simp only [slots?] at decoded
  split at decoded
  · cases decoded
  · rename_i actual origin
    cases Option.some.inj (origin.symm.trans found)
    cases Option.some.inj decoded
    exact Fin.lastCases_castSucc input

theorem modal_output_read {index : Fin installed.modal.length}
    {position : Fin (Occurrences.generate (language installed)).length}
    (found : rawIndex? installed index = some position)
    {profile : Fin ((signature installed).arity (.inr index) + 1) → HSort}
    (decoded : slots? installed (.inr index) = some profile) :
    profile (Fin.last installed.modal[index].rely.length) = (sourceVertex installed).1
      ⟨position, Fin.last (SortProfiles.Slots.modalFamily (language installed)
        (Occurrences.generate (language installed))[position]).inputs.length⟩ := by
  simp only [slots?] at decoded
  split at decoded
  · cases decoded
  · rename_i actual origin
    cases Option.some.inj (origin.symm.trans found)
    cases Option.some.inj decoded
    exact Fin.lastCases_last

/-- Finite admission checks every actual former. No missing slot receives an
implicit default vertex. -/
def vertex? : Option (CubeEnrichment.Vertex (signature installed)) :=
  if complete : ∀ former, (slots? installed former).isSome then
    some (fun former => (slots? installed former).get (complete former))
  else none

theorem vertex?_sound {vertex : CubeEnrichment.Vertex (signature installed)}
    (decoded : vertex? installed = some vertex) :
    ∀ former, slots? installed former = some (vertex former) := by
  unfold vertex? at decoded
  split at decoded
  · cases Option.some.inj decoded
    intro former
    exact (Option.some_get _).symm
  · cases decoded

def sourceCarriers : CubeNativeExtension.SourceCarriers installed.signature (signature installed) 4 where
  type carrier := NativeModalSignature.authoredType (plan installed.generated) installed.declarations installed.modal carrier 0
  formed carrier := NativeModalSignature.authoredFormed (plan installed.generated) installed.declarations installed.modal
    carrier .nil (NativeModalSignature.emptyFormed (plan installed.generated) installed.declarations installed.modal)
  before carrier := NativeModalSignature.authoredFormed_before (plan installed.generated) installed.declarations installed.modal
    carrier .nil _ 4 (by decide)
    (NativeModalSignature.emptyFormed_before (plan installed.generated) installed.declarations installed.modal 4)

def enrichedSignature (vertex : CubeEnrichment.Vertex (signature installed)) :=
  CubeNativeExtension.signature installed.signature vertex 4 (sourceCarriers installed) (by decide)

def enrichedFormation (vertex : CubeEnrichment.Vertex (signature installed)) :=
  CubeNativeExtension.computedHeaders installed.signature vertex 4 (sourceCarriers installed)
    (by decide) installed.formation

end Mettapedia.OSLF.NativeTypes.Generation.NativeCubeProfile
