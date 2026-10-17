import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.CurriedInterfaces
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingModalDiagram
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.AuthoredClassifiers
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ResponseSemantics
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.BindingResponseTargets

/-!
# All indexed observations from original binding receipts

Every shared index is located by its authored name among the matched
captures. Deterministic scoped and sorted metadata makes that location's
parameter equal to the original generated parameter. No new admissibility
predicate or site list is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.BindingObservations

open _root_.CategoryTheory Opposite
open Mettapedia.OSLF.NativeTypes.Modal
open Mettapedia.OSLF.MeTTaIL GeneralExecutionAdmission
open CurriedBindingLanguage
open NativeBindingLocalValues

variable {plan : Plan}

/-- Authored declaration lookups determine the complete metadata of a slot. -/
theorem slot_name_injective {schema : Rules.Schema plan} :
    Function.Injective (fun slot : NativeEventParameters.Slot schema => slot.name) := by
  rintro ⟨name, dependencies, expected, declared, sorted⟩ ⟨name', dependencies', expected', declared', sorted'⟩ same
  dsimp only at same
  subst name'
  have dependenciesEq := Option.some.inj (declared.symm.trans declared')
  have expectedEq := Option.some.inj (sorted.symm.trans sorted')
  cases dependenciesEq
  cases expectedEq
  rfl

/-- A decoded parameter's carrier is likewise determined by its authored name. -/
theorem parameter_name_injective {schema : Rules.Schema plan} :
    Function.Injective (fun parameter : NativeModalParameters.Parameter schema => parameter.slot.name) := by
  rintro ⟨slot, carrier, decoded⟩ ⟨slot', carrier', decoded'⟩ same
  have slots := slot_name_injective same
  dsimp only at slots
  subst slot'
  have carriers := Option.some.inj (decoded.symm.trans decoded')
  cases carriers
  rfl

variable (installed : Joined.Installed) (index : installed.Index)

abbrev operational := installed.indexed.operational
abbrev header := CurriedInterfaces.header installed.indexed index
abbrev indexedHeader := installed.indexed.headers[index]
abbrev planOf := BindingPipeline.plan (operational installed).generated
abbrev admitted := installed.semantic.modalMeanings (indexedHeader installed index).origin
abbrev decoded := AuthoredBindingNativeModel.header_decoded (operational installed) (indexedHeader installed index).origin
abbrev sort := NativeBindingModalDiagram.programSort (admitted installed index)
abbrev ready := (NativeOperationalProfile.check_exact _).mp installed.semantic.operationalMeaning

noncomputable def matchedIndex (position : Fin (indexedHeader installed index).indices.length) :
    Fin (header installed index).matched.length :=
  let names := (header installed index).matched.map (fun parameter => parameter.slot.name)
  let name := (indexedHeader installed index).indices[position].slot.name
  have member : name ∈ names := by
    dsimp only [names]
    rw [(NativeModalHeaders.decode_parameters _ (decoded installed index)).2]
    exact (indexedHeader installed index).indicesMatched _ (List.getElem_mem position.isLt)
  ⟨names.idxOf name, by simpa only [names, List.length_map] using List.idxOf_lt_length_iff.mpr member⟩

theorem matchedIndex_name (position : Fin (indexedHeader installed index).indices.length) :
    (header installed index).matched[matchedIndex installed index position].slot.name =
      (indexedHeader installed index).indices[position].slot.name := by
  let names := (header installed index).matched.map (fun parameter => parameter.slot.name)
  have member : (indexedHeader installed index).indices[position].slot.name ∈ names := by
    dsimp only [names]
    rw [(NativeModalHeaders.decode_parameters _ (decoded installed index)).2]
    exact (indexedHeader installed index).indicesMatched _ (List.getElem_mem position.isLt)
  have selected := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr member)
  simpa only [names, List.getElem_map, matchedIndex, Fin.getElem_fin] using selected

theorem matchedIndex_parameter (position : Fin (indexedHeader installed index).indices.length) :
    (header installed index).matched[matchedIndex installed index position] =
      (indexedHeader installed index).indices[position] :=
  parameter_name_injective (matchedIndex_name installed index position)

/-- Shared-index semantic admission is inherited from its matched capture,
not provided by the caller. -/
noncomputable def indexShape (position : Fin (indexedHeader installed index).indices.length) :
    Shape (indexedHeader installed index).indices[position].slot.dependencies
      (indexedHeader installed index).indices[position].slot.expected
      (indexedHeader installed index).indices[position].carrier := by
  have shape := (admitted installed index).matched (matchedIndex installed index position)
  rw [matchedIndex_parameter installed index position] at shape
  exact shape

abbrev events := NativeBindingSchemaInputs.events (header installed index) (sort installed index)
  installed.semantic.freeEmpty (ready installed)

noncomputable def focus : events installed index ⟶
    meaning (CurriedInterfaces.interface installed.indexed index).focus :=
  NativeBindingModalDiagram.focus (header installed index) (decoded installed index) (admitted installed index)
    installed.semantic.freeEmpty (ready installed) (operational installed).nativeMeaning_admitted
    (operational installed).distinctLabels

noncomputable def target : events installed index ⟶ meaning (header installed index).program :=
  NativeBindingModalDiagram.target (header installed index) (admitted installed index)
    installed.semantic.freeEmpty (ready installed) (operational installed).nativeMeaning_admitted
    (operational installed).distinctLabels

noncomputable def rely (position : Fin (header installed index).rely.length) :
    events installed index ⟶ meaning (header installed index).rely[position].carrier :=
  NativeBindingModalDiagram.rely (header installed index) (decoded installed index) (admitted installed index)
    installed.semantic.freeEmpty (ready installed) (operational installed).nativeMeaning_admitted
    (operational installed).distinctLabels position

/-- A shared capture is read from the original event's ordered matched map. -/
noncomputable def shared (position : Fin (indexedHeader installed index).indices.length) :
    events installed index ⟶ meaning (indexedHeader installed index).indices[position].carrier := by
  have projection := NativeBindingModalDiagram.matched (header installed index) (decoded installed index)
    (admitted installed index) installed.semantic.freeEmpty (ready installed)
    (operational installed).nativeMeaning_admitted (operational installed).distinctLabels
    (matchedIndex installed index position)
  rw [matchedIndex_parameter installed index position] at projection
  exact projection


abbrev interface := CurriedInterfaces.interface installed.indexed index

def indexPosition (position : Fin (interface installed index).indices.length) :
    Fin (indexedHeader installed index).indices.length :=
  ⟨position.val, by
    have lengths := installed.indexed.interfaces_source index
    simpa only [interface, CurriedInterfaces.interface, lengths, SourceInterfaces.Header.interface,
      List.length_ofFn] using position.isLt⟩

theorem indexCarrier (position : Fin (interface installed index).indices.length) :
    (interface installed index).indices[position].1 =
      (indexedHeader installed index).indices[indexPosition installed index position].carrier := by
  simp only [interface, CurriedInterfaces.interface, installed.indexed.interfaces_source,
    SourceInterfaces.Header.interface]
  change ((List.ofFn fun named : Fin (indexedHeader installed index).indices.length =>
    ((indexedHeader installed index).indices[named].carrier,
      (indexedHeader installed index).indexSort installed.indexed.vertex named)).get
        ⟨position.val, by simpa only [List.length_ofFn, indexPosition] using (indexPosition installed index position).isLt⟩).1 = _
  rw [List.get_ofFn]
  rfl

def relyPosition (position : Fin (interface installed index).relies.length) :
    Fin (header installed index).rely.length :=
  ⟨position.val, by
    have lengths := installed.indexed.interfaces_source index
    simpa only [interface, CurriedInterfaces.interface, lengths, SourceInterfaces.Header.interface,
      List.length_ofFn] using position.isLt⟩

theorem relyCarrier (position : Fin (interface installed index).relies.length) :
    (interface installed index).relies[position].1 =
      (header installed index).rely[relyPosition installed index position].carrier := by
  simp only [interface, CurriedInterfaces.interface, installed.indexed.interfaces_source,
    SourceInterfaces.Header.interface]
  change ((List.ofFn fun named : Fin (header installed index).rely.length =>
    ((header installed index).rely[named].carrier,
      (indexedHeader installed index).relySort installed.indexed.vertex named)).get
        ⟨position.val, by simpa only [List.length_ofFn, relyPosition] using (relyPosition installed index position).isLt⟩).1 = _
  rw [List.get_ofFn]
  rfl

/-- The complete independent observation diagram is generated from the
installed source receipts and the language's canonical scoped slot metadata. -/
noncomputable def observations : ResponseSemantics.Observations
    (AuthoredClassifiers.operational installed.indexed) (interface installed index) where
  events := events installed index
  focus := focus installed index
  indices position := by
    rw [indexCarrier]
    exact shared installed index (indexPosition installed index position)
  relies position := by
    rw [relyCarrier]
    exact rely installed index (relyPosition installed index position)
  target := by
    change events installed index ⟶ meaning (installed.indexed.interfaces index).target
    rw [installed.indexed.interfaces_source]
    exact target installed index


/-- The ambient function reifies the original raw local focus, with its
ordered binder prefix retained in the earned body comparison. -/
theorem focus_reconstructs (X : (Worlds (NativeCubeProfile.language (operational installed)))ᵒᵖ)
    (frame : (events installed index).obj X) :
    CurriedBindingLanguage.wrap (admitted installed index).focus.domains
      (CurriedBindingLanguage.toPattern
        ((NativeBindingScopedBodies.nativeBodyIso (header installed index).focusArgument
          (admitted installed index).focus.spine).hom.app X
            ((focus installed index).app X frame))) =
      CurriedBindingLanguage.wrap (admitted installed index).focus.scope.reverse frame.focus := by
  exact NativeBindingLocalValues.nativeMap_source (admitted installed index).focus
    (operational installed).nativeMeaning_admitted (operational installed).distinctLabels X
    ((NativeBindingModalDiagram.focusInput (header installed index) (sort installed index)).app X
      ((NativeBindingSchemaInputs.observe (header installed index) (decoded installed index)
        (sort installed index) installed.semantic.freeEmpty (ready installed)).app X frame))

/-- Every operational target in the semantic diagram is the complete
selected receipt's actual scoped RHS, rather than an arbitrary successor. -/
theorem target_payload (X : (Worlds (NativeCubeProfile.language (operational installed)))ᵒᵖ)
    (frame : (events installed index).obj X) :
    CurriedBindingLanguage.toPattern
      ((NativeBindingModalDiagram.programIso (admitted installed index)).hom.app X
        ((target installed index).app X frame)) = frame.point.val.receipt.target :=
  NativeBindingModalDiagram.target_read (header installed index) (admitted installed index)
    installed.semantic.freeEmpty (ready installed) (operational installed).nativeMeaning_admitted
    (operational installed).distinctLabels X frame

theorem specified_rhs (X : (Worlds (NativeCubeProfile.language (operational installed)))ᵒᵖ)
    (frame : (events installed index).obj X) :
    ScopedRuleMatching.reductWith? (ScopedReflectiveExecution.binderOperation
      (GeneralPlanEnvironment.environment (planOf installed)).reflection
      (installed.indexed.schema index).declaration.rule)
      (installed.indexed.schema index).declaration.rule
      (installed.indexed.schema index).declaration.binding.spec X.unop.context.length
      frame.point.val.receipt.completed = some frame.point.val.receipt.target :=
  BindingResponses.specified_rhs (header installed index) (sort installed index)
    installed.semantic.freeEmpty (ready installed) frame

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.BindingObservations
