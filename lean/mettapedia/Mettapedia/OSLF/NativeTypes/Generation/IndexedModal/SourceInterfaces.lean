import Mettapedia.OSLF.NativeTypes.Generation.NativeCubeProfile
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Parameters
import Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph

/-!
# Complete modal interfaces from installed authored occurrences

Shared variables are decoded in the original scoped rule. Profile coordinates
are read by their authored names, with the target coordinate retained. The
raw focus carrier and its binder context remain distinct from the curried
focus projection used by operational receipts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SourceInterfaces

open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.SortProfiles
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

variable (installed : BindingPipeline.Installed)

abbrev language := NativeCubeProfile.language installed

abbrev schema (origin : Fin installed.modal.length) :=
  Modal.NativeEventDeclarations.schema (BindingPipeline.plan installed.generated) installed.modal[origin].origin

structure Header where
  origin : Fin installed.modal.length
  site : Fin (Occurrences.generate (language installed)).length
  matching : NativeCubeProfile.MatchingOccurrence installed origin site
  indices : List (NativeModalParameters.Parameter (schema installed origin))
  decoded : NativeModalParameters.decodeAll?
    (schema installed origin)
    (DisplayedGraph.indexNames (Occurrences.generate (language installed))[site]) = some indices
  indicesMatched : ∀ parameter ∈ indices, parameter.slot.name ∈ (schema installed origin).matchedNames

def decode? (origin : Fin installed.modal.length) : Option (Header installed) :=
  match found : NativeCubeProfile.rawIndex? installed origin with
  | none => none
  | some site =>
      match decoded : NativeModalParameters.decodeAll?
        (schema installed origin)
        (DisplayedGraph.indexNames (Occurrences.generate (language installed))[site]) with
      | none => none
      | some indices =>
          if shared : ∀ parameter ∈ indices, parameter.slot.name ∈ (schema installed origin).matchedNames then
            some ⟨origin, site, NativeCubeProfile.rawIndex?_sound installed found, indices, decoded, shared⟩
          else none

def decodeAll? : Option (List (Header installed)) :=
  NativeSignature.decodeList (decode? installed) (List.finRange installed.modal.length)

theorem decode_origin {origin : Fin installed.modal.length} {header : Header installed}
    (decoded : decode? installed origin = some header) : header.origin = origin := by
  unfold decode? at decoded
  split at decoded
  · cases decoded
  · split at decoded
    · cases decoded
    · split at decoded
      · cases Option.some.inj decoded
        rfl
      · cases decoded

theorem decodeAll_origins {headers : List (Header installed)}
    (decoded : decodeAll? installed = some headers) :
    headers.map (·.origin) = List.finRange installed.modal.length := by
  have ordered := NativeSignature.decodeList_sound decoded
  generalize original : List.finRange installed.modal.length = origins at ordered ⊢
  clear decoded original
  induction ordered with
  | nil => rfl
  | cons first _ ih => simp only [List.map_cons, decode_origin installed first, ih]

variable {installed} (header : Header installed)

def coordinate {source : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (site : Fin (Occurrences.generate source).length) (label : DisplayedGraph.LocalSlot)
    (member : label ∈ DisplayedGraph.interface (Occurrences.generate source)[site]) :
    DisplayedGraph.Slot source :=
  ⟨site, ⟨(DisplayedGraph.interface (Occurrences.generate source)[site]).idxOf label,
    List.idxOf_lt_length_iff.mpr member⟩⟩

namespace Header

theorem index_names : header.indices.map (fun parameter => parameter.slot.name) =
    DisplayedGraph.indexNames (Occurrences.generate (language installed))[header.site] :=
  NativeModalParameters.decodeAll_names _ header.decoded

def readSlot (vertex : DisplayedGraph.Vertex (language installed)) (label : DisplayedGraph.LocalSlot)
    (member : label ∈ DisplayedGraph.interface (Occurrences.generate (language installed))[header.site]) : HSort :=
  vertex.1 (coordinate header.site label member)

def indexSort (vertex : DisplayedGraph.Vertex (language installed)) (position : Fin header.indices.length) : HSort :=
  header.readSlot vertex (.index header.indices[position].slot.name) (by
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨header.indices[position].slot.name, ?_, rfl⟩
    rw [← header.index_names]
    exact List.mem_map.mpr ⟨header.indices[position], List.getElem_mem position.isLt, rfl⟩)

def relySort (vertex : DisplayedGraph.Vertex (language installed))
    (position : Fin installed.modal[header.origin].rely.length) : HSort :=
  header.readSlot vertex (.rely installed.modal[header.origin].rely[position].slot.name) (by
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨installed.modal[header.origin].rely[position].slot.name, ?_, rfl⟩
    exact header.matching.2.2.mem_iff.mpr
      (List.mem_map.mpr ⟨installed.modal[header.origin].rely[position], List.getElem_mem position.isLt, rfl⟩))

def targetSort (vertex : DisplayedGraph.Vertex (language installed)) : HSort :=
  header.readSlot vertex .target (by simp [DisplayedGraph.interface])

def interface (vertex : DisplayedGraph.Vertex (language installed)) :
    IndexedModal.Interface (NativeSignature.Carrier (language installed)) where
  indices := List.ofFn fun position : Fin header.indices.length =>
    (header.indices[position].carrier, header.indexSort vertex position)
  relies := List.ofFn fun position : Fin installed.modal[header.origin].rely.length =>
    (installed.modal[header.origin].rely[position].carrier, header.relySort vertex position)
  target := installed.modal[header.origin].program
  focus := installed.modal[header.origin].focus
  resultSort := header.targetSort vertex

theorem index_count (vertex : DisplayedGraph.Vertex (language installed)) :
    (header.interface vertex).indices.length =
      (DisplayedGraph.indexNames (Occurrences.generate (language installed))[header.site]).length := by
  have names := congrArg List.length header.index_names
  simpa only [interface, List.length_ofFn, List.length_map] using names

theorem focus_carrier (vertex : DisplayedGraph.Vertex (language installed)) :
    (header.interface vertex).focus = installed.modal[header.origin].focus := rfl

theorem target_carrier (vertex : DisplayedGraph.Vertex (language installed)) :
    (header.interface vertex).target = installed.modal[header.origin].program := rfl

end Header

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SourceInterfaces
