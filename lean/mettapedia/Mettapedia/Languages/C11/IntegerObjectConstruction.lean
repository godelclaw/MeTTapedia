import Mettapedia.Languages.C11.ObjectLayout
import Mettapedia.Languages.C11.IntegerMemoryModel
import Mettapedia.Languages.C11.ScopedLvalues

/-!
# Declared integer objects constructed in owned byte memory

Scalar and positive-length array declarations select their element extent
from the integer memory model. An admitted layout supplies a checked byte
alignment. Construction derives the complete region, element regions,
declared-type records, array descriptor and identifier view; no external
lvalue descriptor is accepted.

Each object receives a fresh allocation lifetime, including scalar objects
viewed as one-element arrays for pointer arithmetic. Retired identities are
not reused. Array roots retain their array type in the identifier binding;
the typed-access catalog stores scalar elements. This avoids conflating the
array and scalar type records when a one-element array has the same byte
range as its element.

The rules describe automatic-object lifetime entry, not the C library
allocator. Scheduling non-VLA lifetime entry at block entry, VLA entry at
the reached declaration, source initializers and native ABI/allocator
correspondence remain distinct obligations. The admitted declaration types
are unqualified integers and arrays of them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerObjectConstruction

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open ByteRanges ByteStorageData ObjectAccessMemory IntegerMemoryModel
open scoped Mettapedia.GSLT.SeparationAlgebra

inductive Shape where
  | scalar
  | array (count : Nat) (positive : 0 < count)
  deriving DecidableEq, Repr

def Shape.count : Shape → Nat
  | .scalar => 1
  | .array count _ => count

theorem Shape.count_positive (shape : Shape) : 0 < shape.count := by
  cases shape with
  | scalar => decide
  | array count positive => exact positive

def Shape.type (shape : Shape) (integer : IntegerType IntegerExtension) : AccessTypes.ObjectType :=
  match shape with
  | .scalar => .scalar (.integer integer)
  | .array count _ => .array (.scalar (.integer integer)) count

structure Declaration where
  name : String
  integer : IntegerType IntegerExtension
  shape : Shape
  deriving DecidableEq, Repr

inductive InitialContents where
  | indeterminate
  | zero
  deriving DecidableEq, Repr

def InitialContents.byte (mode : InitialContents) (characters : ByteStorageData.Profile) : Option (Byte characters) :=
  match mode with
  | .indeterminate => none
  | .zero => some (BitVec.ofNat characters.charBits 0)

def Formation (model : Model) (declaration : Declaration) (element : ObjectLayout.Layout) : Prop :=
  element.bytes = (model.objects declaration.integer).byteCount

instance (model : Model) (declaration : Declaration) (element : ObjectLayout.Layout) :
    Decidable (Formation model declaration element) := inferInstanceAs (Decidable (_ = _))

def region (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) : Identity :=
  ⟨⟨identity, 0⟩, element.bytes * declaration.shape.count⟩

def descriptor (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) : ArrayPointers.Descriptor :=
  ObjectLayout.view identity 0 element declaration.shape.count

def root (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) : Lvalue :=
  ⟨region declaration element identity, ⟨declaration.shape.type declaration.integer, {}⟩⟩

def elementLocation (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId)
    (index : Fin declaration.shape.count) : Lvalue :=
  ⟨⟨(descriptor declaration element identity).address index.val, element.bytes⟩,
    ⟨.scalar (.integer declaration.integer), {}⟩⟩

def regions (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) : List Identity :=
  List.ofFn (fun index : Fin declaration.shape.count => (elementLocation declaration element identity index).object)

def elementRecord (declaration : Declaration) (element : ObjectLayout.Layout) : Record :=
  declaredRecord ⟨.scalar (.integer declaration.integer), {}⟩ element.alignment

def records (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) : ObjectAccessMemory.Catalog :=
  (regions declaration element identity).map (fun object => (object, elementRecord declaration element))

def CatalogFresh (catalog : ObjectAccessMemory.Catalog) (identity : BlockId) : Prop :=
  ∀ entry ∈ catalog, entry.1.address.allocation ≠ identity

instance (catalog : ObjectAccessMemory.Catalog) (identity : BlockId) : Decidable (CatalogFresh catalog identity) :=
  inferInstanceAs (Decidable (∀ entry ∈ catalog, entry.1.address.allocation ≠ identity))

/-- Ownership of a newly created block, stated in heap headers and cells,
independently of the finite record writer. -/
def BlockCreation {Byte : Type} (before : Heap (Excl (Option Byte))) (identity : BlockId)
    (contents : List (Option Byte)) (after : Heap (Excl (Option Byte))) : Prop :=
  before identity = 0 ∧
    (after identity).1 = .own ⟨contents.length, true⟩ ∧
    (∀ offset, (after identity).2 offset =
      if offset < contents.length then CellPermission.whole ((contents[offset]?).getD none) else 0) ∧
    ∀ other, other ≠ identity → after other = before other

def createStorage {Byte : Type} (storage : Storage.State Byte) (identity : BlockId)
    (contents : List (Option Byte)) : Option (Storage.State Byte) :=
  if storage.lookup identity = none then some (ExecutableStorage.put storage identity ⟨true, contents⟩) else none

theorem blockCreation_sound {Byte : Type} (storage saved : Storage.State Byte)
    (identity : BlockId) (contents : List (Option Byte))
    (created : createStorage storage identity contents = some saved) :
    BlockCreation (ByteRanges.heap storage) identity contents (ByteRanges.heap saved) := by
  by_cases fresh : storage.lookup identity = none
  · simp only [createStorage, if_pos fresh, Option.some.injEq] at created
    subst saved
    refine ⟨ExecutableStorage.heap_absent _ _ fresh, ?_, ?_, ?_⟩
    · simp [ByteRanges.heap, ExecutableStorage.heap, ExecutableStorage.Block.resource, ExecutableStorage.Block.header]
    · intro offset
      by_cases inside : offset < contents.length
      · simp [ByteRanges.heap, ExecutableStorage.heap, ExecutableStorage.Block.resource,
          inside, CellPermission.whole]
      · simp [ByteRanges.heap, ExecutableStorage.heap, ExecutableStorage.Block.resource,
          inside, Excl.zero_def]
    · intro other different
      simp only [ByteRanges.heap, ExecutableStorage.heap_put, Function.update_of_ne different]
  · simp only [createStorage, if_neg fresh] at created
    cases created

theorem blockCreation_complete {Byte : Type} (storage : Storage.State Byte) (identity : BlockId)
    (contents : List (Option Byte)) (after : Heap (Excl (Option Byte)))
    (creation : BlockCreation (ByteRanges.heap storage) identity contents after) :
    ∃ saved, createStorage storage identity contents = some saved ∧ ByteRanges.heap saved = after := by
  obtain ⟨fresh, header, cells, other⟩ := creation
  have absent := (ExecutableStorage.absent_iff_empty storage identity).mpr fresh
  refine ⟨ExecutableStorage.put storage identity ⟨true, contents⟩, ?_, ?_⟩
  · simp only [createStorage, if_pos absent]
  · funext observed
    by_cases same : observed = identity
    · subst observed
      apply blockRes_ext
      · simpa [ByteRanges.heap, ExecutableStorage.heap, ExecutableStorage.Block.resource,
          ExecutableStorage.Block.header] using header.symm
      · intro offset
        rw [cells]
        by_cases inside : offset < contents.length
        · simp [ByteRanges.heap, ExecutableStorage.heap, ExecutableStorage.Block.resource,
            inside, CellPermission.whole]
        · simp [ByteRanges.heap, ExecutableStorage.heap, ExecutableStorage.Block.resource,
            inside, Excl.zero_def]
    · rw [other observed same]
      simp only [ByteRanges.heap, ExecutableStorage.heap_put, Function.update_of_ne same]

theorem blockCreation_frame {Byte : Type} (before after frame : Heap (Excl (Option Byte)))
    (identity : BlockId) (contents : List (Option Byte))
    (created : BlockCreation before identity contents after) (freshFrame : frame identity = 0) :
    BlockCreation (before + frame) identity contents (after + frame) := by
  obtain ⟨fresh, header, cells, others⟩ := created
  refine ⟨?_, ?_, ?_, ?_⟩
  · change before identity + frame identity = 0
    rw [fresh, freshFrame, SepAlgebra.add_zero]
  · simpa only [heap_add_header, freshFrame, Prod.fst_zero, SepAlgebra.add_zero] using header
  · intro offset
    simpa only [heap_add_cell, freshFrame, Prod.snd_zero, Pi.zero_apply, SepAlgebra.add_zero] using cells offset
  · intro other different
    simp only [Pi.add_apply, others other different]

theorem BlockCreation.separate {Byte : Type} (before after frame : Heap (Excl (Option Byte)))
    (identity : BlockId) (contents : List (Option Byte))
    (created : BlockCreation before identity contents after) (separate : before ## frame)
    (freshFrame : frame identity = 0) : after ## frame := by
  intro other
  by_cases same : other = identity
  · subst other
    rw [freshFrame]
    exact SepAlgebra.separate_zero _
  · rw [created.2.2.2 other same]
    exact separate other

structure Constructed (model : Model) where
  memory : ObjectAccessMemory.State model.characters
  arrays : ArrayPointers.Catalog
  location : Lvalue
  deriving DecidableEq, Repr

def construct (model : Model) (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) (mode : InitialContents) :
    Option (Constructed model) := do
  if Formation model declaration element ∧ CatalogFresh memory.catalog identity ∧ arrays.lookup identity = none then
    let storage ← createStorage memory.storage identity
      (List.replicate (region declaration element identity).extent (mode.byte model.characters))
    some ⟨⟨storage, records declaration element identity ++ memory.catalog⟩,
      (identity, descriptor declaration element identity) :: arrays, root declaration element identity⟩
  else none

def Creation (model : Model) (before : ObjectAccessMemory.SemanticState model.characters)
    (arrays : ArrayPointers.Catalog) (declaration : Declaration) (element : ObjectLayout.Layout)
    (identity : BlockId) (mode : InitialContents) (after : ObjectAccessMemory.SemanticState model.characters)
    (nextArrays : ArrayPointers.Catalog) (location : Lvalue) : Prop :=
  Formation model declaration element ∧ CatalogFresh before.catalog identity ∧ arrays.lookup identity = none ∧
    BlockCreation before.memory identity
      (List.replicate (region declaration element identity).extent (mode.byte model.characters)) after.memory ∧
    after.catalog = records declaration element identity ++ before.catalog ∧
    nextArrays = (identity, descriptor declaration element identity) :: arrays ∧
    location = root declaration element identity

theorem construct_sound (model : Model) (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) (mode : InitialContents)
    (result : Constructed model) (executed : construct model memory arrays declaration element identity mode = some result) :
    Creation model (ObjectAccessMemory.represent memory) arrays declaration element identity mode
      (ObjectAccessMemory.represent result.memory) result.arrays result.location := by
  by_cases admitted : Formation model declaration element ∧ CatalogFresh memory.catalog identity ∧ arrays.lookup identity = none
  · simp only [construct, if_pos admitted, bind, Option.bind_eq_some_iff, Option.some.injEq] at executed
    obtain ⟨storage, created, rfl⟩ := executed
    exact ⟨admitted.1, admitted.2.1, admitted.2.2, blockCreation_sound _ _ _ _ created, rfl, rfl, rfl⟩
  · simp only [construct, if_neg admitted] at executed
    cases executed

theorem construct_complete (model : Model) (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) (mode : InitialContents)
    (after : ObjectAccessMemory.SemanticState model.characters) (nextArrays : ArrayPointers.Catalog) (location : Lvalue)
    (creation : Creation model (ObjectAccessMemory.represent memory) arrays declaration element identity mode after nextArrays location) :
    ∃ result, construct model memory arrays declaration element identity mode = some result ∧
      ObjectAccessMemory.represent result.memory = after ∧ result.arrays = nextArrays ∧ result.location = location := by
  obtain ⟨formed, fresh, arrayFresh, created, catalog, arraysEqual, locationEqual⟩ := creation
  obtain ⟨storage, stored, represented⟩ := blockCreation_complete memory.storage identity _ after.memory created
  refine ⟨⟨⟨storage, records declaration element identity ++ memory.catalog⟩,
      (identity, descriptor declaration element identity) :: arrays, root declaration element identity⟩, ?_, ?_, arraysEqual.symm, locationEqual.symm⟩
  · have admitted : Formation model declaration element ∧ CatalogFresh memory.catalog identity ∧ arrays.lookup identity = none :=
      ⟨formed, fresh, arrayFresh⟩
    simp only [construct, if_pos admitted, stored, bind, Option.bind_some]
  · cases after
    simp_all only [ObjectAccessMemory.represent]

theorem element_aligned (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId)
    (index : Fin declaration.shape.count) :
    element.alignment ∣ (elementLocation declaration element identity index).object.address.offset := by
  simpa only [elementLocation, descriptor, ObjectLayout.view, ArrayPointers.Descriptor.address,
    ObjectLayout.Layout.alignment, Nat.zero_add] using dvd_mul_of_dvd_left element.alignedSize index.val

theorem element_bounds (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId)
    (index : Fin declaration.shape.count) :
    (elementLocation declaration element identity index).object.address.offset + element.bytes ≤
      (region declaration element identity).extent := by
  have bounded := Nat.mul_le_mul_left element.bytes (Nat.succ_le_iff.mpr index.isLt)
  simpa only [elementLocation, descriptor, ObjectLayout.view, ArrayPointers.Descriptor.address, region,
    Nat.zero_add, Nat.mul_succ] using bounded

theorem elements_disjoint (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId)
    (first second : Fin declaration.shape.count) (different : first ≠ second) :
    Range.Disjoint (elementLocation declaration element identity first).object
      (elementLocation declaration element identity second).object := by
  have unequal : first.val ≠ second.val := fun same => different (Fin.ext same)
  rcases lt_or_gt_of_ne unequal with before | after
  · have ordered := Nat.mul_le_mul_left element.bytes (Nat.succ_le_iff.mpr before)
    exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [elementLocation, descriptor, ObjectLayout.view,
      ArrayPointers.Descriptor.address, Nat.zero_add, Nat.mul_succ] using ordered))))
  · have ordered := Nat.mul_le_mul_left element.bytes (Nat.succ_le_iff.mpr after)
    exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [elementLocation, descriptor, ObjectLayout.view,
      ArrayPointers.Descriptor.address, Nat.zero_add, Nat.mul_succ] using ordered))))

theorem regions_fresh_disjoint (catalog : ObjectAccessMemory.Catalog) (declaration : Declaration)
    (element : ObjectLayout.Layout) (identity : BlockId) (fresh : CatalogFresh catalog identity)
    (index : Fin declaration.shape.count) (old : Identity) (record : Record) (member : (old, record) ∈ catalog) :
    Range.Disjoint (elementLocation declaration element identity index).object old := by
  exact Or.inr (Or.inr (Or.inl (Ne.symm (fresh (old, record) member))))

private theorem lookup_constant {Key Value : Type} [BEq Key] [LawfulBEq Key]
    (keys : List Key) (value : Value) (key : Key) (member : key ∈ keys) :
    (keys.map (fun key => (key, value))).lookup key = some value := by
  induction keys with
  | nil => cases member
  | cons head tail ih =>
      by_cases same : key = head
      · subst head; simp
      · have following : key ∈ tail := (List.mem_cons.mp member).resolve_left same
        simp only [List.map_cons, List.lookup_cons, beq_eq_false_iff_ne.mpr same, ih following]

theorem records_lookup_element (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId)
    (index : Fin declaration.shape.count) :
    (records declaration element identity).lookup (elementLocation declaration element identity index).object =
      some (elementRecord declaration element) := by
  exact lookup_constant _ _ _ (List.mem_ofFn.mpr ⟨index, rfl⟩)

theorem element_pure (model : Model) (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId)
    (formed : Formation model declaration element) (index : Fin declaration.shape.count) :
    PureView (model.layout declaration.integer) (elementRecord declaration element)
      (elementLocation declaration element identity index) := by
  exact ⟨rfl, formed, element.alignment_positive,
    Nat.mod_eq_zero_of_dvd (element_aligned declaration element identity index), rfl, rfl⟩

theorem constructed_live_array (model : Model) (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (declaration : Declaration) (element : ObjectLayout.Layout) (identity : BlockId) (mode : InitialContents)
    (result : Constructed model) (executed : construct model memory arrays declaration element identity mode = some result) :
    ArrayPointers.LiveArray (ByteRanges.heap result.memory.storage) result.arrays identity
      (descriptor declaration element identity) := by
  obtain ⟨_, _, _, ⟨_, header, _, _⟩, _, arraysEqual, _⟩ := construct_sound _ _ _ _ _ _ _ _ executed
  refine ⟨by simp [arraysEqual], element.positive, (region declaration element identity).extent, ?_, ?_⟩
  · simpa only [List.length_replicate, ObjectAccessMemory.represent, descriptor, ObjectLayout.view] using header
  · simp only [descriptor, ObjectLayout.view, region, Nat.zero_add, le_refl]

theorem BlockCreation.holds {Byte : Type} (before after : Heap (Excl (Option Byte)))
    (identity : BlockId) (contents : List (Option Byte))
    (created : BlockCreation before identity contents after) : HoldsBlock after identity contents.length := by
  refine ⟨created.2.1, ?_⟩
  intro offset inside
  refine ⟨(contents[offset]?).getD none, ?_⟩
  rw [created.2.2.1 offset, if_pos inside]

theorem BlockCreation.replicated_read {Byte : Type} (before after : Heap (Excl (Option Byte)))
    (identity : BlockId) (size : Nat) (content : Option Byte)
    (created : BlockCreation before identity (List.replicate size content) after)
    (offset extent : Nat) (bounds : offset + extent ≤ size) :
    ReadRange after ⟨⟨identity, offset⟩, extent⟩ (List.replicate extent content) := by
  refine ⟨size, by simpa only [List.length_replicate] using created.2.1, bounds, List.length_replicate, ?_⟩
  intro index inside
  change index < extent at inside
  have allocated : offset + index < size := by omega
  change CellPermission.read ((after identity).2 (offset + index)) =
    some (((List.replicate extent content)[index]?).getD none)
  simp only [created.2.2.1 (offset + index), List.length_replicate, if_pos allocated]
  simp [allocated, inside]

theorem constructed_raw_element (model : Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (declaration : Declaration) (element : ObjectLayout.Layout)
    (identity : BlockId) (mode : InitialContents) (result : Constructed model)
    (executed : construct model memory arrays declaration element identity mode = some result)
    (index : Fin declaration.shape.count) :
    readBytes result.memory.storage (elementLocation declaration element identity index).object =
      some (List.replicate element.bytes (mode.byte model.characters)) := by
  have created := (construct_sound _ _ _ _ _ _ _ _ executed).2.2.2.1
  apply readBytes_complete
  exact BlockCreation.replicated_read _ _ _ _ _ created _ _ (element_bounds declaration element identity index)

theorem construct_preserves_other_block (model : Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (declaration : Declaration) (element : ObjectLayout.Layout)
    (identity : BlockId) (mode : InitialContents) (result : Constructed model)
    (executed : construct model memory arrays declaration element identity mode = some result)
    (other : BlockId) (different : other ≠ identity) :
    ByteRanges.heap result.memory.storage other = ByteRanges.heap memory.storage other :=
  (construct_sound _ _ _ _ _ _ _ _ executed).2.2.2.1.2.2.2 other different

theorem construct_records_element (model : Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (declaration : Declaration) (element : ObjectLayout.Layout)
    (identity : BlockId) (mode : InitialContents) (result : Constructed model)
    (executed : construct model memory arrays declaration element identity mode = some result)
    (index : Fin declaration.shape.count) :
    result.memory.catalog.lookup (elementLocation declaration element identity index).object =
      some (elementRecord declaration element) := by
  have catalog := (construct_sound _ _ _ _ _ _ _ _ executed).2.2.2.2.1
  change result.memory.catalog = records declaration element identity ++ memory.catalog at catalog
  rw [catalog, List.lookup_append, records_lookup_element]
  rfl

theorem construct_occupied_refused (model : Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (declaration : Declaration) (element : ObjectLayout.Layout)
    (identity : BlockId) (mode : InitialContents) (occupied : memory.storage.lookup identity ≠ none) :
    construct model memory arrays declaration element identity mode = none := by
  unfold construct
  split
  · simp only [createStorage, if_neg occupied, bind, Option.bind_none]
  · rfl

theorem construct_wrong_layout_refused (model : Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (declaration : Declaration) (element : ObjectLayout.Layout)
    (identity : BlockId) (mode : InitialContents) (wrong : ¬ Formation model declaration element) :
    construct model memory arrays declaration element identity mode = none := by
  have refused : ¬ (Formation model declaration element ∧ CatalogFresh memory.catalog identity ∧
      arrays.lookup identity = none) := fun admitted => wrong admitted.1
  simp only [construct, if_neg refused]

def maximumIdentity : List BlockId → BlockId
  | [] => 0
  | first :: rest => max first (maximumIdentity rest)

theorem member_le_maximum (identities : List BlockId) (identity : BlockId) (member : identity ∈ identities) :
    identity ≤ maximumIdentity identities := by
  induction identities with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | following
      · subst identity; exact Nat.le_max_left _ _
      · exact (ih following).trans (Nat.le_max_right _ _)

def mentionedIdentities {characters : ByteStorageData.Profile} (memory : ObjectAccessMemory.State characters)
    (arrays : ArrayPointers.Catalog) : List BlockId :=
  memory.storage.map Prod.fst ++ memory.catalog.map (fun entry => entry.1.address.allocation) ++ arrays.map Prod.fst

def freshIdentity {characters : ByteStorageData.Profile} (memory : ObjectAccessMemory.State characters)
    (arrays : ArrayPointers.Catalog) : BlockId := maximumIdentity (mentionedIdentities memory arrays) + 1

theorem mentioned_below_fresh {characters : ByteStorageData.Profile} (memory : ObjectAccessMemory.State characters)
    (arrays : ArrayPointers.Catalog) (identity : BlockId) (member : identity ∈ mentionedIdentities memory arrays) :
    identity < freshIdentity memory arrays := by
  exact Nat.lt_succ_of_le (member_le_maximum _ _ member)

private theorem lookup_absent_of_keys {Value : Type} (rows : List (BlockId × Value)) (key : BlockId)
    (missing : key ∉ rows.map Prod.fst) : rows.lookup key = none := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨keyHead, value⟩ := head
      have different : key ≠ keyHead := by
        intro same
        exact missing (List.mem_cons.mpr (.inl same))
      have following : key ∉ tail.map Prod.fst := fun member => missing (List.mem_cons_of_mem _ member)
      simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr different, ih following]

theorem fresh_storage_absent {characters : ByteStorageData.Profile} (memory : ObjectAccessMemory.State characters)
    (arrays : ArrayPointers.Catalog) : memory.storage.lookup (freshIdentity memory arrays) = none := by
  apply lookup_absent_of_keys
  intro present
  have all : freshIdentity memory arrays ∈ mentionedIdentities memory arrays := by
    simp only [mentionedIdentities, List.mem_append]
    exact .inl (.inl present)
  exact Nat.lt_irrefl _ (mentioned_below_fresh _ _ _ all)

theorem fresh_catalog_absent {characters : ByteStorageData.Profile} (memory : ObjectAccessMemory.State characters)
    (arrays : ArrayPointers.Catalog) : CatalogFresh memory.catalog (freshIdentity memory arrays) := by
  intro entry member same
  have all : freshIdentity memory arrays ∈ mentionedIdentities memory arrays := by
    simp only [mentionedIdentities, List.mem_append]
    exact .inl (.inr (List.mem_map.mpr ⟨entry, member, same⟩))
  exact Nat.lt_irrefl _ (mentioned_below_fresh _ _ _ all)

theorem fresh_array_absent {characters : ByteStorageData.Profile} (memory : ObjectAccessMemory.State characters)
    (arrays : ArrayPointers.Catalog) : arrays.lookup (freshIdentity memory arrays) = none := by
  apply lookup_absent_of_keys
  intro present
  have all : freshIdentity memory arrays ∈ mentionedIdentities memory arrays := by
    simp only [mentionedIdentities, List.mem_append]
    exact .inr present
  exact Nat.lt_irrefl _ (mentioned_below_fresh _ _ _ all)

def constructFresh (model : Model) (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (declaration : Declaration) (element : ObjectLayout.Layout) (mode : InitialContents) :
    Option (BlockId × Constructed model) :=
  (construct model memory arrays declaration element (freshIdentity memory arrays) mode).map
    (fun result => (freshIdentity memory arrays, result))

theorem constructFresh_exists (model : Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (declaration : Declaration) (element : ObjectLayout.Layout) (mode : InitialContents)
    (formed : Formation model declaration element) : ∃ identity result,
    constructFresh model memory arrays declaration element mode = some (identity, result) := by
  let identity := freshIdentity memory arrays
  have admitted : Formation model declaration element ∧ CatalogFresh memory.catalog identity ∧ arrays.lookup identity = none :=
    ⟨formed, fresh_catalog_absent _ _, fresh_array_absent _ _⟩
  refine ⟨identity, ⟨⟨ExecutableStorage.put memory.storage identity
      ⟨true, List.replicate (region declaration element identity).extent (mode.byte model.characters)⟩,
      records declaration element identity ++ memory.catalog⟩,
    (identity, descriptor declaration element identity) :: arrays, root declaration element identity⟩, ?_⟩
  dsimp only [identity] at admitted ⊢
  simp only [constructFresh, construct, if_pos admitted, createStorage, if_pos (fresh_storage_absent memory arrays),
    bind, Option.bind_some, Option.map_some]

theorem constructFresh_sound (model : Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (declaration : Declaration) (element : ObjectLayout.Layout) (mode : InitialContents)
    (identity : BlockId) (result : Constructed model)
    (executed : constructFresh model memory arrays declaration element mode = some (identity, result)) :
    identity = freshIdentity memory arrays ∧
    Creation model (ObjectAccessMemory.represent memory) arrays declaration element identity mode
      (ObjectAccessMemory.represent result.memory) result.arrays result.location := by
  obtain ⟨object, created, same⟩ := Option.map_eq_some_iff.mp executed
  have fields := Prod.mk.inj same
  obtain ⟨rfl, rfl⟩ := fields
  exact ⟨rfl, construct_sound _ _ _ _ _ _ _ _ created⟩

end Mettapedia.Languages.C11.IntegerObjectConstruction
