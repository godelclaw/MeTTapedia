import Mettapedia.Languages.C11.ByteRanges
import Mettapedia.Languages.C11.IntegerConversion

/-!
# Array-relative pointer operations at byte granularity

The retained object identity selects an array descriptor. Its byte origin,
element stride and runtime element count must fit a live allocation. Pointer
addition checks both the original position and the result, allowing one-past
formation but not one-past dereference. Subtraction additionally requires the
same array identity and a result representable in the named signed
ptrdiff_t format. Finite lookup/checking is proved equivalent to independent
heap-header and index judgments.

Descriptors are admitted memory views, not elaborated C declarations. Their
construction from types/layout, character views, casts and compatible views
of the same array remains a source/type connection. Pointer equality across
adjacent allocations is not defined here. Allocation identities describe
lifetimes, independently of physical-address reuse by a native allocator.

These operations return none when there is no defined result. Full C source
execution must distinguish semantic undefined behavior from malformed
external configuration data. Byte contents do not affect these operations;
ending the allocation lifetime invalidates every retained array view.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ArrayPointers

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open ByteRanges

structure Descriptor where
  allocation : BlockId
  origin : Nat
  elementBytes : Nat
  count : Nat
  deriving DecidableEq, Repr

abbrev Catalog := List (Nat × Descriptor)

structure Pointer where
  object : Nat
  index : Nat
  deriving DecidableEq, Repr

def Descriptor.address (descriptor : Descriptor) (index : Nat) : Address :=
  ⟨descriptor.allocation, descriptor.origin + descriptor.elementBytes * index⟩

variable {Byte : Type}

/-- The declared array region and its lifetime, expressed in the ownership
heap rather than by the executable lookup. -/
def LiveArray (memory : Heap (Excl (Option Byte))) (catalog : Catalog)
    (object : Nat) (descriptor : Descriptor) : Prop :=
  catalog.lookup object = some descriptor ∧ 0 < descriptor.elementBytes ∧
    ∃ extent, (memory descriptor.allocation).1 = .own ⟨extent, true⟩ ∧
      descriptor.origin + descriptor.elementBytes * descriptor.count ≤ extent

def descriptor? (storage : Storage.State Byte) (catalog : Catalog) (object : Nat) :
    Option Descriptor := do
  let descriptor ← catalog.lookup object
  let block ← storage.lookup descriptor.allocation
  if block.live ∧ 0 < descriptor.elementBytes ∧
      descriptor.origin + descriptor.elementBytes * descriptor.count ≤ block.cells.length then
    some descriptor
  else none

theorem descriptor_sound (storage : Storage.State Byte) (catalog : Catalog)
    (object : Nat) (descriptor : Descriptor) (accepted : descriptor? storage catalog object = some descriptor) :
    LiveArray (ByteRanges.heap storage) catalog object descriptor := by
  cases declared : catalog.lookup object with
  | none => simp [descriptor?, declared] at accepted
  | some actual =>
      cases present : storage.lookup actual.allocation with
      | none => simp [descriptor?, declared, present] at accepted
      | some block =>
          by_cases valid : block.live = true ∧ 0 < actual.elementBytes ∧
            actual.origin + actual.elementBytes * actual.count ≤ block.cells.length
          · simp [descriptor?, declared, present, valid] at accepted
            subst descriptor
            refine ⟨declared, valid.2.1, block.cells.length, ?_, valid.2.2⟩
            simp [ByteRanges.heap, ExecutableStorage.heap, present,
              ExecutableStorage.Block.resource, ExecutableStorage.Block.header, valid.1]
          · simp [descriptor?, declared, present, valid] at accepted

theorem descriptor_complete (storage : Storage.State Byte) (catalog : Catalog)
    (object : Nat) (descriptor : Descriptor)
    (live : LiveArray (ByteRanges.heap storage) catalog object descriptor) :
    descriptor? storage catalog object = some descriptor := by
  obtain ⟨declared, positive, extent, header, bounds⟩ := live
  cases present : storage.lookup descriptor.allocation with
  | none => simp [ByteRanges.heap, ExecutableStorage.heap, present, Excl.zero_def] at header
  | some block =>
      have fields : block.cells.length = extent ∧ block.live = true := by
        simpa [ByteRanges.heap, ExecutableStorage.heap, present,
          ExecutableStorage.Block.resource, ExecutableStorage.Block.header] using header
      have bounded : descriptor.origin + descriptor.elementBytes * descriptor.count ≤ block.cells.length := by omega
      simp [descriptor?, declared, present, fields.2, positive, bounded]

theorem descriptor_iff (storage : Storage.State Byte) (catalog : Catalog)
    (object : Nat) (descriptor : Descriptor) :
    descriptor? storage catalog object = some descriptor ↔
      LiveArray (ByteRanges.heap storage) catalog object descriptor :=
  ⟨descriptor_sound storage catalog object descriptor, descriptor_complete storage catalog object descriptor⟩

def WithinArray (memory : Heap (Excl (Option Byte))) (catalog : Catalog)
    (pointer : Pointer) (descriptor : Descriptor) : Prop :=
  LiveArray memory catalog pointer.object descriptor ∧ pointer.index ≤ descriptor.count

def resolve (storage : Storage.State Byte) (catalog : Catalog) (pointer : Pointer) : Option Address := do
  let descriptor ← descriptor? storage catalog pointer.object
  if pointer.index ≤ descriptor.count then some (descriptor.address pointer.index) else none

theorem resolve_iff (storage : Storage.State Byte) (catalog : Catalog) (pointer : Pointer) (address : Address) :
    resolve storage catalog pointer = some address ↔
      ∃ descriptor, WithinArray (ByteRanges.heap storage) catalog pointer descriptor ∧
        address = descriptor.address pointer.index := by
  constructor
  · intro accepted
    cases found : descriptor? storage catalog pointer.object with
    | none => simp [resolve, found] at accepted
    | some descriptor =>
        by_cases inside : pointer.index ≤ descriptor.count
        · simp [resolve, found, inside] at accepted
          exact ⟨descriptor, ⟨descriptor_sound storage catalog pointer.object descriptor found, inside⟩,
            accepted.symm⟩
        · simp [resolve, found, inside] at accepted
  · rintro ⟨descriptor, ⟨live, inside⟩, rfl⟩
    simp [resolve, descriptor_complete storage catalog pointer.object descriptor live, inside]

def elementRange (storage : Storage.State Byte) (catalog : Catalog) (pointer : Pointer) : Option Range := do
  let descriptor ← descriptor? storage catalog pointer.object
  if pointer.index < descriptor.count then
    some ⟨descriptor.address pointer.index, descriptor.elementBytes⟩
  else none

def ElementRange (memory : Heap (Excl (Option Byte))) (catalog : Catalog)
    (pointer : Pointer) (range : Range) : Prop :=
  ∃ descriptor, LiveArray memory catalog pointer.object descriptor ∧
    pointer.index < descriptor.count ∧
    range = ⟨descriptor.address pointer.index, descriptor.elementBytes⟩

theorem elementRange_iff (storage : Storage.State Byte) (catalog : Catalog)
    (pointer : Pointer) (range : Range) :
    elementRange storage catalog pointer = some range ↔
      ElementRange (ByteRanges.heap storage) catalog pointer range := by
  constructor
  · intro accepted
    cases found : descriptor? storage catalog pointer.object with
    | none => simp [elementRange, found] at accepted
    | some descriptor =>
        by_cases inside : pointer.index < descriptor.count
        · simp [elementRange, found, inside] at accepted
          exact ⟨descriptor, descriptor_sound storage catalog pointer.object descriptor found,
            inside, accepted.symm⟩
        · simp [elementRange, found, inside] at accepted
  · rintro ⟨descriptor, live, inside, rfl⟩
    simp [elementRange, descriptor_complete storage catalog pointer.object descriptor live, inside]

theorem ElementRange.byte_bounds (memory : Heap (Excl (Option Byte))) (catalog : Catalog)
    (pointer : Pointer) (range : Range) (element : ElementRange memory catalog pointer range) :
    ∃ extent, (memory range.address.allocation).1 = .own ⟨extent, true⟩ ∧
      range.address.offset + range.extent ≤ extent ∧ 0 < range.extent := by
  obtain ⟨descriptor, ⟨_, positive, extent, header, bounds⟩, inside, rfl⟩ := element
  have multiplication : descriptor.elementBytes * (pointer.index + 1) ≤
      descriptor.elementBytes * descriptor.count :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [Nat.mul_add, Nat.mul_one] at multiplication
  exact ⟨extent, header, by dsimp [Descriptor.address]; omega, positive⟩

def add (storage : Storage.State Byte) (catalog : Catalog) (pointer : Pointer)
    (distance : Int) : Option Pointer := do
  let descriptor ← descriptor? storage catalog pointer.object
  let target := (pointer.index : Int) + distance
  if pointer.index ≤ descriptor.count ∧ 0 ≤ target ∧ target ≤ (descriptor.count : Int) then
    some ⟨pointer.object, target.toNat⟩
  else none

def Addition (memory : Heap (Excl (Option Byte))) (catalog : Catalog)
    (pointer : Pointer) (distance : Int) (result : Pointer) : Prop :=
  ∃ descriptor, WithinArray memory catalog pointer descriptor ∧
    result.object = pointer.object ∧ (result.index : Int) = (pointer.index : Int) + distance ∧
    result.index ≤ descriptor.count

theorem add_sound (storage : Storage.State Byte) (catalog : Catalog) (pointer : Pointer)
    (distance : Int) (result : Pointer) (computed : add storage catalog pointer distance = some result) :
    Addition (ByteRanges.heap storage) catalog pointer distance result := by
  cases found : descriptor? storage catalog pointer.object with
  | none => simp [add, found] at computed
  | some descriptor =>
      by_cases valid : pointer.index ≤ descriptor.count ∧ 0 ≤ (pointer.index : Int) + distance ∧
        (pointer.index : Int) + distance ≤ (descriptor.count : Int)
      · simp [add, found, valid] at computed
        subst result
        refine ⟨descriptor, ⟨descriptor_sound storage catalog pointer.object descriptor found, valid.1⟩,
          rfl, Int.toNat_of_nonneg valid.2.1, ?_⟩
        dsimp
        omega
      · simp [add, found, valid] at computed

theorem add_complete (storage : Storage.State Byte) (catalog : Catalog) (pointer : Pointer)
    (distance : Int) (result : Pointer) (computed : Addition (ByteRanges.heap storage) catalog pointer distance result) :
    add storage catalog pointer distance = some result := by
  obtain ⟨descriptor, ⟨live, inside⟩, objectEqual, indexEqual, bounded⟩ := computed
  have nonnegative : 0 ≤ (pointer.index : Int) + distance := by omega
  have bound : (pointer.index : Int) + distance ≤ (descriptor.count : Int) := by omega
  have target : ((pointer.index : Int) + distance).toNat = result.index := by omega
  have resultEqual : (⟨pointer.object, ((pointer.index : Int) + distance).toNat⟩ : Pointer) = result := by
    cases result
    simp only [Pointer.mk.injEq] at *
    exact ⟨objectEqual.symm, target⟩
  simp [add, descriptor_complete storage catalog pointer.object descriptor live,
    inside, nonnegative, bound, resultEqual]

theorem add_iff (storage : Storage.State Byte) (catalog : Catalog) (pointer : Pointer)
    (distance : Int) (result : Pointer) : add storage catalog pointer distance = some result ↔
      Addition (ByteRanges.heap storage) catalog pointer distance result :=
  ⟨add_sound storage catalog pointer distance result, add_complete storage catalog pointer distance result⟩

structure DifferenceProfile where
  precision : Nat
  positive : 0 < precision
  minimumPrecision : 16 ≤ precision
  representation : SignedRepresentation

def DifferenceProfile.format (profile : DifferenceProfile) : IntegerFormat :=
  .signed profile.precision profile.positive profile.representation

def subtract (profile : DifferenceProfile) (storage : Storage.State Byte) (catalog : Catalog)
    (left right : Pointer) : Option Int := do
  let descriptor ← descriptor? storage catalog left.object
  let difference := (left.index : Int) - (right.index : Int)
  if left.object = right.object ∧ left.index ≤ descriptor.count ∧ right.index ≤ descriptor.count ∧
      profile.format.Represents difference then some difference else none

def Subtraction (profile : DifferenceProfile) (memory : Heap (Excl (Option Byte))) (catalog : Catalog)
    (left right : Pointer) (difference : Int) : Prop :=
  ∃ descriptor, WithinArray memory catalog left descriptor ∧
    left.object = right.object ∧ right.index ≤ descriptor.count ∧
    difference = (left.index : Int) - (right.index : Int) ∧ profile.format.Represents difference

theorem subtract_sound (profile : DifferenceProfile) (storage : Storage.State Byte) (catalog : Catalog)
    (left right : Pointer) (difference : Int)
    (computed : subtract profile storage catalog left right = some difference) :
    Subtraction profile (ByteRanges.heap storage) catalog left right difference := by
  cases found : descriptor? storage catalog left.object with
  | none => simp [subtract, found] at computed
  | some descriptor =>
      by_cases valid : left.object = right.object ∧ left.index ≤ descriptor.count ∧
        right.index ≤ descriptor.count ∧ profile.format.Represents ((left.index : Int) - (right.index : Int))
      · simp only [subtract, found, bind, Option.bind_some, if_pos valid] at computed
        have equal := Option.some.inj computed
        rw [← equal]
        exact ⟨descriptor, ⟨descriptor_sound storage catalog left.object descriptor found, valid.2.1⟩,
          valid.1, valid.2.2.1, rfl, valid.2.2.2⟩
      · simp [subtract, found, valid] at computed

theorem subtract_complete (profile : DifferenceProfile) (storage : Storage.State Byte) (catalog : Catalog)
    (left right : Pointer) (difference : Int)
    (computed : Subtraction profile (ByteRanges.heap storage) catalog left right difference) :
    subtract profile storage catalog left right = some difference := by
  obtain ⟨descriptor, ⟨live, leftBound⟩, same, rightBound, rfl, representable⟩ := computed
  have valid : left.object = right.object ∧ left.index ≤ descriptor.count ∧
      right.index ≤ descriptor.count ∧ profile.format.Represents ((left.index : Int) - (right.index : Int)) :=
    ⟨same, leftBound, rightBound, representable⟩
  simp only [subtract, descriptor_complete storage catalog left.object descriptor live,
    bind, Option.bind_some, if_pos valid]

theorem subtract_iff (profile : DifferenceProfile) (storage : Storage.State Byte) (catalog : Catalog)
    (left right : Pointer) (difference : Int) : subtract profile storage catalog left right = some difference ↔
      Subtraction profile (ByteRanges.heap storage) catalog left right difference :=
  ⟨subtract_sound profile storage catalog left right difference,
    subtract_complete profile storage catalog left right difference⟩

theorem liveArray_headers (before after : Heap (Excl (Option Byte))) (catalog : Catalog)
    (object : Nat) (descriptor : Descriptor)
    (headers : ∀ allocation, (before allocation).1 = (after allocation).1) :
    LiveArray before catalog object descriptor ↔ LiveArray after catalog object descriptor := by
  simp only [LiveArray, headers]

theorem liveArray_preserved_write (before after : Heap (Excl (Option Byte))) (catalog : Catalog)
    (object : Nat) (descriptor : Descriptor) (address : Address) (contents : List (Option Byte))
    (written : WriteRange before address contents after) :
    LiveArray before catalog object descriptor ↔ LiveArray after catalog object descriptor := by
  obtain ⟨_, _, _, _, rfl⟩ := written
  exact liveArray_headers _ _ catalog object descriptor fun allocation =>
    (updateRange_header before address contents allocation).symm

theorem dead_array_has_no_view (storage : Storage.State Byte) (catalog : Catalog)
    (object : Nat) (descriptor : Descriptor) (block : ExecutableStorage.Block Byte)
    (declared : catalog.lookup object = some descriptor)
    (present : storage.lookup descriptor.allocation = some block) (dead : block.live = false) :
    descriptor? storage catalog object = none := by
  simp [descriptor?, declared, present, dead]

end Mettapedia.Languages.C11.ArrayPointers
