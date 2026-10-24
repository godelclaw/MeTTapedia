import Mathlib.Data.List.Sort
import Mettapedia.Machines.Cursor.Protocol
import Mathlib.Data.Nat.Digits.Lemmas
import Mettapedia.Machines.CMemory.Primitives

/-!
# Executable storage for the scalar-cell ownership model

Finite block records are decoded into the existing exclusive-cell resource
heap. Dead records keep their allocation identity and extent, with no held
cells. The executable operations check lifetime and bounds before access.
Their correspondence is with the existing scalar-cell model, whose offsets
count objects rather than bytes; byte representation, effective types and
full C11 object layout are additional obligations.

Storage is a persistent association list. Replacing a record shadows its
previous version; allocation requires an identity absent from the current
lookup, including dead records. An allocation choice is supplied explicitly,
so success at any fresh identity and allocation failure remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.ExecutableStorage

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open CellPermission

variable {V : Type}

@[simp]
theorem read_owned (content : Option V) :
    read (Excl.own content) = some content := rfl

@[simp]
theorem whole_owned (content : Option V) :
    (whole content : Excl (Option V)) = .own content := rfl

structure Block (V : Type) where
  live : Bool
  cells : List (Option V)
  deriving Repr, DecidableEq

abbrev Storage (V : Type) := List (BlockId × Block V)

def Block.header (block : Block V) : Header := ⟨block.cells.length, block.live⟩

def Block.resource (block : Block V) : BlockRes (Excl (Option V)) :=
  (.own block.header, fun offset =>
    if block.live then
      match block.cells[offset]? with
      | some value => .own value
      | none => .empty
    else .empty)

/-- The ownership representation is constructed from the finite records. -/
def heap (storage : Storage V) : Heap (Excl (Option V)) := fun identity =>
  match storage.lookup identity with
  | some block => block.resource
  | none => 0

def put (storage : Storage V) (identity : BlockId) (block : Block V) : Storage V :=
  (identity, block) :: storage

@[simp]
theorem lookup_put_same (storage : Storage V) (identity : BlockId) (block : Block V) :
    (put storage identity block).lookup identity = some block := by
  simp [put]

@[simp]
theorem lookup_put_other (storage : Storage V) (identity other : BlockId)
    (block : Block V) (different : other ≠ identity) :
    (put storage identity block).lookup other = storage.lookup other := by
  have unequal : (other == identity) = false := beq_eq_false_iff_ne.mpr different
  simp [put, List.lookup_cons, unequal]

theorem heap_put (storage : Storage V) (identity : BlockId) (block : Block V) :
    heap (put storage identity block) = Function.update (heap storage) identity block.resource := by
  funext other
  by_cases same : other = identity
  · subst other
    simp [heap]
  · simp [heap, lookup_put_other storage identity other block same,
      Function.update_of_ne same]

@[simp]
theorem heap_absent (storage : Storage V) (identity : BlockId)
    (absent : storage.lookup identity = none) : heap storage identity = 0 := by
  simp [heap, absent]

@[simp]
theorem heap_present (storage : Storage V) (identity : BlockId) (block : Block V)
    (present : storage.lookup identity = some block) :
    heap storage identity = block.resource := by
  simp [heap, present]

theorem absent_iff_empty (storage : Storage V) (identity : BlockId) :
    storage.lookup identity = none ↔ heap storage identity = 0 := by
  cases found : storage.lookup identity with
  | none => simp [heap, found]
  | some block =>
      simp [heap, found, Block.resource]

/-- Every finite storage state describes a well-formed whole resource heap. -/
theorem wellFormed (storage : Storage V) : WellFormed (heap storage) := by
  intro identity offset held
  cases found : storage.lookup identity with
  | none => simp [heap, found] at held
  | some block =>
      cases live : block.live with
      | false => simp [heap, found, Block.resource, live, Excl.zero_def] at held
      | true =>
          refine ⟨block.cells.length, ?_, ?_⟩
          · simp [heap, found, Block.resource, Block.header, live]
          · by_contra outside
            have absent : block.cells[offset]? = none :=
              List.getElem?_eq_none (by omega)
            simp [heap, found, Block.resource, live, absent, Excl.zero_def] at held

def load (storage : Storage V) (address : Ptr) : Option V := do
  let block ← storage.lookup address.block
  if block.live then (block.cells[address.offset]?).join else none

def store (storage : Storage V) (address : Ptr) (value : V) : Option (Storage V) := do
  let block ← storage.lookup address.block
  if block.live ∧ address.offset < block.cells.length then
    some (put storage address.block
      { block with cells := block.cells.set address.offset (some value) })
  else none

def free (storage : Storage V) : Option Ptr → Option (Storage V)
  | none => some storage
  | some address => do
      let block ← storage.lookup address.block
      if block.live ∧ address.offset = 0 then
        some (put storage address.block { block with live := false })
      else none

/-- One-past pointers may be compared but never loaded or stored. -/
def validPointer (storage : Storage V) (address : Ptr) : Bool :=
  match storage.lookup address.block with
  | none => false
  | some block => block.live && decide (address.offset ≤ block.cells.length)

def validOption (storage : Storage V) : Option Ptr → Bool
  | none => true
  | some address => validPointer storage address

def compare (storage : Storage V) (left right : Option Ptr) : Option Bool :=
  if validOption storage left && validOption storage right then
    some (decide (left = right))
  else none

inductive AllocationChoice where
  | failure
  | fresh (identity : BlockId)
  deriving Repr, DecidableEq

def allocate (storage : Storage V) (extent : Nat) :
    AllocationChoice → Option (Option Ptr × Storage V)
  | .failure => some (none, storage)
  | .fresh identity =>
      if storage.lookup identity = none then
        some (some ⟨identity, 0⟩, put storage identity ⟨true, List.replicate extent none⟩)
      else none

/-- Copy the old prefix and leave every additional cell indeterminate. -/
def resize (block : Block V) (extent : Nat) : Block V :=
  ⟨true, List.ofFn (fun index : Fin extent => (block.cells[index.val]?).join)⟩

/-- This realizes the existing nonzero-reallocation primitive. C11's
implementation-defined zero-size reallocation needs a separate profile. -/
def reallocate (storage : Storage V) (address : Option Ptr) (extent : Nat)
    (choice : AllocationChoice) : Option (Option Ptr × Storage V) :=
  match address with
  | none => allocate storage extent choice
  | some address => do
      let block ← storage.lookup address.block
      if block.live ∧ address.offset = 0 ∧ 0 < extent then
        match choice with
        | .failure => some (none, storage)
        | .fresh identity =>
            if storage.lookup identity = none then
              some (some ⟨identity, 0⟩,
                put (put storage address.block { block with live := false })
                  identity (resize block extent))
            else none
      else none

theorem load_exact (storage : Storage V) (address : Ptr) (value : V) :
    load storage address = some value ↔
      read ((heap storage address.block).2 address.offset) = some (some value) := by
  cases found : storage.lookup address.block with
  | none => simp [load, heap, found, read_zero]
  | some block =>
      cases live : block.live with
      | false => simp [load, heap, found, Block.resource, live]
      | true =>
          cases cell : block.cells[address.offset]? with
          | none => simp [load, heap, found, Block.resource, live, cell]
          | some content =>
              cases content <;>
                simp [load, heap, found, Block.resource, live, cell]

/-- Executable loads realize every permitted logical load, including its
unchanged memory endpoint. Indeterminate, dead and absent cells have no load. -/
theorem load_step_iff (storage : Storage V) (address : Ptr) (value : V) :
    load storage address = some value ↔
      (act (L := Excl (Option V)) (.load address)).Step
        (heap storage) value (heap storage) := by
  simpa [act] using load_exact storage address value

theorem store_heap (storage : Storage V) (address : Ptr) (value : V)
    (block : Block V) (present : storage.lookup address.block = some block)
    (live : block.live = true) (inside : address.offset < block.cells.length) :
    heap (put storage address.block
        { block with cells := block.cells.set address.offset (some value) }) =
      (heap storage).setCell address (whole (some value)) := by
  rw [heap_put]
  apply congrArg (Function.update (heap storage) address.block)
  apply blockRes_ext
  · simp [Block.resource, Block.header, heap, present]
  · intro offset
    by_cases same : offset = address.offset
    · subst offset
      simp [Block.resource, live, List.getElem?_set_self inside]
    · simp [Block.resource, live, List.getElem?_set_ne (Ne.symm same),
        heap, present, Function.update_of_ne same]

theorem store_sound (storage next : Storage V) (address : Ptr) (value : V)
    (executed : store storage address value = some next) :
    (act (L := Excl (Option V)) (.store address value)).Safe (heap storage) ∧
      (act (L := Excl (Option V)) (.store address value)).Step
        (heap storage) () (heap next) := by
  cases found : storage.lookup address.block with
  | none => simp [store, found] at executed
  | some block =>
      by_cases valid : block.live = true ∧ address.offset < block.cells.length
      · simp [store, found, valid] at executed
        subst next
        constructor
        · refine ⟨block.cells[address.offset]'valid.2, ?_⟩
          simp [heap, found, Block.resource, valid.1,
            List.getElem?_eq_getElem valid.2]
        · simpa [act, valid.1] using
            store_heap storage address value block found valid.1 valid.2
      · simp [store, found, valid] at executed

/-- Every safe logical store has the corresponding executable endpoint.
The safety premise is essential: the action's raw state relation alone does
not authorize writes to dead or unowned cells. -/
theorem store_complete (storage : Storage V) (address : Ptr) (value : V)
    (after : Heap (Excl (Option V)))
    (safe : (act (L := Excl (Option V)) (.store address value)).Safe (heap storage))
    (stepped : (act (L := Excl (Option V)) (.store address value)).Step
      (heap storage) () after) :
    ∃ next, store storage address value = some next ∧ heap next = after := by
  obtain ⟨content, held⟩ := safe
  cases found : storage.lookup address.block with
  | none => simp [heap, found, Excl.zero_def] at held
  | some block =>
      cases live : block.live with
      | false => simp [heap, found, Block.resource, live] at held
      | true =>
          cases cell : block.cells[address.offset]? with
          | none => simp [heap, found, Block.resource, live, cell] at held
          | some old =>
              obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp cell
              refine ⟨put storage address.block
                { block with cells := block.cells.set address.offset (some value) }, ?_, ?_⟩
              · simp [store, found, live, inside]
              · rw [store_heap storage address value block found live inside]
                exact stepped.symm

theorem holds_present (storage : Storage V) (identity : BlockId) (block : Block V)
    (present : storage.lookup identity = some block) (live : block.live = true) :
    HoldsBlock (heap storage) identity block.cells.length := by
  constructor
  · simp [heap, present, Block.resource, Block.header, live]
  · intro offset inside
    refine ⟨block.cells[offset]'inside, ?_⟩
    simp [heap, present, Block.resource, live, List.getElem?_eq_getElem inside]

theorem free_heap (storage : Storage V) (identity : BlockId) (block : Block V)
    (present : storage.lookup identity = some block) :
    heap (put storage identity { block with live := false }) =
      (heap storage).kill identity block.cells.length := by
  rw [heap_put]
  apply congrArg (Function.update (heap storage) identity)
  apply blockRes_ext
  · rfl
  · intro offset
    by_cases inside : offset < block.cells.length
    · simp [Block.resource, Heap.killedBlock, inside, Excl.zero_def]
    · simp [Block.resource, Heap.killedBlock, inside, heap, present, Excl.zero_def]

theorem free_sound (storage next : Storage V) (address : Option Ptr)
    (executed : free storage address = some next) :
    (act (L := Excl (Option V)) (.free address)).Safe (heap storage) ∧
      (act (L := Excl (Option V)) (.free address)).Step
        (heap storage) () (heap next) := by
  cases address with
  | none =>
      simp [free] at executed
      subst next
      exact ⟨trivial, rfl⟩
  | some address =>
      cases found : storage.lookup address.block with
      | none => simp [free, found] at executed
      | some block =>
          by_cases valid : block.live = true ∧ address.offset = 0
          · simp [free, found, valid] at executed
            subst next
            refine ⟨⟨valid.2, block.cells.length, holds_present storage address.block block found valid.1⟩,
              block.cells.length, ?_, free_heap storage address.block block found⟩
            simp [heap, found, Block.resource, Block.header, valid.1]
          · simp [free, found, valid] at executed

theorem free_complete (storage : Storage V) (address : Option Ptr)
    (after : Heap (Excl (Option V)))
    (safe : (act (L := Excl (Option V)) (.free address)).Safe (heap storage))
    (stepped : (act (L := Excl (Option V)) (.free address)).Step
      (heap storage) () after) :
    ∃ next, free storage address = some next ∧ heap next = after := by
  cases address with
  | none => exact ⟨storage, rfl, stepped.symm⟩
  | some address =>
      obtain ⟨base, extent, header, _⟩ := safe
      cases found : storage.lookup address.block with
      | none => simp [heap, found, Excl.zero_def] at header
      | some block =>
          have identified : block.cells.length = extent ∧ block.live = true := by
            simpa [heap, found, Block.resource, Block.header] using header
          refine ⟨put storage address.block { block with live := false }, ?_, ?_⟩
          · simp [free, found, base, identified.2]
          · obtain ⟨otherExtent, otherHeader, final⟩ := stepped
            have sameExtent : otherExtent = block.cells.length := by
              have fields : block.cells.length = otherExtent ∧ block.live = true := by
                simpa [heap, found, Block.resource, Block.header] using otherHeader
              exact fields.1.symm
            rw [sameExtent] at final
            rw [free_heap storage address.block block found]
            exact final.symm

theorem validPointer_exact (storage : Storage V) (address : Ptr) :
    validPointer storage address = true ↔ Valid (heap storage) address := by
  have header : Valid (heap storage) address ↔
      ∃ extent, (heap storage address.block).1 = .own ⟨extent, true⟩ ∧
        address.offset ≤ extent := by
    constructor
    · rintro (header | held)
      · exact header
      · obtain ⟨extent, live, inside⟩ := (wellFormed storage).live held
        exact ⟨extent, live, Nat.le_of_lt inside⟩
    · exact Or.inl
  rw [header]
  cases found : storage.lookup address.block with
  | none => simp [validPointer, heap, found, Excl.zero_def]
  | some block =>
      cases live : block.live <;>
        simp [validPointer, heap, found, Block.resource, Block.header, live]

theorem validOption_exact (storage : Storage V) (address : Option Ptr) :
    validOption storage address = true ↔ ValidOpt (heap storage) address := by
  cases address with
  | none => simp [validOption, ValidOpt]
  | some address => exact validPointer_exact storage address

/-- Comparison correspondence includes pointer validity, as well as the
result and unchanged memory. Block identities implement this ownership
model's pointer equality; native address equality requires a separate layout.
-/
theorem compare_exact (storage : Storage V) (left right : Option Ptr) (result : Bool) :
    compare storage left right = some result ↔
      (act (L := Excl (Option V)) (.ptrEq left right)).Safe (heap storage) ∧
        (act (L := Excl (Option V)) (.ptrEq left right)).Step
          (heap storage) result (heap storage) := by
  by_cases leftValid : validOption storage left = true <;>
    by_cases rightValid : validOption storage right = true <;>
      simp [compare, act, ← validOption_exact, leftValid, rightValid, eq_comm]

theorem fresh_resource (extent : Nat) :
    (Block.mk true (List.replicate extent (none : Option V))).resource = freshBlock extent := by
  apply blockRes_ext
  · simp [Block.resource, Block.header, freshBlock]
  · intro offset
    by_cases inside : offset < extent
    · simp [Block.resource, freshBlock, List.getElem?_replicate, inside]
    · simp [Block.resource, freshBlock, List.getElem?_replicate, inside, Excl.zero_def]

theorem allocate_sound (storage next : Storage V) (extent : Nat)
    (choice : AllocationChoice) (result : Option Ptr)
    (executed : allocate storage extent choice = some (result, next)) :
    (act (L := Excl (Option V)) (.malloc extent)).Step (heap storage) result (heap next) := by
  cases choice with
  | failure =>
      simp [allocate] at executed
      obtain ⟨rfl, rfl⟩ := executed
      exact Or.inl ⟨rfl, rfl⟩
  | fresh identity =>
      by_cases absent : storage.lookup identity = none
      · simp [allocate, absent] at executed
        obtain ⟨rfl, rfl⟩ := executed
        refine Or.inr ⟨identity, heap_absent storage identity absent, rfl, ?_⟩
        rw [heap_put, fresh_resource]
      · simp [allocate, absent] at executed

/-- Logical allocation choices are all constructible as executable choices;
no fixed allocator identity is imposed on the logical semantics. -/
theorem allocate_complete (storage : Storage V) (extent : Nat)
    (result : Option Ptr) (after : Heap (Excl (Option V)))
    (stepped : (act (L := Excl (Option V)) (.malloc extent)).Step
      (heap storage) result after) :
    ∃ choice next, allocate storage extent choice = some (result, next) ∧ heap next = after := by
  rcases stepped with ⟨rfl, rfl⟩ | ⟨identity, absent, rfl, rfl⟩
  · exact ⟨.failure, storage, rfl, rfl⟩
  · have missing := (absent_iff_empty storage identity).mpr absent
    refine ⟨.fresh identity, put storage identity ⟨true, List.replicate extent none⟩, ?_, ?_⟩
    · simp [allocate, missing]
    · rw [heap_put, fresh_resource]

theorem resize_resource (storage : Storage V) (identity : BlockId) (block : Block V)
    (present : storage.lookup identity = some block) (live : block.live = true)
    (extent : Nat) :
    (resize block extent).resource =
      (heap storage).grownBlock identity block.cells.length extent := by
  apply blockRes_ext
  · simp [resize, Block.resource, Block.header, Heap.grownBlock]
  · intro offset
    by_cases inside : offset < extent
    · by_cases old : offset < block.cells.length
      · simp [Block.resource, resize, List.getElem?_ofFn, inside, old,
          Heap.grownBlock, heap, present, live]
      · simp [Block.resource, resize, List.getElem?_ofFn, inside, old,
          Heap.grownBlock, Excl.zero_def]
    · simp [Block.resource, resize, List.getElem?_ofFn, inside,
        Heap.grownBlock, Excl.zero_def]

theorem reallocate_heap (storage : Storage V) (address : Ptr) (block : Block V)
    (present : storage.lookup address.block = some block) (live : block.live = true)
    (identity : BlockId) (extent : Nat) :
    heap (put (put storage address.block { block with live := false })
        identity (resize block extent)) =
      (heap storage).move address.block block.cells.length identity extent := by
  rw [heap_put, free_heap storage address.block block present,
    resize_resource storage address.block block present live extent]
  rfl

theorem reallocate_sound (storage next : Storage V) (address : Option Ptr) (extent : Nat)
    (choice : AllocationChoice) (result : Option Ptr)
    (executed : reallocate storage address extent choice = some (result, next)) :
    (act (L := Excl (Option V)) (.realloc address extent)).Safe (heap storage) ∧
      (act (L := Excl (Option V)) (.realloc address extent)).Step
        (heap storage) result (heap next) := by
  cases address with
  | none => exact ⟨trivial, allocate_sound storage next extent choice result executed⟩
  | some address =>
      cases present : storage.lookup address.block with
      | none => simp [reallocate, present] at executed
      | some block =>
          by_cases valid : block.live = true ∧ address.offset = 0 ∧ 0 < extent
          · have safe :
                (act (L := Excl (Option V)) (.realloc (some address) extent)).Safe
                  (heap storage) :=
              ⟨valid.2.2, valid.2.1, block.cells.length,
                holds_present storage address.block block present valid.1⟩
            cases choice with
            | failure =>
                simp [reallocate, present, valid] at executed
                obtain ⟨rfl, rfl⟩ := executed
                exact ⟨safe, Or.inl ⟨rfl, rfl⟩⟩
            | fresh identity =>
                by_cases absent : storage.lookup identity = none
                · simp [reallocate, present, valid, absent] at executed
                  obtain ⟨rfl, rfl⟩ := executed
                  refine ⟨safe, Or.inr ⟨block.cells.length, identity, ?_,
                    heap_absent storage identity absent, rfl,
                    reallocate_heap storage address block present valid.1 identity extent⟩⟩
                  simp [heap, present, Block.resource, Block.header, valid.1]
                · simp [reallocate, present, valid, absent] at executed
          · simp [reallocate, present, valid] at executed

theorem reallocate_complete (storage : Storage V) (address : Option Ptr) (extent : Nat)
    (result : Option Ptr) (after : Heap (Excl (Option V)))
    (safe : (act (L := Excl (Option V)) (.realloc address extent)).Safe (heap storage))
    (stepped : (act (L := Excl (Option V)) (.realloc address extent)).Step
      (heap storage) result after) :
    ∃ choice next, reallocate storage address extent choice = some (result, next) ∧
      heap next = after := by
  cases address with
  | none => exact allocate_complete storage extent result after stepped
  | some address =>
      obtain ⟨positive, base, oldExtent, header, _⟩ := safe
      cases present : storage.lookup address.block with
      | none => simp [heap, present, Excl.zero_def] at header
      | some block =>
          have identified : block.cells.length = oldExtent ∧ block.live = true := by
            simpa [heap, present, Block.resource, Block.header] using header
          rcases stepped with ⟨rfl, rfl⟩ |
            ⟨copyExtent, identity, copyHeader, absent, rfl, rfl⟩
          · refine ⟨.failure, storage, ?_, rfl⟩
            simp [reallocate, present, identified.2, base, positive]
          · have missing := (absent_iff_empty storage identity).mpr absent
            have extentEqual : block.cells.length = copyExtent := by
              have fields : block.cells.length = copyExtent ∧ block.live = true := by
                simpa [heap, present, Block.resource, Block.header] using copyHeader
              exact fields.1
            refine ⟨.fresh identity,
              put (put storage address.block { block with live := false })
                identity (resize block extent), ?_, ?_⟩
            · simp [reallocate, present, identified.2, base, positive, missing]
            · rw [reallocate_heap storage address block present identified.2 identity extent,
                extentEqual]

/-- Execute one scalar-cell primitive under an explicit allocation choice.
An invalid allocation choice is refused; refusal alone is not a declaration
of C undefined behavior. Pointer and memory safety are characterized below. -/
def perform (storage : Storage V) (choice : AllocationChoice) :
    (operation : Op V) → Option (operation.Ret × Storage V)
  | .load address => do
      let value ← load storage address
      pure (value, storage)
  | .store address value => do
      let next ← store storage address value
      pure ((), next)
  | .malloc extent => allocate storage extent choice
  | .free address => do
      let next ← free storage address
      pure ((), next)
  | .realloc address extent => reallocate storage address extent choice
  | .ptrEq left right => do
      let value ← compare storage left right
      pure (value, storage)
  | .undefined => none

/-- Every accepted executable operation has the original safety authority
and exact logical endpoint. The executable implementation is not an alias
of the logical action. -/
theorem perform_sound (storage next : Storage V) (choice : AllocationChoice)
    (operation : Op V) (response : operation.Ret)
    (executed : perform storage choice operation = some (response, next)) :
    (act (L := Excl (Option V)) operation).Safe (heap storage) ∧
      (act (L := Excl (Option V)) operation).Step (heap storage) response (heap next) := by
  cases operation with
  | load address =>
      cases readValue : load storage address with
      | none => simp [perform, readValue] at executed
      | some value =>
          simp [perform, readValue] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact ⟨⟨response, (load_exact storage address response).mp readValue⟩,
            (load_step_iff storage address response).mp readValue⟩
  | store address value =>
      cases response
      cases stored : store storage address value with
      | none => simp [perform, stored] at executed
      | some updated =>
          simp [perform, stored] at executed
          have final : updated = next := congrArg Prod.snd executed
          subst next
          exact store_sound storage updated address value stored
  | malloc extent => exact ⟨trivial, allocate_sound storage next extent choice response executed⟩
  | free address =>
      cases response
      cases freed : free storage address with
      | none => simp [perform, freed] at executed
      | some updated =>
          simp [perform, freed] at executed
          have final : updated = next := congrArg Prod.snd executed
          subst next
          exact free_sound storage updated address freed
  | realloc address extent => exact reallocate_sound storage next address extent choice response executed
  | ptrEq left right =>
      cases compared : compare storage left right with
      | none => simp [perform, compared] at executed
      | some value =>
          simp [perform, compared] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact (compare_exact storage left right response).mp compared
  | undefined => simp [perform] at executed

/-- Every safe logical operation can be performed by this executable
storage under a constructible choice, with the same dependent response and
complete resulting ownership heap. -/
theorem perform_complete (storage : Storage V) (operation : Op V)
    (response : operation.Ret) (after : Heap (Excl (Option V)))
    (safe : (act (L := Excl (Option V)) operation).Safe (heap storage))
    (stepped : (act (L := Excl (Option V)) operation).Step (heap storage) response after) :
    ∃ choice next, perform storage choice operation = some (response, next) ∧ heap next = after := by
  cases operation with
  | load address =>
      obtain ⟨readValue, final⟩ := stepped
      have loaded := (load_exact storage address response).mpr readValue
      exact ⟨.failure, storage, by simp [perform, loaded, Option.bind], final.symm⟩
  | store address value =>
      cases response
      obtain ⟨next, stored, final⟩ := store_complete storage address value after safe stepped
      exact ⟨.failure, next, by simp [perform, stored], final⟩
  | malloc extent => exact allocate_complete storage extent response after stepped
  | free address =>
      cases response
      obtain ⟨next, freed, final⟩ := free_complete storage address after safe stepped
      exact ⟨.failure, next, by simp [perform, freed], final⟩
  | realloc address extent => exact reallocate_complete storage address extent response after safe stepped
  | ptrEq left right =>
      obtain ⟨comparedValue, final⟩ := stepped
      have compared := (compare_exact storage left right response).mpr
        ⟨safe, comparedValue, rfl⟩
      exact ⟨.failure, storage, by simp [perform, compared, Option.bind], final.symm⟩
  | undefined => exact safe.elim

theorem default_choice_available (storage next : Storage V) (choice : AllocationChoice)
    (operation : Op V) (response : operation.Ret)
    (executed : perform storage choice operation = some (response, next)) :
    ∃ result saved, perform storage .failure operation = some (result, saved) := by
  cases operation with
  | load address => exact ⟨response, next, executed⟩
  | store address value => exact ⟨response, next, executed⟩
  | malloc extent => exact ⟨none, storage, rfl⟩
  | free address => exact ⟨response, next, executed⟩
  | ptrEq left right => exact ⟨response, next, executed⟩
  | undefined => simp [perform] at executed
  | realloc address extent =>
      cases address with
      | none => exact ⟨none, storage, rfl⟩
      | some address =>
          cases found : storage.lookup address.block with
          | none => simp [perform, reallocate, found] at executed
          | some block =>
              by_cases valid : block.live = true ∧ address.offset = 0 ∧ 0 < extent
              · refine ⟨none, storage, ?_⟩
                simp [perform, reallocate, found, valid]
                rfl
              · simp [perform, reallocate, found, valid] at executed

/-- Allocation failure is always an admissible allocator choice. Therefore
failure under that choice precisely detects an unsafe scalar-cell operation;
a refused occupied allocation identity is not confused with unsafe memory. -/
theorem default_choice_iff_safe (storage : Storage V) (operation : Op V) :
    (∃ response next, perform storage .failure operation = some (response, next)) ↔
      (act (L := Excl (Option V)) operation).Safe (heap storage) := by
  constructor
  · rintro ⟨response, next, executed⟩
    exact (perform_sound storage next .failure operation response executed).1
  · intro safe
    obtain ⟨response, after, stepped⟩ := act_progress (L := Excl (Option V)) operation
      (heap storage) safe
    obtain ⟨choice, next, executed, _⟩ := perform_complete storage operation response after safe stepped
    exact default_choice_available storage next choice operation response executed

theorem default_none_iff_unsafe (storage : Storage V) (operation : Op V) :
    perform storage .failure operation = none ↔
      ¬ (act (L := Excl (Option V)) operation).Safe (heap storage) := by
  constructor
  · intro refused safe
    obtain ⟨response, next, executed⟩ := (default_choice_iff_safe storage operation).mpr safe
    simp [refused] at executed
  · intro notSafe
    cases executed : perform storage .failure operation with
    | none => rfl
    | some result =>
        obtain ⟨response, next⟩ := result
        exact (notSafe (perform_sound storage next .failure operation response executed).1).elim

end Mettapedia.Machines.CMemory.ExecutableStorage

/-!
Indexed storage uses a fixed four-directory radix path and fixed-size element
pages. Actual nullable-slot lookup, single-block installation and element
writes preserve existing addresses/rows. Successful fresh allocation reduces
the retained missing suffix; refusal preserves the original live residual.
Allocation-chain retirement revokes indexed access and frees one block per
step through the existing scalar storage and cursor owners.

The fixed-block initialization service supplies typed null directory cells;
raw calloc bytes, portable null representation, alignment, effective types,
logical/native allocation identities and physical service prices require a
separate native instance. The explicit byte cap of a particular consumer,
concurrent access and memo-hash migration are not refined here.

The two-buffer pass consumes a declared source-index reply word and performs
actual row reads/writes. It proves occurrence/key inventory under a legal
index schedule and earned local typed destination/region support. It does
not choose or implement a sorting comparator. Native bottom-up merge index
legality/sortedness and global pointer/index separation for reachable C
layouts remain independent adapter obligations. Scratch rows borrow payload
keys until a completed pass transfers the complete primary owner.
-/

namespace Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed

open Mettapedia.GSLT.SeparationAlgebra
variable {V : Type}

/-- Four 128-way directories above 64-cell element pages. -/
def route (index : Nat) : List Nat := (Nat.digitsAppend 128 4 (index / 64)).reverse

def offset (index : Nat) : Nat := index % 64

theorem route_length (index : Nat) (bounded : index < 2 ^ 32) : (route index).length = 4 := by
  have pageBound : index / 64 < 128 ^ 4 := by omega
  simpa [route] using Nat.length_digitsAppend (by decide : 1 < 128) 4 pageBound

theorem route_digit (index digit : Nat) (member : digit ∈ route index) : digit < 128 := by
  exact Nat.lt_of_mem_digitsAppend (by decide : 1 < 128) 4 digit (by simpa [route] using member)

theorem offset_bound (index : Nat) : offset index < 64 := Nat.mod_lt _ (by decide)

theorem route_offset_recovers (index : Nat) :
    Nat.ofDigits 128 (route index).reverse * 64 + offset index = index := by
  simp only [route, List.reverse_reverse, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
    Nat.ofDigits_digits, offset]
  omega

theorem route_offset_injective (left right : Nat)
    (sameRoute : route left = route right) (sameOffset : offset left = offset right) : left = right := by
  have lhs := route_offset_recovers left
  have rhs := route_offset_recovers right
  rw [sameRoute, sameOffset] at lhs
  omega

abbrev Slot (V : Type) := Option Ptr ⊕ V

inductive Kind where
  | directory
  | elements
  deriving DecidableEq, Repr

def Kind.extent : Kind → Nat
  | .directory => 128
  | .elements => 64

def Kind.block (kind : Kind) : Block (Slot V) :=
  ⟨true, match kind with
    | .directory => List.replicate 128 (some (.inl none))
    | .elements => List.replicate 64 none⟩

/-- This explicitly named fixed-block allocation/initialization service is
not the malloc primitive. Directory cells contain actual null-pointer values;
element cells have no published typed row. Raw byte zeroing/layout are separate. -/
def calloc (memory : Storage (Slot V)) (kind : Kind) (choice : AllocationChoice) :
    Option (Option Ptr × Storage (Slot V)) := do
  let (result, allocated) ← allocate memory kind.extent choice
  match result with
  | none => some (none, allocated)
  | some pointer => some (some pointer, put allocated pointer.block kind.block)

theorem calloc_failure (memory : Storage (Slot V)) (kind : Kind) :
    calloc memory kind .failure = some (none, memory) := rfl

theorem calloc_fresh (memory : Storage (Slot V)) (kind : Kind) (identity : BlockId)
    (fresh : memory.lookup identity = none) :
    calloc memory kind (.fresh identity) = some (some ⟨identity, 0⟩,
      put (put memory identity ⟨true, List.replicate kind.extent none⟩) identity kind.block) := by
  simp [calloc, allocate, fresh]

theorem load_put_other (memory : Storage V) (identity : BlockId) (block : Block V)
    (address : Ptr) (different : address.block ≠ identity) :
    load (put memory identity block) address = load memory address := by
  simp [load, lookup_put_other memory identity address.block block different]

theorem load_present (memory : Storage V) (address : Ptr) (value : V)
    (loaded : load memory address = some value) :
    ∃ block, memory.lookup address.block = some block ∧ block.live = true ∧ address.offset < block.cells.length := by
  cases found : memory.lookup address.block with
  | none => simp [load, found] at loaded
  | some block =>
      cases live : block.live with
      | false => simp [load, found, live] at loaded
      | true =>
          refine ⟨block, rfl, live, ?_⟩
          by_contra outside
          have absent : block.cells[address.offset]? = none := List.getElem?_eq_none (by omega)
          simp [load, found, live, absent] at loaded

theorem load_store_same (memory next : Storage V) (address : Ptr) (value : V)
    (stored : store memory address value = some next) : load next address = some value := by
  cases found : memory.lookup address.block with
  | none => simp [store, found] at stored
  | some block =>
      by_cases safe : block.live = true ∧ address.offset < block.cells.length
      · simp [store, found, safe] at stored
        subst next
        simp [load, safe]
      · simp [store, found, safe] at stored

theorem load_store_other (memory next : Storage V) (address other : Ptr) (value : V)
    (stored : store memory address value = some next) (different : other ≠ address) :
    load next other = load memory other := by
  cases found : memory.lookup address.block with
  | none => simp [store, found] at stored
  | some block =>
      by_cases safe : block.live = true ∧ address.offset < block.cells.length
      · simp [store, found, safe] at stored
        subst next
        by_cases blockSame : other.block = address.block
        · have offsetDifferent : other.offset ≠ address.offset := by
            intro equal
            exact different (congrArg₂ Ptr.mk blockSame equal)
          simp [load, blockSame, found, safe.1, List.getElem?_set_ne (Ne.symm offsetDifferent)]
        · exact load_put_other memory address.block _ other blockSame
      · simp [store, found, safe] at stored

/-- Null slots may acquire children; existing child pointers and published
rows remain exact. Actual allocation and link writes derive this relation. -/
def CellExtends : Slot V → Slot V → Prop
  | .inl none, after => ∃ child, after = .inl child
  | before, after => after = before

def Extends (before after : Storage (Slot V)) : Prop :=
  ∀ address value, load before address = some value →
    ∃ result, load after address = some result ∧ CellExtends value result

theorem cellExtends_refl (value : Slot V) : CellExtends value value := by
  cases value with
  | inl pointer => cases pointer <;> simp [CellExtends]
  | inr value => rfl

theorem extends_refl (memory : Storage (Slot V)) : Extends memory memory :=
  fun _ value loaded => ⟨value, loaded, cellExtends_refl value⟩

theorem extends_trans (first second third : Storage (Slot V))
    (left : Extends first second) (right : Extends second third) : Extends first third := by
  intro address value loaded
  obtain ⟨middle, found, related⟩ := left address value loaded
  obtain ⟨last, final, next⟩ := right address middle found
  refine ⟨last, final, ?_⟩
  cases value with
  | inr value =>
      change middle = .inr value at related
      subst middle
      exact next
  | inl pointer =>
      cases pointer with
      | none =>
          obtain ⟨child, rfl⟩ := related
          cases child with
          | none => exact next
          | some child =>
              change last = .inl (some child) at next
              exact ⟨some child, next⟩
      | some child =>
          change middle = .inl (some child) at related
          subst middle
          exact next

theorem calloc_extends (memory next : Storage (Slot V)) (kind : Kind)
    (choice : AllocationChoice) (pointer : Option Ptr)
    (executed : calloc memory kind choice = some (pointer, next)) : Extends memory next := by
  cases choice with
  | failure =>
      simp [calloc_failure] at executed
      obtain ⟨rfl, rfl⟩ := executed
      exact extends_refl memory
  | fresh identity =>
      by_cases fresh : memory.lookup identity = none
      · rw [calloc_fresh memory kind identity fresh] at executed
        obtain ⟨rfl, rfl⟩ := executed
        intro address value loaded
        have different : address.block ≠ identity := by
          intro equal
          simp [load, equal, fresh] at loaded
        exact ⟨value, by simpa only [load_put_other _ _ _ _ different] using loaded,
          cellExtends_refl value⟩
      · simp [calloc, allocate, fresh] at executed

theorem null_store_extends (memory next : Storage (Slot V)) (address : Ptr) (child : Ptr)
    (null : load memory address = some (.inl none))
    (stored : store memory address (.inl (some child)) = some next) : Extends memory next := by
  intro other value loaded
  by_cases same : other = address
  · subst other
    have equal : value = .inl none := Option.some.inj (loaded.symm.trans null)
    subst value
    exact ⟨.inl (some child), load_store_same memory next address _ stored, some child, rfl⟩
  · exact ⟨value, (load_store_other memory next address other _ stored same).trans loaded,
      cellExtends_refl value⟩


inductive Seek where
  | ready (leaf : Ptr)
  | missing (slot : Ptr) (suffix : List Nat)
  | refused
  deriving DecidableEq, Repr

/-- Actual nullable directory reads, retaining the first missing child slot.
The suffix determines whether the next fixed block is a directory or a page. -/
def seek (memory : Storage (Slot V)) (pointer : Ptr) : List Nat → Nat × Seek
  | [] => (0, .ready pointer)
  | digit :: rest =>
      match load memory (pointer + digit) with
      | some (.inl none) => (1, .missing (pointer + digit) rest)
      | some (.inl (some child)) =>
          let result := seek memory child rest
          (result.1 + 1, result.2)
      | _ => (1, .refused)

theorem seek_read_bound (memory : Storage (Slot V)) (pointer : Ptr) (path : List Nat) :
    (seek memory pointer path).1 ≤ path.length := by
  induction path generalizing pointer with
  | nil => rfl
  | cons digit rest ih =>
      cases loaded : load memory (pointer + digit) with
      | none => simp [seek, loaded]
      | some value =>
          cases value with
          | inr value => simp [seek, loaded]
          | inl child =>
              cases child with
              | none => simp [seek, loaded]
              | some child => simpa [seek, loaded] using Nat.add_le_add_right (ih child) 1

theorem seek_missing_null (memory : Storage (Slot V)) (pointer slot : Ptr) (path suffix : List Nat)
    (missing : (seek memory pointer path).2 = .missing slot suffix) :
    load memory slot = some (.inl none) := by
  induction path generalizing pointer with
  | nil => simp [seek] at missing
  | cons digit rest ih =>
      cases loaded : load memory (pointer + digit) with
      | none => simp [seek, loaded] at missing
      | some value =>
          cases value with
          | inr value => simp [seek, loaded] at missing
          | inl child =>
              cases child with
              | none =>
                  simp [seek, loaded] at missing
                  simpa [missing.1.symm] using loaded
              | some child => exact ih child (by simpa [seek, loaded] using missing)

theorem seek_ready_of_pointer_reads (before after : Storage (Slot V))
    (kept : ∀ address child, load before address = some (.inl (some child)) →
      load after address = some (.inl (some child)))
    (pointer leaf : Ptr) (path : List Nat) (ready : (seek before pointer path).2 = .ready leaf) :
    (seek after pointer path).2 = .ready leaf := by
  induction path generalizing pointer with
  | nil => simpa [seek] using ready
  | cons digit rest ih =>
      cases loaded : load before (pointer + digit) with
      | none => simp [seek, loaded] at ready
      | some value =>
          cases value with
          | inr value => simp [seek, loaded] at ready
          | inl child =>
              cases child with
              | none => simp [seek, loaded] at ready
              | some child =>
                  have nextRead := kept (pointer + digit) child loaded
                  simpa [seek, nextRead] using ih child (by simpa [seek, loaded] using ready)

theorem seek_ready_extends (before after : Storage (Slot V)) (extension : Extends before after)
    (pointer leaf : Ptr) (path : List Nat) (ready : (seek before pointer path).2 = .ready leaf) :
    (seek after pointer path).2 = .ready leaf := by
  apply seek_ready_of_pointer_reads before after ?_ pointer leaf path ready
  intro address child loaded
  obtain ⟨next, found, same⟩ := extension address (.inl (some child)) loaded
  change next = .inl (some child) at same
  simpa only [same] using found

structure Array (V : Type) where
  memory : Storage (Slot V)
  root : Option Ptr
  chain : List BlockId
  elementSize : Nat
  retiring : Bool
  releasedRev : List BlockId
  deriving Repr, DecidableEq

def Array.empty (size : Nat) : Array V := ⟨[], none, [], size, false, []⟩

/-- Native initialization provides this size admission. The executable
model also rejects malformed records at prepare/access rather than widening
allocator requests. Physical byte layout and alignment are not proved here. -/
def Array.initialize (size : Nat) : Option (Array V) :=
  if 1 ≤ size ∧ size ≤ 256 then some (Array.empty size) else none

theorem Array.initialized_size (size : Nat) (state : Array V)
    (initialized : Array.initialize size = some state) :
    1 ≤ state.elementSize ∧ state.elementSize ≤ 256 := by
  by_cases valid : 1 ≤ size ∧ size ≤ 256
  · simp [Array.initialize, valid] at initialized
    subst state
    exact valid
  · simp [Array.initialize, valid] at initialized

def Array.at (state : Array V) (index : Nat) : Option Ptr :=
  if state.elementSize = 0 ∨ 256 < state.elementSize ∨ state.retiring = true ∨ 2 ^ 32 ≤ index then none else
    state.root.bind fun root => match (seek state.memory root (route index)).2 with
    | .ready leaf => some (leaf + offset index)
    | _ => none

/-- Indeterminate rows and unprepared backing both have no typed read.
Neither result declares logical sequence exhaustion. -/
def Array.read (state : Array V) (index : Nat) : Option V := do
  let address ← state.at index
  match load state.memory address with
  | some (.inr value) => some value
  | _ => none

def Array.write (state : Array V) (index : Nat) (value : V) : Option (Array V) := do
  let address ← state.at index
  let updated ← store state.memory address (.inr value)
  pure { state with memory := updated }

inductive Status where
  | pending
  | ready
  | refused
  deriving DecidableEq, Repr

structure Prepared (V : Type) where
  status : Status
  next : Array V
  reads : Nat
  request : Option Kind
  installed : Bool

/-- Install at most one initialized fixed block. Even a malformed link
refusal retains the allocated block on the owned chain; it cannot leak it.
The actual missing-slot premise below proves that link refusal unreachable. -/
def Array.install (state : Array V) (slot : Option Ptr) (kind : Kind)
    (choice : AllocationChoice) (reads : Nat) : Prepared V :=
  match calloc state.memory kind choice with
  | none => ⟨.refused, state, reads, some kind, false⟩
  | some (none, _) => ⟨.refused, state, reads, some kind, false⟩
  | some (some pointer, memory) =>
      let held := { state with memory := memory, chain := pointer.block :: state.chain }
      match slot with
      | none => ⟨.pending, { held with root := some pointer }, reads, some kind, true⟩
      | some slot =>
          match store memory slot (.inl (some pointer)) with
          | none => ⟨.refused, held, reads, some kind, true⟩
          | some updated => ⟨.pending, { held with memory := updated }, reads, some kind, true⟩

def Array.prepare (state : Array V) (index : Nat) (choice : AllocationChoice) : Prepared V :=
  if state.elementSize = 0 ∨ 256 < state.elementSize ∨ state.retiring = true ∨ 2 ^ 32 ≤ index then ⟨.refused, state, 0, none, false⟩
  else match state.root with
  | none => state.install none .directory choice 0
  | some root =>
      let observed := seek state.memory root (route index)
      match observed.2 with
      | .ready _ => ⟨.ready, state, observed.1, none, false⟩
      | .refused => ⟨.refused, state, observed.1, none, false⟩
      | .missing slot suffix => state.install (some slot)
          (if suffix.isEmpty then .elements else .directory) choice observed.1

theorem Array.failure_keeps_residual (state : Array V) (index : Nat) :
    (state.prepare index .failure).next = state := by
  simp only [Array.prepare]
  split
  · rfl
  · cases root : state.root with
    | none => simp [Array.install, calloc_failure]
    | some pointer => cases observed : (seek state.memory pointer (route index)).2 <;>
        simp [observed, Array.install, calloc_failure]

theorem Array.install_reads (state : Array V) (slot : Option Ptr) (kind : Kind)
    (choice : AllocationChoice) (reads : Nat) : (state.install slot kind choice reads).reads = reads := by
  cases allocated : calloc state.memory kind choice with
  | none => simp [Array.install, allocated]
  | some result =>
      rcases result with ⟨pointer, memory⟩
      cases pointer with
      | none => simp [Array.install, allocated]
      | some pointer =>
          cases slot with
          | none => simp [Array.install, allocated]
          | some address => cases stored : store memory address (.inl (some pointer)) <;>
              simp [Array.install, allocated, stored]

theorem Array.reads_bound (state : Array V) (index : Nat) (choice : AllocationChoice) :
    (state.prepare index choice).reads ≤ 4 := by
  simp only [Array.prepare]
  split
  · exact Nat.zero_le _
  · rename_i admitted
    have bounded : index < 2 ^ 32 := by omega
    have length := route_length index bounded
    cases root : state.root with
    | none => rw [Array.install_reads]; decide
    | some pointer =>
        have limited := seek_read_bound state.memory pointer (route index)
        rw [length] at limited
        cases observed : (seek state.memory pointer (route index)).2 with
        | ready leaf => simpa only [observed] using limited
        | refused => simpa only [observed] using limited
        | missing slot suffix => simpa only [observed, Array.install_reads] using limited

/-- Both possible request extents are fixed independently of initialized
length or highest index. The allocator and ABI remain named service seams. -/
def Kind.requestBytes (header pointerBytes elementSize : Nat) : Kind → Nat
  | .directory => header + 128 * pointerBytes
  | .elements => header + 64 * elementSize

theorem fixed_request_bound (kind : Kind) (header pointerBytes elementSize : Nat)
    (sizeBound : elementSize ≤ 256) :
    kind.requestBytes header pointerBytes elementSize ≤ header + max (128 * pointerBytes) 16384 := by
  cases kind <;> simp only [Kind.requestBytes] <;> omega


theorem calloc_keeps_old_load (memory next : Storage (Slot V)) (kind : Kind)
    (choice : AllocationChoice) (pointer : Option Ptr)
    (executed : calloc memory kind choice = some (pointer, next))
    (address : Ptr) (value : Slot V) (loaded : load memory address = some value) :
    load next address = some value := by
  cases choice with
  | failure =>
      simp [calloc_failure] at executed
      obtain ⟨rfl, rfl⟩ := executed
      exact loaded
  | fresh identity =>
      by_cases fresh : memory.lookup identity = none
      · rw [calloc_fresh memory kind identity fresh] at executed
        obtain ⟨rfl, rfl⟩ := executed
        have different : address.block ≠ identity := by
          intro equal
          simp [load, equal, fresh] at loaded
        simpa only [load_put_other _ _ _ _ different] using loaded
      · simp [calloc, allocate, fresh] at executed

theorem Array.install_extends (state : Array V) (slot : Option Ptr) (kind : Kind)
    (choice : AllocationChoice) (reads : Nat)
    (empty : ∀ address, slot = some address → load state.memory address = some (.inl none)) :
    Extends state.memory (state.install slot kind choice reads).next.memory := by
  cases allocated : calloc state.memory kind choice with
  | none => simpa [Array.install, allocated] using extends_refl state.memory
  | some result =>
      rcases result with ⟨pointer, memory⟩
      cases pointer with
      | none => simpa [Array.install, allocated] using extends_refl state.memory
      | some pointer =>
          have extension := calloc_extends state.memory memory kind choice (some pointer) allocated
          cases slot with
          | none => simpa [Array.install, allocated] using extension
          | some address =>
              have null := calloc_keeps_old_load state.memory memory kind choice (some pointer) allocated
                address (.inl none) (empty address rfl)
              cases stored : store memory address (.inl (some pointer)) with
              | none => simpa [Array.install, allocated, stored] using extension
              | some next =>
                  simpa [Array.install, allocated, stored] using
                    extends_trans state.memory memory next extension (null_store_extends memory next address pointer null stored)

theorem Array.prepare_extends (state : Array V) (index : Nat) (choice : AllocationChoice) :
    Extends state.memory (state.prepare index choice).next.memory := by
  simp only [Array.prepare]
  split
  · exact extends_refl _
  · cases root : state.root with
    | none => exact state.install_extends none .directory choice 0 (by simp)
    | some pointer =>
        cases observed : (seek state.memory pointer (route index)).2 with
        | ready leaf => simpa only [observed] using extends_refl state.memory
        | refused => simpa only [observed] using extends_refl state.memory
        | missing slot suffix =>
            simp only [observed]
            apply state.install_extends
            intro address equal
            have same : slot = address := Option.some.inj equal
            subst address
            exact seek_missing_null state.memory pointer slot (route index) suffix observed

theorem Array.install_fields (state : Array V) (slot : Option Ptr) (kind : Kind)
    (choice : AllocationChoice) (reads : Nat) :
    let next := (state.install slot kind choice reads).next
    next.elementSize = state.elementSize ∧ next.retiring = state.retiring ∧ next.releasedRev = state.releasedRev ∧
      (slot ≠ none → next.root = state.root) := by
  cases allocated : calloc state.memory kind choice with
  | none => simp [Array.install, allocated]
  | some result =>
      rcases result with ⟨pointer, memory⟩
      cases pointer with
      | none => simp [Array.install, allocated]
      | some pointer =>
          cases slot with
          | none => simp [Array.install, allocated]
          | some address => cases stored : store memory address (.inl (some pointer)) <;>
              simp [Array.install, allocated, stored]

theorem Array.prepare_fields (state : Array V) (index : Nat) (choice : AllocationChoice) :
    let next := (state.prepare index choice).next
    next.elementSize = state.elementSize ∧ next.retiring = state.retiring ∧ next.releasedRev = state.releasedRev ∧
      (state.root ≠ none → next.root = state.root) := by
  simp only [Array.prepare]
  split
  · exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  · cases root : state.root with
    | none =>
        have kept := state.install_fields none .directory choice 0
        exact ⟨kept.1, kept.2.1, kept.2.2.1, by simp⟩
    | some pointer =>
        cases observed : (seek state.memory pointer (route index)).2 with
        | ready leaf => simp [observed, root]
        | refused => simp [observed, root]
        | missing slot suffix =>
            have kept := state.install_fields (some slot) (if suffix.isEmpty then .elements else .directory)
              choice (seek state.memory pointer (route index)).1
            simp only [observed]
            exact ⟨kept.1, kept.2.1, kept.2.2.1, fun _ => (kept.2.2.2 (by simp)).trans root⟩

/-- Earlier prepared element addresses do not move when another directory
or page is installed. No reallocation or table-copy premise is supplied. -/
theorem Array.prepare_preserves_at (state : Array V) (target index : Nat) (choice : AllocationChoice)
    (address : Ptr) (prepared : state.at index = some address) :
    (state.prepare target choice).next.at index = some address := by
  have extension := state.prepare_extends target choice
  have fields := state.prepare_fields target choice
  by_cases invalid : state.elementSize = 0 ∨ 256 < state.elementSize ∨ state.retiring = true ∨ 2 ^ 32 ≤ index
  · simp only [Array.at, if_pos invalid, reduceCtorEq] at prepared
  · simp only [Array.at, if_neg invalid] at prepared
    cases root : state.root with
    | none => simp [root] at prepared
    | some pointer =>
        have rootKept := fields.2.2.2 (by simp [root])
        cases observed : (seek state.memory pointer (route index)).2 with
        | refused => simp [root, observed] at prepared
        | missing slot suffix => simp [root, observed] at prepared
        | ready leaf =>
            have ready := seek_ready_extends state.memory (state.prepare target choice).next.memory extension
              pointer leaf (route index) observed
            simp only [Array.at, fields.1, fields.2.1, if_neg invalid, rootKept, root, Option.bind_some, ready]
            simpa only [root, Option.bind_some, observed] using prepared

theorem Array.prepare_preserves_read (state : Array V) (target index : Nat) (choice : AllocationChoice)
    (value : V) (read : state.read index = some value) :
    (state.prepare target choice).next.read index = some value := by
  cases location : state.at index with
  | none => simp [Array.read, location] at read
  | some address =>
      cases loaded : load state.memory address with
      | none => simp [Array.read, location, loaded] at read
      | some entry =>
          cases entry with
          | inl pointer => simp [Array.read, location, loaded] at read
          | inr entry =>
              have same : entry = value := by simpa [Array.read, location, loaded] using read
              subst entry
              have ready := state.prepare_preserves_at target index choice address location
              obtain ⟨new, found, equal⟩ := state.prepare_extends target choice address (.inr value) loaded
              change new = .inr value at equal
              subst new
              simp [Array.read, ready, found]


theorem Array.request_config (state : Array V) (index : Nat) (choice : AllocationChoice)
    (kind : Kind) (requested : (state.prepare index choice).request = some kind) :
    1 ≤ state.elementSize ∧ state.elementSize ≤ 256 := by
  by_cases invalid : state.elementSize = 0 ∨ 256 < state.elementSize ∨ state.retiring = true ∨ 2 ^ 32 ≤ index
  · simp only [Array.prepare, if_pos invalid, reduceCtorEq] at requested
  · omega

theorem Array.actual_request_bound (state : Array V) (index : Nat) (choice : AllocationChoice)
    (kind : Kind) (requested : (state.prepare index choice).request = some kind)
    (header pointerBytes : Nat) :
    kind.requestBytes header pointerBytes state.elementSize ≤ header + max (128 * pointerBytes) 16384 :=
  fixed_request_bound kind header pointerBytes state.elementSize (state.request_config index choice kind requested).2

theorem calloc_allocated (memory next : Storage (Slot V)) (kind : Kind)
    (choice : AllocationChoice) (pointer : Ptr)
    (executed : calloc memory kind choice = some (some pointer, next)) :
    pointer.offset = 0 ∧ memory.lookup pointer.block = none ∧ next.lookup pointer.block = some kind.block := by
  cases choice with
  | failure => simp [calloc_failure] at executed
  | fresh identity =>
      by_cases fresh : memory.lookup identity = none
      · rw [calloc_fresh memory kind identity fresh] at executed
        obtain ⟨rfl, rfl⟩ := executed
        exact ⟨rfl, fresh, by simp⟩
      · simp [calloc, allocate, fresh] at executed

/-- Filling the first absent slot exposes exactly that new suffix. All
previously read nonnull pointers are retained by the proved extension. -/
theorem seek_link_suffix (before after : Storage (Slot V)) (extension : Extends before after)
    (pointer slot child : Ptr) (path suffix : List Nat)
    (missing : (seek before pointer path).2 = .missing slot suffix)
    (linked : load after slot = some (.inl (some child))) :
    (seek after pointer path).2 = (seek after child suffix).2 := by
  induction path generalizing pointer with
  | nil => simp [seek] at missing
  | cons digit rest ih =>
      cases loaded : load before (pointer + digit) with
      | none => simp [seek, loaded] at missing
      | some value =>
          cases value with
          | inr value => simp [seek, loaded] at missing
          | inl next =>
              cases next with
              | none =>
                  have same : pointer + digit = slot ∧ rest = suffix := by simpa [seek, loaded] using missing
                  simp [seek, same.1, same.2, linked]
              | some next =>
                  obtain ⟨result, nextRead, equal⟩ := extension (pointer + digit) _ loaded
                  change result = .inl (some next) at equal
                  subst result
                  simpa [seek, nextRead] using ih next (by simpa [seek, loaded] using missing)


theorem store_available (memory : Storage V) (address : Ptr) (before value : V)
    (loaded : load memory address = some before) : ∃ next, store memory address value = some next := by
  obtain ⟨block, found, live, inside⟩ := load_present memory address before loaded
  exact ⟨put memory address.block { block with cells := block.cells.set address.offset (some value) },
    by simp [store, found, live, inside]⟩

def grown (memory : Storage (Slot V)) (kind : Kind) (identity : BlockId) : Storage (Slot V) :=
  put (put memory identity ⟨true, List.replicate kind.extent none⟩) identity kind.block

theorem directory_null (memory : Storage (Slot V)) (identity digit : Nat)
    (present : memory.lookup identity = some Kind.directory.block) (inside : digit < 128) :
    load memory ((⟨identity, 0⟩ : Ptr) + digit) = some (.inl none) := by
  simp only [load, Ptr.add_block, Ptr.add_offset, Nat.zero_add, present, Kind.block]
  change ((List.replicate 128 (some (.inl none) : Option (Slot V)))[digit]?).join = _
  rw [List.getElem?_replicate, if_pos inside]
  rfl

/-- A successful allocation at a genuinely missing link cannot fail its
constant parent write. The allocated child stays private and owned. -/
theorem Array.fresh_link (state : Array V) (slot : Ptr) (kind : Kind) (identity reads : Nat)
    (fresh : state.memory.lookup identity = none) (null : load state.memory slot = some (.inl none)) :
    ∃ memory, store (grown state.memory kind identity) slot (.inl (some ⟨identity, 0⟩)) = some memory ∧
      state.install (some slot) kind (.fresh identity) reads =
        ⟨.pending, { state with memory := memory, chain := identity :: state.chain }, reads, some kind, true⟩ ∧
      Extends state.memory memory ∧ memory.lookup identity = some kind.block := by
  have allocated := calloc_fresh state.memory kind identity fresh
  change calloc state.memory kind (.fresh identity) = some (some ⟨identity, 0⟩, grown state.memory kind identity) at allocated
  have loaded := calloc_keeps_old_load state.memory (grown state.memory kind identity) kind (.fresh identity)
    (some ⟨identity, 0⟩) allocated slot (.inl none) null
  obtain ⟨memory, stored⟩ := store_available (grown state.memory kind identity) slot (.inl none) (.inl (some ⟨identity, 0⟩)) loaded
  have extension := extends_trans state.memory (grown state.memory kind identity) memory
    (calloc_extends _ _ _ _ _ allocated) (null_store_extends _ _ slot ⟨identity, 0⟩ loaded stored)
  have different : slot.block ≠ identity := by
    intro equal
    simp [load, equal, fresh] at null
  have kept : memory.lookup identity = some kind.block := by
    cases blockFound : (grown state.memory kind identity).lookup slot.block with
    | none => simp [store, blockFound] at stored
    | some block =>
        by_cases valid : block.live = true ∧ slot.offset < block.cells.length
        · simp [store, blockFound, valid] at stored
          subst memory
          rw [lookup_put_other _ _ _ _ (Ne.symm different)]
          simp [grown]
        · simp [store, blockFound, valid] at stored
  exact ⟨memory, stored, by simp [Array.install, allocated, stored], extension, kept⟩

theorem seek_missing_suffix_digits (memory : Storage (Slot V)) (pointer slot : Ptr) (path suffix : List Nat)
    (missing : (seek memory pointer path).2 = .missing slot suffix) :
    ∀ digit ∈ suffix, digit ∈ path := by
  induction path generalizing pointer with
  | nil => simp [seek] at missing
  | cons first rest ih =>
      cases loaded : load memory (pointer + first) with
      | none => simp [seek, loaded] at missing
      | some value =>
          cases value with
          | inr value => simp [seek, loaded] at missing
          | inl child =>
              cases child with
              | none =>
                  have same : pointer + first = slot ∧ rest = suffix := by simpa [seek, loaded] using missing
                  intro digit member
                  simp only [List.mem_cons]
                  exact Or.inr (same.2.symm ▸ member)
              | some child =>
                  have selected := ih child (by simpa [seek, loaded] using missing)
                  exact fun digit member => List.mem_cons_of_mem first (selected digit member)

def Array.remainingInstalls (state : Array V) (index : Nat) : Option Nat :=
  if state.elementSize = 0 ∨ 256 < state.elementSize ∨ state.retiring = true ∨ 2 ^ 32 ≤ index then none
  else match state.root with
  | none => some 5
  | some pointer => match (seek state.memory pointer (route index)).2 with
    | .ready _ => some 0
    | .missing _ suffix => some (suffix.length + 1)
    | .refused => none


/-- A successful fresh allocation reduces the actual missing suffix by one.
The final READY observation is deliberately a later call. -/
theorem Array.prepare_progress (state : Array V) (index identity count : Nat)
    (remaining : state.remainingInstalls index = some (count + 1))
    (fresh : state.memory.lookup identity = none) :
    (state.prepare index (.fresh identity)).status = .pending ∧
      (state.prepare index (.fresh identity)).next.remainingInstalls index = some count ∧
      (state.prepare index (.fresh identity)).next.chain.length = state.chain.length + 1 := by
  by_cases invalid : state.elementSize = 0 ∨ 256 < state.elementSize ∨ state.retiring = true ∨ 2 ^ 32 ≤ index
  · simp only [Array.remainingInstalls, if_pos invalid, reduceCtorEq] at remaining
  · have bounded : index < 2 ^ 32 := by omega
    cases root : state.root with
    | none =>
        have countEq : count = 4 := by
          simp only [Array.remainingInstalls, if_neg invalid, root, Option.some.injEq] at remaining
          omega
        have actual : state.prepare index (.fresh identity) =
            ⟨.pending, { state with
              memory := grown state.memory .directory identity
              root := some ⟨identity, 0⟩
              chain := identity :: state.chain }, 0, some .directory, true⟩ := by
          simp only [Array.prepare, if_neg invalid, root, Array.install, calloc_fresh state.memory .directory identity fresh, grown]
        rw [actual]
        refine ⟨rfl, ?_, by simp⟩
        have length := route_length index bounded
        cases path : route index with
        | nil => simp [path] at length
        | cons digit rest =>
            have digitBound := route_digit index digit (by simp [path])
            have found := directory_null (grown state.memory .directory identity) identity digit (by simp [grown]) digitBound
            have restLength : rest.length = 3 := by simpa [path] using length
            simp only [Array.remainingInstalls, if_neg invalid, seek, path, found]
            simp only [countEq, restLength]
    | some pointer =>
        cases observed : (seek state.memory pointer (route index)).2 with
        | ready leaf =>
            simp only [Array.remainingInstalls, if_neg invalid, root, observed, Option.some.injEq] at remaining
            omega
        | refused => simp only [Array.remainingInstalls, if_neg invalid, root, observed, reduceCtorEq] at remaining
        | missing slot suffix =>
            have countEq : count = suffix.length := by
              simp only [Array.remainingInstalls, if_neg invalid, root, observed, Option.some.injEq] at remaining
              omega
            have null := seek_missing_null state.memory pointer slot (route index) suffix observed
            obtain ⟨memory, stored, installed, extension, newBlock⟩ :=
              state.fresh_link slot (if suffix.isEmpty then .elements else .directory) identity
                (seek state.memory pointer (route index)).1 fresh null
            have actual : state.prepare index (.fresh identity) =
                ⟨.pending, { state with memory := memory, chain := identity :: state.chain },
                  (seek state.memory pointer (route index)).1,
                  some (if suffix.isEmpty then .elements else .directory), true⟩ := by
              simpa only [Array.prepare, if_neg invalid, root, observed] using installed
            rw [actual]
            refine ⟨rfl, ?_, by simp⟩
            have linked := load_store_same (grown state.memory (if suffix.isEmpty then .elements else .directory) identity)
              memory slot (.inl (some ⟨identity, 0⟩)) stored
            have newSeek := seek_link_suffix state.memory memory extension pointer slot ⟨identity, 0⟩
              (route index) suffix observed linked
            cases suffix with
            | nil =>
                simp only [seek] at newSeek
                simp only [Array.remainingInstalls, if_neg invalid, root, newSeek, countEq, List.length_nil]
            | cons digit rest =>
                have digitBound : digit < 128 := route_digit index digit
                  (seek_missing_suffix_digits state.memory pointer slot (route index) (digit :: rest) observed digit (by simp))
                have directory : memory.lookup identity = some Kind.directory.block := by simpa using newBlock
                have read := directory_null memory identity digit directory digitBound
                simp only [seek, read] at newSeek
                simp only [Array.remainingInstalls, if_neg invalid, root, newSeek, countEq, List.length_cons]


theorem calloc_keeps_old_block (memory next : Storage (Slot V)) (kind : Kind)
    (choice : AllocationChoice) (pointer : Option Ptr)
    (executed : calloc memory kind choice = some (pointer, next)) (identity : BlockId)
    (block : Block (Slot V)) (present : memory.lookup identity = some block) :
    next.lookup identity = some block := by
  cases choice with
  | failure =>
      simp [calloc_failure] at executed
      obtain ⟨rfl, rfl⟩ := executed
      exact present
  | fresh freshId =>
      by_cases fresh : memory.lookup freshId = none
      · rw [calloc_fresh memory kind freshId fresh] at executed
        obtain ⟨rfl, rfl⟩ := executed
        have different : identity ≠ freshId := by intro equal; simp [equal, fresh] at present
        simpa only [lookup_put_other _ _ _ _ different] using present
      · simp [calloc, allocate, fresh] at executed

theorem store_keeps_live (memory next : Storage V) (address : Ptr) (value : V)
    (stored : store memory address value = some next) (identity : BlockId)
    (block : Block V) (present : memory.lookup identity = some block) (live : block.live = true) :
    ∃ after, next.lookup identity = some after ∧ after.live = true := by
  cases found : memory.lookup address.block with
  | none => simp [store, found] at stored
  | some target =>
      by_cases valid : target.live = true ∧ address.offset < target.cells.length
      · simp [store, found, valid] at stored
        subst next
        by_cases same : identity = address.block
        · subst identity
          have equal : target = block := Option.some.inj (found.symm.trans present)
          subst target
          exact ⟨{ block with cells := block.cells.set address.offset (some value) }, by simp [live], live⟩
        · exact ⟨block, (lookup_put_other _ _ _ _ same).trans present, live⟩
      · simp [store, found, valid] at stored

def ChainValid (memory : Storage (Slot V)) (chain : List BlockId) : Prop :=
  chain.Nodup ∧ ∀ identity ∈ chain, ∃ block, memory.lookup identity = some block ∧ block.live = true

def Array.Valid (state : Array V) : Prop := ChainValid state.memory state.chain

theorem Array.empty_valid (size : Nat) : (Array.empty (V := V) size).Valid := by
  simp [Array.Valid, ChainValid, Array.empty]

theorem calloc_chain_valid (memory next : Storage (Slot V)) (kind : Kind)
    (choice : AllocationChoice) (pointer : Ptr)
    (executed : calloc memory kind choice = some (some pointer, next))
    (chain : List BlockId) (valid : ChainValid memory chain) : ChainValid next (pointer.block :: chain) := by
  have fresh := calloc_allocated memory next kind choice pointer executed
  constructor
  · apply List.nodup_cons.mpr
    refine ⟨?_, valid.1⟩
    intro member
    obtain ⟨block, present, _live⟩ := valid.2 pointer.block member
    rw [fresh.2.1] at present
    cases present
  · intro identity member
    rcases List.mem_cons.mp member with same | previous
    · subst identity
      exact ⟨kind.block, fresh.2.2, rfl⟩
    · obtain ⟨block, present, live⟩ := valid.2 identity previous
      exact ⟨block, calloc_keeps_old_block memory next kind choice (some pointer) executed identity block present, live⟩

theorem store_chain_valid (memory next : Storage (Slot V)) (address : Ptr) (value : Slot V)
    (stored : store memory address value = some next) (chain : List BlockId)
    (valid : ChainValid memory chain) : ChainValid next chain := by
  refine ⟨valid.1, ?_⟩
  intro identity member
  obtain ⟨block, present, live⟩ := valid.2 identity member
  exact store_keeps_live memory next address value stored identity block present live

theorem Array.install_valid (state : Array V) (slot : Option Ptr) (kind : Kind)
    (choice : AllocationChoice) (reads : Nat) (valid : state.Valid) :
    (state.install slot kind choice reads).next.Valid := by
  cases allocated : calloc state.memory kind choice with
  | none => simpa [Array.install, allocated] using valid
  | some result =>
      rcases result with ⟨pointer, memory⟩
      cases pointer with
      | none => simpa [Array.install, allocated] using valid
      | some pointer =>
          have held := calloc_chain_valid state.memory memory kind choice pointer allocated state.chain valid
          cases slot with
          | none => simpa [Array.install, allocated, Array.Valid] using held
          | some address =>
              cases stored : store memory address (.inl (some pointer)) with
              | none => simpa [Array.install, allocated, stored, Array.Valid] using held
              | some next =>
                  simpa [Array.install, allocated, stored, Array.Valid] using
                    store_chain_valid memory next address (.inl (some pointer)) stored (pointer.block :: state.chain) held

theorem Array.prepare_valid (state : Array V) (index : Nat) (choice : AllocationChoice)
    (valid : state.Valid) : (state.prepare index choice).next.Valid := by
  simp only [Array.prepare]
  split
  · exact valid
  · cases root : state.root with
    | none => exact state.install_valid none .directory choice 0 valid
    | some pointer =>
        cases observed : (seek state.memory pointer (route index)).2 with
        | ready leaf => simpa only [observed] using valid
        | refused => simpa only [observed] using valid
        | missing slot suffix =>
            simpa only [observed] using
              (state.install_valid (some slot) (if suffix.isEmpty then .elements else .directory)
                choice (seek state.memory pointer (route index)).1 valid)

structure Released (V : Type) where
  status : Status
  next : Array V
  freed : Option BlockId

/-- Root revocation and one allocation-chain free. There is no tree walk
and no payload destructor in this backing-store operation. The client must
finish payload disposal before invoking it. Release history is a logical
observer, separate from the zeroed native array header. -/
def Array.releaseOne (state : Array V) : Released V :=
  let stopped := { state with root := none, retiring := true }
  match state.chain with
  | [] => ⟨.ready, { stopped with elementSize := 0, retiring := false }, none⟩
  | identity :: rest =>
      match free state.memory (some ⟨identity, 0⟩) with
      | none => ⟨.refused, stopped, none⟩
      | some memory =>
          ⟨(if rest.isEmpty then .ready else .pending),
            { stopped with memory := memory, chain := rest
                           elementSize := if rest.isEmpty then 0 else state.elementSize
                           retiring := !rest.isEmpty
                           releasedRev := identity :: state.releasedRev }, some identity⟩

theorem Array.release_valid (state : Array V) (valid : state.Valid) : state.releaseOne.next.Valid := by
  cases chain : state.chain with
  | nil => simp [Array.releaseOne, chain, Array.Valid, ChainValid]
  | cons identity rest =>
      obtain ⟨block, present, live⟩ := valid.2 identity (by simp [chain])
      have distinct := List.nodup_cons.mp (show (identity :: rest).Nodup from chain ▸ valid.1)
      have freed : free state.memory (some ⟨identity, 0⟩) = some (put state.memory identity { block with live := false }) := by
        simp [free, present, live]
      simp only [Array.releaseOne, chain, freed]
      refine ⟨distinct.2, ?_⟩
      intro other member
      have different : other ≠ identity := by intro equal; exact distinct.1 (equal ▸ member)
      obtain ⟨otherBlock, found, alive⟩ := valid.2 other (by simp [chain, member])
      exact ⟨otherBlock, (lookup_put_other _ _ _ _ different).trans found, alive⟩

theorem Array.release_count (state : Array V) (valid : state.Valid) :
    state.releaseOne.next.chain.length + (if state.releaseOne.freed.isSome then 1 else 0) = state.chain.length ∧
      state.releaseOne.status ≠ .refused := by
  cases chain : state.chain with
  | nil => simp [Array.releaseOne, chain]
  | cons identity rest =>
      obtain ⟨block, present, live⟩ := valid.2 identity (by simp [chain])
      cases rest <;> simp [Array.releaseOne, chain, free, present, live]

theorem Array.release_revokes_at (state : Array V) (index : Nat) : state.releaseOne.next.at index = none := by
  cases chain : state.chain with
  | nil => simp [Array.releaseOne, chain, Array.at]
  | cons identity rest =>
      cases freed : free state.memory (some ⟨identity, 0⟩) <;>
        simp [Array.releaseOne, chain, freed, Array.at]


def Array.retirementWord (state : Array V) : List BlockId := state.releasedRev.reverse ++ state.chain

theorem Array.release_order (state : Array V) (valid : state.Valid) :
    state.releaseOne.next.retirementWord = state.retirementWord := by
  cases chain : state.chain with
  | nil => simp [Array.releaseOne, chain, Array.retirementWord]
  | cons identity rest =>
      obtain ⟨block, present, live⟩ := valid.2 identity (by simp [chain])
      simp [Array.releaseOne, chain, free, present, live, Array.retirementWord, List.append_assoc]

theorem Array.release_complete (state : Array V) (valid : state.Valid)
    (complete : state.releaseOne.status = .ready) :
    state.releaseOne.next.chain = [] ∧ state.releaseOne.next.root = none ∧
      state.releaseOne.next.elementSize = 0 := by
  cases chain : state.chain with
  | nil => simp [Array.releaseOne, chain]
  | cons identity rest =>
      obtain ⟨block, present, live⟩ := valid.2 identity (by simp [chain])
      cases rest <;> simp_all [Array.releaseOne, free]

open Mettapedia.TypeTheory Mettapedia.Machines.Cursor

/-- Both instances below drive actual storage operations through the
existing cursor. No precomputed allocation/disposal word is interpreted. -/
def protocol : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Unit
  Position _ := Status
  next _ _ := ()

def client : Client (P := protocol) (Return := fun _ _ => Status) where
  V _ _ := Option Status
  str := fun _ _ => TypeCat.ofHom (fun control => match control with
    | none => ⟨.inr (), fun (status : Status) => if status = .pending then none else some status⟩
    | some status => ⟨.inl status, fun impossible => nomatch impossible⟩)

def Array.releaseProvider : Provider protocol where
  State _ _ := Array V
  step state _ := ⟨state.releaseOne.status, state.releaseOne.next⟩

def Array.releaseCharge : Charge (Array.releaseProvider (V := V)) :=
  fun state _ => if state.releaseOne.freed.isSome then 1 else 0

def Array.releasePacket (state : Array V) : Packet (Array.releaseProvider (V := V)) client () := ⟨(), none, state⟩

def Array.releaseRun (fuel : Nat) (state : Array V) :=
  advance Array.releaseProvider client Array.releaseCharge fuel state.releasePacket

theorem Array.release_zero (state : Array V) : state.releaseRun 0 = (0, .paused state.releasePacket) := rfl

theorem Array.release_split (state : Array V) (first later : Nat) :
    state.releaseRun (first + later) = resume Array.releaseProvider client Array.releaseCharge later (state.releaseRun first) :=
  advance_add _ _ _ first later state.releasePacket

private theorem client_poll : client.str () () none =
    ⟨.inr (), fun (status : Status) => if status = .pending then none else some status⟩ := by
  unfold client
  dsimp only
  simp only [TypeCat.ofHom, CategoryTheory.ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  rfl

private theorem client_done (status : Status) : client.str () () (some status) =
    ⟨.inl status, fun impossible => nomatch impossible⟩ := by
  unfold client
  dsimp only
  simp only [TypeCat.ofHom, CategoryTheory.ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  congr 1
  funext impossible
  cases impossible

private theorem release_advance (state : Array V) (fuel : Nat) :
    advance Array.releaseProvider client Array.releaseCharge (fuel + 1) (base := ()) ⟨(), none, state⟩ =
      let response := state.releaseOne
      let rest := advance Array.releaseProvider client Array.releaseCharge fuel
        (base := ()) ⟨(), if response.status = .pending then none else some response.status, response.next⟩
      ((if response.freed.isSome then 1 else 0) + rest.1, rest.2) := by
  simp only [advance, client_poll]
  rfl

private theorem release_done (state : Array V) (fuel : Nat) (status : Status) :
    advance Array.releaseProvider client Array.releaseCharge (fuel + 1) (base := ()) ⟨(), some status, state⟩ =
      (0, .done ⟨(), status, state⟩) := by
  simp only [advance, client_done]

/-- Finite live block chains are actually freed exactly once in their chain
order. Opaque payloads are absent from this backing-store instance. -/
theorem Array.release_finite (state : Array V) (valid : state.Valid) (fuel : Nat)
    (enough : state.chain.length + 2 ≤ fuel) :
    ∃ final, state.releaseRun fuel = (state.chain.length, .done ⟨(), .ready, final⟩) ∧
      final.Valid ∧ final.chain = [] ∧ final.root = none ∧ final.elementSize = 0 ∧
      final.releasedRev.reverse = state.retirementWord := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      have positive : 0 < fuel := by omega
      have kept := state.release_valid valid
      have balance := (state.release_count valid).1
      have notRefused := (state.release_count valid).2
      have order := state.release_order valid
      cases result : state.releaseOne.status with
      | refused => exact False.elim (notRefused result)
      | ready =>
          obtain ⟨empty, root, size⟩ := state.release_complete valid result
          refine ⟨state.releaseOne.next, ?_, kept, empty, root, size, ?_⟩
          · cases fuel with
            | zero => omega
            | succ rest =>
                simp only [Array.releaseRun, Array.releasePacket, release_advance, result,
                  reduceCtorEq, ↓reduceIte, release_done, Nat.add_zero]
                rw [empty, List.length_nil, Nat.zero_add] at balance
                exact Prod.ext balance rfl
          · simpa [Array.retirementWord, empty] using order
      | pending =>
          have nonempty : state.chain ≠ [] := by
            intro empty
            simp [Array.releaseOne, empty] at result
          have one : state.releaseOne.freed.isSome = true := by
            cases chain : state.chain with
            | nil => exact False.elim (nonempty chain)
            | cons identity rest =>
                obtain ⟨block, present, live⟩ := valid.2 identity (by simp [chain])
                simp [Array.releaseOne, chain, free, present, live]
          have room : state.releaseOne.next.chain.length + 2 ≤ fuel := by simp only [one, ↓reduceIte] at balance; omega
          obtain ⟨final, finished, finalValid, empty, root, size, readback⟩ := ih _ kept room
          refine ⟨final, ?_, finalValid, empty, root, size, readback.trans order⟩
          simp only [Array.releaseRun, Array.releasePacket, release_advance, result, ↓reduceIte]
          change ((if state.releaseOne.freed.isSome then 1 else 0) +
            (state.releaseOne.next.releaseRun fuel).1, (state.releaseOne.next.releaseRun fuel).2) = _
          rw [finished]
          exact Prod.ext (by omega) rfl


theorem Array.install_count (state : Array V) (slot : Option Ptr) (kind : Kind)
    (choice : AllocationChoice) (reads : Nat) :
    (state.install slot kind choice reads).next.chain.length =
      state.chain.length + if (state.install slot kind choice reads).installed then 1 else 0 := by
  cases allocated : calloc state.memory kind choice with
  | none => simp [Array.install, allocated]
  | some result =>
      rcases result with ⟨pointer, memory⟩
      cases pointer with
      | none => simp [Array.install, allocated]
      | some pointer =>
          cases slot with
          | none => simp [Array.install, allocated]
          | some address => cases stored : store memory address (.inl (some pointer)) <;>
              simp [Array.install, allocated, stored]

theorem Array.prepare_count (state : Array V) (index : Nat) (choice : AllocationChoice) :
    (state.prepare index choice).next.chain.length =
      state.chain.length + if (state.prepare index choice).installed then 1 else 0 := by
  simp only [Array.prepare]
  split
  · rfl
  · cases root : state.root with
    | none => exact state.install_count none .directory choice 0
    | some pointer =>
        cases observed : (seek state.memory pointer (route index)).2 with
        | ready leaf => simp [observed]
        | refused => simp [observed]
        | missing slot suffix => simpa only [observed] using
            (state.install_count (some slot) (if suffix.isEmpty then .elements else .directory)
              choice (seek state.memory pointer (route index)).1)

theorem Array.one_install_bound (state : Array V) (index : Nat) (choice : AllocationChoice) :
    (state.prepare index choice).next.chain.length ≤ state.chain.length + 1 := by
  rw [state.prepare_count index choice]
  split <;> omega

theorem Array.remaining_ready (state : Array V) (index : Nat) (choice : AllocationChoice)
    (remaining : state.remainingInstalls index = some 0) :
    (state.prepare index choice).status = .ready ∧ (state.prepare index choice).next = state := by
  by_cases invalid : state.elementSize = 0 ∨ 256 < state.elementSize ∨ state.retiring = true ∨ 2 ^ 32 ≤ index
  · simp only [Array.remainingInstalls, if_pos invalid, reduceCtorEq] at remaining
  · simp only [Array.remainingInstalls, if_neg invalid] at remaining
    cases root : state.root with
    | none => simp [root] at remaining
    | some pointer =>
        cases observed : (seek state.memory pointer (route index)).2 with
        | ready leaf => simp only [Array.prepare, if_neg invalid, root, observed, and_self]
        | refused => simp [root, observed] at remaining
        | missing slot suffix => simp [root, observed] at remaining

def Array.prepareProvider (index : Nat) (choose : Array V → BlockId) : Provider protocol where
  State _ _ := Array V
  step state _ := ⟨(state.prepare index (.fresh (choose state))).status,
    (state.prepare index (.fresh (choose state))).next⟩

def Array.prepareCharge (index : Nat) (choose : Array V → BlockId) :
    Charge (Array.prepareProvider index choose) :=
  fun state _ => if (state.prepare index (.fresh (choose state))).installed then 1 else 0

def Array.preparePacket (index : Nat) (choose : Array V → BlockId) (state : Array V) :
    Packet (Array.prepareProvider index choose) client () := ⟨(), none, state⟩

def Array.prepareRun (index : Nat) (choose : Array V → BlockId) (fuel : Nat) (state : Array V) :=
  advance (Array.prepareProvider index choose) client (Array.prepareCharge index choose) fuel (state.preparePacket index choose)

theorem Array.prepare_zero (index : Nat) (choose : Array V → BlockId) (state : Array V) :
    state.prepareRun index choose 0 = (0, .paused (state.preparePacket index choose)) := rfl

theorem Array.prepare_split (index : Nat) (choose : Array V → BlockId) (state : Array V) (first later : Nat) :
    state.prepareRun index choose (first + later) =
      resume (Array.prepareProvider index choose) client (Array.prepareCharge index choose) later
        (state.prepareRun index choose first) := advance_add _ _ _ first later (state.preparePacket index choose)

private theorem prepare_advance (index : Nat) (choose : Array V → BlockId) (state : Array V) (fuel : Nat) :
    advance (Array.prepareProvider index choose) client (Array.prepareCharge index choose) (fuel + 1)
      (base := ()) ⟨(), none, state⟩ =
      let response := state.prepare index (.fresh (choose state))
      let rest := advance (Array.prepareProvider index choose) client (Array.prepareCharge index choose) fuel
        (base := ()) ⟨(), if response.status = .pending then none else some response.status, response.next⟩
      ((if response.installed then 1 else 0) + rest.1, rest.2) := by
  simp only [advance, client_poll]
  rfl

private theorem prepare_done (index : Nat) (choose : Array V → BlockId) (state : Array V) (fuel : Nat) (status : Status) :
    advance (Array.prepareProvider index choose) client (Array.prepareCharge index choose) (fuel + 1)
      (base := ()) ⟨(), some status, state⟩ = (0, .done ⟨(), status, state⟩) := by
  simp only [advance, client_done]

/-- A fresh successful-allocation provider completes the actual missing path.
Allocation refusal has a separate inert/retry law; no completion is asserted
for an allocator that refuses forever. Inspection fuel is not native time. -/
theorem Array.prepare_finite (index : Nat) (choose : Array V → BlockId)
    (fresh : ∀ state : Array V, state.memory.lookup (choose state) = none)
    (state : Array V) (valid : state.Valid) (count fuel : Nat)
    (remaining : state.remainingInstalls index = some count) (enough : count + 2 ≤ fuel) :
    ∃ final, state.prepareRun index choose fuel = (count, .done ⟨(), .ready, final⟩) ∧
      final.Valid ∧ final.remainingInstalls index = some 0 ∧ final.chain.length = state.chain.length + count := by
  induction count generalizing state fuel with
  | zero =>
      have ready := state.remaining_ready index (.fresh (choose state)) remaining
      have balance := state.prepare_count index (.fresh (choose state))
      rw [ready.2] at balance
      have notInstalled : (state.prepare index (.fresh (choose state))).installed = false := by
        cases installed : (state.prepare index (.fresh (choose state))).installed <;> simp_all
      cases fuel with
      | zero => omega
      | succ rest =>
          cases rest with
          | zero => omega
          | succ later =>
              refine ⟨state, ?_, valid, remaining, by simp⟩
              simp only [Array.prepareRun, Array.preparePacket, prepare_advance, ready.1,
                reduceCtorEq, ↓reduceIte, ready.2, prepare_done, notInstalled]
  | succ count ih =>
      obtain ⟨pending, smaller, size⟩ := state.prepare_progress index (choose state) count remaining (fresh state)
      have nextValid := state.prepare_valid index (.fresh (choose state)) valid
      have balance := state.prepare_count index (.fresh (choose state))
      have installed : (state.prepare index (.fresh (choose state))).installed = true := by
        cases installed : (state.prepare index (.fresh (choose state))).installed <;> simp_all
      cases fuel with
      | zero => omega
      | succ later =>
          obtain ⟨final, finished, finalValid, done, length⟩ := ih _ nextValid later smaller (by omega)
          refine ⟨final, ?_, finalValid, done, by omega⟩
          simp only [Array.prepareRun, Array.preparePacket, prepare_advance, pending, ↓reduceIte, installed]
          change (1 + ((state.prepare index (.fresh (choose state))).next.prepareRun index choose later).1,
            ((state.prepare index (.fresh (choose state))).next.prepareRun index choose later).2) = _
          rw [finished]
          exact Prod.ext (by omega) rfl


/-- Typed data-slot admission is local: the writable row cell cannot also
be a directory-pointer cell. Native layout/region separation must realize it. -/
def DataCell (memory : Storage (Slot V)) (address : Ptr) : Prop :=
  ∀ child : Option Ptr, load memory address ≠ some (.inl child)

theorem data_store_keeps_pointers (memory next : Storage (Slot V)) (address : Ptr) (value : V)
    (typed : DataCell memory address) (stored : store memory address (.inr value) = some next) :
    ∀ other child, load memory other = some (.inl (some child)) → load next other = some (.inl (some child)) := by
  intro other child loaded
  have different : other ≠ address := by
    intro same
    exact typed (some child) (same ▸ loaded)
  exact (load_store_other memory next address other (.inr value) stored different).trans loaded

theorem Array.at_of_pointer_reads (state next : Array V)
    (root : next.root = state.root) (size : next.elementSize = state.elementSize)
    (retiring : next.retiring = state.retiring)
    (kept : ∀ address child, load state.memory address = some (.inl (some child)) →
      load next.memory address = some (.inl (some child)))
    (index : Nat) (address : Ptr) (before : state.at index = some address) : next.at index = some address := by
  by_cases invalid : state.elementSize = 0 ∨ 256 < state.elementSize ∨ state.retiring = true ∨ 2 ^ 32 ≤ index
  · simp only [Array.at, if_pos invalid, reduceCtorEq] at before
  · simp only [Array.at, if_neg invalid] at before
    cases head : state.root with
    | none => simp [head] at before
    | some pointer =>
        cases observed : (seek state.memory pointer (route index)).2 with
        | refused => simp [head, observed] at before
        | missing slot suffix => simp [head, observed] at before
        | ready leaf =>
            have ready := seek_ready_of_pointer_reads state.memory next.memory kept pointer leaf (route index) observed
            simp only [Array.at, size, retiring, if_neg invalid, root, head, Option.bind_some, ready]
            simpa only [head, Option.bind_some, observed] using before

theorem Array.write_at_preserved (state next : Array V) (index : Nat) (value : V)
    (address : Ptr) (location : state.at index = some address)
    (typed : DataCell state.memory address) (written : state.write index value = some next)
    (other : Nat) (otherAddress : Ptr) (before : state.at other = some otherAddress) :
    next.at other = some otherAddress := by
  cases stored : store state.memory address (.inr value) with
  | none => simp [Array.write, location, stored] at written
  | some memory =>
      have same : { state with memory := memory } = next := by simpa [Array.write, location, stored] using written
      subst next
      exact state.at_of_pointer_reads { state with memory := memory } rfl rfl rfl
        (data_store_keeps_pointers state.memory memory address value typed stored) other otherAddress before

theorem Array.write_read_same (state next : Array V) (index : Nat) (value : V)
    (address : Ptr) (location : state.at index = some address)
    (typed : DataCell state.memory address) (written : state.write index value = some next) :
    next.read index = some value := by
  have after := state.write_at_preserved next index value address location typed written index address location
  cases stored : store state.memory address (.inr value) with
  | none => simp [Array.write, location, stored] at written
  | some memory =>
      have same : { state with memory := memory } = next := by simpa [Array.write, location, stored] using written
      subst next
      have read := load_store_same state.memory memory address (.inr value) stored
      simp [Array.read, after, read]

theorem Array.write_read_other (state next : Array V) (index : Nat) (value : V)
    (address : Ptr) (location : state.at index = some address)
    (typed : DataCell state.memory address) (written : state.write index value = some next)
    (other : Nat) (otherAddress : Ptr) (before : state.at other = some otherAddress)
    (different : otherAddress ≠ address) : next.read other = state.read other := by
  have after := state.write_at_preserved next index value address location typed written other otherAddress before
  cases stored : store state.memory address (.inr value) with
  | none => simp [Array.write, location, stored] at written
  | some memory =>
      have same : { state with memory := memory } = next := by simpa [Array.write, location, stored] using written
      subst next
      have read := load_store_other state.memory memory address otherAddress (.inr value) stored different
      simp [Array.read, after, before, read]


/-- Actual row identity/value is retained separately from an optional owned
key ticket. Equal payloads need not denote the same row occurrence. -/
structure Row (Value Key : Type) where
  ordinal : Nat
  value : Value
  key : Option Key
  deriving DecidableEq, Repr

variable {Value Key : Type}

/-- `todo` is a declared source-index reply word for one pass, not a sorting
algorithm or whole-key comparator. The native merge must realize its legal
index choices. Every step below reads and writes the actual buffer cells. -/
structure Pass (Value Key : Type) where
  primary : Array (Row Value Key)
  scratch : Array (Row Value Key)
  todo : List Nat
  copiedRev : List Nat
  written : Nat
  expected : Nat
  deriving Repr, DecidableEq

def Pass.start (primary scratch : Array (Row Value Key)) (order : List Nat) : Pass Value Key :=
  ⟨primary, scratch, order, [], 0, order.length⟩

def Pass.prepareOne (state : Pass Value Key) (choice : AllocationChoice) : Status × Pass Value Key :=
  let prepared := state.scratch.prepare state.written choice
  (prepared.status, { state with scratch := prepared.next })

/-- One source row read and one destination element write. Allocation is a
separate retained prepare action; refusal keeps the whole source/prefix. -/
def Pass.copyOne (state : Pass Value Key) : Status × Pass Value Key :=
  match state.todo with
  | [] => (.ready, state)
  | index :: rest =>
      match state.primary.read index with
      | none => (.refused, state)
      | some row =>
          match state.scratch.write state.written row with
          | none => (.refused, state)
          | some scratch => (.pending, { state with
              scratch := scratch
              todo := rest
              copiedRev := index :: state.copiedRev
              written := state.written + 1 })

def Pass.Valid (rows : List (Row Value Key)) (order : List Nat) (state : Pass Value Key) : Prop :=
  state.copiedRev.reverse ++ state.todo = order ∧
    state.written = state.copiedRev.length ∧ state.expected = order.length ∧
    (∀ index row, rows[index]? = some row → state.primary.read index = some row) ∧
    (∀ position index, state.copiedRev.reverse[position]? = some index → state.scratch.read position = rows[index]?)

theorem Pass.start_valid (rows : List (Row Value Key)) (order : List Nat)
    (primary scratch : Array (Row Value Key))
    (initialized : ∀ index row, rows[index]? = some row → primary.read index = some row) :
    (Pass.start primary scratch order).Valid rows order := by
  exact ⟨rfl, rfl, rfl, initialized, by simp [Pass.start]⟩

theorem Pass.prepare_valid (state : Pass Value Key) (rows : List (Row Value Key)) (order : List Nat)
    (valid : state.Valid rows order) (legal : order.Perm (List.range rows.length)) (choice : AllocationChoice) :
    (state.prepareOne choice).2.Valid rows order := by
  refine ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1, ?_⟩
  intro position index previous
  have member : index ∈ order := by
    rw [← valid.1]
    exact List.mem_append_left _ (List.mem_of_getElem? previous)
  have bound : index < rows.length := by simpa using legal.mem_iff.mp member
  have expected : rows[index]? = some rows[index] := List.getElem?_eq_getElem bound
  have old := valid.2.2.2.2 position index previous
  rw [expected] at old ⊢
  exact state.scratch.prepare_preserves_read state.written position choice rows[index] old

/-- The write footprint is an independent cell/region admission. It supplies
no completed prefix, permutation or disposal conclusion. -/
def Pass.WriteAdmission (state : Pass Value Key) : Prop :=
  ∀ address, state.scratch.at state.written = some address →
    DataCell state.scratch.memory address ∧
      ∀ position < state.written, ∃ previous, state.scratch.at position = some previous ∧ previous ≠ address

theorem Pass.copy_valid (state : Pass Value Key) (rows : List (Row Value Key)) (order : List Nat)
    (valid : state.Valid rows order) (legal : order.Perm (List.range rows.length))
    (admitted : state.WriteAdmission) : state.copyOne.2.Valid rows order := by
  cases pending : state.todo with
  | nil => simpa [Pass.copyOne, pending] using valid
  | cons selected rest =>
      cases read : state.primary.read selected with
      | none => simpa [Pass.copyOne, pending, read] using valid
      | some row =>
          cases written : state.scratch.write state.written row with
          | none => simpa [Pass.copyOne, pending, read, written] using valid
          | some scratch =>
              have member : selected ∈ order := by
                rw [← valid.1, pending]
                simp
              have bound : selected < rows.length := by simpa using legal.mem_iff.mp member
              have expected : rows[selected]? = some rows[selected] := List.getElem?_eq_getElem bound
              have equal : rows[selected] = row := Option.some.inj ((valid.2.2.2.1 selected rows[selected] expected).symm.trans read)
              have expectedRow : rows[selected]? = some row := expected.trans (congrArg some equal)
              cases location : state.scratch.at state.written with
              | none => simp [Array.write, location] at written
              | some address =>
                  have footprint := admitted address location
                  have newest := state.scratch.write_read_same scratch state.written row address location footprint.1 written
                  simp only [Pass.copyOne, pending, read, written]
                  refine ⟨?_, by simp [valid.2.1], valid.2.2.1, valid.2.2.2.1, ?_⟩
                  · simpa [pending, List.reverse_cons, List.append_assoc] using valid.1
                  · intro position index lookup
                    have length : state.copiedRev.reverse.length = state.written := by simp [valid.2.1]
                    by_cases earlier : position < state.written
                    · have oldLookup : state.copiedRev.reverse[position]? = some index := by
                        have expanded : (state.copiedRev.reverse ++ [selected])[position]? = some index := by
                          simpa only [List.reverse_cons] using lookup
                        rw [List.getElem?_append_left (by omega)] at expanded
                        exact expanded
                      obtain ⟨previous, before, different⟩ := footprint.2 position earlier
                      exact (state.scratch.write_read_other scratch state.written row address location footprint.1 written
                        position previous before different).trans (valid.2.2.2.2 position index oldLookup)
                    · have within : position < state.written + 1 := by
                        have sized := (List.getElem?_eq_some_iff.mp lookup).1
                        simpa [valid.2.1] using sized
                      have samePosition : position = state.written := by omega
                      have sameIndex : index = selected := by
                        simp only [List.reverse_cons] at lookup
                        rw [List.getElem?_append_right (by omega)] at lookup
                        have difference : position - state.copiedRev.reverse.length = 0 := by omega
                        rw [difference] at lookup
                        exact Option.some.inj lookup.symm
                      simpa [samePosition, sameIndex, expectedRow] using newest

structure Buffers (Value Key : Type) where
  primary : Array (Row Value Key)
  scratch : Array (Row Value Key)
  deriving Repr, DecidableEq

/-- Header/owner swap only, after the complete pass. No payload is disposed
and no partially written scratch is promoted to primary. -/
def Pass.swap (state : Pass Value Key) : Option (Buffers Value Key) :=
  if state.todo.isEmpty && decide (state.written = state.expected) then
    some ⟨state.scratch, state.primary⟩ else none

theorem Pass.incomplete_no_swap (state : Pass Value Key) (pending : state.todo ≠ []) : state.swap = none := by
  simp [Pass.swap, pending]

def observed (state : Array V) (count : Nat) : List (Option V) := (List.range count).map state.read

theorem range_reads (values : List V) : (List.range values.length).map (fun index => values[index]?) = values.map some := by
  apply List.ext_getElem?
  intro position
  by_cases inside : position < values.length
  · simp [List.getElem?_map, List.getElem?_range inside, List.getElem?_eq_getElem inside]
  · have absent : values[position]? = none := List.getElem?_eq_none (by omega)
    have absentRange : (List.range values.length)[position]? = none := List.getElem?_eq_none (by simp; omega)
    simp [List.getElem?_map, absent, absentRange]

theorem Pass.completed_readout (state : Pass Value Key) (rows : List (Row Value Key)) (order : List Nat)
    (valid : state.Valid rows order) (complete : state.todo = []) :
    observed state.scratch state.expected = order.map (fun index => rows[index]?) := by
  have written : state.copiedRev.reverse = order := by simpa [complete] using valid.1
  apply List.ext_getElem?
  intro position
  by_cases inside : position < order.length
  · have atOrder : order[position]? = some order[position] := List.getElem?_eq_getElem inside
    have actual := valid.2.2.2.2 position order[position] (by rw [written]; exact atOrder)
    simp [observed, valid.2.2.1, List.getElem?_map, List.getElem?_range inside, atOrder, actual]
  · have absent : order[position]? = none := List.getElem?_eq_none (by omega)
    have absentRange : (List.range state.expected)[position]? = none := List.getElem?_eq_none (by simp [valid.2.2.1]; omega)
    simp [observed, List.getElem?_map, absentRange, absent]

/-- Exact actual-buffer observations, including every ordinal/value and
repeated payload, permute the independent complete source after a legal pass. -/
theorem Pass.completed_permutation (state : Pass Value Key) (rows : List (Row Value Key)) (order : List Nat)
    (valid : state.Valid rows order) (legal : order.Perm (List.range rows.length)) (complete : state.todo = []) :
    (observed state.scratch state.expected).Perm (rows.map some) := by
  rw [state.completed_readout rows order valid complete]
  have permutation := legal.map (fun index => rows[index]?)
  simpa only [range_reads] using permutation


theorem Array.install_not_ready (state : Array V) (slot : Option Ptr) (kind : Kind)
    (choice : AllocationChoice) (reads : Nat) : (state.install slot kind choice reads).status ≠ .ready := by
  cases allocated : calloc state.memory kind choice with
  | none => simp [Array.install, allocated]
  | some result =>
      rcases result with ⟨pointer, memory⟩
      cases pointer with
      | none => simp [Array.install, allocated]
      | some pointer =>
          cases slot with
          | none => simp [Array.install, allocated]
          | some address => cases stored : store memory address (.inl (some pointer)) <;>
              simp [Array.install, allocated, stored]

theorem Array.ready_keeps_residual (state : Array V) (index : Nat) (choice : AllocationChoice)
    (ready : (state.prepare index choice).status = .ready) : (state.prepare index choice).next = state := by
  by_cases invalid : state.elementSize = 0 ∨ 256 < state.elementSize ∨ state.retiring = true ∨ 2 ^ 32 ≤ index
  · simp only [Array.prepare, if_pos invalid, reduceCtorEq] at ready
  · simp only [Array.prepare, if_neg invalid] at ready ⊢
    cases root : state.root with
    | none =>
        simp only [root] at ready ⊢
        exact False.elim (state.install_not_ready none .directory choice 0 ready)
    | some pointer =>
        simp only [root] at ready ⊢
        cases observed : (seek state.memory pointer (route index)).2 with
        | ready leaf => rfl
        | refused => simp [observed] at ready
        | missing slot suffix =>
            simp only [observed] at ready
            exact False.elim (state.install_not_ready (some slot) (if suffix.isEmpty then .elements else .directory)
              choice (seek state.memory pointer (route index)).1 ready)

theorem Pass.prepare_failure_keeps (state : Pass Value Key) : (state.prepareOne .failure).2 = state := by
  simp [Pass.prepareOne, Array.failure_keeps_residual]

theorem Pass.ready_prepare_keeps (state : Pass Value Key) (choice : AllocationChoice)
    (ready : (state.prepareOne choice).1 = .ready) : (state.prepareOne choice).2 = state := by
  have kept := state.scratch.ready_keeps_residual state.written choice ready
  simp [Pass.prepareOne, kept]

/-- Storage preparation and row copying share one actual retained phase:
allocation installs one block and yields; an already prepared slot admits
one row write. No precomputed row vector is sliced into paid prefixes. -/
def Pass.step (state : Pass Value Key) (choice : AllocationChoice) : Status × Pass Value Key :=
  if state.todo.isEmpty then state.copyOne else
    let prepared := state.prepareOne choice
    match prepared.1 with
    | .ready => prepared.2.copyOne
    | other => (other, prepared.2)

theorem Pass.step_valid (state : Pass Value Key) (rows : List (Row Value Key)) (order : List Nat)
    (valid : state.Valid rows order) (legal : order.Perm (List.range rows.length))
    (admitted : state.WriteAdmission) (choice : AllocationChoice) : (state.step choice).2.Valid rows order := by
  simp only [Pass.step]
  split
  · exact state.copy_valid rows order valid legal admitted
  · cases prepared : (state.prepareOne choice).1 with
    | pending => simpa only [prepared] using state.prepare_valid rows order valid legal choice
    | refused => simpa only [prepared] using state.prepare_valid rows order valid legal choice
    | ready =>
        have kept := state.ready_prepare_keeps choice prepared
        simpa only [prepared, kept] using state.copy_valid rows order valid legal admitted

theorem Pass.copy_primary (state : Pass Value Key) : state.copyOne.2.primary = state.primary := by
  cases pending : state.todo with
  | nil => simp [Pass.copyOne, pending]
  | cons index rest =>
      cases read : state.primary.read index with
      | none => simp [Pass.copyOne, pending, read]
      | some row => cases written : state.scratch.write state.written row <;> simp [Pass.copyOne, pending, read, written]

theorem Pass.step_primary (state : Pass Value Key) (choice : AllocationChoice) :
    (state.step choice).2.primary = state.primary := by
  simp only [Pass.step]
  split
  · exact state.copy_primary
  · cases prepared : (state.prepareOne choice).1 with
    | ready => exact (state.prepareOne choice).2.copy_primary
    | pending => rfl
    | refused => rfl

def Pass.provider (choose : Pass Value Key → AllocationChoice) : Provider protocol where
  State _ _ := Pass Value Key
  step state _ := ⟨(state.step (choose state)).1, (state.step (choose state)).2⟩

def Pass.charge (choose : Pass Value Key → AllocationChoice) : Charge (Pass.provider choose) := fun _ _ => 1

def Pass.packet (choose : Pass Value Key → AllocationChoice) (state : Pass Value Key) :
    Packet (Pass.provider choose) client () := ⟨(), none, state⟩

def Pass.run (choose : Pass Value Key → AllocationChoice) (fuel : Nat) (state : Pass Value Key) :=
  advance (Pass.provider choose) client (Pass.charge choose) fuel (state.packet choose)

def Pass.outcomeState (choose : Pass Value Key → AllocationChoice) :
    Outcome (Pass.provider choose) client () → Pass Value Key
  | .paused ⟨(), _, state⟩ => state
  | .done ⟨(), _, state⟩ => state

theorem Pass.zero (choose : Pass Value Key → AllocationChoice) (state : Pass Value Key) :
    state.run choose 0 = (0, .paused (state.packet choose)) := rfl

theorem Pass.split (choose : Pass Value Key → AllocationChoice) (state : Pass Value Key) (first later : Nat) :
    state.run choose (first + later) = resume (Pass.provider choose) client (Pass.charge choose) later (state.run choose first) :=
  advance_add _ _ _ first later (state.packet choose)

private theorem pass_advance (choose : Pass Value Key → AllocationChoice) (state : Pass Value Key) (fuel : Nat) :
    advance (Pass.provider choose) client (Pass.charge choose) (fuel + 1) (base := ()) ⟨(), none, state⟩ =
      let response := state.step (choose state)
      let rest := advance (Pass.provider choose) client (Pass.charge choose) fuel
        (base := ()) ⟨(), if response.1 = .pending then none else some response.1, response.2⟩
      (1 + rest.1, rest.2) := by
  simp only [advance, client_poll]
  rfl

private theorem pass_done (choose : Pass Value Key → AllocationChoice) (state : Pass Value Key)
    (fuel : Nat) (status : Status) :
    advance (Pass.provider choose) client (Pass.charge choose) (fuel + 1) (base := ()) ⟨(), some status, state⟩ =
      (0, .done ⟨(), status, state⟩) := by
  simp only [advance, client_done]

/-- Local typed/region support at the states actually consulted by the
existing cursor. This is a proof predicate, not another execution function;
it neither computes outputs nor assumes a coherent completed target. -/
def Pass.AdmittedPrefix (choose : Pass Value Key → AllocationChoice) :
    Nat → Option Status → Pass Value Key → Prop
  | 0, _, _ => True
  | _ + 1, some _, _ => True
  | fuel + 1, none, state =>
      state.WriteAdmission ∧
        Pass.AdmittedPrefix choose fuel
          (if (state.step (choose state)).1 = .pending then none else some (state.step (choose state)).1)
          (state.step (choose state)).2

private theorem Pass.prefix_valid_aux (choose : Pass Value Key → AllocationChoice)
    (rows : List (Row Value Key)) (order : List Nat) (legal : order.Perm (List.range rows.length))
    (fuel : Nat) (control : Option Status) (state : Pass Value Key) (valid : state.Valid rows order)
    (admitted : Pass.AdmittedPrefix choose fuel control state) :
    (Pass.outcomeState choose (advance (Pass.provider choose) client (Pass.charge choose) fuel
      (base := ()) ⟨(), control, state⟩).2).Valid rows order := by
  induction fuel generalizing control state with
  | zero => exact valid
  | succ fuel ih =>
      cases control with
      | some status => rw [pass_done]; exact valid
      | none =>
          rw [pass_advance]
          exact ih _ _ (state.step_valid rows order valid legal admitted.1 (choose state)) admitted.2

/-- The prefix relation is derived from actual execution under its logged
local cell/region admission, rather than a premise about all abstract states
or a supplied final permutation. Native realization of that admission is open. -/
theorem Pass.prefix_valid (choose : Pass Value Key → AllocationChoice)
    (rows : List (Row Value Key)) (order : List Nat) (legal : order.Perm (List.range rows.length))
    (state : Pass Value Key) (valid : state.Valid rows order) (fuel : Nat)
    (admitted : Pass.AdmittedPrefix choose fuel none state) :
    (Pass.outcomeState choose (state.run choose fuel).2).Valid rows order :=
  Pass.prefix_valid_aux choose rows order legal fuel none state valid admitted


theorem Pass.copy_ready_empty (state : Pass Value Key) (ready : state.copyOne.1 = .ready) : state.copyOne.2.todo = [] := by
  cases pending : state.todo with
  | nil => simp [Pass.copyOne, pending]
  | cons selected rest =>
      cases read : state.primary.read selected with
      | none => simp [Pass.copyOne, pending, read] at ready
      | some row => cases written : state.scratch.write state.written row <;> simp [Pass.copyOne, pending, read, written] at ready

theorem Pass.step_ready_empty (state : Pass Value Key) (choice : AllocationChoice)
    (ready : (state.step choice).1 = .ready) : (state.step choice).2.todo = [] := by
  by_cases empty : state.todo.isEmpty = true
  · simpa only [Pass.step, if_pos empty] using state.copy_ready_empty (by simpa only [Pass.step, if_pos empty] using ready)
  · simp only [Pass.step, if_neg empty] at ready ⊢
    cases prepared : (state.prepareOne choice).1 with
    | pending => simp [prepared] at ready
    | refused => simp [prepared] at ready
    | ready =>
        simp only [prepared] at ready ⊢
        exact (state.prepareOne choice).2.copy_ready_empty ready

private theorem Pass.ready_result_aux (choose : Pass Value Key → AllocationChoice) (fuel : Nat)
    (control : Option Status) (state : Pass Value Key)
    (stopped : control = some .ready → state.todo = []) (paid : Nat) (final : Pass Value Key)
    (finished : advance (Pass.provider choose) client (Pass.charge choose) fuel
      (base := ()) ⟨(), control, state⟩ = (paid, .done ⟨(), .ready, final⟩)) : final.todo = [] := by
  induction fuel generalizing control state paid with
  | zero => cases finished
  | succ fuel ih =>
      cases control with
      | some status =>
          rw [pass_done] at finished
          have same : status = .ready ∧ state = final := by
            have packets := Outcome.done.inj (congrArg Prod.snd finished)
            have pair := congrArg (fun value : Finished (Pass.provider choose) (Return := fun _ _ => Status) () =>
              ((value.2.1, value.2.2) : Status × Pass Value Key)) packets
            exact Prod.mk.inj pair
          exact same.2 ▸ stopped (congrArg some same.1)
      | none =>
          rw [pass_advance] at finished
          have finalResult := congrArg Prod.snd finished
          refine ih (if (state.step (choose state)).1 = .pending then none else some (state.step (choose state)).1)
            (state.step (choose state)).2 ?_
            (advance (Pass.provider choose) client (Pass.charge choose) fuel (base := ())
              ⟨(), if (state.step (choose state)).1 = .pending then none else some (state.step (choose state)).1,
                (state.step (choose state)).2⟩).1 ?_
          · intro readyControl
            cases reply : (state.step (choose state)).1 with
            | pending => simp [reply] at readyControl
            | ready => exact state.step_ready_empty (choose state) reply
            | refused => simp [reply] at readyControl
          · exact Prod.ext rfl finalResult

def ownedKeys (observations : List (Option (Row Value Key))) : List Key :=
  observations.filterMap fun entry => entry.bind Row.key

/-- Completed cursor execution, rather than a supplied completed-prefix
state, earns the whole permutation and the sole legal buffer-owner swap. -/
theorem Pass.completed_cursor_permutation (choose : Pass Value Key → AllocationChoice)
    (rows : List (Row Value Key)) (order : List Nat) (legal : order.Perm (List.range rows.length))
    (state : Pass Value Key) (valid : state.Valid rows order) (fuel paid : Nat)
    (admitted : Pass.AdmittedPrefix choose fuel none state) (final : Pass Value Key)
    (finished : state.run choose fuel = (paid, .done ⟨(), .ready, final⟩)) :
    (observed final.scratch final.expected).Perm (rows.map some) ∧
      (ownedKeys (observed final.scratch final.expected)).Perm (rows.filterMap Row.key) ∧
      final.swap = some ⟨final.scratch, final.primary⟩ := by
  have kept := state.prefix_valid choose rows order legal valid fuel admitted
  rw [finished] at kept
  change final.Valid rows order at kept
  have empty := Pass.ready_result_aux choose fuel none state (by simp) paid final finished
  have permutation := final.completed_permutation rows order kept legal empty
  have keys := permutation.filterMap (fun entry : Option (Row Value Key) => entry.bind Row.key)
  have exactKeys : (ownedKeys (observed final.scratch final.expected)).Perm (rows.filterMap Row.key) := by
    simpa [ownedKeys, List.filterMap_map] using keys
  have length : final.written = final.expected := by
    have ordered := congrArg List.length kept.1
    simp only [List.length_append, List.length_reverse, empty, List.length_nil, Nat.add_zero] at ordered
    have counted := kept.2.1
    have expected := kept.2.2.1
    omega
  exact ⟨permutation, exactKeys, by simp [Pass.swap, empty, length]⟩


theorem DataCell.of_none (memory : Storage (Slot V)) (address : Ptr)
    (uninitialized : load memory address = none) : DataCell memory address := by
  intro child loaded
  rw [uninitialized] at loaded
  cases loaded

theorem DataCell.of_value (memory : Storage (Slot V)) (address : Ptr) (value : V)
    (initialized : load memory address = some (.inr value)) : DataCell memory address := by
  intro child loaded
  rw [initialized] at loaded
  cases loaded

namespace Controls

set_option maxRecDepth 16384

def prepareFive (state : Array V) (index first : Nat) : Array V :=
  let a := (state.prepare index (.fresh first)).next
  let b := (a.prepare index (.fresh (first + 1))).next
  let c := (b.prepare index (.fresh (first + 2))).next
  let d := (c.prepare index (.fresh (first + 3))).next
  (d.prepare index (.fresh (first + 4))).next

def low : Array Nat := prepareFive (Array.empty 24) 0 1

def writtenLow : Array Nat := (low.write 0 7).getD low

def high : Array Nat := prepareFive writtenLow (2 ^ 32 - 1) 20

theorem actual_uint32_digits_and_offset :
    route (2 ^ 32 - 1) = [31, 127, 127, 127] ∧ offset (2 ^ 32 - 1) = 63 := by decide

theorem actual_five_installs_then_ready :
    low.chain.length = 5 ∧ (low.prepare 0 .failure).status = .ready ∧ low.at 0 = some ⟨5, 0⟩ := by decide

theorem initialization_and_malformed_size_refusal :
    Array.initialize (V := Nat) 0 = none ∧ Array.initialize (V := Nat) 257 = none ∧
      ((Array.empty (V := Nat) 257).prepare 0 (.fresh 1)).status = .refused ∧
      ((Array.empty (V := Nat) 257).prepare 0 (.fresh 1)).next.chain = [] := by decide

theorem missing_backing_is_not_sequence_end :
    (Array.empty (V := Nat) 24).at 0 = none ∧
      ((Array.empty (V := Nat) 24).prepare 0 (.fresh 1)).status = .pending := by decide

theorem allocation_failure_retries_same_target_and_keeps_low_value :
    (writtenLow.prepare (2 ^ 32 - 1) .failure).status = .refused ∧
      (writtenLow.prepare (2 ^ 32 - 1) .failure).next = writtenLow ∧
      high.read 0 = some 7 ∧ high.at 0 = some ⟨5, 0⟩ ∧
      (high.prepare (2 ^ 32 - 1) .failure).status = .ready ∧ high.chain.length = 9 := by decide

theorem adjacent_page_reuses_directories :
    (prepareFive writtenLow 64 10).chain.length = 6 ∧
      (prepareFive writtenLow 64 10).at 64 = some ⟨10, 0⟩ ∧
      (prepareFive writtenLow 64 10).read 0 = some 7 := by decide

theorem overflow_cannot_alias_low_storage :
    (writtenLow.prepare (2 ^ 32) (.fresh 99)).status = .refused ∧
      (writtenLow.prepare (2 ^ 32) (.fresh 99)).next = writtenLow ∧ writtenLow.at (2 ^ 32) = none := by decide

theorem host_layout_request_example :
    Kind.directory.requestBytes 16 8 24 = 1040 ∧ Kind.elements.requestBytes 16 8 24 = 1552 := by decide

def first : Row Nat Nat := ⟨10, 7, some 1000⟩
def second : Row Nat Nat := ⟨11, 7, some 1001⟩
def rows := [first, second]
def order := [1, 0]

def sourceBase : Array (Row Nat Nat) := prepareFive (Array.empty 24) 0 1

def source : Array (Row Nat Nat) :=
  let a := (sourceBase.write 0 first).getD sourceBase
  (a.write 1 second).getD a

def scratch : Array (Row Nat Nat) := prepareFive (Array.empty 24) 0 20

def planned : Pass Nat Nat := Pass.start source scratch order

def borrowed := planned.copyOne.2

def copied := borrowed.copyOne.2

theorem source_rows_are_actual_initialized_values : source.read 0 = some first ∧ source.read 1 = some second := by decide

theorem borrowing_partial_pass_never_swaps_owner :
    borrowed.primary.read 0 = some first ∧ borrowed.primary.read 1 = some second ∧
      borrowed.scratch.read 0 = some second ∧ borrowed.scratch.read 1 = none ∧
      borrowed.written = 1 ∧ borrowed.swap = none := by decide

theorem complete_pass_preserves_equal_payload_occurrences :
    copied.scratch.read 0 = some second ∧ copied.scratch.read 1 = some first ∧
      copied.swap = some ⟨copied.scratch, copied.primary⟩ ∧ first.value = second.value ∧ first.ordinal ≠ second.ordinal := by decide

theorem freeing_borrowed_scratch_would_duplicate_owned_ticket :
    ownedKeys (observed borrowed.primary 2) = [1000, 1001] ∧
      ownedKeys (observed borrowed.scratch 1) = [1001] ∧
      ¬(ownedKeys (observed borrowed.primary 2) ++ ownedKeys (observed borrowed.scratch 1)).Nodup := by decide

theorem duplicate_source_index_word_is_not_a_permutation :
    ¬([1, 1] : List Nat).Perm (List.range 2) := by decide

theorem partial_scratch_payloads_are_not_complete_inventory :
    ¬(observed borrowed.scratch 2).Perm (rows.map some) := by decide


theorem planned_valid : planned.Valid rows order := by
  apply Pass.start_valid
  intro index row found
  cases index with
  | zero =>
      simp [rows] at found
      subst row
      exact source_rows_are_actual_initialized_values.1
  | succ index =>
      cases index with
      | zero =>
          simp [rows] at found
          subst row
          exact source_rows_are_actual_initialized_values.2
      | succ index => simp [rows] at found

theorem legal_order : order.Perm (List.range rows.length) := by decide

theorem admission_planned : planned.WriteAdmission := by
  intro address location
  have expected : planned.scratch.at planned.written = some ⟨24, 0⟩ := by decide
  have equal : (⟨24, 0⟩ : Ptr) = address := Option.some.inj (expected.symm.trans location)
  subst address
  refine ⟨DataCell.of_none _ _ (by decide), ?_⟩
  intro position inside
  change position < 0 at inside
  omega

theorem admission_borrowed : borrowed.WriteAdmission := by
  intro address location
  have expected : borrowed.scratch.at borrowed.written = some ⟨24, 1⟩ := by decide
  have equal : (⟨24, 1⟩ : Ptr) = address := Option.some.inj (expected.symm.trans location)
  subst address
  refine ⟨DataCell.of_none _ _ (by decide), ?_⟩
  intro position inside
  have zero : position = 0 := by change position < 1 at inside; omega
  subst position
  exact ⟨⟨24, 0⟩, by decide, by decide⟩

theorem admission_copied : copied.WriteAdmission := by
  intro address location
  have expected : copied.scratch.at copied.written = some ⟨24, 2⟩ := by decide
  have equal : (⟨24, 2⟩ : Ptr) = address := Option.some.inj (expected.symm.trans location)
  subst address
  refine ⟨DataCell.of_none _ _ (by decide), ?_⟩
  intro position inside
  have cases : position = 0 ∨ position = 1 := by change position < 2 at inside; omega
  rcases cases with zero | one
  · subst position
    exact ⟨⟨24, 0⟩, by decide, by decide⟩
  · subst position
    exact ⟨⟨24, 1⟩, by decide, by decide⟩

def choices (_state : Pass Nat Nat) : AllocationChoice := .failure

theorem actual_first_copy : planned.step .failure = (.pending, borrowed) := by decide

theorem actual_second_copy : borrowed.step .failure = (.pending, copied) := by decide

theorem actual_completed_step : copied.step .failure = (.ready, copied) := by decide

theorem earned_nonempty_prefix : Pass.AdmittedPrefix choices 4 none planned := by
  simp only [Pass.AdmittedPrefix, choices, actual_first_copy, actual_second_copy, actual_completed_step,
    reduceCtorEq, ↓reduceIte]
  exact ⟨admission_planned, admission_borrowed, admission_copied, True.intro⟩

theorem actual_completed_run : planned.run choices 4 = (3, .done ⟨(), .ready, copied⟩) := by
  simp only [Pass.run, Pass.packet, pass_advance, choices, actual_first_copy, actual_second_copy,
    actual_completed_step, reduceCtorEq, ↓reduceIte, pass_done]

/-- A real two-row execution supplies the local support and reaches the
completed owner handoff; the prefix theorem has an inhabited nontrivial scope. -/
theorem earned_completed_permutation_and_owner_swap :
    (observed copied.scratch copied.expected).Perm (rows.map some) ∧
      (ownedKeys (observed copied.scratch copied.expected)).Perm (rows.filterMap Row.key) ∧
      copied.swap = some ⟨copied.scratch, copied.primary⟩ :=
  planned.completed_cursor_permutation choices rows order legal_order planned_valid 4 3
    earned_nonempty_prefix copied actual_completed_run

end Controls


theorem Array.write_valid (state next : Array V) (index : Nat) (value : V)
    (valid : state.Valid) (written : state.write index value = some next) : next.Valid := by
  cases location : state.at index with
  | none => simp [Array.write, location] at written
  | some address =>
      cases stored : store state.memory address (.inr value) with
      | none => simp [Array.write, location, stored] at written
      | some memory =>
          have same : { state with memory := memory } = next := by simpa [Array.write, location, stored] using written
          subst next
          exact store_chain_valid state.memory memory address (.inr value) stored state.chain valid

namespace Controls

set_option maxRecDepth 16384

theorem prepareFive_valid (state : Array V) (valid : state.Valid) (index first : Nat) :
    (prepareFive state index first).Valid := by
  unfold prepareFive
  apply Array.prepare_valid
  apply Array.prepare_valid
  apply Array.prepare_valid
  apply Array.prepare_valid
  exact state.prepare_valid index (.fresh first) valid

theorem complete_primary_storage_valid : copied.scratch.Valid := by
  have initial : scratch.Valid := prepareFive_valid (Array.empty 24) (Array.empty_valid 24) 0 20
  have firstWrite : scratch.write 0 second = some borrowed.scratch := by decide
  have secondWrite : borrowed.scratch.write 1 first = some copied.scratch := by decide
  have next := scratch.write_valid borrowed.scratch 0 second initial firstWrite
  exact borrowed.scratch.write_valid copied.scratch 1 first next secondWrite

end Controls

end Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed

/-!
## Retained adjacent-run index schedules

The producer below retains numeric source frontiers and emits one chosen
position at a time. An independent adjacent `List.merge` specification earns
prefix inventories and completed legal index words. The existing paged copy
cursor then transfers those words through actual row writes and owner swaps.

Comparison supplies a completed pure reply. Declared polls count these
scheduler actions, rather than native byte probes, backing-store preparation,
allocator work or physical time. Schedule-then-copy composition is not an
interleaved native trace simulation. Final adjacent-merge ordering requires
the two input runs to be sorted; the global sorted-run induction across
width-doubling passes is a further obligation. The chronological word and
publication functions are logical readouts of the retained output log.
-/

namespace Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed.MergeSchedule

open Mettapedia.Machines.Cursor

/-- Half-open source positions. This list occurs in the reference and proofs,
not in a scheduler transition. -/
def span (first last : Nat) : List Nat := List.range' first (last - first)

@[simp] theorem span_self (first : Nat) : span first first = [] := by simp [span]

theorem span_cons (first last : Nat) (present : first < last) :
    span first last = first :: span (first + 1) last := by
  obtain ⟨count, length⟩ : ∃ count, last - first = count + 1 := ⟨last - first - 1, by omega⟩
  simp only [span, length, List.range'_succ]
  congr 1
  congr 1
  omega

theorem span_append (first middle last : Nat) (left : first ≤ middle) (right : middle ≤ last) :
    span first middle ++ span middle last = span first last := by
  have middleEq : middle = first + (middle - first) := by omega
  simp only [span]
  conv_lhs => arg 2; rw [middleEq]
  rw [List.range'_append_1]
  congr 1
  omega

/-- Independent whole-pass specification: merge each adjacent clipped pair.
The actual producer below only retains numeric frontiers and emits one head. -/
def reference (before : Nat → Nat → Bool) (width first count : Nat) : List Nat :=
  if count = 0 then [] else
  if width = 0 then List.range' first count else
    let left := min width count
    let right := min width (count - left)
    List.merge (List.range' first left) (List.range' (first + left) right) before ++
      reference before width (first + left + right) (count - left - right)
termination_by count
decreasing_by
  have positive : 0 < min width count := Nat.lt_min.mpr ⟨by omega, by omega⟩
  omega

@[simp] theorem reference_zero (before : Nat → Nat → Bool) (width first : Nat) :
    reference before width first 0 = [] := by rw [reference, if_pos rfl]

theorem reference_perm (before : Nat → Nat → Bool) (width first count : Nat) :
    (reference before width first count).Perm (List.range' first count) := by
  induction count using Nat.strong_induction_on generalizing first with
  | h count ih =>
      by_cases empty : count = 0
      · subst count; simp
      by_cases zero : width = 0
      · rw [reference, if_neg empty, if_pos zero]
      have positive : 0 < min width count := Nat.lt_min.mpr ⟨by omega, by omega⟩
      have smaller : count - min width count - min width (count - min width count) < count := by omega
      have leftBound := Nat.min_le_right width count
      have rightBound := Nat.min_le_right width (count - min width count)
      rw [reference, if_neg empty, if_neg zero]
      exact ((List.merge_perm_append before).append (ih _ smaller _)).trans (by
        apply List.Perm.of_eq
        rw [List.range'_append_1]
        have associate : first + min width count + min width (count - min width count) =
            first + (min width count + min width (count - min width count)) := by omega
        rw [associate, List.range'_append_1]
        congr 1
        omega)

@[simp] theorem reference_length (before : Nat → Nat → Bool) (width first count : Nat) :
    (reference before width first count).length = count :=
  (reference_perm before width first count).length_eq.trans List.length_range'

/-- Numeric state of one unpublished pass. `emittedRev` is its chronological
output log; no transition computes `reference`, `List.merge`, or a range list. -/
structure State where
  length : Nat
  width : Nat
  output : Nat
  left : Nat
  leftEnd : Nat
  right : Nat
  rightEnd : Nat
  active : Bool
  emittedRev : List Nat
  polls : Nat
  deriving Repr, DecidableEq

def State.start (length width : Nat) : State :=
  ⟨length, width, 0, 0, 0, 0, 0, false, [], 0⟩

def State.word (state : State) : List Nat := state.emittedRev.reverse

def State.exhausted (state : State) : Bool :=
  state.left == state.leftEnd && state.right == state.rightEnd

def State.needsComparison (state : State) : Bool :=
  state.active && state.left < state.leftEnd && state.right < state.rightEnd

/-- One setup, one range finish, one completed head selection, or one full-pass
publication. Comparison is a completed service reply, not a physical price. -/
def State.step (before : Nat → Nat → Bool) (state : State) : Status × State :=
  if state.width = 0 then (.refused, state) else
  if !state.active then
    if state.output = state.length then (.ready, { state with polls := state.polls + 1 }) else
      let leftEnd := state.output + min state.width (state.length - state.output)
      let rightEnd := leftEnd + min state.width (state.length - leftEnd)
      (.pending, { state with
        left := state.output
        leftEnd := leftEnd
        right := leftEnd
        rightEnd := rightEnd
        active := true
        polls := state.polls + 1 })
  else if state.exhausted then
    (.pending, { state with active := false, polls := state.polls + 1 })
  else
    let takeLeft := state.right = state.rightEnd ||
      (state.left < state.leftEnd && before state.left state.right)
    let selected := if takeLeft then state.left else state.right
    (.pending, { state with
      output := state.output + 1
      left := if takeLeft then state.left + 1 else state.left
      right := if takeLeft then state.right else state.right + 1
      emittedRev := selected :: state.emittedRev
      polls := state.polls + 1 })

def State.residual (before : Nat → Nat → Bool) (state : State) : List Nat :=
  if state.active then
    List.merge (span state.left state.leftEnd) (span state.right state.rightEnd) before ++
      reference before state.width state.rightEnd (state.length - state.rightEnd)
  else reference before state.width state.output (state.length - state.output)

/-- Local pointer bounds/balance and the earned independent prefix equation.
There is no supplied permutation or final-output premise. -/
structure Valid (before : Nat → Nat → Bool) (state : State) : Prop where
  width_pos : 0 < state.width
  output_le : state.output ≤ state.length
  length_word : state.emittedRev.length = state.output
  bounds : state.active = true →
    state.left ≤ state.leftEnd ∧ state.leftEnd ≤ state.right ∧
      state.right ≤ state.rightEnd ∧ state.rightEnd ≤ state.length
  balance : state.active = true →
    state.output + (state.leftEnd - state.left) + (state.rightEnd - state.right) = state.rightEnd
  equation : state.word ++ state.residual before = reference before state.width 0 state.length

theorem start_valid (before : Nat → Nat → Bool) (length width : Nat) (positive : 0 < width) :
    Valid before (State.start length width) := by
  constructor
  · exact positive
  · simp [State.start]
  · simp [State.start]
  · simp [State.start]
  · simp [State.start]
  · simp [State.start, State.word, State.residual]

private theorem setup_reference (before : Nat → Nat → Bool) (width output length : Nat)
    (positive : 0 < width) (present : output < length) :
    let middle := output + min width (length - output)
    let last := middle + min width (length - middle)
    List.merge (span output middle) (span middle last) before ++
      reference before width last (length - last) = reference before width output (length - output) := by
  dsimp
  have leftBound := Nat.min_le_right width (length - output)
  have rightBound := Nat.min_le_right width (length - (output + min width (length - output)))
  have difference : length - (output + min width (length - output)) =
      length - output - min width (length - output) := by omega
  conv_rhs => rw [reference]
  simp only [if_neg (by omega : length - output ≠ 0), if_neg (by omega : width ≠ 0), span,
    Nat.add_sub_cancel_left, difference]
  congr 1
  congr 1
  omega

private theorem merge_pop_left (before : Nat → Nat → Bool) (left leftEnd right rightEnd : Nat)
    (leftPresent : left < leftEnd) (rightBound : right ≤ rightEnd)
    (chosen : right = rightEnd ∨ before left right = true) :
    List.merge (span left leftEnd) (span right rightEnd) before =
      left :: List.merge (span (left + 1) leftEnd) (span right rightEnd) before := by
  rw [span_cons left leftEnd leftPresent]
  rcases chosen with empty | ordered
  · subst rightEnd; simp
  · by_cases empty : right = rightEnd
    · subst rightEnd; simp
    · rw [span_cons right rightEnd (by omega)]
      simp only [List.merge, ordered, ↓reduceIte]

private theorem merge_pop_right (before : Nat → Nat → Bool) (left leftEnd right rightEnd : Nat)
    (leftBound : left ≤ leftEnd) (rightPresent : right < rightEnd)
    (chosen : left = leftEnd ∨ before left right = false) :
    List.merge (span left leftEnd) (span right rightEnd) before =
      right :: List.merge (span left leftEnd) (span (right + 1) rightEnd) before := by
  rw [span_cons right rightEnd rightPresent]
  rcases chosen with empty | ordered
  · subst leftEnd; simp
  · by_cases empty : left = leftEnd
    · subst leftEnd; simp
    · rw [span_cons left leftEnd (by omega)]
      simp only [List.merge, ordered, Bool.false_eq_true, ↓reduceIte]

theorem step_valid (before : Nat → Nat → Bool) (state : State) (valid : Valid before state) :
    Valid before (state.step before).2 := by
  have positive := valid.width_pos
  have outputBound := valid.output_le
  have lengthWord := valid.length_word
  have equation := valid.equation
  simp only [State.step, if_neg (by omega : state.width ≠ 0)]
  by_cases active : state.active = true
  · simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨leftBound, middleBound, rightBound, endBound⟩ := valid.bounds active
    have balance := valid.balance active
    by_cases exhausted : state.exhausted = true
    · have ended : state.left = state.leftEnd ∧ state.right = state.rightEnd := by
        simpa [State.exhausted] using exhausted
      have atEnd : state.output = state.rightEnd := by omega
      simp only [exhausted, ↓reduceIte]
      refine ⟨positive, outputBound, lengthWord, ?_, ?_, ?_⟩
      · simp
      · simp
      · simpa [State.word, State.residual, active, ended.1, ended.2, atEnd] using equation
    · simp only [exhausted, Bool.false_eq_true, ↓reduceIte]
      have nonempty : state.left < state.leftEnd ∨ state.right < state.rightEnd := by
        simp [State.exhausted] at exhausted
        omega
      by_cases chosen : (state.right = state.rightEnd ||
          (state.left < state.leftEnd && before state.left state.right)) = true
      · have leftPresent : state.left < state.leftEnd := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at chosen
          omega
        have selection : state.right = state.rightEnd ∨ before state.left state.right = true := by
          simpa only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, leftPresent, true_and] using chosen
        have popped := merge_pop_left before state.left state.leftEnd state.right state.rightEnd
          leftPresent rightBound selection
        simp only [chosen, ↓reduceIte]
        refine ⟨positive, by dsimp; omega, by simp [lengthWord], ?_, ?_, ?_⟩
        · intro _; dsimp; exact ⟨by omega, middleBound, rightBound, endBound⟩
        · intro _; dsimp; omega
        · simpa [State.word, State.residual, active, popped, List.append_assoc] using equation
      · have notChosen : (state.right = state.rightEnd ||
            (state.left < state.leftEnd && before state.left state.right)) = false := by
          exact Bool.eq_false_iff.mpr chosen
        have rightPresent : state.right < state.rightEnd := by
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_imp] at notChosen
          omega
        have selection : state.left = state.leftEnd ∨ before state.left state.right = false := by
          by_cases empty : state.left = state.leftEnd
          · exact Or.inl empty
          · right
            have both := Bool.or_eq_false_iff.mp notChosen
            simpa only [show decide (state.left < state.leftEnd) = true from decide_eq_true (by omega),
              Bool.true_and] using both.2
        have popped := merge_pop_right before state.left state.leftEnd state.right state.rightEnd
          leftBound rightPresent selection
        simp only [notChosen, Bool.false_eq_true, ↓reduceIte]
        refine ⟨positive, by dsimp; omega, by simp [lengthWord], ?_, ?_, ?_⟩
        · intro _; dsimp; exact ⟨leftBound, by omega, by omega, endBound⟩
        · intro _; dsimp; omega
        · simpa [State.word, State.residual, active, popped, List.append_assoc] using equation
  · have inactive : state.active = false := Bool.eq_false_iff.mpr active
    simp only [inactive, Bool.not_false, ↓reduceIte]
    by_cases complete : state.output = state.length
    · simp only [complete, ↓reduceIte]
      refine ⟨positive, by simp, ?_, ?_, ?_, ?_⟩
      · simpa only [complete] using lengthWord
      · simp
      · simp
      · simpa [State.word, State.residual, inactive, complete] using equation
    · simp only [complete, ↓reduceIte]
      have leftCount := Nat.min_le_right state.width (state.length - state.output)
      have rightCount := Nat.min_le_right state.width
        (state.length - (state.output + min state.width (state.length - state.output)))
      refine ⟨positive, outputBound, lengthWord, ?_, ?_, ?_⟩
      · intro _; dsimp; omega
      · intro _; dsimp; omega
      · simpa only [State.word, State.residual, inactive, Bool.false_eq_true, ↓reduceIte,
          setup_reference before state.width state.output state.length positive (by omega)] using equation

theorem ready_fields (before : Nat → Nat → Bool) (state : State)
    (positive : 0 < state.width) (ready : (state.step before).1 = .ready) :
    state.active = false ∧ state.output = state.length ∧
      (state.step before).2 = { state with polls := state.polls + 1 } := by
  simp only [State.step, if_neg (Nat.ne_of_gt positive)] at ready ⊢
  split at ready
  · rename_i inactive
    have activeFalse : state.active = false := by simpa using inactive
    simp only [inactive, ↓reduceIte]
    split at ready
    · rename_i complete
      simp only [complete, ↓reduceIte]
      exact ⟨activeFalse, by trivial, by trivial⟩
    · cases ready
  · split at ready <;> cases ready

theorem completed_word (before : Nat → Nat → Bool) (state : State)
    (valid : Valid before state) (ready : (state.step before).1 = .ready) :
    state.word = reference before state.width 0 state.length ∧
      state.word.Perm (List.range state.length) := by
  have fields := ready_fields before state valid.width_pos ready
  have complete : state.active = false ∧ state.output = state.length := ⟨fields.1, fields.2.1⟩
  have exactWord : state.word = reference before state.width 0 state.length := by
    simpa [State.residual, complete.1, complete.2] using valid.equation
  exact ⟨exactWord, exactWord ▸ (by simpa only [List.range_eq_range'] using
    (reference_perm before state.width 0 state.length))⟩

theorem prefix_inventory (before : Nat → Nat → Bool) (state : State) (valid : Valid before state) :
    (state.word ++ state.residual before).Perm (List.range state.length) := by
  rw [valid.equation]
  simpa only [List.range_eq_range'] using reference_perm before state.width 0 state.length

theorem emitted_legal (before : Nat → Nat → Bool) (state : State) (valid : Valid before state) :
    state.word.Nodup ∧ ∀ index ∈ state.word, index < state.length := by
  have inventory := prefix_inventory before state valid
  constructor
  · exact (inventory.nodup_iff.mpr (List.nodup_range (n := state.length))).of_append_left
  · intro index member
    have present := inventory.mem_iff.mp (List.mem_append_left _ member)
    exact List.mem_range.mp present

def State.publish (state : State) : Option (List Nat) :=
  if !state.active && state.output == state.length then some state.word else none

theorem no_early_publication (state : State)
    (unfinished : state.active = true ∨ state.output ≠ state.length) : state.publish = none := by
  simp only [State.publish]
  rcases unfinished with active | unfinished
  · simp [active]
  · simp [unfinished]

theorem published_permutation (before : Nat → Nat → Bool) (state : State)
    (valid : Valid before state) (word : List Nat) (published : state.publish = some word) :
    word.Perm (List.range state.length) := by
  have fields : state.active = false ∧ state.output = state.length ∧ state.word = word := by
    simpa [State.publish, Bool.and_eq_true, Bool.not_eq_true', and_assoc] using published
  have finished : (state.step before).1 = .ready := by
    simp [State.step, Nat.ne_of_gt valid.width_pos, fields.1, fields.2.1]
  simpa only [fields.2.2] using (completed_word before state valid finished).2

theorem step_shape (before : Nat → Nat → Bool) (state : State) :
    (state.step before).2.length = state.length ∧ (state.step before).2.width = state.width := by
  simp only [State.step]
  split
  · exact ⟨rfl, rfl⟩
  · split
    · split <;> exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

theorem step_polls (before : Nat → Nat → Bool) (state : State) (positive : 0 < state.width) :
    (state.step before).2.polls = state.polls + 1 := by
  simp only [State.step, if_neg (by omega : state.width ≠ 0)]
  split
  · split <;> rfl
  · split <;> rfl

/-- A head-selection action appends precisely that source position and
advances only its frontier. The chronological word is a logical observer. -/
theorem one_head_emission (before : Nat → Nat → Bool) (state : State)
    (positive : 0 < state.width) (active : state.active = true) (live : state.exhausted = false) :
    (state.step before).2.output = state.output + 1 ∧
      (((state.step before).2.left = state.left + 1 ∧ (state.step before).2.right = state.right ∧
          (state.step before).2.word = state.word ++ [state.left]) ∨
        ((state.step before).2.left = state.left ∧ (state.step before).2.right = state.right + 1 ∧
          (state.step before).2.word = state.word ++ [state.right])) := by
  simp only [State.step, if_neg (Nat.ne_of_gt positive), active, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, live]
  split <;> simp [State.word]

theorem step_not_refused (before : Nat → Nat → Bool) (state : State) (positive : 0 < state.width) :
    (state.step before).1 ≠ .refused := by
  simp only [State.step, if_neg (by omega : state.width ≠ 0)]
  split
  · split <;> simp
  · split <;> simp

/-- A decreasing scheduler rank, not an elapsed-time or callback-price bound. -/
def State.rank (state : State) : Nat :=
  4 * (state.length - state.output) +
    if state.active then (if state.exhausted then 2 else 0) else 1

theorem step_progress (before : Nat → Nat → Bool) (state : State) (valid : Valid before state)
    (pending : (state.step before).1 = .pending) : (state.step before).2.rank < state.rank := by
  have positive := valid.width_pos
  have outputBound := valid.output_le
  have nextValid := step_valid before state valid
  simp only [State.step, if_neg (by omega : state.width ≠ 0)] at pending ⊢
  by_cases active : state.active = true
  · simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at pending ⊢
    by_cases exhausted : state.exhausted = true
    · simp [exhausted, State.rank, active]
    · simp only [exhausted, Bool.false_eq_true, ↓reduceIte] at pending ⊢
      simp only [State.rank, active, exhausted, Bool.false_eq_true, ↓reduceIte]
      have nextBound := nextValid.output_le
      simp only [State.step, if_neg (by omega : state.width ≠ 0), active,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, exhausted] at nextBound
      change state.output + 1 ≤ state.length at nextBound
      split <;> split <;> omega
  · have inactive : state.active = false := Bool.eq_false_iff.mpr active
    simp only [inactive, Bool.not_false, ↓reduceIte] at pending ⊢
    by_cases complete : state.output = state.length
    · simp [complete] at pending
    · simp only [complete, ↓reduceIte]
      have leftPositive : 0 < min state.width (state.length - state.output) :=
        Nat.lt_min.mpr ⟨positive, by omega⟩
      have notEmpty : (state.output == state.output + min state.width (state.length - state.output) &&
          state.output + min state.width (state.length - state.output) ==
            state.output + min state.width (state.length - state.output) +
              min state.width (state.length - (state.output + min state.width (state.length - state.output)))) = false := by
        have leftNot : (state.output == state.output + min state.width (state.length - state.output)) = false := by
          exact beq_eq_false_iff_ne.mpr (by omega)
        simp only [leftNot, Bool.false_and]
      simp only [State.rank, State.exhausted, inactive, Bool.false_eq_true, ↓reduceIte]
      change 4 * (state.length - state.output) +
        (if (state.output == state.output + min state.width (state.length - state.output) &&
          state.output + min state.width (state.length - state.output) ==
            state.output + min state.width (state.length - state.output) +
              min state.width (state.length - (state.output + min state.width (state.length - state.output))))
          then 2 else 0) < 4 * (state.length - state.output) + 1
      rw [notEmpty]
      simp

def provider (before : Nat → Nat → Bool) : Provider protocol where
  State _ _ := State
  step state _ := ⟨(state.step before).1, (state.step before).2⟩

def charge (before : Nat → Nat → Bool) : Charge (provider before) := fun _ _ => 1

def State.packet (before : Nat → Nat → Bool) (state : State) : Packet (provider before) client () :=
  ⟨(), none, state⟩

def State.run (before : Nat → Nat → Bool) (fuel : Nat) (state : State) :=
  advance (provider before) client (charge before) fuel (state.packet before)

def outcomeState (before : Nat → Nat → Bool) : Outcome (provider before) client () → State
  | .paused ⟨(), _, state⟩ => state
  | .done ⟨(), _, state⟩ => state

theorem run_zero (before : Nat → Nat → Bool) (state : State) :
    state.run before 0 = (0, .paused (state.packet before)) := rfl

theorem run_split (before : Nat → Nat → Bool) (state : State) (first later : Nat) :
    state.run before (first + later) =
      resume (provider before) client (charge before) later (state.run before first) :=
  advance_add _ _ _ first later (state.packet before)

private theorem merge_client_poll : client.str () () none =
    ⟨.inr (), fun (status : Status) => if status = .pending then none else some status⟩ := by
  unfold client
  dsimp only
  simp only [TypeCat.ofHom, CategoryTheory.ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  rfl

private theorem merge_client_done (status : Status) : client.str () () (some status) =
    ⟨.inl status, fun impossible => nomatch impossible⟩ := by
  unfold client
  dsimp only
  simp only [TypeCat.ofHom, CategoryTheory.ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  congr 1
  funext impossible
  nomatch impossible

private theorem advance_poll (before : Nat → Nat → Bool) (state : State) (fuel : Nat) :
    advance (provider before) client (charge before) (fuel + 1) (base := ()) ⟨(), none, state⟩ =
      let response := state.step before
      let rest := advance (provider before) client (charge before) fuel
        (base := ()) ⟨(), if response.1 = .pending then none else some response.1, response.2⟩
      (1 + rest.1, rest.2) := by
  simp only [advance, merge_client_poll]
  rfl

private theorem advance_done (before : Nat → Nat → Bool) (state : State) (status : Status) (fuel : Nat) :
    advance (provider before) client (charge before) (fuel + 1) (base := ()) ⟨(), some status, state⟩ =
      (0, .done ⟨(), status, state⟩) := by simp only [advance, merge_client_done]

private theorem prefix_valid_aux (before : Nat → Nat → Bool) (fuel : Nat)
    (control : Option Status) (state : State) (valid : Valid before state) :
    Valid before (outcomeState before (advance (provider before) client (charge before) fuel
      (base := ()) ⟨(), control, state⟩).2) := by
  induction fuel generalizing state control with
  | zero => exact valid
  | succ fuel ih =>
      cases control with
      | some status => rw [advance_done]; exact valid
      | none => rw [advance_poll]; exact ih _ _ (step_valid before state valid)

/-- Every actual paused prefix retains the independent merge residual and
the exact un-emitted occurrence inventory. -/
theorem prefix_valid (before : Nat → Nat → Bool) (state : State) (valid : Valid before state) (fuel : Nat) :
    Valid before (outcomeState before (state.run before fuel).2) :=
  prefix_valid_aux before fuel none state valid

private theorem receipt_aux (before : Nat → Nat → Bool) (fuel : Nat)
    (control : Option Status) (state : State) (valid : Valid before state) :
    (outcomeState before (advance (provider before) client (charge before) fuel
      (base := ()) ⟨(), control, state⟩).2).polls = state.polls +
      (advance (provider before) client (charge before) fuel (base := ()) ⟨(), control, state⟩).1 := by
  induction fuel generalizing state control with
  | zero => simp [advance, outcomeState]
  | succ fuel ih =>
      cases control with
      | some status => rw [advance_done]; simp [outcomeState]
      | none =>
          rw [advance_poll]
          have rest := ih
            (if (state.step before).1 = .pending then none else some (state.step before).1)
            (state.step before).2 (step_valid before state valid)
          simp only [step_polls before state valid.width_pos, Nat.add_assoc] at rest
          convert rest using 1 <;> rfl

/-- The declared one-poll currency is read back from actual transitions;
it is preserved with the residual under `run_split`. -/
theorem exact_receipt (before : Nat → Nat → Bool) (state : State) (valid : Valid before state) (fuel : Nat) :
    (outcomeState before (state.run before fuel).2).polls = state.polls + (state.run before fuel).1 :=
  receipt_aux before fuel none state valid

theorem finite_completion (before : Nat → Nat → Bool) (state : State) (valid : Valid before state) :
    ∃ (paid : Nat) (final : State),
      state.run before (paid + 1) = (paid, .done ⟨(), .ready, final⟩) ∧
        Valid before final ∧ final.word.Perm (List.range state.length) ∧
        final.publish = some final.word ∧ final.polls = state.polls + paid ∧ paid ≤ state.rank + 1 := by
  have claim : ∀ rank (state : State), state.rank = rank → Valid before state →
      ∃ (paid : Nat) (final : State),
        state.run before (paid + 1) = (paid, .done ⟨(), .ready, final⟩) ∧
          Valid before final ∧ final.word.Perm (List.range state.length) ∧
          final.publish = some final.word ∧ final.polls = state.polls + paid ∧ paid ≤ state.rank + 1 := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
        intro state same valid
        have nextValid := step_valid before state valid
        have polls := step_polls before state valid.width_pos
        have shape := step_shape before state
        cases status : (state.step before).1 with
        | refused => exact (step_not_refused before state valid.width_pos status).elim
        | ready =>
            have exactWord := completed_word before state valid status
            have fields := ready_fields before state valid.width_pos status
            have nextReady : (state.step before).2.active = false ∧ (state.step before).2.output = state.length := by
              simpa only [fields.2.2] using And.intro fields.1 fields.2.1
            have nextWord : (state.step before).2.word = state.word := by rw [fields.2.2]; rfl
            refine ⟨1, (state.step before).2, ?_, nextValid, ?_, ?_, ?_, by omega⟩
            · rw [State.run, State.packet, advance_poll]
              simp only [status, reduceCtorEq, ↓reduceIte, advance_done, Nat.add_zero]
            · simpa only [nextWord] using exactWord.2
            · simp [State.publish, nextReady.1, nextReady.2, shape.1]
            · simpa using polls
        | pending =>
            have smaller := step_progress before state valid status
            obtain ⟨paid, final, finished, finalValid, permutation, published, finalPolls, bound⟩ :=
              ih _ (by omega) (state.step before).2 rfl nextValid
            refine ⟨paid + 1, final, ?_, finalValid, ?_, published, ?_, by omega⟩
            · change advance (provider before) client (charge before) ((paid + 1) + 1)
                (base := ()) ⟨(), none, state⟩ = _
              rw [advance_poll]
              simp only [status, ↓reduceIte]
              change (1 + ((state.step before).2.run before (paid + 1)).1,
                ((state.step before).2.run before (paid + 1)).2) = _
              rw [finished]
              simp only [Nat.add_comm]
            · simpa only [shape.1] using permutation
            · omega
  exact claim state.rank state rfl valid

private theorem prefix_shape_aux (before : Nat → Nat → Bool) (fuel : Nat)
    (control : Option Status) (state : State) :
    let final := outcomeState before (advance (provider before) client (charge before) fuel
      (base := ()) ⟨(), control, state⟩).2
    final.length = state.length ∧ final.width = state.width := by
  induction fuel generalizing state control with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
      cases control with
      | some status => rw [advance_done]; exact ⟨rfl, rfl⟩
      | none =>
          rw [advance_poll]
          have rest := ih (if (state.step before).1 = .pending then none else some (state.step before).1)
            (state.step before).2
          exact ⟨rest.1.trans (step_shape before state).1, rest.2.trans (step_shape before state).2⟩

theorem prefix_shape (before : Nat → Nat → Bool) (state : State) (fuel : Nat) :
    (outcomeState before (state.run before fuel).2).length = state.length ∧
      (outcomeState before (state.run before fuel).2).width = state.width :=
  prefix_shape_aux before fuel none state

private theorem ready_publication_aux (before : Nat → Nat → Bool) (fuel : Nat)
    (control : Option Status) (state : State) (valid : Valid before state)
    (stopped : control = some .ready → state.publish = some state.word) (paid : Nat) (final : State)
    (finished : advance (provider before) client (charge before) fuel
      (base := ()) ⟨(), control, state⟩ = (paid, .done ⟨(), .ready, final⟩)) :
    final.publish = some final.word := by
  induction fuel generalizing control state paid with
  | zero => cases finished
  | succ fuel ih =>
      cases control with
      | some status =>
          rw [advance_done] at finished
          have same : status = .ready ∧ state = final := by
            have packets := Outcome.done.inj (congrArg Prod.snd finished)
            have pair := congrArg (fun value : Finished (provider before) (Return := fun _ _ => Status) () =>
              ((value.2.1, value.2.2) : Status × State)) packets
            exact Prod.mk.inj pair
          exact same.2 ▸ stopped (congrArg some same.1)
      | none =>
          rw [advance_poll] at finished
          have sameResult := congrArg Prod.snd finished
          refine ih (if (state.step before).1 = .pending then none else some (state.step before).1)
            (state.step before).2 (step_valid before state valid) ?_
            (advance (provider before) client (charge before) fuel (base := ())
              ⟨(), if (state.step before).1 = .pending then none else some (state.step before).1,
                (state.step before).2⟩).1 ?_
          · intro readyControl
            cases reply : (state.step before).1 with
            | pending => simp [reply] at readyControl
            | refused => simp [reply] at readyControl
            | ready =>
                have fields := ready_fields before state valid.width_pos reply
                simp [State.publish, fields.2.2, fields.1, fields.2.1]
          · exact Prod.ext rfl sameResult

/-- Any actual completed cursor, including a split/resumed execution, supplies
the legal word. This statement has no legal-index-word input. -/
theorem completed_cursor (before : Nat → Nat → Bool) (state : State) (valid : Valid before state)
    (fuel paid : Nat) (final : State)
    (finished : state.run before fuel = (paid, .done ⟨(), .ready, final⟩)) :
    Valid before final ∧ final.publish = some final.word ∧
      final.word = reference before state.width 0 state.length ∧
      final.word.Perm (List.range state.length) ∧ final.polls = state.polls + paid := by
  have kept := prefix_valid before state valid fuel
  have fields := prefix_shape before state fuel
  have receipt := exact_receipt before state valid fuel
  rw [finished] at kept fields receipt
  change Valid before final at kept
  change final.length = state.length ∧ final.width = state.width at fields
  have published := ready_publication_aux before fuel none state valid (by simp) paid final finished
  have legal := published_permutation before final kept final.word published
  have exactWord : final.word = reference before final.width 0 final.length := by
    have ready : (final.step before).1 = .ready := by
      have data : final.active = false ∧ final.output = final.length := by
        simpa [State.publish] using congrArg Option.isSome published
      simp [State.step, Nat.ne_of_gt kept.width_pos, data.1, data.2]
    exact (completed_word before final kept ready).1
  exact ⟨kept, published, by simpa only [fields.1, fields.2] using exactWord,
    by simpa only [fields.1] using legal, receipt⟩

/-- The actual indexed row-copy cursor receives a word earned by the numeric
merge producer. Local cell/region support and actual copy completion remain
the existing storage service contracts; permutation is now derived here. -/
theorem completed_storage_transfer {Value Key : Type} (before : Nat → Nat → Bool)
    (rows : List (Row Value Key)) (width : Nat) (positive : 0 < width)
    (scheduleFuel schedulePaid : Nat) (scheduleFinal : State)
    (scheduled : (State.start rows.length width).run before scheduleFuel =
      (schedulePaid, .done ⟨(), .ready, scheduleFinal⟩))
    (primary scratch : Array (Row Value Key))
    (initialized : ∀ index row, rows[index]? = some row → primary.read index = some row)
    (choose : Pass Value Key → AllocationChoice) (copyFuel copyPaid : Nat)
    (admitted : (Pass.start primary scratch scheduleFinal.word).AdmittedPrefix choose copyFuel none)
    (copyFinal : Pass Value Key)
    (copied : (Pass.start primary scratch scheduleFinal.word).run choose copyFuel =
      (copyPaid, .done ⟨(), .ready, copyFinal⟩)) :
    (observed copyFinal.scratch copyFinal.expected).Perm (rows.map some) ∧
      (ownedKeys (observed copyFinal.scratch copyFinal.expected)).Perm (rows.filterMap Row.key) ∧
      copyFinal.swap = some ⟨copyFinal.scratch, copyFinal.primary⟩ := by
  have earned := completed_cursor before (State.start rows.length width)
    (start_valid before rows.length width positive) scheduleFuel schedulePaid scheduleFinal scheduled
  exact (Pass.start primary scratch scheduleFinal.word).completed_cursor_permutation choose rows
    scheduleFinal.word earned.2.2.2.1 (Pass.start_valid rows scheduleFinal.word primary scratch initialized)
    copyFuel copyPaid admitted copyFinal copied

/-- Completed-pass publication decides the next width without touching row
contents. The next pass reads the buffer published by the existing copy/swap
interface. This boundary does not itself establish a global sorted-run invariant. -/
inductive Boundary where
  | unpublished
  | finished (word : List Nat)
  | next (width : Nat) (word : List Nat)
  deriving Repr, DecidableEq

def State.boundary (state : State) : Boundary :=
  match state.publish with
  | none => .unpublished
  | some word =>
      if state.width ≥ state.length - state.width then .finished word else .next (2 * state.width) word

theorem next_width_progress (before : Nat → Nat → Bool) (state : State) (valid : Valid before state)
    (width : Nat) (word : List Nat) (next : state.boundary = .next width word) :
    width = 2 * state.width ∧ state.width < width ∧
      state.length - width < state.length - state.width ∧ word.Perm (List.range state.length) := by
  cases published : state.publish with
  | none => simp [State.boundary, published] at next
  | some actual =>
      simp only [State.boundary, published] at next
      split at next
      · cases next
      · have same := Boundary.next.inj next
        have positive := valid.width_pos
        refine ⟨same.1.symm, by omega, by omega, ?_⟩
        simpa only [same.2] using published_permutation before state valid actual published

theorem next_width_uint32 (state : State) (width : Nat) (word : List Nat)
    (bounded : state.length < 2 ^ 32) (next : state.boundary = .next width word) :
    width < state.length ∧ width < 2 ^ 32 := by
  cases published : state.publish with
  | none => simp [State.boundary, published] at next
  | some actual =>
      simp only [State.boundary, published] at next
      split at next
      · cases next
      · have same := Boundary.next.inj next
        constructor <;> omega

theorem final_width_covers (before : Nat → Nat → Bool) (state : State) (valid : Valid before state)
    (word : List Nat) (finished : state.boundary = .finished word) :
    state.length ≤ 2 * state.width ∧ word.Perm (List.range state.length) := by
  cases published : state.publish with
  | none => simp [State.boundary, published] at finished
  | some actual =>
      simp only [State.boundary, published] at finished
      split at finished
      · have same := Boundary.finished.inj finished
        exact ⟨by omega, by simpa only [same] using published_permutation before state valid actual published⟩
      · cases finished

theorem reference_final_merge (before : Nat → Nat → Bool) (width length : Nat)
    (positive : 0 < width) (covers : length ≤ 2 * width) :
    reference before width 0 length =
      List.merge (span 0 (min width length)) (span (min width length) length) before := by
  by_cases empty : length = 0
  · subst length; simp [span]
  · have leftBound := Nat.min_le_right width length
    have clipped : min width (length - min width length) = length - min width length := by omega
    rw [reference, if_neg empty, if_neg (by omega : width ≠ 0)]
    simp only [Nat.zero_add, clipped]
    have exhausted : length - min width length - (length - min width length) = 0 := by omega
    rw [exhausted, reference_zero, List.append_nil]
    simp only [span, Nat.sub_zero]

/-- Ordering is a separate comparison contract. On the final adjacent pair,
sorted inputs plus a total/transitive completed comparison imply sorted output.
The producer still chooses actual heads; the reference is used only in proof. -/
theorem final_pass_sorted (before : Nat → Nat → Bool)
    (transitive : ∀ a b c, before a b = true → before b c = true → before a c = true)
    (total : ∀ a b, (before a b || before b a) = true)
    (length width fuel paid : Nat) (positive : 0 < width) (covers : length ≤ 2 * width)
    (leftSorted : (span 0 (min width length)).Pairwise (fun a b => before a b = true))
    (rightSorted : (span (min width length) length).Pairwise (fun a b => before a b = true))
    (final : State) (finished : (State.start length width).run before fuel =
      (paid, .done ⟨(), .ready, final⟩)) :
    final.word.Pairwise (fun a b => before a b = true) := by
  have earned := completed_cursor before (State.start length width)
    (start_valid before length width positive) fuel paid final finished
  rw [earned.2.2.1]
  change (reference before width 0 length).Pairwise _
  rw [reference_final_merge before width length positive covers]
  exact List.pairwise_merge transitive total _ _ leftSorted rightSorted

/-- A concrete key/ordinal policy; source positions are still distinct from
stored ordinals. No equality or comparison policy for Prime is selected. -/
def keyOrdinal (key ordinal : Nat → Nat) (left right : Nat) : Bool :=
  decide (key left < key right ∨ key left = key right ∧ ordinal left ≤ ordinal right)

theorem keyOrdinal_transitive (key ordinal : Nat → Nat) (first middle last : Nat)
    (left : keyOrdinal key ordinal first middle = true)
    (right : keyOrdinal key ordinal middle last = true) : keyOrdinal key ordinal first last = true := by
  simp only [keyOrdinal, decide_eq_true_eq] at left right ⊢
  omega

theorem keyOrdinal_total (key ordinal : Nat → Nat) (left right : Nat) :
    (keyOrdinal key ordinal left right || keyOrdinal key ordinal right left) = true := by
  simp only [Bool.or_eq_true, keyOrdinal, decide_eq_true_eq]
  omega

/-- The actual final adjacent merge preserves ordinal order within an equal
key class, under the independently stated sorted-input/comparator premises. -/
theorem final_pass_equal_key_ordinals (key ordinal : Nat → Nat)
    (length width fuel paid : Nat) (positive : 0 < width) (covers : length ≤ 2 * width)
    (leftSorted : (span 0 (min width length)).Pairwise
      (fun a b => keyOrdinal key ordinal a b = true))
    (rightSorted : (span (min width length) length).Pairwise
      (fun a b => keyOrdinal key ordinal a b = true))
    (final : State) (finished : (State.start length width).run (keyOrdinal key ordinal) fuel =
      (paid, .done ⟨(), .ready, final⟩)) :
    final.word.Pairwise (fun a b => key a = key b → ordinal a ≤ ordinal b) := by
  have sorted := final_pass_sorted (keyOrdinal key ordinal)
    (keyOrdinal_transitive key ordinal) (keyOrdinal_total key ordinal)
    length width fuel paid positive covers leftSorted rightSorted final finished
  apply sorted.imp
  intro first last ordered sameKey
  simp only [keyOrdinal, decide_eq_true_eq] at ordered
  omega

namespace Controls

set_option maxRecDepth 16384

def descending (left right : Nat) : Bool := decide (right ≤ left)

def twoFinal : State := ⟨2, 1, 2, 1, 1, 2, 2, false, [0, 1], 5⟩

theorem actual_two_cursor : (State.start 2 1).run descending 6 =
    (5, .done ⟨(), .ready, twoFinal⟩) := by rfl

theorem actual_two_earned : twoFinal.word.Perm (List.range 2) ∧ twoFinal.publish = some [1, 0] := by
  have result := completed_cursor descending (State.start 2 1) (start_valid descending 2 1 (by decide))
    6 5 twoFinal actual_two_cursor
  exact ⟨result.2.2.2.1, result.2.1⟩

theorem actual_two_row_owner_transfer :
    (observed BoundedIndexed.Controls.copied.scratch BoundedIndexed.Controls.copied.expected).Perm
        (BoundedIndexed.Controls.rows.map some) ∧
      (ownedKeys (observed BoundedIndexed.Controls.copied.scratch BoundedIndexed.Controls.copied.expected)).Perm
        (BoundedIndexed.Controls.rows.filterMap Row.key) ∧
      BoundedIndexed.Controls.copied.swap =
        some ⟨BoundedIndexed.Controls.copied.scratch, BoundedIndexed.Controls.copied.primary⟩ := by
  apply completed_storage_transfer descending BoundedIndexed.Controls.rows 1 (by decide)
    6 5 twoFinal actual_two_cursor BoundedIndexed.Controls.source BoundedIndexed.Controls.scratch
    BoundedIndexed.Controls.planned_valid.2.2.2.1 BoundedIndexed.Controls.choices 4 3
    BoundedIndexed.Controls.earned_nonempty_prefix BoundedIndexed.Controls.copied
    BoundedIndexed.Controls.actual_completed_run

theorem zero_is_exactly_inert : (State.start 5 1).run descending 0 =
    (0, .paused ((State.start 5 1).packet descending)) := rfl

theorem actual_split_same_receipt_and_residual : (State.start 2 1).run descending (2 + 4) =
    resume (provider descending) client (charge descending) 4 ((State.start 2 1).run descending 2) :=
  run_split descending (State.start 2 1) 2 4

theorem empty_pass_finishes_without_emission :
    (State.start 0 1).run descending 2 =
      (1, .done ⟨(), .ready, { State.start 0 1 with polls := 1 }⟩) := by rfl

def oneFinal : State := ⟨1, 1, 1, 1, 1, 1, 1, false, [0], 4⟩

theorem singleton_is_not_dropped : (State.start 1 1).run descending 5 =
    (4, .done ⟨(), .ready, oneFinal⟩) := by rfl

def oddFinal : State := ⟨5, 1, 5, 5, 5, 5, 5, false, [4, 2, 3, 0, 1], 12⟩

theorem odd_clipped_tail_retained : (State.start 5 1).run descending 13 =
    (12, .done ⟨(), .ready, oddFinal⟩) ∧ oddFinal.word = [1, 0, 3, 2, 4] := by
  constructor <;> rfl

theorem partial_pair_cannot_publish :
    (outcomeState descending ((State.start 2 1).run descending 2).2).publish = none := by rfl

theorem fully_emitted_active_range_still_cannot_publish :
    (outcomeState descending ((State.start 2 1).run descending 3).2).output = 2 ∧
      (outcomeState descending ((State.start 2 1).run descending 3).2).publish = none := by
  constructor <;> rfl

theorem cancellation_retains_exact_unemitted_position :
    (outcomeState descending ((State.start 2 1).run descending 2).2).word = [1] ∧
      (outcomeState descending ((State.start 2 1).run descending 2).2).residual descending = [0] := by
  constructor
  · rfl
  · change List.merge (span 0 1) (span 2 2) descending ++ reference descending 1 2 0 = [0]
    simp [span]

theorem repeated_index_rejected_as_inventory : ¬([0, 0] : List Nat).Perm (List.range 2) := by decide

theorem omitted_index_rejected_as_inventory : ¬([0] : List Nat).Perm (List.range 2) := by decide

def forged : State := ⟨2, 1, 2, 0, 0, 0, 0, false, [0, 0], 0⟩

theorem forged_count_is_not_an_earned_prefix : forged.publish = some [0, 0] ∧ ¬Valid descending forged := by
  refine ⟨rfl, ?_⟩
  intro valid
  exact repeated_index_rejected_as_inventory (published_permutation descending forged valid [0, 0] rfl)

theorem wrong_pair_choice_breaks_reference :
    ¬Valid descending { (outcomeState descending ((State.start 2 1).run descending 2).2) with
      left := 1
      right := 1
      emittedRev := [0] } := by
  intro valid
  have equation := valid.equation
  change [0] ++ (List.merge (span 1 1) (span 1 2) descending ++ reference descending 1 2 0) =
    reference descending 1 0 2 at equation
  have expected : reference descending 1 0 2 = [1, 0] := by simp [reference, descending]
  simp [reference_zero, expected, span] at equation

def equalKey (_index : Nat) : Nat := 7
def backwardOrdinal (index : Nat) : Nat := if index = 0 then 11 else 10

theorem equal_keys_distinct_ordinals_are_not_deduplicated :
    (State.start 2 1).run (keyOrdinal equalKey backwardOrdinal) 6 =
      (5, .done ⟨(), .ready, twoFinal⟩) ∧ equalKey 0 = equalKey 1 ∧ backwardOrdinal 0 ≠ backwardOrdinal 1 := by
  constructor
  · rfl
  · decide

theorem actual_equal_key_ordinal_stability :
    twoFinal.word.Pairwise (fun a b => equalKey a = equalKey b → backwardOrdinal a ≤ backwardOrdinal b) :=
  final_pass_equal_key_ordinals equalKey backwardOrdinal 2 1 6 5 (by decide) (by decide)
    (by decide) (by decide) twoFinal equal_keys_distinct_ordinals_are_not_deduplicated.1

def sameOrdinal (_index : Nat) : Nat := 10
def tieFinal : State := ⟨2, 1, 2, 1, 1, 2, 2, false, [1, 0], 5⟩

theorem equal_completed_keys_keep_left_first :
    (State.start 2 1).run (keyOrdinal equalKey sameOrdinal) 6 =
      (5, .done ⟨(), .ready, tieFinal⟩) ∧ tieFinal.word = [0, 1] := by
  constructor <;> rfl

theorem first_pass_is_not_a_global_sort :
    ¬oddFinal.word.Pairwise (fun left right => descending left right = true) := by decide

theorem width_doubles_only_after_publication : oddFinal.boundary = .next 2 [1, 0, 3, 2, 4] ∧
    (outcomeState descending ((State.start 5 1).run descending 2).2).boundary = .unpublished := by
  constructor <;> rfl

theorem final_two_stops_after_full_merge : twoFinal.boundary = .finished [1, 0] := by rfl

end Controls

end Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed.MergeSchedule

namespace Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed.FrameStack

open Mettapedia.Machines.Cursor

variable {V : Type}

/-- Allocate one typed record, then copy its complete value before any pointer
publication. Byte layout and the fixed native copy are separate services. -/
def newRecord (memory : Storage V) (value : V) (choice : AllocationChoice) :
    Option (Option Ptr × Storage V) := do
  let (pointer, allocated) ← allocate memory 1 choice
  match pointer with
  | none => some (none, allocated)
  | some pointer =>
      let copied ← store allocated pointer value
      some (some pointer, copied)

theorem newRecord_failure (memory : Storage V) (value : V) :
    newRecord memory value .failure = some (none, memory) := rfl

theorem newRecord_fresh (memory : Storage V) (value : V) (identity : BlockId)
    (fresh : memory.lookup identity = none) :
    newRecord memory value (.fresh identity) =
      some (some ⟨identity, 0⟩,
        put (put memory identity ⟨true, [none]⟩) identity ⟨true, [some value]⟩) := by
  simp [newRecord, allocate, fresh, store]

theorem newRecord_published_value (memory next : Storage V) (value : V) (choice : AllocationChoice)
    (pointer : Ptr) (allocated : newRecord memory value choice = some (some pointer, next)) :
    load next pointer = some value ∧ pointer.offset = 0 ∧ memory.lookup pointer.block = none := by
  cases choice with
  | failure => simp [newRecord_failure] at allocated
  | fresh identity =>
      by_cases fresh : memory.lookup identity = none
      · rw [newRecord_fresh memory value identity fresh] at allocated
        obtain ⟨same, rfl⟩ := Prod.mk.inj (Option.some.inj allocated)
        have equal : pointer = ⟨identity, 0⟩ := Option.some.inj same.symm
        subst pointer
        exact ⟨by simp [load], rfl, fresh⟩
      · simp [newRecord, allocate, fresh] at allocated

theorem newRecord_keeps_other (memory next : Storage V) (value : V) (choice : AllocationChoice)
    (pointer other : Ptr) (allocated : newRecord memory value choice = some (some pointer, next))
    (different : other.block ≠ pointer.block) : load next other = load memory other := by
  cases choice with
  | failure => simp [newRecord_failure] at allocated
  | fresh identity =>
      by_cases fresh : memory.lookup identity = none
      · rw [newRecord_fresh memory value identity fresh] at allocated
        obtain ⟨same, rfl⟩ := Prod.mk.inj (Option.some.inj allocated)
        have equal : pointer = ⟨identity, 0⟩ := Option.some.inj same.symm
        subst pointer
        simp only [load_put_other _ _ _ other different]
      · simp [newRecord, allocate, fresh] at allocated

structure Stack (V : Type) where
  backing : Array (Option Ptr)
  records : Storage V
  depth : Nat
  pending : Option V
  recordSize : Nat
  retiring : Bool
  disposed : Nat

def Stack.empty (recordSize : Nat) : Stack V :=
  ⟨Array.empty 8, [], 0, none, recordSize, false, 0⟩

def Stack.committed (state : Stack V) : Nat := state.depth - state.pending.toList.length

/-- The only list below is an independent presentation of the actual memory.
No stack transition stores or traverses this list of records. -/
structure Represents (state : Stack V) (entries : List (Ptr × V)) : Prop where
  depth : state.depth = entries.length + state.pending.toList.length
  bounded : state.depth ≤ 2 ^ 32 - 1
  backing_valid : state.backing.Valid
  records_live : ∀ index pointer value, entries[index]? = some (pointer, value) →
    state.backing.read index = some (some pointer) ∧ load state.records pointer = some value ∧ pointer.offset = 0
  distinct : (entries.map (fun entry => entry.1.block)).Nodup
  covered : ∀ identity block, state.records.lookup identity = some block → block.live = true →
    identity ∈ entries.map (fun entry => entry.1.block)

def Stack.read (state : Stack V) (index : Nat) : Option V :=
  if state.retiring || state.depth ≤ index then none else
    match state.pending with
    | some value => if index = state.depth - 1 then some value else
        (state.backing.read index).join.bind (load state.records)
    | none => (state.backing.read index).join.bind (load state.records)

def Stack.top (state : Stack V) : Option V :=
  if state.depth = 0 then none else state.read (state.depth - 1)

/-- Admission takes the exact pending value without allocating or replaying
any parent computation. The byte size belongs to the static record instance. -/
def Stack.queue (state : Stack V) (size : Nat) (value : V) : Option (Stack V) :=
  if state.retiring || state.pending.isSome || size = 0 || size ≠ state.recordSize ||
      state.backing.elementSize ≠ 8 || 2 ^ 32 - 1 ≤ state.depth then none
  else some { state with depth := state.depth + 1, pending := some value }

inductive Request where
  | backing (kind : Kind)
  | record (bytes : Nat)
  deriving Repr, DecidableEq

def Request.bytes (header pointerBytes : Nat) : Request → Nat
  | .backing kind => kind.requestBytes header pointerBytes 8
  | .record bytes => bytes

structure Reply (V : Type) where
  status : Status
  next : Stack V
  request : Option Request
  record : Option Ptr

def Stack.slotWritable (state : Stack V) : Bool :=
  match state.backing.at (state.depth - 1) with
  | none => false
  | some address => match state.backing.memory.lookup address.block with
    | none => false
    | some block => block.live && decide (address.offset < block.cells.length)

def Stack.slotVacant (state : Stack V) : Bool :=
  (state.backing.read (state.depth - 1)).join.isNone

/-- The record stays unpublished until its complete typed value is stored.
The target cell is checked before requesting the record allocation. -/
def Stack.publishPending (state : Stack V) (recordChoice : AllocationChoice) : Reply V :=
  match state.pending with
  | none => ⟨.ready, state, none, none⟩
  | some value =>
      if !state.slotWritable || !state.slotVacant then ⟨.refused, state, none, none⟩ else
      match newRecord state.records value recordChoice with
      | some (some pointer, records) =>
          match state.backing.write (state.depth - 1) (some pointer) with
          | some backing => ⟨.pending, { state with backing := backing, records := records, pending := none },
              some (.record state.recordSize), some pointer⟩
          | none => ⟨.refused, state, some (.record state.recordSize), none⟩
      | _ => ⟨.refused, state, some (.record state.recordSize), none⟩

/-- A backing preparation action or a complete fixed-record allocation/copy
and pointer publication. Successful publication yields; READY is a later poll.
The typed/separate slot grant below proves prefix preservation. -/
def Stack.advance (state : Stack V) (pageChoice recordChoice : AllocationChoice) : Reply V :=
  if state.retiring || state.recordSize = 0 || state.backing.elementSize ≠ 8 then
    ⟨.refused, state, none, none⟩ else
  match state.pending with
  | none => ⟨.ready, state, none, none⟩
  | some _ =>
      let prepared := state.backing.prepare (state.depth - 1) pageChoice
      let kept := { state with backing := prepared.next }
      match prepared.status with
      | .pending => ⟨.pending, kept, prepared.request.map Request.backing, none⟩
      | .refused => ⟨.refused, kept, prepared.request.map Request.backing, none⟩
      | .ready => kept.publishPending recordChoice

/-- Typed target cell and separation from the existing committed prefix.
This local representation grant is weaker than any desired final-stack law. -/
def Stack.WriteAdmission (state : Stack V) : Prop :=
  ∀ address, state.backing.at (state.depth - 1) = some address →
    (∃ block, state.backing.memory.lookup address.block = some block ∧
      block.live = true ∧ address.offset < block.cells.length) ∧
    DataCell state.backing.memory address ∧
      ∀ index < state.depth - 1, ∃ previous, state.backing.at index = some previous ∧ previous ≠ address

def Stack.PublishAdmission (state : Stack V) : Prop := state.WriteAdmission ∧ state.slotVacant = true

theorem empty_represents (size : Nat) : Represents (Stack.empty (V := V) size) [] := by
  refine ⟨rfl, by simp [Stack.empty], Array.empty_valid 8, ?_, by simp, ?_⟩
  · intro index pointer value member; simp at member
  · intro identity block found; simp [Stack.empty] at found

theorem queue_fields (state next : Stack V) (size : Nat) (value : V)
    (queued : state.queue size value = some next) :
    state.pending = none ∧ state.retiring = false ∧ 0 < state.recordSize ∧ state.backing.elementSize = 8 ∧
      next = { state with depth := state.depth + 1, pending := some value } := by
  simp only [Stack.queue] at queued
  split at queued
  · cases queued
  · rename_i allowed
    have parts : state.retiring = false ∧ state.pending = none ∧ size ≠ 0 ∧ size = state.recordSize ∧
        state.backing.elementSize = 8 ∧ state.depth < 2 ^ 32 - 1 := by simpa [and_assoc] using allowed
    exact ⟨parts.2.1, parts.1, by omega, parts.2.2.2.2.1, (Option.some.inj queued).symm⟩

theorem queue_represents (state next : Stack V) (entries : List (Ptr × V))
    (valid : Represents state entries) (size : Nat) (value : V)
    (queued : state.queue size value = some next) : Represents next entries := by
  have fields := queue_fields state next size value queued
  have bounded : state.depth < 2 ^ 32 - 1 := by
    simp only [Stack.queue] at queued
    split at queued
    · cases queued
    · rename_i allowed
      have parts : state.retiring = false ∧ state.pending = none ∧ size ≠ 0 ∧ size = state.recordSize ∧
          state.backing.elementSize = 8 ∧ state.depth < 2 ^ 32 - 1 := by simpa [and_assoc] using allowed
      exact parts.2.2.2.2.2
  rw [fields.2.2.2.2]
  refine ⟨?_, by dsimp; omega, valid.backing_valid, valid.records_live, valid.distinct, valid.covered⟩
  have depth := valid.depth
  simp only [fields.1, Option.toList_none, List.length_nil, Nat.add_zero] at depth
  simp [depth]

theorem queued_top (state next : Stack V) (size : Nat) (value : V)
    (queued : state.queue size value = some next) : next.top = some value := by
  have fields := queue_fields state next size value queued
  rw [fields.2.2.2.2]
  simp [Stack.top, Stack.read, fields.2.1]

theorem queue_preserves_parent (state next : Stack V) (size : Nat) (value : V)
    (queued : state.queue size value = some next) :
    next.records = state.records ∧ next.backing = state.backing ∧
      next.pending = some value ∧ next.depth = state.depth + 1 := by
  rw [(queue_fields state next size value queued).2.2.2.2]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem writable_write (state : Stack V) (pointer : Option Ptr)
    (writable : state.slotWritable = true) :
    ∃ backing, state.backing.write (state.depth - 1) pointer = some backing := by
  cases location : state.backing.at (state.depth - 1) with
  | none => simp [Stack.slotWritable, location] at writable
  | some address =>
      cases found : state.backing.memory.lookup address.block with
      | none => simp [Stack.slotWritable, location, found] at writable
      | some block =>
          have valid : block.live = true ∧ address.offset < block.cells.length := by
            simpa [Stack.slotWritable, location, found] using writable
          let nextMemory := put state.backing.memory address.block
            { block with cells := block.cells.set address.offset (some (.inr pointer)) }
          exact ⟨{ state.backing with memory := nextMemory },
            by simp [Array.write, location, store, found, valid, nextMemory]⟩

theorem admission_writable (state : Stack V) (admitted : state.WriteAdmission)
    (address : Ptr) (location : state.backing.at (state.depth - 1) = some address) :
    state.slotWritable = true := by
  obtain ⟨block, found, live, inside⟩ := (admitted address location).1
  simp [Stack.slotWritable, location, found, live, inside]

theorem newRecord_lookup_other (memory next : Storage V) (value : V) (choice : AllocationChoice)
    (pointer : Ptr) (allocated : newRecord memory value choice = some (some pointer, next))
    (identity : BlockId) (different : identity ≠ pointer.block) : next.lookup identity = memory.lookup identity := by
  cases choice with
  | failure => simp [newRecord_failure] at allocated
  | fresh freshId =>
      by_cases fresh : memory.lookup freshId = none
      · rw [newRecord_fresh memory value freshId fresh] at allocated
        obtain ⟨same, rfl⟩ := Prod.mk.inj (Option.some.inj allocated)
        have equal : pointer = ⟨freshId, 0⟩ := Option.some.inj same.symm
        subst pointer
        simp only [lookup_put_other _ _ _ _ different]
      · simp [newRecord, allocate, fresh] at allocated

theorem fresh_differs_from_loaded (memory : Storage V) (pointer : Ptr) (value : V)
    (loaded : load memory pointer = some value) (identity : BlockId) (fresh : memory.lookup identity = none) :
    pointer.block ≠ identity := by
  intro same
  simp [load, same, fresh] at loaded

theorem prepare_represents (state : Stack V) (entries : List (Ptr × V))
    (valid : Represents state entries) (choice : AllocationChoice) :
    Represents { state with backing := (state.backing.prepare (state.depth - 1) choice).next } entries := by
  refine ⟨valid.depth, valid.bounded, state.backing.prepare_valid _ choice valid.backing_valid,
    ?_, valid.distinct, valid.covered⟩
  intro index pointer value found
  have previous := valid.records_live index pointer value found
  exact ⟨state.backing.prepare_preserves_read _ index choice (some pointer) previous.1,
    previous.2.1, previous.2.2⟩

theorem committed_read (state : Stack V) (entries : List (Ptr × V)) (valid : Represents state entries)
    (live : state.retiring = false) (index : Nat) (pointer : Ptr) (value : V)
    (found : entries[index]? = some (pointer, value)) : state.read index = some value := by
  have inside : index < entries.length := (List.getElem?_eq_some_iff.mp found).1
  have depth := valid.depth
  have stored := valid.records_live index pointer value found
  cases pending : state.pending with
  | none =>
      have bounded : index < state.depth := by simp [pending] at depth; omega
      simp [Stack.read, live, show ¬state.depth ≤ index by omega, pending, stored.1, stored.2.1]
  | some saved =>
      have bounded : index < state.depth := by simp [pending] at depth; omega
      have different : index ≠ state.depth - 1 := by simp [pending] at depth; omega
      simp [Stack.read, live, show ¬state.depth ≤ index by omega, pending, different, stored.1, stored.2.1]

theorem queue_preserves_reads (state next : Stack V) (size : Nat) (value : V)
    (queued : state.queue size value = some next) (index : Nat) (earlier : index < state.depth) :
    next.read index = state.read index := by
  have fields := queue_fields state next size value queued
  rw [fields.2.2.2.2]
  simp [Stack.read, fields.2.1, fields.1, show ¬state.depth ≤ index by omega,
    show ¬state.depth + 1 ≤ index by omega, show index ≠ state.depth by omega]

theorem commit_represents (state : Stack V) (entries : List (Ptr × V)) (valid : Represents state entries)
    (value : V) (pending : state.pending = some value) (admitted : state.WriteAdmission)
    (pointer : Ptr) (records : Storage V) (choice : AllocationChoice)
    (allocated : newRecord state.records value choice = some (some pointer, records))
    (backing : Array (Option Ptr))
    (written : state.backing.write (state.depth - 1) (some pointer) = some backing) :
    Represents { state with backing := backing, records := records, pending := none } (entries ++ [(pointer, value)]) := by
  have depth : state.depth = entries.length + 1 := by simpa [pending] using valid.depth
  have fresh := newRecord_published_value state.records records value choice pointer allocated
  obtain ⟨address, location⟩ : ∃ address, state.backing.at (state.depth - 1) = some address := by
    cases location : state.backing.at (state.depth - 1) with
    | none => simp [Array.write, location] at written
    | some address => exact ⟨address, rfl⟩
  have support := admitted address location
  have lastRead := state.backing.write_read_same backing (state.depth - 1) (some pointer)
    address location support.2.1 written
  have notOld : pointer.block ∉ entries.map (fun entry => entry.1.block) := by
    intro member
    obtain ⟨⟨previous, content⟩, occurs, same⟩ := List.mem_map.mp member
    obtain ⟨index, found⟩ := List.getElem?_of_mem occurs
    have loaded := (valid.records_live index previous content found).2.1
    have different := fresh_differs_from_loaded state.records previous content loaded pointer.block fresh.2.2
    exact different same
  refine ⟨by simp [depth], valid.bounded, state.backing.write_valid backing _ _ valid.backing_valid written,
    ?_, ?_, ?_⟩
  · intro index previous content found
    by_cases prior : index < entries.length
    · have old : entries[index]? = some (previous, content) := by
        simpa only [List.getElem?_append, if_pos prior] using found
      have stored := valid.records_live index previous content old
      obtain ⟨priorAddress, priorAt, different⟩ := support.2.2 index (by omega)
      have kept := state.backing.write_read_other backing (state.depth - 1) (some pointer)
        address location support.2.1 written index priorAddress priorAt different
      have separate := fresh_differs_from_loaded state.records previous content stored.2.1 pointer.block fresh.2.2
      exact ⟨kept.trans stored.1,
        (newRecord_keeps_other state.records records value choice pointer previous allocated separate).trans stored.2.1,
        stored.2.2⟩
    · have indexEq : index = entries.length := by
        have bounded := (List.getElem?_eq_some_iff.mp found).1
        simp only [List.length_append, List.length_singleton] at bounded
        omega
      subst index
      have same : pointer = previous ∧ value = content := by simpa using found
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨by simpa [depth] using lastRead, fresh.1, fresh.2.1⟩
  · simpa only [List.map_append, List.map_cons, List.map_nil, List.concat_eq_append] using valid.distinct.concat notOld
  · intro identity block found live
    by_cases same : identity = pointer.block
    · simp [same]
    · have previous := newRecord_lookup_other state.records records value choice pointer allocated identity same
      have member := valid.covered identity block (previous ▸ found) live
      simpa only [List.map_append, List.map_cons, List.map_nil] using
        (List.mem_append_left [pointer.block] member)

theorem publish_fresh (state : Stack V) (value : V) (pending : state.pending = some value)
    (writable : state.slotWritable = true) (vacant : state.slotVacant = true) (identity : BlockId) (fresh : state.records.lookup identity = none) :
    ∃ backing records, state.backing.write (state.depth - 1) (some ⟨identity, 0⟩) = some backing ∧
      newRecord state.records value (.fresh identity) = some (some ⟨identity, 0⟩, records) ∧
      state.publishPending (.fresh identity) =
        ⟨.pending, { state with backing := backing, records := records, pending := none },
          some (.record state.recordSize), some ⟨identity, 0⟩⟩ := by
  obtain ⟨backing, written⟩ := writable_write state (some ⟨identity, 0⟩) writable
  refine ⟨backing, _, written, newRecord_fresh _ _ _ fresh, ?_⟩
  simp [Stack.publishPending, pending, writable, vacant, newRecord_fresh _ _ _ fresh, written]

theorem publish_allocation_refusal (state : Stack V) (value : V) (pending : state.pending = some value) :
    (state.publishPending .failure).status = .refused ∧ (state.publishPending .failure).next = state := by
  cases writable : state.slotWritable <;> cases vacant : state.slotVacant <;>
    simp [Stack.publishPending, pending, writable, vacant, newRecord_failure]

theorem advance_ready_keeps (state : Stack V) (pageChoice recordChoice : AllocationChoice)
    (live : state.retiring = false) (positive : 0 < state.recordSize) (configured : state.backing.elementSize = 8)
    (value : V) (pending : state.pending = some value)
    (ready : (state.backing.prepare (state.depth - 1) pageChoice).status = .ready) :
    state.advance pageChoice recordChoice = state.publishPending recordChoice := by
  have kept := state.backing.ready_keeps_residual (state.depth - 1) pageChoice ready
  have allowed : (state.retiring || state.recordSize = 0 || state.backing.elementSize ≠ 8) = false := by
    simp [live, Nat.ne_of_gt positive, configured]
  simp only [Stack.advance, allowed, Bool.false_eq_true, ↓reduceIte, pending, ready, kept]
  have same : { state with pending := some value } = state := by rw [← pending]
  exact congrArg (fun next : Stack V => next.publishPending recordChoice) same

theorem prepare_ready_address (backing : Array (Option Ptr)) (index : Nat) (choice : AllocationChoice)
    (ready : (backing.prepare index choice).status = .ready) : ∃ address, backing.at index = some address := by
  by_cases invalid : backing.elementSize = 0 ∨ 256 < backing.elementSize ∨ backing.retiring = true ∨ 2 ^ 32 ≤ index
  · simp only [Array.prepare, if_pos invalid, reduceCtorEq] at ready
  · simp only [Array.prepare, if_neg invalid] at ready
    cases root : backing.root with
    | none => exact (backing.install_not_ready none .directory choice 0 (by simpa only [root] using ready)).elim
    | some pointer =>
        cases observed : (seek backing.memory pointer (route index)).2 with
        | ready leaf => exact ⟨leaf + offset index, by simp only [Array.at, if_neg invalid, root, Option.bind_some, observed]⟩
        | refused => simp [root, observed] at ready
        | missing slot suffix =>
            exact (backing.install_not_ready (some slot) (if suffix.isEmpty then .elements else .directory)
              choice (seek backing.memory pointer (route index)).1 (by simpa [root, observed] using ready)).elim

theorem write_fields (before after : Array (Option Ptr)) (index : Nat) (value : Option Ptr)
    (written : before.write index value = some after) :
    after.chain = before.chain ∧ after.elementSize = before.elementSize ∧
      after.retiring = before.retiring ∧ after.root = before.root := by
  cases location : before.at index with
  | none => simp [Array.write, location] at written
  | some address =>
      cases stored : store before.memory address (.inr value) with
      | none => simp [Array.write, location, stored] at written
      | some memory =>
          have same : { before with memory := memory } = after := by
            simpa [Array.write, location, stored] using written
          subst after
          exact ⟨rfl, rfl, rfl, rfl⟩

theorem advance_install (state : Stack V) (pageChoice recordChoice : AllocationChoice)
    (live : state.retiring = false) (positive : 0 < state.recordSize) (configured : state.backing.elementSize = 8)
    (value : V) (pending : state.pending = some value)
    (installing : (state.backing.prepare (state.depth - 1) pageChoice).status = .pending) :
    state.advance pageChoice recordChoice = ⟨.pending,
      { state with backing := (state.backing.prepare (state.depth - 1) pageChoice).next },
      (state.backing.prepare (state.depth - 1) pageChoice).request.map Request.backing, none⟩ := by
  have allowed : (state.retiring || state.recordSize = 0 || state.backing.elementSize ≠ 8) = false := by
    simp [live, Nat.ne_of_gt positive, configured]
  simp only [Stack.advance, allowed, Bool.false_eq_true, ↓reduceIte, pending, installing]

theorem advance_no_pending (state : Stack V) (pageChoice recordChoice : AllocationChoice)
    (live : state.retiring = false) (positive : 0 < state.recordSize) (configured : state.backing.elementSize = 8)
    (pending : state.pending = none) :
    state.advance pageChoice recordChoice = ⟨.ready, state, none, none⟩ := by
  simp [Stack.advance, live, Nat.ne_of_gt positive, configured, pending]

def pushProvider (page record : Stack V → AllocationChoice) : Provider protocol where
  State _ _ := Stack V
  step state _ := ⟨(state.advance (page state) (record state)).status,
    (state.advance (page state) (record state)).next⟩

def pushCharge (page record : Stack V → AllocationChoice) : Charge (pushProvider page record) := fun _ _ => 1

def Stack.pushPacket (page record : Stack V → AllocationChoice) (state : Stack V) : Packet (pushProvider page record) client () :=
  ⟨(), none, state⟩

def Stack.pushRun (page record : Stack V → AllocationChoice) (fuel : Nat) (state : Stack V) :=
  Cursor.advance (pushProvider page record) client (pushCharge page record) fuel (state.pushPacket page record)

theorem push_zero (page record : Stack V → AllocationChoice) (state : Stack V) :
    state.pushRun page record 0 = (0, .paused (state.pushPacket page record)) := rfl

theorem push_split (page record : Stack V → AllocationChoice) (state : Stack V) (first later : Nat) :
    state.pushRun page record (first + later) =
      resume (pushProvider page record) client (pushCharge page record) later (state.pushRun page record first) :=
  advance_add _ _ _ first later (state.pushPacket page record)

private theorem fs_client_poll : client.str () () none =
    ⟨.inr (), fun (status : Status) => if status = .pending then none else some status⟩ := by
  unfold client
  dsimp only
  simp only [TypeCat.ofHom, CategoryTheory.ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  rfl

private theorem fs_client_done (status : Status) : client.str () () (some status) =
    ⟨.inl status, fun impossible => nomatch impossible⟩ := by
  unfold client
  dsimp only
  simp only [TypeCat.ofHom, CategoryTheory.ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply]
  congr 1
  funext impossible
  nomatch impossible

private theorem push_poll (page record : Stack V → AllocationChoice) (state : Stack V) (fuel : Nat) :
    Cursor.advance (pushProvider page record) client (pushCharge page record) (fuel + 1)
      (base := ()) ⟨(), none, state⟩ =
      let response := state.advance (page state) (record state)
      let rest := Cursor.advance (pushProvider page record) client (pushCharge page record) fuel
        (base := ()) ⟨(), if response.status = .pending then none else some response.status, response.next⟩
      (1 + rest.1, rest.2) := by
  simp only [Cursor.advance, fs_client_poll]
  rfl

private theorem push_done (page record : Stack V → AllocationChoice) (state : Stack V) (fuel : Nat) (status : Status) :
    Cursor.advance (pushProvider page record) client (pushCharge page record) (fuel + 1)
      (base := ()) ⟨(), some status, state⟩ = (0, .done ⟨(), status, state⟩) := by
  simp only [Cursor.advance, fs_client_done]

/-- Local typed-slot support is required only at the publication state reached
by these actual successive installation actions. This is a proof predicate,
not a second execution or a completed-stack premise. -/
def Stack.PushAdmission (page record : Stack V → AllocationChoice) : Nat → Stack V → Prop
  | 0, state => state.PublishAdmission
  | count + 1, state =>
      Stack.PushAdmission page record count (state.advance (page state) (record state)).next

def freshChoice (choose : Stack V → BlockId) : Stack V → AllocationChoice := fun state => .fresh (choose state)

theorem push_finite (page record : Stack V → BlockId)
    (pageFresh : ∀ state : Stack V, state.backing.memory.lookup (page state) = none)
    (recordFresh : ∀ state : Stack V, state.records.lookup (record state) = none)
    (state : Stack V) (entries : List (Ptr × V)) (valid : Represents state entries)
    (live : state.retiring = false) (positive : 0 < state.recordSize) (configured : state.backing.elementSize = 8)
    (value : V) (pending : state.pending = some value) (count : Nat)
    (remaining : state.backing.remainingInstalls (state.depth - 1) = some count)
    (admitted : Stack.PushAdmission (freshChoice page) (freshChoice record) count state) :
    ∃ pointer final,
      state.pushRun (freshChoice page) (freshChoice record) (count + 3) = (count + 2, .done ⟨(), .ready, final⟩) ∧
        Represents final (entries ++ [(pointer, value)]) ∧ final.pending = none ∧
        final.depth = state.depth ∧ final.recordSize = state.recordSize ∧ final.retiring = false ∧
        final.backing.chain.length = state.backing.chain.length + count := by
  induction count generalizing state with
  | zero =>
      have ready := (state.backing.remaining_ready (state.depth - 1) (.fresh (page state)) remaining).1
      obtain ⟨address, location⟩ := prepare_ready_address state.backing (state.depth - 1) (.fresh (page state)) ready
      have writable := admission_writable state admitted.1 address location
      obtain ⟨backing, records, written, allocated, published⟩ :=
        publish_fresh state value pending writable admitted.2 (record state) (recordFresh state)
      let final := { state with backing := backing, records := records, pending := none }
      have first := (advance_ready_keeps state (.fresh (page state)) (.fresh (record state))
        live positive configured value pending ready).trans published
      have headers := write_fields state.backing backing (state.depth - 1) (some ⟨record state, 0⟩) written
      have next : final.advance (.fresh (page final)) (.fresh (record final)) = ⟨.ready, final, none, none⟩ :=
        advance_no_pending final _ _ live positive (headers.2.1.trans configured) rfl
      refine ⟨⟨record state, 0⟩, final, ?_,
        commit_represents state entries valid value pending admitted.1 _ _ _ allocated backing written,
        rfl, rfl, rfl, live, ?_⟩
      · have finalRun : final.pushRun (freshChoice page) (freshChoice record) 2 = (1, .done ⟨(), .ready, final⟩) := by
          change Cursor.advance (pushProvider (freshChoice page) (freshChoice record)) client (pushCharge (freshChoice page) (freshChoice record)) (1 + 1)
            (base := ()) ⟨(), none, final⟩ = _
          rw [push_poll]
          simp only [freshChoice, next, reduceCtorEq, ↓reduceIte, push_done, Nat.add_zero]
        change Cursor.advance (pushProvider (freshChoice page) (freshChoice record)) client (pushCharge (freshChoice page) (freshChoice record)) (2 + 1)
          (base := ()) ⟨(), none, state⟩ = _
        rw [push_poll]
        simp only [freshChoice, first, ↓reduceIte]
        change (1 + (final.pushRun (freshChoice page) (freshChoice record) 2).1, (final.pushRun (freshChoice page) (freshChoice record) 2).2) = _
        rw [finalRun]
        rfl
      · simpa only [Nat.add_zero] using congrArg List.length headers.1
  | succ count ih =>
      have progress := state.backing.prepare_progress (state.depth - 1) (page state) count remaining (pageFresh state)
      let next := { state with backing := (state.backing.prepare (state.depth - 1) (.fresh (page state))).next }
      have first := advance_install state (.fresh (page state)) (.fresh (record state))
        live positive configured value pending progress.1
      have nextValid : Represents next entries := prepare_represents state entries valid (.fresh (page state))
      have headers := state.backing.prepare_fields (state.depth - 1) (.fresh (page state))
      have support : Stack.PushAdmission (freshChoice page) (freshChoice record) count next := by
        simpa only [Stack.PushAdmission, freshChoice, first] using admitted
      obtain ⟨pointer, final, finished, represented, noPending, depth, size, living, chain⟩ :=
        ih next nextValid live positive (headers.1.trans configured) pending progress.2.1 support
      refine ⟨pointer, final, ?_, represented, noPending, depth, size, living, ?_⟩
      · change Cursor.advance (pushProvider (freshChoice page) (freshChoice record)) client (pushCharge (freshChoice page) (freshChoice record)) ((count + 3) + 1)
          (base := ()) ⟨(), none, state⟩ = _
        rw [push_poll]
        simp only [freshChoice, first, ↓reduceIte]
        change (1 + (next.pushRun (freshChoice page) (freshChoice record) (count + 3)).1, (next.pushRun (freshChoice page) (freshChoice record) (count + 3)).2) = _
        rw [finished]
        congr 1
        omega
      · change final.backing.chain.length = _ at chain ⊢
        dsimp only [next] at chain
        have countChanged := progress.2.2
        omega

def pushOutcomeState (page record : Stack V → AllocationChoice) : Outcome (pushProvider page record) client () → Stack V
  | .paused ⟨(), _, state⟩ => state
  | .done ⟨(), _, state⟩ => state

def logicalValues (state : Stack V) (entries : List (Ptr × V)) : List V :=
  entries.map Prod.snd ++ state.pending.toList

private theorem no_pending_prefix (page record : Stack V → AllocationChoice) (fuel : Nat)
    (control : Option Status) (state : Stack V) (live : state.retiring = false)
    (positive : 0 < state.recordSize) (configured : state.backing.elementSize = 8) (pending : state.pending = none) :
    pushOutcomeState page record (Cursor.advance (pushProvider page record) client (pushCharge page record) fuel
      (base := ()) ⟨(), control, state⟩).2 = state := by
  induction fuel generalizing control with
  | zero => rfl
  | succ fuel ih =>
      cases control with
      | some status => rw [push_done]; rfl
      | none =>
          rw [push_poll]
          simp only [advance_no_pending state _ _ live positive configured pending, reduceCtorEq, ↓reduceIte]
          exact ih (some .ready)

/-- Every pause retains the actual earlier record-address prefix and the
same complete logical values, including the exact saved pending record.
The fresh provider and earned publication-cell support are explicit. -/
theorem push_prefix (page record : Stack V → BlockId)
    (pageFresh : ∀ state : Stack V, state.backing.memory.lookup (page state) = none)
    (recordFresh : ∀ state : Stack V, state.records.lookup (record state) = none)
    (state : Stack V) (entries : List (Ptr × V)) (valid : Represents state entries)
    (live : state.retiring = false) (positive : 0 < state.recordSize) (configured : state.backing.elementSize = 8)
    (value : V) (pending : state.pending = some value) (count : Nat)
    (remaining : state.backing.remainingInstalls (state.depth - 1) = some count)
    (admitted : Stack.PushAdmission (freshChoice page) (freshChoice record) count state) (fuel : Nat) :
    let final := pushOutcomeState (freshChoice page) (freshChoice record)
      (state.pushRun (freshChoice page) (freshChoice record) fuel).2
    ∃ nextEntries, Represents final nextEntries ∧ entries.IsPrefix nextEntries ∧
      logicalValues final nextEntries = logicalValues state entries := by
  induction count generalizing state fuel with
  | zero =>
      cases fuel with
      | zero => exact ⟨entries, valid, List.prefix_rfl, rfl⟩
      | succ fuel =>
          have ready := (state.backing.remaining_ready _ (.fresh (page state)) remaining).1
          obtain ⟨address, location⟩ := prepare_ready_address state.backing _ (.fresh (page state)) ready
          obtain ⟨backing, records, written, allocated, published⟩ := publish_fresh state value pending
            (admission_writable state admitted.1 address location) admitted.2 (record state) (recordFresh state)
          let final := { state with backing := backing, records := records, pending := none }
          have first := (advance_ready_keeps state (.fresh (page state)) (.fresh (record state))
            live positive configured value pending ready).trans published
          have headers := write_fields state.backing backing _ _ written
          have kept := no_pending_prefix (freshChoice page) (freshChoice record) fuel none final
            live positive (headers.2.1.trans configured) rfl
          have outcome : pushOutcomeState (freshChoice page) (freshChoice record)
              (state.pushRun (freshChoice page) (freshChoice record) (fuel + 1)).2 = final := by
            rw [Stack.pushRun, Stack.pushPacket, push_poll]
            simp only [freshChoice, first, ↓reduceIte]
            convert kept using 1
          change ∃ nextEntries, Represents
            (pushOutcomeState (freshChoice page) (freshChoice record)
              (state.pushRun (freshChoice page) (freshChoice record) (fuel + 1)).2) nextEntries ∧
            entries.IsPrefix nextEntries ∧ logicalValues
              (pushOutcomeState (freshChoice page) (freshChoice record)
                (state.pushRun (freshChoice page) (freshChoice record) (fuel + 1)).2) nextEntries = logicalValues state entries
          rw [outcome]
          refine ⟨entries ++ [(⟨record state, 0⟩, value)],
            commit_represents state entries valid value pending admitted.1 _ _ _ allocated backing written,
            ⟨[(⟨record state, 0⟩, value)], rfl⟩, ?_⟩
          simp [logicalValues, final, pending]
  | succ count ih =>
      cases fuel with
      | zero => exact ⟨entries, valid, List.prefix_rfl, rfl⟩
      | succ fuel =>
          have progress := state.backing.prepare_progress _ (page state) count remaining (pageFresh state)
          let next := { state with backing := (state.backing.prepare (state.depth - 1) (.fresh (page state))).next }
          have first := advance_install state (.fresh (page state)) (.fresh (record state))
            live positive configured value pending progress.1
          have support : Stack.PushAdmission (freshChoice page) (freshChoice record) count next := by
            simpa only [Stack.PushAdmission, freshChoice, first] using admitted
          have headers := state.backing.prepare_fields (state.depth - 1) (.fresh (page state))
          have rest := ih next (prepare_represents state entries valid (.fresh (page state))) live positive
            (headers.1.trans configured) pending progress.2.1 support fuel
          have outcome : pushOutcomeState (freshChoice page) (freshChoice record)
              (state.pushRun (freshChoice page) (freshChoice record) (fuel + 1)).2 =
              pushOutcomeState (freshChoice page) (freshChoice record)
                (next.pushRun (freshChoice page) (freshChoice record) fuel).2 := by
            rw [Stack.pushRun, Stack.pushPacket, push_poll]
            simp only [freshChoice, first, ↓reduceIte]
            rfl
          change ∃ nextEntries, Represents
            (pushOutcomeState (freshChoice page) (freshChoice record)
              (state.pushRun (freshChoice page) (freshChoice record) (fuel + 1)).2) nextEntries ∧
            entries.IsPrefix nextEntries ∧ logicalValues
              (pushOutcomeState (freshChoice page) (freshChoice record)
                (state.pushRun (freshChoice page) (freshChoice record) (fuel + 1)).2) nextEntries = logicalValues state entries
          rw [outcome]
          exact rest


/-- Raw record retirement. The caller must first retire owned record contents;
the typed lifecycle adapter supplies that admission. This operation does not
authenticate an arbitrary payload-ownership assertion. -/
def Stack.pop (state : Stack V) : Option (Stack V) :=
  if state.retiring || state.depth = 0 then none else
  match state.pending with
  | some _ => some { state with depth := state.depth - 1, pending := none }
  | none => do
      let pointer ← (state.backing.read (state.depth - 1)).join
      let _ ← load state.records pointer
      let backing ← state.backing.write (state.depth - 1) none
      let records ← free state.records (some pointer)
      some { state with
        backing := backing
        records := records
        depth := state.depth - 1
        disposed := state.disposed + 1 }

theorem pending_pop (state : Stack V) (entries : List (Ptr × V)) (valid : Represents state entries)
    (live : state.retiring = false) (value : V) (pending : state.pending = some value) :
    state.pop = some { state with depth := state.depth - 1, pending := none } ∧
      Represents { state with depth := state.depth - 1, pending := none } entries := by
  have depth : state.depth = entries.length + 1 := by simpa [pending] using valid.depth
  have bound := valid.bounded
  refine ⟨by simp [Stack.pop, live, show state.depth ≠ 0 by omega, pending],
    ?_, by dsimp; omega, valid.backing_valid, valid.records_live, valid.distinct, valid.covered⟩
  simp [depth]

theorem free_initialized (memory : Storage V) (pointer : Ptr) (value : V)
    (loaded : load memory pointer = some value) (base : pointer.offset = 0) :
    ∃ block, memory.lookup pointer.block = some block ∧ block.live = true ∧
      free memory (some pointer) = some (put memory pointer.block { block with live := false }) ∧
      load (put memory pointer.block { block with live := false }) pointer = none := by
  obtain ⟨block, found, live, _⟩ := load_present memory pointer value loaded
  exact ⟨block, found, live, by simp [free, found, live, base], by simp [load]⟩

theorem committed_pop (state : Stack V) (entries : List (Ptr × V)) (pointer : Ptr) (value : V)
    (valid : Represents state (entries ++ [(pointer, value)])) (live : state.retiring = false)
    (pending : state.pending = none) (admitted : state.WriteAdmission) :
    ∃ next,
      state.pop = some next ∧ Represents next entries ∧ next.depth = state.depth - 1 ∧
        next.disposed = state.disposed + 1 ∧ next.pending = none ∧ next.retiring = false ∧
        next.recordSize = state.recordSize ∧ next.backing.chain = state.backing.chain ∧
        load next.records pointer = none ∧ next.backing.read (state.depth - 1) = some none := by
  have depth : state.depth = entries.length + 1 := by simpa [pending] using valid.depth
  have last := valid.records_live entries.length pointer value (by simp)
  have readLast : state.backing.read (state.depth - 1) = some (some pointer) := by simpa [depth] using last.1
  obtain ⟨address, location⟩ : ∃ address, state.backing.at (state.depth - 1) = some address := by
    cases location : state.backing.at (state.depth - 1) with
    | none => simp [Array.read, location] at readLast
    | some address => exact ⟨address, rfl⟩
  have support := admitted address location
  have writable := admission_writable state admitted address location
  obtain ⟨backing, written⟩ := writable_write state none writable
  have nulled := state.backing.write_read_same backing (state.depth - 1) none address location support.2.1 written
  obtain ⟨block, found, allocated, freed, dead⟩ := free_initialized state.records pointer value last.2.1 last.2.2
  let records := put state.records pointer.block { block with live := false }
  let next := { state with
    backing := backing
    records := records
    depth := state.depth - 1
    disposed := state.disposed + 1 }
  have distinct : (entries.map (fun entry => entry.1.block) ++ [pointer.block]).Nodup := by
    simpa only [List.map_append, List.map_cons, List.map_nil] using valid.distinct
  have notOld : pointer.block ∉ entries.map (fun entry => entry.1.block) := by
    intro member
    exact distinct.disjoint member (by simp)
  have represented : Represents next entries := by
    refine ⟨by simp [next, depth, pending], by dsimp [next]; have bound := valid.bounded; omega,
      state.backing.write_valid _ _ _ valid.backing_valid written, ?_, distinct.of_append_left, ?_⟩
    · intro index previous content present
      have inside : index < entries.length := (List.getElem?_eq_some_iff.mp present).1
      have old := valid.records_live index previous content (by
        simpa only [List.getElem?_append, if_pos inside] using present)
      obtain ⟨priorAddress, priorAt, different⟩ := support.2.2 index (by omega)
      have kept := state.backing.write_read_other backing (state.depth - 1) none address location support.2.1
        written index priorAddress priorAt different
      have separate : previous.block ≠ pointer.block := by
        intro same
        have member : previous.block ∈ entries.map (fun entry => entry.1.block) :=
          List.mem_map.mpr ⟨(previous, content), List.mem_of_getElem? present, rfl⟩
        exact notOld (same ▸ member)
      exact ⟨kept.trans old.1,
        (load_put_other state.records pointer.block { block with live := false } previous separate).trans old.2.1,
        old.2.2⟩
    · intro identity current currentFound currentLive
      by_cases same : identity = pointer.block
      · have equal : current = { block with live := false } := by
          simpa [next, records, same] using currentFound.symm
        simp [equal] at currentLive
      · have previous : state.records.lookup identity = some current := by
          simpa [next, records, lookup_put_other _ _ _ _ same] using currentFound
        have member := valid.covered identity current previous currentLive
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at member
        exact member.resolve_right same
  refine ⟨next, ?_, represented, rfl, rfl, pending, live, rfl,
    (write_fields state.backing backing _ _ written).1, dead, nulled⟩
  simp only [Stack.pop, live, Bool.false_or, show state.depth ≠ 0 by omega, decide_false,
    Bool.false_eq_true, ↓reduceIte, pending, readLast, Option.join_some, Option.bind_eq_bind, Option.bind_some,
    last.2.1, written, freed]
  simp [next, records, live, pending]

/-- Backing retirement is admitted only after every logical frame has gone.
It never calls record or payload destructors. -/
def Stack.releaseBacking (state : Stack V) : Reply V :=
  if state.depth ≠ 0 || state.pending.isSome then ⟨.refused, state, none, none⟩ else
    let released := state.backing.releaseOne
    ⟨released.status, { state with backing := released.next, retiring := true }, none, none⟩

theorem no_early_backing_release (state : Stack V) (unfinished : state.depth ≠ 0 ∨ state.pending.isSome = true) :
    (state.releaseBacking).status = .refused ∧ (state.releaseBacking).next = state := by
  simp [Stack.releaseBacking, unfinished]

theorem empty_has_no_live_record (state : Stack V) (entries : List (Ptr × V))
    (valid : Represents state entries) (zero : state.depth = 0) :
    state.pending = none ∧ entries = [] ∧
      ∀ identity block, state.records.lookup identity = some block → block.live = false := by
  have depth := valid.depth
  have empty : entries = [] := List.length_eq_zero_iff.mp (by omega)
  have pending : state.pending = none := by
    cases observed : state.pending with
    | none => rfl
    | some value => simp [observed, zero] at depth
  refine ⟨pending, empty, ?_⟩
  intro identity block found
  have noLive : block.live ≠ true := by
    intro live
    have member := valid.covered identity block found live
    simp [empty] at member
  exact Bool.eq_false_iff.mpr noLive

def Stack.PopAdmission (clear : V → Bool) (state : Stack V) : Prop :=
  state.retiring = false ∧ (∀ value, state.top = some value → clear value = true) ∧
    (state.pending = none → state.WriteAdmission)

/-- The typed client gate is separate from raw record pop. Only already
retired record contents pass this gate; backing retirement never visits them. -/
def Stack.cleanupStep (clear : V → Bool) (state : Stack V) : Reply V :=
  if state.depth = 0 then state.releaseBacking else
  match state.top with
  | none => ⟨.refused, state, none, none⟩
  | some value =>
      if clear value then
        match state.pop with
        | none => ⟨.refused, state, none, none⟩
        | some next => ⟨.pending, next, none, none⟩
      else ⟨.refused, state, none, none⟩

theorem uncleared_refuses_pop (clear : V → Bool) (state : Stack V) (positive : 0 < state.depth)
    (value : V) (top : state.top = some value) (notClear : clear value = false) :
    (state.cleanupStep clear).status = .refused ∧ (state.cleanupStep clear).next = state := by
  simp [Stack.cleanupStep, Nat.ne_of_gt positive, top, notClear]

theorem cleanup_pop (clear : V → Bool) (state : Stack V) (entries : List (Ptr × V))
    (valid : Represents state entries) (positive : 0 < state.depth) (admitted : state.PopAdmission clear) :
    ∃ next nextEntries, state.cleanupStep clear = ⟨.pending, next, none, none⟩ ∧
      Represents next nextEntries ∧ next.depth = state.depth - 1 ∧ next.retiring = false ∧
      next.recordSize = state.recordSize ∧ next.backing.chain = state.backing.chain ∧
      next.disposed + next.committed = state.disposed + state.committed := by
  cases pending : state.pending with
  | some value =>
      have top : state.top = some value := by
        simp [Stack.top, Stack.read, Nat.ne_of_gt positive, admitted.1, pending, positive]
      have clearTop := admitted.2.1 value top
      have popped := pending_pop state entries valid admitted.1 value pending
      let next := { state with depth := state.depth - 1, pending := none }
      refine ⟨next, entries, ?_, popped.2, rfl, admitted.1, rfl, rfl, ?_⟩
      · simp [Stack.cleanupStep, Nat.ne_of_gt positive, top, clearTop, popped.1, next]
      · simp [next, Stack.committed, pending]
  | none =>
      induction entries using List.reverseRecOn with
      | nil =>
          have depth := valid.depth
          simp [pending] at depth
          omega
      | append_singleton entries entry _ =>
          rcases entry with ⟨pointer, value⟩
          have depth : state.depth = entries.length + 1 := by simpa [pending] using valid.depth
          have top : state.top = some value := by
            simp only [Stack.top, if_neg (Nat.ne_of_gt positive)]
            exact committed_read state (entries ++ [(pointer, value)]) valid admitted.1
              (state.depth - 1) pointer value (by simp [depth])
          have clearTop := admitted.2.1 value top
          obtain ⟨next, popped, represented, nextDepth, disposed, noPending, live, size, chain, _⟩ :=
            committed_pop state entries pointer value valid admitted.1 pending (admitted.2.2 pending)
          refine ⟨next, entries, ?_, represented, nextDepth, live, size, chain, ?_⟩
          · simp [Stack.cleanupStep, Nat.ne_of_gt positive, top, clearTop, popped]
          · simp only [Stack.committed, pending, noPending, Option.toList_none, List.length_nil, Nat.sub_zero]
            omega

def cleanupProvider (clear : V → Bool) : Provider protocol where
  State _ _ := Stack V
  step state _ := ⟨(state.cleanupStep clear).status, (state.cleanupStep clear).next⟩

def cleanupCharge (clear : V → Bool) : Charge (cleanupProvider clear) := fun _ _ => 1

def Stack.cleanupPacket (clear : V → Bool) (state : Stack V) : Packet (cleanupProvider clear) client () :=
  ⟨(), none, state⟩

def Stack.cleanupRun (clear : V → Bool) (fuel : Nat) (state : Stack V) :=
  Cursor.advance (cleanupProvider clear) client (cleanupCharge clear) fuel (state.cleanupPacket clear)

theorem cleanup_zero (clear : V → Bool) (state : Stack V) :
    state.cleanupRun clear 0 = (0, .paused (state.cleanupPacket clear)) := rfl

theorem cleanup_split (clear : V → Bool) (state : Stack V) (first later : Nat) :
    state.cleanupRun clear (first + later) =
      resume (cleanupProvider clear) client (cleanupCharge clear) later (state.cleanupRun clear first) :=
  advance_add _ _ _ first later (state.cleanupPacket clear)

private theorem cleanup_poll (clear : V → Bool) (state : Stack V) (fuel : Nat) :
    Cursor.advance (cleanupProvider clear) client (cleanupCharge clear) (fuel + 1)
      (base := ()) ⟨(), none, state⟩ =
      let response := state.cleanupStep clear
      let rest := Cursor.advance (cleanupProvider clear) client (cleanupCharge clear) fuel
        (base := ()) ⟨(), if response.status = .pending then none else some response.status, response.next⟩
      (1 + rest.1, rest.2) := by
  simp only [Cursor.advance, fs_client_poll]
  rfl

private theorem cleanup_done (clear : V → Bool) (state : Stack V) (fuel : Nat) (status : Status) :
    Cursor.advance (cleanupProvider clear) client (cleanupCharge clear) (fuel + 1)
      (base := ()) ⟨(), some status, state⟩ = (0, .done ⟨(), status, state⟩) := by
  simp only [Cursor.advance, fs_client_done]

/-- Reuse the actual backing release provider once all record ownership is
gone. The fixed context is retained; its external lifetime is still a premise. -/
def backingHom (clear : V → Bool) (base : Stack V) (zero : base.depth = 0)
    (pending : base.pending = none) (retiring : base.retiring = true) :
    Hom (Array.releaseProvider (V := Option Ptr)) (cleanupProvider clear) where
  map backing := { base with backing := backing }
  step backing _ := by
    simp [Array.releaseProvider, cleanupProvider, Stack.cleanupStep, zero, Stack.releaseBacking, pending, retiring]

theorem backing_finite (clear : V → Bool) (state : Stack V) (zero : state.depth = 0)
    (pending : state.pending = none) (valid : state.backing.Valid) :
    ∃ fuel paid final, state.cleanupRun clear fuel = (paid, .done ⟨(), .ready, final⟩) ∧
      final.depth = 0 ∧ final.pending = none ∧ final.records = state.records ∧
      final.disposed = state.disposed ∧ final.backing.Valid ∧ final.backing.chain = [] ∧
      final.backing.root = none ∧ final.backing.elementSize = 0 ∧
      final.backing.releasedRev.reverse = state.backing.retirementWord := by
  have first : state.cleanupStep clear =
      ⟨state.backing.releaseOne.status,
        { state with backing := state.backing.releaseOne.next, retiring := true }, none, none⟩ := by
    simp [Stack.cleanupStep, zero, Stack.releaseBacking, pending]
  have nextValid := state.backing.release_valid valid
  have notRefused := (state.backing.release_count valid).2
  have order := state.backing.release_order valid
  cases status : state.backing.releaseOne.status with
  | refused => exact (notRefused status).elim
  | ready =>
      obtain ⟨empty, root, size⟩ := state.backing.release_complete valid status
      refine ⟨2, 1, { state with backing := state.backing.releaseOne.next, retiring := true }, ?_,
        zero, pending, rfl, rfl, nextValid, empty, root, size, ?_⟩
      · change Cursor.advance (cleanupProvider clear) client (cleanupCharge clear) (1 + 1)
          (base := ()) ⟨(), none, state⟩ = _
        rw [cleanup_poll]
        simp only [first, status, reduceCtorEq, ↓reduceIte, cleanup_done, Nat.add_zero]
      · simpa [Array.retirementWord, empty] using order
  | pending =>
      let next := { state with backing := state.backing.releaseOne.next, retiring := true }
      let fuel := next.backing.chain.length + 2
      obtain ⟨array, finished, arrayValid, empty, root, size, readback⟩ :=
        next.backing.release_finite nextValid fuel (by rfl)
      let hom := backingHom clear next zero pending rfl
      have corresponding := hom.advance client Array.releaseCharge (cleanupCharge clear) fuel
        (base := ()) ⟨(), none, next.backing⟩
      change Cursor.advance Array.releaseProvider client Array.releaseCharge fuel
        (base := ()) ⟨(), none, next.backing⟩ = _ at finished
      rw [finished] at corresponding
      change .done ⟨(), .ready, { next with backing := array }⟩ = (next.cleanupRun clear fuel).2 at corresponding
      have targetRun : next.cleanupRun clear fuel =
          ((next.cleanupRun clear fuel).1, .done ⟨(), .ready, { next with backing := array }⟩) :=
        Prod.ext rfl corresponding.symm
      refine ⟨fuel + 1, 1 + (next.cleanupRun clear fuel).1, { next with backing := array }, ?_,
        zero, pending, rfl, rfl, arrayValid, empty, root, size, readback.trans order⟩
      change Cursor.advance (cleanupProvider clear) client (cleanupCharge clear) (fuel + 1)
        (base := ()) ⟨(), none, state⟩ = _
      rw [cleanup_poll]
      simp only [first, status, ↓reduceIte]
      change (1 + (next.cleanupRun clear fuel).1, (next.cleanupRun clear fuel).2) = _
      exact Prod.ext rfl corresponding.symm

/-- Local resource-clear and memory-cell grants for the actual successive
frame pops. No grant is requested once backing-only retirement begins. -/
def Stack.CleanupAdmission (clear : V → Bool) : Nat → Stack V → Prop
  | 0, _ => True
  | count + 1, state =>
      (0 < state.depth → state.PopAdmission clear) ∧
        Stack.CleanupAdmission clear count (state.cleanupStep clear).next

theorem cleanup_finite (clear : V → Bool) (state : Stack V) (entries : List (Ptr × V))
    (valid : Represents state entries) (admitted : Stack.CleanupAdmission clear state.depth state) :
    ∃ fuel paid final,
      state.cleanupRun clear fuel = (paid, .done ⟨(), .ready, final⟩) ∧
        final.depth = 0 ∧ final.pending = none ∧ final.backing.chain = [] ∧
        final.backing.root = none ∧ final.backing.elementSize = 0 ∧ final.backing.Valid ∧
        final.disposed = state.disposed + state.committed ∧
        ∀ identity block, final.records.lookup identity = some block → block.live = false := by
  have claim : ∀ depth (state : Stack V) (entries : List (Ptr × V)), state.depth = depth →
      Represents state entries → Stack.CleanupAdmission clear depth state →
      ∃ fuel paid final, state.cleanupRun clear fuel = (paid, .done ⟨(), .ready, final⟩) ∧
        final.depth = 0 ∧ final.pending = none ∧ final.backing.chain = [] ∧
        final.backing.root = none ∧ final.backing.elementSize = 0 ∧ final.backing.Valid ∧
        final.disposed = state.disposed + state.committed ∧
        ∀ identity block, final.records.lookup identity = some block → block.live = false := by
    intro depth
    induction depth with
    | zero =>
        intro state entries same valid _
        have closed := empty_has_no_live_record state entries valid same
        obtain ⟨fuel, paid, final, finished, depth, pending, records, disposed,
          backingValid, chain, root, size, _⟩ := backing_finite clear state same closed.1 valid.backing_valid
        refine ⟨fuel, paid, final, finished, depth, pending, chain, root, size, backingValid, ?_, ?_⟩
        · simpa [Stack.committed, same] using disposed
        · intro identity block found
          exact closed.2.2 identity block (records ▸ found)
    | succ depth ih =>
        intro state entries same valid admitted
        obtain ⟨next, nextEntries, first, represented, nextDepth, live, size, chain, balance⟩ :=
          cleanup_pop clear state entries valid (by omega) (admitted.1 (by omega))
        have support : Stack.CleanupAdmission clear depth next := by
          simpa only [Stack.CleanupAdmission, first] using admitted.2
        obtain ⟨fuel, paid, final, finished, zero, pending, empty, root, frameSize, backingValid, disposed, closed⟩ :=
          ih next nextEntries (by omega) represented support
        refine ⟨fuel + 1, 1 + paid, final, ?_, zero, pending, empty, root, frameSize, backingValid,
          by omega, closed⟩
        change Cursor.advance (cleanupProvider clear) client (cleanupCharge clear) (fuel + 1)
          (base := ()) ⟨(), none, state⟩ = _
        rw [cleanup_poll]
        simp only [first, ↓reduceIte]
        change (1 + (next.cleanupRun clear fuel).1, (next.cleanupRun clear fuel).2) = _
        rw [finished]
  exact claim state.depth state entries rfl valid admitted

/-- A fixed record update retains its address. Pending-top writes stay in
the single saved record; earlier installed records remain independently
addressable while that child is pending. -/
def Stack.write (state : Stack V) (index : Nat) (value : V) : Option (Stack V) :=
  if state.retiring || state.depth ≤ index then none else
  if state.pending.isSome && index = state.depth - 1 then
    some { state with pending := some value }
  else do
    let pointer ← (state.backing.read index).join
    let records ← store state.records pointer value
    some { state with records := records }

theorem write_pending (state : Stack V) (value old : V) (live : state.retiring = false)
    (positive : 0 < state.depth) (pending : state.pending = some old) :
    state.write (state.depth - 1) value = some { state with pending := some value } := by
  simp [Stack.write, live, pending, positive]

theorem write_committed (state : Stack V) (index : Nat) (pointer : Ptr) (value : V)
    (records : Storage V) (live : state.retiring = false) (bounded : index < state.depth)
    (notPending : state.pending = none ∨ index ≠ state.depth - 1)
    (location : state.backing.read index = some (some pointer))
    (stored : store state.records pointer value = some records) :
    state.write index value = some { state with records := records } ∧
      ({ state with records := records } : Stack V).read index = some value := by
  have skip : (state.pending.isSome && index = state.depth - 1) = false := by
    rcases notPending with absent | different <;> simp [*]
  constructor
  · simp [Stack.write, live, show ¬state.depth ≤ index by omega, skip, location, stored]
  · have read := load_store_same state.records records pointer value stored
    cases pending : state.pending with
    | none => simp [Stack.read, live, show ¬state.depth ≤ index by omega, location, read]
    | some saved =>
        have different : index ≠ state.depth - 1 := by simpa [pending] using notPending
        simp [Stack.read, live, show ¬state.depth ≤ index by omega, different, location, read]

theorem store_lookup_other (memory next : Storage V) (pointer : Ptr) (value : V)
    (stored : store memory pointer value = some next) (identity : BlockId) (different : identity ≠ pointer.block) :
    next.lookup identity = memory.lookup identity := by
  cases found : memory.lookup pointer.block with
  | none => simp [store, found] at stored
  | some block =>
      by_cases valid : block.live = true ∧ pointer.offset < block.cells.length
      · simp [store, found, valid] at stored
        subst next
        exact lookup_put_other _ _ _ _ different
      · simp [store, found, valid] at stored

theorem write_top_represents (state : Stack V) (entries : List (Ptr × V)) (pointer : Ptr) (old value : V)
    (valid : Represents state (entries ++ [(pointer, old)])) (live : state.retiring = false)
    (pending : state.pending = none) :
    ∃ records,
      state.write (state.depth - 1) value = some { state with records := records } ∧
      Represents { state with records := records } (entries ++ [(pointer, value)]) ∧
      load records pointer = some value := by
  have depth : state.depth = entries.length + 1 := by simpa [pending] using valid.depth
  have last := valid.records_live entries.length pointer old (by simp)
  obtain ⟨records, stored⟩ := store_available state.records pointer old value last.2.1
  have sameRead := load_store_same state.records records pointer value stored
  have update := write_committed state (state.depth - 1) pointer value records live (by omega)
    (Or.inl pending) (by simpa [depth] using last.1) stored
  have distinct : (entries.map (fun entry => entry.1.block) ++ [pointer.block]).Nodup := by
    simpa only [List.map_append, List.map_cons, List.map_nil] using valid.distinct
  refine ⟨records, update.1, ?_, sameRead⟩
  refine ⟨by simpa using valid.depth, valid.bounded, valid.backing_valid, ?_, ?_, ?_⟩
  · intro index previous content present
    by_cases prior : index < entries.length
    · have located : entries[index]? = some (previous, content) := by
        simpa only [List.getElem?_append, if_pos prior] using present
      have oldEntry := valid.records_live index previous content (by
        simpa only [List.getElem?_append, if_pos prior] using located)
      have different : previous.block ≠ pointer.block := by
        intro same
        have member : previous.block ∈ entries.map (fun entry => entry.1.block) :=
          List.mem_map.mpr ⟨(previous, content), List.mem_of_getElem? located, rfl⟩
        exact distinct.disjoint (same ▸ member) (by simp)
      exact ⟨oldEntry.1, (load_store_other state.records records pointer previous value stored
        (by intro equal; exact different (congrArg Ptr.block equal))).trans oldEntry.2.1, oldEntry.2.2⟩
    · have lastIndex : index = entries.length := by
        have bounded := (List.getElem?_eq_some_iff.mp present).1
        simp only [List.length_append, List.length_singleton] at bounded
        omega
      subst index
      have same : pointer = previous ∧ value = content := by simpa using present
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨last.1, sameRead, last.2.2⟩
  · simpa only [List.map_append, List.map_cons, List.map_nil] using distinct
  · intro identity block found blockLive
    by_cases same : identity = pointer.block
    · simp [same]
    · have previous : state.records.lookup identity = some block :=
        (store_lookup_other state.records records pointer value stored identity same) ▸ found
      have member := valid.covered identity block previous blockLive
      simpa only [List.map_append, List.map_cons, List.map_nil] using member

def Stack.initialize (size : Nat) : Option (Stack V) :=
  if 0 < size then some (Stack.empty size) else none

theorem initialized_config (size : Nat) (state : Stack V) (initialized : Stack.initialize size = some state) :
    0 < state.recordSize ∧ state.backing.elementSize = 8 ∧ Represents state [] := by
  by_cases positive : 0 < size
  · simp [Stack.initialize, positive] at initialized
    subst state
    exact ⟨positive, rfl, empty_represents size⟩
  · simp [Stack.initialize, positive] at initialized

theorem publication_occupied_refusal (state : Stack V) (value : V) (pending : state.pending = some value)
    (pointer : Ptr) (occupied : state.backing.read (state.depth - 1) = some (some pointer))
    (choice : AllocationChoice) :
    (state.publishPending choice).status = .refused ∧ (state.publishPending choice).next = state := by
  simp [Stack.publishPending, pending, Stack.slotVacant, occupied]

theorem advance_failure_keeps (state : Stack V) : (state.advance .failure .failure).next = state := by
  unfold Stack.advance
  split
  · rfl
  · cases pending : state.pending with
    | none => rfl
    | some value =>
        have kept := state.backing.failure_keeps_residual (state.depth - 1)
        have same : { state with pending := some value } = state := by rw [← pending]
        cases status : (state.backing.prepare (state.depth - 1) .failure).status with
        | pending => simpa only [status, kept] using same
        | refused => simpa only [status, kept] using same
        | ready =>
            simp only [status, kept]
            change (({ state with pending := some value } : Stack V).publishPending .failure).next = state
            rw [same]
            exact (publish_allocation_refusal state value pending).2

theorem published_request_record (state : Stack V) (choice : AllocationChoice) (request : Request)
    (requested : (state.publishPending choice).request = some request) : request = .record state.recordSize := by
  cases pending : state.pending with
  | none => simp [Stack.publishPending, pending] at requested
  | some value =>
      by_cases blocked : (!state.slotWritable || !state.slotVacant) = true
      · simp only [Stack.publishPending, pending, if_pos blocked, reduceCtorEq] at requested
      · cases allocated : newRecord state.records value choice with
        | none => simpa [Stack.publishPending, pending, blocked, allocated] using requested.symm
        | some result =>
            rcases result with ⟨pointer, records⟩
            cases pointer with
            | none => simpa [Stack.publishPending, pending, blocked, allocated] using requested.symm
            | some pointer =>
                cases written : state.backing.write (state.depth - 1) (some pointer) <;>
                  simpa [Stack.publishPending, pending, blocked, allocated, written] using requested.symm

theorem advance_request_shape (state : Stack V) (pageChoice recordChoice : AllocationChoice)
    (request : Request) (requested : (state.advance pageChoice recordChoice).request = some request) :
    (∃ kind, request = .backing kind) ∨ request = .record state.recordSize := by
  simp only [Stack.advance] at requested
  split at requested
  · cases requested
  · cases pending : state.pending with
    | none => simp [pending] at requested
    | some value =>
        simp only [pending] at requested
        cases status : (state.backing.prepare (state.depth - 1) pageChoice).status with
        | pending =>
            simp only [status] at requested
            cases requestedKind : (state.backing.prepare (state.depth - 1) pageChoice).request with
            | none => simp [requestedKind] at requested
            | some kind => exact Or.inl ⟨kind, (Option.some.inj (by simpa [requestedKind] using requested)).symm⟩
        | refused =>
            simp only [status] at requested
            cases requestedKind : (state.backing.prepare (state.depth - 1) pageChoice).request with
            | none => simp [requestedKind] at requested
            | some kind => exact Or.inl ⟨kind, (Option.some.inj (by simpa [requestedKind] using requested)).symm⟩
        | ready =>
            simp only [status] at requested
            exact Or.inr (published_request_record
              { state with backing := (state.backing.prepare (state.depth - 1) pageChoice).next, pending := some value }
              recordChoice request requested)

/-- Fixed pointer-directory/page requests and the static record-copy request
have no depth factor. ABI and allocator/zeroing latency are separate services. -/
theorem actual_request_bound (state : Stack V) (pageChoice recordChoice : AllocationChoice)
    (request : Request) (requested : (state.advance pageChoice recordChoice).request = some request)
    (header pointerBytes : Nat) : request.bytes header pointerBytes ≤
      max (header + max (128 * pointerBytes) (64 * 8)) state.recordSize := by
  rcases advance_request_shape state pageChoice recordChoice request requested with ⟨kind, rfl⟩ | rfl
  · cases kind <;> simp only [Request.bytes, Kind.requestBytes] <;> omega
  · exact Nat.le_max_right _ _

theorem ready_backing_no_install (backing : Array (Option Ptr)) (index : Nat) (choice : AllocationChoice)
    (ready : (backing.prepare index choice).status = .ready) : (backing.prepare index choice).installed = false := by
  have balance := backing.prepare_count index choice
  rw [backing.ready_keeps_residual index choice ready] at balance
  cases installed : (backing.prepare index choice).installed <;> simp_all

theorem read_load (backing : Array (Option Ptr)) (index : Nat) (value : Option Ptr)
    (read : backing.read index = some value) (address : Ptr) (location : backing.at index = some address) :
    load backing.memory address = some (.inr value) := by
  simp only [Array.read, location, Option.bind_eq_bind, Option.bind_some] at read
  cases loaded : load backing.memory address with
  | none => simp [loaded] at read
  | some entry =>
      cases entry with
      | inl child => simp [loaded] at read
      | inr content =>
          have same : content = value := by simpa [loaded] using read
          subst content
          rfl

theorem publish_metadata (state : Stack V) (choice : AllocationChoice) :
    (state.publishPending choice).next.depth = state.depth ∧
      (state.publishPending choice).next.recordSize = state.recordSize ∧
      (state.publishPending choice).next.retiring = state.retiring ∧
      (state.publishPending choice).next.disposed = state.disposed := by
  simp only [Stack.publishPending]
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · split
      · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl⟩

theorem advance_metadata (state : Stack V) (pageChoice recordChoice : AllocationChoice) :
    (state.advance pageChoice recordChoice).next.depth = state.depth ∧
      (state.advance pageChoice recordChoice).next.recordSize = state.recordSize ∧
      (state.advance pageChoice recordChoice).next.retiring = state.retiring ∧
      (state.advance pageChoice recordChoice).next.disposed = state.disposed := by
  simp only [Stack.advance]
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · exact publish_metadata _ recordChoice

private theorem push_disposed_aux (page record : Stack V → AllocationChoice) (fuel : Nat)
    (control : Option Status) (state : Stack V) :
    (pushOutcomeState page record (Cursor.advance (pushProvider page record) client (pushCharge page record) fuel
      (base := ()) ⟨(), control, state⟩).2).disposed = state.disposed := by
  induction fuel generalizing control state with
  | zero => rfl
  | succ fuel ih =>
      cases control with
      | some status => rw [push_done]; rfl
      | none =>
          rw [push_poll]
          exact (ih _ _).trans (advance_metadata state (page state) (record state)).2.2.2

theorem push_preserves_disposed (page record : Stack V → AllocationChoice) (state : Stack V) (fuel : Nat) :
    (pushOutcomeState page record (state.pushRun page record fuel).2).disposed = state.disposed :=
  push_disposed_aux page record fuel none state

/-- A logical fresh-provider witness for finite executable memories. This
finite scan is not proposed as a native bounded allocator implementation. -/
def freshIdentity : Storage V → BlockId
  | [] => 0
  | (identity, _) :: rest => max (identity + 1) (freshIdentity rest)

theorem freshIdentity_absent (memory : Storage V) (identity : BlockId) (bound : freshIdentity memory ≤ identity) :
    memory.lookup identity = none := by
  induction memory with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨head, value⟩
      have heads : head + 1 ≤ identity := (Nat.le_max_left _ _).trans bound
      have tail : freshIdentity rest ≤ identity := (Nat.le_max_right _ _).trans bound
      have different : identity ≠ head := Nat.ne_of_gt (Nat.lt_of_succ_le heads)
      simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte] using ih tail

namespace Controls

set_option maxRecDepth 16384

def pages (state : Stack Nat) : BlockId := freshIdentity state.backing.memory
def records (state : Stack Nat) : BlockId := freshIdentity state.records + 1000

theorem pages_fresh (state : Stack Nat) : state.backing.memory.lookup (pages state) = none :=
  freshIdentity_absent _ _ (Nat.le_refl _)

theorem records_fresh (state : Stack Nat) : state.records.lookup (records state) = none :=
  freshIdentity_absent _ _ (by simp [records])

def empty : Stack Nat := Stack.empty 352
def queued : Stack Nat := { empty with depth := 1, pending := some 17 }

def pageStep (state : Stack Nat) : Stack Nat :=
  (state.advance (.fresh (pages state)) (.fresh (records state))).next

def prepared : Stack Nat := pageStep (pageStep (pageStep (pageStep (pageStep queued))))
def installed : Stack Nat := pageStep prepared
def child : Stack Nat := { installed with depth := 2, pending := some 29 }

theorem actual_queue : empty.queue 352 17 = some queued := by rfl

theorem queued_represents : Represents queued [] :=
  queue_represents empty queued [] (empty_represents 352) 352 17 actual_queue

theorem queued_value_is_immediately_top : queued.top = some 17 ∧ queued.records = [] ∧ queued.backing.chain = [] := by
  exact ⟨rfl, rfl, rfl⟩

theorem record_size_does_not_widen_array_cap :
    queued.recordSize = 352 ∧ queued.backing.elementSize = 8 ∧ Array.initialize (V := Option Ptr) 352 = none := by decide

theorem pending_growth_failure_keeps_exact_record :
    (queued.advance .failure .failure).status = .refused ∧ (queued.advance .failure .failure).next = queued ∧
      (queued.advance .failure .failure).next.top = some 17 := by
  exact ⟨rfl, advance_failure_keeps queued, rfl⟩

theorem prepared_local_publication_admission : prepared.PublishAdmission := by
  refine ⟨?_, by decide⟩
  intro address location
  have expected : prepared.backing.at (prepared.depth - 1) = some ⟨4, 0⟩ := by decide
  have same : (⟨4, 0⟩ : Ptr) = address := Option.some.inj (expected.symm.trans location)
  subst address
  refine ⟨⟨Kind.elements.block, by decide, rfl, by decide⟩, DataCell.of_none _ _ (by decide), ?_⟩
  intro index before
  change index < 0 at before
  omega

theorem actual_path_support : Stack.PushAdmission (freshChoice pages) (freshChoice records) 5 queued := by
  change prepared.PublishAdmission
  exact prepared_local_publication_admission

theorem real_fresh_provider_completes :
    ∃ pointer final, queued.pushRun (freshChoice pages) (freshChoice records) 8 =
      (7, .done ⟨(), .ready, final⟩) ∧ Represents final [(pointer, 17)] ∧
      final.pending = none ∧ final.depth = 1 ∧ final.recordSize = 352 ∧ final.retiring = false ∧ final.backing.chain.length = 5 := by
  simpa only [List.nil_append, show queued.depth = 1 from rfl, show queued.recordSize = 352 from rfl,
    show queued.backing.chain.length = 0 from rfl, Nat.zero_add] using
    push_finite pages records pages_fresh records_fresh queued [] queued_represents rfl (by decide) rfl
      17 rfl 5 (by decide) actual_path_support

theorem every_pause_keeps_actual_values (fuel : Nat) :
    let final := pushOutcomeState (freshChoice pages) (freshChoice records)
      (queued.pushRun (freshChoice pages) (freshChoice records) fuel).2
    ∃ entries, Represents final entries ∧ logicalValues final entries = [17] := by
  obtain ⟨entries, represented, _, values⟩ := push_prefix pages records pages_fresh records_fresh queued []
    queued_represents rfl (by decide) rfl 17 rfl 5 (by decide) actual_path_support fuel
  exact ⟨entries, represented, values⟩

theorem prepared_represents : Represents prepared [] := by
  obtain ⟨entries, represented, _⟩ := every_pause_keeps_actual_values 5
  change Represents prepared entries at represented
  have length := represented.depth
  have depth : prepared.depth = 1 := by decide
  have pending : prepared.pending = some 17 := by decide
  simp only [depth, pending, Option.toList_some, List.length_singleton] at length
  have emptyEntries : entries = [] := List.length_eq_zero_iff.mp (by omega)
  simpa only [emptyEntries] using represented

theorem prepared_backing_valid : prepared.backing.Valid := prepared_represents.backing_valid

theorem no_uninitialized_record_is_published :
    prepared.pending = some 17 ∧ prepared.backing.read 0 = none ∧
      (prepared.advance .failure (.fresh 1000)).status = .pending ∧
      installed.pending = none ∧ installed.backing.read 0 = some (some ⟨1000, 0⟩) ∧
      load installed.records ⟨1000, 0⟩ = some 17 ∧ installed.top = some 17 := by decide

theorem publication_yields_before_ready :
    (prepared.advance .failure (.fresh 1000)).status = .pending ∧
      (installed.advance .failure .failure).status = .ready := by decide

theorem prior_record_survives_child_request_and_refusal :
    installed.queue 352 29 = some child ∧ child.read 0 = some 17 ∧ child.top = some 29 ∧
      child.backing.read 0 = some (some ⟨1000, 0⟩) ∧
      (child.advance .failure .failure).next = child := by
  refine ⟨?_, by decide, by decide, by decide, advance_failure_keeps child⟩
  rfl

def parentUpdated : Stack Nat := (child.write 0 23).getD child

theorem mutable_parent_progress_is_not_replayed : parentUpdated.read 0 = some 23 ∧ parentUpdated.top = some 29 ∧
    parentUpdated.backing.read 0 = child.backing.read 0 ∧ parentUpdated.pending = child.pending := by decide

theorem second_pending_and_wrong_record_type_refused :
    queued.queue 352 99 = none ∧ installed.queue 120 99 = none ∧ empty.queue 0 99 = none := by decide

def occupied : Stack Nat := { installed with pending := some 29 }

theorem occupied_target_is_not_silently_overwritten :
    (occupied.publishPending (.fresh 2000)).status = .refused ∧
      (occupied.publishPending (.fresh 2000)).next = occupied := by
  apply publication_occupied_refusal occupied 29 rfl ⟨1000, 0⟩ (by decide)

theorem backing_held_for_pending_or_live_frames :
    queued.releaseBacking.next = queued ∧ installed.releaseBacking.next = installed := by
  constructor <;> rfl

def clear (value : Nat) : Bool := decide (value = 0)

theorem live_contents_block_typed_retirement :
    (installed.cleanupStep clear).status = .refused ∧ (installed.cleanupStep clear).next = installed := by
  exact uncleared_refuses_pop clear installed (by decide) 17 (by decide) rfl

theorem pending_pop_has_no_record_free :
    (queued.pop.map Stack.disposed) = some 0 ∧ (queued.pop.map Stack.depth) = some 0 ∧
      (queued.pop.map Stack.records) = some [] := by decide

theorem fixed_record_requests :
    (Request.backing .directory).bytes 16 8 = 1040 ∧
      (Request.backing .elements).bytes 16 8 = 528 ∧
      (Request.record 352).bytes 16 8 = 352 := by decide

def failures (_state : Stack Nat) : AllocationChoice := .failure

theorem actual_refusal_receipt : queued.pushRun failures failures 2 = (1, .done ⟨(), .refused, queued⟩) := by rfl

theorem refused_client_does_not_implicitly_restart (later : Nat) :
    resume (pushProvider failures failures) client (pushCharge failures failures) later
      (queued.pushRun failures failures 2) = (1, .done ⟨(), .refused, queued⟩) := by
  rw [actual_refusal_receipt]
  rfl

theorem retry_uses_saved_value : (queued.advance .failure .failure).next.queue 352 99 = none ∧
    (queued.advance .failure .failure).next.top = some 17 := by
  rw [advance_failure_keeps]
  constructor <;> rfl

theorem initialized_positive_config :
    Stack.initialize (V := Nat) 0 = none ∧ (Stack.initialize (V := Nat) 352).isSome = true := by decide

theorem count_exhaustion_refuses_without_losing_pending :
    ({ empty with depth := 2 ^ 32 - 1 } : Stack Nat).queue 352 17 = none := by decide

theorem full_lifo_cleanup_has_a_real_nonempty_instance :
    ∃ (pointer : Ptr) (start updated final : Stack Nat) (fuel paid : Nat),
      queued.pushRun (freshChoice pages) (freshChoice records) 8 = (7, .done ⟨(), .ready, start⟩) ∧
      start.write 0 0 = some updated ∧ updated.cleanupRun clear fuel = (paid, .done ⟨(), .ready, final⟩) ∧
      final.depth = 0 ∧ final.pending = none ∧ final.backing.chain = [] ∧
      final.backing.root = none ∧ final.disposed = 1 ∧ load final.records pointer = none := by
  obtain ⟨pointer, start, ran, represented, pending, depth, size, live, _⟩ := real_fresh_provider_completes
  obtain ⟨recordMemory, written, updatedRepresents, value⟩ :=
    write_top_represents start [] pointer 17 0 represented live pending
  let updated := { start with records := recordMemory }
  have top : updated.top = some 0 := by
    simp only [Stack.top, show updated.depth = 1 from depth, Nat.one_ne_zero, ↓reduceIte, Nat.sub_self]
    exact committed_read updated [(pointer, 0)] updatedRepresents live 0 pointer 0 (by simp)
  have location := (updatedRepresents.records_live 0 pointer 0 (by simp)).1
  have admission : updated.WriteAdmission := by
    intro address located
    have located0 : updated.backing.at 0 = some address := by
      simpa only [show updated.depth = 1 from depth, Nat.sub_self] using located
    have stored := read_load updated.backing 0 (some pointer) location address located0
    obtain ⟨block, found, blockLive, inside⟩ := load_present _ _ _ stored
    refine ⟨⟨block, found, blockLive, inside⟩, DataCell.of_value _ _ _ stored, ?_⟩
    intro index bounded
    change index < start.depth - 1 at bounded
    omega
  have popAllowed : updated.PopAdmission clear := by
    refine ⟨live, ?_, fun _ => admission⟩
    intro content observed
    have same : content = 0 := Option.some.inj (observed.symm.trans top)
    simp [same, clear]
  have cleanupAllowed : Stack.CleanupAdmission clear updated.depth updated := by
    rw [show updated.depth = 1 from depth]
    change (0 < updated.depth → updated.PopAdmission clear) ∧ True
    exact ⟨fun _ => popAllowed, trivial⟩
  obtain ⟨fuel, paid, final, finished, zero, noPending, noBacking, root, _, _, disposed, closed⟩ :=
    cleanup_finite clear updated [(pointer, 0)] updatedRepresents cleanupAllowed
  have disposedInitial : start.disposed = 0 := by
    have preserved := push_preserves_disposed (freshChoice pages) (freshChoice records) queued 8
    rw [ran] at preserved
    exact preserved
  have dead : load final.records pointer = none := by
    cases found : final.records.lookup pointer.block with
    | none => simp [load, found]
    | some block => simp [load, found, closed pointer.block block found]
  refine ⟨pointer, start, updated, final, fuel, paid, ran, ?_, finished, zero, noPending, noBacking, root, ?_, dead⟩
  · have indexEq : start.depth - 1 = 0 := by omega
    rw [indexEq] at written
    exact written
  · simpa [updated, Stack.committed, pending, depth, disposedInitial] using disposed

end Controls

end Mettapedia.Machines.CMemory.ExecutableStorage.BoundedIndexed.FrameStack
