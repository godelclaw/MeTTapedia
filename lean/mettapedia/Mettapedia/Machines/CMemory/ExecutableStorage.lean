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
