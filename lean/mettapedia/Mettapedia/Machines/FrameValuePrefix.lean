import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Logical frame inventories with bounded backing prefixes

The authoritative schema supplies logical coordinates independently of their
physical backing. A missing backing cell denotes an unbound slot with version
zero. Reserving storage adds only such cells; storing a value changes exactly
one logical coordinate. A larger logical domain must clear any formerly
hidden backing cells before admitting them.

The capacity calculation doubles a positive allocation until sufficient,
using the requested size at the bounded-integer overflow entrance. Its bound
is on the greatest requested prefix, not on the number of currently bound
variables. Sparse writes to high coordinates are a separating example.
`initial` describes fresh backing; a recycled allocation can retain its old
capacity. The growth theorem explicitly permits that unchanged capacity.

These are representation and capacity laws. Native schema lookup, owners,
copy-on-write, allocation and the C loops retain separate conformance duties.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.FrameValuePrefix

abbrev Cell (Value : Type) := Option Value × Nat

def unbound {Value : Type} : Cell Value := (none, 0)

def cell {Value : Type} (cells : List (Cell Value)) (index : Nat) : Cell Value :=
  cells[index]?.getD unbound

def reserve {Value : Type} (cells : List (Cell Value)) (capacity : Nat) :
    List (Cell Value) :=
  cells ++ List.replicate (capacity - cells.length) unbound

theorem reserve_length {Value : Type} (cells : List (Cell Value)) (capacity : Nat) :
    (reserve cells capacity).length = max cells.length capacity := by
  simp only [reserve, List.length_append, List.length_replicate]
  omega

theorem reserve_cell {Value : Type} (cells : List (Cell Value))
    (capacity index : Nat) : cell (reserve cells capacity) index = cell cells index := by
  by_cases inside : index < cells.length
  · simp [cell, reserve, List.getElem?_append_left inside]
  · have absent : cells[index]? = none := List.getElem?_eq_none (by omega)
    simp only [cell, reserve, List.getElem?_append, inside, ↓reduceIte,
      List.getElem?_replicate, absent]
    split <;> rfl

/-- A prefix representation cannot store a nonempty value beyond its backing.
This is a lower bound for this representation, not for arbitrary sparse maps. -/
theorem bound_cell_needs_backing {Value : Type} (cells : List (Cell Value))
    (index : Nat) (bound : (cell cells index).1 ≠ none) : index < cells.length := by
  by_contra outside
  have absent : cells[index]? = none := List.getElem?_eq_none (by omega)
  exact bound (by simp [cell, absent, unbound])

structure Frame (Value : Type) where
  logical : Nat
  cells : List (Cell Value)
  deriving DecidableEq

def read {Value : Type} (frame : Frame Value) (index : Nat) : Option (Cell Value) :=
  if index < frame.logical then some (cell frame.cells index) else none

def initial {Value : Type} (logical : Nat) : Frame Value :=
  ⟨logical, List.replicate (min logical 64) unbound⟩

theorem initial_read {Value : Type} (logical index : Nat) :
    read (initial logical : Frame Value) index =
      if index < logical then some unbound else none := by
  by_cases present : index < logical
  · simp only [read, initial, present, ↓reduceIte, cell, List.getElem?_replicate]
    split <;> rfl
  · simp [read, initial, present]

theorem initial_backing_le {Value : Type} (logical : Nat) :
    (initial logical : Frame Value).cells.length ≤ 64 := by
  simp [initial]

def store {Value : Type} (capacity : Nat) (frame : Frame Value)
    (index : Nat) (value : Cell Value) : Option (Frame Value) :=
  if index < frame.logical then
    let cells := reserve frame.cells (max capacity (index + 1))
    some { frame with cells := cells.set index value }
  else none

theorem store_preserves_inventory {Value : Type} (capacity index : Nat)
    (frame after : Frame Value) (value : Cell Value)
    (stored : store capacity frame index value = some after) :
    after.logical = frame.logical := by
  unfold store at stored
  split at stored
  · cases Option.some.inj stored
    rfl
  · cases stored

theorem store_read {Value : Type} (capacity index query : Nat)
    (frame after : Frame Value) (value : Cell Value)
    (stored : store capacity frame index value = some after) :
    read after query =
      if query = index then some value else read frame query := by
  unfold store at stored
  split at stored
  · rename_i admitted
    cases Option.some.inj stored
    have backed : index < (reserve frame.cells (max capacity (index + 1))).length := by
      rw [reserve_length]
      omega
    by_cases same : query = index
    · subst query
      simp [read, cell, admitted, List.getElem?_set_self backed]
    · simp only [read]
      by_cases present : query < frame.logical
      · simp only [present, ↓reduceIte, cell, List.getElem?_set_ne (Ne.symm same)]
        simpa [same, read, present, cell] using congrArg some
          (reserve_cell frame.cells (max capacity (index + 1)) query)
      · simp [present, same]
  · cases stored

/-- Changing the logical domain does not admit stale hidden backing values. -/
def extendDomain {Value : Type} (frame : Frame Value) (logical : Nat) : Frame Value :=
  { logical := logical
    cells := frame.cells.take frame.logical ++
      List.replicate (frame.cells.length - frame.logical) unbound }

theorem extendDomain_read_old {Value : Type} (frame : Frame Value)
    (logical index : Nat) (grows : frame.logical ≤ logical) (old : index < frame.logical) :
    read (extendDomain frame logical) index = read frame index := by
  have present : index < logical := by omega
  simp only [read, extendDomain, present, old, ↓reduceIte, cell]
  by_cases backed : index < frame.cells.length
  · have taken : index < (frame.cells.take frame.logical).length := by simp; omega
    simp [List.getElem?_append_left taken, old]
  · have absent : frame.cells[index]? = none := List.getElem?_eq_none (by omega)
    have afterTake : (frame.cells.take frame.logical).length ≤ index := by simp; omega
    simp only [List.getElem?_append_right afterTake, List.getElem?_replicate, absent]
    split <;> rfl

theorem extendDomain_read_new {Value : Type} (frame : Frame Value)
    (logical index : Nat) (new : frame.logical ≤ index) (admitted : index < logical) :
    read (extendDomain frame logical) index = some unbound := by
  have afterTake : (frame.cells.take frame.logical).length ≤ index := by simp; omega
  simp only [read, extendDomain, admitted, ↓reduceIte, cell,
    List.getElem?_append_right afterTake, List.getElem?_replicate]
  split <;> rfl

/-- Native bounded doubling: an overflow entrance uses the exact request. -/
def growCapacity (limit current needed : Nat) (positive : 0 < current) : Nat :=
  if needed ≤ current then current
  else if limit / 2 < current then needed
  else growCapacity limit (2 * current) needed (by omega)
termination_by needed - current
decreasing_by omega

theorem capacity_bounds (limit current needed : Nat) (positive : 0 < current) :
    needed ≤ growCapacity limit current needed positive ∧
      (growCapacity limit current needed positive = current ∨
       growCapacity limit current needed positive < 2 * needed) := by
  fun_induction growCapacity limit current needed positive <;> omega

theorem capacity_within_limit (limit current needed : Nat) (positive : 0 < current)
    (oldBound : current ≤ limit) (requestBound : needed ≤ limit) :
    growCapacity limit current needed positive ≤ limit := by
  fun_induction growCapacity limit current needed positive <;> omega

-- A large inventory does not allocate a value for each unbound coordinate.
example : (initial 1024 : Frame Nat).cells.length = 64 ∧
    read (initial 1024 : Frame Nat) 1023 = some unbound := by decide

-- A late write remains visible, while an unrelated earlier slot stays empty.
example : let changed := store 128 (initial 128 : Frame Nat) 127 (some 7, 11)
    changed.map (fun frame => (read frame 127, read frame 0)) =
      some (some (some 7, 11), some unbound) := by decide

-- A physical spare cell is not authority to extend the logical inventory.
example : read (⟨1, [unbound, (some 99, 8)]⟩ : Frame Nat) 1 = none ∧
    read (extendDomain (⟨1, [unbound, (some 99, 8)]⟩ : Frame Nat) 2) 1 =
      some unbound := by decide

-- Merely changing the bound would expose stale backing storage.
example : read (⟨2, [unbound, (some 99, 8)]⟩ : Frame Nat) 1 ≠
    read (extendDomain (⟨1, [unbound, (some 99, 8)]⟩ : Frame Nat) 2) 1 := by decide

-- Prefix storage is not sparse storage: one very late write needs its prefix.
example : growCapacity 65535 16 1024 (by decide) = 1024 := by
  repeat' (rw [growCapacity]; norm_num)

end Mettapedia.Machines.FrameValuePrefix
