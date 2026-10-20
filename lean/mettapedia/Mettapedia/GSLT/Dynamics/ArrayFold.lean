import Mettapedia.GSLT.Dynamics.OrderedListFold
import Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting
import Mettapedia.GraphTheory.Representation.CostModel

/-!
# Direct indexed array execution of ordered folds

The target retains one bounded immutable array slice and advances its start
offset. It reads the backing array directly; neither `extract` nor list
conversion is executed by its step function. The existing slice model is
used to state the independent list observation and prove correspondence.

The resource account distinguishes entry reads, accumulator updates and
cursor advances. It counts these target operations, not CPU instructions,
pointer accesses or elapsed time. Allocation, ownership transfer and C memory
safety are not inferred from Lean's immutable-array semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ArrayFold

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting
open Mettapedia.GraphTheory.Representation

variable {Item Acc : Type}

theorem slice_toList (slice : StackSlice Item) :
    slice.toList = (slice.cells.toList.drop slice.start).take slice.count := by
  simp [StackSlice.toList, StackSlice.toArray, Array.toList_extract,
    List.extract_eq_take_drop]

theorem slice_toList_length (slice : StackSlice Item) : slice.toList.length = slice.count := by
  rw [slice_toList]
  simp only [List.length_take, List.length_drop, Array.length_toList]
  exact Nat.min_eq_left (by have bound := slice.inBounds; omega)

/-- The source observation exposes exactly the cell loaded by the target,
followed by the advanced slice. -/
theorem slice_cons (slice : StackSlice Item) (positive : 0 < slice.count) :
    slice.toList = slice.cells[slice.start]'(by have bound := slice.inBounds; omega) ::
      (slice.advance positive).toList := by
  rw [slice_toList, List.drop_eq_getElem_cons
    (by simpa only [Array.length_toList] using
      (show slice.start < slice.cells.size by have bound := slice.inBounds; omega))]
  rw [List.take_cons positive]
  simp only [Array.getElem_toList, slice_toList, StackSlice.advance]


inductive State (Item Acc : Type) where
  | active (slice : StackSlice Item) (accumulator : Acc)
  | done (result : Acc)

def step? (operation : Acc → Item → Acc) : State Item Acc → Option (State Item Acc)
  | .active slice accumulator =>
      if positive : 0 < slice.count then
        some (.active (slice.advance positive)
          (operation accumulator (slice.cells[slice.start]'(by have bound := slice.inBounds; omega))))
      else some (.done accumulator)
  | .done _ => none

def decode : State Item Acc → OrderedListFold.State Item Acc
  | .active slice accumulator => .active slice.toList accumulator
  | .done result => .done result

/-- Target success is precisely one source step on the decoded states. -/
theorem step_correspondence (operation : Acc → Item → Acc)
    (source : State Item Acc) (target : OrderedListFold.State Item Acc) :
    (step? operation source).map decode = some target ↔
      OrderedListFold.Step operation (decode source) target := by
  cases source with
  | done result => simp only [step?, Option.map_none, reduceCtorEq, decode]; constructor <;> intro h <;> cases h
  | active slice accumulator =>
      by_cases positive : 0 < slice.count
      · rw [step?, dif_pos positive, Option.map_some]
        simp only [decode]
        rw [slice_cons slice positive]
        constructor
        · intro h; cases h; exact .consume _ _ _
        · intro step; cases step; rfl
      · have empty : slice.toList = [] := by
          apply List.eq_nil_of_length_eq_zero
          rw [slice_toList_length]
          omega
        simp only [step?, dif_neg positive, Option.map_some, decode, empty]
        constructor
        · intro h; cases h; exact .finish _
        · intro step; cases step; rfl

/-- Direct indexed loop. The remaining count is its termination measure. -/
def run (operation : Acc → Item → Acc) (slice : StackSlice Item) (initial : Acc) : Acc :=
  if positive : 0 < slice.count then
    run operation (slice.advance positive)
      (operation initial (slice.cells[slice.start]'(by have bound := slice.inBounds; omega)))
  else initial
termination_by slice.count
decreasing_by simp [StackSlice.advance]; omega

/-- The direct array loop implements the independent list fold for every
valid slice, including nonzero starts and empty slices. -/
theorem run_eq_foldl (operation : Acc → Item → Acc) (slice : StackSlice Item) (initial : Acc) :
    run operation slice initial = slice.toList.foldl operation initial := by
  rw [run]
  split_ifs with positive
  · rw [slice_cons slice positive, List.foldl_cons, run_eq_foldl]
  · have empty : slice.toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [slice_toList_length]
      omega
    rw [empty, List.foldl_nil]
termination_by slice.count
decreasing_by simp [StackSlice.advance]; omega

/-- The transcript of actual per-entry target work. This evaluates the same
loop while accumulating one read, update and cursor advance per entry. -/
def runCounted (operation : Acc → Item → Acc) (slice : StackSlice Item) (initial : Acc) : Acc × Nat :=
  if positive : 0 < slice.count then
    let rest := runCounted operation (slice.advance positive)
      (operation initial (slice.cells[slice.start]'(by have bound := slice.inBounds; omega)))
    (rest.1, rest.2 + 1)
  else (initial, 0)
termination_by slice.count
decreasing_by simp [StackSlice.advance]; omega

theorem runCounted_exact (operation : Acc → Item → Acc) (slice : StackSlice Item) (initial : Acc) :
    runCounted operation slice initial = (run operation slice initial, slice.count) := by
  rw [runCounted, run]
  split_ifs with positive
  · rw [runCounted_exact]
    simp only [StackSlice.advance]
    congr 1
    omega
  · have zero : slice.count = 0 := by omega
    simp [zero]
termination_by slice.count
decreasing_by simp [StackSlice.advance]; omega

/-- Read/update/cursor work is parameterized independently of physical cost.
The existing multidimensional resource algebra retains separate coordinates. -/
def account (count : Nat) : Resources :=
  { reads := count, writes := count, time := 3 * count + 1 }

theorem counted_resource_account (operation : Acc → Item → Acc)
    (slice : StackSlice Item) (initial : Acc) :
    account (runCounted operation slice initial).2 = account slice.count := by
  rw [runCounted_exact]

namespace Controls

def middleSlice : StackSlice Nat := ⟨#[99, 2, 3, 88], 1, 2, by decide⟩

theorem nonzero_start_uses_only_slice :
    runCounted Nat.add middleSlice 10 = (15, 2) := by
  rw [runCounted_exact, run_eq_foldl]
  decide

theorem duplicate_cells_are_not_skipped :
    runCounted Nat.add (StackSlice.ofArray #[2, 2]) 0 = (4, 2) := by
  rw [runCounted_exact, run_eq_foldl]
  decide

theorem invalid_slice_refused :
    ¬ ∃ slice : StackSlice Nat, slice.cells = #[1] ∧ slice.start = 1 ∧ slice.count = 1 := by
  rintro ⟨slice, cells, start, count⟩
  have bound := slice.inBounds
  rw [cells, start, count] at bound
  norm_num at bound

end Controls

end Mettapedia.GSLT.Dynamics.ArrayFold
