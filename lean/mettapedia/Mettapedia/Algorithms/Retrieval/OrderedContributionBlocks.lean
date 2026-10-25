import Mettapedia.Algorithms.Retrieval.OrderedGroupedFold
import Mathlib.Tactic.Ring

/-!
An append accumulator repeatedly copies the prefix it has already collected.
Its replacement emits an ordered block per row and consumes those blocks.
The laws retain the entire occurrence stream and first-key order, without
reassociating the accumulator. The work model counts copied sequence slots;
it is not a claim about C allocation counts or machine instructions.
-/

namespace Mettapedia.Algorithms.Retrieval.OrderedContributionBlocks

variable {A B K R V : Type*}

def appendCollect (emit : A → List B) (seed : List B) (rows : List A) : List B :=
  rows.foldl (fun collected row => collected ++ emit row) seed

theorem appendCollect_eq_flatMap (emit : A → List B) (seed : List B)
    (rows : List A) :
    appendCollect emit seed rows = seed ++ rows.flatMap emit := by
  induction rows generalizing seed with
  | nil => simp [appendCollect]
  | cons row rest ih =>
      simpa [appendCollect, List.append_assoc] using
        ih (seed := seed ++ emit row)

theorem empty_appendCollect_eq_flatten (emit : A → List B) (rows : List A) :
    appendCollect emit [] rows = (rows.map emit).flatten := by
  simpa [List.flatMap] using appendCollect_eq_flatMap emit [] rows

theorem groupedBlocks_eq_appendCollect [DecidableEq K]
    (step : R → V → R) (initial : K → R) (state : List (K × R))
    (emit : A → List (K × V)) (rows : List A) :
    OrderedGroupedFold.groupedBlocks step initial state (rows.map emit) =
      OrderedGroupedFold.grouped step initial state (appendCollect emit [] rows) := by
  rw [OrderedGroupedFold.groupedBlocks_eq_flatten, empty_appendCollect_eq_flatten]

/-- Copy both sides of each append, including the accumulated prefix. -/
def appendSlots (copied : Nat) : List (List B) → Nat
  | [] => 0
  | block :: rest => copied + block.length + appendSlots (copied + block.length) rest

/-- One block visit and one element visit, with no repeated prefix copy. -/
def blockSlots (blocks : List (List B)) : Nat :=
  blocks.length + blocks.flatten.length

theorem singleton_appendSlots_twice (value : B) (count start : Nat) :
    2 * appendSlots start (List.replicate count [value]) =
      2 * count * start + count * (count + 1) := by
  induction count generalizing start with
  | zero => simp [appendSlots]
  | succ count ih =>
      simp only [List.replicate_succ, appendSlots, List.length_singleton]
      calc
        2 * (start + 1 + appendSlots (start + 1) (List.replicate count [value])) =
            2 * (start + 1) +
              2 * appendSlots (start + 1) (List.replicate count [value]) := by omega
        _ = 2 * (start + 1) + (2 * count * (start + 1) + count * (count + 1)) := by
              rw [ih]
        _ = 2 * (count + 1) * start + (count + 1) * (count + 1 + 1) := by ring

theorem singleton_blockSlots (value : B) (count : Nat) :
    blockSlots (List.replicate count [value]) = 2 * count := by
  induction count with
  | zero => simp [blockSlots]
  | succ count ih =>
      simp only [blockSlots, List.replicate_succ, List.length_cons,
        List.flatten_cons, List.length_append, List.length_nil,
        List.length_replicate] at *
      omega

/-- One fixed observation world; this does not cache reads across mutations. -/
def decorateOnce (read : A → B) (eligible : B → Bool) (decorate : B → A → V)
    (rows : List A) : List V :=
  (rows.map fun row =>
    let observed := read row
    if eligible observed then some (decorate observed row) else none).filterMap id

theorem decorateOnce_eq_filter_map (read : A → B) (eligible : B → Bool)
    (decorate : B → A → V) (rows : List A) :
    decorateOnce read eligible decorate rows =
      (rows.filter (fun row => eligible (read row))).map
        (fun row => decorate (read row) row) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      cases observed : eligible (read row) <;>
        simp_all [decorateOnce]

example : appendCollect (fun row : Nat => [row, row + 10]) [] [2, 1] =
    [2, 12, 1, 11] := by decide +kernel

example : appendCollect (fun row : Nat => if row = 0 then [] else [row, row]) []
    [0, 2, 0, 2] = [2, 2, 2, 2] := by decide +kernel

example : appendCollect (fun row : Nat => [row]) [] [2, 1] ≠ [1, 2] := by
  decide +kernel

example : OrderedGroupedFold.groupedBlocks (fun (total : Int) value => total * 10 + value)
    (fun (_ : Bool) => 0) [] [[(true, 2)], [], [(false, 8), (true, 5)]] =
    [(true, 25), (false, 8)] := by decide +kernel

example : appendSlots 0 (List.replicate 4 [true]) = 10 ∧
    blockSlots (List.replicate 4 [true]) = 8 := by decide +kernel

example : appendSlots 0 [[true]] = 1 ∧ blockSlots [[true]] = 2 := by
  decide +kernel

#print axioms groupedBlocks_eq_appendCollect
#print axioms singleton_appendSlots_twice
#print axioms singleton_blockSlots
#print axioms decorateOnce_eq_filter_map

end Mettapedia.Algorithms.Retrieval.OrderedContributionBlocks
