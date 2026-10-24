import Mathlib.Data.List.Lattice

/-!
# Ordered occurrence intersection

Scan the left sequence in order, consuming at most one equal right occurrence
per retained element. Equality is explicit in the model; applying these laws
to a runtime key relation requires a corresponding equality interpretation.
This does not replace matching with structural hashing or verify native code.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Collections.OrderedIntersection

variable {Row : Type*} [DecidableEq Row]

/-- Remove the first matching occurrence, distinguishing absence from an
empty remaining sequence. -/
def consume (row : Row) : List Row → Option (List Row)
  | [] => none
  | first :: rest => if row = first then some rest else (consume row rest).map (first :: ·)

theorem consume_eq_erase (row : Row) (rows : List Row) :
    consume row rows = if row ∈ rows then some (rows.erase row) else none := by
  induction rows with
  | nil => simp [consume]
  | cons first rest ih =>
      by_cases same : row = first
      · subst first
        simp [consume]
      · simp [consume, same, ih, Ne.symm same]

def intersect : List Row → List Row → List Row
  | [], _ => []
  | row :: rest, right =>
      match consume row right with
      | none => intersect rest right
      | some remaining => row :: intersect rest remaining

/-- The explicit consuming scan realizes Mathlib's bag intersection, with
its stronger left-sequence observation retained. -/
theorem intersect_eq_bagInter (left right : List Row) :
    intersect left right = left.bagInter right := by
  induction left generalizing right with
  | nil => simp [intersect]
  | cons row rest ih =>
      by_cases present : row ∈ right <;>
        simp [intersect, consume_eq_erase, present, ih]

theorem preserves_left_order (left right : List Row) :
    (intersect left right).Sublist left := by
  rw [intersect_eq_bagInter]
  exact List.bagInter_sublist_left

theorem multiplicity (left right : List Row) (row : Row) :
    (intersect left right).count row = min (left.count row) (right.count row) := by
  rw [intersect_eq_bagInter, List.count_bagInter]

/-- Membership uses a singleton, so repeated right occurrences cannot
amplify this Boolean observation. -/
theorem singleton_membership (right : List Row) (row : Row) :
    intersect [row] right = if row ∈ right then [row] else [] := by
  rw [intersect_eq_bagInter, List.singleton_bagInter]

example : intersect ([2, 2, 1, 3] : List Nat) [1, 2, 1] = [2, 1] := by decide

example : intersect ([1, 2] : List Nat) [2, 1] ≠ intersect [2, 1] [1, 2] := by decide

/-- Filtering by membership alone incorrectly duplicates a consumed RHS row. -/
example : intersect ([2, 2] : List Nat) [2] ≠ [2, 2] := by decide

#print axioms consume_eq_erase
#print axioms intersect_eq_bagInter
#print axioms preserves_left_order
#print axioms multiplicity
#print axioms singleton_membership

end Mettapedia.Algorithms.Collections.OrderedIntersection
