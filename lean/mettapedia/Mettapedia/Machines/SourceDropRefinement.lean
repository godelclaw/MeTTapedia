import Mathlib.Data.List.DropRight
import Mathlib.Data.Int.Basic

/-!
# Borrowing the suffix of a source-defined drop recurrence

The source tests an integer counter, destructures one constructor, subtracts
one and recurs. For nonnegative counters its result is exactly the persistent
list suffix. Suffix selection commutes with any later reading of the elements,
so selecting the carrier does not require materializing its contents first.

The counted cost is tail-link reads, not CPU instructions. Native source
recognition, constructor policy, shape validation, interrupts and ownership
remain C implementation obligations. Optimality below is restricted to an
explicit sequential tail-access model; no global optimality theorem is claimed.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.SourceDropRefinement

variable {Element Value : Type}

def source (count : Int) : List Element → List Element
  | [] => []
  | head :: tail => if count = 0 then head :: tail else source (count - 1) tail

def tailReads : Nat → List Element → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | count + 1, _ :: tail => 1 + tailReads count tail

theorem source_nonnegative (count : Nat) (values : List Element) :
    source (count : Int) values = values.drop count := by
  induction count generalizing values with
  | zero => cases values <;> simp [source]
  | succ count ih =>
      cases values with
      | nil => simp [source]
      | cons head tail =>
          simp only [source, Int.natCast_add, Int.natCast_one]
          have nonzero : (count : Int) + 1 ≠ 0 := by omega
          rw [if_neg nonzero]
          simpa only [Int.add_sub_cancel, List.drop_succ_cons] using ih tail

theorem exact_tail_reads (count : Nat) (values : List Element) :
    tailReads count values = min count values.length := by
  induction count generalizing values with
  | zero => simp [tailReads]
  | succ count ih =>
      cases values with
      | nil => simp [tailReads]
      | cons head tail => simp [tailReads, ih, Nat.add_comm]

/-- A sequential tail-access machine starts with only the input carrier.
It may spend a step without advancing, or read one tail link. There is no
cached suffix pointer, index, random access, or externally known length.
This is an explicit access model, not a model of every list representation. -/
inductive TailAccess : List Element → List Element → Nat → Prop where
  | here (values : List Element) : TailAccess values values 0
  | wait {values result : List Element} {cost : Nat} :
      TailAccess values result cost → TailAccess values result (cost + 1)
  | advance {head : Element} {tail result : List Element} {cost : Nat} :
      TailAccess tail result cost → TailAccess (head :: tail) result (cost + 1)

theorem access_length_bound {values result : List Element} {cost : Nat}
    (execution : TailAccess values result cost) :
    values.length ≤ result.length + cost := by
  induction execution with
  | here => simp
  | wait _ ih => omega
  | advance _ ih => simp only [List.length_cons]; omega

/-- The admitted traversal realizes its exact counted cost in the access model. -/
theorem traversal_realized (count : Nat) (values : List Element) :
    TailAccess values (values.drop count) (tailReads count values) := by
  induction count generalizing values with
  | zero => simpa only [List.drop_zero, tailReads] using TailAccess.here values
  | succ count ih =>
      cases values with
      | nil => simpa only [List.drop_nil, tailReads] using TailAccess.here ([] : List Element)
      | cons head tail =>
          simpa only [List.drop_succ_cons, tailReads, Nat.add_comm] using
            (TailAccess.advance (head := head) (ih tail))

/-- No sequential tail-access execution reaches this suffix with fewer
link steps. Additional indexes, cached pointers, known lengths, or a
representation permitting jumps are deliberately outside this theorem. -/
theorem traversal_optimal {count cost : Nat} {values : List Element}
    (execution : TailAccess values (source (count : Int) values) cost) :
    tailReads count values ≤ cost := by
  have bound := access_length_bound execution
  rw [source_nonnegative, List.length_drop] at bound
  rw [exact_tail_reads]
  omega

/-- Values may be read in a later binding environment; suffix selection
preserves their positions and sharing rather than reading them early. -/
theorem read_after_select (read : Element → Value)
    (count : Nat) (values : List Element) :
    (values.drop count).map read = (values.map read).drop count := by
  induction count generalizing values with
  | zero => rfl
  | succ count ih => cases values <;> simp [ih]

theorem source_read_transport (read : Element → Value)
    (count : Nat) (values : List Element) :
    (source (count : Int) values).map read =
      source (count : Int) (values.map read) := by
  rw [source_nonnegative, source_nonnegative, read_after_select]

/-- Splitting the traversal preserves the same suffix. -/
theorem split_selection (first second : Nat) (values : List Element) :
    (source (first : Int) values |> source (second : Int)) =
      source ((first + second : Nat) : Int) values := by
  simp only [source_nonnegative, List.drop_drop]

theorem ignored_heads (read : Element → Value)
    (count : Nat) (values : List Element) :
    (source (count : Int) values).length =
      (source (count : Int) (values.map read)).length := by
  rw [← source_read_transport]
  exact (List.length_map _).symm

/-- Positive counter steps remain representable; subtraction never crosses
below zero on this admitted branch. -/
theorem decrement_bounds (maximum remaining : Nat)
    (positive : 0 < remaining) (bounded : remaining ≤ maximum) :
    0 ≤ (remaining : Int) - 1 ∧ (remaining : Int) - 1 ≤ (maximum : Int) := by
  omega

namespace Controls

theorem zero_keeps_carrier : source (0 : Int) [1, 2, 3] = [1, 2, 3] := by decide

theorem suffix_selected : source (2 : Int) [1, 2, 3] = [3] := by decide

theorem past_end : source (7 : Int) [1, 2, 3] = [] := by decide

/-- Negative counts are outside the native admission, even though this
finite source program has a result. -/
theorem negative_source : source (-1 : Int) [1, 2, 3] = [] := by decide

theorem decrement_by_two_differs : source (2 : Int) [1, 2, 3] ≠ [2, 3] := by decide

theorem exact_access : TailAccess [1, 2, 3] [3] 2 := by
  exact traversal_realized 2 [1, 2, 3]

theorem extra_step_is_legal : TailAccess [1, 2, 3] [3] 3 := by
  exact TailAccess.wait exact_access

theorem one_step_is_insufficient : ¬ TailAccess [1, 2, 3] [3] 1 := by
  intro execution
  have bound := access_length_bound execution
  simp at bound

theorem later_binding_observed :
    (source (1 : Int) [0, 1, 1]).map (fun key => if key = 1 then 7 else 4) = [7, 7] := by
  decide

end Controls
end Mettapedia.Machines.SourceDropRefinement
