import Mettapedia.GSLT.Dynamics.ChainAggregation
import Mathlib.Algebra.DualNumber

/-!
# Counts and selected integer sums in path messages

The native path route carries `(count, sum)` in checked machine integers.
Its mathematical carrier is the existing dual-number semiring over integers.
A row contributes `(1, value)` at the selected premise and `(1, 0)` elsewhere.
This module connects the table algorithm to occurrence counts and sums of
row contributions. It does not assert that machine overflow cannot occur.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ChainMoments

open ChainAggregation

abbrev Moment := DualNumber Int

def rowWeight (value : Int) (selected : Bool) : Moment :=
  (1, if selected then value else 0)

def carry (previous : Moment) (value : Int) (selected : Bool) : Moment :=
  (previous.fst, previous.snd + if selected then previous.fst * value else 0)

theorem carry_is_weight_product (previous : Moment) (value : Int) (selected : Bool) :
    carry previous value selected = previous * rowWeight value selected := by
  apply TrivSqZeroExt.ext
  · change previous.fst = previous.fst * 1
    exact (mul_one _).symm
  · change previous.snd + (if selected then previous.fst * value else 0) =
      previous.fst * (if selected then value else 0) + previous.snd * 1
    cases selected <;> simp [add_comm]

theorem merging_adds_both_accounts (first second : Moment) :
    (first + second).fst = first.fst + second.fst ∧
    (first + second).snd = first.snd + second.snd := ⟨rfl, rfl⟩

variable {Key : Type*}

def valid (path : Path Key Moment) : Prop :=
  path.weight.fst = 1 ∧
  path.weight.snd = (path.rows.map fun row => row.weight.snd).sum

theorem seed_valid (relation : List (Edge Key Moment))
    (unit : ∀ row ∈ relation, row.weight.fst = 1) :
    ∀ path ∈ seed relation, valid path := by
  intro path member
  obtain ⟨row, row_member, rfl⟩ := List.mem_map.mp member
  exact ⟨unit row row_member, by simp⟩

theorem attach_valid (path : Path Key Moment) (row : Edge Key Moment)
    (before : valid path) (unit : row.weight.fst = 1) :
    valid (attach path row) := by
  obtain ⟨count, sum⟩ := before
  constructor
  · simp [attach, count, unit]
  · simp [attach, count, unit, sum, add_comm]

theorem extend_valid [DecidableEq Key] (paths : List (Path Key Moment))
    (relation : List (Edge Key Moment))
    (before : ∀ path ∈ paths, valid path)
    (unit : ∀ row ∈ relation, row.weight.fst = 1) :
    ∀ path ∈ extend paths relation, valid path := by
  intro path member
  obtain ⟨previous, previous_member, emitted⟩ := List.mem_flatMap.mp member
  obtain ⟨row, row_member, joined⟩ := List.mem_flatMap.mp emitted
  split_ifs at joined with matched
  · have same := List.mem_singleton.mp joined
    subst path
    exact attach_valid previous row (before previous previous_member) (unit row row_member)
  · simp at joined

theorem enumerateFrom_valid [DecidableEq Key] (paths : List (Path Key Moment))
    (relations : List (List (Edge Key Moment)))
    (before : ∀ path ∈ paths, valid path)
    (unit : ∀ relation ∈ relations, ∀ row ∈ relation, row.weight.fst = 1) :
    ∀ path ∈ enumerateFrom paths relations, valid path := by
  induction relations generalizing paths with
  | nil => exact before
  | cons relation rest ih =>
      exact ih (extend paths relation)
        (extend_valid paths relation before (unit relation (by simp)))
        (fun rows member => unit rows (by simp [member]))

theorem enumerate_valid [DecidableEq Key] (relations : List (List (Edge Key Moment)))
    (unit : ∀ relation ∈ relations, ∀ row ∈ relation, row.weight.fst = 1) :
    ∀ path ∈ enumerate relations, valid path := by
  cases relations with
  | nil => simp [enumerate]
  | cons relation rest =>
      exact enumerateFrom_valid (seed relation) rest
        (seed_valid relation (unit relation (by simp)))
        (fun rows member => unit rows (by simp [member]))

theorem total_accounts (paths : List (Path Key Moment))
    (correct : ∀ path ∈ paths, valid path) :
    (total paths).fst = (paths.length : Int) ∧
    (total paths).snd =
      (paths.map fun path => (path.rows.map fun row => row.weight.snd).sum).sum := by
  induction paths with
  | nil => simp [total]
  | cons path rest ih =>
      obtain ⟨count, sum⟩ := correct path (by simp)
      obtain ⟨rest_count, rest_sum⟩ := ih (fun p member => correct p (by simp [member]))
      constructor
      · simp only [total, List.map_cons, List.sum_cons, TrivSqZeroExt.fst_add]
        change path.weight.fst + (total rest).fst = _
        rw [count, rest_count, List.length_cons, Nat.cast_add, Nat.cast_one]
        exact add_comm _ _
      · simp only [total, List.map_cons, List.sum_cons, TrivSqZeroExt.snd_add]
        change path.weight.snd + (total rest).snd = _
        rw [sum, rest_sum]

/-- The keyed execution algorithm returns the exact number of path
occurrences and the sum of their row contributions, for arbitrary length. -/
theorem aggregate_accounts [DecidableEq Key]
    (relations : List (List (Edge Key Moment)))
    (unit : ∀ relation ∈ relations, ∀ row ∈ relation, row.weight.fst = 1) :
    (aggregate relations).fst = ((enumerate relations).length : Int) ∧
    (aggregate relations).snd =
      ((enumerate relations).map fun path =>
        (path.rows.map fun row => row.weight.snd).sum).sum := by
  rw [← arbitrary_chain_total]
  exact total_accounts _ (enumerate_valid relations unit)

namespace Controls

def first : List (Edge Nat Moment) :=
  [⟨0, 1, rowWeight 0 false⟩, ⟨0, 1, rowWeight 0 false⟩]

def selected : List (Edge Nat Moment) :=
  [⟨1, 2, rowWeight (-3) true⟩, ⟨1, 2, rowWeight 5 true⟩]

def last : List (Edge Nat Moment) := [⟨2, 3, rowWeight 0 false⟩]

theorem selected_column_occurrences :
    (aggregate [first, selected, last, last.map fun row =>
      { row with source := 3, target := 4 }]).fst = 4 ∧
    (aggregate [first, selected, last, last.map fun row =>
      { row with source := 3, target := 4 }]).snd = 4 := by
  decide

theorem weight_is_not_a_proof_count :
    (rowWeight 5 true).fst = 1 ∧ (rowWeight 5 true).snd ≠ 1 := by
  decide

end Controls

end Mettapedia.GSLT.Dynamics.ChainMoments
