import Mettapedia.GSLT.Dynamics.RelationalCardinality
import Mathlib.Tactic.Tauto

/-!
# Prefix bounds supplied by a covering relation

The candidate domain is the independent Cartesian product of coordinate
domains. A covering relation admits only prefixes realized by its rows.
Every depth has at most as many distinct admitted prefixes as physical guard
rows, including repeated rows. This does not charge native range seeks:
their comparison bounds and the iterator's prefix invariant are separate
implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RelationalGuardBounds

open scoped BigOperators
open RelationalCardinality

variable {Key : Type*} [DecidableEq Key]

def guardPrefixes (rows : List (List Key)) (depth : Nat) : Finset (List Key) :=
  (rows.map fun row => row.take depth).toFinset

def guardedPrefixes (domains rows : List (List Key)) (depth : Nat) : Finset (List Key) :=
  ((occurrenceProduct domains).map fun assignment => assignment.take depth).toFinset.filter
    fun keys => keys ∈ guardPrefixes rows depth

theorem guardPrefixes_card_le_rows (rows : List (List Key)) (depth : Nat) :
    (guardPrefixes rows depth).card ≤ rows.length := by
  simpa [guardPrefixes] using List.toFinset_card_le (rows.map fun row => row.take depth)

theorem guardedPrefixes_subset (domains rows : List (List Key)) (depth : Nat) :
    guardedPrefixes domains rows depth ⊆ guardPrefixes rows depth := by
  intro keys present
  exact (Finset.mem_filter.mp present).2

theorem guardedPrefixes_card_le_rows (domains rows : List (List Key)) (depth : Nat) :
    (guardedPrefixes domains rows depth).card ≤ rows.length :=
  (Finset.card_le_card (guardedPrefixes_subset domains rows depth)).trans
    (guardPrefixes_card_le_rows rows depth)

/-- The bound counts distinct binding prefixes, not expanded occurrence
products or primitive instructions. Query width remains explicit. -/
theorem guarded_prefix_work_le (domains rows : List (List Key)) (width : Nat) :
    (∑ depth ∈ Finset.range width, (guardedPrefixes domains rows (depth + 1)).card) ≤
      width * rows.length := by
  calc
    _ ≤ ∑ _depth ∈ Finset.range width, rows.length :=
      Finset.sum_le_sum fun depth _ => guardedPrefixes_card_le_rows domains rows (depth + 1)
    _ = _ := by simp

omit [DecidableEq Key] in
theorem occurrenceProduct_member_length (domains : List (List Key))
    {assignment : List Key} (present : assignment ∈ occurrenceProduct domains) :
    assignment.length = domains.length := by
  induction domains generalizing assignment with
  | nil => simp [occurrenceProduct] at present; subst assignment; rfl
  | cons domain rest ih =>
      obtain ⟨key, _, selected⟩ := List.mem_flatMap.mp present
      obtain ⟨tail, member, rfl⟩ := List.mem_map.mp selected
      simp [ih member]

theorem guardPrefixes_full_width (rows : List (List Key)) (width : Nat)
    (fullWidth : ∀ row ∈ rows, row.length = width) :
    guardPrefixes rows width = rows.toFinset := by
  apply congrArg List.toFinset
  calc
    _ = rows.map id := by
      apply List.map_congr_left
      intro row member
      exact List.take_of_length_le (Nat.le_of_eq (fullWidth row member))
    _ = _ := List.map_id _

/-- Full-width guarding is exactly intersection with the complete relation,
not intersection with a projection that has forgotten shared coordinates. -/
theorem guarded_complete_assignments (domains rows : List (List Key))
    (fullWidth : ∀ row ∈ rows, row.length = domains.length) :
    guardedPrefixes domains rows domains.length =
      (occurrenceProduct domains).toFinset ∩ rows.toFinset := by
  have fullCandidates :
      (occurrenceProduct domains).map (fun assignment => assignment.take domains.length) =
        occurrenceProduct domains := by
    calc
      _ = (occurrenceProduct domains).map id := by
        apply List.map_congr_left
        intro assignment present
        exact List.take_of_length_le (Nat.le_of_eq (occurrenceProduct_member_length domains present))
      _ = _ := List.map_id _
  simp only [guardedPrefixes, fullCandidates, guardPrefixes_full_width rows _ fullWidth]
  ext assignment
  simp

namespace Controls

theorem sparse_guard_keeps_two_of_four_assignments :
    guardedPrefixes ([[0, 1], [0, 1]] : List (List Nat)) [[0, 1], [1, 0]] 2 =
      {[0, 1], [1, 0]} := by
  ext assignment
  simp [guardedPrefixes, guardPrefixes, occurrenceProduct]; tauto

theorem repeated_guard_rows_share_support :
    (guardPrefixes ([[0, 1], [0, 1], [1, 0]] : List (List Nat)) 2).card = 2 := by decide

theorem a_partial_relation_is_not_a_full_guard :
    guardedPrefixes ([[0], [0, 1]] : List (List Nat)) [[0]] 2 = ∅ ∧
    (occurrenceProduct ([[0], [0, 1]] : List (List Nat))).length = 2 := by
  simp [guardedPrefixes, guardPrefixes, occurrenceProduct]

end Controls

end Mettapedia.GSLT.Dynamics.RelationalGuardBounds
