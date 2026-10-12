import Mettapedia.GSLT.Dynamics.RelationalCardinality
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Bag aggregation over one shared coordinate

The reference enumerates one physical row of the first factor and all
compatible row products of the remaining factors. The grouped algorithm
visits each supported key once and multiplies its occurrence multiplicities.
All other bindings must already be factor-private row constraints. A second
shared coordinate cannot be erased by this law.

This establishes the aggregation and finite key-domain laws. Native sorted
range navigation and its charged seeks are separate correspondence controls.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.SingleKeyAggregation

open scoped BigOperators
open RelationalCardinality

variable {Key Row : Type*} [DecidableEq Key]

def rowsAt (rows : List (Key × Row)) (key : Key) : List (Key × Row) :=
  rows.filter fun row => decide (row.1 = key)

theorem rowsAt_length (rows : List (Key × Row)) (key : Key) :
    (rowsAt rows key).length = (rows.map Prod.fst).count key := by
  induction rows with
  | nil => simp [rowsAt]
  | cons row rest ih =>
      by_cases same : row.1 = key
      · simpa [rowsAt, same] using congrArg Nat.succ ih
      · simpa [rowsAt, same, Ne.symm same] using ih

def witnesses (first : List (Key × Row))
    (rest : List (List (Key × Row))) : List (List (Key × Row)) :=
  first.flatMap fun row =>
    (occurrenceProduct (rest.map fun rows => rowsAt rows row.1)).map (row :: ·)

def groupedCount (first : List (Key × Row))
    (rest : List (List (Key × Row))) : Nat :=
  ∑ key ∈ (first.map Prod.fst).toFinset,
    (rowsAt first key).length * leafMultiplicity (rest.map fun rows => rowsAt rows key)

/-- Duplicate first-factor rows remain weights, including equal payloads. -/
theorem groupedCount_eq_witnesses_length
    (first : List (Key × Row)) (rest : List (List (Key × Row))) :
    groupedCount first rest = (witnesses first rest).length := by
  simp only [groupedCount, witnesses, List.length_flatMap, List.length_map,
    occurrenceProduct_length, rowsAt_length]
  simpa [List.map_map, Function.comp_def, nsmul_eq_mul] using
    (Finset.sum_list_map_count (first.map Prod.fst)
      (fun key => leafMultiplicity (rest.map fun rows => rowsAt rows key))).symm

def commonKeys (first : List (Key × Row))
    (rest : List (List (Key × Row))) : Finset Key :=
  (first.map Prod.fst).toFinset.filter fun key =>
    ∀ rows ∈ rest, (rowsAt rows key).length ≠ 0

/-- Intersections skip precisely zero-weight assignments. Their absence
cannot remove a proof occurrence with nonzero multiplicity. -/
theorem groupedCount_eq_commonKeys_sum
    (first : List (Key × Row)) (rest : List (List (Key × Row))) :
    groupedCount first rest =
      ∑ key ∈ commonKeys first rest,
        (rowsAt first key).length * leafMultiplicity (rest.map fun rows => rowsAt rows key) := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro key present absent
  have missing : ¬ ∀ rows ∈ rest, (rowsAt rows key).length ≠ 0 := by
    simpa [commonKeys, present] using absent
  push Not at missing
  obtain ⟨rows, member, empty⟩ := missing
  have zeroMember : (0 : Nat) ∈ rest.map (fun rows => (rowsAt rows key).length) :=
    List.mem_map.mpr ⟨rows, member, empty⟩
  have zero : leafMultiplicity (rest.map fun rows => rowsAt rows key) = 0 := by
    simpa [leafMultiplicity, List.map_map, Function.comp_def] using
      (List.prod_eq_zero zeroMember)
  simp [zero]

/-- The grouped observer visits at most one assignment per first-factor
support key, regardless of the private Cartesian-product cardinality. -/
theorem commonKeys_card_le_input (first : List (Key × Row))
    (rest : List (List (Key × Row))) :
    (commonKeys first rest).card ≤ first.length := by
  calc
    _ ≤ (first.map Prod.fst).toFinset.card := Finset.card_filter_le _ _
    _ ≤ (first.map Prod.fst).length := List.toFinset_card_le _
    _ = _ := List.length_map Prod.fst

namespace Controls

theorem repeated_private_products_keep_weights :
    groupedCount ([(0, 10), (0, 10), (1, 11)] : List (Nat × Nat))
      [[(0, 20), (0, 21), (1, 22)], [(0, 30), (1, 31), (1, 32)]] = 6 := by decide

theorem missing_keys_contribute_no_witnesses :
    commonKeys ([(0, 10), (1, 11)] : List (Nat × Nat)) [[(1, 20), (2, 21)]] = {1} := by decide

theorem a_second_shared_coordinate_cannot_be_private :
    groupedCount ([(0, 1), (0, 2)] : List (Nat × Nat)) [[(0, 1), (0, 2)]] = 4 ∧
    (([(0, 1), (0, 2)] : List (Nat × Nat)).flatMap fun left =>
      ([(0, 1), (0, 2)] : List (Nat × Nat)).filter (fun right => decide (left = right))).length = 2 := by
  decide

end Controls

end Mettapedia.GSLT.Dynamics.SingleKeyAggregation
