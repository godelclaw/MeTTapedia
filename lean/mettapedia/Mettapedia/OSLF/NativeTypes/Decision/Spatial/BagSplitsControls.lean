import Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagSplits
import Mathlib.Data.Finset.Card

/-! Positive and negative controls for complete bag decompositions. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagSplits.Controls

def oneB (input : Multiset String) : Bool := decide (input = {"b"})

theorem repeated_occurrences_can_separate :
    (["b"], ["b"]) ∈ enumerate ["b", "b"] := by decide

theorem one_occurrence_cannot_be_shared :
    (["b"], ["b"]) ∉ enumerate ["b"] := by decide

theorem empty_left_is_included :
    ([], ["b", "b"]) ∈ enumerate ["b", "b"] := by decide

theorem empty_right_is_included :
    (["b", "b"], []) ∈ enumerate ["b", "b"] := by decide

theorem empty_input_has_only_empty_split :
    enumerate ([] : List String) = [([], [])] := rfl

theorem exactly_two_copies_accept : check oneB oneB ["b", "b"] = true := by decide

theorem missing_copy_rejected : check oneB oneB ["b"] = false := by decide

theorem extra_copy_rejected : check oneB oneB ["b", "b", "b"] = false := by decide

theorem wrong_value_rejected : check oneB oneB ["b", "c"] = false := by decide

theorem occurrence_allocations_count_four : (enumerate ["b", "b"]).length = 4 := by decide

theorem value_pairs_count_three : (candidates ({"b", "b"} : Multiset String)).card = 3 := by
  decide

theorem candidate_retains_multiplicity :
    (({"b", "b"} : Multiset String), 0) ∈ candidates {"b", "b"} := by decide

theorem candidate_cannot_gain_an_occurrence :
    (({"b", "b"} : Multiset String), {"b"}) ∉ candidates {"b", "b"} := by decide

end Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagSplits.Controls
