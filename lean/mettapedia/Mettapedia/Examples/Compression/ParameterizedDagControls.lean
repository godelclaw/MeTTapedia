import Mettapedia.Algorithms.Compression.ParameterizedDag

/-! Positive and negative controls for shared, finite DAG parameter slots. -/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.ParameterizedDagControls

open KolmogorovComplexity
open Algorithms.Compression
open ParameterizedDag

theorem duplicate_choices_remain_occurrences :
    (ParameterRegion.product (indexDomains [[false, false], [true, false]])).map
      (select [[false, false], [true, false]]) =
        [some [false, true], some [false, false], some [false, true], some [false, false]] := by
  rw [selected_product]
  rfl

theorem empty_region_is_not_one_assignment :
    (ParameterRegion.product (indexDomains [([] : List Bool)])).map
      (select [([] : List Bool)]) = [] := by
  rw [selected_product]
  rfl

theorem no_parameters_has_one_empty_assignment :
    (ParameterRegion.product (indexDomains ([] : List (List Bool)))).map
      (select ([] : List (List Bool))) = [some []] := rfl

theorem wrong_assignment_length_is_rejected :
    select [[false], [true]] [0] = none := rfl

theorem out_of_range_choice_is_rejected : select [[false]] [1] = none := rfl

private def sharedTemplate : List TemplateRecord :=
  [.parameter 0, .parameter 1, .parameter 0, .fixed (.node [] [0, 1, 2])]

theorem repeated_slot_preserves_one_assignment :
    instantiate [[true, false], [true]] sharedTemplate =
      some [.leaf [true, false], .leaf [true], .leaf [true, false], .node [] [0, 1, 2]] := rfl

theorem direct_shared_execution :
    foldTemplate List.length (fun _ values => values.sum)
      [[true, false], [true]] sharedTemplate [] = some [2, 1, 2, 5] := by decide

theorem missing_parameter_is_not_a_literal_zero :
    instantiate [[true]] sharedTemplate = none := rfl

theorem forward_reference_remains_invalid :
    foldTemplate List.length (fun _ values => values.sum) [[]]
      [.fixed (.node [] [0]), .parameter 0] [] = none := rfl

#print axioms select_length
#print axioms lookup_range
#print axioms selected_product
#print axioms complete_selected_product
#print axioms selected_product_coverage
#print axioms fit_complete_optimal
#print axioms instantiate_record_agrees
#print axioms instantiate_fold_agrees
#print axioms instantiate_length
#print axioms instantiate_preserves_references
#print axioms select_sorted
#print axioms parameter_lookup
#print axioms instantiate_record_infers
#print axioms instantiate_records_infer
#print axioms selected_roots_sound
#print axioms duplicate_choices_remain_occurrences
#print axioms empty_region_is_not_one_assignment
#print axioms no_parameters_has_one_empty_assignment
#print axioms wrong_assignment_length_is_rejected
#print axioms out_of_range_choice_is_rejected
#print axioms repeated_slot_preserves_one_assignment
#print axioms direct_shared_execution
#print axioms missing_parameter_is_not_a_literal_zero
#print axioms forward_reference_remains_invalid

end Mettapedia.Examples.Compression.ParameterizedDagControls
