import Mettapedia.Algorithms.Compression.SharedObservation

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.SharedObservationControls

open Mettapedia.Algorithms.Compression.SharedObservation

private def read (value : Nat) : Option Nat := if value = 99 then none else some (value / 10)
private def exactPolicy (source candidate : Nat) : Bool := source == candidate
private def near (source candidate : Nat) : Bool :=
  decide (source ≤ candidate + 1 ∧ candidate ≤ source + 1)
private def cost (value : Nat) : Nat := 100 - value

theorem three_equal_artifacts_read_once : (shared read 10 10 10).reads = 1 := by decide

theorem two_equal_artifacts_read_twice : (shared read 10 10 11).reads = 2 := by decide

theorem equal_observations_are_not_equal_keys :
    (shared read 10 11 12).reads = 3 ∧
      (shared read 10 11 12).source = some 1 ∧
      (shared read 10 11 12).before = some 1 ∧
      (shared read 10 11 12).after = some 1 := by decide

theorem invalid_repeated_artifact_still_rejected :
    sharedCheck read exactPolicy cost 99 99 99 = .invalid := by decide

theorem real_complete_cost_improvement_accepted :
    sharedCheck read exactPolicy cost 10 10 11 = .accepted 11 90 89 := by decide

theorem unchanged_cost_rejected :
    sharedCheck read exactPolicy cost 10 10 10 = .notSmaller := by decide

theorem tolerance_does_not_accumulate :
    near 0 1 = true ∧ near 1 2 = true ∧
      sharedCheck read near cost 0 10 20 = .reconstruction := by decide

#print axioms Mettapedia.Algorithms.Compression.SharedObservation.shared_values
#print axioms Mettapedia.Algorithms.Compression.SharedObservation.shared_reads_le_three
#print axioms Mettapedia.Algorithms.Compression.SharedObservation.all_equal_reads_once
#print axioms Mettapedia.Algorithms.Compression.SharedObservation.original_current_equal_reads_twice
#print axioms Mettapedia.Algorithms.Compression.SharedObservation.all_distinct_reads_three
#print axioms Mettapedia.Algorithms.Compression.SharedObservation.sharedCheck_eq
#print axioms Mettapedia.Algorithms.Compression.SharedObservation.shared_accept_iff
#print axioms Mettapedia.Algorithms.Compression.SharedObservation.changed_original_policy_refused
#print axioms Mettapedia.Algorithms.Compression.SharedObservation.accepted_complete_cost_decreases
#print axioms three_equal_artifacts_read_once
#print axioms two_equal_artifacts_read_twice
#print axioms equal_observations_are_not_equal_keys
#print axioms invalid_repeated_artifact_still_rejected
#print axioms real_complete_cost_improvement_accepted
#print axioms unchanged_cost_rejected
#print axioms tolerance_does_not_accumulate

end Mettapedia.Examples.Compression.SharedObservationControls
