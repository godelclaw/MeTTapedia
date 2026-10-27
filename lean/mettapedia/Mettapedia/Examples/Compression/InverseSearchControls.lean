import Mettapedia.Algorithms.Compression.MaskedScalarInverse
import Mettapedia.Algorithms.Compression.EvidenceSampling

/-! Exact field constraints and retained-sample fairness. These declarations
do not establish rounded scalar identities, a physical packed decoder, or a
complete inverse search over binary64 values. Native controls independently
check candidate programs against their original observations. -/

open Mettapedia.Algorithms.Compression

#print axioms MaskedScalarInverse.add_iff
#print axioms MaskedScalarInverse.subtractLeft_iff
#print axioms MaskedScalarInverse.subtractRight_iff
#print axioms MaskedScalarInverse.multiply_iff
#print axioms MaskedScalarInverse.proposal_is_relaxation
#print axioms MaskedScalarInverse.checked_proposal_iff
#print axioms MaskedScalarInverse.masked_product_fiber
#print axioms MaskedScalarInverse.Controls.zero_product_can_leave_a_parameter_free
#print axioms MaskedScalarInverse.Controls.inconsistent_zero_product_has_no_exact_preimage
#print axioms MaskedScalarInverse.Controls.relaxed_proposal_is_not_a_solution_certificate
#print axioms MaskedScalarInverse.Controls.unobserved_coordinate_imposes_no_equation

#print axioms EvidenceSampling.tick_pending_preserves
#print axioms EvidenceSampling.tick_answer_preserves
#print axioms EvidenceSampling.scan_accounts
#print axioms EvidenceSampling.remaining_reachable
#print axioms EvidenceSampling.eventually_services_sample
#print axioms EvidenceSampling.Controls.samples_after_masked_and_duplicate_positions_survive
#print axioms EvidenceSampling.Controls.budget_stop_keeps_later_answer
#print axioms EvidenceSampling.Controls.later_quantum_yields_retained_answer
