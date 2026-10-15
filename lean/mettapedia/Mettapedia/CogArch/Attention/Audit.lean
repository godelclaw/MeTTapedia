import Mettapedia.ProbabilityTheory.MarkovChain.Audit
import Mettapedia.Algorithms.Retrieval.Audit
import Mettapedia.CogArch.Attention
import Mettapedia.CogArch.Memory
import Mettapedia.Algorithms.Retrieval
import Mettapedia.ProbabilityTheory.MarkovChain
import Mettapedia.PLN.Bridges.CogArch

/-! Kernel dependencies of the attention, memory and evidence bridge. -/

#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.replace_total
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.replace_preserves_other
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.sweep_total
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.retention_disabled
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.retention_zero_time
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.retention_positive
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.retention_le_one
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.retention_compose
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.advance_total
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.advance_values_compose
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.advance_compose
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.consolidate_sti
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.consolidate_lti_uses_new_mti
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.consolidation_disabled
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.consolidate_total
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.smoothing_between
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.calibration_disabled
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.calibrated_half_life_positive
#print axioms Mettapedia.CogArch.Attention.ThreeTimescale.calibration_roundtrip
#print axioms Mettapedia.CogArch.Attention.Spreading.spreadBank_total
#print axioms Mettapedia.CogArch.Memory.HierarchicalSummary.revisionStamp_eq_iff
#print axioms Mettapedia.CogArch.Memory.HierarchicalSummary.changed_membership_changes_stamp
#print axioms Mettapedia.CogArch.Memory.HierarchicalSummary.changed_dependency_changes_stamp
#print axioms Mettapedia.CogArch.Memory.HierarchicalSummary.unrelated_revision_does_not_change_stamp
#print axioms Mettapedia.CogArch.Memory.HierarchicalSummary.added_member_changes_stamp
#print axioms Mettapedia.CogArch.Memory.HierarchicalSummary.removed_member_changes_stamp
#print axioms Mettapedia.CogArch.Memory.HierarchicalSummary.latest_time_misses_removed_membership
#print axioms Mettapedia.CogArch.Memory.MemoryRefinement.completion_after_forget
#print axioms Mettapedia.CogArch.Memory.MemoryRefinement.old_completion_cannot_replace_new_edit
#print axioms Mettapedia.CogArch.Memory.MemoryRefinement.complete_preserves_originals
#print axioms Mettapedia.CogArch.Memory.MemoryRefinement.capture_preserves_retirement
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.normalize_row_sum
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.transport_mass
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.step_nonneg
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.rounds_mass
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.rounds_zero_outside_reachable
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.transport_distance
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.restart_error_bound
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.restart_has_unique_fixed_point
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.setEdge_idempotent
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.duplicate_edge_bias
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.spreading_revision_commute
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.extract_after_revision
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.replay_does_not_add_evidence
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.deletion_removes_supported_edge
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.attenuation_confidence_le
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.attenuation_strength
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.attenuation_not_idempotent
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.confidence_weighted_share_changes
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.ranking_stable
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.direct_product_not_full_deduction

#print axioms Mettapedia.CogArch.Attention.PremiseActivation.pool_mono
#print axioms Mettapedia.CogArch.Attention.PremiseActivation.seeds_retained
#print axioms Mettapedia.CogArch.Attention.PremiseActivation.covers_reachable_dependencies
#print axioms Mettapedia.CogArch.Attention.PremiseActivation.rankedView_subset
#print axioms Mettapedia.CogArch.Attention.PremiseActivation.ranking_cannot_recover_missing
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.Kernel.nonneg
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.Kernel.row_sum
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.Kernel.power_stochastic
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.normalize_nonneg
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.transport_nonneg
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.transport_mono
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.step_disabled
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.step_mass
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.rounds_nonneg
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.reachable_mono
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.restart_distance
#print axioms Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport.restart_eq_walk_step
#print axioms Mettapedia.CogArch.Attention.PremiseActivation.mem_pool
#print axioms Mettapedia.CogArch.Attention.PremiseActivation.zero_rounds
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.spreading_preserves_evidence
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.link_learning_preserves_world
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.revision_preserves_attention
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.record_idempotent
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.records_commute
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.deletion_idempotent
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.deletion_preserves_outside
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.attenuation_total
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.attenuation_le
#print axioms Mettapedia.PLN.Bridges.CogArch.AttentionEvidence.attenuation_total_le

#print axioms Mettapedia.CogArch.Attention.Equilibrium.lazy_transport
#print axioms Mettapedia.CogArch.Attention.Equilibrium.continuation_nonneg
#print axioms Mettapedia.CogArch.Attention.Equilibrium.continuation_lt_one
#print axioms Mettapedia.CogArch.Attention.Equilibrium.lazy_ppr_eq_ppr
#print axioms Mettapedia.CogArch.Attention.Equilibrium.mean_hops
#print axioms Mettapedia.CogArch.Attention.Equilibrium.impulse_zero
#print axioms Mettapedia.CogArch.Attention.Equilibrium.impulse_add
#print axioms Mettapedia.CogArch.Attention.Equilibrium.impulse_succ
#print axioms Mettapedia.CogArch.Attention.Equilibrium.sti_cycle
#print axioms Mettapedia.CogArch.Attention.Equilibrium.stimulate_spread_decay
#print axioms Mettapedia.CogArch.Attention.Equilibrium.sti_unroll
#print axioms Mettapedia.CogArch.Attention.Equilibrium.sti_steady_state
#print axioms Mettapedia.CogArch.Attention.Equilibrium.lazy_ppr_tail
#print axioms Mettapedia.CogArch.Attention.Relevance.concept_shortcut
#print axioms Mettapedia.CogArch.Attention.Relevance.spreading_regret
#print axioms Mettapedia.CogArch.Attention.Relevance.walk_generated_needs_optimal
#print axioms Mettapedia.CogArch.Attention.SpreadingExamples.hub_first
#print axioms Mettapedia.CogArch.Attention.SpreadingExamples.hub_second
#print axioms Mettapedia.CogArch.Attention.SpreadingExamples.hub_fixed
#print axioms Mettapedia.CogArch.Attention.SpreadingExamples.extra_round_lowers_recall
#print axioms Mettapedia.CogArch.Attention.SpreadingExamples.usefulness_gain_not_concave
