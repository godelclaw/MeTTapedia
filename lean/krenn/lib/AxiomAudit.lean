import MainTheorem
import MinimalSupport
import NoCancellation
import GraphMatchingBridge
import Mettapedia.Combinatorics.Matching

/-! # Axiom audit
Every top-level conditional theorem, with its dependency cone printed. -/

#print axioms MainTheorem.krenn_gu_of_three_regularity
#print axioms MainTheorem.no_ghz_above_four
#print axioms MainTheorem.krenn_gu_of_liveDegree
#print axioms MinimalSupport.krenn_gu_of_minimalLiveDegree
#print axioms NoCancellation.krenn_gu_of_mixedSurvives
#print axioms NoCancellation.krenn_gu_of_certifiedPartition
#print axioms NoCancellation.krenn_gu_of_colourDegreeOne
#print axioms CycleCoordinates.no_three_regular_uniform
#print axioms MatchingParity.Pairing.toSubgraph_isPerfectMatching
#print axioms MatchingParity.Pairing.toSubgraph_ofPerfectMatching_adj
#print axioms MatchingParity.Pairing.exchange_toSubgraph_isPerfectMatching

/-! Reusable theory promoted to MeTTapedia. -/
#print axioms MatchingSum.pmSum_expand
#print axioms MatchingCrossing.exists_crossing
#print axioms MatchingCrossing.pmSum_four_two_terms
#print axioms MatchingCrossing.pmSum_six_three_dead
#print axioms MatchingRestriction.matchable_split_of_invariant
#print axioms MatchingHall.pmSum_eq_zero_of_internal_dead
#print axioms MatchingNonvanishing.pmSum_ne_zero_of_unique_matching
#print axioms MatchingNonvanishing.pmSum_ne_zero_of_two_matchings
#print axioms MatchingNonvanishing.certified_forced_pair
#print axioms MatchingParity.Pairing.kempeExchange_isPerfectMatching
#print axioms MatchingLoopless.amplitude_ignore_loops
#print axioms MatchingSupport.liveNeighbours_deloop
#print axioms MatchingBlockRank.block_split
#print axioms MatchingFourVertices.pairing_four_cases
#print axioms MatchingFourVertices.zero_edge_of_pairing_four_ne
#print axioms MixedColouring.perm_of_mixColouring
#print axioms MixedColouring.mixColouring_of_disconnected
#print axioms MixedColouring.exists_mixed_model
#print axioms CycleCoordinates.exists_mixed
