import MainTheorem
import MinimalSupport
import NoCancellation
import GraphMatchingBridge

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
