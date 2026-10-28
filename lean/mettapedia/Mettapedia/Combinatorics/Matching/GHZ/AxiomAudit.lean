import Mettapedia.Combinatorics.Matching.GHZ
import Mettapedia.Algebra.Polynomial
import Mettapedia.Combinatorics.Matching.GraphFactorization
import Mettapedia.Combinatorics.Matching.GraphServability
import Mettapedia.Combinatorics.Matching.ServabilityCounterexamples
import Mettapedia.Combinatorics.Matching.SixCyclePotential
import Mettapedia.Combinatorics.Matching.SixVertexPotential
import Mettapedia.Combinatorics.Matching.SixVertexStars
import Mettapedia.Combinatorics.Matching.TripleOrbitClassification
import Mettapedia.Combinatorics.Matching.ThreePairColorProfiles
import Lean.Util.CollectAxioms
import Mettapedia.Combinatorics.Matching.GHZ.ConditionalThreeRegularity
import Mettapedia.Combinatorics.Matching.GHZ.MinimalSupport
import Mettapedia.Combinatorics.Matching.GHZ.NoCancellation
import Mettapedia.Combinatorics.Matching.GHZ.StarNormalForm
import Mettapedia.Combinatorics.Matching.GraphBridge
import Mettapedia.Combinatorics.Matching.GHZ.CharacteristicTwo.SixSite
import Mettapedia.Combinatorics.Matching.GHZ.UniformRigidity
import Mettapedia.Combinatorics.Matching.GHZ.TightCut
import Mettapedia.Combinatorics.Matching.GHZ.Fermionic.Obstruction
import Mettapedia.Combinatorics.Matching

/-! # Axiom audit
Every top-level conditional theorem, with its dependency cone printed. -/

#print axioms GHZ.ConditionalThreeRegularity.krenn_gu_of_three_regularity
#print axioms GHZ.ConditionalThreeRegularity.no_ghz_above_four
#print axioms GHZ.ConditionalThreeRegularity.krenn_gu_of_liveDegree
#print axioms GHZ.MinimalSupport.krenn_gu_of_minimalLiveDegree
#print axioms GHZ.NoCancellation.krenn_gu_of_mixedSurvives
#print axioms GHZ.NoCancellation.krenn_gu_of_certifiedPartition
#print axioms GHZ.NoCancellation.krenn_gu_of_colorDegreeOne
#print axioms GHZ.CycleCoordinates.no_three_regular_uniform
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

/-! Receiving-colour detour compatibility. -/
#print axioms GHZ.NoCancellation.certified_quad_cross_relation
#print axioms GHZ.StarNormalForm.certified_detour_cross_relation
#print axioms GHZ.StarNormalForm.detour_port_reuse_forces_size_one_circuits
#print axioms GHZ.StarNormalForm.thirdColor_thirdColor
#print axioms GHZ.StarNormalForm.exists_detourPorts
#print axioms GHZ.StarNormalForm.same_side_reuse_size_one_circuit
#print axioms GHZ.StarNormalForm.crossed_one_port_dichotomy
#print axioms GHZ.StarNormalForm.double_certified_detour_overlap_normal_form
#print axioms GHZ.StarNormalForm.receiving_pair_normal_form
#print axioms GHZ.StarNormalForm.excess_site_receiving_pair_normal_form
#print axioms MatchingCrossing.exists_dead_pair_detour_on
#print axioms MatchingCrossing.four_le_card_of_dead_pair_detour
#print axioms MatchingCrossing.dead_pair_detour_card_two
#print axioms MatchingCrossing.dead_pair_detour_card_four
#print axioms GHZ.StarNormalForm.disjoint_detours_force_outward_routes
#print axioms GHZ.StarNormalForm.eight_le_card_of_disjoint_detours
#print axioms GHZ.StarNormalForm.disjoint_detours_card_eight_exhaustion
#print axioms GHZ.StarNormalForm.receiving_pair_routed_normal_form
#print axioms GHZ.StarNormalForm.excess_site_receiving_pair_routed
#print axioms GHZ.StarNormalForm.CrossedOnePortCap.r_ne_q
#print axioms GHZ.StarNormalForm.exists_crossedCapTails
#print axioms GHZ.StarNormalForm.six_le_card_of_crossedCapTails
#print axioms GHZ.StarNormalForm.crossedCapTails_card_six
#print axioms GHZ.StarNormalForm.seven_le_card_of_distinct_tails
#print axioms GHZ.StarNormalForm.crossedCapTails_card_eight
#print axioms GHZ.StarNormalForm.disjoint_detours_octet_synchronized
#print axioms GHZ.StarNormalForm.exists_disjointDetourOctet
#print axioms GHZ.StarNormalForm.pair_overlap_trichotomy
#print axioms GHZ.StarNormalForm.outward_route_overlap
#print axioms GHZ.StarNormalForm.outward_route_overlap_sized
#print axioms GHZ.StarNormalForm.ten_le_card_of_two_beyond_octet
#print axioms GHZ.StarNormalForm.routed_pair_dead_with_live_arms
#print axioms GHZ.StarNormalForm.certificate_does_not_transfer_upward
#print axioms GHZ.StarNormalForm.routing_iteration_obstruction
#print axioms GHZ.StarNormalForm.excess_site_routing_network
#print axioms GHZ.StarNormalForm.live_pair_annihilates_complement
#print axioms GHZ.StarNormalForm.octet_ghz_relations

/-! Characteristic two: contraction, four-site rigidity, and the six-site base. -/
#print axioms MatchingCharTwo.capValue_mul_pmSum_contracted
#print axioms GHZ.CharacteristicTwo.isGHZOver_contract
#print axioms GHZ.CharacteristicTwo.no_isGHZOver_of_six
#print axioms GHZ.CharacteristicTwo.fourRigid
#print axioms GHZ.CharacteristicTwo.rigid_pair
#print axioms GHZ.CharacteristicTwo.SixCNF.sixFmla_unsat
#print axioms GHZ.CharacteristicTwo.no_isGHZOver_six

/-! Uniform rigidity: contraction against site vectors, and the cap lemma. -/
#print axioms MatchingSiteVectors.pmSum_formW
#print axioms GHZ.UniformRigidity.pmSum_formW_univ_of_isGHZ
#print axioms GHZ.UniformRigidity.cap_lemma
#print axioms MatchingSiteVectors.pmSum_two_over_odd_cut
#print axioms GHZ.UniformRigidity.split_lemma
#print axioms GHZ.UniformRigidity.three_monoAt
#print axioms MatchingTightCut.amplitude_shoreContract
#print axioms GHZ.TightCut.isGHZOver_shoreContract
#print axioms GHZ.TightCut.four_star
#print axioms GHZ.TightCut.false_of_shoreTight_six
#print axioms MatchingTightCut.amplitude_eq_crossOne_of_dead
#print axioms GHZ.TightCut.shoreTight_of_export_dead
#print axioms GHZ.TightCut.shoreTight_of_import_dead
#print axioms GHZ.TightCut.exists_common_export
#print axioms GHZ.TightCut.false_of_odd_sign_relation
#print axioms MatchingPfaffian.pfSum_expand
#print axioms MatchingPfaffian.a_mul_pfSum_update
#print axioms MatchingPfaffian.capVal_mul_pfSum_update_eq_cap
#print axioms GHZ.Fermionic.isFermiGHZ_contract
#print axioms GHZ.Fermionic.no_isFermiGHZ_six
#print axioms GHZ.Fermionic.krennGu_fermi
#print axioms GHZ.Fermionic.not_isGHZOver_of_pfaffian
#print axioms GHZ.Fermionic.not_isGHZOver_of_coherentSigns
#print axioms GHZ.TightCut.productState_of_port
#print axioms GHZ.TightCut.pair_elimination
#print axioms GHZ.TightCut.not_isGHZOver_of_pair
#print axioms GHZ.TightCut.paired_port_identity
#print axioms GHZ.TightCut.not_isGHZOver_of_paired_port

/-! The origin-based audit also covers private helpers and generated declarations;
its scope is the matching and polynomial modules loaded by the imports above. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let rejected ← liftCoreM <| collectAxioms ``sorryAx
  unless (rejected.filter fun axiomName => !allowed.contains axiomName).contains ``sorryAx do
    throwError "admission negative control failed"
  let mut declarations := 0
  let mut theorems := 0
  let mut modules := 0
  let mut executionOnly := 0
  for index in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[index]!
    let path := moduleName.toString
    if path.startsWith "Mettapedia.Combinatorics.Matching." ||
        path.startsWith "Mettapedia.Algebra.Polynomial." then
      let moduleData := env.header.moduleData[index]!
      let names := (moduleData.constNames ++ moduleData.extraConstNames).toList.eraseDups
      let mut checked := 0
      for name in names do
        let some info := env.checked.get.find? name | do
          unless moduleData.extraConstNames.contains name do
            throwError "unavailable kernel declaration {name}"
          executionOnly := executionOnly + 1
          continue
        if info matches .axiomInfo _ then throwError "owned axiom declaration {name}"
        -- Generated execution helpers (for example `_unsafe_rec`) are not
        -- trusted proof declarations. Every theorem is still audited below.
        if (info.isUnsafe || info.isPartial) && !(info matches .thmInfo _) then
          executionOnly := executionOnly + 1
          continue
        let axioms ← liftCoreM <| collectAxioms name
        let excess := axioms.filter fun axiomName => !allowed.contains axiomName
        unless excess.isEmpty do throwError "{name}: unexpected axioms {excess}"
        checked := checked + 1
        declarations := declarations + 1
        if info matches .thmInfo _ then theorems := theorems + 1
      if !names.isEmpty && checked == 0 then throwError "empty kernel audit in {moduleName}"
      modules := modules + 1
      logInfo m!"AUDIT {moduleName}: {checked} kernel declarations"
  unless theorems > 0 do throwError "empty theorem audit"
  logInfo m!"Matching and polynomial audit: {modules} modules; {theorems} theorems; {declarations} declarations; {executionOnly} execution-only entries; standard axioms only."
