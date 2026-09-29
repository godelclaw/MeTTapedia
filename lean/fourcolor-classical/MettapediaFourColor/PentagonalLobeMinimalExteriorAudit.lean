import MettapediaFourColor.PentagonalLobeMinimalExterior
import Lean.Util.CollectAxioms

/-! Dependency audit of exterior connectivity derived from minimality and exact local recognition. -/

open Lean Elab Command
open FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``SixPortBoundaryConnectivity.hasCycle_of_boundary_card_lt_card_add_two,
      [``GoertzelV24CubicSmallBoundaryCycle.card_sideDart_eq_three_mul,
        ``SimpleGraph.IsTree.card_edgeFinset]),
    (``SixPortBoundaryConnectivity.three_le_componentPorts,
      [``SixPortBoundaryConnectivity.component_not_cycle_of_card_le_three,
        ``GoertzelV24CubicSmallBoundaryCycle.hasCycleOnSide_of_cubic_of_connected_induce_of_crossing_le_two]),
    (``SixPortBoundaryConnectivity.four_le_componentPorts_of_adj,
      [``SixPortBoundaryConnectivity.component_not_cycle_of_card_le_three,
        ``GoertzelV24CubicSmallBoundaryCycle.hasCycleOnSide_or_card_eq_one_of_local_cubic_of_connected_induce_of_crossing_le_three]),
    (``SixPortBoundaryConnectivity.connected_of_internal_edge_of_boundary_card_le_six,
      [``SixPortBoundaryConnectivity.three_le_componentPorts,
        ``SixPortBoundaryConnectivity.four_le_componentPorts_of_adj,
        ``MatchingBoundaryConnectivity.components_disjoint]),
    (``SixPortBoundaryConnectivity.connected_of_two_lt_card_of_boundary_card_le_six,
      [``SixPortBoundaryConnectivity.connected_of_internal_edge_of_boundary_card_le_six,
        ``GoertzelV24CubicSmallBoundaryCycle.card_sideDart_eq_three_mul]),
    (``SphericalVertexLowerBound.twenty_le_card_vertices,
      [``GoertzelV24FaceOrbitIncidence.sum_card_orbitFaceDarts_eq_card_darts,
        ``RotationSystem.card_darts_eq_three_times_card_vertices]),
    (``PentagonalLobePatch.Tangle.Embedded.inside_hasCycle,
      [``SixPortBoundaryConnectivity.hasCycle_of_boundary_card_lt_card_add_two,
        ``PentagonalLobePatch.Tangle.Embedded.inside_connected]),
    (``PentagonalLobePatch.Tangle.Embedded.exterior_connected_of_minimum_face_size,
      [``SixPortBoundaryConnectivity.connected_of_two_lt_card_of_boundary_card_le_six,
        ``SphericalVertexLowerBound.twenty_le_card_vertices,
        ``PentagonalLobePatch.Tangle.Embedded.inside_hasCycle,
        ``PentagonalLobePatch.Tangle.Embedded.size_decrease]),
    (``PentagonalLobePatch.Tangle.Embedded.strict_reduction_of_minimum_face_size,
      [``PentagonalLobePatch.Tangle.Embedded.exterior_connected_of_minimum_face_size,
        ``PentagonalLobePatch.Tangle.Embedded.strict_reduction,
        ``PentagonalLobePatch.Tangle.open_reconstruct_from_tree]),
    (``PentagonalLobePatch.Tangle.Embedded.exterior_connected_of_minimality,
      [``PentagonalLobePatch.Tangle.Embedded.exterior_connected_of_minimum_face_size,
        ``GoertzelV24MinimalFaceSize.orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample,
        ``GoertzelV24ThreeEdgeCutMinimality.cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample]),
    (``PentagonalLobePatch.Tangle.Embedded.not_in_minimal_counterexample_of_recognition,
      [``PentagonalLobePatch.Tangle.Embedded.exterior_connected_of_minimality,
        ``PentagonalLobePatch.Tangle.Embedded.strict_reduction,
        ``PentagonalLobePatch.Tangle.open_reconstruct_from_tree])]
  let forbidden : List Name := [`FourColor.Bulk, `FourColor.Reduce,
    `FourColor.checkCert_sound, `FourColor.check_reducible_valid,
    `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all,
    `FourColor.DiamondConfigurations, `FourColor.DiamondFamilyReducibility,
    `FourColor.DiamondProfileReducibility]
  let mut inspected : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        inspected := inspected.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Required dependency {name} is absent from {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) then
        throwError m!"Configuration certificate or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Pentagonal lobe with minimal exterior: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
