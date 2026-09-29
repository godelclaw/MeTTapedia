import MettapediaFourColor.PentagonalLobeDistinctAttachments
import Lean.Util.CollectAxioms

/-! Dependency audit of the local attachment criterion and actual strict reduction. -/

open Lean Elab Command
open FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``MatchingBoundaryConnectivity.hasCycle_of_injective_boundary,
      [``GoertzelV24CubicSmallBoundaryCycle.card_sideDart_eq_three_mul,
        ``GoertzelV24CubicSmallBoundaryCycle.card_internalSideDart_eq_twice_card_edges,
        ``SimpleGraph.IsTree.card_edgeFinset]),
    (``MatchingBoundaryConnectivity.component_hasCycle,
      [``MatchingBoundaryConnectivity.hasCycle_of_injective_boundary,
        ``RootedCutSaturation.induce_inducedReachableSide_connected]),
    (``MatchingBoundaryConnectivity.mem_componentEdges, []),
    (``MatchingBoundaryConnectivity.four_le_componentPorts,
      [``MatchingBoundaryConnectivity.component_hasCycle,
        ``MatchingBoundaryConnectivity.mem_componentEdges]),
    (``MatchingBoundaryConnectivity.connected_of_boundary_card_lt_eight,
      [``MatchingBoundaryConnectivity.four_le_componentPorts,
        ``MatchingBoundaryConnectivity.components_disjoint]),
    (``MatchingBoundaryConnectivity.crossingBoundaryEquiv, []),
    (``PentagonalLobePatch.Tangle.Embedded.exterior_connected_of_distinct_attachments,
      [``MatchingBoundaryConnectivity.connected_of_boundary_card_lt_eight,
        ``MatchingBoundaryConnectivity.crossingBoundaryEquiv]),
    (``PentagonalLobePatch.Tangle.Embedded.strict_reduction_of_distinct_attachments,
      [``PentagonalLobePatch.Tangle.Embedded.exterior_connected_of_distinct_attachments,
        ``PentagonalLobePatch.Tangle.Embedded.strict_reduction,
        ``PentagonalLobePatch.Tangle.Embedded.size_decrease,
        ``PentagonalLobePatch.Tangle.open_reconstruct_from_tree]),
    (``PentagonalLobePatch.Tangle.Embedded.not_in_minimal_counterexample_of_distinct_attachments,
      [``PentagonalLobePatch.Tangle.Embedded.exterior_connected_of_distinct_attachments,
        ``GoertzelV24ThreeEdgeCutMinimality.cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample,
        ``PentagonalLobePatch.Tangle.Embedded.strict_reduction])]
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
  logInfo m!"Pentagonal lobe with distinct attachments: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
