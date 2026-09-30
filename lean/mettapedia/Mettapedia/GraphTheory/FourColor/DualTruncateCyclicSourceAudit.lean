import Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSourceExample
import Lean.Util.CollectAxioms

/-! Audit the cut-to-connectivity bridge and its actual source, target and
construction consumers. Reused forest counting, the coupled source supplier
and the concrete cut checker are required dependencies. Complete classical
Four Colour endpoints and source colour-word certificates are excluded. -/

open Lean Elab Command
open Mettapedia.GraphTheory
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``CubicPairDeletionConnectivity.hasCycleOnSide_of_two_le_card_of_crossing_le_three,
      [``CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two]),
    (``CubicPairDeletionConnectivity.reverseCrossing_injective,
      [``CubicPairDeletionConnectivity.crossing_ends_deleted]),
    (``CubicPairDeletionConnectivity.two_component_crossing_card_le_six,
      [``CubicPairDeletionConnectivity.reverseCrossing_injective,
       ``CubicPairDeletionConnectivity.reverseCrossing_ne]),
    (``CubicPairDeletionConnectivity.componentSide_card_two_le, []),
    (``CubicPairDeletionConnectivity.pairDeletion_connected,
      [``CubicPairDeletionConnectivity.two_component_crossing_card_le_six,
       ``CubicPairDeletionConnectivity.componentSide_card_two_le,
       ``CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two]),
    (``CubicPairDeletionConnectivity.colourable_three_of_cyclic_connectivity,
      [``CubicPairDeletionConnectivity.pairDeletion_connected,
       ``CoupledThreeColouring.colourable_of_pairDeletionConnected]),
    (``DualTruncateCyclicSource.source_of_cyclic_pair,
      [``CubicPairDeletionConnectivity.pairDeletion_connected,
       ``CoupledThreeColouring.colouring_of_connected_pair]),
    (``DualTruncateCyclicSource.source,
      [``CubicPairDeletionConnectivity.colourable_three_of_cyclic_connectivity,
       ``DualTruncateStructuralColoring.ofPrimalColouring]),
    (``DualTruncateCyclicSource.tait,
      [``DualTruncateCyclicSource.source, ``DualTruncateConstructionGSLT.tait]),
    (``DualTruncateCyclicSource.every_complete_sweep,
      [``DualTruncateCyclicSource.source,
       ``DualTruncateConstructionGSLT.supported_encoded_route]),
    (``DualTruncateCyclicSourceExample.finite_boundary_bound, []),
    (``DualTruncateCyclicSourceExample.boundaryPairs_card, []),
    (``DualTruncateCyclicSourceExample.cyclic_four,
      [``DualTruncateCyclicSourceExample.finite_boundary_bound,
       ``DualTruncateCyclicSourceExample.boundaryPairs_card]),
    (``DualTruncateCyclicSourceExample.regular, []),
    (``DualTruncateCyclicSourceExample.every_pair_deletion_connected,
      [``DualTruncateCyclicSourceExample.cyclic_four,
       ``CubicPairDeletionConnectivity.pairDeletion_connected]),
    (``DualTruncateCyclicSourceExample.shared_source_colouring,
      [``DualTruncateCyclicSource.source_of_cyclic_pair,
       ``DualTruncateCyclicSourceExample.cyclic_four]),
    (``DualTruncateCyclicSourceExample.target_tait,
      [``DualTruncateCyclicSource.tait,
       ``DualTruncateCyclicSourceExample.cyclic_four]),
    (``DualTruncateCyclicSourceExample.every_complete_sweep,
      [``DualTruncateCyclicSource.every_complete_sweep,
       ``DualTruncateCyclicSourceExample.cyclic_four])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks,
    `Lean.ofReduceBool, `sorryAx,
    ``CubicRotationByteCertificate.ProperWord,
    ``CubicRotationByteCertificate.threeVertexColoring]
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
        throwError m!"Forbidden proof dependency in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Cyclic source connectivity and reconstruction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    source colour-word certificates and complete classical theorem absent."
