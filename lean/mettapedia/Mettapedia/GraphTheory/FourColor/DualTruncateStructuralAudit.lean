import Mettapedia.GraphTheory.FourColor.DualTruncateCoupledExample
import Lean.Util.CollectAxioms

/-! Audit the structural source supplier and its literal colouring and GSLT
consumers. The source hypotheses concern graph structure, and do not include
a colour word, a complete Four Colour endpoint or an unfinished Brooks proof.
The concrete cube supplies the required paths through its actual rotation. -/

open Lean Elab Command
open Mettapedia.GraphTheory
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``CoupledThreeColouring.colouring_of_coupledOrder, []),
    (``CoupledThreeColouring.reverseDistanceRank_injective, []),
    (``CoupledThreeColouring.closer_neighbour, []),
    (``CoupledThreeColouring.coupledOrder_of_connected_pair,
      [``CoupledThreeColouring.closer_neighbour,
       ``CoupledThreeColouring.reverseDistanceRank_injective]),
    (``CoupledThreeColouring.colouring_of_connected_pair,
      [``CoupledThreeColouring.coupledOrder_of_connected_pair,
       ``CoupledThreeColouring.colouring_of_coupledOrder]),
    (``CoupledThreeColouring.exists_nonadjacent_neighbours,
      [``SimpleGraph.Walk.exists_adj_adj_not_adj_ne]),
    (``CoupledThreeColouring.colourable_of_pairDeletionConnected,
      [``CoupledThreeColouring.exists_nonadjacent_neighbours,
       ``CoupledThreeColouring.colouring_of_connected_pair]),
    (``DualTruncateStructuralColoring.primal_degree_le_three,
      [``DualTruncateStructuralColoring.primal_neighbours]),
    (``DualTruncateStructuralColoring.ofPrimalColouring,
      [``DualTruncateStructuralColoring.palette_nonzero,
       ``DualTruncateStructuralColoring.palette_injective]),
    (``DualTruncateStructuralColoring.source_of_connected_pair,
      [``CoupledThreeColouring.colouring_of_connected_pair,
       ``DualTruncateStructuralColoring.ofPrimalColouring]),
    (``DualTruncateStructuralColoring.source_of_pairDeletionConnected,
      [``CoupledThreeColouring.colourable_of_pairDeletionConnected]),
    (``DualTruncateStructuralColoring.tait_of_connected_pair,
      [``DualTruncateStructuralColoring.source_of_connected_pair,
       ``DualTruncateConstructionGSLT.tait]),
    (``DualTruncateStructuralColoring.tait_of_pairDeletionConnected,
      [``DualTruncateStructuralColoring.source_of_pairDeletionConnected,
       ``DualTruncateConstructionGSLT.tait]),
    (``DualTruncateStructuralColoring.supported_route_of_connected_pair,
      [``DualTruncateStructuralColoring.source_of_connected_pair,
       ``DualTruncateConstructionGSLT.supported_encoded_route]),
    (``DualTruncateStructuralColoring.supported_route_of_pairDeletionConnected,
      [``DualTruncateStructuralColoring.source_of_pairDeletionConnected,
       ``DualTruncateConstructionGSLT.supported_encoded_route]),
    (``DualTruncateCoupledExample.source_shared_colouring,
      [``DualTruncateCoupledExample.retained_connected,
       ``DualTruncateStructuralColoring.source_of_connected_pair]),
    (``DualTruncateCoupledExample.target_tait,
      [``DualTruncateStructuralColoring.tait_of_connected_pair]),
    (``DualTruncateCoupledExample.every_complete_sweep,
      [``DualTruncateStructuralColoring.supported_route_of_connected_pair]),
    (``DualTruncateCoupledExample.complete_four_not_three_colourable, [])]
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
  logInfo m!"Structural dual-and-truncate source colouring: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    source colour certificates, unfinished Brooks endpoint and complete classical theorem absent."
