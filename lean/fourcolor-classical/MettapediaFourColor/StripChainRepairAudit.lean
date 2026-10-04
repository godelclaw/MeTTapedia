import MettapediaFourColor.StripChainRepair
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``KempeBalancedBlock.ear_or_nested, [``StrictMono.eq_id,
      ``Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching.exists_adjacent_within]),
    (``KempeBalancedBlock.noncross_of_cyclic, [``KempeBalancedBlock.crossing_iff_cyclic]),
    (``KempeBalancedBlock.coclosure, [``KempeBalancedBlock.ear_or_nested,
      ``KempeChromogramMatching.recover_stable]),
    (``KempeShortBlock.delete_pair, [``KempeShortBlock.skip_covers,
      ``KempeBalancedBlock.noncross_of_cyclic]),
    (``KempeShortBlock.ear_or_punctured, [``KempeBalancedBlock.ear_or_nested,
      ``Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching.exists_adjacent_majority]),
    (``KempeShortBlock.coclosure, [``KempeShortBlock.ear_or_punctured,
      ``KempeChromogramMatching.recover_stable]),
    (``KempeAnchorSelection.coclosure, [``KempeChromogramMatching.recover_stable,
      ``KempeRetainedMatching.possible_of_mate, ``KempeAnchorSelection.feasible_mate]),
    (``StripChainRepair.checked, [``KempeIntervalMatching.possible]),
    (``StripChainRepair.select, [``KempeAnchorSelection.feasible_reindex,
      ``StripChainRepair.selected_sound]),
    (``StripChainRepair.one_ready, [``StripSymbolicRepair.Direct]),
    (``StripChainRepair.two_ready, [``StripSymbolicRepair.Direct]),
    (``StripChainRepair.coordinates, [``StripChainRepair.positions]),
    (``StripChainRepair.coordinate_order, [``KempeBalancedBlock.noncross_of_cyclic]),
    (``StripChainRepair.ear_contracts, [``StripChainRepair.single]),
    (``StripChainRepair.nested_ready, [``StripChainRepair.one_ready, ``StripChainRepair.two_ready]),
    (``StripChainRepair.short_coordinates, [``StripChainRepair.shortPositions]),
    (``StripChainRepair.short_ear_contracts, [``StripChainRepair.single]),
    (``StripChainRepair.punctured_ready, [``StripChainRepair.one_ready, ``StripChainRepair.two_ready]),
    (``StripChainRepair.stages, [``KempeBalancedBlock.coclosure, ``KempeAnchorSelection.coclosure,
      ``KempeShortBlock.coclosure, ``StripSymbolicRepair.direct_coclosure]),
    (``StripChainRepair.repair, [``StripChainRepair.stages, ``StripChainRepair.source_trace]),
    (``StripChainRepair.nonextension, [``StripCriticalChain.no_core,
      ``StripResponseSummary.no_trace]),
    (``StripChainRepair.compatible_changed, [``StripChainRepair.repair,
      ``StripChainRepair.nonextension, ``GraphTraceAlignment.align,
      ``StripSourceExtension.complete_valid])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.CompositionalComplete,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData,
    `FourColor.StripSpherePhase.whole_repair, `FourColor.StripPhaseObstruction.repairHistory]
  let mut all : NameSet := {}
  for (root, required) in contracts do
    let mut todo := [root]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if forbidden.any (·.isPrefixOf name) then
          throwError m!"Forbidden dependency in {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Missing semantic dependency in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Critical-chain repair: {contracts.length} roots; {all.toList.length} declarations."
