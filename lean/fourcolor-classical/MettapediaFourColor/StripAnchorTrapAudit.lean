import MettapediaFourColor.StripAnchorTrapHistory
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor
open SimpleGraph

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripAnchoredExtension.terminal_iff, [``StripPuncturedExtension.relaxed_iff]),
    (``StripAnchoredExtension.reconstruct, [``StripAnchoredExtension.terminal_iff,
      ``StripPartialColouring.partial_valid]),
    (``StripAnchoredExtension.possible_map, [``StripAnchoredExtension.partial_map]),
    (``StripAnchoredExtension.count_map, [``StripAnchoredExtension.possible_map]),
    (``StripAnchoredExtension.full_map, [``StripResponseSummary.terminal_iff]),
    (``StripAnchorTrap.planar, [``GraphDiskEuler.planar]),
    (``StripAnchorTrap.base_profile, []),
    (``StripAnchorTrap.answer_barrier, []),
    (``StripAnchorTrap.base_barrier, [``KempePhaseBoundary.endpoint,
      ``StripAnchorTrap.answer_barrier]),
    (``StripAnchorTrap.orbit_profile, [``StripAnchoredExtension.count_map,
      ``StripAnchoredExtension.full_map]),
    (``StripAnchorTrap.pointwise_stays, [``StripAnchorTrap.base_barrier,
      ``StripAnchoredExtension.count_map, ``StripAnchoredExtension.full_map]),
    (``StripAnchorTrap.step_stays, [``KempePairHistory.pointwise,
      ``StripAnchorTrap.pointwise_stays]),
    (``StripAnchorTrap.history_nonextension, [``StripAnchorTrap.history_stays,
      ``StripAnchorTrap.orbit_profile]),
    (``StripAnchorTrap.history_no_source, [``StripAnchorTrap.history_nonextension,
      ``StripResponseSummary.valid_of_colouring]),
    (``StripAnchorTrap.repairStep, [``StripAnchorTrap.repair_eq,
      ``KempeSeparatedChains.Certificate.step,
      ``SimpleGraph.Coloring.swap_apply_of_chain]),
    (``StripAnchorTrap.escape_profiles, [``StripAnchorTrap.base_profile,
      ``StripAnchorTrap.intermediate_profile, ``StripAnchorTrap.final_valid]),
    (``StripAnchorTrap.source_edges, []),
    (``StripAnchorTrap.core_stars, []),
    (``StripAnchorTrap.repair_length, []),
    (``StripAnchorTrap.reconstructed, [``StripAnchorTrap.repairStep,
      ``StripAnchorTrap.whole_valid])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate]
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
  logInfo m!"Physical joint-anchor trap: {contracts.length} roots; \
    {all.toList.length} declarations."
