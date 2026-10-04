import MettapediaFourColor.StripStrongAnchorTrap
import MettapediaFourColor.StripAnchorTrapHistory
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor
open SimpleGraph

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripGuardedOrbit.pointwise_stays, [``StripAnchoredExtension.count_map,
      ``StripAnchoredExtension.full_map]),
    (``StripGuardedOrbit.history_nonextension, [``StripGuardedOrbit.history_stays,
      ``KempePairHistory.pointwise]),
    (``StripAnchorTrap.pointwise_stays, [``StripGuardedOrbit.pointwise_stays,
      ``StripAnchorTrap.base_barrier]),
    (``StripStrongAnchorTrap.planar, [``GraphTriangulationEuler.planar_iff_balance,
      ``StripStrongAnchorTrap.triangular, ``StripStrongAnchorTrap.connected]),
    (``StripStrongAnchorTrap.minimum_degree, [``GraphRotationRows.Rows.degree]),
    (``StripStrongAnchorTrap.maximum_degree, [``GraphRotationRows.Rows.degree]),
    (``StripStrongAnchorTrap.exterior_adj, []),
    (``StripStrongAnchorTrap.source_edges, []),
    (``StripStrongAnchorTrap.source_injective, []),
    (``StripStrongAnchorTrap.core_stars, []),
    (``StripStrongAnchorTrap.base_barrier, [``KempePhaseBoundary.endpoint,
      ``StripStrongAnchorTrap.answer_barrier]),
    (``StripStrongAnchorTrap.no_guarded_reconstruction,
      [``StripGuardedOrbit.history_nonextension, ``StripStrongAnchorTrap.base_barrier,
       ``StripStrongAnchorTrap.source_edges, ``StripResponseSummary.valid_of_colouring]),
    (``StripStrongAnchorTrap.repairStep, [``KempeSeparatedChains.Certificate.step,
      ``StripStrongAnchorTrap.repair_eq]),
    (``StripStrongAnchorTrap.repair_length, []),
    (``StripStrongAnchorTrap.escape_profiles, [``StripStrongAnchorTrap.base_profile,
      ``StripStrongAnchorTrap.intermediate_profile, ``StripStrongAnchorTrap.final_valid]),
    (``StripStrongAnchorTrap.reconstructed, [``StripStrongAnchorTrap.repairStep,
      ``StripStrongAnchorTrap.whole_valid])]
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
  logInfo m!"Shared guarded orbit and spherical anchor trap: {contracts.length} roots; \
    {all.toList.length} declarations."
