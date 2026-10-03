import MettapediaFourColor.WheelFamilyChecked
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let recordShards := (List.range 17).map fun i =>
    Name.str `FourColor.WheelRepairCertificate s!"recordShard{i}"
  let inputShards := (List.range 17).map fun i =>
    Name.str `FourColor.WheelRepairCertificate s!"inputShard{i}"
  let roots : List (Name × List Name) := [
    (``KempeSharedMaskCertificate.check_sound,
      [``KempeMaskCertificate.entries_complete, ``KempeChordMasks.recolor_matches]),
    (``WheelRepairCertificate.terminalCheck_sound, [``WheelSeedRepairCertificate.source_edges]),
    (``WheelRepairCertificate.checked, recordShards),
    (``WheelRepairCertificate.coverage, inputShards),
    (``WheelRepairCertificate.repair,
      [``WheelRepairCertificate.checked, ``WheelRepairCertificate.coverage,
       ``KempeIndexedCertificate.sound, ``KempeSharedMaskCertificate.check_sound]),
    (``WheelFamilyChecked.two_five_repair,
      [``WheelRepairCertificate.repair, ``BoundaryTriangleRepair.repair]),
    (``WheelFamilyChecked.reconstruct,
      [``WheelRepairCertificate.repair, ``TwoFiveWheelRepair.reconstruct]),
    (``WheelFamilyChecked.repaired_sectors,
      [``WheelRepairCertificate.repair, ``WheelColouringGSLT.split_iff]),
    (``WheelFamilyChecked.source_colorable,
      [``WheelRepairCertificate.repair, ``D3009Preembedding.disk_injective,
       ``ActualDualContract.singleton_colorable, ``InjectiveEmbeddedRepair.colorable]),
    (``WheelFamilyChecked.two_five_colorable,
      [``WheelRepairCertificate.repair, ``TwoFiveWheelPreembedding.disk_injective,
       ``ActualDualContract.singleton_colorable, ``InjectiveEmbeddedRepair.colorable]),
    (``WheelFamilyChecked.source_profile_excluded, [``ActualWheelOccurrence.occurrence]),
    (``WheelFamilyChecked.two_five_profile_excluded, [``TwoFiveWheelOccurrence.supplied]),
    (``WheelFamilyChecked.pair_exists,
      [``WheelRepairCertificate.repair, ``RuleFanSevenCluster.pair_exists, ``Bulk.Cfg006.hpairs])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate, `FourColor.ExceptionalRepairData,
    `FourColor.WheelSeedRepairData]
  let mut all : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Missing dependency {name} in {root}"
    for name in seen.toList do
      let permitted := root == ``WheelFamilyChecked.pair_exists &&
        (`FourColor.Bulk.Cfg006).isPrefixOf name
      if forbidden.any (·.isPrefixOf name) ||
          (name.toString.startsWith "FourColor.Bulk.Cfg" && !permitted) ||
          name.toString.startsWith "FourColor.Bulk.Hyb" ||
          ((`FourColor.DiamondProfileData).isPrefixOf name &&
            root != ``WheelFamilyChecked.pair_exists) then
        throwError m!"Forbidden endpoint or unrelated certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Complete wheel family: {roots.length} roots; \
    {all.toList.length} declarations. All 34 finite shards are retained. \
    One full source repair supplies all six target positions, actual strict \
    reconstruction and joint GSLT sectors. The pair-supply consumer additionally \
    retains configuration 7 and the shared diamond profile. \
    Joint closing laws and universal coverage are not claimed."
