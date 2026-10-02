import MettapediaFourColor.WheelSeedRepairChecked
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``KempeMaskCertificate.entries_eq, [``KempeMaskCertificate.enumeratedEntries]),
    (``WheelSeedRepairCertificate.source_edges, [``D3009Wheel.input]),
    (``WheelSeedRepairCertificate.terminalCheck_sound,
      [``WheelSeedRepairCertificate.source_edges]),
    (``WheelSeedRepairCertificate.check_sound, [``KempeMaskCertificate.check_sound]),
    (``WheelSeedRepairCertificate.checked, [``WheelSeedRepairData.records]),
    (``WheelSeedRepairCertificate.seed_repair,
      [``WheelSeedRepairCertificate.checked, ``KempeIndexedCertificate.sound]),
    (``WheelSeedRepairCertificate.repaired_sectors,
      [``WheelSeedRepairCertificate.seed_repair, ``WheelColouringGSLT.split_iff]),
    (``WheelSeedRepairCertificate.repaired_construction,
      [``WheelSeedRepairCertificate.seed_repair, ``D3009Construction.ringTrace_iff])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate, `FourColor.ExceptionalRepairData,
    `FourColor.DiamondProfileData, `FourColor.Bulk]
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
      if forbidden.any (·.isPrefixOf name) then
        throwError m!"Forbidden complete theorem or unrelated certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Wheel seed repair: {roots.length} roots; {all.toList.length} declarations. \
    Nine checked states answer all 132 exterior skeletons for the retained seed. \
    Exact source colourings and compatible closed GSLT sectors. \
    No complete Four Colour theorem or unrelated configuration certificate. \
    Complete thirteen-port repair and actual exterior closure remain separate."
