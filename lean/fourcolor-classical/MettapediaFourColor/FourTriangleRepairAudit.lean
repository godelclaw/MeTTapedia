import MettapediaFourColor.FourTriangleRepairGeometry
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``FullRankRepair.repairs, [``Bulk.known_coclosure]),
    (``FourTriangleConstruction.numbered_eq, []),
    (``FourTriangleConstruction.faces, []),
    (``FourTriangleConstruction.core_degrees, []),
    (``FourTriangleConstruction.source_rotation, []),
    (``FourTriangleConstruction.boundary_alignment, []),
    (``FourTriangleConstruction.ringTrace_iff,
      [``FourTriangleConstruction.numbered_eq,
       ``ConfigurationFaceGraph.Presentation.ringTrace_iff]),
    (``FourTriangleRepair.fan_reference,
      [``FullRankRepair.repairs, ``FourTriangleRepair.fan_mask, ``Bulk.Cfg032.hpairs]),
    (``FourTriangleRepair.tripod_reference,
      [``FullRankRepair.repairs, ``FourTriangleRepair.tripod_mask, ``Bulk.Cfg036.hpairs]),
    (``FourTriangleRepair.reconstruct,
      [``FourTriangleRepair.reference_repair, ``FourTriangleConstruction.ringTrace_iff]),
    (``FourTriangleOccurrence.preembedding, [``LocalPreembedding.of_radius2]),
    (``FourTriangleOccurrence.disk_injective,
      [``FourTriangleOccurrence.faithful, ``FaithfulKernelEmbedding.disk_injective]),
    (``FourTriangleRepairGeometry.valid_contract, [``KempeRepairContract.valid_singleton]),
    (``FourTriangleRepairGeometry.singleton_reducible,
      [``FourTriangleRepair.reference_repair, ``FourTriangleRepairGeometry.valid_contract]),
    (``FourTriangleRepairGeometry.colorable,
      [``ActualDualContract.singleton_colorable, ``FourTriangleOccurrence.disk_injective,
       ``InjectiveEmbeddedRepair.colorable, ``FourTriangleRepairGeometry.singleton_reducible]),
    (``FourTriangleRepairGeometry.not_in_minimal,
      [``FourTriangleRepairGeometry.colorable])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate, `FourColor.WheelRepairData,
    `FourColor.WheelSeedRepairData, `FourColor.DiamondProfileData,
    ``Bulk.Cfg032.hctr, ``Bulk.Cfg036.hctr]
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
      let permitted := (`FourColor.Bulk.Cfg032).isPrefixOf name ||
        (`FourColor.Bulk.Cfg036).isPrefixOf name
      if forbidden.any (·.isPrefixOf name) ||
          (name.toString.startsWith "FourColor.Bulk.Cfg" && !permitted) ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or unrelated certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Four-triangle source repair: {roots.length} roots; \
    {all.toList.length} declarations. Complete source geometry, full proper-domain \
    repair and actual strict reconstruction share two retained rank certificates. \
    Neither original contract check is used. Complete occurrences remain explicit \
    hypotheses; core-to-boundary completion and geometric coverage are not claimed."
