import MettapediaFourColor.NearLinearDiamondRepair
import Lean.Util.CollectAxioms

/-!
Audit source fidelity, embedded transport and the shared repair consumers.
The common finite profile is retained. Every original configuration rank
certificate and every complete Four Colour endpoint is excluded.
-/

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``BoundaryRepairTransport.boundary_iff, [``BoundaryRepairTransport.coloring]),
    (``BoundaryRepairTransport.trace_iff, [``BoundaryRepairTransport.coloring]),
    (``BoundaryRepairTransport.repairs, [``BoundaryRepairTransport.trace_iff,
      ``KempeBoundarySplit.graph_rotate_back]),
    (``NearLinearDiamondData.input0000, [``NearLinearDiamondData.parseRows]),
    (``NearLinearDiamondData.input0001, [``NearLinearDiamondData.parseRows]),
    (``NearLinearDiamondData.iso0000, [``NearLinearDiamondData.Input.graph,
      ``NearLinearDiamondData.input0000, ``DiamondConfigurations.graph001]),
    (``NearLinearDiamondData.iso0001, [``NearLinearDiamondData.Input.graph,
      ``NearLinearDiamondData.input0001, ``DiamondConfigurations.graph002]),
    (``NearLinearDiamondData.rotation0000, [``NearLinearDiamondData.stars0000,
      ``DiamondConfigurations.stars001]),
    (``NearLinearDiamondData.rotation0001, [``NearLinearDiamondData.stars0001,
      ``DiamondConfigurations.stars002]),
    (``NearLinearDiamondData.degree0000, [``NearLinearDiamondData.coreRow]),
    (``NearLinearDiamondData.degree0001, [``NearLinearDiamondData.coreRow]),
    (``NearLinearDiamondData.boundary0000, [``NearLinearDiamondData.Input.boundary]),
    (``NearLinearDiamondData.boundary0001, [``NearLinearDiamondData.Input.boundary]),
    (``NearLinearDiamondRepair.boundary0000_iff, [``BoundaryRepairTransport.boundary_iff]),
    (``NearLinearDiamondRepair.boundary0001_iff, [``BoundaryRepairTransport.boundary_iff]),
    (``NearLinearDiamondRepair.sourceInsertion,
      [``NearLinearDiamondData.iso0000, ``NearLinearDiamondData.iso0001,
       ``DiamondInsertion.insert12]),
    (``NearLinearDiamondRepair.sourceInsertion_rotation,
      [``ConfigurationFaceGraph.triangleStar]),
    (``NearLinearDiamondRepair.sourceInsertion_boundary,
      [``ConfigurationFaceGraph.triangleBoundary]),
    (``NearLinearDiamondRepair.sourceInsertion_commutes,
      [``NearLinearDiamondRepair.sourceInsertion, ``DiamondInsertion.insert12]),
    (``NearLinearDiamondRepair.repair0000, [``BoundaryRepairTransport.repairs,
      ``NearLinearDiamondData.boundary0000, ``DiamondConfigurations.numbered001,
      ``DiamondProfileReducibility.transferred001, ``KempeBoundarySplit.repairs_collapse,
      ``DiamondProfileCertificate.repair]),
    (``NearLinearDiamondRepair.repair0001, [``BoundaryRepairTransport.repairs,
      ``NearLinearDiamondData.boundary0001, ``DiamondConfigurations.numbered002,
      ``DiamondProfileReducibility.repair002, ``DiamondProfileCertificate.repair]),
    (``NearLinearDiamondRepair.construction_history0001, [``DiamondInsertion.alternatives12,
      ``DiamondInsertionGSLT.semantics, ``NearLinearDiamondRepair.coloring0001]),
    (``NearLinearDiamondRepair.compatible_repair0001, [``NearLinearDiamondRepair.repair0001,
      ``NearLinearDiamondRepair.construction_history0001])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducible_block_0,
    `FourColor.DiamondSplitRepair.base_repair, `FourColor.DiamondBoundaryRepair.repair,
    `FourColor.DiamondJointRepair.contract_repair, `FourColor.coversRec, `FourColor.coversRec_sound]
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
      if forbidden.any (·.isPrefixOf name) || name.toString.startsWith "FourColor.Bulk.Cfg" ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Independent configuration certificate or complete theorem in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Near-linear diamond bridge: {roots.length} roots; \
    {inspected.toList.length} declarations; two exact source presentations; \
    shared profile and split repair; no original configuration certificate or complete theorem."
